{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards     #-}

-- | This module parses the s-expression output that Z3 (and other SMTLIB2
--   solvers) emit — in particular the results of @(apply <tactic>)@ which come
--   back wrapped as @(goals (goal <formula> ... :precision .. :depth ..) ...)@ —
--   back into a 'Language.Fixpoint.Types.Expr'.
--
--   It is the inverse of the @instance SMTLIB2 Expr@ in
--   "Language.Fixpoint.Smt.Serialize" for the quantifier-free linear-arithmetic
--   subset produced by the w-variable weakest-precondition machinery. See
--   'parseGoals'/'parseExpr' for the entry points and the module notes below
--   for the exact subset and quirks handled.
--
--   NOTE [Symbol encoding]. liquid-fixpoint serializes a 'Symbol' via
--   'symbolSafeText' (== 'symbolEncoded'), which %-encodes any character
--   outside @[a-zA-Z0-9_.]@ as @$<ord>$@ (and adds @fix$@/@key$@/@z$@ prefixes
--   in some cases). Z3 echoes those encoded names back verbatim. To recover the
--   /original/ 'Symbol' (so that @serialize -> parse@ round-trips) we decode
--   that encoding with 'decodeSymText' before calling 'symbol'.
--
--   NOTE [= is ambiguous]. Both @PIff@ and @PAtom Eq@ serialize to @(= a b)@,
--   and @PAtom Ne@ serializes to @(not (= a b))@. Lacking sort information we
--   always read @(= a b)@ as @PAtom Eq a b@. This is logically faithful but not
--   structurally identical for @PIff@/@Ne@ inputs.

module Language.Fixpoint.Smt.Parse
  ( -- * Entry points (Text -> Either String Expr)
    parseExpr
  , parseGoals

    -- * Attoparsec parsers (mirroring 'Language.Fixpoint.Smt.Interface.SmtParser')
  , exprP
  , goalsP

    -- * Symbol decoding (inverse of 'symbolSafeText')
  , decodeSymText
  ) where

import           Control.Applicative      ((<|>), many)
import           Control.Monad            (void)
import           Data.Char                (chr, isSpace)
import qualified Data.HashSet             as S
import qualified Data.Text                as T
import qualified Data.Attoparsec.Text     as A

import           Language.Fixpoint.Types

--------------------------------------------------------------------------------
-- | Entry points --------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Parse a single Z3 formula s-expression into an 'Expr'.
parseExpr :: T.Text -> Either String Expr
parseExpr = A.parseOnly (skip *> exprP <* skip <* A.endOfInput)

-- | Parse the @(goals (goal F ...) ...)@ wrapper emitted by @(apply ...)@ into
--   a single 'Expr'. Multiple formulas /within/ a goal are conjoined (AND);
--   multiple goals are disjoined (OR).
parseGoals :: T.Text -> Either String Expr
parseGoals = A.parseOnly (skip *> goalsP <* skip <* A.endOfInput)

--------------------------------------------------------------------------------
-- | Lexing helpers ------------------------------------------------------------
--------------------------------------------------------------------------------

type SmtParser a = A.Parser a

-- | Skip whitespace (Z3 output may also have its lines concatenated with no
--   separator, which is fine — parens delimit tokens).
skip :: SmtParser ()
skip = A.skipSpace

-- | @lex p@ runs @p@ and then consumes trailing whitespace.
lexP :: SmtParser a -> SmtParser a
lexP p = p <* skip

-- | A single unquoted SMTLIB token: any run of characters that is not a paren,
--   whitespace, or the quote/pipe characters.
tokenText :: SmtParser T.Text
tokenText = A.takeWhile1 (\c -> not (isSpace c || c == '(' || c == ')' || c == '"' || c == '|'))

-- | A @|quoted symbol|@ (SMTLIB v2.6). Z3 uses these when a name contains
--   characters that would otherwise need escaping.
pipeText :: SmtParser T.Text
pipeText = A.char '|' *> A.takeWhile (/= '|') <* A.char '|'

lparen, rparen :: SmtParser ()
lparen = void (lexP (A.char '('))
rparen = void (lexP (A.char ')'))

-- | @parens p@ = @'(' p ')'@ modulo surrounding whitespace.
parens :: SmtParser a -> SmtParser a
parens p = lparen *> p <* rparen

-- | Parse @kw@ as a full token (so that e.g. @and@ does not match a prefix of
--   @android@).
keyword :: T.Text -> SmtParser ()
keyword kw = lexP $ do
  t <- tokenText
  if t == kw then pure () else fail ("expected keyword " ++ T.unpack kw)

--------------------------------------------------------------------------------
-- | Goals wrapper -------------------------------------------------------------
--------------------------------------------------------------------------------

-- | @(goals <goal>*)@
goalsP :: SmtParser Expr
goalsP = parens $ do
  keyword "goals"
  gs <- many goalP
  pure (orExprs gs)

-- | @(goal F* :key val ...)@ — the formulas are conjoined; the trailing
--   @:precision precise :depth N@ (and any other @:attr val@) are ignored.
goalP :: SmtParser Expr
goalP = parens $ do
  keyword "goal"
  fs <- many (attribute <|> (Just <$> exprP))
  pure (andExprs [f | Just f <- fs])

-- | A goal attribute @:name value@. Returns 'Nothing' so the caller can drop
--   it. We swallow one value token/s-expression after the @:name@.
attribute :: SmtParser (Maybe Expr)
attribute = do
  _ <- lexP (A.char ':' *> tokenText)          -- :precision, :depth, ...
  _ <- A.option () (void attrValue)            -- precise, 1, ...
  pure Nothing
  where
    attrValue = lexP (void tokenText) <|> skipSexp

-- | Skip a balanced parenthesized s-expression (used to drop attribute values
--   we do not care about).
skipSexp :: SmtParser ()
skipSexp = parens (void (many (skipSexp <|> lexP (void (pipeText <|> tokenText)))))

--------------------------------------------------------------------------------
-- | Expressions ---------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Parse a formula/term. Either an atom or a parenthesized application.
exprP :: SmtParser Expr
exprP = lexP (atomP <|> parens appP)

-- | An atom: @true@, @false@, an integer literal, or a variable.
atomP :: SmtParser Expr
atomP =
      (PTrue  <$ keywordAtom "true")
  <|> (PFalse <$ keywordAtom "false")
  <|> conP
  <|> (mkVar <$> (pipeText <|> tokenText))

-- | Like 'keyword' but does not consume trailing space itself (it is used from
--   within 'atomP', which is already wrapped by 'lexP').
keywordAtom :: T.Text -> SmtParser ()
keywordAtom kw = do
  t <- A.takeWhile1 (\c -> not (isSpace c || c == '(' || c == ')'))
  if t == kw then pure () else fail ("expected " ++ T.unpack kw)

-- | A non-negative integer literal atom. (Negative literals show up as
--   @(- 5)@ and are handled in 'appP'.)
conP :: SmtParser Expr
conP = do
  ds <- A.takeWhile1 (\c -> c >= '0' && c <= '9')
  -- Make sure it is a *complete* token (not the head of an identifier like 0x).
  next <- A.peekChar
  case next of
    Just c | not (isSpace c || c == '(' || c == ')') -> fail "not an int literal"
    _ -> pure (ECon (I (read (T.unpack ds))))

-- | A parenthesized application: the head token decides the form.
appP :: SmtParser Expr
appP =
      letP
  <|> boolP
  <|> arithP
  <|> relP
  <|> quantP
  <|> asP
  <|> underscoreP
  <|> appLikeP

-- | @(let ((x e) ...) body)@ — expanded by substituting each binding into the
--   body (Z3's simplifier occasionally emits these).
letP :: SmtParser Expr
letP = do
  keyword "let"
  binds <- parens (many binding)
  body <- exprP
  pure (foldr (\(x, e) acc -> subst1 acc (x, e)) body binds)
  where
    binding = parens $ do
      x <- lexP (mkSym <$> (pipeText <|> tokenText))
      e <- exprP
      pure (x, e)

-- | Boolean connectives.
boolP :: SmtParser Expr
boolP =
      (keyword "and" *> (andExprs <$> many exprP))
  <|> (keyword "or"  *> (orExprs  <$> many exprP))
  <|> (keyword "not" *> (PNot <$> exprP))
  <|> (keyword "=>"  *> (impChain <$> exprP <*> many exprP))
  <|> (keyword "ite" *> (EIte <$> exprP <*> exprP <*> exprP))
  where
    -- (=> a b c) desugars to a => (b => c)
    impChain e []       = e
    impChain e (x : xs) = PImp e (impChain x xs)

-- | Arithmetic. Note @-@ is overloaded: unary @(- e)@ is negation, binary
--   @(- a b ...)@ is subtraction. @*@ / @SMTLIB_OP_MUL@ is 'Times',
--   @div@ / @SMTLIB_OP_DIV@ is 'Div', @mod@ is 'Mod'.
arithP :: SmtParser Expr
arithP =
      (keyword "+"   *> (binChain (EBin Plus)  (ECon (I 0)) <$> many1 exprP))
  <|> (keyword "-"   *> minusP)
  <|> (keyword "*"   *> (binChain (EBin Times) (ECon (I 1)) <$> many1 exprP))
  <|> (keyword "div" *> (EBin Div <$> exprP <*> exprP))
  <|> (keyword "mod" *> (EBin Mod <$> exprP <*> exprP))
  <|> (keyword mulName *> (binChain (EBin Times) (ECon (I 1)) <$> many1 exprP))
  <|> (keyword divName *> (EBin Div <$> exprP <*> exprP))
  where
    minusP = do
      es <- many1 exprP
      pure $ case es of
        [e] -> negateExpr e             -- unary minus
        _   -> foldl1 (EBin Minus) es   -- (- a b c) = ((a-b)-c)

-- | Comparison relations.
relP :: SmtParser Expr
relP =
      (keyword "="  *> (PAtom Eq <$> exprP <*> exprP))   -- see NOTE [= is ambiguous]
  <|> (keyword ">=" *> (PAtom Ge <$> exprP <*> exprP))
  <|> (keyword ">"  *> (PAtom Gt <$> exprP <*> exprP))
  <|> (keyword "<=" *> (PAtom Le <$> exprP <*> exprP))
  <|> (keyword "<"  *> (PAtom Lt <$> exprP <*> exprP))
  <|> (keyword "distinct" *> (mkDistinct <$> exprP <*> exprP))

-- | Quantifiers (should be gone after QE, but parse defensively).
quantP :: SmtParser Expr
quantP =
      (keyword "forall" *> (PAll   <$> sortedVars <*> exprP))
  <|> (keyword "exists" *> (PExist <$> sortedVars <*> exprP))
  where
    sortedVars = parens (many sortedVar)
    sortedVar  = parens $ do
      x <- lexP (mkSym <$> (pipeText <|> tokenText))
      s <- sortP
      pure (x, s)

-- | @(as <expr> <sort>)@ — a sort ascription. We drop the sort and keep the
--   expression.
asP :: SmtParser Expr
asP = keyword "as" *> (exprP <* sortP)

-- | @(_ name idx ...)@ — an indexed identifier. Treated as an (opaque)
--   variable named after the whole thing joined by @_@.
underscoreP :: SmtParser Expr
underscoreP = do
  keyword "_"
  ts <- many1 (lexP (pipeText <|> tokenText))
  pure (mkVar (T.intercalate "_" ("_" : ts)))

-- | A function application @(f a b ...)@ where @f@ is a symbol. Builds the
--   curried @EApp@ spine as in the serializer. Recognizes @SMTLIB_OP_MUL@ /
--   @SMTLIB_OP_DIV@ as arithmetic if they appear as a head.
appLikeP :: SmtParser Expr
appLikeP = do
  f  <- lexP (mkVar <$> (pipeText <|> tokenText))
  as <- many exprP
  pure (foldl EApp f as)

--------------------------------------------------------------------------------
-- | Sorts (only needed inside quantifiers / @as@; minimal support) ------------
--------------------------------------------------------------------------------

-- | A very small sort parser: @Int@, @Real@, @Bool@, other atoms as 'FObj', and
--   parenthesized applications collapsed to their head's 'FObj' (we never need
--   the precise sort — it is discarded for @as@ and only used for binder
--   annotations that QE removes).
sortP :: SmtParser Sort
sortP = lexP (atomSort <|> parens appSort)
  where
    atomSort = do
      t <- pipeText <|> tokenText
      pure $ case t of
        "Int"  -> intSort
        "int"  -> intSort
        "Real" -> realSort
        "Bool" -> boolSort
        _      -> FObj (mkSym t)
    appSort = do
      _ <- lexP (pipeText <|> tokenText)
      _ <- many sortP
      pure intSort   -- collapse; precise value is irrelevant for our use

--------------------------------------------------------------------------------
-- | Smart constructors / helpers ----------------------------------------------
--------------------------------------------------------------------------------

-- | Build a variable 'Expr' from the (encoded) Z3 name.
mkVar :: T.Text -> Expr
mkVar = EVar . mkSym

-- | Build a 'Symbol' from an (encoded) Z3 name, decoding the liquid-fixpoint
--   symbol encoding first. See NOTE [Symbol encoding].
mkSym :: T.Text -> Symbol
mkSym = symbol . decodeSymText

andExprs :: [Expr] -> Expr
andExprs [e] = e
andExprs es  = PAnd es

orExprs :: [Expr] -> Expr
orExprs [e] = e
orExprs es  = POr es

-- | @(distinct a b)@ over two arguments is @a /= b@.
mkDistinct :: Expr -> Expr -> Expr
mkDistinct a b = PNot (PAtom Eq a b)

-- | Negate an expression, folding integer literals so that @(- 5)@ becomes the
--   literal @-5@ (matching how the serializer would emit @ECon (I (-5))@ vs
--   @ENeg@).
negateExpr :: Expr -> Expr
negateExpr (ECon (I n)) = ECon (I (negate n))
negateExpr e            = ENeg e

-- | Left-fold a binary op over a non-empty list, using the unit for the empty
--   case (which 'many1' guarantees does not happen, but keeps it total).
binChain :: (Expr -> Expr -> Expr) -> Expr -> [Expr] -> Expr
binChain _  z []       = z
binChain _  _ [e]      = e
binChain op _ (e : es) = foldl op e es

mulName, divName :: T.Text
mulName = symbolText mulFuncName   -- "SMTLIB_OP_MUL"
divName = symbolText divFuncName   -- "SMTLIB_OP_DIV"

-- | 'A.many1' is not exported by attoparsec-text under that name in all
--   versions; define locally.
many1 :: SmtParser a -> SmtParser [a]
many1 p = (:) <$> p <*> many p

--------------------------------------------------------------------------------
-- | Symbol decoding: inverse of 'symbolSafeText' ------------------------------
--------------------------------------------------------------------------------

-- | Decode the liquid-fixpoint symbol encoding (see 'symbolSafeText' /
--   'Language.Fixpoint.Types.Names.encode') back to the original raw text, so
--   that @symbol . decodeSymText . symbolSafeText . symbol == symbol@ on the
--   names that occur in practice.
--
--   Encoding recap:
--
--     * unsafe chars (anything outside @[a-zA-Z0-9_.]@) become @$<ord>$@;
--     * if the name does not start with a letter, a @fix$@ prefix is added;
--     * if the name is a reserved keyword, a @key$@ prefix is added;
--     * if the result then starts with @$@, a @z@ is prepended.
decodeSymText :: T.Text -> T.Text
decodeSymText enc =
  case T.stripPrefix "key$" enc of
    Just krest | decodeDollars krest `S.member` keywordsSet -> decodeDollars krest
    _ ->
      let dd = decodeDollars enc
      in case T.stripPrefix "fix$" dd of
           Just frest | not (startsAlpha frest) -> frest
           _                                    -> dd
  where
    -- Undo the @z$@ padding (only meaningful directly before a @$...$@ escape).
    unpad t = case T.stripPrefix "z$" t of
                Just r | "$" `T.isPrefixOf` r -> r
                _                             -> t

    decodeDollars = go . unpad

    go t = case T.uncons t of
      Nothing -> T.empty
      Just ('$', rest) ->
        let (digits, rest') = T.span (/= '$') rest
        in case (T.null digits, T.stripPrefix "$" rest', readDigits digits) of
             (False, Just rest'', Just n) -> T.cons (chr n) (go rest'')
             _                            -> T.cons '$' (go rest)
      Just (c, rest) -> T.cons c (go rest)

    readDigits d
      | T.all (\c -> c >= '0' && c <= '9') d
      , not (T.null d) = case reads (T.unpack d) of
                           [(n, "")] | n >= 0 && n <= 0x10FFFF -> Just n
                           _                                   -> Nothing
      | otherwise      = Nothing

    startsAlpha t = case T.uncons t of
      Just (c, _) -> (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
      Nothing     -> False

-- | The reserved keywords that get a @key$@ prefix under 'encode'
--   (mirrors 'Language.Fixpoint.Types.Names.keywords').
keywordsSet :: S.HashSet T.Text
keywordsSet = S.fromList
  [ "env", "id", "tag", "qualif", "constant", "cut", "bind"
  , "constraint", "lhs", "rhs", "NaN", "min", "map" ]
