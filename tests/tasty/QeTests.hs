{-# LANGUAGE OverloadedStrings #-}

-- | Tests for 'Language.Fixpoint.Smt.Parse' (parsing Z3 s-expression output
--   back into an 'Expr') and for 'Language.Fixpoint.Smt.Interface.qe'
--   (quantifier elimination + simplification through Z3).
--
--   The parser tests come in two flavours:
--
--     1. /Round-trip/ tests: take an 'Expr', serialize it with the real
--        @instance SMTLIB2 Expr@ (the exact syntax Z3 sees), parse it back, and
--        check we recover a structurally-equivalent 'Expr' (modulo the
--        documented @=@/@Ne@/@PIff@ normalization).
--
--     2. /Literal/ tests: feed hand-written Z3 output (captured from actual
--        @z3@ runs) to the parser and check the produced 'Expr'.
--
--   The QE tests require a live @z3@ on @PATH@ and are only added to the group
--   when the environment variable @FIXPOINT_QE_TESTS@ is set (so the default
--   @stack test@ run does not depend on a solver being present in the tasty
--   suite). Run them with:
--
--   > FIXPOINT_QE_TESTS=1 stack test liquid-fixpoint:tasty
module QeTests (tests) where

import           Control.Monad.State (evalState, evalStateT)
import qualified Data.ByteString.Builder     as BS
import qualified Data.ByteString.Lazy        as LBS
import qualified Data.Text                   as T
import qualified Data.Text.Encoding          as TE
import           System.Environment          (lookupEnv)
import           System.IO.Unsafe            (unsafePerformIO)

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Config (defConfig)
import           Language.Fixpoint.Smt.Types    (runSmt2)
import           Language.Fixpoint.Smt.Serialize ()
import           Language.Fixpoint.Smt.Parse    (parseExpr, parseGoals, decodeSymText)
import           Language.Fixpoint.Smt.Interface (makeContextNoLog, qe)

import           Test.Tasty
import           Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "QeTests"
  [ decodeTests
  , roundtripTests
  , literalTests
  , qeTests
  ]

--------------------------------------------------------------------------------
-- | helpers -------------------------------------------------------------------
--------------------------------------------------------------------------------

sym :: T.Text -> Symbol
sym = symbol

var :: T.Text -> Expr
var = EVar . sym

int :: Integer -> Expr
int = ECon . I

-- | Serialize an 'Expr' with the real 'instance SMTLIB2 Expr', i.e. exactly the
--   text that would be sent to (and hence echoed by) Z3.
serialize :: Expr -> T.Text
serialize e =
  TE.decodeUtf8 . LBS.toStrict . BS.toLazyByteString $
    evalState (runSmt2 e) (mempty :: SymEnv)

--------------------------------------------------------------------------------
-- | symbol decoding -----------------------------------------------------------
--------------------------------------------------------------------------------

decodeTests :: TestTree
decodeTests = testGroup "decodeSymText (inverse of symbolSafeText)"
  [ mk "a0##wvq"
  , mk "reftgen$m$0"
  , mk "fld0$0"
  , mk "m"
  , mk "a1"
  , mk "x!0"
  , mk "$foo"
  , mk "3x"
  , mk "SMTLIB_OP_MUL"
  , mk "a.b_c"
  , mk "env"
  , mk "map"
  ]
  where
    -- symbolSafeText . symbol is the encoder; decodeSymText must invert it.
    mk raw = testCase (T.unpack raw) $
      decodeSymText (symbolSafeText (sym raw)) @?= raw

--------------------------------------------------------------------------------
-- | serialize -> parse round-trips --------------------------------------------
--------------------------------------------------------------------------------

roundtripTests :: TestTree
roundtripTests = testGroup "serialize -> parse round-trip"
  [ mk "true"       PTrue
  , mk "false"      PFalse
  , mk "var"        (var "m")
  , mk "encvar"     (var "a0##wvq")
  , mk "int"        (int 5)
  , mkExpect "negint" (ENeg (int 5)) (int (-5))                     -- (- 5) folds to literal -5
  , mk "ge"         (PAtom Ge (var "m") (int 0))
  , mk "gt"         (PAtom Gt (var "x") (var "y"))
  , mk "lt"         (PAtom Lt (var "x") (int 3))
  , mk "le"         (PAtom Le (var "x") (int 3))
  , mk "and"        (PAnd [PAtom Ge (var "m") (int 0), PAtom Ge (var "a1") (int 0)])
  , mk "or"         (POr  [PAtom Ge (var "m") (int 0), PAtom Le (var "a1") (int 0)])
  , mk "not"        (PNot (PAtom Ge (var "m") (int 0)))
  , mk "imp"        (PImp (PAtom Ge (var "m") (int 0)) (PAtom Eq (var "a1") (var "m")))
  , mk "plus"       (EBin Plus (var "x") (int 1))
  , mk "minus"      (EBin Minus (var "x") (var "y"))
  , mk "neg"        (ENeg (var "y"))                                -- (- y)
  , mk "app1"       (EApp (var "fld0$0") (var "a0##wvq"))
  , mk "app2"       (EApp (EApp (var "f") (var "a")) (var "b"))
  , mk "nested"
      (PImp (PAnd [ PAtom Ge (var "a0##wvq") (int 0)
                  , PAtom Ge (var "m") (int 0)
                  , PAtom Ge (var "a1") (int 0) ])
            (PAtom Eq (var "a1") (var "m")))
    -- Times/Div serialize to SMTLIB_OP_MUL/DIV, which the parser reads back as EBin.
  , mk "times"      (EBin Times (int 2) (var "x"))
  , mk "div"        (EBin Div (var "x") (int 2))
  , mk "mod"        (EBin Mod (var "x") (int 3))
  , mk "forall"
      (PAll [(sym "a0##wvq", intSort)]
        (PImp (PAtom Ge (var "a0##wvq") (int 0)) (PAtom Eq (var "a1") (var "m"))))
    -- Documented normalizations: PIff and Ne come back as Eq / not Eq.
  , mkExpect "iff-normalizes"
      (PIff (var "p") (var "q"))
      (PAtom Eq (var "p") (var "q"))
  , mkExpect "ne-normalizes"
      (PAtom Ne (var "x") (var "y"))
      (PNot (PAtom Eq (var "x") (var "y")))
  ]
  where
    -- identity round-trip: parse (serialize e) == e
    mk name e = testCase name $ parseExpr (serialize e) @?= Right e
    -- round-trip with an expected (normalized) result
    mkExpect name e expected = testCase name $ parseExpr (serialize e) @?= Right expected

--------------------------------------------------------------------------------
-- | literal Z3 output ---------------------------------------------------------
--------------------------------------------------------------------------------

literalTests :: TestTree
literalTests = testGroup "parse literal z3 output"
  [ testCase "goal wrapper (qe)" $
      parseGoals "(goals\n(goal\n  (not (and (not (= a1 m)) (>= m 0) (>= a1 0) true))\n  :precision precise :depth 1)\n)"
        @?= Right (PNot (PAnd [ PNot (PAtom Eq (var "a1") (var "m"))
                              , PAtom Ge (var "m") (int 0)
                              , PAtom Ge (var "a1") (int 0)
                              , PTrue ]))

  , testCase "goal with two conjoined formulas" $
      parseGoals "(goals (goal (>= x 0) (=> (>= y 0) (= x y)) :precision precise :depth 2))"
        @?= Right (PAnd [ PAtom Ge (var "x") (int 0)
                        , PImp (PAtom Ge (var "y") (int 0)) (PAtom Eq (var "x") (var "y")) ])

  , testCase "goal false" $
      parseGoals "(goals (goal false :precision precise :depth 1))"
        @?= Right PFalse

  , testCase "two goals disjoined" $
      parseGoals "(goals (goal (>= x 5) :precision precise :depth 3) (goal (<= x 0) :precision precise :depth 3))"
        @?= Right (POr [PAtom Ge (var "x") (int 5), PAtom Le (var "x") (int 0)])

  , testCase "arithmetic with negative literal and star" $
      parseGoals "(goals (goal (= (+ (* 2 x) (* (- 1) y)) 5) :precision precise :depth 2))"
        @?= Right (PAtom Eq (EBin Plus (EBin Times (int 2) (var "x"))
                                       (EBin Times (int (-1)) (var "y"))) (int 5))

  , testCase "let is expanded" $
      parseGoals "(goals (goal (let ((a!1 (>= x 0))) (not a!1)) :precision precise :depth 2))"
        @?= Right (PNot (PAtom Ge (var "x") (int 0)))

  , testCase "encoded symbols decoded, function application" $
      parseExpr "(fld0$36$0 a0$35$$35$wvq)"
        @?= Right (EApp (var "fld0$0") (var "a0##wvq"))

  , testCase "mod" $
      parseExpr "(mod x 3)" @?= Right (EBin Mod (var "x") (int 3))

  , testCase "div" $
      parseExpr "(div x 2)" @?= Right (EBin Div (var "x") (int 2))
  ]

--------------------------------------------------------------------------------
-- | end-to-end QE (requires z3; gated behind FIXPOINT_QE_TESTS) ----------------
--------------------------------------------------------------------------------

qeTests :: TestTree
qeTests
  | qeEnabled = testGroup "qe (end-to-end, needs z3)"
      [ testCaseSteps "forall a0. (a0>=0 && m>=0 && a1>=0) => a1=m  is quantifier-free" $ \step -> do
          r <- runQe f1
          step ("result: " ++ show r)
          assertBool "result should be quantifier free" (isQuantFree r)

      , testCaseSteps "forall q. q>=0 => x=y   simplifies to x=y" $ \step -> do
          r <- runQe f2
          step ("result: " ++ show r)
          r @?= PAtom Eq (var "x") (var "y")

      , testCaseSteps "quantifier-free arithmetic round-trips through qe" $ \step -> do
          r <- runQe f3
          step ("result: " ++ show r)
          assertBool "result should be quantifier free" (isQuantFree r)
      ]
  | otherwise = testGroup "qe (end-to-end, needs z3) [SKIPPED: set FIXPOINT_QE_TESTS=1]" []
  where
    f1 = PAll [(sym "a0##wvq", intSort)]
           (PImp (PAnd [ PAtom Ge (var "a0##wvq") (int 0)
                       , PAtom Ge (var "m") (int 0)
                       , PAtom Ge (var "a1") (int 0) ])
                 (PAtom Eq (var "a1") (var "m")))
    f2 = PAll [(sym "q", intSort)]
           (PImp (PAtom Ge (var "q") (int 0)) (PAtom Eq (var "x") (var "y")))
    f3 = PAnd [ PAtom Eq (EBin Plus (EBin Times (int 2) (var "x")) (ENeg (var "y"))) (int 5)
              , PAtom Ge (var "x") (int 0) ]

    runQe e = do
      me <- makeContextNoLog defConfig
      evalStateT (qe e) me

{-# NOINLINE qeEnabled #-}
qeEnabled :: Bool
qeEnabled = unsafePerformIO $ maybe False (const True) <$> lookupEnv "FIXPOINT_QE_TESTS"

-- | Is the expression free of quantifiers?
isQuantFree :: Expr -> Bool
isQuantFree = go
  where
    go (PAll _ _)       = False
    go (PExist _ _)     = False
    go (PAnd es)        = all go es
    go (POr es)         = all go es
    go (PNot e)         = go e
    go (PImp a b)       = go a && go b
    go (PIff a b)       = go a && go b
    go (PAtom _ a b)    = go a && go b
    go (EBin _ a b)     = go a && go b
    go (ENeg e)         = go e
    go (EApp a b)       = go a && go b
    go (EIte a b c)     = go a && go b && go c
    go (ECst e _)       = go e
    go (ELet _ a b)     = go a && go b
    go (ECoerc _ _ e)   = go e
    go _                = True
