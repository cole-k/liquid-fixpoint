{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}

--------------------------------------------------------------------------------
-- | Weakest-precondition reconstruction of w-variable (weak k-var) solutions.
--
-- During Phase 1 the standard fixpoint runs with every (body-only) w-var pinned
-- to @true@. Whenever a /w-guarded/ constraint drops a qualifier @Q@ from a
-- k-var head, 'Language.Fixpoint.Solver.Solve.refineC' records that drop on the
-- fly (see 'WDrop'): the responsible constraint is exactly the one being
-- refined, so no post-hoc search is needed.
--
-- This module turns those recorded drops into candidate w-var solutions. For a
-- drop @(w, c, Q@head)@ we build the weakest precondition that would let @Q@
-- survive on that constraint:
--
-- >   w  :=  forall (vars of the LHS that are NOT arguments of w) . LHS => Q@head
--
-- where @LHS@ is the (hoisted) left-hand side of @c@ under the final solution,
-- with @w@ itself expanded to @true@ (which it is, being seeded that way). A
-- w-var responsible for several drops gets the conjunction of the per-drop WPs.
--
-- The resulting formula is generally quantified. Eliminating the quantifiers
-- (QE, e.g. via Z3) to express the solution purely over the w-var's own
-- arguments -- and checking non-vacuity -- is a later step; here we just build
-- and report the quantified candidate.
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.WVarSolve
  ( solveWVars
  ) where

import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S
import qualified Data.List                          as L
import           Control.Monad                      (filterM)
import           Control.Monad.IO.Class             (liftIO)
-- import qualified Debug.Trace                     as Debug  -- for [WVAR-PERF] instrumentation
import           Language.Fixpoint.Types.Config     (Config)
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.Types.Solutions  as Sol
import qualified Language.Fixpoint.Types.Visitor    as V
import           Language.Fixpoint.Solver.Monad     (SolveM, WDrop(..), getWDrops, filterValid, smtEnablembqi)
import           Language.Fixpoint.Smt.Interface    (qeMany)
import qualified Language.Fixpoint.Solver.Solution  as So

--------------------------------------------------------------------------------
-- | Build candidate w-var solutions from the drops captured during Phase 1.
--   Runs inside 'SolveM' (after refinement).
--
--   A captured drop is only turned into a WP if it is /relevant/: re-adding the
--   dropped qualifier to its k-var must actually help prove one of the failing
--   heads. This discards drops from constraints (e.g. base cases) whose
--   qualifiers have nothing to do with the failure -- otherwise every w-var that
--   happens to guard such a constraint would be reported with a useless (but
--   satisfiable) "solution". Surviving conjuncts are additionally checked for
--   non-vacuity (satisfiability with the domain) and simplified with QE.
--------------------------------------------------------------------------------
solveWVars
  :: forall a. (F.Loc a)
  => Config
  -> S.HashSet F.Symbol            -- ^ scope
  -> F.SInfo a
  -> Sol.Solution                  -- ^ final solution
  -> [F.SimpC a]                   -- ^ failing (concrete) constraints
  -> SolveM a F.WVarResult
solveWVars cfg scope fi sFinal failCs = do
  drops <- getWDrops
  -- The non-vacuity checks below are quantified; MBQI must be on for the
  -- solver to decide them (the preamble disables it for the QF Phase-1 checks).
  smtEnablembqi
  -- The same drop is recorded on every fixpoint iteration; dedup first (cheap,
  -- on the provenance) before building/checking WPs.
  let uniqueDrops = M.elems $ M.fromList [ (dropKey d, d) | d <- drops ]
  -- Keep only drops whose qualifier actually helps rescue a failing head.
  relDrops <- filterM relevant uniqueDrops
  let cands = [ (w, wpOfDrop w d) | d <- relDrops, w <- wdWVars d ]
  perDrop <- filterM nonVacuous cands
  -- Simplify each surviving WP conjunct with Z3 quantifier elimination, in a
  -- FRESH context (qeMany) so `(apply qe)` does not see the main solver's
  -- ambient assertions. Best-effort: a formula QE can't handle is returned
  -- unchanged.
  let ws0  = map fst perDrop
      es0  = map (fst . snd) perDrop
  es1 <- liftIO $ qeMany cfg es0
  let perWVar = M.fromListWith (++) [ (w, [e]) | (w, e) <- zip ws0 es1 ]
  return $ M.map mkFix perWVar
  where
    be = F.bs fi
    cm = F.cm fi

    -- | Is this drop relevant to some failing head? I.e. does re-adding the
    --   dropped qualifier to its k-var make a failing head (that reads that
    --   k-var) valid, when it was not before?
    relevant :: WDrop -> SolveM a Bool
    relevant d = anyM (rescues d) [ c | c <- failCs, wdKVar d `elem` V.envKVars be c ]

    rescues :: WDrop -> F.SimpC a -> SolveM a Bool
    rescues d c = do
      let sEnh = addEQual (wdKVar d) (wdEQual d) sFinal
          lhs  = So.lhsPred cfg scope F.emptyIBindEnv be sEnh c
          rhs  = F.crhs c
      isValid (F.srcSpan (F.sinfo c)) lhs rhs

    -- | Add an EQual to a k-var's QBind in the solution.
    addEQual :: F.KVar -> Sol.EQual -> Sol.Solution -> Sol.Solution
    addEQual k eq s = s { Sol.sMap = M.adjust add k (Sol.sMap s) }
      where add (Sol.QB eqs) = Sol.QB (eq : eqs)

    isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM a Bool
    isValid sp p q = not . null <$> filterValid sp p [(q, ())]

    anyM :: Monad m => (b -> m Bool) -> [b] -> m Bool
    anyM _ []     = return False
    anyM f (x:xs) = do b <- f x; if b then return True else anyM f xs

    -- cheap identity of a drop for deduplication
    dropKey :: WDrop -> (F.SubcId, F.KVar, F.Expr)
    dropKey d = (wdCid d, wdKVar d, wdHead d)

    mkFix :: [F.Expr] -> F.WVarFix
    mkFix conjs =
      F.WVarFix { F.wfSolution = F.pAnd (L.nub conjs)
                , F.wfDrops    = L.nub conjs }

    -- | A WP conjunct is useful iff, conjoined with the constraint's LHS
    --   (the reachable domain), it is satisfiable. Otherwise the only way to
    --   satisfy the WP is to make the w-var's guard false on the whole reachable
    --   domain -- i.e. a vacuous "fix" -- so we reject it. This is what filters
    --   out an ambient w-var (e.g. one guarding the whole constraint whose args
    --   don't mention the variable being constrained).
    nonVacuous :: (F.WVar, (F.Expr, F.Expr)) -> SolveM a Bool
    nonVacuous (_, (phi, lhs)) = satisfiable (F.pAnd [phi, lhs])

    -- | @phi@ is satisfiable  <=>  @phi => false@ is NOT valid. We assert @phi@
    --   itself as the LHS so its free variables get declared to the solver.
    satisfiable :: F.Expr -> SolveM a Bool
    satisfiable phi = do
      valid <- not . null <$> filterValid F.dummySpan phi [(F.PFalse, ())]
      return (not valid)

    -- | The WP conjunct for a single recorded drop, /for a specific w-var/:
    --   only that w-var's own arguments are kept free; every other variable in
    --   the LHS is universally quantified. Returns the conjunct and the LHS
    --   context (used for the non-vacuity check).
    --
    --   The quantified variables are alpha-renamed to fresh names so they can
    --   never collide with the w-var's (free) argument variables -- including in
    --   the non-vacuity check, where the raw LHS (with those variables free) is
    --   conjoined with the quantified WP.
    wpOfDrop :: F.WVar -> WDrop -> (F.Expr, F.Expr)
    wpOfDrop w (WDrop _ cid _ qHead _) =
      case M.lookup cid cm of
        Nothing -> (F.PTrue, F.PTrue)
        Just c  ->
          let lhs    = So.lhsPred cfg scope F.emptyIBindEnv be sFinal c
              body   = F.PImp lhs qHead
              wargs  = wvarArgSyms w c
              qvars  = [ (x, t)
                       | (x, t) <- binderSorts c
                       , x `S.member` F.exprSymbolsSet body
                       , not (x `S.member` wargs) ]
              -- alpha-rename quantified vars to fresh names
              su     = F.mkSubst [ (x, F.eVar (fresh x)) | (x, _) <- qvars ]
              qvars' = [ (fresh x, t) | (x, t) <- qvars ]
              wp     = if null qvars' then body
                       else F.PAll qvars' (F.subst su body)
          in  (wp, lhs)

    fresh :: F.Symbol -> F.Symbol
    fresh x = F.suffixSymbol x (F.symbol "wvq")

    -- | Symbols that appear as arguments to occurrences of the /given/ w-var in
    --   @c@'s environment -- the variables that w-var is allowed to keep free.
    wvarArgSyms :: F.WVar -> F.SimpC a -> S.HashSet F.Symbol
    wvarArgSyms w c = S.fromList
      [ y
      | (_, sr) <- envBinds c
      , F.PKVar k _ su <- kvarApps (F.reftPred (F.sr_reft sr))
      , k == F.wvarKVar w
      , e <- M.elems (F.fromKVarSubst su)
      , y <- S.toList (F.exprSymbolsSet e) ]

    -- | @(symbol, sort)@ for every binder in scope of @c@.
    binderSorts :: F.SimpC a -> [(F.Symbol, F.Sort)]
    binderSorts c = [ (x, F.sr_sort sr) | (x, sr) <- envBinds c ]

    envBinds :: F.SimpC a -> [(F.Symbol, F.SortedReft)]
    envBinds c =
      [ (x, sr) | i <- F.elemsIBindEnv (F.senv c)
                , let (x, sr, _) = F.lookupBindEnv i be ]

-- | Collect the @PKVar@ conjuncts of an expression (the kvar/w-var
--   applications), regardless of nesting under @PAnd@.
kvarApps :: F.Expr -> [F.Expr]
kvarApps = go
  where
    go (F.PAnd ps)      = concatMap go ps
    go e@(F.PKVar {})   = [e]
    go _                = []
