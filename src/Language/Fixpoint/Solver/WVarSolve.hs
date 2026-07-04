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
import           Data.Ord                           (comparing)
import           Data.Hashable                      (Hashable)
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
--   Algorithm (per failing head @h@):
--
--     1. Gather every reclaimed qualifier from a w-guarded drop whose k-var
--        appears in @h@'s LHS. (Vacuous qualifiers -- ones that contradict their
--        own constraint's body -- were already discarded at drop time, so no
--        w-var could rescue them.)
--     2. Re-add *all* of them to their k-vars and check the conjunction proves
--        @h@. If not, @h@ cannot be fixed by these w-vars; skip it.
--     3. Minimize: greedily drop qualifiers while @h@ still proves, leaving a
--        minimal load-bearing subset that (together) validates @h@.
--     4. For each surviving qualifier, build the weakest precondition on its
--        responsible w-var. Group per w-var (a w-var responsible for several
--        gets the conjunction), then simplify with QE.
--
--   The minimization over the *conjunction* is what lets a fix that needs
--   several cooperating qualifiers/w-vars be found -- not just single-qualifier
--   rescues.
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
  -- The WP non-vacuity/QE below is quantified; MBQI must be on (the preamble
  -- disables it for the QF Phase-1 checks).
  smtEnablembqi
  -- The same drop is recorded on every fixpoint iteration; dedup.
  let uniqueDrops = M.elems $ M.fromList [ (dropKey d, d) | d <- drops ]
  -- For each failing head, find a minimal set of reclaimed qualifiers that
  -- together prove it; keep the union of those load-bearing drops.
  coreDrops <- concat <$> mapM (loadBearing uniqueDrops) failCs
  -- Build per-drop WP conjuncts, attributing each drop to the /best-covering/
  -- guarding w-var (the one whose arguments mention the most of the variables
  -- the qualifier constrains). When several w-vars guard a constraint, a
  -- qualifier can often be provided by any of them, but the best-covering one
  -- gives the least degenerate solution; picking it avoids reporting the same
  -- qualifier as a separate (often vacuous) "fix" on every ambient w-var.
  -- Keep only non-vacuous conjuncts (satisfiable with the constraint domain).
  let cands0 = L.nub [ (w, wpOfDrop w d) | d <- coreDrops, Just w <- [bestWVar d] ]
  cands <- filterM (\(_, (wp, lhs)) -> satisfiable (F.pAnd [wp, lhs])) cands0
  -- Simplify each WP conjunct with Z3 quantifier elimination, in a FRESH
  -- context (qeMany) so `(apply qe)` does not see the solver's ambient
  -- assertions. Best-effort: a formula QE can't handle is returned unchanged.
  let ws0   = map fst cands
      es0   = map (fst . snd) cands
      lhss0 = map (snd . snd) cands
  es1 <- liftIO $ qeMany cfg es0
  -- group per w-var, carrying each conjunct's QE'd WP and its domain (lhs)
  let perWVar = M.fromListWith (++) [ (w, [(e, l)]) | (w, e, l) <- zip3 ws0 es1 lhss0 ]
  -- Final vacuity guard (domain-aware): a w-var's *combined* solution must be
  -- satisfiable together with the domains its conjuncts came from. This rejects
  -- bundles whose conjuncts contradict each other on the reachable domain
  -- (e.g. i0>0 AND i0<=0), which are not real fixes.
  perWVar' <- filterMapM
                (\els -> satisfiable (F.pAnd (map fst els ++ map snd els)))
                perWVar
  return $ M.map (mkFix . map fst) perWVar'
  where
    be = F.bs fi
    cm = F.cm fi

    -- | Keep only the map entries whose value list satisfies the predicate.
    filterMapM :: (Eq k, Hashable k, Monad m)
               => ([v] -> m Bool) -> M.HashMap k [v] -> m (M.HashMap k [v])
    filterMapM p m = M.fromList <$> filterM (p . snd) (M.toList m)

    -- | For a single failing constraint @c@: a small set of reclaimed qualifiers
    --   that, re-added to their k-vars, makes @c@ valid /non-vacuously/. We build
    --   the set up greedily: start from nothing and add a candidate only if it
    --   keeps the enhanced LHS satisfiable (adding contradictory qualifiers would
    --   make the k-var false and "prove" the head trivially); stop once the head
    --   holds. Empty if the head can't be rescued this way.
    loadBearing :: [WDrop] -> F.SimpC a -> SolveM a [WDrop]
    loadBearing ds c = grow c [] cand
      where
        lhsKs = V.envKVars be c
        cand  = L.sortOn coverGap [ d | d <- ds, wdKVar d `elem` lhsKs ]

    -- | Grow a consistent, load-bearing set. @acc@ (kept LHS-satisfiable) is the
    --   set so far; try each remaining candidate, keeping only those that
    --   preserve satisfiability, and stop as soon as the head holds.
    grow :: F.SimpC a -> [WDrop] -> [WDrop] -> SolveM a [WDrop]
    grow c acc rest = do
      done <- headHolds c acc
      if done then return acc else go rest
      where
        go []      = return []             -- couldn't rescue the head
        go (d:ds') = do
          keepSat <- lhsSat c (acc ++ [d])
          if keepSat then do r <- grow c (acc ++ [d]) ds'
                             if null r then go ds' else return r
                     else go ds'

    -- | Is the enhanced LHS (k-vars augmented by @ds@) satisfiable?
    lhsSat :: F.SimpC a -> [WDrop] -> SolveM a Bool
    lhsSat c ds = satisfiable (So.lhsPred cfg scope F.emptyIBindEnv be (enhance ds) c)

    -- | The final solution with every drop in @ds@ re-added to its k-var.
    enhance :: [WDrop] -> Sol.Solution
    enhance = foldr (\d -> addEQual (wdKVar d) (wdEQual d)) sFinal

    -- | How many variables of the dropped qualifier are NOT covered by (the best
    --   of) its guarding w-vars' arguments. 0 = some w-var sees every variable
    --   the qualifier constrains (a clean fix); larger = more degenerate.
    coverGap :: WDrop -> Int
    coverGap d =
      let qvs = F.exprSymbolsSet (wdHead d)
          wargs w = maybe mempty (wvarArgSyms w) (M.lookup (wdCid d) cm)
          gap w = S.size (qvs `S.difference` wargs w)
      in  case wdWVars d of
            [] -> S.size qvs
            ws -> minimum (map gap ws)

    -- | The best-covering guarding w-var for a drop: the one whose arguments
    --   mention the most of the qualifier's variables.
    bestWVar :: WDrop -> Maybe F.WVar
    bestWVar d =
      let qvs = F.exprSymbolsSet (wdHead d)
          wargs w = maybe mempty (wvarArgSyms w) (M.lookup (wdCid d) cm)
          gap w = S.size (qvs `S.difference` wargs w)
      in  case wdWVars d of
            [] -> Nothing
            ws -> Just (L.minimumBy (comparing gap) ws)

    -- | Does @c@'s head hold under the enhancement by @ds@? (Callers keep the
    --   enhanced LHS satisfiable, so this is a genuine, non-vacuous check.)
    headHolds :: F.SimpC a -> [WDrop] -> SolveM a Bool
    headHolds c ds =
      isValid (F.srcSpan (F.sinfo c))
              (So.lhsPred cfg scope F.emptyIBindEnv be (enhance ds) c)
              (F.crhs c)

    -- | Add an EQual to a k-var's QBind in the solution.
    addEQual :: F.KVar -> Sol.EQual -> Sol.Solution -> Sol.Solution
    addEQual k eq s = s { Sol.sMap = M.adjust add k (Sol.sMap s) }
      where add (Sol.QB eqs) = Sol.QB (eq : eqs)

    isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM a Bool
    isValid sp p q = not . null <$> filterValid sp p [(q, ())]

    -- | @phi@ is satisfiable  <=>  @phi => false@ is NOT valid. Assert @phi@ as
    --   the LHS so its free variables get declared to the solver.
    satisfiable :: F.Expr -> SolveM a Bool
    satisfiable phi = do
      valid <- not . null <$> filterValid F.dummySpan phi [(F.PFalse, ())]
      return (not valid)

    -- cheap identity of a drop for deduplication
    dropKey :: WDrop -> (F.SubcId, F.KVar, F.Expr)
    dropKey d = (wdCid d, wdKVar d, wdHead d)

    mkFix :: [F.Expr] -> F.WVarFix
    mkFix conjs =
      F.WVarFix { F.wfSolution = F.pAnd (L.nub conjs)
                , F.wfDrops    = L.nub conjs }

    -- | The WP conjunct for a single recorded drop, /for a specific w-var/:
    --   only that w-var's own arguments are kept free; every other variable in
    --   the LHS is universally quantified.
    --
    --   The quantified variables are alpha-renamed to fresh names so they can
    --   never collide with the w-var's (free) argument variables.
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
