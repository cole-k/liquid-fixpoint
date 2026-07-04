{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}

--------------------------------------------------------------------------------
-- | Reconstruct candidate w-variable (weak k-var) solutions from the qualifier
--   "drops" recorded during Phase 1.
--
-- During Phase 1 the standard fixpoint runs with every (body-only) w-var pinned
-- to @true@. Whenever a /w-guarded/ constraint drops a qualifier @Q@ from a
-- k-var head, 'Language.Fixpoint.Solver.Solve.refineC' records that drop and
-- the w-var(s) that /could/ save it (their WP for @Q@ is non-vacuous).
--
-- Here we run a small \"reclaimed qualifier\" fixpoint, in parallel to (and not
-- affecting) the real solution:
--
--   * seed: each dropped @(k, Q)@ tagged with the w-vars that can save it;
--   * a reclaimed @(k, Q)@ must survive every constraint @c'@ where @k@ is a
--     head, exactly like a normal qualifier -- /except/ that it survives @c'@ if
--     EITHER @lhs(c') => Q@ holds directly, OR one of its tagged w-vars guards
--     @c'@ and can prove @Q@ there (non-vacuous WP in that context). A tagged
--     w-var that cannot prove @Q@ at @c'@ is dropped from @Q@'s tag; a @Q@ left
--     with no savers is removed;
--   * this only shrinks, so it converges.
--
-- After convergence, for each failing head we report, per w-var, the WP solution
-- built from the reclaimed qualifiers that w-var still saves and that make the
-- head valid. WPs are simplified with quantifier elimination.
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.WVarSolve
  ( solveWVars
  ) where

import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S
import qualified Data.List                          as L
import           Control.Monad                      (foldM, filterM)
import           Control.Monad.IO.Class             (liftIO)
import           Data.IORef                         (IORef, newIORef, readIORef, modifyIORef')
import           Language.Fixpoint.Types.Config     (Config)
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.Types.Solutions  as Sol
import qualified Language.Fixpoint.Types.Visitor    as V
import           Language.Fixpoint.Solver.Monad     (SolveM, WDrop(..), getWDrops, filterValid, smtEnablembqi)
import           Language.Fixpoint.Smt.Interface    (qeMany)
import qualified Language.Fixpoint.Solver.Solution  as So

-- | A reclaimed qualifier: a k-var and one of its (formal-param) qualifiers.
type RQual = (F.KVar, Sol.EQual)

-- | The reclaimed set: each reclaimed qualifier tagged with the w-vars that can
--   currently save it. An association list (qualifiers lack a 'Hashable'
--   instance, and the set is small).
type Reclaimed = [(RQual, S.HashSet F.WVar)]

-- | Identity of a reclaimed qualifier (for dedup/comparison), using the
--   instantiated predicate which /is/ hashable/comparable.
rqKey :: RQual -> (F.KVar, F.Expr)
rqKey (k, eq) = (k, Sol.eqPred eq)

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
  -- The WP checks below are quantified; MBQI must be on (the preamble disables
  -- it for the QF Phase-1 checks).
  smtEnablembqi
  -- Seed the reclaimed set from the recorded drops (deduped, savers unioned).
  let seed = M.elems $ M.fromListWith mrg
               [ (rqKey (wdKVar d, wdEQual d), ((wdKVar d, wdEQual d), S.fromList (wdWVars d)))
               | d <- drops ]
      mrg (rq, ws1) (_, ws2) = (rq, S.union ws1 ws2)
  -- Run the reclaimed-qualifier fixpoint: keep only qualifiers that survive
  -- every constraint where their k-var is a head, via LHS or a saving w-var.
  reclaimed <- fixReclaimed seed
  -- Report: per failing head, per w-var, the WP for the reclaimed qualifiers
  -- that w-var still saves and that make the head valid. The subset search can
  -- backtrack; bound it by a solver-call budget so a hard head (e.g. over
  -- uninterpreted functions) can never blow up (this only affects the
  -- diagnostic, never the verdict).
  budget <- liftIO (newIORef (2000 :: Int))
  cands <- reportCandidates budget reclaimed
  -- Simplify each WP conjunct with QE (fresh context; best-effort).
  let ws0 = map fst cands
      es0 = map snd cands
  es1 <- liftIO $ qeMany cfg es0
  let perWVar = M.fromListWith (++) [ (w, [e]) | (w, e) <- zip ws0 es1 ]
  return $ M.map mkFix perWVar
  where
    be = F.bs fi
    cm = F.cm fi
    cs = M.elems cm

    -- constraints where kvar @k@ appears as a head (RHS), with the head's
    -- substitution so we can instantiate a formal-param qualifier there.
    headConstraints :: F.KVar -> [(F.SimpC a, F.Subst, F.TyVarSubst)]
    headConstraints k =
      [ (c, su, tvsu) | c <- cs, (k', su, tvsu) <- rhsKSubs (F.crhs c), k' == k ]

    ----------------------------------------------------------------------------
    -- The reclaimed-qualifier fixpoint (monotone: only shrinks).
    ----------------------------------------------------------------------------
    -- The saver-survival check depends only on the fixed final solution and the
    -- constraints (not on the reclaimed set), so a single pass already reaches
    -- the fixpoint -- no iteration needed.
    fixReclaimed :: Reclaimed -> SolveM a Reclaimed
    fixReclaimed = stepReclaimed

    -- one pass: re-check every reclaimed qualifier against its k-var's head
    -- constraints, shrinking savers / dropping qualifiers.
    --
    -- The survival check uses the /real/ final solution for the LHS (not one
    -- enhanced with the reclaimed qualifiers): the reclaimed set as a whole is a
    -- union of possibilities from different w-vars and can be inconsistent, which
    -- would make an enhanced LHS false and vacuously "imply" everything.
    stepReclaimed :: Reclaimed -> SolveM a Reclaimed
    stepReclaimed r = do
      updated <- mapM (recheck sFinal) r
      return [ (rq, ws) | (rq, ws) <- updated, not (S.null ws) ]

    -- re-check a single reclaimed qualifier across all its head-constraints
    recheck :: Sol.Solution -> (RQual, S.HashSet F.WVar)
            -> SolveM a (RQual, S.HashSet F.WVar)
    recheck sol (rq@(k, _), ws0) = do
      ws' <- foldM (survive sol rq) ws0 (headConstraints k)
      return (rq, ws')

    -- shrink the saver set for @(k, eq)@ against one head-constraint @c'@.
    survive :: Sol.Solution -> RQual -> S.HashSet F.WVar
            -> (F.SimpC a, F.Subst, F.TyVarSubst) -> SolveM a (S.HashSet F.WVar)
    survive sol (_, eq) ws (c', su, tvsu) = do
      let qHead = instantiate su tvsu eq        -- Q at this head's args
          lhs   = So.lhsPred cfg scope F.emptyIBindEnv be sol c'
      impl <- isValid (cstrSpan c') lhs qHead
      if impl
        then return ws                          -- LHS proves it: all savers OK here
        else S.fromList <$>                     -- else keep only w-vars that can prove it
               filterM (\w -> canSave w c' lhs qHead) (S.toList ws)

    -- can w-var @w@ prove @qHead@ on @c'@? It must guard @c'@ (occur in its LHS)
    -- can w-var @w@ prove @qHead@ on @c'@? It must guard @c'@ (occur in its LHS)
    -- and its WP there must be non-vacuous. We eliminate the WP's quantifier with
    -- QE first so the satisfiability check is quantifier-free (fast) instead of
    -- relying on MBQI, which is ~0.5s per quantified query.
    canSave :: F.WVar -> F.SimpC a -> F.Expr -> F.Expr -> SolveM a Bool
    canSave w c' lhs qHead
      | not (w `guards` c') = return False
      | otherwise           = do
          let (wp, dom) = mkWP w c' lhs qHead
          -- Non-vacuity is decided by eliminating the WP's quantifier (QE) and a
          -- cheap quantifier-free satisfiability check. For WPs over uninterpreted
          -- functions QE is both slow and usually cannot eliminate the
          -- quantifier, so we skip it and conservatively keep the saver (whether
          -- the solution really fixes a head is re-checked at report time).
          if hasApp wp then return True else do
            wp' <- liftIO (qe1 wp)
            if hasQuant wp' then return True
                            else satisfiable (F.pAnd [wp', dom])

    -- QE a single formula (fresh Z3 context); returns it unchanged on failure.
    qe1 :: F.Expr -> IO F.Expr
    qe1 e = do es <- qeMany cfg [e]
               return (case es of (x:_) -> x; [] -> e)

    guards :: F.WVar -> F.SimpC a -> Bool
    guards w c' = F.wvarKVar w `elem` V.envKVars be c'


    ----------------------------------------------------------------------------
    -- Reporting
    ----------------------------------------------------------------------------
    -- For each failing head and w-var, the WP conjuncts (with domain) for the
    -- reclaimed qualifiers that w-var saves and that make the head valid. We
    -- accept a set of qualifiers for @(h, w)@ only if adding them to their
    -- k-vars makes @h@ valid (non-vacuously).
    -- For each failing head and w-var, find a consistent subset of the
    -- qualifiers that w saves (for k-vars in the head's LHS) that makes the head
    -- valid; report the WP for each qualifier in that subset. Consistency: we
    -- add a qualifier only if it keeps the enhanced LHS satisfiable (so we never
    -- "prove" the head by making a k-var contradictory).
    reportCandidates :: IORef Int -> Reclaimed -> SolveM a [(F.WVar, F.Expr)]
    reportCandidates budget r = fmap concat $ forM' failCs $ \h ->
      fmap concat $ forM' (allWVars r) $ \w -> do
        let hKs   = V.envKVars be h
            quals = [ (k, eq) | ((k, eq), ws) <- r, S.member w ws, k `elem` hKs ]
        core <- growHead budget h [] quals
        return [ (w, wp) | (k, eq) <- core, (wp, _) <- wpAt w k eq ]

    -- greedily grow a consistent qualifier set that proves head @h@; [] if none
    -- (or the budget is exhausted). Add a candidate only if it keeps the
    -- enhanced LHS satisfiable, and stop as soon as the head is valid.
    growHead :: IORef Int -> F.SimpC a -> [RQual] -> [RQual] -> SolveM a [RQual]
    growHead budget h acc rest = do
      n <- liftIO (readIORef budget)
      if n <= 0 then return [] else do
        done <- tick >> headValid h acc
        if done then return acc else go rest
      where
        tick = liftIO (modifyIORef' budget (subtract 1))
        go []       = return []
        go (q:rest') = do
          ok <- tick >> headLhsSat h (acc ++ [q])
          if ok then do r <- growHead budget h (acc ++ [q]) rest'
                        if null r then go rest' else return r
                else go rest'

    -- is the enhanced LHS of @h@ (k-vars augmented by @qs@) satisfiable?
    headLhsSat :: F.SimpC a -> [RQual] -> SolveM a Bool
    headLhsSat h qs =
      satisfiable (So.lhsPred cfg scope F.emptyIBindEnv be (addQuals qs) h)

    -- does @h@'s head hold under the enhancement by @qs@?
    headValid :: F.SimpC a -> [RQual] -> SolveM a Bool
    headValid h qs
      | null qs   = return False
      | otherwise =
          isValid (cstrSpan h)
                  (So.lhsPred cfg scope F.emptyIBindEnv be (addQuals qs) h)
                  (F.crhs h)

    addQuals :: [RQual] -> Sol.Solution
    addQuals qs = foldr (\(k, eq) -> addEQual k eq) sFinal qs

    -- WP of w for qualifier @(k, eq)@ at every head-constraint of k that w
    -- guards (conjoined isn't needed here; each is a separate reported conjunct).
    wpAt :: F.WVar -> F.KVar -> Sol.EQual -> [(F.Expr, F.Expr)]
    wpAt w k eq =
      [ mkWP w c' (So.lhsPred cfg scope F.emptyIBindEnv be sFinal c') (instantiate su tvsu eq)
      | (c', su, tvsu) <- headConstraints k, w `guards` c' ]

    ----------------------------------------------------------------------------
    -- Helpers
    ----------------------------------------------------------------------------

    -- instantiate a formal-param qualifier at a head's actual arguments.
    instantiate :: F.Subst -> F.TyVarSubst -> Sol.EQual -> F.Expr
    instantiate su tvsu eq =
      case So.qbPreds su tvsu (Sol.QB [eq]) of
        ((p, _):_) -> p
        []         -> F.PTrue

    -- | The weakest precondition for w-var @w@ to prove @qHead@ given @lhs@ on
    --   constraint @c'@: universally quantify every variable of @lhs => qHead@
    --   that is not one of @w@'s arguments (alpha-renamed fresh to avoid capture).
    --   Returns @(wp, domain)@ where domain = lhs (for the non-vacuity check).
    mkWP :: F.WVar -> F.SimpC a -> F.Expr -> F.Expr -> (F.Expr, F.Expr)
    mkWP w c' lhs qHead =
      let body   = F.PImp lhs qHead
          wargs  = wvarArgSyms w c'
          qvars  = [ (x, t) | (x, t) <- binderSorts c'
                            , x `S.member` F.exprSymbolsSet body
                            , not (x `S.member` wargs) ]
          su     = F.mkSubst [ (x, F.eVar (fresh x)) | (x, _) <- qvars ]
          qvars' = [ (fresh x, t) | (x, t) <- qvars ]
          wp     = if null qvars' then body else F.PAll qvars' (F.subst su body)
      in  (wp, lhs)

    fresh :: F.Symbol -> F.Symbol
    fresh x = F.suffixSymbol x (F.symbol "wvq")

    addEQual :: F.KVar -> Sol.EQual -> Sol.Solution -> Sol.Solution
    addEQual k eq s = s { Sol.sMap = M.adjust add k (Sol.sMap s) }
      where add (Sol.QB eqs) = Sol.QB (eq : eqs)

    isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM a Bool
    isValid sp p q = not . null <$> filterValid sp p [(q, ())]

    -- | @phi@ satisfiable  <=>  @phi => false@ is not valid, i.e. filterValid
    --   returns no survivors.
    satisfiable :: F.Expr -> SolveM a Bool
    satisfiable phi = null <$> filterValid F.dummySpan phi [(F.PFalse, ())]

    mkFix :: [F.Expr] -> F.WVarFix
    mkFix conjs = F.WVarFix { F.wfSolution = F.pAnd cs', F.wfDrops = cs' }
      where cs' = L.nub conjs

    allWVars :: Reclaimed -> [F.WVar]
    allWVars = L.nub . concatMap (S.toList . snd)

    forM' :: [b] -> (b -> SolveM a c) -> SolveM a [c]
    forM' xs f = mapM f xs

    cstrSpan :: F.SimpC a -> F.SrcSpan
    cstrSpan = F.srcSpan . F.sinfo

    -- | Symbols that appear as arguments to occurrences of @w@ in @c'@.
    wvarArgSyms :: F.WVar -> F.SimpC a -> S.HashSet F.Symbol
    wvarArgSyms w c' = S.fromList
      [ y
      | (_, sr) <- envBinds c'
      , F.PKVar k _ su <- kvarApps (F.reftPred (F.sr_reft sr))
      , k == F.wvarKVar w
      , e <- M.elems (F.fromKVarSubst su)
      , y <- S.toList (F.exprSymbolsSet e) ]

    binderSorts :: F.SimpC a -> [(F.Symbol, F.Sort)]
    binderSorts c' = [ (x, F.sr_sort sr) | (x, sr) <- envBinds c' ]

    envBinds :: F.SimpC a -> [(F.Symbol, F.SortedReft)]
    envBinds c' =
      [ (x, sr) | i <- F.elemsIBindEnv (F.senv c')
                , let (x, sr, _) = F.lookupBindEnv i be ]

-- | K-vars on the RHS (head) with their substitutions.
rhsKSubs :: F.Expr -> [(F.KVar, F.Subst, F.TyVarSubst)]
rhsKSubs (F.PAnd ps)         = concatMap rhsKSubs ps
rhsKSubs (F.PKVar k tvsu su) = [(k, F.substFromKSubst su, tvsu)]
rhsKSubs _                   = []

-- | Does the expression contain a quantifier?
hasQuant :: F.Expr -> Bool
hasQuant = anyExpr q where q (F.PAll _ _) = True; q (F.PExist _ _) = True; q _ = False

-- | Does the expression contain a (non-nullary) function application?
hasApp :: F.Expr -> Bool
hasApp = anyExpr q where q (F.EApp _ _) = True; q _ = False

-- | Is the predicate @p@ true of the expression or any subexpression?
anyExpr :: (F.Expr -> Bool) -> F.Expr -> Bool
anyExpr p = go
  where
    go e | p e = True
    go e = case e of
      F.PAll _ b    -> go b
      F.PExist _ b  -> go b
      F.PAnd xs     -> any go xs
      F.POr xs      -> any go xs
      F.PNot x      -> go x
      F.PImp a b    -> go a || go b
      F.PIff a b    -> go a || go b
      F.PAtom _ a b -> go a || go b
      F.EBin _ a b  -> go a || go b
      F.ENeg x      -> go x
      F.EApp a b    -> go a || go b
      F.ECst x _    -> go x
      F.EIte a b c  -> go a || go b || go c
      _             -> False

-- | Collect the @PKVar@ conjuncts of an expression.
kvarApps :: F.Expr -> [F.Expr]
kvarApps = go
  where
    go (F.PAnd ps)    = concatMap go ps
    go e@(F.PKVar {}) = [e]
    go _              = []
