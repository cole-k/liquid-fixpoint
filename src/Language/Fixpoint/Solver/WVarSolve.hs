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
import           Language.Fixpoint.Types.Config     (Config)
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.Types.Solutions  as Sol
import           Language.Fixpoint.Solver.Monad     (SolveM, WDrop(..), getWDrops)
import qualified Language.Fixpoint.Solver.Solution  as So

--------------------------------------------------------------------------------
-- | Build candidate w-var solutions from the drops captured during Phase 1.
--   Runs inside 'SolveM' (after refinement) but needs no SMT queries itself --
--   it is pure term construction over the final solution.
--------------------------------------------------------------------------------
solveWVars
  :: forall a. (F.Loc a)
  => Config
  -> S.HashSet F.Symbol            -- ^ scope
  -> F.SInfo a
  -> Sol.Solution                  -- ^ final solution
  -> SolveM a F.WVarResult
solveWVars cfg scope fi sFinal = do
  drops <- getWDrops
  let perWVar = M.fromListWith (++)
        [ (w, [wpOfDrop d]) | d <- drops, w <- wdWVars d ]
  return $ M.map mkFix perWVar
  where
    be = F.bs fi
    cm = F.cm fi

    mkFix :: [F.Expr] -> F.WVarFix
    mkFix conjs =
      F.WVarFix { F.wfSolution = F.pAnd (L.nub conjs)
                , F.wfDrops    = L.nub conjs }

    -- | The WP conjunct for a single recorded drop.
    wpOfDrop :: WDrop -> F.Expr
    wpOfDrop (WDrop _ cid _ qHead) =
      case M.lookup cid cm of
        Nothing -> F.PTrue
        Just c  ->
          let lhs    = So.lhsPred cfg scope F.emptyIBindEnv be sFinal c
              body   = F.PImp lhs qHead
              -- variables the w-var "sees": the args of every weak occurrence in c
              wargs  = wvarArgSyms c
              -- quantify everything free in body that is not a w-var argument,
              -- restricting to symbols that are actually binders of c (so we
              -- have their sorts and don't accidentally bind constants).
              qsorts = [ (x, t)
                       | (x, t) <- binderSorts c
                       , x `S.member` F.exprSymbolsSet body
                       , not (x `S.member` wargs) ]
          in  if null qsorts then body else F.PAll qsorts body

    -- | Symbols that appear as arguments to a weak k-var occurrence in @c@'s
    --   environment -- the variables the w-var is allowed to keep free.
    wvarArgSyms :: F.SimpC a -> S.HashSet F.Symbol
    wvarArgSyms c = S.fromList
      [ y
      | (_, sr) <- envBinds c
      , F.PKVar k _ su <- kvarApps (F.reftPred (F.sr_reft sr))
      , S.member (F.kvarWVar k) (F.wVars fi)
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
