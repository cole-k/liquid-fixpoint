--------------------------------------------------------------------------------
-- | Support for "w-variables" (weak k-vars).
--
-- A w-var is an unknown predicate (represented in the AST exactly like a k-var,
-- i.e. as a 'F.PKVar' node) that is declared via @(wvar ...)@ and recorded in
-- @F.wVars@. Semantically it should be solved to the /weakest/ value that keeps
-- the system satisfiable; the standard fixpoint instead treats it as @true@,
-- which may over-constrain k-vars and cause a head to fail.
--
-- This module contains the pieces that are shared across the solver:
--
--   * classification of w-vars by where they occur (only in bodies, only in
--     heads, or both);
--   * elision of "only-head" w-vars, which are never consulted and so can be
--     made to disappear entirely;
--   * the set of "only-body" w-vars, which are the ones the actual w-var
--     machinery (seed-to-true in Phase 1, rescue analysis afterwards) acts on.
--
-- The distinction between a weak k-var and an ordinary one is drawn /solely/ by
-- membership in @F.wVars@; everywhere else a w-var is treated exactly like a
-- k-var, which is correct precisely because an "only-body" w-var never appears
-- as a head and so is never refined.
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.WVar
  ( WVarClass (..)
  , classifyWVars
  , bodyOnlyWVars
  , elideOnlyHeadWVars
  ) where

import qualified Data.HashMap.Strict            as M
import qualified Data.HashSet                   as S
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Visitor as V

--------------------------------------------------------------------------------
-- | How the declared w-vars occur in the constraints.
--
-- A w-var is expected (in the non-edge-case) to occur either only in body
-- position or only in head position. The @both@ case does arise (e.g. for
-- w-vars coming from recursive functions); it is not handled here beyond being
-- reported, and such w-vars are left to behave like ordinary k-vars.
--------------------------------------------------------------------------------
data WVarClass = WVarClass
  { wcBodyOnly :: !(S.HashSet F.WVar)  -- ^ occur in some body, in no head
  , wcHeadOnly :: !(S.HashSet F.WVar)  -- ^ occur in some head, in no body
  , wcBoth     :: !(S.HashSet F.WVar)  -- ^ occur in both positions (edge case)
  }

--------------------------------------------------------------------------------
classifyWVars :: F.SInfo a -> WVarClass
--------------------------------------------------------------------------------
classifyWVars si = WVarClass
  { wcBodyOnly = bodyWs `S.difference` headWs
  , wcHeadOnly = headWs `S.difference` bodyWs
  , wcBoth     = bodyWs `S.intersection` headWs
  }
  where
    ws      = F.wVars si
    be      = F.bs si
    cs      = M.elems (F.cm si)
    -- restrict occurrence scans to the declared w-vars
    keep ks = S.fromList [ F.kvarWVar k | k <- ks, F.kvarWVar k `S.member` ws ]
    bodyWs  = S.unions [ keep (V.envKVars be c) | c <- cs ]
    headWs  = S.unions [ keep (V.rhsKVars c)    | c <- cs ]

-- | The "only-body" w-vars: the ones the w-var machinery actually operates on.
bodyOnlyWVars :: F.SInfo a -> S.HashSet F.WVar
bodyOnlyWVars = wcBodyOnly . classifyWVars

--------------------------------------------------------------------------------
-- | Make every "only-head" w-var disappear.
--
-- An only-head w-var is never read anywhere, so a constraint @L => $w(x)@ is
-- trivially satisfiable and imposes no observable obligation. We drop the w-var
-- occurrences from constraint heads (a head that becomes @PAnd []@ i.e. @true@
-- is then ignored by the worklist's existing tautology filtering) and remove
-- the w-var from @ws@/@wVars@ so it leaves no trace in the solution.
--------------------------------------------------------------------------------
elideOnlyHeadWVars :: F.SInfo a -> F.SInfo a
elideOnlyHeadWVars si
  | S.null headOnly = si
  | otherwise       = si
      { F.cm    = stripRhs <$> F.cm si
      , F.ws    = M.filterWithKey (\k _ -> not (isHeadOnly k)) (F.ws si)
      , F.wVars = F.wVars si `S.difference` headOnly
      }
  where
    headOnly        = wcHeadOnly (classifyWVars si)
    headOnlyKs      = S.map F.wvarKVar headOnly
    isHeadOnly k    = S.member k headOnlyKs
    stripRhs c      = c { F._crhs = dropKs (F.crhs c) }
    -- remove only-head-w-var PKVar conjuncts from a (possibly conjunctive) RHS
    dropKs e        = F.pAnd [ p | p <- F.conjuncts e, not (isHeadOnlyKVar p) ]
    isHeadOnlyKVar (F.PKVar k _ _) = isHeadOnly k
    isHeadOnlyKVar _               = False
