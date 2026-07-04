{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}

--------------------------------------------------------------------------------
-- | Rescue analysis for w-variables (weak k-vars).
--
-- After the standard fixpoint has run with every (body-only) w-var pinned to
-- @true@ (Phase 1), some concrete heads may fail because pinning a w-var to
-- @true@ over-constrained the k-vars in its body. This module answers, for each
-- such failing head, the diagnostic question:
--
--   /which qualifiers, stripped from the k-vars during Phase 1, would -- if/
--   /added back -- make this head valid again, and which w-var(s) are/
--   /responsible for them?/
--
-- It does NOT compute an actual solution for the w-var (that requires
-- weakest-precondition reasoning, because a rescued qualifier and the w-var
-- generally live in different variable scopes). It only reports the rescued
-- qualifiers and responsible w-vars; working backwards to a solution is left to
-- a later phase.
--
-- The rescued qualifiers are obtained by comparing the /initial/ candidate set
-- for each k-var (the fully-instantiated "top" from @Solution.init@) with the
-- /final/ solved set: their difference is everything that was stripped. We then
-- (a) check that re-adding all of them proves the head, and (b) greedily shrink
-- to a near-minimal subset that still proves it.
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.WVarSolve
  ( rescueWVars
  ) where

import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S
import qualified Data.List                          as L
import qualified Language.Fixpoint.Types            as F
import qualified Language.Fixpoint.Types.Solutions  as Sol
import qualified Language.Fixpoint.Types.Visitor    as V
import           Language.Fixpoint.Types.Config     (Config)
import           Language.Fixpoint.Solver.Monad     (SolveM, filterValid)
import qualified Language.Fixpoint.Solver.Solution  as So
import qualified Language.Fixpoint.Solver.WVar      as WVar

--------------------------------------------------------------------------------
-- | For every failing concrete constraint, compute the candidate w-var
--   fixes (rescued qualifiers + responsible w-vars). Runs inside 'SolveM',
--   reusing the live SMT context.
--
--   @s0@ is the /initial/ solution (before refinement), @sFinal@ the solved
--   one; @failing@ are the constraint ids reported Unsafe.
--------------------------------------------------------------------------------
rescueWVars
  :: forall a. (F.Loc a)
  => Config
  -> S.HashSet F.Symbol            -- ^ scope
  -> F.IBindEnv                    -- ^ bindings already known to SMT
  -> F.SInfo a
  -> Sol.Solution                  -- ^ initial solution (pre-refine)
  -> Sol.Solution                  -- ^ final solution
  -> [F.SubcId]                    -- ^ failing constraint ids
  -> SolveM a F.WVarResult
rescueWVars cfg scope bindingsInSmt fi s0 sFinal failing
  | S.null bodyWs = return mempty
  | otherwise     = do
      fixes <- mapM tryRescue failing
      return $ M.fromList [ (i, [fx]) | (i, Just fx) <- zip failing fixes ]
  where
    bodyWs   = WVar.bodyOnlyWVars fi
    be       = F.bs fi
    cm       = F.cm fi

    -- qualifiers stripped from each k-var over the whole run
    strippedOf :: F.KVar -> [Sol.EQual]
    strippedOf k =
      let ini = equals (Sol.lookupQBind s0 k)
          fin = equals (Sol.lookupQBind sFinal k)
      in  [ e | e <- ini, e `notElem` fin ]

    -- attempt to rescue a single failing constraint
    tryRescue :: F.SubcId -> SolveM a (Maybe F.WVarFix)
    tryRescue i =
      case M.lookup i cm of
        Nothing -> return Nothing
        Just c  -> do
          let lhsKs    = L.nub [ k | k <- V.envKVars be c
                                   , not (isWeak k) ]
              stripped = [ (k, e) | k <- lhsKs, e <- strippedOf k ]
          if null stripped
            then return Nothing
            else do
              -- Does re-adding *all* stripped quals make the head valid?
              okAll <- headHolds c (map snd stripped)
              if not okAll
                then return Nothing
                else do
                  core  <- minimizeCore c stripped
                  let ws = responsibleWVars (map fst core)
                  return $ Just F.WVarFix
                    { F.wfWVars   = S.toList ws
                    , F.wfRescued = Sol.eqPred . snd <$> core
                    }

    -- | Does @c@'s head hold when the LHS is enhanced by re-adding @extra@
    --   qualifiers to the k-vars they were stripped from?
    headHolds :: (F.Loc a) => F.SimpC a -> [Sol.EQual] -> SolveM a Bool
    headHolds c extra = do
      let sEnh = enhance extra
          lhs  = So.lhsPred cfg scope bindingsInSmt be sEnh c
          rhs  = F.crhs c
      valid (F.srcSpan (F.sinfo c)) lhs rhs

    -- | Enhance the final solution by adding the given EQuals back to whatever
    --   k-var each one belongs to. We recompute per-kvar membership from the
    --   stripped sets so the EQual lands on the right k-var.
    --
    --   NOTE (v1 limitations): (1) only cut k-vars (those in @sMap@) are
    --   enhanced; non-cut/hypothesis k-vars are left as-is. (2) if the same
    --   qualifier was stripped from several k-vars it is re-added to all of
    --   them. Both only make the enhanced LHS stronger, so the head-proving
    --   check stays sound as a "could this be recovered" test.
    enhance :: [Sol.EQual] -> Sol.Solution
    enhance extra = sFinal { Sol.sMap = M.mapWithKey add (Sol.sMap sFinal) }
      where
        addMap = M.fromListWith (++)
                   [ (k, [e]) | k <- allKs, e <- strippedOf k, e `elem` extra ]
        allKs  = M.keys (Sol.sMap sFinal)
        add k (Sol.QB eqs) =
          Sol.QB (eqs ++ M.lookupDefault [] k addMap)

    -- | Greedily drop qualifiers from the rescued set while the head still
    --   holds -- a cheap approximation of an unsat core. Starts from the full
    --   set (already known to prove the head) and removes one at a time.
    --
    --   NOTE: this is order-dependent and only near-minimal; a genuine unsat
    --   core (fewest w-vars, alternative bundles) is future work.
    minimizeCore
      :: (F.Loc a)
      => F.SimpC a -> [(F.KVar, Sol.EQual)] -> SolveM a [(F.KVar, Sol.EQual)]
    minimizeCore c = go []
      where
        -- @kept@: already-decided-necessary; @rest@: still to consider.
        go kept []             = return kept
        go kept (x:rest)       = do
          -- try to drop x: does the head still hold with kept ++ rest?
          ok <- headHolds c (map snd (kept ++ rest))
          if ok then go kept rest        -- x was redundant, drop it
                else go (kept ++ [x]) rest  -- x is needed, keep it

    -- w-vars responsible for the rescued k-vars: a body-only w-var is deemed
    -- responsible if it guards some constraint whose k-var footprint (body or
    -- head) touches one of the rescued k-vars.
    responsibleWVars :: [F.KVar] -> S.HashSet F.WVar
    responsibleWVars ks =
      let kset = S.fromList ks
      in  S.fromList
            [ w
            | w <- S.toList bodyWs
            , any (guardsAndTouches w kset) (M.elems cm)
            ]

    guardsAndTouches :: F.WVar -> S.HashSet F.KVar -> F.SimpC a -> Bool
    guardsAndTouches w kset c =
      let bodyk = V.envKVars be c
          allk  = bodyk ++ V.rhsKVars c
      in  (F.wvarKVar w `elem` bodyk)
          && any (`S.member` kset) (filter (not . isWeak) allk)

    isWeak k = S.member (F.kvarWVar k) (F.wVars fi)

    valid sp p q = not . null <$> filterValid sp p [(q, ())]

    equals :: Sol.QBind -> [Sol.EQual]
    equals (Sol.QB eqs) = eqs
