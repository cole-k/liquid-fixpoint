{-# LANGUAGE PatternGuards     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

--------------------------------------------------------------------------------
-- | Solve a system of horn-clause constraints ---------------------------------
--------------------------------------------------------------------------------

module Language.Fixpoint.Solver.Solve (solve) where

import           Control.Monad (forM, when, filterM)
import           Control.Monad.Reader
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Misc            as Misc
import qualified Language.Fixpoint.Types           as F
import qualified Language.Fixpoint.Types.Solutions as Sol
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Config hiding (stats)
import           Language.Fixpoint.SortCheck          (ElabParam(..), elaborate)
import           Language.Fixpoint.Solver.Sanitize (symbolEnv)
import qualified Language.Fixpoint.Solver.Solution  as S
import qualified Language.Fixpoint.Smt.Types as T
import qualified Language.Fixpoint.Solver.Worklist  as W
import qualified Language.Fixpoint.Solver.Eliminate as E
import qualified Language.Fixpoint.Types.Visitor as V
import           Language.Fixpoint.Types.Visitor (isConcC)
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Utils.Progress
import           Language.Fixpoint.Utils.Files (Ext (KVars, Sccs))
import           Language.Fixpoint.Graph
import           Text.PrettyPrint.HughesPJ
import           Text.Printf
import           Language.Fixpoint.Verbosity
import           Control.DeepSeq
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
-- import qualified Data.Maybe          as Mb
import qualified Data.List           as L
import Language.Fixpoint.Types (resStatus, FixResult(Unsafe))
import Language.Fixpoint.Smt.Interface (smtComment)
import Language.Fixpoint.Solver.Interpreter (instInterpreter)
import qualified Language.Fixpoint.Solver.PLE as PLE      (instantiate)
import Data.Maybe (maybeToList)
import System.IO (hFlush, stdout)

mytrace :: String -> a -> a
mytrace
  -- s x = trace s x
  _ x = x
{-
solve_ :: (NFData a, F.Fixpoint a, F.Loc a)
       => Config
       -> F.SInfo a
       -> Sol.Solution
       -> W.Worklist a
       -> SolveM a (F.Result (Integer, a), Stats)
       -}
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
solve
  :: forall a. (NFData a, F.Fixpoint a, Show a, F.Loc a)
  => Config -> ElabParam -> S.HashSet F.Symbol -> F.SInfo a -> IO (F.Result (Integer, a))
--------------------------------------------------------------------------------

solve cfg elabParam scope fi = do
    tracePhase cfg "classify KVars and initialize worklist"
    dumpKVars cfg sI
    dumpSccGraph cfg sI
    tracePhase cfg "initialize SMT and start refinement"
    vb <- getVerbosity
    (res, stat) <- (if Quiet == vb then id else withProgressFI sI) $ runSolverM cfg sI elabParam act
    tracePhase cfg "solver complete"
    when (solverStats cfg) $ printStats fi wkl stat
    -- print (numIter stat)
    return res
  where
    act :: SolveM a (F.Result (Integer, a), Stats)
    act = do
      ctx <- getContext
      let sEnv = symbolEnv cfg fi
          s1 = s0{Sol.sMap = M.map (elabQBind ctx "solve" sEnv) (Sol.sMap s0)}
      solve_ cfg scope fi s1 wkl
    -- solverInfo computes the set of cut and non-cut kvars, then initializes
    -- the solutions of the non-cut KVars (in the sHyp field)
    --
    -- S.init provides an initial solution for the cut KVars
    sI  = solverInfo cfg fi
    wkl = W.init sI
    s0  = (siSol sI)
      { Sol.sMap = M.union forced (S.init cfg fi (S.difference ks forcedKs))
      , Sol.sHyp = M.filterWithKey (\k _ -> not (S.member k forcedKs)) (Sol.sHyp (siSol sI))
      }
    forced = M.fromList [(k, Sol.QB [Sol.trueEqual]) | k <- S.toList forcedKs]
    forcedKs = S.filter (\k -> F.kv k `S.member` forcedNames) (S.fromList (M.keys (F.ws fi)))
    forcedNames = S.fromList (forceKVars cfg)
    ks  = siVars sI
    elabQBind ctx msg env (Sol.QB xs) = Sol.QB (map elabEQual xs)
      where
        elabEQual eq =
          eq { Sol.eqPred =
                elaborate
                 (ElabParam (T.ctxElabF ctx) (F.atLoc F.dummySpan msg) env)
                 (Sol.eqPred eq)
              }

dumpKVars :: Config -> SolverInfo a -> IO ()
dumpKVars cfg sI = when (dumpKvars cfg) $ do
  let file = queryFile KVars cfg
      cuts = S.toList (siVars sI)
      nonCuts = M.keys (Sol.sHyp (siSol sI))
      contents = unlines
        (["cut " ++ show k | k <- cuts] ++ ["non-cut " ++ show k | k <- nonCuts])
  ensurePath file
  putStrLn $ "Saving KVar classification: " ++ file
  writeFile file contents
  hFlush stdout

dumpSccGraph :: Config -> SolverInfo a -> IO ()
dumpSccGraph cfg sI = do
  traceSccs cfg sI
  when (dumpSccs cfg) $ do
    let file = queryFile Sccs cfg
    ensurePath file
    putStrLn $ "Saving SCC dependency graph: " ++ file
    writeFile file (sccGraph sI)
    hFlush stdout

traceSccs :: Config -> SolverInfo a -> IO ()
traceSccs cfg sI = when (traceSolver cfg) $ do
  let sccs = sccConstraints sI
  putStrLn $ "  SCC scheduler: " ++ show (cNumScc (siDeps sI)) ++ " ranks; "
    ++ show (length sccs) ++ " contain worklist constraints"
  mapM_ putStrLn
    [ "  SCC " ++ show number ++ " (rank " ++ show rank ++ "): " ++ show (length cs) ++ " constraints, "
        ++ show (S.size ks) ++ " KVars"
    | (number, (rank, cs)) <- zip [1 :: Int ..] sccs
    , let ks = sccKVars cs
    ]

sccGraph :: SolverInfo a -> String
sccGraph sI = unlines $
  ["digraph SCCs {", "  rankdir=LR;"]
  ++ concat
    [ [ "  subgraph cluster_" ++ show number ++ " {"
      , "    label=\"SCC " ++ show number ++ " (rank " ++ show rank ++ "): " ++ show (length cs)
          ++ " constraints, " ++ show (S.size ks) ++ " KVars\";"
      ]
      ++ ["    " ++ kvarNode k ++ ";" | k <- L.sortOn show (S.toList ks)]
      ++ ["  }"]
    | (number, (rank, cs)) <- zip [1 :: Int ..] (sccConstraints sI)
    , let ks = sccKVars cs
    ]
  ++ [ "  " ++ kvarNode from ++ " -> " ++ kvarNode to ++ ";"
     | (from, to) <- kvarEdges sI
     , S.member from refinementKVars
     , S.member to refinementKVars
     ]
  ++ ["}"]
  where
    refinementKVars = S.unions [sccKVars cs | (_, cs) <- sccConstraints sI]

sccConstraints :: SolverInfo a -> [(Int, [F.SimpC a])]
sccConstraints sI =
  [ (rank, cs)
  | (rank, cs) <- L.sortOn fst (M.toList grouped)
  ]
  where
    query = siQuery sI
    grouped = M.fromListWith (++)
      [ (rScc (lookupCMap (cRank (siDeps sI)) i), [c])
      | (i, c) <- M.toList (F.cm query)
      , not (isConcC c)
      ]

sccKVars :: [F.SimpC a] -> S.HashSet F.KVar
sccKVars = S.fromList . concatMap V.rhsKVars

kvarEdges :: SolverInfo a -> [(F.KVar, F.KVar)]
kvarEdges sI = S.toList . S.fromList $
  [ (input, output)
  | c <- M.elems (F.cm query)
  , output <- V.rhsKVars c
  , input <- V.envKVars (F.bs query) c
  ]
  where
    query = siQuery sI

kvarNode :: F.KVar -> String
kvarNode k = "\"" ++ concatMap escape (show k) ++ "\""
  where
    escape '\"' = "\\\""
    escape '\\' = "\\\\"
    escape c    = [c]

tracePhase :: Config -> String -> IO ()
tracePhase cfg phase = when (traceSolver cfg) $ startPhase Misc.Loud phase >> hFlush stdout

--------------------------------------------------------------------------------
-- | Progress Bar
--------------------------------------------------------------------------------
withProgressFI :: SolverInfo a -> IO b -> IO b
withProgressFI = withProgress . (+ 1) . fromIntegral . cNumScc . siDeps
--------------------------------------------------------------------------------

printStats :: F.SInfo a ->  W.Worklist a -> Stats -> IO ()
printStats fi w s = putStrLn "\n" >> ppTs [ ptable fi, ptable s, ptable w ]
  where
    ppTs          = putStrLn . showpp . mconcat

--------------------------------------------------------------------------------
solverInfo :: Config -> F.SInfo a -> SolverInfo a
--------------------------------------------------------------------------------
solverInfo cfg fI
  | useElim cfg = E.solverInfo cfg fI
  | otherwise   = SI mempty fI cD (siKvars fI)
  where
    cD          = elimDeps fI (kvEdges fI) mempty

siKvars :: F.SInfo a -> S.HashSet F.KVar
siKvars = S.fromList . M.keys . F.ws

doInterpret :: (F.Loc a) =>  Config -> F.SInfo a -> [F.SubcId] -> SolveM a (F.BindEnv a)
doInterpret cfg fi subcIds = liftIO $ instInterpreter cfg fi (Just subcIds)

--------------------------------------------------------------------------------
{-# SCC solve_ #-}
solve_ :: (NFData a, F.Fixpoint a, F.Loc a)
       => Config
       -> S.HashSet F.Symbol
       -> F.SInfo a
       -> Sol.Solution
       -> W.Worklist a
       -> SolveM a (F.Result (Integer, a), Stats)
--------------------------------------------------------------------------------
solve_ cfg scope fi s2 wkl = do
  liftSMT $ smtComment "solve: start"
  (s3, res0) <- sendConcreteBindingsToSMT F.emptyIBindEnv (F.bs fi) $ \bindingsInSmt -> do
    -- let s3   = solveEbinds fi s2
    (s3, usedNonCuts) <- {- SCC "sol-refine" -} refine scope bindingsInSmt (F.bs fi) s2 wkl
    lift $ tracePhase cfg "refinement complete; validate constraints"
    res0     <- {- SCC "sol-result" -} result scope bindingsInSmt cfg fi (W.unsatCandidates wkl) s3 usedNonCuts
    return (s3, res0)

  (fi1, res1) <- case resStatus res0 of  {- first run the interpreter -}
    Unsafe _ bads | rewriteAxioms cfg && interpreter cfg -> do
      lift $ tracePhase cfg "run interpreter"
      liftSMT $ smtComment "solve: interpreter"
      bs <- doInterpret cfg fi (map fst $ mytrace ("before the Interpreter " ++ show (length bads) ++ " constraints remain") bads)
      let fi1 = fi { F.bs = bs }
          badCs = lookupCMap (F.cm fi) <$> map fst bads
      liftSMT $ smtComment "solve: pos-interpreter check"
      fmap (fi1,) $ sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg fi1 badCs s3 mempty
    _ -> return  (fi, mytrace "all checked before interpreter" res0)

  res2  <- case resStatus res1 of  {- then run normal PLE on remaining unsolved constraints -}
    Unsafe _ bads2 | rewriteAxioms cfg -> do
      lift $ tracePhase cfg "run PLE"
      when (save cfg) $
        liftIO $ S.saveSolution cfg ".pre-ple" res1
      liftSMT $ smtComment "solve: ple"
      bs <- liftSMT $ PLE.instantiate cfg scope fi1 (Just s3) (Just $ map fst bads2)
      -- Check the constraints one last time after PLE
      let fi2 = fi { F.bs = bs }
          badsCs2 = lookupCMap (F.cm fi) <$> map fst bads2
      liftSMT $ smtComment "solve: pos-ple check"
      sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg fi2 badsCs2 s3 mempty
    _ -> return $ mytrace "all checked with interpreter" res1

  liftSMT $ smtComment "solve: finished"
  st      <- stats
  let res3 = {- SCC "sol-tidy" -} tidyResult cfg res2
  return $!! (res3, st)


--------------------------------------------------------------------------------
-- | tidyResult ensures we replace the temporary kVarArg names introduced to
--   ensure uniqueness with the original names in the given WF constraints.
--------------------------------------------------------------------------------
tidyResult :: Config -> F.Result a -> F.Result a
tidyResult _ r = r
  { F.resSolution = tidySolution (F.resSolution r)
  , F.resNonCutsSolution = M.map (fmap tidyPred) (F.resNonCutsSolution r)
  , F.resSorts = fmap tidyBind <$>  F.resSorts r
  }

tidySolution :: F.FixSolution -> F.FixSolution
tidySolution = fmap tidyPred

tidyBind :: (F.Symbol, F.Sort) -> (F.Symbol, F.Sort)
tidyBind (x, t) = (F.tidySymbol x, t)

tidyPred :: F.Expr -> F.Expr
tidyPred =  go
  where
    ts = F.tidySymbol
    tb = tidyBind
    go (F.EApp s e)      = F.EApp (go s) (go e)
    go (F.ELam (x,t) e)  = F.ELam (ts x, t) (go e)
    go (F.ECoerc a t e)  = F.ECoerc a t (go e)
    go (F.ENeg e)        = F.ENeg (go e)
    go (F.EBin op e1 e2) = F.EBin op (go e1) (go e2)
    go (F.ELet x e1 e2)  = F.ELet (ts x) (go e1) (go e2)
    go (F.EIte p e1 e2)  = F.EIte (go p) (go e1) (go e2)
    go (F.ECst e so)     = F.ECst (go e) so
    go (F.EVar x)        = F.EVar (ts x)
    go (F.PAnd ps)       = F.PAnd $ map go ps
    go (F.POr  ps)       = F.POr  $ map go ps
    go (F.PNot p)        = F.PNot $ go p
    go (F.PImp p1 p2)    = F.PImp (go p1) (go p2)
    go (F.PIff p1 p2)    = F.PIff (go p1) (go p2)
    go (F.PAtom r e1 e2) = F.PAtom r (go e1) (go e2)
    go (F.PExist xts e)  = F.PExist (tb <$> xts) (go e)
    go (F.PAll xts e)    = F.PAll   (tb <$> xts) (go e)
    go  p                = p

--------------------------------------------------------------------------------
{-# SCC refine #-}
-- | Implementation of the inference algorithm from:
--
-- "Liquid Types", PLDI 2008, https://ranjitjhala.github.io/static/liquid_types.pdf
--
refine
  :: forall a. F.Loc a
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> F.BindEnv a
  -> Sol.Solution
  -> W.Worklist a
   -> SolveM a (Sol.Solution, S.HashSet F.KVar)
--------------------------------------------------------------------------------
refine scope bindingsInSmt be0 s0 w0 = go be0 s0 w0 mempty
  where
    go :: F.BindEnv a -> Sol.Solution -> W.Worklist a -> S.HashSet F.KVar -> SolveM a (Sol.Solution, S.HashSet F.KVar)
    go be s w used
      | Just (c, w', newScc, rnk) <- W.pop w = do
          i       <- tickIter newScc
          cfg     <- T.config <$> getContext
          lift $ when (newScc && traceSolver cfg) $
            putStrLn $ "  Refining SCC rank " ++ show rnk ++ ", constraint " ++ show (F.subcId c)
          (b, s') <- refineC scope bindingsInSmt be i s c
          lift $ writeLoud $ refineMsg i c b rnk (showpp s')
          let w'' = if b then W.push c w' else w'
              used' = S.union used (S.fromList (V.envKVars be c))
          go be s' w'' used'
      | otherwise = return (s, used)
      where
        -- DEBUG
        refineMsg i c b rnk s = printf "\niter=%d id=%d change=%s rank=%d s=%s\n"
                                 i (F.subcId c) (show b) rnk s

---------------------------------------------------------------------------
-- | Single Step Refinement -----------------------------------------------
---------------------------------------------------------------------------
{-# SCC refineC #-}
refineC
  :: forall a. (F.Loc a)
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> F.BindEnv a
  -> Int
  -> Sol.Solution
  -> F.SimpC a
  -> SolveM a (Bool, Sol.Solution)
---------------------------------------------------------------------------
refineC scope bindingsInSmt be _i s c =
  do cfg <- T.config <$> getContext
     let krhs = filter (not . isForced cfg . fst) (rhsCands s)
     if all (null . snd) krhs
        then return (False, s)
        else do
          let lhs = S.lhsPred cfg scope bindingsInSmt be s c
          lift $ when (traceSolver cfg) $
            putStrLn $ "  SMT refinement check for constraint " ++ show (F.subcId c)
          kqs <- forM krhs $ \(k, rhs) ->
            (,) k . Sol.QB <$> filterValid (cstrSpan c) lhs rhs
          return $ S.update s kqs
  where
    isForced cfg' k = F.kv k `S.member` S.fromList (forceKVars cfg')
    rhsCands :: Sol.Solution -> [(F.KVar, Sol.Cand Sol.EQual)]
    rhsCands s = M.toList $ M.fromList $ map cnd ks
      where
        ks          = predKs . F.crhs $ c
        cnd :: (F.KVar, F.Subst, F.TyVarSubst) -> (F.KVar , Sol.Cand Sol.EQual)
        cnd (k, su, tvsu) = (k, S.qbPreds su tvsu (Sol.lookupQBind s k))

predKs :: F.Expr -> [(F.KVar, F.Subst, F.TyVarSubst)]
predKs (F.PAnd ps)    = concatMap predKs ps
predKs (F.PKVar k tvsu su) = [(k, F.substFromKSubst su, tvsu)]
predKs _              = []

--------------------------------------------------------------------------------
-- | Convert Solution into Result ----------------------------------------------
--------------------------------------------------------------------------------
{-# SCC result #-}
result
  :: (F.Fixpoint a, F.Loc a, NFData a)
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> Config
   -> F.SInfo a
   -> [F.SimpC a]
   -> Sol.Solution
   -> S.HashSet F.KVar
   -> SolveM a (F.Result (Integer, a))
--------------------------------------------------------------------------------
result scope bindingsInSmt cfg fi cs s usedNonCuts =
  sendConcreteBindingsToSMT bindingsInSmt be $ \bindingsInSmt2 -> do
    lift       $ writeLoud "Computing Result"
    let sCheck = if usedNonCutResult cfg then usedSolution s usedNonCuts else s
    stat      <- result_ scope bindingsInSmt2 be cfg cs sCheck
    lift       $ whenLoud $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
    if skipResultSolution cfg
      then return $ F.Result (ci <$> stat) mempty mempty mempty
      else do
        resCut <- solResult cfg s
        let resNonCut = nonCutsResult cfg scope be s usedNonCuts
            resSorts = resultSorts fi (M.keys resCut ++ M.keys resNonCut) be
        return $ F.Result (ci <$> stat) resCut resNonCut resSorts
  where
    ci c = (F.subcId c, F.sinfo c)
    be = F.bs fi

    nonCutsResult cfg' scope' be' sol used
      | usedNonCutResult cfg' = M.filterWithKey (\k _ -> S.member k used)
          (S.nonCutsResult cfg' scope' be' sol)
      | otherwise = S.nonCutsResult cfg' scope' be' sol

    usedSolution sol used = sol
      { Sol.sMap = M.union (M.fromList
          [(k, Sol.QB [Sol.trueEqual]) | k <- M.keys (Sol.sHyp sol), not (S.member k used)])
          (Sol.sMap sol)
      , Sol.sHyp = M.filterWithKey (\k _ -> S.member k used) (Sol.sHyp sol)
      }

resultSorts :: F.SInfo a -> [F.KVar] -> F.BindEnv a -> F.ResultSorts
resultSorts fi ks be = M.fromList
  [(k, xts)
    | k <- ks
    , xts <- maybeToList (kvarScope fi be k) ]

kvarScope :: F.SInfo a -> F.BindEnv a -> F.KVar -> Maybe [(F.Symbol, F.Sort)]
kvarScope fi be k = do
  w <- M.lookup k (F.ws fi)
  let bs = F.wenv w
  let (v, t, _) = F.wrft w
  return $ (v, t) : [ bindInfo be i | i <- L.sort (F.elemsIBindEnv bs) ]

bindInfo :: F.BindEnv a -> F.BindId -> (F.Symbol, F.Sort)
bindInfo be i = (x, F.sr_sort sr)
  where
    (x, sr, _) = F.lookupBindEnv i be

solResult :: Config -> Sol.Solution -> SolveM ann (M.HashMap F.KVar F.Expr)
solResult cfg = minimizeResult cfg . Sol.result

result_
  :: (F.Loc a, NFData a)
  => S.HashSet F.Symbol
  -> F.IBindEnv
  -> F.BindEnv a
  -> Config
  -> [F.SimpC a]
  -> Sol.Solution
  -> SolveM a (F.FixResult (F.SimpC a))
result_ scope bindingsInSmt be cfg cs0 s = do
  unsatisfiedConstraints <- if skipResultCheck cfg || skipResultSolution cfg
    then pure []
    else if fastResultCheck cfg
      then do
        fastFailures <- check sFast cs
        check s fastFailures
      else check s cs
  sts      <- stats
  pure $ res sts unsatisfiedConstraints
  where
    cs          = isChecked cfg cs0
    check sol   = filterM (isUnsat scope bindingsInSmt be sol)
    sFast       = s { Sol.sMap = M.union fastCuts (Sol.sMap s)
                    , Sol.sHyp = mempty
                    }
    fastCuts    = M.fromList [(k, Sol.QB [Sol.trueEqual]) | k <- M.keys (Sol.sHyp s)]
    res sts []  = F.Safe sts
    res sts cs' = F.Unsafe sts cs'

isChecked :: Config -> [F.SimpC a] -> [F.SimpC a]
isChecked cfg cs = case checkCstr cfg of
  []   -> cs
  ids  -> let s = S.fromList ids in
          [c | c <- cs, S.member (F.subcId c) s ]

--------------------------------------------------------------------------------
-- | `minimizeResult` transforms each KVar's result by removing
--   conjuncts that are implied by others. That is,
--
--      minimizeConjuncts :: ps:[Pred] -> {qs:[Pred] | subset qs ps}
--
--   such that `minimizeConjuncts ps` is a minimal subset of ps where no
--   is implied by /\_{q' in qs \ qs}
--   see: tests/pos/min00.fq for an example.
--------------------------------------------------------------------------------
minimizeResult :: Config -> M.HashMap F.KVar F.Expr
               -> SolveM ann (M.HashMap F.KVar F.Expr)
--------------------------------------------------------------------------------
minimizeResult cfg s
  | minimalSol cfg = mapM minimizeConjuncts s
  | otherwise      = return s

minimizeConjuncts :: F.Expr -> SolveM ann F.Expr
minimizeConjuncts p = F.pAnd <$> go (F.conjuncts p) []
  where
    go []     acc   = return acc
    go (p:ps) acc   = do b <- isValid F.dummySpan (F.pAnd (acc ++ ps)) p
                         if b then go ps acc
                              else go ps (p:acc)

--------------------------------------------------------------------------------
isUnsat
  :: (F.Loc a, NFData a) => S.HashSet F.Symbol -> F.IBindEnv -> F.BindEnv a -> Sol.Solution -> F.SimpC a -> SolveM a Bool
--------------------------------------------------------------------------------
isUnsat scope bindingsInSmt be s c = do
  -- lift   $ printf "isUnsat %s" (show (F.subcId c))
  _     <- tickIter True -- newScc
  cfg <- T.config <$> getContext
  let lp = S.lhsPred cfg scope bindingsInSmt be s c
      rp = rhsPred c
  res   <- not <$> isValid (cstrSpan c) lp rp
  lift   $ whenLoud $ showUnsat res (F.subcId c) lp rp
  return res

showUnsat :: Bool -> Integer -> F.Pred -> F.Pred -> IO ()
showUnsat u i lP rP = {- when u $ -} do
  putStrLn $ printf   "UNSAT id %s %s" (show i) (show u)
  putStrLn $ showpp $ "LHS:" <+> pprint lP
  putStrLn $ showpp $ "RHS:" <+> pprint rP

--------------------------------------------------------------------------------
-- | Predicate corresponding to RHS of constraint in current solution
--------------------------------------------------------------------------------
rhsPred :: F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
rhsPred c
  | isTarget c = F.crhs c
  | otherwise  = errorstar $ "rhsPred on non-target: " ++ show (F.sid c)

--------------------------------------------------------------------------------
isValid :: F.SrcSpan -> F.Expr -> F.Expr -> SolveM ann Bool
--------------------------------------------------------------------------------
isValid sp p q = not . null <$> filterValid sp p [(q, ())]

cstrSpan :: (F.Loc a) => F.SimpC a -> F.SrcSpan
cstrSpan = F.srcSpan . F.sinfo

{-
---------------------------------------------------------------------------
donePhase' :: String -> SolveM ()
---------------------------------------------------------------------------
donePhase' msg = lift $ do
  threadDelay 25000
  putBlankLn
  donePhase Loud msg
-}
