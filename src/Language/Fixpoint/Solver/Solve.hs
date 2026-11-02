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
import           Language.Fixpoint.Solver.Monad
import           Language.Fixpoint.Utils.Progress
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
import qualified Language.Fixpoint.Types.Visitor as V
import System.IO (hFlush, stdout)
import Control.Exception (evaluate)
import GHC.Clock (getMonotonicTimeNSec)
import Data.Word (Word64)

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
    when (traceSolver cfg) $ do
      dumpManifest fi sI
    whenLoud $ donePhase Misc.Loud "Worklist Initialize"
    vb <- getVerbosity
    (res, stat) <- (if Quiet == vb then id else withProgressFI sI) $ runSolverM cfg sI elabParam act
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
    s0  = (siSol sI) { Sol.sMap = S.init cfg fi ks }
    ks  = siVars sI
    elabQBind ctx msg env (Sol.QB xs) = Sol.QB (map elabEQual xs)
      where
        elabEQual eq =
          eq { Sol.eqPred =
                elaborate
                 (ElabParam (T.ctxElabF ctx) (F.atLoc F.dummySpan msg) env)
                 (Sol.eqPred eq)
             }


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
  t0 <- liftIO $ traceClock cfg
  liftSMT $ smtComment "solve: start"
  (s3, res0) <- sendConcreteBindingsToSMT F.emptyIBindEnv (F.bs fi) $ \bindingsInSmt -> do
    -- let s3   = solveEbinds fi s2
    s3       <- {- SCC "sol-refine" -} refine scope bindingsInSmt (F.bs fi) s2 wkl
    liftIO $ when (traceSolver cfg) $ phaseTime "bindings_and_refinement" t0
    t1 <- liftIO $ traceClock cfg
    res0     <- {- SCC "sol-result" -} result scope bindingsInSmt cfg fi (W.unsatCandidates wkl) s3
    liftIO $ when (traceSolver cfg) $ phaseTime "validation_and_result_construction" t1
    return (s3, res0)

  (fi1, res1) <- case resStatus res0 of  {- first run the interpreter -}
    Unsafe _ bads | rewriteAxioms cfg && interpreter cfg -> do
      liftSMT $ smtComment "solve: interpreter"
      bs <- doInterpret cfg fi (map fst $ mytrace ("before the Interpreter " ++ show (length bads) ++ " constraints remain") bads)
      let fi1 = fi { F.bs = bs }
          badCs = lookupCMap (F.cm fi) <$> map fst bads
      liftSMT $ smtComment "solve: pos-interpreter check"
      fmap (fi1,) $ sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg fi1 badCs s3
    _ -> return  (fi, mytrace "all checked before interpreter" res0)

  res2  <- case resStatus res1 of  {- then run normal PLE on remaining unsolved constraints -}
    Unsafe _ bads2 | rewriteAxioms cfg -> do
      when (save cfg) $
        liftIO $ S.saveSolution cfg ".pre-ple" res1
      liftSMT $ smtComment "solve: ple"
      bs <- liftSMT $ PLE.instantiate cfg scope fi1 (Just s3) (Just $ map fst bads2)
      -- Check the constraints one last time after PLE
      let fi2 = fi { F.bs = bs }
          badsCs2 = lookupCMap (F.cm fi) <$> map fst bads2
      liftSMT $ smtComment "solve: pos-ple check"
      sendConcreteBindingsToSMT F.emptyIBindEnv bs $ \bindingsInSmt ->
        result scope bindingsInSmt cfg fi2 badsCs2 s3
    _ -> return $ mytrace "all checked with interpreter" res1

  liftSMT $ smtComment "solve: finished"
  st      <- stats
  let res3 = {- SCC "sol-tidy" -} tidyResult cfg res2
  when (traceSolver cfg) $ do
    counts <- nonCutExpansions
    liftIO $ mapM_ (\((phase, k), n) -> diagnostic $ "NONCUT_EXPANSIONS phase=" ++ phase
      ++ " kvar=" ++ show k ++ " count=" ++ show n)
      (L.sortOn (\((phase, k), _) -> (phase, show k)) $ M.toList counts)
  -- The original return $!! below already deeply evaluates Result, including
  -- Delayed non-cut output formulas. Time that existing demand, not a new force
  -- of use-site expansions. Includes tidying/cut results/status as well.
  t0 <- liftIO $ traceClock cfg
  if traceSolver cfg
    then do
      res <- liftIO $ evaluate $ force (res3, st)
      liftIO $ phaseTime "result_materialization" t0
      return res
    else return $!! (res3, st)


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
  -> SolveM a Sol.Solution
--------------------------------------------------------------------------------
refine scope bindingsInSmt be0 s0 w0 = do
  cfg <- T.config <$> getContext
  go cfg be0 s0 w0 M.empty
  where
    go :: Config -> F.BindEnv a -> Sol.Solution -> W.Worklist a -> M.HashMap Int Profile -> SolveM a Sol.Solution
    go cfg be s w profiles
      | Just (c, w', newScc, rnk) <- W.pop w = do
         i       <- tickIter newScc
         t0 <- liftIO $ traceClock cfg
         (b, s', info, assertions) <- refineC scope bindingsInSmt be i s c
         b `seq` pure ()
         t1 <- liftIO $ traceClock cfg
         when (traceSolver cfg) $
           recordNonCutExpansions "refine" (M.map (* toInteger assertions) $ S.kiExpansions info)
         let p' = Profile (toInteger (t1 - t0)) 1 (if b then 1 else 0)
         liftIO $ when (traceSolver cfg) $ diagnostic $ "SCC_VISIT rank=" ++ show rnk
           ++ " constraint=" ++ show (F.subcId c) ++ " origins=" ++ show (F.srcOrigin (F.sinfo c)) ++ profileFields p'
         lift $ writeLoud $ refineMsg i c b rnk (showpp s')
         let w'' = if b then W.push c w' else w'
         go cfg be s' w'' (if traceSolver cfg then M.insertWith addProfile rnk p' profiles else profiles)
      | otherwise = do
          liftIO $ when (traceSolver cfg) $ do
            mapM_ (\(rank, p) -> diagnostic $ "SCC_TIME rank=" ++ show rank ++ profileFields p) (L.sortOn fst $ M.toList profiles)
          return s
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
  -> SolveM a (Bool, Sol.Solution, S.KInfo, Int)
---------------------------------------------------------------------------
refineC scope bindingsInSmt be _i s c =
  do let krhs = rhsCands s
     cfg <- T.config <$> getContext
     if all (null . snd) krhs
        then return (False, s, mempty, 0)
        else do
          let (lhs, info) = S.lhsPredInfo cfg scope bindingsInSmt be s c
          kqs <- forM krhs $ \(k, rhs) ->
            (,) k . Sol.QB <$> filterValid (cstrSpan c) lhs rhs
          let (b, s') = S.update s kqs
          return (b, s', info, length krhs)
  where
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
  -> SolveM a (F.Result (Integer, a))
--------------------------------------------------------------------------------
result scope bindingsInSmt cfg fi cs s =
  sendConcreteBindingsToSMT bindingsInSmt be $ \bindingsInSmt2 -> do
    lift       $ writeLoud "Computing Result"
    stat      <- result_ scope bindingsInSmt2 be cfg cs s
    lift       $ whenLoud $ putStrLn $ "RESULT: " ++ show (F.sid <$> stat)
    resCut    <- solResult cfg s
    let resNonCut = S.nonCutsResult cfg scope be s
        resSorts = resultSorts fi (M.keys resCut ++ M.keys resNonCut) be
    return     $ F.Result (ci <$> stat) resCut resNonCut resSorts
  where
    ci c = (F.subcId c, F.sinfo c)
    be = F.bs fi

resultSorts :: F.SInfo a -> [F.KVar] -> F.BindEnv a -> F.ResultSorts
resultSorts fi ks be = M.fromList
  [(k, xts)
    | k <- ks
    , xts <- maybeToList (kvarScope fi be k) ]

kvarScope :: F.SInfo a -> F.BindEnv a -> F.KVar -> Maybe [(F.Symbol, F.Sort)]
kvarScope fi be k = do
  w <- M.lookup k (F.ws fi)
  let bs = F.wenv w
  return $ F.wvvs w ++ [ bindInfo be i | i <- L.sort (F.elemsIBindEnv bs) ]

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
  unsatisfiedConstraints <- filterM (isUnsat scope bindingsInSmt be s) cs
  sts      <- stats
  pure $ res sts unsatisfiedConstraints
  where
    cs          = isChecked cfg cs0
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
  t0 <- liftIO $ traceClock cfg
  let (lp, info) = S.lhsPredInfo cfg scope bindingsInSmt be s c
      rp = rhsPred c
  res <- not <$> isValid (cstrSpan c) lp rp
  res `seq` pure ()
  t1 <- liftIO $ traceClock cfg
  when (traceSolver cfg) $ recordNonCutExpansions "concrete" (S.kiExpansions info)
  let p = Profile (toInteger (t1 - t0)) 1 0
  liftIO $ when (traceSolver cfg) $ do
    diagnostic $ "CONCRETE_TIME constraint=" ++ show (F.subcId c)
      ++ " origins=" ++ show (F.srcOrigin (F.sinfo c)) ++ " valid=" ++ show (not res) ++ profileFields p
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

data Profile = Profile
  { elapsed, visits, changes :: !Integer }

addProfile :: Profile -> Profile -> Profile
addProfile a b = Profile
  (elapsed a + elapsed b) (visits a + visits b) (changes a + changes b)

profileFields :: Profile -> String
profileFields p = concat [" " ++ name ++ "=" ++ show value | (name, value) <-
  [("elapsed_ns", elapsed p), ("visits", visits p), ("changes", changes p)]]

diagnostic :: String -> IO ()
diagnostic msg = putStrLn msg >> hFlush stdout

phaseTime :: String -> Word64 -> IO ()
phaseTime name start = do
  end <- getMonotonicTimeNSec
  diagnostic $ "PHASE_TIME phase=" ++ name ++ " elapsed_ns=" ++ show (end - start)

traceClock :: Config -> IO Word64
traceClock cfg = if traceSolver cfg then getMonotonicTimeNSec else pure 0

dumpManifest :: F.Loc a => F.SInfo a -> SolverInfo a -> IO ()
dumpManifest fi si = do
  mapM_ dump (L.sortOn fst $ M.toList grouped)
  mapM_ concrete [c | c <- M.elems (F.cm fi), V.isConcC c]
  mapM_ noncut (L.sortOn (show . fst) $ M.toList $ Sol.sHyp $ siSol si)
  where
    ranks = cRank (siDeps si)
    rank c = rScc (lookupCMap ranks (F.subcId c))
    grouped = M.fromListWith (++) [(rank c, [c]) | c <- M.elems (F.cm (siQuery si)), not (V.isConcC c)]
    unique :: Ord b => [b] -> [b]
    unique = map head . L.group . L.sort
    origins cs = unique $ concatMap (F.srcOrigin . F.sinfo) cs
    fields cs = " origins=" ++ show (origins cs)
    dump (r, cs) = diagnostic $ "SCC_MANIFEST rank=" ++ show r
      ++ " constraints=" ++ show (unique $ map F.subcId cs)
      ++ " head_kvars=" ++ show (unique $ map show $ concatMap V.rhsKVars cs)
      ++ " successor_ranks=" ++ show (unique [rScc x | c <- cs, j <- M.lookupDefault [] (F.subcId c) (cSucc (siDeps si)),
                                                       Just x <- [M.lookup j ranks], rScc x /= r]) ++ fields cs
    concrete c = diagnostic $ "CONCRETE_MANIFEST constraint=" ++ show (F.subcId c)
      ++ " rank=" ++ show (rank c) ++ fields [c]
    noncut (k, cubes) = diagnostic $ "NONCUT_MANIFEST kvar=" ++ show k
      ++ " constraints=" ++ show (unique $ map Sol.cuId cubes)
      ++ fields [c | cube <- cubes, Just c <- [M.lookup (Sol.cuId cube) (F.cm fi)]]

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
