-------------------------------------------------------------------------------
-- | This module defines a function to solve NNF constraints,
--   by reducing them to the standard FInfo.
-------------------------------------------------------------------------------

module Language.Fixpoint.Horn.Solve (solveHorn, solve) where

import System.Exit ( ExitCode )
import Control.DeepSeq ( NFData(..) )
import Control.Monad.State.Strict (State, evalState, get, put)
import System.IO (hFlush, stdout)
import Control.Monad (when)
import qualified Language.Fixpoint.Misc         as Misc
import qualified Language.Fixpoint.Utils.Files  as Files
import qualified Language.Fixpoint.Solver       as Solver
import qualified Language.Fixpoint.Parse        as Parse
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Horn.Types   as H

import qualified Language.Fixpoint.Horn.Parse   as H

import qualified Language.Fixpoint.Horn.Transformations as Tx
import Text.PrettyPrint.HughesPJ.Compat ( render )
import Language.Fixpoint.Horn.Info ( hornFInfo )

import Language.Fixpoint.Verbosity ( whenLoud )
import qualified Data.Aeson as Aeson
-- import Debug.Trace (traceM)

----------------------------------------------------------------------------------
solveHorn :: F.Config -> IO ExitCode
----------------------------------------------------------------------------------
solveHorn baseCfg0 = do
  q <- parseQuery baseCfg0
  let baseCfg = baseCfg0 { F.explicitKvars = True }
  -- If you want to set --eliminate=none, you better make it a pragma
  let cfgElim = if F.eliminate baseCfg == F.None
                  then baseCfg { F.eliminate =  F.Some }
                  else baseCfg

  cfgPragmas <- F.withPragmas cfgElim (H.qOpts q)

  when (F.save cfgPragmas) (saveHornQuery cfgPragmas q)

  r <- solve cfgPragmas q
  Solver.resultExitCode cfgPragmas r

parseQuery :: F.Config -> IO H.TagQuery
parseQuery cfg
  | F.stdin cfg = Parse.parseFromStdIn H.hornP
  | json        = loadFromJSON file
  | otherwise   = Parse.parseFromFile H.hornP file
  where
    json  = Files.isExtFile Files.Json file
    file  = F.srcFile cfg

loadFromJSON :: FilePath -> IO H.TagQuery
loadFromJSON f = do
  r <- Aeson.eitherDecodeFileStrict f
  case r of
    Right v -> return v
    Left err -> error ("Error in loadFromJSON: " ++ err)

saveHornQuery :: F.Config -> H.Query H.Tag -> IO ()
saveHornQuery cfg q = do
  saveHornSMT2 cfg q
  saveHornJSON cfg q

saveHornSMT2 :: F.ToHornSMT a => F.Config -> a -> IO ()
saveHornSMT2 cfg q = do
  let hq   = F.queryFile Files.HSmt2 cfg
  putStrLn $ "Saving Horn Query: " ++ hq ++ "\n"
  Misc.ensurePath hq
  writeFile hq $ render (F.toHornSMT q)

saveHornJSON :: F.Config -> H.Query H.Tag -> IO ()
saveHornJSON cfg q = do
  let hjson   = F.queryFile Files.HJSON cfg
  putStrLn $ "Saving Horn Query: " ++ hjson ++ "\n"
  Misc.ensurePath hjson
  Aeson.encodeFile hjson q

----------------------------------------------------------------------------------
eliminate :: (F.Fixpoint a, F.PPrint a) => F.Config -> H.Query a -> IO (H.Query a)
----------------------------------------------------------------------------------
eliminate cfg q
  | F.eliminate cfg == F.Existentials = do
    Tx.solveEbs cfg q
  | F.eliminate cfg == F.Horn = do
    let c = Tx.elim $ H.qCstr q
    whenLoud $ putStrLn "Horn Elim:"
    whenLoud $ putStrLn $ F.showpp c
    pure $ q { H.qCstr = c }
  | otherwise = pure q

----------------------------------------------------------------------------------
solve :: (F.PPrint a, NFData a, F.Loc a, Show a, F.Fixpoint a) => F.Config -> H.Query a
       -> IO (F.Result (Integer, a))
----------------------------------------------------------------------------------
solve cfg qry = do
  if F.traceSolver cfg
    then do
      let numbered = (fmap (Origin []) qry)
            { H.qCstr = evalState (numberHeads (H.qCstr qry)) 0 }
          allOrigins = headOrigins (H.qCstr numbered)
          transformed = F.eliminate cfg `elem` [F.Horn, F.Existentials]
          preserve (Origin ids a) = Origin (if transformed then allOrigins else ids) a
      dumpInputHeads (H.qCstr numbered)
      when transformed $ putStrLn "INPUT_PROVENANCE mode=conservative_frontend_elimination"
      fmap (fmap (\(i, Origin _ a) -> (i, a))) $ solveQuery cfg (fmap preserve numbered)
    else solveQuery cfg qry

data Origin a = Origin ![Int] !a deriving (Show)

instance NFData a => NFData (Origin a) where
  rnf (Origin i a) = rnf i `seq` rnf a

instance F.Loc a => F.Loc (Origin a) where
  srcSpan (Origin _ a) = F.srcSpan a
  srcOrigin (Origin ids _) = ids

instance F.Fixpoint a => F.Fixpoint (Origin a) where
  toFix (Origin _ a) = F.toFix a

instance F.PPrint a => F.PPrint (Origin a) where
  pprintPrec n t (Origin _ a) = F.pprintPrec n t a

numberHeads :: H.Cstr a -> State Int (H.Cstr (Origin a))
numberHeads (H.Head p a) = do
  i <- get
  put (i + 1)
  pure $ H.Head p (Origin [i] a)
numberHeads (H.CAnd cs) = H.CAnd <$> mapM numberHeads cs
numberHeads (H.All b c) = H.All (fmap (Origin []) b) <$> numberHeads c

headOrigins :: H.Cstr (Origin a) -> [Int]
headOrigins (H.Head _ (Origin ids _)) = ids
headOrigins (H.CAnd cs) = concatMap headOrigins cs
headOrigins (H.All _ c) = headOrigins c

dumpInputHeads :: H.Cstr (Origin a) -> IO ()
dumpInputHeads (H.Head _ (Origin ids _)) = do
  putStrLn $ "INPUT_HEAD origins=" ++ show ids
  hFlush stdout
dumpInputHeads (H.CAnd cs) = mapM_ dumpInputHeads cs
dumpInputHeads (H.All _ c) = dumpInputHeads c

solveQuery :: (F.PPrint a, NFData a, F.Loc a, Show a, F.Fixpoint a)
           => F.Config -> H.Query a -> IO (F.Result (Integer, a))
solveQuery cfg qry = do
  let c = Tx.uniq $ Tx.flatten $ H.qCstr qry
  whenLoud $ putStrLn "Horn Uniq:"
  whenLoud $ putStrLn $ F.showpp c
  q <- eliminate cfg ({- void $ -} qry { H.qCstr = c })
  let fi = hornFInfo cfg q
  Solver.solve cfg fi
