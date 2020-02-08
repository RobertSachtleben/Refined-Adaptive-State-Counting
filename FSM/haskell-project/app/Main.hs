module Main where

import Test 
import FSM
import System.Directory as Directory
import qualified Data.Time as Time
import qualified Data.Set as Set

fsmName = "dr" --todo: check file handling
main = do
  d <- Directory.getCurrentDirectory
  putStrLn $ "Current dir: " ++ d
  s <- Time.getCurrentTime
  putStrLn $ "Started : " ++ (show s)
  --let fsmPath = d ++ "\\" ++ fsmName
  let fsmPath = fsmName
  putStrLn $ "Path       : " ++ fsmPath
  fsmFile <- readFile $ fsmPath ++ ".fsm"
  case readFSM fsmFile of 
    Right fsm -> do 
      putStrLn $ show $ size fsm
      writeFile (fsmName ++ ".dot") $ fsmToDot fsm
      let (ts,ps) = calculate_test_suite fsm $ size fsm
      putStrLn $ show $ length ts
      putStrLn $ show $ length ps
      t1 <-  Time.getCurrentTime
      putStrLn $ "Calc'd   : " ++ (show t1)

      let (ts_nub,ps_nub) = (Set.elems $ Set.fromList ts, Set.elems $ Set.fromList ps)
      putStrLn $ show $ length ts_nub
      putStrLn $ show $ length ps_nub
      t2 <-  Time.getCurrentTime
      putStrLn $ "Nubbed   : " ++ (show t2)

      writeFile (fsmName ++ "_output_ts") $ unlines $ map show ts_nub
      writeFile (fsmName ++ "_output_ps") $ unlines $ map show ps_nub
      t3 <-  Time.getCurrentTime
      putStrLn $ "Stored   : " ++ (show t3)
      
      let suite = get_path_set (ts_nub,ps_nub)
      putStrLn $ show $ length suite
      t4 <-  Time.getCurrentTime
      putStrLn $ "Path'd   : " ++ (show t4)

      writeFile (fsmName ++ "_output_suite") $ unlines $ map show $ Set.elems suite
      t3 <-  Time.getCurrentTime
      putStrLn $ "Stored   : " ++ (show t3)