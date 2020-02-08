{-# LANGUAGE StandaloneDeriving #-}

module Test 
  ( readFSM,
    fsmToDot,
    get_path_set
  ) where
import FSM
import qualified Data.List
import qualified Data.Char
import qualified System.Environment
import qualified Data.Time
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set


deriving instance Show a => Show (Set a)
deriving instance (Show a, Show b) => Show (FSM_ext a b)
deriving instance (Show a, Show b) => Show (Sum a b)


deriving instance Read a => Read (Set a)
deriving instance (Read a, Read b) => Read (FSM_ext a b)
deriving instance (Read a, Read b) => Read (Sum a b)

deriving instance Eq a => Eq (Set a)
deriving instance (Eq a, Eq b) => Eq (FSM_ext a b)

deriving instance Ord a => Ord (Set a)
deriving instance (Ord a, Ord b) => Ord (FSM_ext a b)
deriving instance (Ord a, Ord b) => Ord (Sum a b)

nat_to_int :: Nat -> Integer 
nat_to_int Zero_nat = 0
nat_to_int (Suc n) = 1 + nat_to_int n

instance Show Nat where 
    show n = show $ nat_to_int n

 

--------------------------------------------------------------------------------
-- reading FSMs from .fsm files and writing fsms as .dot files
--------------------------------------------------------------------------------


dotShow :: (Show a) => a -> String 
dotShow x = "\"" ++ (show x) ++ "\""

transitionToDot :: (Show a) => (a, (Integer, (Integer, a))) -> String
transitionToDot (q,(x,(y,q'))) = (dotShow q) ++ " -> " ++ (dotShow q') ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 

transitionToDotLR :: (Eq a, Show a) => (a, (Integer, (Integer, a))) -> a -> a -> String
transitionToDotLR (q,(x,(y,q'))) ql qr = (dotShow q) ++ " -> " ++ (if q' == ql then "L" else if q' == qr then "R" else dotShow q') ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 

fsmToDotInternal :: (Eq a, Show a) => FSM_ext a b -> String
fsmToDotInternal m = 
    "\trankdir=LR;\n"
    ++ "\tnode [shape = doublecircle]; " ++ (dotShow $ initial m) ++ "\n"
    ++ "\tnode [shape = circle];\n" 
    ++ (unlines $ map (\t -> "\t" ++ transitionToDot t) (wf_transitions m)) ++ "\n"

fsmToDot :: (Eq a, Show a) => FSM_ext a b -> String
fsmToDot m = 
    "strict digraph fsm {\n"
    ++ (fsmToDotInternal m) ++ "\n"
    ++ "}"     

fromInl :: Sum a b -> a
fromInl (Inl x) = x         
            


readTransition :: String -> Either String (Integer, (Integer, (Integer, Integer))) 
readTransition line = 
    if length ts /= 4
        then Left $ "Not exactly 4 parameters for transition: " ++ line
        else if all (all Data.Char.isDigit) ts
            then Right (q1,(x,(y,q2)))
            else Left $ "Contains parameter that is not a positive integer: " ++ line     
    where  
        ts = words line
        q1 = read $ ts !! 0
        x  = read $ ts !! 1
        y  = read $ ts !! 2
        q2 = read $ ts !! 3 


readTransitions :: String -> Either String [(Integer, (Integer, (Integer, Integer)))]
readTransitions ts = Prelude.foldr f (Right []) (zip [1::Integer ..] $ lines ts)
    where
        f (n,line) (Right ts) = case readTransition line of 
                                Right t -> Right $ t:ts
                                Left err -> Left $ "ERROR (line " ++ (show n) ++ "): " ++ err
        f _ err = err
        
readFSM :: String -> Either String (FSM_ext Integer ())
readFSM fsmStr = readTransitions fsmStr >>= (\ts -> Right $ FSM_ext 0 (Data.List.nub $ map (fst . snd) ts) (Data.List.nub $ map (fst . snd . snd) ts) (Data.List.nub ts) ())


-- todo: move to main
{-
readAndPrintFSM :: IO ()
readAndPrintFSM = do
    args <- System.Environment.getArgs
    fsmFile <- readFile (args !! 0)
    let destination = (args !! 1)
    case readFSM fsmFile of 
        Right fsm -> writeFile destination $ fsmToDot fsm
        Left err  -> putStrLn err
-}


--------------------------------------------------------------------------------
-- representing test suites as .dot files
--------------------------------------------------------------------------------



-- TODO: import from old Main.hs




--------------------------------------------------------------------------------
-- representing test suites as lists of IO sequences
--------------------------------------------------------------------------------





get_io :: [(a, (Integer, (Integer, a)))] -> [(Integer,Integer)]
get_io = map (\(_,(x,(y,_))) -> (x,y) )

get_path_set :: (Show a, Ord a) => ([(a, ([(a, (Integer, (Integer, a)))], FSM_ext (Sum (a, a) a) b))],  [(a, FSM_ext a b)]) -> Set.Set [(Integer, Integer)]
get_path_set (ts,ps) =  Prelude.foldl f Set.empty ts
  where
    f prev (q,(p,atc)) = case Prelude.lookup q ps of  
                          Just preamble -> Set.union prev $ Set.fromList [ (get_io p1) ++ (get_io p) ++ (get_io p2) | p1 <- maximal_acyclic_paths preamble, p2 <- maximal_acyclic_paths atc]
                          Nothing       -> error $ "State " ++ (show q) ++ " is not d-reachable"







-- TODO: move to new Main
{-
fsmName = "dr"
main = do
  s <- Data.Time.getCurrentTime
  putStrLn $ "Started : " ++ (show s)
  fsmFile <- readFile $ fsmName ++ ".fsm"
  case readFSM fsmFile of 
    Right fsm -> do 
      putStrLn $ show $ size fsm
      writeFile (fsmName ++ ".dot") $ fsmToDot fsm
      let (ts_orig,fP) = calculate_test_suite fsm $ size fsm
      putStrLn $ show $ length ts_orig
      c <- Data.Time.getCurrentTime
      putStrLn $ "Calc'd   : " ++ (show c)

      let ts_nub = Set.elems $ Set.fromList ts_orig
      putStrLn $ show $ length ts_nub
      n <- Data.Time.getCurrentTime
      putStrLn $ "Nubbed   : " ++ (show n)

      writeFile (fsmName ++ "_output_l") $ unlines $ map show ts_nub
      f <- Data.Time.getCurrentTime
      putStrLn $ "Stored   : " ++ (show f)
      
      ts_l <- readFile $ fsmName ++ "_output_l"
      let ts = map (\t -> read t :: (Integer, (FSM_ext Integer (), ([(Integer, (Integer, (Integer, Integer)))], FSM_ext (Sum (Integer, Integer) Integer) ())))) 
                  (lines ts_l)
      putStrLn $ show $ length ts
      l <- Data.Time.getCurrentTime
      putStrLn $ "Loaded   : " ++ (show l)
      
      let ts_m = collect_ATCs_hs ts
      putStrLn $ show $ length ts_m
      writeFile (fsmName ++ "_map_l") $ unlines $ map show ts_m
      m <- Data.Time.getCurrentTime
      putStrLn $ "Mapped   : " ++ (show m)

      let (cpr, cp, ca, co) = convert_tests_c ts_m
      putStrLn $ show $ length $ fst cpr
      putStrLn $ show $ length $ snd cpr
      putStrLn $ show $ length $ fst cp
      putStrLn $ show $ length $ snd cp
      putStrLn $ show $ length $ fst ca
      putStrLn $ show $ length $ snd ca
      putStrLn $ show $ length $ fst co
      putStrLn $ show $ length $ snd co
      v <- Data.Time.getCurrentTime
      putStrLn $ "Converted: " ++ (show v)

      writeFile (fsmName ++ "_test.dot") $ convert_to_dot_c (cpr, cp, ca, co)

      f <- Data.Time.getCurrentTime
      putStrLn $ "Finished : " ++ (show f)

-}