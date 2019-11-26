{-# LANGUAGE StandaloneDeriving #-}

module Main where
import FSM
import qualified Data.List
import qualified Data.Char
import qualified System.Environment


deriving instance Show a => Show (Set a)
deriving instance (Show a, Show b) => Show (FSM_ext a b)
deriving instance (Show a, Show b) => Show (Sum a b)

showIOSequence :: [(Integer, Integer)] -> String
showIOSequence io = "(" ++ (concat $ map show (map fst io)) ++ "/" ++  (concat $ map show (map snd io)) ++ ")"

isMaximalSequence :: [(Integer, Integer)] -> [[(Integer, Integer)]] -> Bool
isMaximalSequence seq = Prelude.all (\ seq' -> seq' == seq || (not $ Data.List.isPrefixOf seq seq'))

getMaxSequences :: [[(Integer, Integer)]] -> [[(Integer, Integer)]]
getMaxSequences seqs = Data.List.nub $ filter (\ seq -> isMaximalSequence seq seqs) seqs

showTraversalTest :: ([(Integer, Integer)], [[(Integer, Integer)]]) -> String
showTraversalTest (trav,tests) = 
    "    Traversal sequence: " ++ (showIOSequence trav) ++ "\n" ++ 
    "      Test sequences: " ++ (Data.List.intercalate "\n                      " $ map showIOSequence $ getMaxSequences tests) 

showTest :: (Set [(Integer, Integer)], [([(Integer, Integer)], [[(Integer, Integer)]])]) -> String
showTest (Set pr, tts) = 
    "  Preamble:\t" ++ (Data.List.intercalate "\n      " $ map showIOSequence $ getMaxSequences pr) ++ "\n" ++ (Data.List.intercalate "\n" $ map showTraversalTest tts) 

showTestSuite :: [(Set [(Integer, Integer)], [([(Integer, Integer)], [[(Integer, Integer)]])])] -> String
showTestSuite ptts = "[\n" ++ (unlines $ map showTest ptts) ++ "]" 



showTraversalTest' :: ([(Integer, Integer)], [[(Integer, Integer)]]) -> String
showTraversalTest' (trav,tests) = 
    "\t" ++ (showIOSequence trav) ++ "\n\t\t" ++ (Data.List.intercalate "\n\t\t" $ map showIOSequence $ getMaxSequences tests) 

showTest' :: (Set [(Integer, Integer)], [([(Integer, Integer)], [[(Integer, Integer)]])]) -> String
showTest' (Set pr, tts) = 
    (Data.List.intercalate " " $ map showIOSequence $ getMaxSequences pr) ++ "\n" ++ (Data.List.intercalate "\n" $ map showTraversalTest' tts) 

showTestSuite' :: [(Set [(Integer, Integer)], [([(Integer, Integer)], [[(Integer, Integer)]])])] -> String
showTestSuite' ptts = "[\n" ++ (unlines $ map showTest' ptts) ++ "]" 



transitionToDot :: (Show a) => (a, (Integer, (Integer, a))) -> String
transitionToDot (q,(x,(y,q'))) = (dotShow q) ++ " -> " ++ (dotShow q') ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 

transitionToDotLR :: (Eq a, Show a) => (a, (Integer, (Integer, a))) -> a -> a -> String
transitionToDotLR (q,(x,(y,q'))) ql qr = (dotShow q) ++ " -> " ++ (if q' == ql then "L" else if q' == qr then "R" else dotShow q') ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 

dotShow :: (Show a) => a -> String 
dotShow = (map (\x -> if Data.Char.isAlphaNum x then x else '_')) . show

fsmToDotInternal :: (Eq a, Show a) => FSM_ext a b -> String
fsmToDotInternal m = 
    "\trankdir=LR;\n"
    ++ "\tnode [shape = doublecircle]; " ++ (dotShow $ initial m) ++ "\n"
    ++ "\tnode [shape = circle];\n" 
    ++ (unlines $ map (\t -> "\t" ++ transitionToDot t) (wf_transitions m)) ++ "\n"

fsmToDotInternalLR :: (Eq a, Show a) => FSM_ext a b -> (a,a) -> String
fsmToDotInternalLR m (ql,qr) = 
    "\trankdir=LR;\n"
    ++ "\tnode [shape = doublecircle]; " ++ (dotShow $ initial m) ++ "\n"
    ++ "\tnode [shape = circle];\n" 
    ++ (unlines $ map (\t -> "\t" ++ transitionToDotLR t ql qr) (wf_transitions m)) ++ "\n"

fsmToDot :: (Eq a, Show a) => FSM_ext a b -> String
fsmToDot m = 
    "digraph fsm {\n"
    ++ (fsmToDotInternal m) ++ "\n"
    ++ "}"     

separatorsToDots :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDots m mName = mapM_ (\rs -> writeFile (mName ++ "_" ++ (dotShow $ fst $ fst rs) ++ "_" ++ (dotShow $ snd $ fst rs) ++ ".dot") (fsmToDot $ snd rs)) $ r_distinguishable_state_pairs_with_separators_naive m

separatorsToDot :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDot m mName = 
    writeFile 
        (mName ++ "_separators.dot") 
        ("digraph fsm {\n"
            ++ (unlines $ map (fsmToDotInternal . snd) $ r_distinguishable_state_pairs_with_separators_naive m)
            ++ "}")

fromInl :: Sum a b -> a
fromInl (Inl x) = x            

separatorsToDotLR :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDotLR m mName = 
    writeFile 
        (mName ++ "_separators.dot") 
        ("digraph fsm {\n"
            ++ (unlines $ map (\rs -> fsmToDotInternalLR (snd rs) (Inr $ fst $ fst rs, Inr $ snd $ fst rs)) $ r_distinguishable_state_pairs_with_separators_naive m)
            ++ "}")
            





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
        
-- read .fsm file
readFSM :: String -> Either String (FSM_ext Integer ())
readFSM fsmStr = readTransitions fsmStr >>= (\ts -> Right $ FSM_ext 0 (map (fst . snd) ts) (map (fst . snd . snd) ts) ts ())



readAndPrintFSM :: IO ()
readAndPrintFSM = do
    args <- System.Environment.getArgs
    fsmFile <- readFile (args !! 0)
    let destination = (args !! 1)
    case readFSM fsmFile of 
        Right fsm -> writeFile destination $ fsmToDot fsm
        Left err  -> putStrLn err

--main = putStrLn $ show $ maximal_repetition_sets_from_separators m_ex_DR
main = separatorsToDotLR m_ex_DR "m_ex_DR"
--main = readAndPrintFSM        