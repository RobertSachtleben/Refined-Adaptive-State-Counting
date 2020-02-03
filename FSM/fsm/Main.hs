{-# LANGUAGE StandaloneDeriving #-}

module Main where
import FSM
import qualified Data.List
import qualified Data.Char
import qualified System.Environment


deriving instance Show a => Show (Set a)
deriving instance (Show a, Show b) => Show (FSM_ext a b)
deriving instance (Show a, Show b) => Show (Sum a b)

-- TODO: bad implementation, use intermediate conversion to integer
instance Show Nat where 
    show Zero_nat = "0"
    show (Suc n) = show $ 1 + read (show n)

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
--dotShow = (map (\x -> if Data.Char.isAlphaNum x then x else '_')) . show
dotShow x = "\"" ++ (show x) ++ "\""


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
    "strict digraph fsm {\n"
    ++ (fsmToDotInternal m) ++ "\n"
    ++ "}"     

separatorsToDots :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDots m mName = mapM_ (\rs -> writeFile (mName ++ "_" ++ (dotShow $ fst $ fst rs) ++ "_" ++ (dotShow $ snd $ fst rs) ++ ".dot") (fsmToDot $ snd rs)) $ r_distinguishable_state_pairs_with_separators_naive m

separatorsToDot :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDot m mName = 
    writeFile 
        (mName ++ "_separators.dot") 
        ("strict digraph fsm {\n"
            ++ (unlines $ map (fsmToDotInternal . snd) $ r_distinguishable_state_pairs_with_separators_naive m)
            ++ "}")

fromInl :: Sum a b -> a
fromInl (Inl x) = x            

separatorsToDotLR :: (Eq a, Show a) => FSM_ext a b -> String -> IO ()
separatorsToDotLR m mName = 
    writeFile 
        (mName ++ "_separators.dot") 
        ("strict digraph fsm {\n"
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




type Source = String
type Target = String
type Style = String
type Node = String

is_inl :: Sum a b -> Bool 
is_inl (Inl _) = True
is_inl _ = False

preamble_to_dot :: (Show a, Eq a) => a -> FSM_ext a b -> String
preamble_to_dot a p = nodeHeader ++ (unlines $ map (\t -> transitionToDot t) (wf_transitions p)) ++ "\n"
  where
    internalNodes = filter ((/=) a) (nodes_from_distinct_paths p) 
    nodeHeader = "node [shape = doublecircle, style = filled, fillcolor=cyan]; " ++ (dotShow $ initial p) ++ "\n"
                  ++ "node [shape = circle, style = filled, fillcolor=cadetblue1]; " ++ (Data.List.intersperse ' ' $ concatMap dotShow internalNodes) ++ "\n"
                  ++ "node [shape = circle, style = filled, fillcolor=blueviolet]; " ++ (dotShow a) ++ "\n"



m_traversal_path_to_dot :: (Show a, Eq a) => [(a, (Integer, (Integer, a)))] -> String
m_traversal_path_to_dot p = "node [shape = circle, style = filled, fillcolor=darkorchid1];\n"
                            ++ (unlines $ (map (\(n,(q,(x,(y,q')))) -> if (n == 0) then (dotShow q) ++ " -> " ++ (show $ (show q') ++ "_(" ++ (show $ n + 1) ++ ")" ) ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 
                                                                                   else (show $ (show q) ++ "_(" ++ (show n) ++ ")" ) ++ " -> " ++ (show $ (show q') ++ "_(" ++ (show $ n + 1) ++ ")" ) ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" )
                                               (zip [0..] p)))







atc_to_dot :: (Show a, Eq a) => a -> String -> FSM_ext (Sum (a, a) a) b -> String
atc_to_dot a srcStr atc = nodeHeader ++ srcTransition ++ (unlines $ map transitionToDot (wf_transitions atc)) ++ "\n"
  where
    internalNodes = filter is_inl (nodes_from_distinct_paths atc) 
    nodeHeader = "node [shape = circle, style = filled, fillcolor=cadetblue1]; " ++ (concat $ (Data.List.intersperse " ") $ map dotShow internalNodes) ++ "\n"
                 ++ "node [shape = circle, style = filled, fillcolor=\"#66FF66\"]; " ++ (show $ "Inr " ++ (show a)) ++ "\n"
                 ++ "node [shape = circle, style = filled, fillcolor=\"#FF6666\"]; \n" -- every other node (i.e.: the other Inr node)
    srcTransition = srcStr ++ " -> " ++ (dotShow $ initial atc) ++ " [ style = dashed ];\n" 

-- does remove initial states of the atc
{-
atc_to_dot :: (Show a, Eq a) => a -> String -> FSM_ext (Sum (a, a) a) b -> String
atc_to_dot a srcStr atc = nodeHeader ++ (unlines $ map (\(q,(x,(y,q'))) -> if (q == initial atc) then srcStr ++ " -> " ++ (dotShow q') ++ " [ label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\" ];" 
                                                                                                 else transitionToDot (q,(x,(y,q')))) 
                                                    (wf_transitions atc)) ++ "\n"
  where
    internalNodes = filter (\q -> (is_inl q) && (q /= initial atc)) (nodes_from_distinct_paths atc) 
    nodeHeader = "node [shape = circle, style = filled, fillcolor=cadetblue1]; " ++ (concat $ (Data.List.intersperse " ") $ map dotShow internalNodes) ++ "\n"
                 ++ "node [shape = circle, style = filled, fillcolor=\"#66FF66\"]; " ++ (show $ "Inr " ++ (show a)) ++ "\n"
                 ++ "node [shape = circle, style = filled, fillcolor=\"#FF6666\"]; \n" -- every other node (i.e.: the other Inr node)
-}


-- ,color=black, penwidth=3
test_to_dot :: (Show a, Eq a) => (a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], Set (FSM_ext (Sum (a, a) a) b)))) -> String
test_to_dot (q,(preamble,(p, Set atcs)))= 
    header ++ "\n" ++
    preamble_dot ++ "\n" ++
    path_dot ++ "\n" ++
    atc_dot ++ "\n" ++
    footer
  where 
    header = "digraph fsm {\nrankdir=LR;\n"
    footer = "}"
    preamble_dot = preamble_to_dot q preamble
    path_dot = m_traversal_path_to_dot p
    atc_dot = concatMap (atc_to_dot (target p q) (show $ (show (target p q)) ++ "_(" ++ (show $ length p) ++ ")" )) atcs
    




convert_transition :: Show a => (a, (Integer, (Integer, a))) -> (Source,Target,Style)
convert_transition (q,(x,(y,q'))) = (dotShow q, dotShow q', "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"") 

-- result: (edges,uniqueNodes,possiblyReusedNodes)
convert_preamble :: (Show a, Eq a) => a -> FSM_ext a b -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])
convert_preamble a pr = (map convert_transition (wf_transitions pr), 
                         [(dotShow $ initial pr, "shape = doublecircle, style = filled, fillcolor=deepskyblue4"), (dotShow a, "shape = doublecircle, style = filled, fillcolor=blueviolet")],
                         map (\ q -> (dotShow q, "shape = circle, style = filled, fillcolor=cadetblue1")) $ filter ((/=) a) (nodes_from_distinct_paths pr)      
                          )

convert_m_traversal_path :: (Show a, Eq a) => a -> [(a, (Integer, (Integer, a)))] -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])
convert_m_traversal_path src p = (map (\(n,(q,(x,(y,q')))) -> if (n == 0) then (dotShow q, show $ (show q') ++ "_(1)" ++ "\nfrom: " ++ (show src), "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"")
                                                                        else (show $ (show q) ++ "_(" ++ (show n) ++ ")" ++ "\nfrom: " ++ (show src), show $ (show q') ++ "_(" ++ (show $ n + 1) ++ ")" ++ "\nfrom: " ++ (show src), "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"" ))
                                  (zip [0..] p),
                              [],
                              (map (\(n,(q,(x,(y,q')))) -> (show $ (show q') ++ "_(" ++ (show $ n+1) ++ ")" ++ "\nfrom: " ++ (show src), "shape = circle, style = filled, fillcolor=darkorchid1"))
                                   (zip [0..] p))
                             )

convert_atc :: (Show a, Eq a) => a -> String -> FSM_ext (Sum (a, a) a) b -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                             
convert_atc a srcStr atc = ((srcStr, showATCNode $ initial atc, "style = dashed" ) 
                             : (map (\(q,(x,(y,q'))) -> case q' of Inr s -> if s == a then (showATCNode q, "PASS", "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"")
                                                                                      else (showATCNode q, "FAIL", "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"")
                                                                   _     -> (showATCNode q, showATCNode q', "label = \"" ++ (show x) ++ "/" ++ (show y) ++ "\"")) 
                                    (wf_transitions atc)), 
                            [("FAIL","shape = circle, style = filled, fillcolor=\"#FF6666\""),("PASS","shape = circle, style = filled, fillcolor=\"#66FF66\"")],
                            map (\q -> (showATCNode q, "shape = doublecircle, style = filled, fillcolor=gold")) 
                                (filter is_inl (nodes_from_distinct_paths atc))
                           )
  where 
    showATCNode q = show $ (show q) ++ "\nfrom: " ++ (show a)

convert_test :: (Show a, Eq a) => (a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], Set (FSM_ext (Sum (a, a) a) b)))) -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_test (q,(preamble,(p, Set atcs))) = (ePr ++ eP ++ eA, uPr ++ uP ++ uA, dPr ++ dP ++ dA)
  where 
    (ePr,uPr,dPr) = convert_preamble q preamble
    (eP, uP, dP ) = convert_m_traversal_path q p
    (eA, uA, dA ) = foldl (\(eA',uA',dA') atc -> case convert_atc (target p q) (show $ (show (target p q)) ++ "_(" ++ (show $ length p) ++ ")"  ++ "\nfrom: " ++ (show q)) atc of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) atcs
    

convert_tests :: (Show a, Eq a) => [(a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], Set (FSM_ext (Sum (a, a) a) b))))] -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_tests = foldl (\(eA',uA',dA') t -> case convert_test t of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) 


convert_to_dot ::  ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)]) -> String
convert_to_dot (es,us,ds) = 
    "digraph fsm {\nrankdir=LR;\n"
    ++ (unlines $ map (\(node,style) -> "node [" ++ style ++ " ]; " ++ node) (Data.List.nub us))
    ++ (unlines $ map (\(node,style) -> "node [" ++ style ++ " ]; " ++ node) (Data.List.nub ds))
    ++ (unlines $ map (\(src,tgt,style) -> src ++ "->" ++ tgt ++ " [" ++ style ++ " ];") (Data.List.nub es))
    ++"}"




-- todo: add fun to get trees showing m-traversal-paths and the used D (termination criterion)

int_to_nat :: Int -> Nat 
int_to_nat 0 = Zero_nat
int_to_nat n = Suc (int_to_nat (n-1)) 

--main = writeFile "test.dot" $ "digraph fsm {\nrankdir=LR;\n" ++ (concatMap test_to_dot $ filter (\(q,_) -> q == 1) $ calculate_test_suite m_ex_H $ int_to_nat 4) ++ "}"
--main = writeFile "testC.dot" $ convert_to_dot $ convert_tests $ calculate_test_suite m_ex_DR $ int_to_nat 4
main = writeFile "testDR.dot" $ convert_to_dot $ convert_tests $ calculate_test_suite m_ex_DR $ size m_ex_DR











--main = putStrLn $ show $ maximal_repetition_sets_from_separators m_ex_DR
--main = separatorsToDotLR m_ex_DR "m_ex_DR"
--main = readAndPrintFSM        

--main = mapM_ (putStrLn . show ) $ enumerate_FSMs 0 [0,1,2,3] [0,1] [0,1,2]
--main = putStrLn . show . length $ enumerate_FSMs 0 [0,1,2,3] [0,1] [0,1,2]

--main = putStrLn . show $ foldl (\b a -> (b+1)) 0 $ enumerate_FSMs 0 [0,1,2,3] [0,1] [0,1,2]
--main = putStrLn . show . generate_sublists $ enumerate_transitions [0,1,2,3] [0,1] [0,1,2]

--main = putStrLn . show $ find_FSM (\fsm -> observable fsm && single_input fsm && all (\q -> member q (nodes fsm)) [0,1,2]) 0 [0,1,2] [0,1] [0,1,2]


{-
find_FSMa ::
  forall a.
    (FSM_ext a () -> Bool) ->
      a -> [Integer] ->
             [Integer] ->
               [(a, (Integer, (Integer, a)))] ->
                 [Bool] -> Integer -> Maybe (FSM_ext a ());
--find_FSMa f q xs ys ts bs Zero_nat = Nothing;
find_FSMa f q xs ys ts bs k =
  let {
    m = FSM_ext q xs ys
          (map_filter (\ x -> (if snd x then Just (fst x) else Nothing))
            (zip ts bs))
          ();
  } in (if f m then Just m else (case next_boolean_list bs of {
                                  Nothing -> Nothing;
                                  Just bsa -> find_FSMa f q xs ys ts bsa (k-1);
                                }));

power :: forall a. (Power a) => a -> Nat -> a;
power a Zero_nat = one;
power a (Suc n) = times a (power a n);

nat_to_Integer :: Nat -> Integer;
nat_to_Integer Zero_nat = 0;
nat_to_Integer (Suc k) = 1 + nat_to_Integer k;

find_FSM ::
  forall a.
    (FSM_ext a () -> Bool) ->
      a -> [a] -> [Integer] -> [Integer] -> Maybe (FSM_ext a ());
find_FSM f q qs xs ys =
  let {
    ts = enumerate_transitions qs xs ys;
  } in find_FSMa f q xs ys ts (replicate (size_list ts) True)
         ((2::Integer) ^ (nat_to_Integer (size_list ts)));

-}