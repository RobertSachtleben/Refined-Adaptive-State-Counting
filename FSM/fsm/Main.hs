{-# LANGUAGE StandaloneDeriving #-}

module Main where
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

{-
-- ignores b
instance (Show a, Show b) => Show (FSM_ext a b)
  where
    show (FSM_ext a ins outs ts b) =
      "FSM "
      ++ (show a) ++ " "
      ++ (show ins) ++ " "
      ++ (show outs) ++ " "
      ++ (Data.List.intercalate ", " $ map (\(q,(x,(y,q'))) -> "(" ++ (show q) ++ "," ++ (show x) ++ "," ++ (show y) ++ "," ++ (show q') ++ ")") ts )
-}

deriving instance Read a => Read (Set a)
deriving instance (Read a, Read b) => Read (FSM_ext a b)
deriving instance (Read a, Read b) => Read (Sum a b)

deriving instance Eq a => Eq (Set a)
--deriving instance (Eq a, Eq b) => Eq (FSM_ext a b)
--deriving instance (Eq a, Eq b) => Eq (Sum a b)

deriving instance Ord a => Ord (Set a)
deriving instance (Ord a, Ord b) => Ord (FSM_ext a b)
deriving instance (Ord a, Ord b) => Ord (Sum a b)

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
readFSM fsmStr = readTransitions fsmStr >>= (\ts -> Right $ FSM_ext 0 (Data.List.nub $ map (fst . snd) ts) (Data.List.nub $ map (fst . snd . snd) ts) (Data.List.nub ts) ())



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
                            map (\q -> (showATCNode q, "shape = circle, style = filled, fillcolor=gold")) 
                                (filter is_inl (nodes_from_distinct_paths atc))
                           )
  where 
    showATCNode q = show $ (show q) ++ "\nfrom: " ++ (show a)

convert_test :: (Show a, Eq a) => (a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], Set (FSM_ext (Sum (a, a) a) b)))) -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_test (q,(preamble,(p, Set atcs))) = (ePr ++ eP ++ eA, uPr ++ uP ++ uA, dPr ++ dP ++ dA)
  where 
    (ePr,uPr,dPr) = convert_preamble q preamble
    (eP, uP, dP ) = convert_m_traversal_path q p
    (eA, uA, dA ) = foldl (\(eA',uA',dA') atc -> case convert_atc (target p q) 
                                                                  (if length p == 0 then show $ (show q)
                                                                                    else show $ (show (target p q)) ++ "_(" ++ (show $ length p) ++ ")"  ++ "\nfrom: " ++ (show q)) 
                                                                  atc 
                                                   of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) atcs
    

convert_tests :: (Show a, Eq a) => [(a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], Set (FSM_ext (Sum (a, a) a) b))))] -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_tests = foldl (\(eA',uA',dA') t -> case convert_test t of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) 

convert_tests'' :: (Show a, Eq a) => [(a, (FSM_ext a b,  ([(a, (Integer, (Integer, a)))], [(FSM_ext (Sum (a, a) a) b)])))] -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_tests'' = foldl (\(eA',uA',dA') (q,(pr,(p,atcs))) -> case convert_test (q,(pr,(p,Set atcs))) of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) 


convert_test' :: (Show a, Eq a) => (a, FSM_ext a b,  [(a, (Integer, (Integer, a)))], [(FSM_ext (Sum (a, a) a) b)]) -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_test' (q,preamble,p, atcs) = (ePr ++ eP ++ eA, uPr ++ uP ++ uA, dPr ++ dP ++ dA)
  where 
    (ePr,uPr,dPr) = convert_preamble q preamble
    (eP, uP, dP ) = convert_m_traversal_path q p
    (eA, uA, dA ) = foldl (\(eA',uA',dA') atc -> case convert_atc (target p q) 
                                                                  (if length p == 0 then show $ (show q)
                                                                                    else show $ (show (target p q)) ++ "_(" ++ (show $ length p) ++ ")"  ++ "\nfrom: " ++ (show q)) 
                                                                  atc 
                                                   of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) atcs
    

convert_tests' :: (Show a, Eq a) => [(a, FSM_ext a b,  [(a, (Integer, (Integer, a)))], [(FSM_ext (Sum (a, a) a) b)])] -> ([(Source,Target,Style)],[(Node,Style)],[(Node,Style)])                        
convert_tests' = foldl (\(eA',uA',dA') t -> case convert_test' t of (eA'',uA'',dA'') -> (eA' ++ eA'', uA' ++ uA'', dA' ++ dA'') ) ([],[],[]) 





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

--main = writeFile "testDR.dot" $ convert_to_dot $ convert_tests $ calculate_test_suite m_ex_DR $ size m_ex_DR
--main = putStrLn . show $ calculate_state_separator_from_s_states m_ex_DR 0 200
--main = mapM_ (\ (q1,q2) -> putStrLn $ show $ calculate_state_separator_from_s_states  m_ex_DR q1 q2 ) $ non_sym_dist_pairs (nodes_from_distinct_paths  m_ex_DR)
--main = putStrLn . show $ r_distinguishable_state_pairs_with_separators_naive m_ex_DR 
--main = putStrLn . show $ d_reachable_states_with_preambles m_ex_DR


--main = putStrLn . show $ x
--main = putStrLn . show $ calculate_test_suite m_ex_DR $ size m_ex_DR
--main = writeFile "testDR.dot" $ convert_to_dot $ convert_tests $ calculate_test_suite m_ex_DR $ size m_ex_DR
--main = writeFile "testH.dot" $ convert_to_dot $ convert_tests $ calculate_test_suite m_ex_H $ int_to_nat 8






-- calculate test suite and also return internal calc
calculate_test_suite_w ma m =
  let {
    rdssl = r_distinguishable_state_pairs_with_separators_naive ma;
    rdss = Set rdssl;
    rds = image fst rdss;
    rdp = filter
            (\ s ->
              ball s
                (\ q1 ->
                  ball s
                    (\ q2 ->
                      (if not (q1 == q2) then member (q1, q2) rds else True))))
            (map Set (pow_list (nodes_from_distinct_paths ma)));
    mprd = filter (\ s -> not (any (less_set s) rdp)) rdp;
    drsp = d_reachable_states_with_preambles ma;
    drs = map fst drsp;
    mrs = map (\ s -> (s, inf_set s (Set drs))) mprd;
    mtp = map (\ q -> (q, m_traversal_paths_with_witness ma q mrs m)) drs;
    fTP = list_as_fun mtp [];
    fRD = (\ q1 q2 -> snd (the (find (\ qqA -> fst qqA == (q1, q2)) rdssl)));
    pmtp = concatMap (\ (q, p) -> map (\ (pa, _) -> (q, (p, pa))) (fTP q)) drsp;
    prefixPairTests =
      concatMap (\ (q, p) -> prefix_pair_tests q p fRD (fTP q)) drsp;
    preamblePrefixTests =
      concatMap (\ (q, p) -> preamble_prefix_tests q p fRD (fTP q) drsp) drsp;
    preamblePairTests = preamble_pair_tests drsp rdssl;
  } in (
        prefixPairTests ++ preamblePrefixTests ++ preamblePairTests
        --collect_ATCs pmtp (prefixPairTests ++ preamblePrefixTests ++ preamblePairTests),
        --concatMap (\ (q, p) -> map (\ (pa, (rd,dr)) -> (q, p, pa, rd, dr)) (fTP q)) drsp
       )





collect_ATCs_hs :: (Ord a, Ord b, Ord c) => [(a,(b,(c,d)))] -> [(a,b,c,[d])]
collect_ATCs_hs xs = map (\((a,b,c),ds) -> (a,b,c,ds)) $ Map.assocs m
  where 
    m = foldl (\ m (a,(b,(c,d))) -> Map.insertWith (\ _ old -> d:old)--(flip (++))
                                               (a,b,c) 
                                               [d]
                                               m ) 
              Map.empty
              xs



--main = mapM_ (putStrLn . show) $ calculate_test_suite_w m_ex_H $ int_to_nat 8
main2 = do
  s <- Data.Time.getCurrentTime
  putStrLn $ "Started : " ++ (show s)
  --putStrLn $ show $ length $ calculate_test_suite_w m_ex_DR $ int_to_nat 12
  --putStrLn $ show $ size m_ex_DR
  --writeFile "dr_output" $ show $ calculate_test_suite_w m_ex_DR $ size m_ex_DR
  --writeFile "dr_output_l" $ unlines $ map show $ calculate_test_suite_w m_ex_DR $ size m_ex_DR
  ts_l <- readFile "dr_output_l"
  --let ts = read ts_l :: [(Integer, (FSM_ext Integer (), ([(Integer, (Integer, (Integer, Integer)))], FSM_ext (Sum (Integer, Integer) Integer) ())))]
  let ts = map (\t -> read t :: (Integer, (FSM_ext Integer (), ([(Integer, (Integer, (Integer, Integer)))], FSM_ext (Sum (Integer, Integer) Integer) ())))) 
               (lines ts_l)
  putStrLn $ show $ length ts
  l <- Data.Time.getCurrentTime
  putStrLn $ "Loaded  : " ++ (show l)
-- todo: inline collect_ATCs_hs?
  putStrLn $ show $ length $ collect_ATCs_hs ts
  f <- Data.Time.getCurrentTime
  putStrLn $ "Finished: " ++ (show f)

fsmName = "dr_small"
main = do
  s <- Data.Time.getCurrentTime
  putStrLn $ "Started : " ++ (show s)
  fsmFile <- readFile $ fsmName ++ ".fsm"
  case readFSM fsmFile of 
    Right fsm -> do 
      putStrLn $ show $ size fsm
      writeFile (fsmName ++ ".dot") $ fsmToDot fsm
      let ts_orig = calculate_test_suite_w fsm $ size fsm
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

      let (eds,uds,dds) = convert_tests' ts_m
      putStrLn $ show $ length eds
      putStrLn $ show $ length uds
      putStrLn $ show $ length dds
      v <- Data.Time.getCurrentTime
      putStrLn $ "Converted: " ++ (show v)

      writeFile (fsmName ++ "_test.dot") $ convert_to_dot (eds,uds,dds)

      f <- Data.Time.getCurrentTime
      putStrLn $ "Finished : " ++ (show f)

    
{-

main = do
    args <- System.Environment.getArgs
    fsmFile <- readFile (args !! 0)
    let m = (read (args !! 1)) :: Int 
    let fsmDotTarget = (args !! 2)
    let testDotTarget = (args !! 3)
    case readFSM fsmFile of 
        Right fsm -> do 
          writeFile fsmDotTarget $ fsmToDot fsm
          case calculate_test_suite_w fsm (int_to_nat m) of  
            (testSuite,testData) -> do
              writeFile testDotTarget $ convert_to_dot $ convert_tests $ testSuite
              mapM_ (putStrLn . show) testData
        Left err  -> putStrLn err


-}
