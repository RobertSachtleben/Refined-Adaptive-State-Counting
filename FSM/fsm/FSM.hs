{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  FSM(Sum(..), Comm_monoid_add, Nat, Num, Set(..), FSM_ext(..), bex, initial,
       target, nodes_from_distinct_paths, nodes, size, ball, find, image,
       m_ex_9, m_ex_H, from_FSM, pow_list, wf_transitions, observable,
       single_input, the, m_ex_DR, completely_specified, maximal_acyclic_paths,
       list_as_fun, prefix_pair_tests,
       r_distinguishable_state_pairs_with_separators_naive,
       d_reachable_states_with_preambles, m_traversal_paths_with_witness,
       preamble_prefix_tests, preamble_pair_tests, calculate_test_suite, sum,
       calculate_test_suite_set,
       maximal_pairwise_r_distinguishable_state_sets_from_separators,
       maximal_repetition_sets_from_separators)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

data Sum a b = Inl a | Inr b;

equal_sum :: forall a b. (Eq a, Eq b) => Sum a b -> Sum a b -> Bool;
equal_sum (Inl x1) (Inr x2) = False;
equal_sum (Inr x2) (Inl x1) = False;
equal_sum (Inr x2) (Inr y2) = x2 == y2;
equal_sum (Inl x1) (Inl y1) = x1 == y1;

instance (Eq a, Eq b) => Eq (Sum a b) where {
  a == b = equal_sum a b;
};

class Plus a where {
  plus :: a -> a -> a;
};

class (Plus a) => Semigroup_add a where {
};

class Zero a where {
  zero :: a;
};

class (Semigroup_add a, Zero a) => Monoid_add a where {
};

class (Semigroup_add a) => Ab_semigroup_add a where {
};

class (Ab_semigroup_add a, Monoid_add a) => Comm_monoid_add a where {
};

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data FSM_ext a b =
  FSM_ext a [Integer] [Integer] [(a, (Integer, (Integer, a)))] b;

bex :: forall a. Set a -> (a -> Bool) -> Bool;
bex (Set xs) p = any p xs;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

card :: forall a. (Eq a) => Set a -> Nat;
card (Set xs) = size_list (remdups xs);

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

transitions :: forall a b. FSM_ext a b -> [(a, (Integer, (Integer, a)))];
transitions (FSM_ext initial inputs outputs transitions more) = transitions;

outputs :: forall a b. FSM_ext a b -> [Integer];
outputs (FSM_ext initial inputs outputs transitions more) = outputs;

inputs :: forall a b. FSM_ext a b -> [Integer];
inputs (FSM_ext initial inputs outputs transitions more) = inputs;

io_valid_transitions ::
  forall a. FSM_ext a () -> [(a, (Integer, (Integer, a)))];
io_valid_transitions m =
  filter
    (\ t ->
      membera (inputs m) (fst (snd t)) &&
        membera (outputs m) (fst (snd (snd t))))
    (transitions m);

visited_states :: forall a. a -> [(a, (Integer, (Integer, a)))] -> [a];
visited_states q p = q : map (\ a -> snd (snd (snd a))) p;

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

initial :: forall a b. FSM_ext a b -> a;
initial (FSM_ext initial inputs outputs transitions more) = initial;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (membera xs x) && distinct xs;

last :: forall a. [a] -> a;
last (x : xs) = (if null xs then x else last xs);

target :: forall a. [(a, (Integer, (Integer, a)))] -> a -> a;
target p q = last (visited_states q p);

distinct_paths_up_to_length_from_initial ::
  forall a. (Eq a) => FSM_ext a () -> Nat -> [[(a, (Integer, (Integer, a)))]];
distinct_paths_up_to_length_from_initial m Zero_nat = [[]];
distinct_paths_up_to_length_from_initial m (Suc n) =
  let {
    pn = distinct_paths_up_to_length_from_initial m n;
  } in pn ++ map_filter
               (\ x ->
                 (if fst (snd x) == target (fst x) (initial m) &&
                       distinct
                         (visited_states (initial m) (fst x) ++
                           [snd (snd (snd (snd x)))])
                   then Just (fst x ++ [snd x]) else Nothing))
               (concat
                 (map_filter
                   (\ x ->
                     (if equal_nat (size_list x) n
                       then Just (map (\ a -> (x, a)) (io_valid_transitions m))
                       else Nothing))
                   pn));

nodes_from_distinct_paths :: forall a. (Eq a) => FSM_ext a () -> [a];
nodes_from_distinct_paths m =
  remdups
    (map (\ p -> target p (initial m))
      (distinct_paths_up_to_length_from_initial m
        (size_list (io_valid_transitions m))));

nodes :: forall a. (Eq a) => FSM_ext a () -> Set a;
nodes m = Set (nodes_from_distinct_paths m);

size :: forall a. (Eq a) => FSM_ext a () -> Nat;
size m = card (nodes m);

ball :: forall a. Set a -> (a -> Bool) -> Bool;
ball (Set xs) p = all p xs;

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) = (case n of {
                    Zero_nat -> [];
                    Suc m -> x : take m xs;
                  });

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

m_ex_9 :: FSM_ext Integer ();
m_ex_9 =
  FSM_ext (0 :: Integer) [(0 :: Integer), (1 :: Integer)]
    [(0 :: Integer), (1 :: Integer), (2 :: Integer), (3 :: Integer)]
    [((0 :: Integer), ((0 :: Integer), ((2 :: Integer), (2 :: Integer)))),
      ((0 :: Integer), ((0 :: Integer), ((3 :: Integer), (2 :: Integer)))),
      ((0 :: Integer), ((1 :: Integer), ((0 :: Integer), (3 :: Integer)))),
      ((0 :: Integer), ((1 :: Integer), ((1 :: Integer), (3 :: Integer)))),
      ((1 :: Integer), ((0 :: Integer), ((3 :: Integer), (2 :: Integer)))),
      ((1 :: Integer), ((1 :: Integer), ((1 :: Integer), (3 :: Integer)))),
      ((2 :: Integer), ((0 :: Integer), ((2 :: Integer), (2 :: Integer)))),
      ((2 :: Integer), ((1 :: Integer), ((3 :: Integer), (3 :: Integer)))),
      ((3 :: Integer), ((0 :: Integer), ((2 :: Integer), (2 :: Integer)))),
      ((3 :: Integer), ((1 :: Integer), ((0 :: Integer), (2 :: Integer)))),
      ((3 :: Integer), ((1 :: Integer), ((1 :: Integer), (1 :: Integer))))]
    ();

m_ex_H :: FSM_ext Integer ();
m_ex_H =
  FSM_ext (1 :: Integer) [(0 :: Integer), (1 :: Integer)]
    [(0 :: Integer), (1 :: Integer)]
    [((1 :: Integer), ((0 :: Integer), ((0 :: Integer), (2 :: Integer)))),
      ((1 :: Integer), ((0 :: Integer), ((1 :: Integer), (4 :: Integer)))),
      ((1 :: Integer), ((1 :: Integer), ((1 :: Integer), (4 :: Integer)))),
      ((2 :: Integer), ((0 :: Integer), ((0 :: Integer), (2 :: Integer)))),
      ((2 :: Integer), ((1 :: Integer), ((1 :: Integer), (4 :: Integer)))),
      ((3 :: Integer), ((0 :: Integer), ((1 :: Integer), (4 :: Integer)))),
      ((3 :: Integer), ((1 :: Integer), ((0 :: Integer), (1 :: Integer)))),
      ((3 :: Integer), ((1 :: Integer), ((1 :: Integer), (3 :: Integer)))),
      ((4 :: Integer), ((0 :: Integer), ((0 :: Integer), (3 :: Integer)))),
      ((4 :: Integer), ((1 :: Integer), ((0 :: Integer), (1 :: Integer))))]
    ();

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Coset xs) = Coset (removeAll x xs);
insert x (Set xs) = Set (inserta x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Coset xs) = not (membera xs x);
member x (Set xs) = membera xs x;

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Coset xs) = Coset (inserta x xs);
remove x (Set xs) = Set (removeAll x xs);

more :: forall a b. FSM_ext a b -> b;
more (FSM_ext initial inputs outputs transitions more) = more;

from_FSM :: forall a. FSM_ext a () -> a -> FSM_ext a ();
from_FSM m q = FSM_ext q (inputs m) (outputs m) (transitions m) (more m);

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

is_prefix :: forall a. (Eq a) => [a] -> [a] -> Bool;
is_prefix [] uu = True;
is_prefix (x : xs) [] = False;
is_prefix (x : xs) (y : ys) = x == y && is_prefix xs ys;

pow_list :: forall a. [a] -> [[a]];
pow_list [] = [[]];
pow_list (x : xs) = let {
                      pxs = pow_list xs;
                    } in pxs ++ map (\ a -> x : a) pxs;

prefixes :: forall a. [a] -> [[a]];
prefixes [] = [[]];
prefixes (v : va) = prefixes (butlast (v : va)) ++ [v : va];

wf_transitions ::
  forall a. (Eq a) => FSM_ext a () -> [(a, (Integer, (Integer, a)))];
wf_transitions m =
  filter
    (\ t ->
      member (fst t) (nodes m) &&
        membera (inputs m) (fst (snd t)) &&
          membera (outputs m) (fst (snd (snd t))))
    (transitions m);

observable :: forall a. (Eq a) => FSM_ext a () -> Bool;
observable m =
  all (\ t1 ->
        all (\ t2 ->
              (if fst t1 == fst t2 &&
                    fst (snd t1) == fst (snd t2) &&
                      fst (snd (snd t1)) == fst (snd (snd t2))
                then snd (snd (snd t1)) == snd (snd (snd t2)) else True))
          (wf_transitions m))
    (wf_transitions m);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

find_index :: forall a. (a -> Bool) -> [a] -> Maybe Nat;
find_index f [] = Nothing;
find_index f (x : xs) =
  (if f x then Just Zero_nat else (case find_index f xs of {
                                    Nothing -> Nothing;
                                    Just k -> Just (Suc k);
                                  }));

single_input_by_transition_list ::
  forall a. (Eq a) => FSM_ext a () -> [(a, (Integer, (Integer, a)))] -> Bool;
single_input_by_transition_list m [] = True;
single_input_by_transition_list m (t1 : ts) =
  (case find (\ t2 ->
               not (t1 == t2) &&
                 fst t1 == fst t2 && not (fst (snd t1) == fst (snd t2)))
          ts
    of {
    Nothing -> single_input_by_transition_list m ts;
    Just _ -> False;
  });

single_input :: forall a. (Eq a) => FSM_ext a () -> Bool;
single_input m = single_input_by_transition_list m (remdups (wf_transitions m));

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

deadlock_state :: forall a. (Eq a) => FSM_ext a () -> a -> Bool;
deadlock_state m q = not (any (\ t -> fst t == q) (wf_transitions m));

cartesian_product_list :: forall a b. [a] -> [b] -> [(a, b)];
cartesian_product_list xs ys = concatMap (\ x -> map (\ a -> (x, a)) ys) xs;

product_transitions ::
  forall a b.
    (Eq a,
      Eq b) => FSM_ext a () ->
                 FSM_ext b () -> [((a, b), (Integer, (Integer, (a, b))))];
product_transitions a b =
  map_filter
    (\ x ->
      (if (case x of {
            (t1, t2) ->
              fst (snd t1) == fst (snd t2) &&
                fst (snd (snd t1)) == fst (snd (snd t2));
          })
        then Just (case x of {
                    (t1, t2) ->
                      ((fst t1, fst t2),
                        (fst (snd t1),
                          (fst (snd (snd t1)),
                            (snd (snd (snd t1)), snd (snd (snd t2))))));
                  })
        else Nothing))
    (cartesian_product_list (wf_transitions a) (wf_transitions b));

product ::
  forall a b. (Eq a, Eq b) => FSM_ext a () -> FSM_ext b () -> FSM_ext (a, b) ();
product a b =
  FSM_ext (initial a, initial b) (inputs a ++ inputs b) (outputs a ++ outputs b)
    (product_transitions a b) (more a);

m_ex_DR :: FSM_ext Integer ();
m_ex_DR =
  FSM_ext (0 :: Integer) [(0 :: Integer), (1 :: Integer)]
    [(0 :: Integer), (1 :: Integer), (2 :: Integer)]
    [((0 :: Integer), ((0 :: Integer), ((0 :: Integer), (100 :: Integer)))),
      ((100 :: Integer), ((0 :: Integer), ((0 :: Integer), (101 :: Integer)))),
      ((100 :: Integer), ((0 :: Integer), ((1 :: Integer), (101 :: Integer)))),
      ((101 :: Integer), ((0 :: Integer), ((0 :: Integer), (102 :: Integer)))),
      ((101 :: Integer), ((0 :: Integer), ((1 :: Integer), (102 :: Integer)))),
      ((102 :: Integer), ((0 :: Integer), ((0 :: Integer), (103 :: Integer)))),
      ((102 :: Integer), ((0 :: Integer), ((1 :: Integer), (103 :: Integer)))),
      ((103 :: Integer), ((0 :: Integer), ((0 :: Integer), (104 :: Integer)))),
      ((103 :: Integer), ((0 :: Integer), ((1 :: Integer), (104 :: Integer)))),
      ((104 :: Integer), ((0 :: Integer), ((0 :: Integer), (100 :: Integer)))),
      ((104 :: Integer), ((0 :: Integer), ((1 :: Integer), (100 :: Integer)))),
      ((104 :: Integer), ((1 :: Integer), ((0 :: Integer), (400 :: Integer)))),
      ((0 :: Integer), ((0 :: Integer), ((2 :: Integer), (200 :: Integer)))),
      ((200 :: Integer), ((0 :: Integer), ((2 :: Integer), (201 :: Integer)))),
      ((201 :: Integer), ((0 :: Integer), ((2 :: Integer), (202 :: Integer)))),
      ((202 :: Integer), ((0 :: Integer), ((2 :: Integer), (203 :: Integer)))),
      ((203 :: Integer), ((0 :: Integer), ((2 :: Integer), (200 :: Integer)))),
      ((203 :: Integer), ((1 :: Integer), ((0 :: Integer), (400 :: Integer)))),
      ((0 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((100 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((101 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((102 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((103 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((200 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((201 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((202 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((300 :: Integer), ((0 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((300 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((400 :: Integer), ((0 :: Integer), ((0 :: Integer), (300 :: Integer)))),
      ((300 :: Integer), ((1 :: Integer), ((0 :: Integer), (300 :: Integer))))]
    ();

non_sym_dist_pairsa :: forall a. [a] -> [(a, a)];
non_sym_dist_pairsa [] = [];
non_sym_dist_pairsa (x : xs) = map (\ a -> (x, a)) xs ++ non_sym_dist_pairsa xs;

non_sym_dist_pairs :: forall a. (Eq a) => [a] -> [(a, a)];
non_sym_dist_pairs xs = non_sym_dist_pairsa (remdups xs);

completely_specified :: forall a. (Eq a) => FSM_ext a () -> Bool;
completely_specified m =
  ball (nodes m)
    (\ q ->
      all (\ x ->
            any (\ t -> fst t == q && fst (snd t) == x) (wf_transitions m))
        (inputs m));

one_nat :: Nat;
one_nat = Suc Zero_nat;

inf_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
inf_set a (Coset xs) = fold remove xs a;
inf_set a (Set xs) = Set (filter (\ x -> member x a) xs);

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);
sup_set (Set xs) a = fold insert xs a;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

d_states ::
  forall a.
    (Eq a) => [(a, Integer)] ->
                Set (a, (Integer, (Integer, a))) -> Nat -> a -> [(a, Integer)];
d_states qx h Zero_nat q = [];
d_states qx h (Suc k) q =
  let {
    qa = d_states qx h k q;
  } in (if less_nat (size_list qa) k then qa
         else (case find (\ qxa ->
                           not (fst qxa == q) &&
                             all (\ qxaa -> not (fst qxa == fst qxaa)) qa &&
                               bex h (\ t ->
                                       fst t == fst qxa &&
 fst (snd t) == snd qxa) &&
                                 ball h
                                   (\ t ->
                                     (if fst t == fst qxa &&
   fst (snd t) == snd qxa
                                       then snd (snd (snd t)) == q ||
      any (\ qxb -> fst qxb == snd (snd (snd t))) qa
                                       else True)))
                      qx
                of {
                Nothing -> qa;
                Just qxa -> qa ++ [qxa];
              }));

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

maximal_acyclic_paths ::
  forall a. (Eq a) => FSM_ext a () -> [[(a, (Integer, (Integer, a)))]];
maximal_acyclic_paths m =
  let {
    ps = distinct_paths_up_to_length_from_initial m
           (minus_nat (size m) one_nat);
  } in filter (\ p -> not (any (\ pa -> is_prefix p pa && not (p == pa)) ps))
         ps;

less_eq_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_eq_set (Coset []) (Set []) = False;
less_eq_set a (Coset ys) = all (\ y -> not (member y a)) ys;
less_eq_set (Set xs) b = all (\ x -> member x b) xs;

less_set :: forall a. (Eq a) => Set a -> Set a -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

s_states ::
  forall a.
    (Eq a) => [(a, Integer)] ->
                Set (a, (Integer, (Integer, a))) -> Nat -> [(a, Integer)];
s_states qx h Zero_nat = [];
s_states qx h (Suc k) =
  let {
    q = s_states qx h k;
  } in (if less_nat (size_list q) k then q
         else (case find (\ qxa ->
                           all (\ qxaa -> not (fst qxa == fst qxaa)) q &&
                             ball h
                               (\ t ->
                                 (if fst t == fst qxa && fst (snd t) == snd qxa
                                   then any
  (\ qxb -> fst qxb == snd (snd (snd t))) q
                                   else True)))
                      qx
                of {
                Nothing -> q;
                Just qxa -> q ++ [qxa];
              }));

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

list_as_fun :: forall a b. (Eq a) => [(a, b)] -> b -> a -> b;
list_as_fun xs defaultValue = (\ x -> (case find (\ (a, _) -> a == x) xs of {
Nothing -> defaultValue;
Just (_, b) -> b;
                                      }));

d_states_opt :: forall a. (Eq a) => FSM_ext a () -> Nat -> a -> [(a, Integer)];
d_states_opt m k q =
  d_states
    (concatMap (\ qa -> map (\ a -> (qa, a)) (inputs m))
      (nodes_from_distinct_paths m))
    (Set (wf_transitions m)) k q;

prefix_pairs :: forall a. [a] -> [([a], [a])];
prefix_pairs [] = [];
prefix_pairs (v : va) =
  prefix_pairs (butlast (v : va)) ++
    map (\ ys -> (ys, v : va)) (butlast (prefixes (v : va)));

times_nat :: Nat -> Nat -> Nat;
times_nat Zero_nat n = Zero_nat;
times_nat (Suc m) n = plus_nat n (times_nat m n);

s_states_opt :: forall a. (Eq a) => FSM_ext a () -> Nat -> [(a, Integer)];
s_states_opt c k =
  s_states
    (concatMap (\ q -> map (\ a -> (q, a)) (inputs c))
      (nodes_from_distinct_paths c))
    (Set (wf_transitions c)) k;

prefix_pair_testsa ::
  forall a b.
    (Eq a) => a -> (a -> a -> FSM_ext b ()) ->
                     ([(a, (Integer, (Integer, a)))], (Set a, Set a)) ->
                       [[(a, ([(a, (Integer, (Integer, a)))], FSM_ext b ()))]];
prefix_pair_testsa q fRD (p, (rd, dr)) =
  map_filter
    (\ x ->
      (if (case x of {
            (p1, p2) ->
              member (target p1 q) rd &&
                member (target p2 q) rd && not (target p1 q == target p2 q);
          })
        then Just (case x of {
                    (p1, p2) ->
                      [(q, (p1, fRD (target p1 q) (target p2 q))),
                        (q, (p2, fRD (target p1 q) (target p2 q)))];
                  })
        else Nothing))
    (prefix_pairs p);

prefix_pair_tests ::
  forall a b.
    (Eq a) => a -> (a -> a -> FSM_ext b ()) ->
                     [([(a, (Integer, (Integer, a)))], (Set a, Set a))] ->
                       [(a, ([(a, (Integer, (Integer, a)))], FSM_ext b ()))];
prefix_pair_tests q fRD pds = concat (concatMap (prefix_pair_testsa q fRD) pds);

choose_state_separator_deadlock_input ::
  forall a.
    (Eq a) => FSM_ext a () -> FSM_ext (a, a) () -> (a, a) -> Maybe Integer;
choose_state_separator_deadlock_input m s qq =
  (if member qq (nodes s) && deadlock_state s qq
    then find (\ x ->
                not (any (\ t1 ->
                           any (\ t2 ->
                                 fst t1 == fst qq &&
                                   fst t2 == snd qq &&
                                     fst (snd t1) == x &&
                                       fst (snd t2) == x &&
 fst (snd (snd t1)) == fst (snd (snd t2)))
                             (wf_transitions m))
                      (wf_transitions m)))
           (inputs m)
    else Nothing);

distinguishing_transitions_right ::
  forall a.
    (Eq a) => FSM_ext a () ->
                a -> a -> [(Sum (a, a) a, (Integer, (Integer, Sum (a, a) a)))];
distinguishing_transitions_right m q1 q2 =
  map_filter
    (\ x ->
      (if fst (snd x) == snd (fst x) &&
            not (any (\ t ->
                       fst t == fst (fst x) &&
                         fst (snd t) == fst (snd (snd x)) &&
                           fst (snd (snd t)) == fst (snd (snd (snd x))))
                  (transitions m))
        then Just (Inl (fst x),
                    (fst (snd (snd x)), (fst (snd (snd (snd x))), Inr q2)))
        else Nothing))
    (concatMap (\ qq -> map (\ a -> (qq, a)) (wf_transitions m))
      (nodes_from_distinct_paths (product (from_FSM m q1) (from_FSM m q2))));

distinguishing_transitions_left ::
  forall a.
    (Eq a) => FSM_ext a () ->
                a -> a -> [(Sum (a, a) a, (Integer, (Integer, Sum (a, a) a)))];
distinguishing_transitions_left m q1 q2 =
  map_filter
    (\ x ->
      (if fst (snd x) == fst (fst x) &&
            not (any (\ t ->
                       fst t == snd (fst x) &&
                         fst (snd t) == fst (snd (snd x)) &&
                           fst (snd (snd t)) == fst (snd (snd (snd x))))
                  (transitions m))
        then Just (Inl (fst x),
                    (fst (snd (snd x)), (fst (snd (snd (snd x))), Inr q1)))
        else Nothing))
    (concatMap (\ qq -> map (\ a -> (qq, a)) (wf_transitions m))
      (nodes_from_distinct_paths (product (from_FSM m q1) (from_FSM m q2))));

state_separator_from_product_submachine ::
  forall a.
    (Eq a) => FSM_ext a () -> FSM_ext (a, a) () -> FSM_ext (Sum (a, a) a) ();
state_separator_from_product_submachine m s =
  FSM_ext (Inl (initial s)) (inputs m) (outputs m)
    (let {
       t_old =
         map (\ t ->
               (Inl (fst t),
                 (fst (snd t), (fst (snd (snd t)), Inl (snd (snd (snd t)))))))
           (wf_transitions s);
       t_left =
         map_filter
           (\ x ->
             (if fst (snd x) == fst (fst x) &&
                   choose_state_separator_deadlock_input m s (fst x) ==
                     Just (fst (snd (snd x)))
               then Just (Inl (fst x),
                           (fst (snd (snd x)),
                             (fst (snd (snd (snd x))), Inr (fst (initial s)))))
               else Nothing))
           (concatMap (\ qq -> map (\ a -> (qq, a)) (wf_transitions m))
             (nodes_from_distinct_paths
               (product (from_FSM m (fst (initial s)))
                 (from_FSM m (snd (initial s))))));
       t_right =
         map_filter
           (\ x ->
             (if fst (snd x) == snd (fst x) &&
                   choose_state_separator_deadlock_input m s (fst x) ==
                     Just (fst (snd (snd x)))
               then Just (Inl (fst x),
                           (fst (snd (snd x)),
                             (fst (snd (snd (snd x))), Inr (snd (initial s)))))
               else Nothing))
           (concatMap (\ qq -> map (\ a -> (qq, a)) (wf_transitions m))
             (nodes_from_distinct_paths
               (product (from_FSM m (fst (initial s)))
                 (from_FSM m (snd (initial s))))));
     } in t_old ++
            t_left ++
              t_right ++
                filter
                  (\ t ->
                    not (member t
                          (sup_set (sup_set (Set t_old) (Set t_left))
                            (Set t_right))) &&
                      any (\ ta ->
                            equal_sum (fst t) (fst ta) &&
                              fst (snd t) == fst (snd ta))
                        t_old)
                  (distinguishing_transitions_left m (fst (initial s))
                    (snd (initial s))) ++
                  filter
                    (\ t ->
                      not (member t
                            (sup_set (sup_set (Set t_old) (Set t_left))
                              (Set t_right))) &&
                        any (\ ta ->
                              equal_sum (fst t) (fst ta) &&
                                fst (snd t) == fst (snd ta))
                          t_old)
                    (distinguishing_transitions_right m (fst (initial s))
                      (snd (initial s))))
    (more m);

calculate_state_separator_from_s_states ::
  forall a.
    (Eq a) => FSM_ext a () -> a -> a -> Maybe (FSM_ext (Sum (a, a) a) ());
calculate_state_separator_from_s_states m q1 q2 =
  let {
    pr = product (from_FSM m q1) (from_FSM m q2);
    ss = s_states_opt pr (size pr);
  } in (case find_index (\ qqt -> fst qqt == (q1, q2)) ss of {
         Nothing -> Nothing;
         Just i ->
           Just (state_separator_from_product_submachine m
                  (FSM_ext (q1, q2) (inputs pr) (outputs pr)
                    (filter
                      (\ t ->
                        not (is_none
                              (find (\ qqx ->
                                      fst t == fst qqx &&
fst (snd t) == snd qqx)
                                (take (Suc i) ss))))
                      (wf_transitions pr))
                    (more m)));
       });

r_distinguishable_state_pairs_with_separators_naive ::
  forall a. (Eq a) => FSM_ext a () -> [((a, a), FSM_ext (Sum (a, a) a) ())];
r_distinguishable_state_pairs_with_separators_naive m =
  let {
    nonSymNodes = non_sym_dist_pairs (nodes_from_distinct_paths m);
    nonSymSeps =
      map (\ (q1, q2) ->
            ((q1, q2), calculate_state_separator_from_s_states m q1 q2))
        nonSymNodes;
    a = map_filter
          (\ x ->
            (if (case x of {
                  (a, b) -> (case a of {
                              (_, _) -> (\ aa -> not (is_none aa));
                            })
                              b;
                })
              then Just (case x of {
                          (a, b) ->
                            (case a of {
                              (q1, q2) -> (\ aa -> ((q1, q2), the aa));
                            })
                              b;
                        })
              else Nothing))
          nonSymSeps;
  } in concatMap
         (\ (aa, b) ->
           (case aa of {
             (q1, q2) -> (\ ab -> [((q1, q2), ab), ((q2, q1), ab)]);
           })
             b)
         a;

calculate_state_preamble_from_d_states ::
  forall a. (Eq a) => FSM_ext a () -> a -> Maybe (FSM_ext a ());
calculate_state_preamble_from_d_states m q =
  (if q == initial m
    then Just (FSM_ext (initial m) (inputs m) (outputs m) [] (more m))
    else let {
           ds = d_states_opt m (size m) q;
         } in (case find_index (\ qqt -> fst qqt == initial m) ds of {
                Nothing -> Nothing;
                Just i ->
                  Just (FSM_ext (initial m) (inputs m) (outputs m)
                         (filter
                           (\ t ->
                             any (\ qqx ->
                                   fst t == fst qqx && fst (snd t) == snd qqx)
                               (take (Suc i) ds))
                           (wf_transitions m))
                         (more m));
              }));

d_reachable_states_with_preambles ::
  forall a. (Eq a) => FSM_ext a () -> [(a, FSM_ext a ())];
d_reachable_states_with_preambles m =
  map_filter
    (\ x ->
      (if not (is_none (snd x)) then Just (fst x, the (snd x)) else Nothing))
    (map (\ q -> (q, calculate_state_preamble_from_d_states m q))
      (nodes_from_distinct_paths m));

paths_up_to_length_or_condition_with_witness ::
  forall a b.
    (Eq a) => FSM_ext a () ->
                a -> Nat ->
                       ([(a, (Integer, (Integer, a)))] -> Maybe b) ->
                         [(a, (Integer, (Integer, a)))] ->
                           [([(a, (Integer, (Integer, a)))], b)];
paths_up_to_length_or_condition_with_witness m q Zero_nat f pref =
  (case f pref of {
    Nothing -> [];
    Just x -> [(pref, x)];
  });
paths_up_to_length_or_condition_with_witness m q (Suc k) f pref =
  (case f pref of {
    Nothing ->
      concat
        (map_filter
          (\ x ->
            (if fst x == target pref q
              then Just (paths_up_to_length_or_condition_with_witness m q k f
                          (pref ++ [x]))
              else Nothing))
          (wf_transitions m));
    Just x -> [(pref, x)];
  });

m_traversal_paths_with_witness_up_to_length ::
  forall a.
    (Eq a) => FSM_ext a () ->
                a -> [(Set a, Set a)] ->
                       Nat ->
                         Nat ->
                           [([(a, (Integer, (Integer, a)))], (Set a, Set a))];
m_traversal_paths_with_witness_up_to_length ma q d m k =
  paths_up_to_length_or_condition_with_witness ma q k
    (\ p ->
      find (\ da ->
             less_eq_nat (Suc (minus_nat m (card (snd da))))
               (size_list
                 (filter (\ t -> member (snd (snd (snd t))) (fst da)) p)))
        d)
    [];

m_traversal_paths_with_witness ::
  forall a.
    (Eq a) => FSM_ext a () ->
                a -> [(Set a, Set a)] ->
                       Nat ->
                         [([(a, (Integer, (Integer, a)))], (Set a, Set a))];
m_traversal_paths_with_witness ma q d m =
  m_traversal_paths_with_witness_up_to_length ma q d m
    (Suc (times_nat (size ma) m));

preamble_prefix_tests ::
  forall a b.
    (Eq a) => a -> (a -> a -> FSM_ext b ()) ->
                     [([(a, (Integer, (Integer, a)))], (Set a, Set a))] ->
                       [(a, FSM_ext a ())] ->
                         [(a, ([(a, (Integer, (Integer, a)))], FSM_ext b ()))];
preamble_prefix_tests q fRD pds ps =
  concat
    (map_filter
      (\ x ->
        (if (case x of {
              (a, b) ->
                (case a of {
                  (_, (rd, _)) ->
                    (\ (aa, ba) ->
                      (case aa of {
                        (q2, _) ->
                          (\ p1 ->
                            member (target p1 q) rd &&
                              member q2 rd && not (target p1 q == q2));
                      })
                        ba);
                })
                  b;
            })
          then Just (case x of {
                      (a, b) ->
                        (case a of {
                          (_, (_, _)) ->
                            (\ (aa, ba) ->
                              (case aa of {
                                (q2, _) ->
                                  (\ p1 ->
                                    [(q, (p1, fRD (target p1 q) q2)),
                                      (q2, ([], fRD (target p1 q) q2))]);
                              })
                                ba);
                        })
                          b;
                    })
          else Nothing))
      (concatMap
        (\ (a, b) ->
          (case a of {
            (p, (rd, dr)) ->
              (\ (q2, p2) ->
                map (\ p1 -> ((p, (rd, dr)), ((q2, p2), p1))) (prefixes p));
          })
            b)
        (cartesian_product_list pds ps)));

preamble_pair_tests ::
  forall a b.
    (Eq a) => [(a, FSM_ext a ())] ->
                [((a, a), FSM_ext b ())] ->
                  [(a, ([(a, (Integer, (Integer, a)))], FSM_ext b ()))];
preamble_pair_tests ps rds =
  concatMap
    (\ (a, b) ->
      (case a of {
        (q1, _) ->
          (\ (q2, _) ->
            (case find (\ qqA -> fst qqA == (q1, q2)) rds of {
              Nothing -> [];
              Just ((_, _), aa) -> [(q1, ([], aa)), (q2, ([], aa))];
            }));
      })
        b)
    (cartesian_product_list ps ps);

calculate_test_suite ::
  forall a.
    (Eq a) => FSM_ext a () ->
                Nat ->
                  ([(a, ([(a, (Integer, (Integer, a)))],
                          FSM_ext (Sum (a, a) a) ()))],
                    [(a, FSM_ext a ())]);
calculate_test_suite ma m =
  let {
    rdssl = r_distinguishable_state_pairs_with_separators_naive ma;
    rds = Set (map fst rdssl);
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
    _ = concatMap (\ (q, _) -> map (\ (p, _) -> (q, p)) (fTP q)) drsp;
    prefixPairTests =
      concatMap (\ (q, _) -> prefix_pair_tests q fRD (fTP q)) drsp;
    preamblePrefixTests =
      concatMap (\ (q, _) -> preamble_prefix_tests q fRD (fTP q) drsp) drsp;
    preamblePairTests = preamble_pair_tests drsp rdssl;
  } in (prefixPairTests ++ preamblePrefixTests ++ preamblePairTests, drsp);

sum_list :: forall a. (Monoid_add a) => [a] -> a;
sum_list xs = foldr plus xs zero;

sum :: forall a b. (Eq a, Comm_monoid_add b) => (a -> b) -> Set a -> b;
sum g (Set xs) = sum_list (map g (remdups xs));

d_reachable_states :: forall a. (Eq a) => FSM_ext a () -> [a];
d_reachable_states m = map fst (d_reachable_states_with_preambles m);

calculate_test_suite_set ::
  forall a.
    (Eq a) => FSM_ext a () ->
                Nat ->
                  (Set (a, ([(a, (Integer, (Integer, a)))],
                             FSM_ext (Sum (a, a) a) ())),
                    [(a, FSM_ext a ())]);
calculate_test_suite_set ma m = (case calculate_test_suite ma m of {
                                  (ts, a) -> (Set ts, a);
                                });

r_distinguishable_state_pairs_with_separators ::
  forall a. (Eq a) => FSM_ext a () -> Set ((a, a), FSM_ext (Sum (a, a) a) ());
r_distinguishable_state_pairs_with_separators m =
  Set (r_distinguishable_state_pairs_with_separators_naive m);

pairwise_r_distinguishable_state_sets_from_separators ::
  forall a. (Eq a) => FSM_ext a () -> [Set a];
pairwise_r_distinguishable_state_sets_from_separators m =
  let {
    rds = image fst (r_distinguishable_state_pairs_with_separators m);
  } in filter
         (\ s ->
           ball s
             (\ q1 ->
               ball s
                 (\ q2 ->
                   (if not (q1 == q2) then member (q1, q2) rds else True))))
         (map Set (pow_list (nodes_from_distinct_paths m)));

maximal_pairwise_r_distinguishable_state_sets_from_separators ::
  forall a. (Eq a) => FSM_ext a () -> [Set a];
maximal_pairwise_r_distinguishable_state_sets_from_separators m =
  let {
    pr = pairwise_r_distinguishable_state_sets_from_separators m;
  } in filter (\ s -> not (any (less_set s) pr)) pr;

maximal_repetition_sets_from_separators ::
  forall a. (Eq a) => FSM_ext a () -> [(Set a, Set a)];
maximal_repetition_sets_from_separators m =
  map (\ s -> (s, inf_set s (Set (d_reachable_states m))))
    (maximal_pairwise_r_distinguishable_state_sets_from_separators m);

}
