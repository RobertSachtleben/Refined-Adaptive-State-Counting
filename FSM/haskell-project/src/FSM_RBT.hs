{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  FSM_RBT(Sum, Linorder, Nat, Num, Set, FSM_ext(..), m_ex_DR,
           calculate_test_suite_rbt)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

data Sum a b = Inl a | Inr b;

less_eq_sum :: forall a b. (Ord a, Ord b) => Sum a b -> Sum a b -> Bool;
less_eq_sum (Inl a) (Inl b) = less_eq a b;
less_eq_sum (Inl a) (Inr b) = True;
less_eq_sum (Inr a) (Inl b) = False;
less_eq_sum (Inr a) (Inr b) = less_eq a b;

equal_sum :: forall a b. (Eq a, Eq b) => Sum a b -> Sum a b -> Bool;
equal_sum (Inl x1) (Inr x2) = False;
equal_sum (Inr x2) (Inl x1) = False;
equal_sum (Inr x2) (Inr y2) = x2 == y2;
equal_sum (Inl x1) (Inl y1) = x1 == y1;

less_sum ::
  forall a b. (Eq a, Ord a, Eq b, Ord b) => Sum a b -> Sum a b -> Bool;
less_sum a b = less_eq_sum a b && not (equal_sum a b);

instance (Eq a, Ord a, Eq b, Ord b) => Ord (Sum a b) where {
  less_eq = less_eq_sum;
  less = less_sum;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

class (Order a) => Linorder a where {
};

instance (Eq a, Linorder a, Eq b, Linorder b) => Preorder (Sum a b) where {
};

instance (Eq a, Linorder a, Eq b, Linorder b) => Order (Sum a b) where {
};

instance (Eq a, Linorder a, Eq b, Linorder b) => Linorder (Sum a b) where {
};

less_eq_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less_eq y1 y2;

less_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less y1 y2;

instance (Ord a, Ord b) => Ord (a, b) where {
  less_eq = less_eq_prod;
  less = less_prod;
};

instance (Preorder a, Preorder b) => Preorder (a, b) where {
};

instance (Order a, Order b) => Order (a, b) where {
};

instance (Linorder a, Linorder b) => Linorder (a, b) where {
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

instance Preorder Integer where {
};

instance Order Integer where {
};

instance Linorder Integer where {
};

data Nat = Zero_nat | Suc Nat;

data Num = One | Bit0 Num | Bit1 Num;

data Color = R | B;

data Rbta a b = Empty | Branch Color (Rbta a b) a b (Rbta a b);

newtype Rbt b a = RBT (Rbta b a);

data Set a = Set (Rbt a ()) | Coset (Rbt a ());

data FSM_ext a b =
  FSM_ext a [Integer] [Integer] [(a, (Integer, (Integer, a)))] b;

data Compare = LT | GT | EQ;

impl_of :: forall b a. (Linorder b) => Rbt b a -> Rbta b a;
impl_of (RBT x) = x;

foldia ::
  forall a b c.
    (Linorder b) => (a -> Bool) -> (b -> c -> a -> a) -> Rbta b c -> a -> a;
foldia c f Empty s = s;
foldia c f (Branch col l k v r) s =
  (if c s then let {
                 sa = foldia c f l s;
               } in (if c sa then foldia c f r (f k v sa) else sa)
    else s);

foldi ::
  forall a b c.
    (Linorder b) => (a -> Bool) -> (b -> c -> a -> a) -> Rbt b c -> a -> a;
foldi x xb xd = foldia x xb (impl_of xd);

bex :: forall a. (Linorder a) => Set a -> (a -> Bool) -> Bool;
bex (Set t) p = foldi (\ s -> s == False) (\ k _ s -> s || p k) t False;

plus_nat :: Nat -> Nat -> Nat;
plus_nat (Suc m) n = plus_nat m (Suc n);
plus_nat Zero_nat n = n;

one_nat :: Nat;
one_nat = Suc Zero_nat;

folda :: forall a b c. (a -> b -> c -> c) -> Rbta a b -> c -> c;
folda f (Branch c lt k v rt) x = folda f rt (f k v (folda f lt x));
folda f Empty x = x;

fold :: forall a b c. (Linorder a) => (a -> b -> c -> c) -> Rbt a b -> c -> c;
fold x xc = folda x (impl_of xc);

card :: forall a. (Linorder a) => Set a -> Nat;
card (Set t) = fold (\ _ _ ta -> plus_nat ta one_nat) t Zero_nat;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (Suc n) xs;
gen_length n [] = n;

size_list :: forall a. [a] -> Nat;
size_list = gen_length Zero_nat;

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

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

io_valid_transitions ::
  forall a b. FSM_ext a b -> [(a, (Integer, (Integer, a)))];
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
  forall a b. (Eq a) => FSM_ext a b -> Nat -> [[(a, (Integer, (Integer, a)))]];
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

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

nodes_from_distinct_paths :: forall a b. (Eq a) => FSM_ext a b -> [a];
nodes_from_distinct_paths m =
  remdups
    (map (\ p -> target p (initial m))
      (distinct_paths_up_to_length_from_initial m
        (size_list (io_valid_transitions m))));

empty :: forall a b. (Linorder a) => Rbt a b;
empty = RBT Empty;

bot_set :: forall a. (Linorder a) => Set a;
bot_set = Set empty;

balance :: forall a b. Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
balance (Branch R a w x b) s t (Branch R c y z d) =
  Branch R (Branch B a w x b) s t (Branch B c y z d);
balance (Branch R (Branch R a w x b) s t c) y z Empty =
  Branch R (Branch B a w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch R a w x b) s t c) y z (Branch B va vb vc vd) =
  Branch R (Branch B a w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R Empty w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance (Branch R (Branch B va vb vc vd) w x (Branch R b s t c)) y z Empty =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch R Empty w x (Branch R b s t c)) y z (Branch B va vb vc vd) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch R (Branch B ve vf vg vh) w x (Branch R b s t c)) y z
  (Branch B va vb vc vd) =
  Branch R (Branch B (Branch B ve vf vg vh) w x b) s t
    (Branch B c y z (Branch B va vb vc vd));
balance Empty w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z d);
balance (Branch B va vb vc vd) w x (Branch R b s t (Branch R c y z d)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z d);
balance Empty w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z Empty);
balance Empty w x (Branch R (Branch R b s t c) y z (Branch B va vb vc vd)) =
  Branch R (Branch B Empty w x b) s t (Branch B c y z (Branch B va vb vc vd));
balance (Branch B va vb vc vd) w x (Branch R (Branch R b s t c) y z Empty) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t (Branch B c y z Empty);
balance (Branch B va vb vc vd) w x
  (Branch R (Branch R b s t c) y z (Branch B ve vf vg vh)) =
  Branch R (Branch B (Branch B va vb vc vd) w x b) s t
    (Branch B c y z (Branch B ve vf vg vh));
balance Empty s t Empty = Branch B Empty s t Empty;
balance Empty s t (Branch B va vb vc vd) =
  Branch B Empty s t (Branch B va vb vc vd);
balance Empty s t (Branch v Empty vb vc Empty) =
  Branch B Empty s t (Branch v Empty vb vc Empty);
balance Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty) =
  Branch B Empty s t (Branch v (Branch B ve vf vg vh) vb vc Empty);
balance Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi)) =
  Branch B Empty s t (Branch v Empty vb vc (Branch B vf vg vh vi));
balance Empty s t (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi))
  = Branch B Empty s t
      (Branch v (Branch B ve vj vk vl) vb vc (Branch B vf vg vh vi));
balance (Branch B va vb vc vd) s t Empty =
  Branch B (Branch B va vb vc vd) s t Empty;
balance (Branch B va vb vc vd) s t (Branch B ve vf vg vh) =
  Branch B (Branch B va vb vc vd) s t (Branch B ve vf vg vh);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty) =
  Branch B (Branch B va vb vc vd) s t (Branch v Empty vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v (Branch B vi vj vk vl) vf vg Empty)
  = Branch B (Branch B va vb vc vd) s t
      (Branch v (Branch B vi vj vk vl) vf vg Empty);
balance (Branch B va vb vc vd) s t (Branch v Empty vf vg (Branch B vj vk vl vm))
  = Branch B (Branch B va vb vc vd) s t
      (Branch v Empty vf vg (Branch B vj vk vl vm));
balance (Branch B va vb vc vd) s t
  (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm)) =
  Branch B (Branch B va vb vc vd) s t
    (Branch v (Branch B vi vn vo vp) vf vg (Branch B vj vk vl vm));
balance (Branch v Empty vb vc Empty) s t Empty =
  Branch B (Branch v Empty vb vc Empty) s t Empty;
balance (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty =
  Branch B (Branch v Empty vb vc (Branch B ve vf vg vh)) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty =
  Branch B (Branch v (Branch B vf vg vh vi) vb vc Empty) s t Empty;
balance (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t Empty
  = Branch B (Branch v (Branch B vf vg vh vi) vb vc (Branch B ve vj vk vl)) s t
      Empty;
balance (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd) =
  Branch B (Branch v Empty vf vg Empty) s t (Branch B va vb vc vd);
balance (Branch v Empty vf vg (Branch B vi vj vk vl)) s t (Branch B va vb vc vd)
  = Branch B (Branch v Empty vf vg (Branch B vi vj vk vl)) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg Empty) s t (Branch B va vb vc vd)
  = Branch B (Branch v (Branch B vj vk vl vm) vf vg Empty) s t
      (Branch B va vb vc vd);
balance (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
  (Branch B va vb vc vd) =
  Branch B (Branch v (Branch B vj vk vl vm) vf vg (Branch B vi vn vo vp)) s t
    (Branch B va vb vc vd);

rbt_ins ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> a -> b -> Rbta a b -> Rbta a b;
rbt_ins f k v Empty = Branch R Empty k v Empty;
rbt_ins f k v (Branch B l x y r) =
  (if less k x then balance (rbt_ins f k v l) x y r
    else (if less x k then balance l x y (rbt_ins f k v r)
           else Branch B l x (f k y v) r));
rbt_ins f k v (Branch R l x y r) =
  (if less k x then Branch R (rbt_ins f k v l) x y r
    else (if less x k then Branch R l x y (rbt_ins f k v r)
           else Branch R l x (f k y v) r));

paint :: forall a b. Color -> Rbta a b -> Rbta a b;
paint c Empty = Empty;
paint c (Branch uu l k v r) = Branch c l k v r;

rbt_insert_with_key ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> a -> b -> Rbta a b -> Rbta a b;
rbt_insert_with_key f k v t = paint B (rbt_ins f k v t);

rbt_insert :: forall a b. (Ord a) => a -> b -> Rbta a b -> Rbta a b;
rbt_insert = rbt_insert_with_key (\ _ _ nv -> nv);

insert :: forall a b. (Linorder a) => a -> b -> Rbt a b -> Rbt a b;
insert xc xd xe = RBT (rbt_insert xc xd (impl_of xe));

balance_right :: forall a b. Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
balance_right a k x (Branch R b s y c) = Branch R a k x (Branch B b s y c);
balance_right (Branch B a k x b) s y Empty =
  balance (Branch R a k x b) s y Empty;
balance_right (Branch B a k x b) s y (Branch B va vb vc vd) =
  balance (Branch R a k x b) s y (Branch B va vb vc vd);
balance_right (Branch R a k x (Branch B b s y c)) t z Empty =
  Branch R (balance (paint R a) k x b) s y (Branch B c t z Empty);
balance_right (Branch R a k x (Branch B b s y c)) t z (Branch B va vb vc vd) =
  Branch R (balance (paint R a) k x b) s y
    (Branch B c t z (Branch B va vb vc vd));
balance_right Empty k x Empty = Empty;
balance_right (Branch R va vb vc Empty) k x Empty = Empty;
balance_right (Branch R va vb vc (Branch R ve vf vg vh)) k x Empty = Empty;
balance_right Empty k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg Empty) k x (Branch B va vb vc vd) = Empty;
balance_right (Branch R ve vf vg (Branch R vi vj vk vl)) k x
  (Branch B va vb vc vd) = Empty;

balance_left :: forall a b. Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
balance_left (Branch R a k x b) s y c = Branch R (Branch B a k x b) s y c;
balance_left Empty k x (Branch B a s y b) =
  balance Empty k x (Branch R a s y b);
balance_left (Branch B va vb vc vd) k x (Branch B a s y b) =
  balance (Branch B va vb vc vd) k x (Branch R a s y b);
balance_left Empty k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B Empty k x a) s y (balance b t z (paint R c));
balance_left (Branch B va vb vc vd) k x (Branch R (Branch B a s y b) t z c) =
  Branch R (Branch B (Branch B va vb vc vd) k x a) s y
    (balance b t z (paint R c));
balance_left Empty k x Empty = Empty;
balance_left Empty k x (Branch R Empty vb vc vd) = Empty;
balance_left Empty k x (Branch R (Branch R ve vf vg vh) vb vc vd) = Empty;
balance_left (Branch B va vb vc vd) k x Empty = Empty;
balance_left (Branch B va vb vc vd) k x (Branch R Empty vf vg vh) = Empty;
balance_left (Branch B va vb vc vd) k x
  (Branch R (Branch R vi vj vk vl) vf vg vh) = Empty;

combine :: forall a b. Rbta a b -> Rbta a b -> Rbta a b;
combine Empty x = x;
combine (Branch v va vb vc vd) Empty = Branch v va vb vc vd;
combine (Branch R a k x b) (Branch R c s y d) =
  (case combine b c of {
    Empty -> Branch R a k x (Branch R Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch R a k x b2) t z (Branch R c2 s y d);
    Branch B b2 t z c2 -> Branch R a k x (Branch R (Branch B b2 t z c2) s y d);
  });
combine (Branch B a k x b) (Branch B c s y d) =
  (case combine b c of {
    Empty -> balance_left a k x (Branch B Empty s y d);
    Branch R b2 t z c2 -> Branch R (Branch B a k x b2) t z (Branch B c2 s y d);
    Branch B b2 t z c2 ->
      balance_left a k x (Branch B (Branch B b2 t z c2) s y d);
  });
combine (Branch B va vb vc vd) (Branch R b k x c) =
  Branch R (combine (Branch B va vb vc vd) b) k x c;
combine (Branch R a k x b) (Branch B va vb vc vd) =
  Branch R a k x (combine b (Branch B va vb vc vd));

rbt_del :: forall a b. (Ord a) => a -> Rbta a b -> Rbta a b;
rbt_del x Empty = Empty;
rbt_del x (Branch c a y s b) =
  (if less x y then rbt_del_from_left x a y s b
    else (if less y x then rbt_del_from_right x a y s b else combine a b));

rbt_del_from_left ::
  forall a b. (Ord a) => a -> Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
rbt_del_from_left x (Branch B lt z v rt) y s b =
  balance_left (rbt_del x (Branch B lt z v rt)) y s b;
rbt_del_from_left x Empty y s b = Branch R (rbt_del x Empty) y s b;
rbt_del_from_left x (Branch R va vb vc vd) y s b =
  Branch R (rbt_del x (Branch R va vb vc vd)) y s b;

rbt_del_from_right ::
  forall a b. (Ord a) => a -> Rbta a b -> a -> b -> Rbta a b -> Rbta a b;
rbt_del_from_right x a y s (Branch B lt z v rt) =
  balance_right a y s (rbt_del x (Branch B lt z v rt));
rbt_del_from_right x a y s Empty = Branch R a y s (rbt_del x Empty);
rbt_del_from_right x a y s (Branch R va vb vc vd) =
  Branch R a y s (rbt_del x (Branch R va vb vc vd));

rbt_delete :: forall a b. (Ord a) => a -> Rbta a b -> Rbta a b;
rbt_delete k t = paint B (rbt_del k t);

delete :: forall a b. (Linorder a) => a -> Rbt a b -> Rbt a b;
delete xb xc = RBT (rbt_delete xb (impl_of xc));

inserta :: forall a. (Linorder a) => a -> Set a -> Set a;
inserta x (Coset t) = Coset (delete x t);
inserta x (Set t) = Set (insert x () t);

set :: forall a. (Linorder a) => [a] -> Set a;
set (x21 : x22) = inserta x21 (set x22);
set [] = bot_set;

nodes :: forall a b. (Eq a, Linorder a) => FSM_ext a b -> Set a;
nodes m = set (nodes_from_distinct_paths m);

size :: forall a b. (Eq a, Linorder a) => FSM_ext a b -> Nat;
size m = card (nodes m);

ball :: forall a. (Linorder a) => Set a -> (a -> Bool) -> Bool;
ball (Set t) p = foldi (\ s -> s == True) (\ k _ s -> s && p k) t True;

find :: forall a. (a -> Bool) -> [a] -> Maybe a;
find uu [] = Nothing;
find p (x : xs) = (if p x then Just x else find p xs);

take :: forall a. Nat -> [a] -> [a];
take n [] = [];
take n (x : xs) = (case n of {
                    Zero_nat -> [];
                    Suc m -> x : take m xs;
                  });

sunion_with ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> [(a, b)] -> [(a, b)] -> [(a, b)];
sunion_with f ((ka, va) : asa) ((k, v) : bs) =
  (if less k ka then (k, v) : sunion_with f ((ka, va) : asa) bs
    else (if less ka k then (ka, va) : sunion_with f asa ((k, v) : bs)
           else (ka, f ka va v) : sunion_with f asa bs));
sunion_with f [] bs = bs;
sunion_with f asa [] = asa;

skip_red :: forall a b. Rbta a b -> Rbta a b;
skip_red (Branch R l k v r) = l;
skip_red Empty = Empty;
skip_red (Branch B va vb vc vd) = Branch B va vb vc vd;

skip_black :: forall a b. Rbta a b -> Rbta a b;
skip_black t = let {
                 ta = skip_red t;
               } in (case ta of {
                      Empty -> ta;
                      Branch R _ _ _ _ -> ta;
                      Branch B l _ _ _ -> l;
                    });

compare_height ::
  forall a b. Rbta a b -> Rbta a b -> Rbta a b -> Rbta a b -> Compare;
compare_height sx s t tx =
  (case (skip_red sx, (skip_red s, (skip_red t, skip_red tx))) of {
    (Empty, (Empty, (_, Empty))) -> EQ;
    (Empty, (Empty, (_, Branch _ _ _ _ _))) -> LT;
    (Empty, (Branch _ _ _ _ _, (Empty, _))) -> EQ;
    (Empty, (Branch _ _ _ _ _, (Branch _ _ _ _ _, Empty))) -> EQ;
    (Empty, (Branch _ sa _ _ _, (Branch _ ta _ _ _, Branch _ txa _ _ _))) ->
      compare_height Empty sa ta (skip_black txa);
    (Branch _ _ _ _ _, (Empty, (Empty, Empty))) -> GT;
    (Branch _ _ _ _ _, (Empty, (Empty, Branch _ _ _ _ _))) -> LT;
    (Branch _ _ _ _ _, (Empty, (Branch _ _ _ _ _, Empty))) -> EQ;
    (Branch _ _ _ _ _, (Empty, (Branch _ _ _ _ _, Branch _ _ _ _ _))) -> LT;
    (Branch _ _ _ _ _, (Branch _ _ _ _ _, (Empty, _))) -> GT;
    (Branch _ sxa _ _ _, (Branch _ sa _ _ _, (Branch _ ta _ _ _, Empty))) ->
      compare_height (skip_black sxa) sa ta Empty;
    (Branch _ sxa _ _ _,
      (Branch _ sa _ _ _, (Branch _ ta _ _ _, Branch _ txa _ _ _)))
      -> compare_height (skip_black sxa) sa ta (skip_black txa);
  });

apfst :: forall a b c. (a -> b) -> (a, c) -> (b, c);
apfst f (x, y) = (f x, y);

minus_nat :: Nat -> Nat -> Nat;
minus_nat (Suc m) (Suc n) = minus_nat m n;
minus_nat Zero_nat n = Zero_nat;
minus_nat m Zero_nat = m;

less_nat :: Nat -> Nat -> Bool;
less_nat m (Suc n) = less_eq_nat m n;
less_nat n Zero_nat = False;

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat (Suc m) n = less_nat m n;
less_eq_nat Zero_nat n = True;

divmod_nat :: Nat -> Nat -> (Nat, Nat);
divmod_nat m n =
  (if equal_nat n Zero_nat || less_nat m n then (Zero_nat, m)
    else let {
           a = divmod_nat (minus_nat m n) n;
         } in (case a of {
                (q, aa) -> (Suc q, aa);
              }));

nat_of_num :: Num -> Nat;
nat_of_num (Bit1 n) = let {
                        m = nat_of_num n;
                      } in Suc (plus_nat m m);
nat_of_num (Bit0 n) = let {
                        m = nat_of_num n;
                      } in plus_nat m m;
nat_of_num One = one_nat;

rbtreeify_g :: forall a b. Nat -> [(a, b)] -> (Rbta a b, [(a, b)]);
rbtreeify_g n kvs =
  (if equal_nat n Zero_nat || equal_nat n one_nat then (Empty, kvs)
    else (case divmod_nat n (nat_of_num (Bit0 One)) of {
           (na, r) ->
             (if equal_nat r Zero_nat
               then (case rbtreeify_g na kvs of {
                      (t1, (k, v) : kvsa) ->
                        apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                    })
               else (case rbtreeify_f na kvs of {
                      (t1, (k, v) : kvsa) ->
                        apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                    }));
         }));

rbtreeify_f :: forall a b. Nat -> [(a, b)] -> (Rbta a b, [(a, b)]);
rbtreeify_f n kvs =
  (if equal_nat n Zero_nat then (Empty, kvs)
    else (if equal_nat n one_nat
           then (case kvs of {
                  (k, v) : kvsa -> (Branch R Empty k v Empty, kvsa);
                })
           else (case divmod_nat n (nat_of_num (Bit0 One)) of {
                  (na, r) ->
                    (if equal_nat r Zero_nat
                      then (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               apfst (Branch B t1 k v) (rbtreeify_g na kvsa);
                           })
                      else (case rbtreeify_f na kvs of {
                             (t1, (k, v) : kvsa) ->
                               apfst (Branch B t1 k v) (rbtreeify_f na kvsa);
                           }));
                })));

rbtreeify :: forall a b. [(a, b)] -> Rbta a b;
rbtreeify kvs = fst (rbtreeify_g (Suc (size_list kvs)) kvs);

gen_entries :: forall a b. [((a, b), Rbta a b)] -> Rbta a b -> [(a, b)];
gen_entries kvts (Branch c l k v r) = gen_entries (((k, v), r) : kvts) l;
gen_entries ((kv, t) : kvts) Empty = kv : gen_entries kvts t;
gen_entries [] Empty = [];

entries :: forall a b. Rbta a b -> [(a, b)];
entries = gen_entries [];

rbt_union_with_key ::
  forall a b. (Ord a) => (a -> b -> b -> b) -> Rbta a b -> Rbta a b -> Rbta a b;
rbt_union_with_key f t1 t2 =
  (case compare_height t1 t1 t2 t2 of {
    LT -> folda (rbt_insert_with_key (\ k v w -> f k w v)) t1 t2;
    GT -> folda (rbt_insert_with_key f) t2 t1;
    EQ -> rbtreeify (sunion_with f (entries t1) (entries t2));
  });

rbt_union :: forall a b. (Ord a) => Rbta a b -> Rbta a b -> Rbta a b;
rbt_union = rbt_union_with_key (\ _ _ rv -> rv);

union :: forall a b. (Linorder a) => Rbt a b -> Rbt a b -> Rbt a b;
union xb xc = RBT (rbt_union (impl_of xb) (impl_of xc));

rbt_lookup :: forall a b. (Ord a) => Rbta a b -> a -> Maybe b;
rbt_lookup Empty k = Nothing;
rbt_lookup (Branch uu l x y r) k =
  (if less k x then rbt_lookup l k
    else (if less x k then rbt_lookup r k else Just y));

lookup :: forall a b. (Linorder a) => Rbt a b -> a -> Maybe b;
lookup x = rbt_lookup (impl_of x);

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

member :: forall a. (Linorder a) => a -> Set a -> Bool;
member x (Coset t) = is_none (lookup t x);
member x (Set t) = lookup t x == Just ();

remove :: forall a. (Linorder a) => a -> Set a -> Set a;
remove x (Coset t) = Coset (insert x () t);
remove x (Set t) = Set (delete x t);

more :: forall a b. FSM_ext a b -> b;
more (FSM_ext initial inputs outputs transitions more) = more;

from_FSM :: forall a b. FSM_ext a b -> a -> FSM_ext a b;
from_FSM m q = FSM_ext q (inputs m) (outputs m) (transitions m) (more m);

butlast :: forall a. [a] -> [a];
butlast [] = [];
butlast (x : xs) = (if null xs then [] else x : butlast xs);

pow_list :: forall a. [a] -> [[a]];
pow_list [] = [[]];
pow_list (x : xs) = let {
                      pxs = pow_list xs;
                    } in pxs ++ map (\ a -> x : a) pxs;

prefixes :: forall a. [a] -> [[a]];
prefixes [] = [[]];
prefixes (v : va) = prefixes (butlast (v : va)) ++ [v : va];

find_index :: forall a. (a -> Bool) -> [a] -> Maybe Nat;
find_index f [] = Nothing;
find_index f (x : xs) =
  (if f x then Just Zero_nat else (case find_index f xs of {
                                    Nothing -> Nothing;
                                    Just k -> Just (Suc k);
                                  }));

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

wf_transitions ::
  forall a b.
    (Eq a, Linorder a) => FSM_ext a b -> [(a, (Integer, (Integer, a)))];
wf_transitions m =
  filter
    (\ t ->
      member (fst t) (nodes m) &&
        membera (inputs m) (fst (snd t)) &&
          membera (outputs m) (fst (snd (snd t))))
    (transitions m);

deadlock_state :: forall a b. (Eq a, Linorder a) => FSM_ext a b -> a -> Bool;
deadlock_state m q = not (any (\ t -> fst t == q) (wf_transitions m));

rbt_filter :: forall a b. (Linorder a) => (a -> Bool) -> Rbt a b -> Set a;
rbt_filter p t = fold (\ k _ a -> (if p k then inserta k a else a)) t bot_set;

cartesian_product_list :: forall a b. [a] -> [b] -> [(a, b)];
cartesian_product_list xs ys = concatMap (\ x -> map (\ a -> (x, a)) ys) xs;

product_transitions ::
  forall a b c d.
    (Eq a, Linorder a, Eq c,
      Linorder c) => FSM_ext a b ->
                       FSM_ext c d -> [((a, c), (Integer, (Integer, (a, c))))];
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
  forall a b c d.
    (Eq a, Linorder a, Eq c,
      Linorder c) => FSM_ext a b -> FSM_ext c d -> FSM_ext (a, c) b;
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

inf_set :: forall a. (Linorder a) => Set a -> Set a -> Set a;
inf_set (Coset t1) (Coset t2) = Coset (union t1 t2);
inf_set a (Coset t) = fold (\ k _ -> remove k) t a;
inf_set a (Set t) = rbt_filter (\ k -> member k a) t;

uminus_set :: forall a. (Linorder a) => Set a -> Set a;
uminus_set (Coset xs) = Set xs;
uminus_set (Set xs) = Coset xs;

sup_set :: forall a. (Linorder a) => Set a -> Set a -> Set a;
sup_set (Set t1) (Set t2) = Set (union t1 t2);
sup_set (Coset t) a = uminus_set (rbt_filter (\ k -> not (member k a)) t);
sup_set (Set t) a = fold (\ k _ -> inserta k) t a;

d_states ::
  forall a.
    (Eq a,
      Linorder a) => [(a, Integer)] ->
                       Set (a, (Integer, (Integer, a))) ->
                         Nat -> a -> [(a, Integer)];
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

less_eq_set :: forall a. (Linorder a) => Set a -> Set a -> Bool;
less_eq_set (Coset t1) (Set t2) =
  (case (impl_of t1, impl_of t2) of {
    (Empty, Empty) -> False;
    (Empty, Branch _ _ _ _ _) ->
      (error :: forall a. String -> (() -> a) -> a) "non_empty_trees"
        (\ _ -> less_eq_set (Coset t1) (Set t2));
    (Branch _ _ _ _ _, _) ->
      (error :: forall a. String -> (() -> a) -> a) "non_empty_trees"
        (\ _ -> less_eq_set (Coset t1) (Set t2));
  });
less_eq_set a (Coset t) = ball (Set t) (\ y -> not (member y a));
less_eq_set (Set t) b = ball (Set t) (\ x -> member x b);

less_set :: forall a. (Linorder a) => Set a -> Set a -> Bool;
less_set a b = less_eq_set a b && not (less_eq_set b a);

s_states ::
  forall a.
    (Eq a,
      Linorder a) => [(a, Integer)] ->
                       Set (a, (Integer, (Integer, a))) ->
                         Nat -> [(a, Integer)];
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

list_as_fun :: forall a b. (Eq a) => [(a, b)] -> b -> a -> b;
list_as_fun xs defaultValue = (\ x -> (case find (\ (a, _) -> a == x) xs of {
Nothing -> defaultValue;
Just (_, b) -> b;
                                      }));

d_states_opt ::
  forall a b. (Eq a, Linorder a) => FSM_ext a b -> Nat -> a -> [(a, Integer)];
d_states_opt m k q =
  d_states
    (concatMap (\ qa -> map (\ a -> (qa, a)) (inputs m))
      (nodes_from_distinct_paths m))
    (set (wf_transitions m)) k q;

prefix_pairs :: forall a. [a] -> [([a], [a])];
prefix_pairs [] = [];
prefix_pairs (v : va) =
  prefix_pairs (butlast (v : va)) ++
    map (\ ys -> (ys, v : va)) (butlast (prefixes (v : va)));

times_nat :: Nat -> Nat -> Nat;
times_nat Zero_nat n = Zero_nat;
times_nat (Suc m) n = plus_nat n (times_nat m n);

s_states_opt ::
  forall a b. (Eq a, Linorder a) => FSM_ext a b -> Nat -> [(a, Integer)];
s_states_opt c k =
  s_states
    (concatMap (\ q -> map (\ a -> (q, a)) (inputs c))
      (nodes_from_distinct_paths c))
    (set (wf_transitions c)) k;

prefix_pair_testsa ::
  forall a b c.
    (Eq a,
      Linorder a) => a -> (a -> a -> FSM_ext b c) ->
                            ([(a, (Integer, (Integer, a)))], (Set a, Set a)) ->
                              [[(a, ([(a, (Integer, (Integer, a)))],
                                      FSM_ext b c))]];
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
  forall a b c.
    (Eq a,
      Linorder a) => a -> (a -> a -> FSM_ext b c) ->
                            [([(a, (Integer, (Integer, a)))],
                               (Set a, Set a))] ->
                              [(a, ([(a, (Integer, (Integer, a)))],
                                     FSM_ext b c))];
prefix_pair_tests q fRD pds = concat (concatMap (prefix_pair_testsa q fRD) pds);

preamble_pair_tests ::
  forall a b c d.
    (Eq a) => [(a, FSM_ext a b)] ->
                [((a, a), FSM_ext c d)] ->
                  [(a, ([(a, (Integer, (Integer, a)))], FSM_ext c d))];
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

preamble_prefix_tests ::
  forall a b c d.
    (Eq a,
      Linorder a) => a -> (a -> a -> FSM_ext b c) ->
                            [([(a, (Integer, (Integer, a)))],
                               (Set a, Set a))] ->
                              [(a, FSM_ext a d)] ->
                                [(a, ([(a, (Integer, (Integer, a)))],
                                       FSM_ext b c))];
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

choose_state_separator_deadlock_input ::
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b -> FSM_ext (a, a) b -> (a, a) -> Maybe Integer;
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
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       a -> a -> [(Sum (a, a) a,
                                    (Integer, (Integer, Sum (a, a) a)))];
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
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       a -> a -> [(Sum (a, a) a,
                                    (Integer, (Integer, Sum (a, a) a)))];
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
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       FSM_ext (a, a) b -> FSM_ext (Sum (a, a) a) b;
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
                          (sup_set (sup_set (set t_old) (set t_left))
                            (set t_right))) &&
                      any (\ ta ->
                            equal_sum (fst t) (fst ta) &&
                              fst (snd t) == fst (snd ta))
                        t_old)
                  (distinguishing_transitions_left m (fst (initial s))
                    (snd (initial s))) ++
                  filter
                    (\ t ->
                      not (member t
                            (sup_set (sup_set (set t_old) (set t_left))
                              (set t_right))) &&
                        any (\ ta ->
                              equal_sum (fst t) (fst ta) &&
                                fst (snd t) == fst (snd ta))
                          t_old)
                    (distinguishing_transitions_right m (fst (initial s))
                      (snd (initial s))))
    (more m);

calculate_state_separator_from_s_states ::
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b -> a -> a -> Maybe (FSM_ext (Sum (a, a) a) b);
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
  forall a b.
    (Eq a, Linorder a) => FSM_ext a b -> [((a, a), FSM_ext (Sum (a, a) a) b)];
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
  forall a b. (Eq a, Linorder a) => FSM_ext a b -> a -> Maybe (FSM_ext a b);
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
  forall a b. (Eq a, Linorder a) => FSM_ext a b -> [(a, FSM_ext a b)];
d_reachable_states_with_preambles m =
  map_filter
    (\ x ->
      (if not (is_none (snd x)) then Just (fst x, the (snd x)) else Nothing))
    (map (\ q -> (q, calculate_state_preamble_from_d_states m q))
      (nodes_from_distinct_paths m));

paths_up_to_length_or_condition_with_witness ::
  forall a b c.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       a -> Nat ->
                              ([(a, (Integer, (Integer, a)))] -> Maybe c) ->
                                [(a, (Integer, (Integer, a)))] ->
                                  [([(a, (Integer, (Integer, a)))], c)];
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
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       a -> [(Set a, Set a)] ->
                              Nat ->
                                Nat ->
                                  [([(a, (Integer, (Integer, a)))],
                                     (Set a, Set a))];
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
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       a -> [(Set a, Set a)] ->
                              Nat ->
                                [([(a, (Integer, (Integer, a)))],
                                   (Set a, Set a))];
m_traversal_paths_with_witness ma q d m =
  m_traversal_paths_with_witness_up_to_length ma q d m
    (Suc (times_nat (size ma) m));

calculate_test_suite_rbt ::
  forall a b.
    (Eq a,
      Linorder a) => FSM_ext a b ->
                       Nat ->
                         ([(a, ([(a, (Integer, (Integer, a)))],
                                 FSM_ext (Sum (a, a) a) b))],
                           [(a, FSM_ext a b)]);
calculate_test_suite_rbt ma m =
  let {
    rdssl = r_distinguishable_state_pairs_with_separators_naive ma;
    rds = set (map fst rdssl);
    rdp = filter
            (\ s ->
              ball s
                (\ q1 ->
                  ball s
                    (\ q2 ->
                      (if not (q1 == q2) then member (q1, q2) rds else True))))
            (map set (pow_list (nodes_from_distinct_paths ma)));
    mprd = filter (\ s -> not (any (less_set s) rdp)) rdp;
    drsp = d_reachable_states_with_preambles ma;
    drs = map fst drsp;
    mrs = map (\ s -> (s, inf_set s (set drs))) mprd;
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

}
