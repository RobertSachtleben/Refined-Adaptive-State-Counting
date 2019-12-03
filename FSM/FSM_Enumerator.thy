theory FSM_Enumerator
imports State_Separator (* TODO *)
begin


(* TODO: move *)
(* TODO: just add left ... *)
(*
fun find_last_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_last_index f xs = (case find_index f (rev xs) of 
    None \<Rightarrow> None |
    Some i \<Rightarrow> Some (length xs - Suc i))"

value "find_index ((=) True) [False,True,True,False,True]"
value "find_last_index ((=) True) [False,True,True,False,True]"

lemma find_last_index_index :
  assumes "find_last_index f xs = Some k"
  shows "k < length xs" and "f (xs ! k)" and "\<And> j . j > k \<Longrightarrow> k < length xs \<Longrightarrow> \<not> f (xs ! j)"
*)

fun next_boolean_list :: "bool list \<Rightarrow> (bool list) option" where
  "next_boolean_list [] = None" |
  "next_boolean_list (False#[]) = None" |
  "next_boolean_list (False#ts) = (case next_boolean_list ts of None \<Rightarrow> None | Some ts' \<Rightarrow> Some (True # ts'))" |
  "next_boolean_list (True#ts) = Some (False # ts)"

value "next_boolean_list [True ,True ,True ]"
value "next_boolean_list [False,True ,True ]"
value "next_boolean_list [True ,False,True ]"
value "next_boolean_list [False,False,True ]"
value "next_boolean_list [True ,True ,False]"
value "next_boolean_list [False,True ,False]"
value "next_boolean_list [True ,False,False]"
value "next_boolean_list [False,False,False]"



fun bool_list_less :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where 
  "bool_list_less [] bs2 = True" |
  "bool_list_less bs1 [] = False" |
  "bool_list_less (b1#bs1) (b2#bs2) = ((\<not>b1 \<and> b2) \<or> ((b1 = b2) \<and> (bs1 \<noteq> bs2) \<and> bool_list_less bs1 bs2))"

abbreviation(input) "bool_lists k \<equiv> {bs :: bool list . length bs = k}"




lemma next_boolean_list_length :
  assumes "next_boolean_list bs = Some bs'"
shows "length bs' = length bs"
using assms proof (induction bs arbitrary: bs')
  case Nil
  then show ?case by auto
next
  case (Cons b bs)
  then show ?case proof (cases "length bs > 0")
    case True
    then show ?thesis proof (cases b)
      case True
      then show ?thesis using \<open>0 < length bs\<close> 
        using Cons.prems by auto
    next
      case False
      then have "b = False" by auto
      then have "next_boolean_list (False # bs) = Some bs'" using Cons.prems by auto
      then obtain bs'' where "next_boolean_list bs = Some bs''"
      proof -
        assume "\<And>bs''. next_boolean_list bs = Some bs'' \<Longrightarrow> thesis"
        then show ?thesis
          by (metis (no_types) True \<open>next_boolean_list (False # bs) = Some bs'\<close> length_0_conv neq_Nil_conv next_boolean_list.simps(3) not_None_eq not_less0 option.simps(4))
      qed
      then have "next_boolean_list (False # bs) = Some (True # bs'')"
        using \<open>next_boolean_list (False # bs) = Some bs'\<close> 
        using next_boolean_list.elims by force
      
      then show ?thesis using Cons.IH[OF \<open>next_boolean_list bs = Some bs''\<close>] 
        using \<open>next_boolean_list (False # bs) = Some bs'\<close> by auto
    qed
  next
    case False
    then show ?thesis 
      using Cons 
      by (metis (full_types) length_Cons length_greater_0_conv next_boolean_list.simps(2) next_boolean_list.simps(4) not_None_eq option.sel)
  qed
qed


fun enumerate_transitions :: "'a list \<Rightarrow> Input list \<Rightarrow> Output list \<Rightarrow> 'a Transition list" where
  "enumerate_transitions qs xs ys = cartesian_product_list qs
                                      (cartesian_product_list xs
                                        (cartesian_product_list ys qs))"

fun find_FSM' :: "('a FSM \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> Input list \<Rightarrow> Output list \<Rightarrow> 'a Transition list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'a FSM option" where
  "find_FSM' f q xs ys ts bs 0 = None" |
  "find_FSM' f q xs ys ts bs (Suc k) = (let M = \<lparr> initial = q, inputs = xs, outputs = ys, transitions = map fst (filter snd (zip ts bs)) \<rparr> in
    if f M then Some M 
    else (case next_boolean_list bs of
      Some bs' \<Rightarrow> find_FSM' f q xs ys ts bs' k |
      None \<Rightarrow> None))"

fun find_FSM :: "('a FSM \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> Input list \<Rightarrow> Output list \<Rightarrow> 'a FSM option" where
  "find_FSM f q qs xs ys = (let ts = enumerate_transitions qs xs ys 
                            in find_FSM' f q xs ys ts (replicate (length ts) True) (power 2 (length ts)))"





(*

lemma next_boolean_list_diff :
  assumes "length bs > 0"
  and     "next_boolean_list bs = Some bs'"
shows "bool_list_less bs bs' \<and> \<not> (\<exists> bs'' . bool_list_less bs bs'' \<and> bool_list_less bs'' bs')"
using next_boolean_list_length[OF assms(2)] assms(1) proof (induction bs' bs rule: list_induct2) 
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)
  
qed
using assms proof (induction bs)
case Nil
  then show ?case by auto
next
  case (Cons b bs)
  then show ?case proof (cases "length bs > 0")
    case True
    then show ?thesis using Cons 
  next
    case False
    then show ?thesis sorry
  qed
qed 





fun find_boolean_list :: "(bool list \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> (bool list) option"


lemma next_boolean_list_find :
  assumes "\<exists> bs . length bs = k \<and> P bs"
  shows "

fun next_selector_list :: "bool list \<Rightarrow> (bool list) option" where
  "next_selector_list = 










(* TODO: move *)
fun generate_sublists :: "'a list \<Rightarrow> 'a list list" where
  "generate_sublists [] = [[]]" |
  "generate_sublists (x#xs) = (let sl = generate_sublists xs in sl @ (map ((#) x) sl))"

value "generate_sublists [0::nat,1,2,3]"

lemma set_map_insert :
  "image set (set (map ((#) x) xs)) = image (insert x) (image set (set xs))"
by (induction xs; auto)

lemma generate_sublists_powerset :
  "image set (set (generate_sublists xs)) = Pow (set xs)"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  have "image set (set (map ((#) x) (generate_sublists xs))) = (image (insert x) (Pow (set xs)))"
    using Cons set_map_insert[of x "generate_sublists xs"]
    by simp 

  then have "image set (set (generate_sublists xs @ map ((#) x) (generate_sublists xs))) = Pow (set xs) \<union> (image (insert x) (Pow (set xs)))"
    using Cons
    by (simp add: image_Un) 
  moreover have "Pow (set (x # xs)) = Pow (set xs) \<union> (image (insert x) (Pow (set xs)))"
    by (simp add: Pow_insert) 
  ultimately show ?case unfolding generate_sublists.simps Let_def 
    by auto 
qed



fun enumerate_transitions :: "'a list \<Rightarrow> Input list \<Rightarrow> Output list \<Rightarrow> 'a Transition list" where
  "enumerate_transitions qs xs ys = cartesian_product_list qs
                                      (cartesian_product_list xs
                                        (cartesian_product_list ys qs))"

value "enumerate_transitions [0::nat,1,2,3] [0,1] [0,1,2]"

(* TODO: add variant that also uses sublists for inputs and outputs? *) 
fun enumerate_FSMs :: "'a \<Rightarrow> 'a list \<Rightarrow> Input list \<Rightarrow> Output list \<Rightarrow> 'a FSM list" where
  "enumerate_FSMs q qs xs ys = map (\<lambda> ts . \<lparr> initial = q, inputs = xs, outputs = ys, transitions = ts  \<rparr>) (generate_sublists (enumerate_transitions qs xs ys))"

value "enumerate_FSMs (0::nat) [0,1] [0] [0,1]"

value "filter observable (enumerate_FSMs (0::nat) [0,1] [0] [0,1])" 
*)

end