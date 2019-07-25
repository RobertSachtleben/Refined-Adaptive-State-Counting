theory FSM3
imports Main
begin

(*type_synonym State = nat*)
type_synonym Input = integer
type_synonym Output = integer
(*type_synonym Transition = "(nat \<times> nat \<times> nat \<times> nat)"*)
type_synonym 'state Transition = "('state \<times> Input \<times> Output \<times> 'state)"

record 'state FSM = 
  initial :: 'state 
  inputs  :: "Input list"
  outputs  :: "Output list"  
  transitions :: "('state Transition) list" 

abbreviation "t_source (a :: 'state Transition) \<equiv> fst a" 
abbreviation "t_input  (a :: 'state Transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: 'state Transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: 'state Transition) \<equiv> snd (snd (snd a))"

abbreviation "p_io (p :: 'state Transition list) \<equiv> map (\<lambda> t . (t_input t, t_output t)) p"

value "t_source (1,2,3,4::nat)"
value "t_input  (1,2,3,4::nat)"
value "t_output (1,2,3,4::nat)"
value "t_target (1,2,3,4::nat)"



fun is_wf_transition :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition \<Rightarrow> bool" where
  "is_wf_transition M t = ((t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun wf_transitions :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition list" where
  "wf_transitions M = filter (is_wf_transition M) (transitions M)"

abbreviation "h M \<equiv> set (wf_transitions M)"



fun pairwise_immediately_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_immediately_reachable M =  image (\<lambda> t. (t_source t, t_target t)) (h M)"

lemma wf_transrel_transition_ob : 
  assumes "(q,q') \<in> pairwise_immediately_reachable M"
  obtains t
  where "t \<in> h M"
    and "t_source t = q"
    and "t_target t = q'"
    and "is_wf_transition M t"
  using assms by auto

fun pairwise_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_reachable M = trancl (pairwise_immediately_reachable M)"

fun reachable :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
  "reachable M q q' = (q = q' \<or> (q, q') \<in> pairwise_reachable M)"

fun initially_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> bool" where
  "initially_reachable M q = reachable M (initial M) q"

fun nodes' :: "('state, 'b) FSM_scheme \<Rightarrow> 'state set" where
  "nodes' M = insert (initial M) (set (filter (initially_reachable M) (map t_target (wf_transitions M))))"



lemma reachable_next :
  assumes "reachable M q (t_source t)"
  and     "t \<in> h M"
shows "reachable M q (t_target t)"
proof -
  have "q = t_source t \<or> (q, t_source t) \<in> pairwise_reachable M"
    using assms(1) by auto
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately show ?thesis 
  proof (cases "q = t_source t")
    case True
    then show ?thesis
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> by auto       
  next
    case False
    then have "(q, t_source t) \<in> pairwise_reachable M" 
      using \<open>q = t_source t \<or> (q, t_source t) \<in> pairwise_reachable M\<close> by auto
    then have "(q, t_target t) \<in> pairwise_reachable M" 
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> by auto
    then show ?thesis 
      by auto
  qed
qed

lemma reachable_next' :
  assumes "reachable M (t_target t) q"
  and     "t \<in> h M"
shows "reachable M (t_source t) q"
proof -
  have "t_target t = q \<or> (t_target t, q) \<in> pairwise_reachable M"
    using assms(1) by auto
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately show ?thesis 
  proof (cases "q = t_target t")
    case True
    then show ?thesis
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> by auto       
  next
    case False
    then have "(t_target t, q) \<in> pairwise_reachable M" 
      using \<open>t_target t = q \<or> (t_target t, q) \<in> pairwise_reachable M\<close> by auto
    then have "(t_source t, q) \<in> pairwise_reachable M" 
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> by auto
    then show ?thesis 
      by auto
  qed
qed


lemma nodes'_next :
  assumes "t_source t \<in> nodes' M"
  and     "t \<in> h M"
shows "t_target t \<in> nodes' M"
proof (cases "t_source t = initial M")
  case True
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately have "(initial M, t_target t) \<in> pairwise_reachable M"
    by auto
  then show ?thesis 
    using assms(2) by auto
next
  case False
  then have "(initial M, t_source t) \<in> pairwise_reachable M"
    using assms(1) by auto
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately have "(initial M, t_target t) \<in> pairwise_reachable M"
    by auto
  then show ?thesis 
    using assms(2) by auto
qed




inductive path :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "path M q []" |
  cons[intro!] : "t \<in> h M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"

fun visited_states :: "'state \<Rightarrow> 'state Transition list \<Rightarrow> 'state list" where
  "visited_states q p = (q # map t_target p)"

fun target :: "'state Transition list \<Rightarrow> 'state \<Rightarrow> 'state" where
  "target p q = last (visited_states q p)"

fun path' :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  "path' M q [] = True" |
  "path' M q (t#ts) = (t \<in> h M \<and> q = t_source t \<and> path M (t_target t) ts)"


lemma path_code[code] : "path M q p = path' M q p" 
  by (induction p; auto)


lemma path_h :
  assumes "path M q p"
  shows "set p \<subseteq> h M"
  using assms by (induct p arbitrary: q; fastforce)

(* Example FSM *)
definition "M_ex = (\<lparr> 
                      initial = 2::integer, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (2,1,30,4),
                                      (3,1,10,5),
                                      (4,0,10,3),
                                      (4,2,20,2),
                                      (5,2,30,3)]\<rparr>) "

(* example FSM of Hieron's paper *)
definition "M_ex_H = (\<lparr> 
                      initial = 1::integer, 
                      inputs = [0,1], 
                      outputs = [0,1], 
                      transitions = [ (1,0,0,2),
                                      (1,0,1,4),
                                      (1,1,1,4),
                                      (2,0,0,2),
                                      (2,1,1,4),
                                      (3,0,1,4),
                                      (3,1,0,1),
                                      (3,1,1,3),
                                      (4,0,0,3),
                                      (4,1,0,1)
                                      ]\<rparr>)"

(* example FSM of TA exercise 09 *)
definition "M_ex_9 = (\<lparr> 
                      initial = 0::integer, 
                      inputs = [0,1], 
                      outputs = [0,1,2,3], 
                      transitions = [ 
                                      (0,0,2,2),
                                      (0,0,3,2),
                                      (0,1,0,3),
                                      (0,1,1,3),
                                      (1,0,3,2),
                                      (1,1,1,3),
                                      (2,0,2,2),
                                      (2,1,3,3),
                                      (3,0,2,2),
                                      (3,1,0,2),
                                      (3,1,1,1)
                                      ]\<rparr>)"



definition "M_ex' = (\<lparr> 
                      initial = 1000::int, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (1000,1,20,1003),
                                      (1000,1,30,1003),
                                      (1003,2,10,1005),
                                      (1003,0,10,1004),
                                      (1003,2,20,1002),
                                      (1005,2,30,1004)]\<rparr>)"

value "nodes' M_ex"
value "path M_ex 2 []"
value "path M_ex 3 [(3,1,10,5),(5,2,30,3)]"
value "path M_ex 3 [(3,1,10,5),(5,2,30,4)]"
value "path M_ex 3 [(2,1,20,3)]"
value "path M_ex 2 [(2,1,20,3),(3,1,10,5),(5,2,30,3),(3,1,10,5),(5,2,30,3),(3,1,10,5),(5,2,30,3)]"

fun lists_of_length :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "lists_of_length T 0 = [[]]" |
  "lists_of_length T (Suc n) = concat (map (\<lambda> xs . map (\<lambda> x . x#xs) T ) (lists_of_length T n))" 

lemma lists_of_length_containment :
  assumes "set xs \<subseteq> set T"
  and     "length xs = n"
shows "xs \<in> set (lists_of_length T n)"
using assms proof (induction xs arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then obtain k where "n = Suc k" 
    by auto
  then have "xs \<in> set (lists_of_length T k)" 
    using Cons by auto
  moreover have "a \<in> set T" 
    using Cons by auto
  ultimately show ?case 
    using \<open>n = Suc k\<close> by auto
qed




lemma lists_of_length_length :
  assumes "xs \<in> set (lists_of_length T n)"
  shows "length xs = n"
proof -
  have "\<forall> xs \<in> set (lists_of_length T n) . length xs = n"
    by (induction n; simp)
  then show ?thesis using assms by blast
qed

lemma lists_of_length_elems :
  assumes "xs \<in> set (lists_of_length T n)"
  shows "set xs \<subseteq> set T"
proof -
  have "\<forall> xs \<in> set (lists_of_length T n) . set xs \<subseteq> set T"
    by (induction n; simp)
  then show ?thesis using assms by blast
qed
  
lemma lists_of_length_list_set : "set (lists_of_length xs k) = {xs' . length xs' = k \<and> set xs' \<subseteq> set xs}"
  using lists_of_length_containment[of _ xs k] lists_of_length_length[of _ xs k] lists_of_length_elems[of _ xs k] by blast
    

value "lists_of_length [1,2,3::nat] 3"

fun paths_of_length :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state Transition list list" where
  "paths_of_length M q n = filter (path M q) (lists_of_length (wf_transitions M) n)"

value "paths M_ex 2 5"

lemma paths_of_length_containment : 
  assumes "path M q p"
  shows "p \<in> set (paths_of_length M q (length p))"
proof -
  have "set p \<subseteq> h M"
    by (meson assms path_h) 
  then have "p \<in> set (lists_of_length (wf_transitions M) (length p))"
    by (metis lists_of_length_containment)
  then show ?thesis
    by (simp add: assms) 
qed

lemma paths_of_length_is_path :
  assumes "p \<in> set (paths_of_length M q k)"
  shows "path M q p"
    and "length p = k"
proof -
  show "path M q p"
    using assms by auto
  show "length p = k"
    using assms lists_of_length_length by fastforce
qed

lemma paths_of_length_path_set :
  "set (paths_of_length M q k) = { p . path M q p \<and> length p = k }"
using paths_of_length_is_path[of _ M q k] paths_of_length_containment[of M q] by blast

(* ++++++++ alternative path generation function, equality not yet proven ++++++++ *)
fun extend_path :: "('a, 'b) FSM_scheme \<Rightarrow> 'a Transition list \<Rightarrow> 'a Transition list list" where
  "extend_path M p = map (\<lambda> t . p@[t]) (filter (\<lambda>t . t_source t = target p (initial M)) (wf_transitions M))"

fun paths_up_to_length' :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a Transition list list \<times> 'a Transition list list)" where
  "paths_up_to_length' M q 0 = ([[]],[])" |
  "paths_up_to_length' M q (Suc n) = (case paths_up_to_length' M q n of
    (maxPaths,shorterPaths) \<Rightarrow> ((filter (\<lambda>p . p \<notin> set (shorterPaths@maxPaths)) (concat (map (\<lambda> p . extend_path M p) maxPaths))),shorterPaths@maxPaths))" 

fun paths_up_to_length'' :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "paths_up_to_length'' M q n = (case paths_up_to_length' M q n of (mP,sP) \<Rightarrow> sP@mP)"

value "paths_up_to_length'' M_ex 2 0"
value[code] "paths_up_to_length'' M_ex 2 15"
value[code] "paths_up_to_length'' M_ex_H 2 5"
(* ++++++++++++++++ *)

fun paths_up_to_length :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state Transition list list" where
  "paths_up_to_length M q 0 = [[]]" |
  "paths_up_to_length M q (Suc n) = (paths_up_to_length M q n) @ (paths_of_length M q (Suc n))"

value[code] "paths_up_to_length M_ex 2 8"
value[code] "paths_up_to_length M_ex_H 2 4"

lemma paths_up_to_length_path_set :
  "set (paths_up_to_length M q k) = { p . path M q p \<and> length p \<le> k }"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)

  have "set (paths_up_to_length M q (Suc k)) = set (paths_up_to_length M q k) \<union> set (paths_of_length M q (Suc k))"
    using paths_up_to_length.simps(2) by (metis set_append) 
  
  moreover have "{p. path M q p \<and> length p \<le> Suc k} = {p. path M q p \<and> length p \<le> k} \<union> {p. path M q p \<and> length p = Suc k}"
    by auto

  ultimately show ?case using Suc.IH
    by (metis paths_of_length_path_set) 
qed














fun language_state_for_input :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "language_state_for_input M q xs = map p_io (filter (\<lambda> ts . xs = map t_input ts) (paths_of_length M q (length xs)))"

value "language_state_for_input M_ex 2 [1]"
value "language_state_for_input M_ex 2 [1,2]"
value "language_state_for_input M_ex 3 [1,2,1,2,1,2]"

fun language_state_for_inputs :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list list \<Rightarrow> (Input \<times> Output) list list" where
  "language_state_for_inputs M q xss = concat (map (language_state_for_input M q) xss)" 

value "language_state_for_inputs M_ex 2 [[1]]"
value "language_state_for_inputs M_ex 2 [[1], [1,2]]"
value "language_state_for_inputs M_ex 3 [[1,2,1,2,1,2], [1], [2]]"

lemma concat_map_elem :
  assumes "y \<in> set (concat (map f xs))"
  obtains x where "x \<in> set xs"
              and "y \<in> set (f x)"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
  proof (cases "y \<in> set (f a)")
    case True
    then show ?thesis 
      using Cons.prems(1) by auto
  next
    case False
    then have "y \<in> set (concat (map f xs))"
      using Cons by auto
    have "\<exists> x . x \<in> set xs \<and> y \<in> set (f x)"  
    proof (rule ccontr)
      assume "\<nexists>x. x \<in> set xs \<and> y \<in> set (f x)"
      then have "\<not>(y \<in> set (concat (map f xs)))"
        by auto
      then show False 
        using \<open>y \<in> set (concat (map f xs))\<close> by auto
    qed
    then show ?thesis
      using Cons.prems(1) by auto     
  qed
qed

lemma language_state_for_inputs_from_language_state_for_input :
  assumes "io \<in> set (language_state_for_inputs M q xss)"
  obtains xs 
  where "xs \<in> set xss"
    and "io \<in> set (language_state_for_input M q xs)"
   using concat_map_elem[of io "language_state_for_input M q" xss] assms unfolding language_state_for_inputs.simps by blast



fun LS\<^sub>i\<^sub>n :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list set \<Rightarrow> (Input \<times> Output) list set" where 
  "LS\<^sub>i\<^sub>n M q U = { map (\<lambda> t . (t_input t, t_output t)) p | p . path M q p \<and> map t_input p \<in> U }"

abbreviation "L\<^sub>i\<^sub>n M \<equiv> LS\<^sub>i\<^sub>n M (initial M)"



lemma set_map_subset :
  assumes "x \<in> set xs"
  and     "t \<in> set (map f [x])"
shows "t \<in> set (map f xs)"
  using assms by auto


lemma LS\<^sub>i\<^sub>n_subset_language_state_for_inputs : "LS\<^sub>i\<^sub>n M q (set xss) \<subseteq> set (language_state_for_inputs M q xss)"
proof 
  fix x assume "x \<in> LS\<^sub>i\<^sub>n M q (set xss)"
  then obtain p where "path M q p" 
                and   "map t_input p \<in> (set xss)"
                and   "x = map (\<lambda> t . (t_input t, t_output t)) p"
    by auto
  have "p \<in> set (filter (\<lambda> ts . map t_input p = map t_input ts) (paths_of_length M q (length (map t_input p))))"
    using \<open>path M q p\<close> paths_of_length_containment by fastforce
  then have "map (\<lambda> t . (t_input t, t_output t)) p \<in> set (language_state_for_input M q (map t_input p))"
    by auto
  then obtain tr where  "tr \<in> set (map (language_state_for_input M q) [map t_input p])" 
                 and    "map (\<lambda> t . (t_input t, t_output t)) p \<in> set tr" 
    by auto
  have "tr \<in> set (map (language_state_for_input M q) xss)"
    using set_map_subset[OF \<open>map t_input p \<in> (set xss)\<close>  \<open>tr \<in> set (map (language_state_for_input M q) [map t_input p])\<close>] by auto

  then have "set tr \<subseteq> set (language_state_for_inputs M q xss)"
    by auto
  then have "map (\<lambda> t . (t_input t, t_output t)) p \<in> set (language_state_for_inputs M q xss)"  
    using \<open>map (\<lambda> t . (t_input t, t_output t)) p \<in> set tr\<close> by blast
  then show "x \<in> set (language_state_for_inputs M q xss)"
    using \<open>x = map (\<lambda> t . (t_input t, t_output t)) p\<close> by auto
qed

lemma LS\<^sub>i\<^sub>n_inputs : 
  assumes "io \<in> LS\<^sub>i\<^sub>n M q U"
  shows "map fst io \<in> U" 
proof -
  obtain p where "io = map (\<lambda> t . (t_input t, t_output t)) p"
           and   "path M q p"
           and   "map t_input p \<in> U"
    using assms by auto
  then have "map fst io = map t_input p" 
    by auto
  then show ?thesis 
    using \<open>map t_input p \<in> U\<close> by auto
qed

lemma language_state_for_input_inputs : 
  assumes "io \<in> set (language_state_for_input M q xs)"
  shows "map fst io = xs" 
proof -
  obtain p where "io = map (\<lambda> t . (t_input t, t_output t)) p"
           and   "p \<in> set (filter (\<lambda> ts . xs = map t_input ts) (paths_of_length M q (length xs)))"
    using assms by auto
  then show ?thesis by auto
qed


lemma language_state_for_inputs_inputs : 
  assumes "io \<in> set (language_state_for_inputs M q U)"
  shows "map fst io \<in> set U"
  by (metis assms language_state_for_input_inputs language_state_for_inputs_from_language_state_for_input) 

lemma language_state_for_inputs_subset_LS\<^sub>i\<^sub>n : "set (language_state_for_inputs M q xss) \<subseteq> LS\<^sub>i\<^sub>n M q (set xss)"
proof 
  fix x assume "x \<in> set (language_state_for_inputs M q xss)"
  then obtain p where "x = map (\<lambda> t . (t_input t, t_output t)) p"
                and   "p \<in> set (filter (\<lambda> ts . map fst x = map t_input ts) (paths_of_length M q (length (map fst x))))"
    by auto
  then have "path M q p"
    by (metis (no_types) \<open>p \<in> set (filter (\<lambda>ts. map fst x = map t_input ts) (paths_of_length M q (length (map fst x))))\<close> filter_set member_filter paths_of_length.simps)
  moreover have "map t_input p = map fst x"
    by (simp add: \<open>x = map (\<lambda>t. (t_input t, t_output t)) p\<close>)
  ultimately have "x \<in> LS\<^sub>i\<^sub>n M q {map fst x}"
    using LS\<^sub>i\<^sub>n.simps \<open>x = map (\<lambda>t. (t_input t, t_output t)) p\<close> by auto 
  moreover have "map fst x \<in> set xss"
    using \<open>x \<in> set (language_state_for_inputs M q xss)\<close> language_state_for_inputs_inputs by fastforce
  ultimately show "x \<in> LS\<^sub>i\<^sub>n M q (set xss)"
    using \<open>x = map (\<lambda>t. (t_input t, t_output t)) p\<close> by auto  
qed
    

    

lemma LS\<^sub>i\<^sub>n_code[code] : "LS\<^sub>i\<^sub>n M q (set xss) = set (language_state_for_inputs M q xss)"
  by (meson LS\<^sub>i\<^sub>n_subset_language_state_for_inputs language_state_for_inputs_subset_LS\<^sub>i\<^sub>n subset_antisym) 
 

value "LS\<^sub>i\<^sub>n M_ex 2 {[1]}"






lemma path_append[intro!] :
  assumes "path M q p1"
      and "path M (target p1 q) p2"
  shows "path M q (p1@p2)"
using assms by (induct p1 arbitrary: p2; auto)
  
lemma path_prefix :
  assumes "path M q (p1@p2)"
  shows "path M q p1"
  using assms by (induction p1 arbitrary: q; auto)

lemma path_suffix :
  assumes "path M q (p1@p2)"
  shows "path M (target p1 q) p2"
using assms by (induction p1 arbitrary: q; auto)

lemma path_append_elim[elim!] :
  assumes "path M q (p1@p2)"
  obtains "path M q p1"
      and "path M (target p1 q) p2"
  by (meson assms path_prefix path_suffix)

lemma path_append_target:
  "target (p1@p2) q = target p2 (target p1 q)" 
  by (induction p1) (simp+)

lemma path_append_target_hd :
  assumes "length p > 0"
  shows "target p q = target (tl p) (t_target (hd p))"
using assms by (induction p) (simp+)


fun LS :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> (Input \<times> Output) list set" where
  "LS M q = { p_io p | p . path M q p }"

abbreviation "L M \<equiv> LS M (initial M)"



fun cartesian_product_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where 
  "cartesian_product_list xs ys = concat (map (\<lambda> x . map (\<lambda> y . (x,y)) ys) xs)"

value "cartesian_product_list [1,2,3::nat] [10,20,30::nat]"

lemma cartesian_product_list_set : "set (cartesian_product_list xs ys) = {(x,y) | x y . x \<in> set xs \<and> y \<in> set ys}"
  by auto

fun product_transitions :: "('state1, 'b) FSM_scheme \<Rightarrow> ('state2, 'c) FSM_scheme \<Rightarrow> ('state1 \<times> 'state2) Transition list" where
  "product_transitions A B = map (\<lambda> (t1,t2). ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))) (filter (\<lambda> (t1,t2) . t_input t1 = t_input t2 \<and> t_output t1 = t_output t2) (cartesian_product_list (wf_transitions A) (wf_transitions B)))"


value "product_transitions M_ex M_ex'"





    

lemma product_transitions_alt1 : "set (product_transitions A B) = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
proof 
  show "set (product_transitions A B) \<subseteq> {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
  proof 
    fix x assume "x \<in> set (product_transitions A B)"
    then obtain t1 t2 where "x = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
                        and "t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
                        and "(t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B))"
      by force
    then show "x \<in> {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}" by blast
  qed

  show "{((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2} \<subseteq> set (product_transitions A B)"
    by force
qed

lemma product_transitions_alt2 : "set (product_transitions A B) = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . t1 \<in> set (wf_transitions A) \<and> t2 \<in> set (wf_transitions B) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
(is "?P = ?A2")
proof -
  have "?P = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
    using product_transitions_alt1 by assumption
  also have "... = ?A2" by force
  finally show ?thesis by auto
qed

lemma product_transitions_alt3 : "set (product_transitions A B) = {((q1,q2),x,y,(q1',q2')) | q1 q2 x y q1' q2' . (q1,x,y,q1') \<in> set (wf_transitions A) \<and> (q2,x,y,q2') \<in> set (wf_transitions B)}"
(is "?P = ?A3")
proof -
  have "?P = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . t1 \<in> set (wf_transitions A) \<and> t2 \<in> set (wf_transitions B) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
    using product_transitions_alt2 by assumption
  also have "... = ?A3" by force
  finally show ?thesis by simp
qed


fun product :: "('state1, 'b) FSM_scheme \<Rightarrow> ('state2, 'c) FSM_scheme \<Rightarrow> (('state1 \<times> 'state2), 'b) FSM_scheme" where
  "product A B =
  \<lparr>
    initial = (initial A, initial B),
    inputs = (inputs A) @ (inputs B),
    outputs = (outputs A) @ (outputs B),
    transitions = product_transitions A B,
    \<dots> = FSM.more A    
  \<rparr>"

    (*
    inputs = remdups ((inputs A) @ (inputs B)),
    outputs = remdups ((outputs A) @ (outputs B)),
    transitions = remdups (product_transitions A B)
    *)


value "product M_ex M_ex'"

abbreviation "left_path p \<equiv> map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p"
abbreviation "right_path p \<equiv> map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p"
abbreviation "zip_path p1 p2 \<equiv> (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))"


lemma product_simps[simp]:
  "initial (product A B) = (initial A, initial B)"  
  "inputs (product A B) = inputs A @ inputs B"
  "outputs (product A B) = outputs A @ outputs B"
  "transitions (product A B) = product_transitions A B"
unfolding product_def by simp+




lemma product_transitions_wf :
  "set (product_transitions A B) = h (product A B)"
proof -
  have "\<And> t . t \<in> set (product_transitions A B) \<Longrightarrow> t \<in> h (product A B)"
  proof -
    fix t assume *: "t \<in> set (product_transitions A B)"
    then obtain t1 t2 where "t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)"
                        and "t1 \<in> h A \<and> t2 \<in> h B \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
      using product_transitions_alt2[of A B] by blast
    then have "is_wf_transition (product A B) t"
      unfolding is_wf_transition.simps by auto
    then show "t \<in> h (product A B)" using *
      by (metis filter_set member_filter product_simps(4) wf_transitions.simps) 
  qed
  moreover have "\<And> t . t \<in> h (product A B) \<Longrightarrow>  t \<in> set (product_transitions A B)"
    by (metis filter_set member_filter product_simps(4) wf_transitions.simps) 
  ultimately show ?thesis by blast
qed
  

lemma product_transition :
  "((q1,q2),x,y,(q1',q2')) \<in> h (product A B) \<longleftrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B"
  using product_transitions_wf[of A B] product_transitions_alt3[of A B] by blast


lemma product_path:
  "path (product A B) (q1,q2) p \<longleftrightarrow> (path A q1 (left_path p) \<and> path B q2 (right_path p))"
proof (induction p arbitrary: q1 q2)
  case Nil
  then show ?case by auto
next
  case (Cons t p)
  then show ?case 
  proof (cases "path (product A B) (q1, q2) [t]")
    case True
    then have "t \<in> h (product A B)"
      by (meson path'.simps(2) path_code) 
    then obtain t1 t2 where "t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2))"
                        and "t1 \<in> set (wf_transitions A)" 
                        and "t2 \<in> set (wf_transitions B)" 
                        and "t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
    proof -
      assume a1: "\<And>t1 t2. \<lbrakk>t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2); t1 \<in> h A; t2 \<in> h B; t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<rbrakk> \<Longrightarrow> thesis"
      have "(q1, q2) = t_source t \<and> path (product A B) (t_target t) [] \<and> t \<in> set (transitions (product A B)) \<and> t_input t \<in> set (inputs (product A B)) \<and> t_output t \<in> set (outputs (product A B))"
        using True by blast
      then have "t \<in> {((t_source p, t_source pa), t_input p, t_output p, t_target p, t_target pa) | p pa. p \<in> h A \<and> pa \<in> h B \<and> t_input p = t_input pa \<and> t_output p = t_output pa}"
        by (metis product_simps(4) product_transitions_alt2)
      then show ?thesis
        using a1 by blast
    qed

    have "t1 = (fst (t_source t), t_input t, t_output t, fst (t_target t))" 
      using \<open>t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2))\<close> by auto
    then have "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
      using \<open>t1 \<in> set (wf_transitions A)\<close> by auto
    have "path A q1 [(fst (t_source t), t_input t, t_output t, fst (t_target t))]"
    proof -
      have "q1 = t_source (fst (t_source t), t_input t, t_output t, fst (t_target t))"
        by (metis (no_types) True fst_conv path'.simps(2) path_code)
      then show ?thesis
        using \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A\<close> by blast
    qed

    then have *: "path A q1 (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) (t # p)) = path A (fst (t_target t)) (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p)"
      by auto

    have "t2 = (snd (t_source t), t_input t, t_output t, snd (t_target t))" 
      using \<open>t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2))\<close> \<open>t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close> by auto
    then have "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
      using \<open>t2 \<in> set (wf_transitions B)\<close> by auto
    have "path B q2 [(snd (t_source t), t_input t, t_output t, snd (t_target t))]"
    proof -
      have "(t_source t1, t_source t2) = (q1, q2)"
        by (metis (no_types) True \<open>t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)\<close> fstI path'.simps(2) path_code)
      then have "t_source t1 = q1 \<and> t_source t2 = q2"
        by simp
      then show ?thesis
        using \<open>(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B\<close> \<open>t2 = (snd (t_source t), t_input t, t_output t, snd (t_target t))\<close> by fastforce
    qed

    then have **: "path B q2 (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) (t # p)) = path B (snd (t_target t)) (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p)"
      by auto

    have ***: "path (product A B) (q1, q2) (t # p) = path (product A B) (t_target t) p"
      by (metis True path'.simps(2) path_code) 
      
      

    show ?thesis
      by (metis (no_types, lifting) "*" "**" Cons.IH "***" prod.collapse)
  next
    case False
    then have *: "\<not> path (product A B) (q1, q2) (t # p)"
      by (metis (no_types, lifting) list.distinct(1) list.sel(1) path.simps) 

    have "\<not> (path A q1 [(fst (t_source t), t_input t, t_output t, fst (t_target t))]
              \<and> path B q2 [(snd (t_source t), t_input t, t_output t, snd (t_target t))])"
    proof (rule ccontr)
      assume "\<not> \<not> (path A q1 [(fst (t_source t), t_input t, t_output t, fst (t_target t))]
              \<and> path B q2 [(snd (t_source t), t_input t, t_output t, snd (t_target t))])"
      then have "q1 = fst (t_source t)"
           and  "q2 = snd (t_source t)"
           and  "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
           and  "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
        by auto

      have "t \<in> set (transitions (product A B))"
      proof -
        have "t = ((fst (t_source t), snd (t_source t)), t_input t, t_output t, fst (t_target t), snd (t_target t))"
          by auto
        then have "t \<in> {((a, b), n, na, aa, ba) |a b n na aa ba. (a, n, na, aa) \<in> h A \<and> (b, n, na, ba) \<in> h B}"
          using \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A\<close> \<open>(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B\<close> by blast
        then show ?thesis
          by (metis (no_types) product_simps(4) product_transitions_alt3)
      qed 

      have "t_input t \<in> set (inputs A)" 
      and  "t_output t \<in> set (outputs A)"
        using \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A\<close> by auto
      then have "t_input t \<in> set (inputs (product A B))" 
           and  "t_output t \<in> set (outputs (product A B))" 
        by auto

      have "t \<in> h (product A B)"
        by (metis \<open>t \<in> set (transitions (product A B))\<close> \<open>t_input t \<in> set (inputs (product A B))\<close> \<open>t_output t \<in> set (outputs (product A B))\<close> filter_set is_wf_transition.elims(3) member_filter wf_transitions.elims) 
        
      have "path (product A B) (q1, q2) [t]"
        by (metis \<open>q1 = fst (t_source t)\<close> \<open>q2 = snd (t_source t)\<close> \<open>t \<in> h (product A B)\<close> path.simps prod.collapse)
        
      then show "False" using False by auto 
    qed

    then have **: "\<not> (path A q1 (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) (t # p)) 
                      \<and> path B q2 (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) (t # p)))" by auto

    show ?thesis using * ** by auto
  qed
qed




lemma product_path_rev:
  assumes "p_io p1 = p_io p2"
  shows "path (product A B) (q1,q2) (zip_path p1 p2)
          \<longleftrightarrow> path A q1 p1 \<and> path B q2 p2"
proof -
  have "length p1 = length p2" using assms
    using map_eq_imp_length_eq by blast 
  then have "(map (\<lambda> t . (fst (t_source t), t_input t, t_output t, fst (t_target t))) (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))) = p1"
    by (induction p1 p2 arbitrary: q1 q2 rule: list_induct2; auto)

  moreover have "(map (\<lambda> t . (snd (t_source t), t_input t, t_output t, snd (t_target t))) (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))) = p2"
    using \<open>length p1 = length p2\<close> assms by (induction p1 p2 arbitrary: q1 q2 rule: list_induct2; auto)

  ultimately show ?thesis using product_path[of A B q1 q2 "(map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))"]
    by auto
qed
    
    






lemma "LS (product A B) (q1,q2) = LS A q1 \<inter> LS B q2"
proof 
  show "LS (product A B) (q1, q2) \<subseteq> LS A q1 \<inter> LS B q2"
  proof 
    fix io assume "io \<in> LS (product A B) (q1, q2)"
    then obtain p where "io = p_io p" 
                    and "path (product A B) (q1,q2) p"
      by auto
    then obtain p1 p2 where "path A q1 p1" 
                        and "path B q2 p2"
                        and "io = p_io p1" 
                        and "io = p_io p2"
      using product_path[of A B q1 q2] by auto
    then show "io \<in> LS A q1 \<inter> LS B q2" 
      unfolding LS.simps by blast
  qed

  show "LS A q1 \<inter> LS B q2 \<subseteq> LS (product A B) (q1, q2)"
  proof
    fix io assume "io \<in> LS A q1 \<inter> LS B q2"
    then obtain p1 p2 where "path A q1 p1" 
                        and "path B q2 p2"
                        and "io = p_io p1" 
                        and "io = p_io p2"
                        and "p_io p1 = p_io p2"
      by auto

    let ?p = "zip_path p1 p2"
    
    
    have "length p1 = length p2"
      using \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq by blast 
    moreover have "p_io ?p = p_io (map fst (zip p1 p2))" by auto
    ultimately have "p_io ?p = p_io p1" by auto

    then have "p_io ?p = io" 
      using \<open>io = p_io p1\<close> by auto
    moreover have "path (product A B) (q1, q2) ?p"
      using product_path_rev[OF \<open>p_io p1 = p_io p2\<close>, of A B q1 q2] \<open>path A q1 p1\<close> \<open>path B q2 p2\<close> by auto
    ultimately show "io \<in> LS (product A B) (q1, q2)" 
      unfolding LS.simps by blast
  qed
qed


inductive_set nodes :: "('state, 'b) FSM_scheme \<Rightarrow> 'state set" for M :: "('state, 'b) FSM_scheme" where
  initial[intro!]: "initial M \<in> nodes M" |
  step[intro!]: "t \<in> h M \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_target t \<in> nodes M"


instantiation FSM_ext  :: (type,type) size 
begin

definition size where [simp, code]: "size (m::('a, 'b) FSM_ext) = card (nodes m)"

instance ..

end

lemma nodes_path : 
  assumes "q \<in> nodes M"
  and     "path M q p"
shows "(target p q) \<in> nodes M"
  using assms proof (induction p arbitrary: q) 
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then have "t_target a \<in> nodes M" 
       and  "path M (t_target a) p" 
    using Cons by auto
  then show ?case
    using Cons.IH[of "t_target a"] by auto
qed

lemma nodes_path_initial :
  assumes "path M (initial M) p"
  shows "(target p (initial M)) \<in> nodes M"
  by (meson assms nodes.initial nodes_path)


lemma path_reachable : 
  assumes "reachable M q1 q2"
  obtains p where "path M q1 p"
            and   "target p q1 = q2"
  using assms unfolding reachable.simps
proof (cases "q1 = q2")
  case True
  then have "path M q1 []" and "target [] q1 = q2" by auto
  then show ?thesis using that by blast
next
  case False
  then have "(q1, q2) \<in> pairwise_reachable M" using assms by auto
  then have "\<exists> p . path M q1 p \<and> target p q1 = q2" unfolding pairwise_reachable.simps pairwise_immediately_reachable.simps
  proof (induction rule: trancl.induct) 
    case (r_into_trancl a b)
    then obtain t where "t \<in> h M"
                  and   "a = t_source t"
                  and   "b = t_target t"
      by auto
    then have "path M a [t] \<and> target [t] a = b" by auto
    then show ?case by force 
  next
    case (trancl_into_trancl a b c)
    then obtain p t where "t \<in> h M"
                and   "b = t_source t"
                and   "c = t_target t"
                and "path M a p \<and> target p a = b"
      by auto
    then have "path M a (p@[t]) \<and> target (p@[t]) a = c" by auto
    then show ?case by metis 
  qed
  then show ?thesis using that by blast
qed 

lemma reachable_nodes :
  assumes "initially_reachable M q"
  shows "q \<in> nodes M"
  by (metis assms initially_reachable.elims(2) nodes.initial nodes_path path_reachable)

(* TODO: remove/refactor this legacy method of calculating nodes, superceded by nodes generated via distinct paths  *)
fun nodes_list :: "('state, 'b) FSM_scheme \<Rightarrow> 'state list" where
  "nodes_list M = remdups ((initial M) # (filter (initially_reachable M) (map t_target (wf_transitions M))))"

lemma nodes'_nodes_list : "set (nodes_list M) = nodes' M"
  unfolding nodes_list.simps nodes'.simps
  by (metis (lifting) list.simps(15) set_remdups) 



lemma nodes_nodes' : "nodes M = nodes' M"
proof
  show "nodes M \<subseteq> nodes' M"
  proof 
    fix x assume "x \<in> nodes M"
    then show "x \<in> nodes' M"
    proof (induction)
      case initial
      then show ?case by auto
    next
      case (step t)
      then show ?case
        using nodes'_next by blast 
    qed
  qed
  show "nodes' M \<subseteq> nodes M"
  proof 
    fix x assume "x \<in> nodes' M"

    then show "x \<in> nodes M"
      by (metis filter_set insert_iff member_filter nodes.simps nodes'.simps reachable_nodes)
  qed
qed

(*
lemma nodes_code[code] : "nodes M = set (nodes_list M)"
  using nodes_nodes' nodes'_nodes_list by metis
*)

lemma visited_states_prefix :
  assumes "q' \<in> set (visited_states q p)"
  shows "\<exists> p1 p2 . p = p1@p2 \<and> target p1 q = q'"
using assms proof (induction p arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case 
  proof (cases "q' \<in> set (visited_states (t_target a) p)")
    case True
    then obtain p1 p2 where "p = p1 @ p2 \<and> target p1 (t_target a) = q'"
      using Cons.IH by blast
    then have "(a#p) = (a#p1)@p2 \<and> target (a#p1) q = q'"
      by auto
    then show ?thesis by blast
  next
    case False
    then have "q' = q" 
      using Cons.prems by auto     
    then show ?thesis
      by auto 
  qed
qed 

lemma nondistinct_path_loop :
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
shows "\<exists> p1 p2 p3 . p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target p1 q = target (p1@p2) q"
using assms proof (induction p arbitrary: q)
  case (nil M q)
  then show ?case by auto
next
  case (cons t M ts)
  then show ?case 
  proof (cases "distinct (visited_states (t_target t) ts)")
    case True
    then have "q \<in> set (visited_states (t_target t) ts)"
      using cons.prems by simp 
    then obtain p2 p3 where "ts = p2@p3" and "target p2 (t_target t) = q" 
      using visited_states_prefix[of q "t_target t" ts] by blast
    then have "(t#ts) = []@(t#p2)@p3 \<and> (t#p2) \<noteq> [] \<and> target [] q = target ([]@(t#p2)) q"
      using cons.hyps by auto
    then show ?thesis by blast
  next
    case False
    then obtain p1 p2 p3 where "ts = p1@p2@p3" and "p2 \<noteq> []" and "target p1 (t_target t) = target (p1@p2) (t_target t)" 
      using cons.IH by blast
    then have "t#ts = (t#p1)@p2@p3 \<and> p2 \<noteq> [] \<and> target (t#p1) q = target ((t#p1)@p2) q"
      by simp
    then show ?thesis by blast    
  qed
qed

lemma nondistinct_path_shortening : 
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
shows "\<exists> p' . path M q p' \<and> target p' q = target p q \<and> length p' < length p"
proof -
  obtain p1 p2 p3 where *: "p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target p1 q = target (p1@p2) q" 
    using nondistinct_path_loop[OF assms] by blast
  then have "path M q (p1@p3)"
    using assms(1) by force
  moreover have "target (p1@p3) q = target p q"
    by (metis (full_types) * path_append_target)
  moreover have "length (p1@p3) < length p"
    using * by auto
  ultimately show ?thesis by blast
qed

lemma paths_finite : "finite { p . path M q p \<and> length p \<le> k }"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  have "{ p . path M q p \<and> length p = (Suc k) } = set (paths_of_length M q (Suc k))"
    using paths_of_length_path_set[of M q "Suc k"] by blast
  then have "finite { p . path M q p \<and> length p = (Suc k) }"
    by (metis List.finite_set)
  moreover have "finite { p . path M q p \<and> length p < (Suc k) }"
    using Suc.IH less_Suc_eq_le by auto
  moreover have "{ p . path M q p \<and> length p \<le> (Suc k) } = { p . path M q p \<and> length p = (Suc k) } \<union> { p . path M q p \<and> length p < (Suc k) }"
    by auto
  ultimately show ?case
    by auto 
qed



lemma distinct_path_from_nondistinct_path :
  assumes "path M q p"
  and     "\<not> distinct (visited_states q p)"
obtains p' where "path M q p'" and "target p q = target p' q" and "distinct (visited_states q p')"
proof -
  
  let ?paths = "{p' . (path M q p' \<and> target p' q = target p q \<and> length p' \<le> length p)}"
  let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
  have "?paths \<noteq> empty" 
    using assms(1) by auto
  moreover have "finite ?paths" 
    using paths_finite[of M q "length p"]
    by (metis (no_types, lifting) Collect_mono rev_finite_subset)
  ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" 
    by (meson arg_min_nat_lemma equals0I)
  then have "path M q ?minPath" and "target ?minPath q = target p q" 
    by auto
  
  moreover have "distinct (visited_states q ?minPath)"
  proof (rule ccontr)
    assume "\<not> distinct (visited_states q ?minPath)"
    have "\<exists> p' . path M q p' \<and> target p' q = target p q \<and> length p' < length ?minPath" 
      using nondistinct_path_shortening[OF \<open>path M q ?minPath\<close> \<open>\<not> distinct (visited_states q ?minPath)\<close>] minPath_def
            \<open>target ?minPath q = target p q\<close> by auto
    then show "False" 
      using minPath_def using arg_min_nat_le dual_order.strict_trans1 by auto 
  qed

  ultimately show ?thesis
    by (simp add: that)
qed     

lemma path_to_nodes : 
  assumes "q \<in> nodes M"
  obtains p where "path M (initial M) p"
            and   "q = (target p (initial M))"
proof -
  have "q \<in> nodes' M"
    using assms nodes_nodes' by force  
  then have "reachable M (initial M) q" 
    by auto
  then show ?thesis
    by (metis path_reachable that)
qed




fun distinct_paths_up_to_length :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "distinct_paths_up_to_length M q 0 = [[]]" |
  "distinct_paths_up_to_length M q (Suc n) = (let pn= distinct_paths_up_to_length M q n in
    pn @ map (\<lambda> pt . (fst pt)@[(snd pt)]) (filter (\<lambda>pt . (t_source (snd pt) = target (fst pt) q) \<and> distinct ((visited_states q (fst pt))@[(t_target (snd pt))])) (concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (wf_transitions M)) (filter (\<lambda>p . length p = n) pn)))))"



lemma distinct_paths_up_to_length_path_set : "set (distinct_paths_up_to_length M q n) = {p . path M q p \<and> distinct (visited_states q p) \<and> length p \<le> n}"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)

  let ?pn = "distinct_paths_up_to_length M q n"
  let ?pnS = "map (\<lambda> pt . (fst pt)@[(snd pt)]) (filter (\<lambda>pt . (t_source (snd pt) = target (fst pt) q) \<and> distinct ((visited_states q (fst pt))@[(t_target (snd pt))])) (concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (wf_transitions M)) (filter (\<lambda>p . length p = n) ?pn))))"

  

  have "distinct_paths_up_to_length M q (Suc n) = ?pn @ ?pnS"
    unfolding distinct_paths_up_to_length.simps(2)[of M q n] by metis
  then have "set (distinct_paths_up_to_length M q (Suc n)) = set ?pn \<union> set ?pnS"
    using set_append by metis

  have "\<And> p . p \<in> set ?pn \<Longrightarrow> length p \<le> n" using Suc.IH by blast
  then have "\<And> p . p \<in> set ?pn \<Longrightarrow> length p \<noteq> Suc n" by fastforce 
  moreover have "\<And> p . p \<in> set ?pnS \<Longrightarrow> length p = Suc n"  by auto
  ultimately have "set ?pn \<inter> set ?pnS = {}" by blast

  let ?sn = "{p . path M q p \<and> distinct (visited_states q p) \<and> length p \<le> n}"
  let ?snS = "{p . path M q p \<and> distinct (visited_states q p) \<and> length p = Suc n}"

  have "{p. path M q p \<and> distinct (visited_states q p) \<and> length p \<le> Suc n} = ?sn \<union> ?snS" by fastforce
  have "?sn \<inter> ?snS = {}" by fastforce

  

  let ?fc = "(\<lambda> pt . (fst pt)@[(snd pt)])"
  let ?ff = "(\<lambda>pt . (t_source (snd pt) = target (fst pt) q) \<and> distinct ((visited_states q (fst pt))@[(t_target (snd pt))]))"
  let ?fp = "(concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (wf_transitions M)) (filter (\<lambda>p . length p = n) ?pn)))"

  have "?pnS = map ?fc (filter ?ff ?fp)" by presburger
  have "set ?fp = {(p,t) | p t . p \<in> set ?pn \<and> t \<in> h M \<and> length p = n}" by fastforce
  then have "set ?fp = {(p,t) | p t . path M q p \<and> distinct (visited_states q p) \<and> t \<in> h M \<and> length p = n}" 
    using Suc.IH by fastforce
  moreover have "set (filter ?ff ?fp) = {(p,t) \<in> set ?fp . t_source t = target p q \<and> distinct ((visited_states q p)@[t_target t])}"
    by fastforce
  ultimately have "set (filter ?ff ?fp) = {(p,t) \<in> {(p,t) | p t . path M q p \<and> distinct (visited_states q p) \<and> t \<in> h M \<and> length p = n} . t_source t = target p q \<and> distinct ((visited_states q p)@[t_target t])}"    
    by presburger
  then have "set (filter ?ff ?fp) = {(p,t) | p t . path M q p \<and> distinct (visited_states q p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p q \<and> distinct ((visited_states q p)@[t_target t])}"
    by fastforce    
  moreover have "\<And> p t . (path M q p \<and> distinct (visited_states q p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p q \<and> distinct ((visited_states q p)@[t_target t]))
                   = (path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length p = n)"
  proof 
    have "\<And> p t . (visited_states q p)@[t_target t] = visited_states q (p@[t])" by auto
    then have *: "\<And> p t . distinct (visited_states q p @ [t_target t]) = (distinct (visited_states q p) \<and> distinct (visited_states q (p @ [t])))" by auto
    have **: "\<And> p t . (path M q p \<and> t \<in> h M \<and> t_source t = target p q) = path M q (p @ [t])"
      by (metis (no_types) list.distinct(1) list.inject path.simps path_append path_append_elim) 
    show "\<And> p t . path M q p \<and>
           distinct (visited_states q p) \<and>
           t \<in> h M \<and>
           length p = n \<and> t_source t = target p q \<and> distinct (visited_states q p @ [t_target t]) \<Longrightarrow>
           path M q (p @ [t]) \<and> distinct (visited_states q (p @ [t])) \<and> length p = n" 
      using * ** by metis
    show "\<And>p t. path M q (p @ [t]) \<and> distinct (visited_states q (p @ [t])) \<and> length p = n \<Longrightarrow>
           path M q p \<and>
           distinct (visited_states q p) \<and>
           t \<in> h M \<and>
           length p = n \<and> t_source t = target p q \<and> distinct (visited_states q p @ [t_target t])"
      using * ** by fastforce
  qed

  ultimately have "set (filter ?ff ?fp) = {(p,t) | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length p = n }"
    by presburger
  then have "set (filter ?ff ?fp) = {(p,t) | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
    by auto
  moreover have "set ?pnS = image (\<lambda>pt. fst pt @ [snd pt]) (set (filter ?ff ?fp))" by auto
  ultimately have "set ?pnS = image (\<lambda>pt. fst pt @ [snd pt]) {(p,t) | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
    by presburger

  then have "set ?pnS = {(\<lambda>pt. fst pt @ [snd pt]) pt | pt . pt \<in> {(p,t) | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }}"
    using Setcompr_eq_image by metis
  then have "set ?pnS = {p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
    by auto
  moreover have "{p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n } = ?snS"
  proof 
    show "{p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n } \<subseteq> ?snS"
      by blast
    show "?snS \<subseteq> {p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
    proof 
      fix p assume "p \<in> ?snS"
      then have "length p > 0" by auto
      then have "p = (butlast p)@[last p]" by auto

      have "path M q ((butlast p)@[last p]) \<and> distinct (visited_states q ((butlast p)@[last p])) \<and> length ((butlast p)@[last p]) = Suc n"
        using \<open>p \<in> ?snS\<close> \<open>p = (butlast p)@[last p]\<close> by auto
      then have "(butlast p)@[last p] \<in> {p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
        by fastforce
      then show "p \<in> {p@[t] | p t . path M q (p@[t]) \<and> distinct (visited_states q (p@[t])) \<and> length (p@[t]) = Suc n }"
        using \<open>p = (butlast p)@[last p]\<close> by auto
    qed
  qed
  ultimately have "set ?pnS = ?snS" by presburger
    
  show ?case 
    using \<open>set (distinct_paths_up_to_length M q (Suc n)) = set ?pn \<union> set ?pnS\<close> 
          \<open>{p. path M q p \<and> distinct (visited_states q p) \<and> length p \<le> Suc n} = ?sn \<union> ?snS\<close>
          Suc.IH
          \<open>set ?pnS = ?snS\<close>
    by blast
qed  




fun nodes_from_distinct_paths :: "('a,'b) FSM_scheme \<Rightarrow> 'a list" where
  "nodes_from_distinct_paths M = remdups (map (\<lambda>p . target p (initial M)) (distinct_paths_up_to_length M (initial M) (length (wf_transitions M))))"

lemma distinct_path_length_limit :
  assumes "path M q p"
  and     "distinct (visited_states q p)"
shows "length p \<le> length (wf_transitions M)"
proof (rule ccontr)
  assume *: "\<not> length p \<le> length (wf_transitions M)"

  have "card (h M) \<le> length (wf_transitions M)"
    using card_length by blast 
  have "set p \<subseteq> h M" 
    using assms(1) by (meson path_h) 
  
  have "\<not> distinct p"
    by (metis (no_types, lifting) "*" List.finite_set \<open>card (h M) \<le> length (wf_transitions M)\<close> \<open>set p \<subseteq> h M\<close> card_mono distinct_card dual_order.trans)
  then have "\<not> distinct (map t_target p)"
    by (simp add: distinct_map)
  then have "\<not>distinct (visited_states q p)"
    unfolding visited_states.simps by auto
  then show "False" using assms(2) by auto
qed

lemma distinct_path_length_limit_nodes :
  assumes "path M q p"
  and     "q \<in> nodes M"
  and     "distinct (visited_states q p)"
shows "length p < size M"
proof (rule ccontr)
  assume *: "\<not> length p < size M"

  have "length (visited_states q p) = Suc (length p)"
    by simp
  then have "length (visited_states q p) \<ge> size M"
    using "*" by linarith
  moreover have "set (visited_states q p) \<subseteq> nodes M"
    by (metis assms(1) assms(2) nodes_path path_prefix subsetI visited_states_prefix)
  moreover have "finite (nodes M)"
    by (metis List.finite_set finite.simps nodes'.simps nodes_nodes')
  ultimately have "\<not>distinct (visited_states q p)"
    unfolding size_def
    by (metis "*" Suc_le_lessD \<open>length (visited_states q p) = Suc (length p)\<close> card_mono distinct_card size_def)
  then show "False" using assms(3) by auto
qed

lemma nodes_code[code]: "nodes M = set (nodes_from_distinct_paths M)"
proof -
  have "set (nodes_from_distinct_paths M) = image (\<lambda>p . target p (initial M)) {p. path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> length (wf_transitions M)}"
    using distinct_paths_up_to_length_path_set[of M "initial M" "length (wf_transitions M)"] by auto
  moreover have "{p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> length (wf_transitions M)} 
        = {p . path M (initial M) p \<and> distinct (visited_states (initial M) p)}" 
    using distinct_path_length_limit by metis
  ultimately have "set (nodes_from_distinct_paths M) = {target p (initial M) | p . path M (initial M) p \<and> distinct (visited_states (initial M) p)}"
    by (simp add: setcompr_eq_image)

  moreover have "{target p (initial M) | p . path M (initial M) p \<and> distinct (visited_states (initial M) p)} = nodes M"
  proof -
    have "\<And> q . q \<in> {target p (initial M) | p . path M (initial M) p \<and> distinct (visited_states (initial M) p)} \<Longrightarrow> q \<in> nodes M"
      using nodes_path by fastforce
    moreover have "\<And> q . q \<in> nodes M \<Longrightarrow> q \<in> {target p (initial M) | p . path M (initial M) p \<and> distinct (visited_states (initial M) p)}"
    proof -
      fix q :: 'a
      assume "q \<in> nodes M"
      then have "\<exists>ps. q = target ps (initial M) \<and> path M (initial M) ps \<and> distinct (visited_states (initial M) ps)"
        by (metis distinct_path_from_nondistinct_path path_to_nodes)
      then show "q \<in> {target ps (initial M) |ps. path M (initial M) ps \<and> distinct (visited_states (initial M) ps)}"
        by blast
    qed      
    ultimately show ?thesis by blast
  qed
      

  ultimately show ?thesis by fast
qed



















  




lemma product_nodes : "nodes (product A B) \<subseteq> (nodes A) \<times> (nodes B)"
proof 
  fix q assume "q \<in> nodes (product A B)"
  then obtain p where "path (product A B) (initial (product A B)) p"
                and   "q = target p (initial (product A B))" 
    by (metis path_to_nodes)

  let ?p1 = "left_path p"
  let ?p2 = "right_path p"

  have "path A (initial A) ?p1"
  and  "path B (initial B) ?p2"
    using product_path[of A B "initial A" "initial B" p]
    using \<open>path (product A B) (initial (product A B)) p\<close> by auto 

  moreover have "target p (initial (product A B)) = (target ?p1 (initial A), target ?p2 (initial B))"
    by (induction p; auto)  

  ultimately show "q \<in> (nodes A) \<times> (nodes B)"
    by (metis (no_types, lifting) SigmaI \<open>q = target p (initial (product A B))\<close> nodes_path_initial)
qed











fun completely_specified :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> q' y . (q,x,y,q') \<in> h M)"
abbreviation "completely_specifiedH M \<equiv> (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_alt_def : "completely_specified M = completely_specifiedH M"
  by force 


lemma h_contents :
  assumes "t \<in> h M"
  and     "t_source t \<in> nodes M"
shows "t_target t \<in> nodes M" 
and   "t_input t \<in> set (inputs M)"
and   "t_output t \<in> set (outputs M)"
  using assms by auto

fun deterministic :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "deterministic M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<longrightarrow> t_output t1 = t_output t2 \<and> t_target t1 = t_target t2)" 
abbreviation "deterministicH M \<equiv> (\<forall> q1 x y' y''  q1' q1'' . (q1,x,y',q1') \<in> h M \<and> (q1,x,y'',q1'') \<in> h M \<longrightarrow> y' = y'' \<and> q1' = q1'')"

lemma deterministic_alt_def : "deterministic M = deterministicH M" by auto



fun observable :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "observable M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<longrightarrow> t_target t1 = t_target t2)" 
abbreviation "observableH M \<equiv> (\<forall> q1 x y q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x,y,q1'') \<in> h M \<longrightarrow> q1' = q1'')"

lemma observable_alt_def : "observable M = observableH M" by auto
lemma observable_code[code] : "observable M = (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<longrightarrow> t_target t1 = t_target t2)"
  unfolding observable.simps by blast

value "observable M_ex"



fun single_input :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "single_input M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<longrightarrow> t_input t1 = t_input t2)" 
abbreviation "single_inputH M \<equiv> (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x',y',q1'') \<in> h M \<and> q1 \<in> nodes M \<longrightarrow> x = x')"
lemma single_input_alt_def : "single_input M = single_inputH M" by force

fun single_input_by_transition_list :: "('a, 'b) FSM_scheme \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "single_input_by_transition_list M [] = True" |
  "single_input_by_transition_list M (t1#ts) = (case find (\<lambda> t2 . t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2) ts of
    None \<Rightarrow> single_input_by_transition_list M ts | 
    Some _ \<Rightarrow> False)"


lemma find_result_props : 
  assumes "find P xs = Some x" 
  shows "x \<in> set xs" and "P x"
proof -
  show "x \<in> set xs" using assms by (metis find_Some_iff nth_mem)
  show "P x" using assms by (metis find_Some_iff)
qed

lemma single_input_by_transition_list_correctness :
  assumes "set xs \<subseteq> h M"
  shows "single_input_by_transition_list M xs = (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2))"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then have "a \<in> h M" by auto

  let ?P = "(\<forall> t1 \<in> set (a#xs) . \<not>(\<exists> t2 \<in> set (a#xs) .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2))"

  have "?P = (\<forall> t1 \<in> set (a#xs) . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2))"
    using set_subset_Cons by auto
  then have *: "?P = ((\<not>(\<exists> t2 \<in> set xs .a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input t2)) \<and> (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2)))"
    by auto
  
  
  show ?case
  proof (cases "find (\<lambda> t2 . a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input t2) xs")
    case None
    
    have "\<not>(\<exists> t2 \<in> set xs .a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input t2)"
      using find_None_iff[of "(\<lambda> t2 . a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input t2)" xs] None by blast
    then have "?P = (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2))"
      using * by blast
    moreover have "single_input_by_transition_list M (a#xs) = single_input_by_transition_list M xs"
      unfolding single_input_by_transition_list.simps None by auto
    ultimately show ?thesis using Cons by auto
  next
    case (Some a2)
    then have "a2 \<in> set xs" using find_result_props(1) by fast
    moreover have "a \<noteq> a2 \<and> t_source a = t_source a2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input a2"
      using find_result_props(2)[OF Some] by assumption
    ultimately have "\<not>?P"
      using \<open>(\<forall>t1\<in>set (a # xs). \<not> (\<exists>t2\<in>set (a # xs). t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2)) = (\<not> (\<exists>t2\<in>set xs. a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_source a \<in> nodes M \<and> t_input a \<noteq> t_input t2) \<and> (\<forall>t1\<in>set xs. \<not> (\<exists>t2\<in>set xs. t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2)))\<close> \<open>a2 \<in> set xs\<close> by blast 
    moreover have "\<not>(single_input_by_transition_list M (a#xs))"
      using Some unfolding single_input_by_transition_list.simps by auto
    ultimately show ?thesis by simp
  qed
qed

fun single_input' :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "single_input' M = single_input_by_transition_list M (wf_transitions M)"

lemma single_input_code[code] : "single_input M = single_input' M"
  unfolding single_input'.simps single_input.simps using single_input_by_transition_list_correctness[of "wf_transitions M" M]
  by (metis order_refl) 


value "single_input M_ex"


fun output_complete :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "output_complete M = (\<forall> t \<in> h M . \<forall> y \<in> set (outputs M) . \<exists> t' \<in> h M . t_source t = t_source t' \<and> t_input t = t_input t' \<and> t_output t' = y)" 
abbreviation "output_completeH M \<equiv> (\<forall> q x . (\<exists> y q' . (q,x,y,q') \<in> h M) \<longrightarrow> (\<forall> y \<in> set (outputs M) . \<exists> q' . (q,x,y,q') \<in> h M))"

lemma output_complete_alt_def : "output_complete M = output_completeH M" by (rule; fastforce)

value "output_complete M_ex"


fun acyclic :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "acyclic M = (\<forall> p . path M (initial M) p \<longrightarrow> distinct (visited_states (initial M) p))"
  (* original formulation: "acyclic M = finite (L M)" - this follows from the path-distinctness property, as repetitions along paths allow for infinite loops *)

fun contains_cyclic_path :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "contains_cyclic_path M = (\<exists> p \<in> set (distinct_paths_up_to_length M (initial M) (size M)) . \<exists> t \<in> h M . path M (initial M) (p@[t]) \<and> \<not>distinct (visited_states (initial M) (p@[t]))) "


lemma acyclic_code[code] : "acyclic M = (\<not>contains_cyclic_path M)"
proof 
  show "FSM3.acyclic M \<Longrightarrow> \<not> contains_cyclic_path M"
    by (meson acyclic.elims(2) contains_cyclic_path.elims(2))

  have "\<not> FSM3.acyclic M \<Longrightarrow> contains_cyclic_path M"
  proof -
    assume "\<not> FSM3.acyclic M"
    then obtain p where "path M (initial M) p" and "\<not>distinct (visited_states (initial M) p)" by auto
    

    let ?paths = "{ p' . path M (initial M) p' \<and> \<not>distinct (visited_states (initial M) p') \<and> length p' \<le> length p}"
    let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
    have "?paths \<noteq> empty" 
      using \<open>path M (initial M) p\<close> \<open>\<not>distinct (visited_states (initial M) p)\<close> by auto
    moreover have "finite ?paths" 
      using paths_finite[of M "initial M" "length p"]
      by (metis (no_types, lifting) Collect_mono rev_finite_subset)
    ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" 
      by (meson arg_min_nat_lemma equals0I)
    then have "path M (initial M) ?minPath" and "\<not>distinct (visited_states (initial M) ?minPath)" 
      by auto

    then have "length ?minPath > 0"
      by auto
    then have "length (butlast ?minPath) < length ?minPath"
      by auto
    moreover have "path M (initial M) (butlast ?minPath)"
      using \<open>path M (initial M) ?minPath\<close>
      by (metis (no_types, lifting) \<open>0 < length (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> append_butlast_last_id length_greater_0_conv path_prefix) 
    ultimately have "distinct (visited_states (initial M) (butlast ?minPath))"
      using dual_order.strict_implies_order dual_order.strict_trans1 minPath_def by blast

    then have "(butlast ?minPath) \<in> set (distinct_paths_up_to_length M (initial M) (size M))"
      using \<open>path M (initial M) (butlast ?minPath)\<close> distinct_path_length_limit_nodes
      by (metis (no_types, lifting) distinct_paths_up_to_length_path_set less_imp_le mem_Collect_eq nodes.initial)
    moreover have "(last ?minPath) \<in> h M"
      by (metis (no_types, lifting) \<open>0 < length (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> \<open>path M (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> contra_subsetD last_in_set length_greater_0_conv path_h) 
    moreover have "path M (initial M) ((butlast ?minPath)@[(last ?minPath)]) \<and> \<not>distinct (visited_states (initial M) ((butlast ?minPath)@[(last ?minPath)]))"
      using \<open>0 < length (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> \<open>\<not> distinct (visited_states (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p}))\<close> \<open>path M (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> by auto
    ultimately show "contains_cyclic_path M"
      unfolding contains_cyclic_path.simps
      by meson 
  qed
  then show "\<not> contains_cyclic_path M \<Longrightarrow> FSM3.acyclic M" by blast
qed



fun deadlock_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where 
  "deadlock_state M q = (\<not>(\<exists> t \<in> h M . t_source t = q))"

lemma deadlock_state_alt_def : "deadlock_state M q = (LS M q = {[]})" 
proof 
  show "deadlock_state M q \<Longrightarrow> LS M q = {[]}" 
  proof (rule ccontr)
    assume "deadlock_state M q" and "LS M q \<noteq> {[]}"
    moreover have "[] \<in> LS M q" by auto
    ultimately obtain xy io where "xy#io \<in> LS M q"
      by (metis all_not_in_conv is_singletonI' is_singleton_the_elem neq_Nil_conv singletonD) 
    then obtain t where "t \<in> h M" and "t_source t = q"
      by auto
    then show "False" 
      using \<open>deadlock_state M q\<close> by (meson deadlock_state.elims(2)) 
  qed
  show "LS M q = {[]} \<Longrightarrow> deadlock_state M q"
  proof (rule ccontr)
    assume "LS M q = {[]}" and "\<not> deadlock_state M q"
    then obtain t where "t \<in> h M \<and> t_source t = q" by auto
    then have "p_io [t] \<in> LS M q"
      by (metis (mono_tags, lifting) LS.simps cons mem_Collect_eq nil) 
    then show "False" using \<open>LS M q = {[]}\<close>
      by blast
  qed
qed

fun completed_path :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "completed_path M q p = deadlock_state M (target p q)"





fun io_in :: "(Input \<times> Output) list \<Rightarrow> Input list" where
  "io_in io = map fst io"

fun io_out :: "(Input \<times> Output) list \<Rightarrow> Input list" where
  "io_out io = map snd io"

lemma io_zip : "zip (io_in io) (io_out io) = io" 
  by (induction io; simp)





fun fst_io_target' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "fst_io_target' M [] q = Some q" |
  "fst_io_target' M (xy#io) q = (case (find (\<lambda> t' . t_source t' = q \<and> t_input t' = fst xy \<and> t_output t' = snd xy) (wf_transitions M)) of
    None \<Rightarrow> None |
    Some t' \<Rightarrow> fst_io_target' M io (t_target t'))"

fun fst_io_target :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "fst_io_target M io q = (case (fst_io_target' M io q) of 
    None \<Rightarrow> {} |
    Some t \<Rightarrow> {t})"

lemma find_set : 
  assumes "find P xs = Some x"
  shows "x \<in> set xs"
using assms proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis find.simps(2) list.set_intros(1) list.set_intros(2) option.inject) 
qed

lemma find_condition : 
  assumes "find P xs = Some x"
  shows "P x"
using assms proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis find.simps(2) option.inject)     
qed


lemma fst_io_target'_path :
  assumes "fst_io_target' M io q = Some q'"
  obtains p
  where "path M q p" 
    and "target p q = q'"
    and "p_io p = io"
proof -
  have "\<exists> p . path M q p \<and> target p q = q' \<and> p_io p = io"
  using assms proof (induction io arbitrary: q)
    case Nil 
    then show ?case by auto
  next
    case (Cons a io)
    from Cons.prems obtain t where *: "find (\<lambda> t' . t_source t' = q \<and> t_input t' = fst a \<and> t_output t' = snd a) (wf_transitions M) = Some t"
                                  and **: "fst_io_target' M io (t_target t) = Some q'"
      unfolding fst_io_target'.simps
      by (metis (no_types, lifting) option.case_eq_if option.exhaust_sel option.simps(3))  
  
    from * have "t \<in> h M" 
      by (meson find_set)
    have "t_source t = q" 
     and "t_input t = fst a" 
     and "t_output t = snd a"
      using find_condition[OF *] by auto  
      
    obtain p where "path M (t_target t) p" 
               and "target p (t_target t) = q'"
               and "p_io p = io"
      using "**" Cons.IH by blast  
  
  
    have "path M q (t#p)"
      using \<open>path M (t_target t) p\<close> \<open>t \<in> h M\<close> \<open>t_source t = q\<close> by blast 
    moreover have "target (t#p) q = q'" 
      using \<open>target p (t_target t) = q'\<close> by auto
    moreover have "p_io (t#p) = a#io"
      by (simp add: \<open>p_io p = io\<close> \<open>t_input t = fst a\<close> \<open>t_output t = snd a\<close>)
    ultimately show ?case
      by (metis (no_types, lifting))  
  qed
  then show ?thesis using that by blast
qed



fun is_io_target :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_io_target M [] q q' = (q = q')" |
  "is_io_target M (xy#io) q q' = (\<exists> t \<in> h M . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target M io (t_target t) q')"

value "is_io_target M_ex [(1,20)] (initial M_ex) 4"
value "is_io_target M_ex [(1,20)] (initial M_ex) 3"

fun is_io_target' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_io_target' M [] q q' = (q = q')" |
  "is_io_target' M (xy#io) q q' = (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target' M io (t_target t) q') (wf_transitions M) \<noteq> [])"

lemma is_io_target_code[code] :
  "is_io_target M io q q' = is_io_target' M io q q'" 
proof 
  show "is_io_target M io q q' \<Longrightarrow> is_io_target' M io q q'"
  proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)
    then obtain t where "t \<in> h M" 
                    and "t_source t = q" 
                    and "t_input t = fst xy" 
                    and "t_output t = snd xy" 
                    and "is_io_target M io (t_target t) q'"
      by auto
    then have "is_io_target' M io (t_target t) q'"
      using Cons.IH by auto
    have "t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target' M io (t_target t) q'"
      using \<open>is_io_target' M io (t_target t) q'\<close> \<open>t_input t = fst xy\<close> \<open>t_output t = snd xy\<close> \<open>t_source t = q\<close> by fastforce
      
    then have "(filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target' M io (t_target t) q') (wf_transitions M) \<noteq> [])"
      by (metis (mono_tags, lifting) \<open>t \<in> h M\<close> filter_empty_conv)  
      
    then show ?case by auto
  qed
  show "is_io_target' M io q q' \<Longrightarrow> is_io_target M io q q'"
  proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)

    let ?t = "hd (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target' M io (t_target t) q') (wf_transitions M))" 
    have "length (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target' M io (t_target t) q') (wf_transitions M)) > 0"
      using Cons by auto
    then obtain t where "t \<in> h M" 
                    and "t_source t = q" 
                    and "t_input t = fst xy" 
                    and "t_output t = snd xy" 
                    and "is_io_target' M io (t_target t) q'"
      using filter_empty_conv by blast
    then show ?case using Cons.IH
      by (meson is_io_target.simps(2)) 
  qed
qed


lemma is_io_target_path : 
  "is_io_target M io q q' \<longleftrightarrow> (\<exists> p . path M q p \<and> target p q = q' \<and> p_io p = io)"
proof (induction io arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons xy io)
  have "is_io_target M (xy # io) q q' \<Longrightarrow> (\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io)"
  proof -
    assume "is_io_target M (xy # io) q q'"
    then obtain t where "t \<in> h M" 
                    and "t_source t = q" 
                    and "t_input t = fst xy" 
                    and "t_output t = snd xy" 
                    and "is_io_target M io (t_target t) q'"
      by auto
    then obtain p where "path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io"
      using Cons by auto

    have "path M q (t#p)"
      using \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> \<open>t \<in> h M\<close> \<open>t_source t = q\<close> by blast
    moreover have "target (t#p) q = q'"
      using \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> by auto
    moreover have "p_io (t#p) = xy # io"
      by (simp add: \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> \<open>t_input t = fst xy\<close> \<open>t_output t = snd xy\<close>)
    ultimately have "path M q (t#p) \<and> target (t#p) q = q' \<and> p_io (t#p) = xy # io" 
      by auto
    then show "is_io_target M (xy # io) q q' \<Longrightarrow> (\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io)"
      by (metis (no_types, lifting)) 
  qed

  moreover have "(\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io) \<Longrightarrow> is_io_target M (xy # io) q q'"
  proof -
    assume "(\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io)"
    then obtain p where "path M q p \<and> target p q = q' \<and> p_io p = xy # io"
      by presburger 
    then have "length p > 0" 
      by auto

    let ?t = "hd p"
    let ?p = "tl p"
    have "path M (t_target ?t) ?p"
      using \<open>path M q p \<and> target p q = q' \<and> p_io p = xy # io\<close> by auto

    

    moreover have "target ?p (t_target ?t) = q'"
      using path_append_target_hd[OF \<open>length p > 0\<close>, of q']
            \<open>path M q p \<and> target p q = q' \<and> p_io p = xy # io\<close> 
      by auto
    moreover have "p_io ?p = io"
      by (simp add: \<open>path M q p \<and> target p q = q' \<and> p_io p = xy # io\<close> map_tl)

    ultimately have "is_io_target M io (t_target ?t) q'"
      using Cons.IH by blast 

    then show "is_io_target M (xy#io) q q'"
      using \<open>path M q p \<and> target p q = q' \<and> p_io p = xy # io\<close> by auto
  qed

  ultimately show ?case
    by (metis (no_types, lifting))
qed








fun io_targets :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets M io q = {target p q | p . path M q p \<and> p_io p = io}"

fun io_targets' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets' M io q = set (map (\<lambda> p . target p q) (filter (\<lambda> p . p_io p = io) (paths_of_length M q (length io))))"

fun io_targets_list :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "io_targets_list M [] q = [q]" |
  "io_targets_list M (xy#io) q = (concat (map (io_targets_list M io) (map t_target (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy) (wf_transitions M)))))"


lemma set_concat_map_sublist :
  assumes "x \<in> set (concat (map f xs))"
  and     "set xs \<subseteq> set xs'"
shows "x \<in> set (concat (map f xs'))"
using assms by (induction xs) (auto)

lemma set_concat_map_elem :
  assumes "x \<in> set (concat (map f xs))"
  shows "\<exists> x' \<in> set xs . x \<in> set (f x')"
using assms by auto



lemma io_targets_from_list[code] :
  "io_targets M io q = set (io_targets_list M io q)"
proof -
  have "\<And>x. x \<in> io_targets M io q \<Longrightarrow> x \<in> set (io_targets_list M io q)"
  proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io)
    obtain p where "target p q = x" and "path M q p" and "p_io p = xy # io"
      using Cons.prems by fastforce 
    let ?t = "hd p"
    let ?p = "tl p"
    have "path M (t_target ?t) ?p"
      using \<open>p_io p = xy # io\<close> \<open>path M q p\<close> by force 
    moreover have "p_io ?p = io"
      using \<open>p_io p = xy # io\<close> by auto
    moreover have "target ?p (t_target ?t) = x"
      using \<open>target p q = x\<close> \<open>p_io p = xy # io\<close> by auto 
    ultimately have "x \<in> io_targets M io (t_target ?t)"
      by fastforce
    then have "x \<in> set (io_targets_list M io (t_target ?t))"
      using Cons.IH by auto
    then have "x \<in> set (concat (map (io_targets_list M io) [t_target ?t]))" 
      by auto
    moreover have "set [t_target ?t] \<subseteq> set (map t_target (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy) (wf_transitions M)))"
    proof -
      have "t_source ?t = q \<and> t_input ?t = fst xy \<and> t_output ?t = snd xy"
        using \<open>p_io p = xy # io\<close> \<open>path M q p\<close> by force
      moreover have "?t \<in> h M"
        using \<open>p_io p = xy # io\<close> \<open>path M q p\<close> by auto
      ultimately show ?thesis
        by auto 
    qed
    
    ultimately show ?case 
      unfolding io_targets_list.simps using set_concat_map_sublist[of x "io_targets_list M io" "[t_target ?t]"] by blast
  qed

  moreover have "\<And>x. x \<in> set (io_targets_list M io q) \<Longrightarrow> x \<in> io_targets M io q"
  proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons xy io) 
    then obtain t where "x \<in> set (io_targets_list M io (t_target t))"
                    and *: "t \<in> set (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy) (wf_transitions M))"
      by auto
    then have "x \<in> io_targets M io (t_target t)"
      using Cons.IH by auto
    then obtain p where "target p (t_target t) = x \<and> path M (t_target t) p \<and> p_io p = io"
      by auto
    moreover have "t \<in> h M \<and> t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy"
      using * by auto
    ultimately have "x = target (t#p) q" and "path M q (t#p)" and "p_io (t#p) = xy # io"
      using length_Cons by auto
      
    then show ?case 
      unfolding io_targets.simps
      by (metis (mono_tags, lifting) mem_Collect_eq) 
  qed

  ultimately show ?thesis by blast
qed 

(*
lemma io_targets_code[code] : "io_targets M io q = io_targets' M io q" 
proof -
  have "\<And> q' . q' \<in> io_targets M io q \<Longrightarrow> q' \<in> io_targets' M io q"
  proof -
    fix q' assume "q' \<in> io_targets M io q"
    then obtain p where "path M q p"
                    and "p_io p = io"
                    and "target p q = q'"
      by auto
    then have "length p = length io"
      by auto
    have "p \<in> set (paths_of_length M q (length io))"
      by (metis \<open>length p = length io\<close> \<open>path M q p\<close> paths_of_length_containment)
    
    then show "q' \<in> io_targets' M io q" 
      unfolding io_targets'.simps using \<open>p_io p = io\<close> \<open>target p q = q'\<close>
      by fastforce 
  qed

  moreover have "\<And> q' . q' \<in> io_targets' M io q \<Longrightarrow> q' \<in> io_targets M io q"
  proof -
    fix q' assume "q' \<in> io_targets' M io q"
    then obtain p where "path M q p"
                    and "p_io p = io"
                    and "target p q = q'"
      by auto
    then show "q' \<in> io_targets M io q" 
      unfolding io_targets.simps by blast
  qed

  ultimately show ?thesis by blast
qed
*)

value "io_targets M_ex [] (initial M_ex)"

lemma io_targets_nodes :
  assumes "q \<in> nodes M"
  shows "io_targets M io q \<subseteq> nodes M"
  using assms nodes_path by fastforce

lemma nodes_finite :
  "finite (nodes M)"
  by (metis (no_types) List.finite_set finite_insert nodes'.simps nodes_code) 

lemma io_targets_is_io_target :
  "io_targets M io q = {q' . is_io_target M io q q'}"
  using is_io_target_path[of M io q] by fastforce 


lemma observable_transition_unique :
  assumes "observable M"
      and "t \<in> h M" 
      and "t_source t = q" 
      and "t_input t = x" 
      and "t_output t = y"
    shows "\<exists>! t . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> t_output t = y"
  by (metis assms observable.elims(2) prod.expand)



lemma observable_path_unique :
  assumes "observable M"
  and     "path M q p"
  and     "path M q p'"
  and     "p_io p = p_io p'"
shows "p = p'"
proof -
  have "length p = length p'"
    using assms(4) map_eq_imp_length_eq by blast 
  then show ?thesis
  using \<open>p_io p = p_io p'\<close> \<open>path M q p\<close> \<open>path M q p'\<close> proof (induction p p' arbitrary: q rule: list_induct2)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs y ys)
    then have *: "x \<in> h M \<and> y \<in> h M \<and> t_source x = t_source y \<and> t_input x = t_input y \<and> t_output x = t_output y" 
      by auto
    then have "t_target x = t_target y" 
      using assms(1) observable.elims(2) by blast 
    then have "x = y"
      by (simp add: "*" prod.expand) 
      

    have "p_io xs = p_io ys" 
      using Cons by auto

    moreover have "path M (t_target x) xs" 
      using Cons by auto
    moreover have "path M (t_target x) ys"
      using Cons \<open>t_target x = t_target y\<close> by auto
    ultimately have "xs = ys" 
      using Cons by auto

    then show ?case 
      using \<open>x = y\<close> by simp
  qed
qed

lemma observable_io_targets : 
  assumes "observable M"
  and "io \<in> LS M q"
obtains q'
where "io_targets M io q = {q'}"
proof -

  obtain p where "path M q p" and "p_io p = io" 
    using assms(2) by auto 
  then have "target p q \<in> io_targets M io q"
    by auto   

  have "\<exists> q' . io_targets M io q = {q'}"
  proof (rule ccontr)
    assume "\<nexists>q'. io_targets M io q = {q'}"
    then have "\<exists> q' . q' \<noteq> target p q \<and> q' \<in> io_targets M io q"
      by (metis \<open>target p q \<in> io_targets M io q\<close> empty_Collect_eq io_targets_is_io_target is_singletonI' is_singleton_def mem_Collect_eq) 
    then obtain q' where "q' \<noteq> target p q" and "q' \<in> io_targets M io q" 
      by blast
    then obtain p' where "path M q p'" and "target p' q = q'" and "p_io p' = io"
      by auto 
    then have "p_io p = p_io p'" 
      using \<open>p_io p = io\<close> by simp
    then have "p = p'"
      using observable_path_unique[OF assms(1) \<open>path M q p\<close> \<open>path M q p'\<close>] by simp
    then show "False"
      using \<open>q' \<noteq> target p q\<close> \<open>target p' q = q'\<close> by auto
  qed

  then show ?thesis using that by blast
qed



    


fun minimal :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> nodes M . \<forall> q' \<in> nodes M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"










lemma distinct_path_ob :
  assumes "reachable M q1 q2"
  obtains p where "path M q1 p"
              and "target p q1 = q2"
              and "distinct (visited_states q1 p)"
proof -
  obtain p' where "path M q1 p'" and "target p' q1 = q2"
    using assms by (meson path_reachable) 
  then obtain p where "path M q1 p"
                  and "target p q1 = q2"
                  and "distinct (visited_states q1 p)"
    using distinct_path_from_nondistinct_path[OF \<open>path M q1 p'\<close>]
    by metis
  then show ?thesis using that by blast
qed


lemma visited_states_are_nodes :
  assumes "q1 \<in> nodes M"
      and "path M q1 p"
  shows "set (visited_states q1 p) \<subseteq> nodes M"
  by (metis assms(1) assms(2) nodes_path path_prefix subsetI visited_states_prefix)



lemma distinct_path_length_reachable :
  assumes "reachable M q1 q2"
  and     "q1 \<in> nodes M"
  obtains p where "path M q1 p"
              and "target p q1 = q2"
              and "length p < size M"
proof -
  obtain p where "path M q1 p"
             and "target p q1 = q2"
             and "distinct (visited_states q1 p)"
    using distinct_path_ob[OF assms(1)] by blast

  have "set (visited_states q1 p) \<subseteq> nodes M"
    using visited_states_are_nodes
    by (metis \<open>path M q1 p\<close> assms(2))
  then have "length (visited_states q1 p) \<le> size M"
    using nodes_finite
    by (metis \<open>distinct (visited_states q1 p)\<close> card_mono distinct_card size_def) 
  then have "length p < size M"
    by simp 

  show ?thesis
    using \<open>length p < size M\<close> \<open>path M q1 p\<close> \<open>target p q1 = q2\<close> that by blast
qed

lemma reachable_path : 
  "reachable M q1 q2 \<longleftrightarrow> (\<exists> p . path M q1 p \<and> target p q1 = q2)" 
proof
  show "reachable M q1 q2 \<Longrightarrow> \<exists>p. path M q1 p \<and> target p q1 = q2"
    by (meson path_reachable) 
  show "\<exists>p. path M q1 p \<and> target p q1 = q2 \<Longrightarrow> reachable M q1 q2"
  proof -
    assume "\<exists>p. path M q1 p \<and> target p q1 = q2"
    then obtain p where "path M q1 p" and "target p q1 = q2"
      by auto
    then show "reachable M q1 q2"
    proof (induction p arbitrary: q1 rule: list.induct)
      case Nil
      then show ?case by auto
    next
      case (Cons t ts)
      then have "path M (t_target t) ts" and "target ts (t_target t) = q2" by auto
      then have "reachable M (t_target t) q2" using Cons.IH by auto

      have "t \<in> h M" using Cons by auto
      moreover have "t_source t = q1" using Cons by auto
      ultimately show ?case 
        using reachable_next'[OF \<open>reachable M (t_target t) q2\<close>] by auto
    qed
  qed
qed

lemma distinct_path_length :
  assumes "path M q p"
  and     "q \<in> nodes M"
obtains p' where "path M q p'"
             and "target p' q = target p q"
             and "length p' < size M"
  by (meson assms distinct_path_length_reachable reachable_path) 



(* function to retrieve a single io_target *)
abbreviation "io_target M io q \<equiv> hd (io_targets_list M io q)"

lemma observable_first_io_target :
  assumes "observable M"
  and     "io \<in> LS M q"
shows "io_targets M io q = {io_target M io q}"
  by (metis assms insert_not_empty io_targets_from_list list.set(1) list.set_sel(1) observable_io_targets singletonD)

lemma observable_path_io_target : 
  assumes "observable M"
  and     "path M q p"
shows "target p q = io_target M (p_io p) q"
proof -
  have "target p q \<in> io_targets M (p_io p) q"
    using assms(2) by auto
  then show ?thesis using assms(1) observable_first_io_target
    by (metis (mono_tags, lifting) LS.simps assms(2) mem_Collect_eq singletonD) 
qed






fun is_io_reduction_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state A a B b = (LS A a \<subseteq> LS B b)"

abbreviation "is_io_reduction A B \<equiv> is_io_reduction_state A (initial A) B (initial B)" 
notation 
  is_io_reduction ("_ \<preceq> _")


fun is_io_reduction_state_on_inputs :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> Input list set \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state_on_inputs A a U B b = (LS\<^sub>i\<^sub>n A a U \<subseteq> LS\<^sub>i\<^sub>n B b U)"

abbreviation "is_io_reduction_on_inputs A U B \<equiv> is_io_reduction_state_on_inputs A (initial A) U B (initial B)" 
notation 
  is_io_reduction_on_inputs ("_ \<preceq>\<lbrakk>_\<rbrakk> _")
  
(* extends Petrenko's definition to explicitly require same inputs and outputs *)
fun is_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> set (transitions A) \<subseteq> set (transitions B) \<and> inputs A = inputs B \<and> outputs A = outputs B)"
  (* "is_submachine A B = (initial A = initial B \<and> h A \<subseteq> h B \<and> inputs A = inputs B \<and> outputs A = outputs B)" *)

lemma submachine_h :
  assumes "is_submachine A B"
  shows "h A \<subseteq> h B"
  using assms by auto

lemma submachine_path :
  assumes "is_submachine A B"
  and     "path A q p"
shows "path B q p"
  using assms by (induction p arbitrary: q; fastforce)

lemma submachine_nodes :
  assumes "is_submachine A B"
  shows "nodes A \<subseteq> nodes B"
  by (metis (no_types, lifting) assms is_submachine.elims(2) nodes.initial nodes_path path_to_nodes submachine_path subsetI) 

lemma submachine_reduction : 
  assumes "is_submachine A B"
  shows "is_io_reduction A B"
  using submachine_path[OF assms] assms by auto 

fun from_FSM :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme" where
  "from_FSM M q = \<lparr> initial = q, inputs = inputs M, outputs = outputs M, transitions = transitions M, \<dots> = FSM.more M \<rparr>"


fun r_compatible :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "r_compatible M q1 q2 = ((\<exists> S . completely_specified S \<and> is_submachine S (product (from_FSM M q1) (from_FSM M q2))))"

abbreviation "r_distinguishable M q1 q2 \<equiv> \<not> r_compatible M q1 q2"


fun r_distinguishable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"






lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M))"
  by auto

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  unfolding r_distinguishable_k.simps by fastforce



lemma io_targets_are_nodes :
  assumes "q' \<in> io_targets M io q"
      and "q \<in> nodes M"
  shows "q' \<in> nodes M"              
  by (meson assms contra_subsetD io_targets_nodes)
  


lemma completely_specified_io_targets : 
  assumes "completely_specified M"
  shows "\<forall> q \<in> io_targets M io (initial M) . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x"
  by (meson assms completely_specified_alt_def io_targets_are_nodes nodes.initial)


fun completely_specified_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "completely_specified_state M q = (\<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_states :
  "completely_specified M = (\<forall> q \<in> nodes M . completely_specified_state M q)"
  unfolding completely_specified.simps completely_specified_state.simps by force 

(* nodes that are reachable in at most k transitions *)
fun reachable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target p q | p . path M q p \<and> length p \<le> n}" 

lemma reachable_k_0 : "reachable_k M q 0 = {q}" 
  by auto

lemma reachable_k_nodes : "nodes M = reachable_k M (initial M) ( size M - 1)"
proof -
  have "\<And>q. q \<in> nodes M \<Longrightarrow> q \<in> reachable_k M (initial M) ( size M - 1)"
  proof -
    fix q assume "q \<in> nodes M"
    then obtain p where "path M (initial M) p" and "target p (initial M) = q"
      by (metis path_to_nodes) 
    then obtain p' where "path M (initial M) p'"
                     and "target p' (initial M) = target p (initial M)" 
                     and "length p' < size M"
      using distinct_path_length[of M "initial M" p] by auto
    then show "q \<in> reachable_k M (initial M) ( size M - 1)"
      using \<open>target p (initial M) = q\<close> list.size(3) mem_Collect_eq not_less_eq_eq reachable_k.simps by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( size M - 1) \<Longrightarrow> x \<in> nodes M"
    using nodes_path_initial by auto
  
  ultimately show ?thesis by blast
qed


lemma from_FSM_h :
  shows "h (from_FSM M q) = h M" 
  unfolding wf_transitions.simps is_wf_transition.simps by auto


lemma product_transition_split :
  assumes "t \<in> h (product A B)"
  obtains t1 t2 
  where "t1 \<in> h A \<and> t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
    and "t2 \<in> h B \<and> t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)"      
proof -
  have "t \<in> set (filter (is_wf_transition (product A B)) (transitions (product A B)))"
    using assms by (metis wf_transitions.simps) 
  then have "t \<in> set (transitions (product A B))"
    by (metis filter_set member_filter)    
  then have "t \<in> set (map (\<lambda>(t1, t2).
                      ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2))
               (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)
                 (cartesian_product_list (wf_transitions A) (wf_transitions B))))"
    by (metis product_simps(4) product_transitions.elims) 

  then obtain t1 t2 where "t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
                 and "(t1,t2) \<in> set (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)
                                      (cartesian_product_list (wf_transitions A) (wf_transitions B)))"
    by (metis (no_types, lifting) case_prod_beta' imageE prod.collapse set_map)

  then have *: "t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)" 
    by auto
  have **: "t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
    by (simp add: \<open>t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)\<close>)

  have "(t1,t2) \<in> h A \<times> h B"
    using \<open>(t1,t2) \<in> set (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2) (cartesian_product_list (wf_transitions A) (wf_transitions B)))\<close> cartesian_product_list_set[of "(wf_transitions A)" "(wf_transitions B)"] by auto
  then have "t1 \<in> h A" and "t2 \<in> h B" by auto

  have "t1 \<in> h A \<and> t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
   and "t2 \<in> h B \<and> t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)" 
    using \<open>t1 : h A\<close> * \<open>t2 \<in> h B\<close> ** by auto

  then show ?thesis
    using that by blast 
qed
    



lemma r_distinguishable_k_0_not_completely_specified :
  assumes "r_distinguishable_k M q1 q2 0"
  shows "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
proof -
  let ?F1 = "from_FSM M q1"
  let ?F2 = "from_FSM M q2"
  let ?P = "product ?F1 ?F2"

  obtain x where "x \<in> set (inputs M)" 
             and "\<not> (\<exists> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"  
    using assms by auto

  then have *: "\<not> (\<exists> t1 t2 . t1 \<in> h ?F1 \<and> t2 \<in> h ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    by auto
  
  have **: "\<not> (\<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x)"
  proof (rule ccontr)  
    assume "\<not> \<not> (\<exists>t\<in>h (product (from_FSM M q1) (from_FSM M q2)). t_source t = (q1, q2) \<and> t_input t = x)"
    then obtain t where "t \<in> h ?P" and "t_source t = (q1,q2)" and "t_input t = x"
      by blast 

    have "\<exists> t1 t2 . t1 \<in> h ?F1 \<and> t2 \<in> h ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
      using product_transition_split[OF \<open>t \<in> h ?P\<close>]
      by (metis \<open>t_input t = x\<close> \<open>t_source t = (q1, q2)\<close> fst_conv snd_conv)
    then show "False" 
      using * by auto
  qed

  moreover have "x \<in> set (inputs ?P)"
    using \<open>x \<in> set (inputs M)\<close> by auto

  ultimately have "\<not> completely_specified_state ?P (q1,q2)"
    by (meson completely_specified_state.elims(2))
    

  have "(q1,q2) = initial (product (from_FSM M q1) (from_FSM M q2))"
    by auto

  show ?thesis
    using \<open>(q1, q2) = initial (product (from_FSM M q1) (from_FSM M q2))\<close> \<open>\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1, q2)\<close> by presburger
  
qed
    

lemma complete_submachine_initial :
  assumes "is_submachine A B"
      and "completely_specified A"
  shows "completely_specified_state B (initial B)"
proof -
  have "initial B = initial A"
    using assms(1) by auto

  moreover have "completely_specified_state A (initial A)"
    using assms(2) by (meson completely_specified_states nodes.initial) 

  moreover have "inputs A = inputs B" and "h A \<subseteq> h B"
    using assms(1) by auto

  ultimately show ?thesis 
    unfolding completely_specified_state.simps by fastforce
qed
  


lemma from_FSM_path :
  assumes "q \<in> nodes M"
      and "path (from_FSM M q) q p"
  shows "path M q p"
using assms proof (induction p rule: rev_induct) 
  case Nil
  then show ?case by auto
next
  case (snoc t p)
  then show ?case by auto
qed

lemma from_FSM_nodes :
  assumes "q \<in> nodes M"
  shows "nodes (from_FSM M q) \<subseteq> nodes M"
  using from_FSM_path[OF assms]
  by (metis assms from_FSM.simps nodes_path path_to_nodes select_convs(1) subsetI) 

lemma submachine_from :
  assumes "is_submachine S M"
  shows "is_submachine (from_FSM S q) (from_FSM M q)"
  using assms by auto

lemma submachine_transition_product_from :
  assumes "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
      and "((q1,q2),x,y,(q1',q2')) \<in> h S"
 shows "is_submachine (from_FSM S (q1',q2')) (product (from_FSM M q1') (from_FSM M q2'))"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?P' = "(product (from_FSM M q1') (from_FSM M q2'))"
  let ?F = "(from_FSM S (q1',q2'))"  

  have "inputs (from_FSM M q1) = inputs (from_FSM M q1')"
   and "inputs (from_FSM M q2) = inputs (from_FSM M q2')"
   and "outputs (from_FSM M q1) = outputs (from_FSM M q1')"
   and "outputs (from_FSM M q2) = outputs (from_FSM M q2')"
    by auto

  have "transitions (from_FSM M q1) = transitions (from_FSM M q1')" and "transitions (from_FSM M q2) = transitions (from_FSM M q2')"
    by auto
  

  have "wf_transitions (from_FSM M q1) = wf_transitions (from_FSM M q1')" 
   and "wf_transitions (from_FSM M q2) = wf_transitions (from_FSM M q2')"
    unfolding wf_transitions.simps is_wf_transition.simps by auto
  
  then have "product_transitions (from_FSM M q1) (from_FSM M q2) = product_transitions (from_FSM M q1') (from_FSM M q2')" 
    unfolding product_transitions.simps  by fastforce
  then have **: "set (transitions ?F) \<subseteq> set (transitions ?P')"
    by (metis (no_types, lifting) assms(1) from_FSM.simps is_submachine.elims(2) product_simps(4) select_convs(4))

  (*
  then have "h ?P = h ?P'" 
    unfolding product.simps
    by (metis FSM3.product.simps \<open>inputs (from_FSM M q1) = inputs (from_FSM M q1')\<close> \<open>inputs (from_FSM M q2) = inputs (from_FSM M q2')\<close> \<open>outputs (from_FSM M q1) = outputs (from_FSM M q1')\<close> \<open>outputs (from_FSM M q2) = outputs (from_FSM M q2')\<close> from_FSM.simps from_FSM_h product_simps(2) product_simps(3) product_simps(4))  
  then have **: "h ?F \<subseteq> h ?P'"
    by (metis (no_types, lifting) assms(1) submachine_h from_FSM_h) 
  *)

  have *: "initial ?F = initial ?P'" 
    by auto

  have ***: "inputs ?F = inputs ?P'"
  proof -
    have "inputs (from_FSM M q1) @ inputs (from_FSM M q2) = inputs S"
      by (metis (no_types) assms(1) is_submachine.simps product_simps(2))
    then show ?thesis
      by (metis (no_types) from_FSM.simps product_simps(2) select_convs(2))
  qed 

  have ****: "outputs ?F = outputs ?P'"
  proof -
    have "outputs (from_FSM M q1) @ outputs (from_FSM M q2) = outputs S"
      by (metis (no_types) assms(1) is_submachine.simps product_simps(3))
    then show ?thesis
      by (metis (no_types) from_FSM.simps product_simps(3) select_convs(3))
  qed


  show "is_submachine ?F ?P'" 
    using is_submachine.simps[of ?F ?P'] * ** *** **** by blast 
qed




lemma submachine_transition_complete_product_from :
  assumes "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
      and "completely_specified S"
      and "((q1,q2),x,y,(q1',q2')) \<in> h S"
 shows "completely_specified (from_FSM S (q1',q2'))"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?P' = "(product (from_FSM M q1') (from_FSM M q2'))"
  let ?F = "(from_FSM S (q1',q2'))"  

  have "initial ?P = (q1,q2)"
    by auto
  then have "initial S = (q1,q2)" 
    using assms(1) by (metis is_submachine.simps) 
  then have "(q1',q2') \<in> nodes S"
    using assms(3)
    by (metis fst_conv nodes.initial nodes.step snd_conv) 
  then have "nodes ?F \<subseteq> nodes S"
    using from_FSM_nodes by metis
  moreover have "inputs ?F = inputs S"
    by auto
  ultimately show "completely_specified ?F"
    using assms(2) by auto 
qed



lemma from_FSM_product_inputs[simp] :
  "set (inputs (product (from_FSM M q1) (from_FSM M q2))) = set (inputs M)"
  unfolding product.simps from_FSM.simps by auto

lemma from_FSM_product_outputs[simp] :
  "set (outputs (product (from_FSM M q1) (from_FSM M q2))) = set (outputs M)"
  unfolding product.simps from_FSM.simps by auto

lemma from_FSM_product_initial[simp] : 
  "initial (product (from_FSM M q1) (from_FSM M q2)) = (q1,q2)" by auto

lemma from_FSM_transitions :
  "transitions (from_FSM M q) = transitions M" by auto 

lemma from_FSM_is_wf_transition :
  "is_wf_transition (from_FSM M q) t = is_wf_transition M t" by auto

lemma from_FSM_wf_transitions :
  "wf_transitions (from_FSM M q1) = wf_transitions (from_FSM M q2)" 
  using from_FSM_is_wf_transition
  by (metis filter_cong from_FSM_transitions wf_transitions.simps) 


lemma from_FSM_product_transitions : 
  "transitions (product (from_FSM M q1) (from_FSM M q2)) = transitions (product (from_FSM M q3) (from_FSM M q4))"
  unfolding product.simps product_transitions.simps using from_FSM_wf_transitions
  by (metis (no_types, lifting) select_convs(4)) 

lemma from_FSM_product_h : 
  "h (product (from_FSM M q1) (from_FSM M q2)) = h (product (from_FSM M q3) (from_FSM M q4))" (is "h ?P1 = h ?P2")
proof -
  have "\<And> t . is_wf_transition ?P1 t = is_wf_transition ?P2 t" by auto  
  then show ?thesis using from_FSM_product_transitions unfolding wf_transitions.simps
    by (metis filter_cong) 
qed
  
lemma h_subset_path :
  assumes "h A \<subseteq> h B"
  and "path A q p"
shows "path B q p"
  using assms by (induction p arbitrary: q; fastforce)

lemma h_equivalence_path :
  assumes "h A = h B"
  shows "path A q p \<longleftrightarrow> path B q p"
  by (metis assms h_subset_path subset_code(1))

lemma r_distinguishable_k_intersection_path : 
  assumes "\<not> r_distinguishable_k M q1 q2 k"
  and "length xs \<le> Suc k"
  and "set xs \<subseteq> set (inputs M)"
shows "\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs"
using assms proof (induction k arbitrary: q1 q2 xs)
  case 0
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  show ?case
  proof (cases "length xs < Suc 0")
    case True
    then show ?thesis by auto
  next
    case False
    
    have "completely_specified_state ?P (q1,q2)"
    proof (rule ccontr)
      assume "\<not> completely_specified_state ?P (q1,q2)"
      then obtain x where "x \<in> set (inputs ?P)"
                      and "\<not> (\<exists>t\<in>h ?P. t_source t = (q1, q2) \<and> t_input t = x)" 
        unfolding completely_specified_state.simps by blast
      then have "\<nexists>t1 t2.
                    t1 \<in> h M \<and>
                    t2 \<in> h M \<and>
                    t_source t1 = q1 \<and>
                    t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
        by (metis from_FSM_h fst_conv prod.exhaust_sel product_transition snd_conv)
      then have "r_distinguishable_k M q1 q2 0"
        using \<open>x \<in> set (inputs ?P)\<close> unfolding r_distinguishable_k.simps by auto
      then show "False"
        using "0.prems" by simp
    qed
    then have *: "\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
      unfolding completely_specified_state.simps by blast

    let ?x = "hd xs"
    have "xs = [?x]"
      using "0.prems"(2) False
      by (metis Suc_length_conv le_neq_implies_less length_0_conv list.sel(1)) 
    
    have "?x \<in> set (inputs M)"
      using "0.prems"(3) False by auto
    then obtain t where "t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = ?x"
      using * by (metis from_FSM_product_inputs) 
    then have "path ?P (q1,q2) [t] \<and> map fst (p_io [t]) = xs"
      by (metis (no_types, lifting) \<open>xs = [hd xs]\<close> fst_conv list.simps(8) list.simps(9) path.simps)
    then show ?thesis
      by (metis (no_types, lifting)) 
  qed
next
  case (Suc k)
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  
  

  show ?case 
  proof (cases "length xs \<le> Suc k")
    case True
    have "\<not> r_distinguishable_k M q1 q2 k" 
      using Suc.prems(1) by auto
    show ?thesis 
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M q1 q2 k\<close> True Suc.prems(3)] by assumption
  next
    case False
    then have "length xs = Suc (Suc k)"
      using Suc.prems(2) by auto
    
    then have "hd xs \<in> set (inputs M)"
      by (metis Suc.prems(3) contra_subsetD hd_in_set length_greater_0_conv zero_less_Suc) 
    have "set (tl xs) \<subseteq> set (inputs M)"
      by (metis \<open>length xs = Suc (Suc k)\<close> Suc.prems(3) dual_order.trans hd_Cons_tl length_0_conv nat.simps(3) set_subset_Cons)
    have "length (tl xs) \<le> Suc k"
      by (simp add: \<open>length xs = Suc (Suc k)\<close>) 

    let ?x = "hd xs"
    let ?xs = "tl xs"


    have "\<forall> x \<in> set (inputs M) . \<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
    proof 
      fix x assume "x \<in> set (inputs M)"
  
      have "\<not>(\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        using Suc.prems by auto
      then have "\<forall> x \<in> set (inputs M) . \<exists> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> \<not> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        by blast
      then obtain t1 t2 where *: "t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2" 
                          and **: "\<not> r_distinguishable_k M (t_target t1) (t_target t2) k"
        using \<open>x \<in> set (inputs M)\<close> by auto
      have ***: "((q1,q2), x, t_output t1, (t_target t1, t_target t2)) \<in> h ?P"
        by (metis (no_types) "*" from_FSM_h prod.collapse product_transition) 
      
      show "\<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
        by (metis "**" "***" fst_conv snd_conv)
    qed

    then obtain t where "t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = ?x" 
                    and "\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
      using \<open>?x \<in> set (inputs M)\<close> by blast 

    obtain p where "path (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))) ((fst (t_target t)), (snd (t_target t))) p \<and> map fst (p_io p) = ?xs"
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close> \<open>length (tl xs) \<le> Suc k\<close> \<open>set (tl xs) \<subseteq> set (inputs M)\<close>] by blast
    then have "path ?P (t_target t) p \<and> map fst (p_io p) = ?xs"
      by (metis (no_types, lifting) from_FSM_product_h h_equivalence_path prod.collapse)
      

    then have "path ?P (q1,q2) (t#p) \<and> map fst (p_io (t#p)) = xs"
      by (metis (no_types, lifting) \<open>length xs = Suc (Suc k)\<close> \<open>t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = hd xs\<close> cons fst_conv hd_Cons_tl length_greater_0_conv list.simps(9) zero_less_Suc)

    then show ?thesis
      by (metis (no_types, lifting)) 
  qed
qed



lemma r_distinguishable_k_intersection_paths : 
  assumes "\<not>(\<exists> k . r_distinguishable_k M q1 q2 k)"
  shows "\<forall> xs . set xs \<subseteq> set (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)"
proof (rule ccontr)
  assume "\<not> (\<forall> xs . set xs \<subseteq> set (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs))"
  then obtain xs where "set xs \<subseteq> set (inputs M)"
                   and "\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)" 
    by blast

  have "\<not> r_distinguishable_k M q1 q2 (length xs)"
    using assms by auto

  show "False" 
    using r_distinguishable_k_intersection_path[OF \<open>\<not> r_distinguishable_k M q1 q2 (length xs)\<close> _ \<open>set xs \<subseteq> set (inputs M)\<close>]
          \<open>\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)\<close> by fastforce
qed 
    

lemma filter_double :
  assumes "x \<in> set (filter P1 xs)"
  and     "P2 x"
shows "x \<in> set (filter P2 (filter P1 xs))"
  by (metis (no_types) assms(1) assms(2) filter_set member_filter)

lemma filter_list_set :
  assumes "x \<in> set xs"
  and     "P x"
shows "x \<in> set (filter P xs)"
  by (simp add: assms(1) assms(2))

lemma filter_list_set_not_contained :
  assumes "x \<in> set xs"
  and     "\<not> P x"
shows "x \<notin> set (filter P xs)"
  by (simp add: assms(1) assms(2))































fun completely_specified_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "completely_specified_k M q k = (\<forall> p . (path M q p \<and> length p \<le> k) \<longrightarrow> completely_specified_state M (target p q))"




lemma r_distinguishable_alt_def :
  "r_distinguishable M q1 q2 \<longleftrightarrow> (\<exists> k . r_distinguishable_k M q1 q2 k)"
proof 
  show "r_distinguishable M q1 q2 \<Longrightarrow> \<exists>k. r_distinguishable_k M q1 q2 k" 
  proof (rule ccontr)

    (* Proof sketch: if no k exists such that q1 and q2 are r(k)-distinguishable, then 
                     it is possible to construct a complete submachine of the product 
                     machine (product (from_FSM M q1) (from_FSM M q2)) by using only those
                     transitions in (product (from_FSM M q1) (from_FSM M q2)) that lead
                     from a pair of non r(0)-distinguishable states to a pair that is not
                     r(j)-distinguishable for any j. 
    *)


    assume "r_distinguishable M q1 q2"
    assume c_assm: "\<nexists>k. r_distinguishable_k M q1 q2 k"
  
    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    (* filter function to restrict transitions of ?P *)
    let ?f = "\<lambda> t . \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)"
    let ?ft = "filter ?f (transitions ?P)"
    (* resulting submachine of ?P *)
    let ?PC = "?P\<lparr> transitions := ?ft \<rparr>"   
  
  
    have h_ft : "h ?PC = { t \<in> h ?P . ?f t }"
    proof -
      have wf_eq: "\<And> t . is_wf_transition ?PC t = is_wf_transition ?P t"
        by (metis (no_types, lifting) FSM3.product.simps is_wf_transition.simps select_convs(2) select_convs(3) update_convs(4))
      have "transitions ?PC = ?ft"
          by (metis (mono_tags, lifting) select_convs(4) surjective update_convs(4))
  
      have "\<And> t . t \<in> h ?PC \<Longrightarrow> t \<in> h ?P \<and> ?f t"
        by (metis (no_types, lifting) \<open>transitions ?PC = ?ft\<close> filter_is_subset filter_list_set_not_contained product_simps(4) product_transitions_wf subsetCE wf_transitions.simps)
      moreover have "\<And> t . t \<in> h ?P \<and> ?f t \<Longrightarrow> t \<in> h ?PC"
      proof -
        fix t assume "t \<in> h ?P \<and> ?f t"
        then have "t \<in> set (transitions ?P)" and "is_wf_transition ?P t" 
          by (metis filter_set member_filter wf_transitions.simps)+
        have "(\<lambda> t . ?f t) t" 
          using \<open>t \<in> h ?P \<and> ?f t\<close> by blast
        have "t \<in> set ?ft"
          using filter_list_set[OF \<open>t \<in> set (transitions ?P)\<close>, of "(\<lambda> t . ?f t)", OF \<open>(\<lambda> t . ?f t) t\<close>] by assumption
        moreover have "is_wf_transition ?PC t"
          using  wf_eq \<open>is_wf_transition ?P t\<close> by blast
        moreover have "transitions ?PC = ?ft"
          by (metis (mono_tags, lifting) select_convs(4) surjective update_convs(4))
        ultimately have "t \<in> set (transitions ?PC)" and "is_wf_transition ?PC t" 
          by metis+
        show "t \<in> h ?PC" 
          unfolding wf_transitions.simps using filter_list_set[OF \<open>t \<in> set (transitions ?PC)\<close>, of "is_wf_transition ?PC", OF \<open>is_wf_transition ?PC t\<close>] by assumption
      qed
  
      ultimately show ?thesis by blast
    qed
  
    have nodes_non_r_d_k : "\<And> q . q \<in> nodes ?PC \<Longrightarrow> \<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
    proof -   
      fix q assume "q \<in> nodes ?PC"
      
      have "q = initial ?PC \<or> (\<exists> t \<in> h ?PC . q = t_target t)"
        by (metis (no_types, lifting) \<open>q \<in> nodes ?PC\<close> nodes.cases) 
      then have "q = (q1,q2) \<or> (\<exists> t \<in> h ?PC . q = t_target t)"
        by (metis (no_types, lifting) FSM3.product.simps from_FSM_product_initial select_convs(1) update_convs(4))
      
      show "\<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
      proof (cases "q = (q1,q2)")
        case True
        then show ?thesis using c_assm by auto
      next
        case False
        then obtain t where "t \<in> h ?PC" and "q = t_target t" using \<open>q = (q1,q2) \<or> (\<exists> t \<in> h ?PC . q = t_target t)\<close> by blast
        then show ?thesis
          using h_ft by blast 
      qed
    qed
  
  
    have "\<And> k q . q \<in> nodes ?PC \<Longrightarrow> completely_specified_state ?PC q"  
    proof -
      fix k q assume "q \<in> nodes ?PC"
      show "completely_specified_state ?PC q"
       proof (rule ccontr)
        assume "\<not> completely_specified_state ?PC q"
        then obtain x where "x \<in> set (inputs ?PC)"
                        and "\<not> (\<exists>t\<in>h ?PC. t_source t = q \<and> t_input t = x)" 
          unfolding completely_specified_state.simps by blast
  
        have "\<not> (\<exists>t\<in>h ?P. t_source t = q \<and> t_input t = x \<and> ?f t)"
          using h_ft \<open>\<not> (\<exists>t\<in>h ?PC. t_source t = q \<and> t_input t = x)\<close> mem_Collect_eq
          by blast
  
        then have *: "\<nexists>t1 t2.
                      t1 \<in> h M \<and>
                      t2 \<in> h M \<and>
                      t_source t1 = (fst q) \<and>
                      t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2
                      \<and> \<not> r_distinguishable_k M (fst q) (snd q) 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (t_target t1) (t_target t2) k)"
          by (metis from_FSM_h fst_conv prod.exhaust_sel product_transition snd_conv)
        
          
        
        have "\<exists> k . r_distinguishable_k M (fst q) (snd q) k"
        proof (cases "r_distinguishable_k M (fst q) (snd q) 0")
          case True
          then show ?thesis by blast
        next
          case False
          
  
          let ?tp = "{(t1,t2) | t1 t2 . t1 \<in> h M \<and>
                                         t2 \<in> h M \<and>
                                         t_source t1 = (fst q) \<and>
                                         t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
  
          have "finite ?tp"
          proof -
            have "finite (h M)" by auto
            then have "finite (h M \<times> h M)" by auto
            moreover have "?tp \<subseteq> (h M \<times> h M)" by blast
            ultimately  show ?thesis by (simp add: finite_subset) 
          qed
  
          have k_ex : "\<forall> t \<in> ?tp . \<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'"
          proof 
            fix t assume "t \<in> ?tp"
  
            let ?t1 = "fst t"
            let ?t2 = "snd t"
            from \<open>t \<in> ?tp\<close> have "?t1 \<in> h M \<and>
                                 ?t2 \<in> h M \<and>
                                 t_source ?t1 = (fst q) \<and>
                                 t_source ?t2 = (snd q) \<and> t_input ?t1 = x \<and> t_input ?t2 = x \<and> t_output ?t1 = t_output ?t2" by auto
            then obtain k where "r_distinguishable_k M (t_target ?t1) (t_target ?t2) k"
              using False * by blast
            then have "\<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target ?t1) (t_target ?t2) k'"
              using nat_induct_at_least by fastforce
            then show "\<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'" by auto
          qed
  
            
          
          then obtain fk where fk_def : "\<forall> t \<in> ?tp . \<forall> k' . k' \<ge> fk t \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'" 
          proof -
            have "\<exists> f . \<forall> t \<in> ?tp . \<forall> k' . k' \<ge> f t \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'"
            proof 
              let ?fk = "\<lambda> t . SOME k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'"
              show "\<forall> t \<in> ?tp . \<forall> k' . k' \<ge> ?fk t \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'"
              proof 
                fix t assume "t \<in> ?tp"
                then have "\<exists> k . (\<lambda> k . (\<forall> k'. k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k')) k"
                  using k_ex by blast
                then have "(\<lambda> k . (\<forall> k'. k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k')) (?fk t)"
                  using someI_ex[of "(\<lambda> k . (\<forall> k'. k' \<ge> k \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'))"] by blast
                then show "\<forall> k' . k' \<ge> ?fk t \<longrightarrow> r_distinguishable_k M (t_target (fst t)) (t_target (snd t)) k'"
                  by blast
              qed
            qed
            then show ?thesis using that by blast
          qed
  
          obtain kMax where "\<forall> t \<in> ?tp . fk t \<le> kMax"
          proof -
            let ?kMax = "Max (image fk ?tp)"
            have "\<forall> t \<in> ?tp . fk t \<le> ?kMax"
              using \<open>finite ?tp\<close> by auto
            then show ?thesis using that by blast
          qed
  
          then have "\<forall> (t1,t2) \<in> ?tp . r_distinguishable_k M (t_target t1) (t_target t2) kMax"
            using fk_def by (metis (no_types, lifting) prod.case_eq_if) 
  
          then have "\<And> t1 t2.
                      (t1 \<in> h M \<and>
                       t2 \<in> h M \<and>
                       t_source t1 = (fst q) \<and>
                       t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)
                      \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) kMax"
            using * by blast
          then have "r_distinguishable_k M (fst q) (snd q) (Suc kMax)"
            unfolding r_distinguishable_k.simps
            by (metis (no_types, lifting) FSM3.product.simps \<open>x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>t. \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> (\<nexists>k. r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>))\<close> from_FSM_product_inputs select_convs(2) update_convs(4)) 
          then show ?thesis by blast  
        qed
  
        then show "False" using nodes_non_r_d_k[OF \<open>q \<in> nodes ?PC\<close>] by blast
      qed
    qed
  
    then have "completely_specified ?PC"
      using completely_specified_states by blast 
  
    moreover have "is_submachine ?PC ?P"
      unfolding is_submachine.simps
    proof -
      have f1: "\<forall>f fa. outputs (transitions_update fa (f::('a \<times> 'a, 'b) FSM_scheme)) = outputs f"
        by force
      have f2: "\<forall>f fa. inputs (transitions_update fa (f::('a \<times> 'a, 'b) FSM_scheme)) = inputs f"
        by auto
      have f3: "\<forall>f fa. initial (transitions_update fa (f::('a \<times> 'a, 'b) FSM_scheme)) = initial f"
        by auto
      have "\<forall>f fa. transitions (transitions_update fa (f::('a \<times> 'a, 'b) FSM_scheme)) = fa (transitions f)"
        by simp
      then show "initial (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>p. \<not> r_distinguishable_k M (fst (t_source p)) (snd (t_source p)) 0 \<and> \<not> Ex (r_distinguishable_k M (fst (t_target p)) (snd (t_target p)))) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>) = initial (product (from_FSM M q1) (from_FSM M q2)) \<and> set (transitions (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>p. \<not> r_distinguishable_k M (fst (t_source p)) (snd (t_source p)) 0 \<and> \<not> Ex (r_distinguishable_k M (fst (t_target p)) (snd (t_target p)))) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>)) \<subseteq> set (transitions (product (from_FSM M q1) (from_FSM M q2))) \<and> inputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>p. \<not> r_distinguishable_k M (fst (t_source p)) (snd (t_source p)) 0 \<and> \<not> Ex (r_distinguishable_k M (fst (t_target p)) (snd (t_target p)))) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>) = inputs (product (from_FSM M q1) (from_FSM M q2)) \<and> outputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>p. \<not> r_distinguishable_k M (fst (t_source p)) (snd (t_source p)) 0 \<and> \<not> Ex (r_distinguishable_k M (fst (t_target p)) (snd (t_target p)))) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>) = outputs (product (from_FSM M q1) (from_FSM M q2))"
        using f3 f2 f1 by (metis filter_is_subset)
    qed
  
    ultimately have "r_compatible M q1 q2"
      unfolding r_compatible.simps by blast
    then show "False" using \<open>r_distinguishable M q1 q2\<close>
      by blast 
  qed

  show "\<exists>k. r_distinguishable_k M q1 q2 k \<Longrightarrow> r_distinguishable M q1 q2"
  proof (rule ccontr)
    assume *: "\<not> r_distinguishable M q1 q2"
    assume **: "\<exists>k. r_distinguishable_k M q1 q2 k"        
    then obtain k where "r_distinguishable_k M q1 q2 k" by auto
    then show "False"
    using * proof (induction k arbitrary: q1 q2)
      case 0
      then obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                      and "completely_specified S"
        by (meson r_compatible.elims(2))      
      then have "completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
        using complete_submachine_initial by metis
      then show "False" using r_distinguishable_k_0_not_completely_specified[OF "0.prems"(1)] by metis
    next
      case (Suc k)
      then show "False" 
      proof (cases "r_distinguishable_k M q1 q2 k")
        case True
        then show ?thesis 
          using Suc.IH Suc.prems(2) by blast 
      next
        case False
        then obtain x where "x \<in> set (inputs M)"
                        and "\<forall>y q1' q2'. (q1, x, y, q1') \<in> h M \<and> (q2, x, y, q2') \<in> h M \<longrightarrow> r_distinguishable_k M q1' q2' k"
          using Suc.prems(1) by fastforce

        from Suc obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                            and "completely_specified S"
          by (meson r_compatible.elims(2)) 

        have "x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2)))"
          using \<open>x \<in> set (inputs M)\<close> by auto
        then have "x \<in> set (inputs S)" 
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis is_submachine.elims(2)) 

        moreover have "initial S = (q1,q2)"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis from_FSM_product_initial is_submachine.elims(2)) 
        ultimately obtain y q1' q2' where "((q1,q2),x,y,(q1',q2')) \<in> h S"
          using \<open>completely_specified S\<close> using nodes.initial by fastforce 
        then have "((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          using submachine_h by blast
        then have "(q1, x, y, q1') \<in> h M" and "(q2, x, y, q2') \<in> h M"
          by (metis (no_types) \<open>((q1, q2), x, y, q1', q2') \<in> h (product (from_FSM M q1) (from_FSM M q2))\<close> from_FSM_h product_transition)+ 
        then have "r_distinguishable_k M q1' q2' k" 
          using \<open>\<forall>y q1' q2'. (q1, x, y, q1') \<in> h M \<and> (q2, x, y, q2') \<in> h M \<longrightarrow> r_distinguishable_k M q1' q2' k\<close> by blast
        then have "r_distinguishable M q1' q2'"
          using Suc.IH by blast 

        moreover have "\<exists> S' . completely_specified S' \<and> is_submachine S' (product (from_FSM M q1') (from_FSM M q2'))"
          using \<open>((q1,q2),x,y,(q1',q2')) \<in> h S\<close>
          by (meson \<open>completely_specified S\<close> \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close> submachine_transition_complete_product_from submachine_transition_product_from) 

        ultimately show "False" unfolding r_compatible.simps by blast
      qed
    qed
  qed
qed



(* definitely-reachable & state preambles *)

(* TODO: use actual definition
fun definitely_reachable :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<forall> S . completely_specified S \<and> is_submachine S M \<longrightarrow> q \<in> nodes S)"

lemma definitely_reachable_alt_def :
  "definitely_reachable M q = (\<exists> S . is_preamble S M q)"
  sorry
*)

fun is_preamble :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_preamble S M q = (acyclic S \<and> single_input S \<and> is_submachine S M \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h S))))"

fun definitely_reachable :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<exists> S . is_preamble S M q)"


(* variation closed under prefix relation *)
fun is_preamble_set :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "is_preamble_set M q P = (
    P \<subseteq> L M
    \<and> (\<forall> p . (path M (initial M) p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states (initial M) p))
    \<and> (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)
    \<and> (\<forall> xys xy y . (xys@[xy] \<in> P \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> P)
    \<and> (\<forall> xys \<in> P . ((io_target M xys (initial M) = q 
                     \<and> \<not> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
                   \<or> (\<not> io_target M xys (initial M) = q 
                        \<and> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
    \<and> (\<exists> xys \<in> P . io_target M xys (initial M) = q)
    \<and> (\<forall> xys1 xys2 . xys1@xys2 \<in> P \<longrightarrow> xys1 \<in> P)
  )"   

lemma preamble_set_contains_empty_sequence :
  assumes "is_preamble_set M q P"
  shows "[] \<in> P" 
proof -
  from assms obtain xys where "xys \<in> P \<and> io_target M xys (initial M) = q" unfolding is_preamble_set.simps by blast
  then have "[] @ xys \<in> P" by auto
  then show ?thesis using assms unfolding is_preamble_set.simps by blast
qed

lemma submachine_language :
  assumes "is_submachine S M"
  shows "L S \<subseteq> L M"
proof - (* TODO: format auto-generated code *)
obtain pps :: "(integer \<times> integer) list set \<Rightarrow> (integer \<times> integer) list set \<Rightarrow> (integer \<times> integer) list" where
  f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
  by moura
  have f2: "initial S = initial M \<and> set (transitions S) \<subseteq> set (transitions M) \<and> inputs S = inputs M \<and> outputs S = outputs M"
    using assms is_submachine.simps by blast
  obtain ppsa :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
    f3: "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (ppsa x0 x1 x2) \<and> path x2 x1 (ppsa x0 x1 x2))"
by moura
  { assume "path M (initial M) (ppsa (pps (L M) (L S)) (initial M) S)"
    moreover
    { assume "\<exists>ps. pps (L M) (L S) = p_io ps \<and> path M (initial M) ps"
      then have "pps (L M) (L S) \<notin> L S \<or> pps (L M) (L S) \<in> L M"
        by simp
      then have ?thesis
        using f1 by (meson subsetI) }
    ultimately have "L S \<subseteq> L M \<or> pps (L M) (L S) \<noteq> p_io (ppsa (pps (L M) (L S)) (initial M) S) \<or> \<not> path S (initial M) (ppsa (pps (L M) (L S)) (initial M) S)"
      by blast }
  moreover
  { assume "pps (L M) (L S) \<noteq> p_io (ppsa (pps (L M) (L S)) (initial M) S) \<or> \<not> path S (initial M) (ppsa (pps (L M) (L S)) (initial M) S)"
    then have "\<nexists>ps. pps (L M) (L S) = p_io ps \<and> path S (initial M) ps"
      using f3 by presburger
    then have "\<nexists>ps. pps (L M) (L S) = p_io ps \<and> path S (initial S) ps"
using f2 by presburger
  then have "pps (L M) (L S) \<notin> {p_io ps |ps. path S (initial S) ps}"
    by blast
  then have ?thesis
    using f1 by (metis (no_types) LS.simps subsetI) }
  ultimately show ?thesis
    by (meson assms submachine_path)
qed


lemma submachine_observable :
  assumes "is_submachine S M"
  and     "observable M"
shows "observable S"
  using assms unfolding is_submachine.simps observable.simps
  by (meson assms(1) contra_subsetD submachine_h)

lemma language_prefix : 
  assumes "io1@io2 \<in> LS M q"
  shows "io1 \<in> LS M q"
proof -
  obtain p where "path M q p" and "p_io p = io1@io2" 
    using assms by auto
  let ?tp = "take (length io1) p"
  have "path M q ?tp"
    by (metis (no_types) \<open>path M q p\<close> append_take_drop_id path_prefix) 
  moreover have "p_io ?tp = io1"
    using \<open>p_io p = io1@io2\<close> by (metis append_eq_conv_conj take_map) 
  ultimately show ?thesis
    by force 
qed

lemma observable_submachine_io_target :
  assumes "observable M"
  and     "is_submachine S M"
  and     "io \<in> L S"
shows "io_target S io (initial S) = io_target M io (initial M)"
proof -
  obtain pps :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
    "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (pps x0 x1 x2) \<and> path x2 x1 (pps x0 x1 x2))"
    by moura
  then have f1: "io = p_io (pps io (initial M) S) \<and> path S (initial M) (pps io (initial M) S)"
    using assms(2) assms(3) by force
  have f2: "\<forall>f a ps. \<not> observable (f::('a, 'b) FSM_scheme) \<or> \<not> path f a ps \<or> target ps a = io_target f (p_io ps) a"
    by (metis (no_types) observable_path_io_target)
  then have f3: "target (pps io (initial M) S) (initial M) = io_target S (p_io (pps io (initial M) S)) (initial M)"
    using f1 assms(1) assms(2) submachine_observable by blast
  have "target (pps io (initial M) S) (initial M) = io_target M (p_io (pps io (initial M) S)) (initial M)"
    using f2 f1 by (meson assms(1) assms(2) submachine_path)
  then show ?thesis
    using f3 f1 assms(2) by auto
qed



(* the language of a preamble is a preamble-set *)
lemma preamble_has_preamble_set :
  assumes "observable M"
  and     "is_preamble S M q"
  shows "is_preamble_set M q (L S)"
proof (rule ccontr)
  assume "\<not> is_preamble_set M q (L S)"
  then consider
    (f1) "\<not> (L S \<subseteq> L M)" |
    (f2) "\<not> (\<forall> p . (path M (initial M) p \<and> p_io p \<in> L S) \<longrightarrow> distinct (visited_states (initial M) p))" |
    (f3) "\<not> (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> L S \<and> xys2@[xy2] \<in> L S \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)" |
    (f4) "\<not> (\<forall> xys xy y . (xys@[xy] \<in> L S \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> L S)" |
    (f5) "\<not> (\<forall> xys \<in> L S . ((io_target M xys (initial M) = q 
                     \<and> \<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))
                   \<or> (\<not> io_target M xys (initial M) = q 
                        \<and> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))" |
    (f6) "\<not> (\<exists> xys \<in> L S . io_target M xys (initial M) = q)" |
    (f7) "\<not> (\<forall> xys1 xys2 . xys1@xys2 \<in> L S \<longrightarrow> xys1 \<in> L S)"
    unfolding is_preamble_set.simps by blast
  then show "False"
  proof cases
    case f1 (* violates submachine property *)
    moreover have "L S \<subseteq> L M"  
      using assms(2) unfolding is_preamble.simps by (metis submachine_language)
    ultimately show "False" by simp 
  next
    case f2 (* violates acyclicness property (for observable M) *)
    then obtain p where "path M (initial M) p" and "p_io p \<in> L S" and "\<not> distinct (visited_states (initial M) p)"
      by blast
    from \<open>p_io p \<in> L S\<close> obtain p' where "path S (initial S) p'" and "p_io p' = p_io p"
      using LS.elims by auto 
    then have "path M (initial M) p'" 
      using assms(2) unfolding is_preamble.simps
      by (metis is_submachine.elims(2) submachine_path) 

    have "observable S"  
      using assms unfolding is_preamble.simps by (metis submachine_observable)
    have "p' = p"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) p\<close> \<open>path M (initial M) p'\<close>] using \<open>p_io p' = p_io p\<close> by auto
    then have "\<not> distinct (visited_states (initial S) p')"
      using \<open>\<not> distinct (visited_states (initial M) p)\<close> assms(2) unfolding is_preamble.simps is_submachine.simps by simp
    then show "False"
      using assms(2) unfolding is_preamble.simps by (meson \<open>path S (initial S) p'\<close> acyclic.elims(2))
  next
    case f3 (* violates single-input property (for observable M) *)
    then obtain xys1 xys2 xy1 xy2 where "xys1@[xy1] \<in> L S" 
                                    and "xys2@[xy2] \<in> L S" 
                                    and "io_target M xys1 (initial M) = io_target M xys2 (initial M)"
                                    and "fst xy1 \<noteq> fst xy2" 
      by blast

    then obtain p1 p2 where "path S (initial S) p1" and "p_io p1 = xys1@[xy1]"
                        and "path S (initial S) p2" and "p_io p2 = xys2@[xy2]" 
      by auto
    let ?hp1 = "butlast p1"
    let ?hp2 = "butlast p2"
    let ?t1 = "last p1"
    let ?t2 = "last p2"

    have "path S (initial S) (?hp1@[?t1])" and "p_io (?hp1@[?t1]) = xys1@[xy1]"
      using \<open>path S (initial S) p1\<close> \<open>p_io p1 = xys1@[xy1]\<close> by (metis (no_types, lifting) Nil_is_map_conv snoc_eq_iff_butlast)+
    then have "path S (initial S) ?hp1" by blast
    then have "path M (initial M) ?hp1"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
    then have "target ?hp1 (initial M) = io_target M xys1 (initial M)"
      by (metis (mono_tags, lifting) \<open>p_io p1 = xys1 @ [xy1]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)
      

    have "path S (initial S) (?hp2@[?t2])" and "p_io (?hp2@[?t2]) = xys2@[xy2]"
      using \<open>path S (initial S) p2\<close> \<open>p_io p2 = xys2@[xy2]\<close> by (metis (no_types, lifting) Nil_is_map_conv snoc_eq_iff_butlast)+
    then have "path S (initial S) ?hp2" by blast
    then have "path M (initial M) ?hp2"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
    then have "target ?hp2 (initial M) = io_target M xys2 (initial M)"
      by (metis (mono_tags, lifting) \<open>p_io p2 = xys2 @ [xy2]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)

    have "target ?hp1 (initial M) = target ?hp2 (initial M)"
      using \<open>io_target M xys1 (initial M) = io_target M xys2 (initial M)\<close> \<open>target (butlast p1) (initial M) = io_target M xys1 (initial M)\<close> \<open>target (butlast p2) (initial M) = io_target M xys2 (initial M)\<close> by presburger
    moreover have "t_source ?t1 = target ?hp1 (initial M)"
      by (metis (no_types) \<open>path S (initial S) (butlast p1 @ [last p1])\<close> assms(2) is_preamble.simps is_submachine.elims(2) path_append_elim path_cons_elim)
    moreover have "t_source ?t2 = target ?hp2 (initial M)"
      by (metis (no_types) \<open>path S (initial S) (butlast p2 @ [last p2])\<close> assms(2) is_preamble.simps is_submachine.elims(2) path_append_elim path_cons_elim)
    ultimately have "t_source ?t1 = t_source ?t2" by auto
    moreover have "?t1 \<in> h S"
      by (metis (no_types, lifting) \<open>path S (initial S) (butlast p1 @ [last p1])\<close> assms(2) contra_subsetD is_preamble.simps is_submachine.elims(2) last_in_set path_h snoc_eq_iff_butlast)
    moreover have "?t2 \<in> h S"
      by (metis (no_types, lifting) \<open>path S (initial S) (butlast p2 @ [last p2])\<close> assms(2) contra_subsetD is_preamble.simps is_submachine.elims(2) last_in_set path_h snoc_eq_iff_butlast)
    moreover have "t_source ?t1 \<in> nodes S"
      by (metis (no_types, hide_lams) \<open>path S (initial S) (butlast p1)\<close> \<open>t_source (last p1) = target (butlast p1) (initial M)\<close> assms(2) is_preamble.simps is_submachine.elims(2) nodes.initial nodes_path)    
    ultimately have "t_input ?t1 = t_input ?t2"
      using assms(2) unfolding is_preamble.simps single_input.simps by blast
      
    then have "fst xy1 = fst xy2"
      using \<open>p_io (butlast p1 @ [last p1]) = xys1 @ [xy1]\<close> \<open>p_io (butlast p2 @ [last p2]) = xys2 @ [xy2]\<close> by auto
    then show "False" using \<open>fst xy1 \<noteq> fst xy2\<close> by simp
  next
    case f4 (* misses transition in M (for observable M) *)
    then obtain xys xy y where "xys@[xy] \<in> L S" and "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))" and  "\<not> xys@[(fst xy,y)] \<in> L S"
      by blast

    then obtain p where "path S (initial S) p" and "p_io p = xys@[xy]" 
      by auto
    let ?hp = "butlast p"
    let ?t = "last p"
    have "path S (initial S) ?hp" 
      using \<open>path S (initial S) p\<close>
      by (metis append_butlast_last_id butlast.simps(1) path_prefix) 
    then have "path M (initial M) ?hp"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)

    have "p_io ?hp = xys"
      using \<open>p_io p = xys@[xy]\<close>
      by (simp add: map_butlast)

    have "?t \<in> h S" 
      by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys @ [xy]\<close> \<open>path S (initial S) p\<close> contra_subsetD last_in_set path_h snoc_eq_iff_butlast) 
    have "fst xy \<in> set (inputs S)" and "t_source ?t = target ?hp (initial S) \<and> t_input ?t = fst xy"
      by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys @ [xy]\<close> \<open>path S (initial S) p\<close> fst_conv last_map path_cons_elim path_suffix snoc_eq_iff_butlast)+
      
    have "target ?hp (initial M) \<in> nodes S"
      by (metis \<open>path S (initial S) (butlast p)\<close> assms(2) is_preamble.simps is_submachine.elims(2) nodes_path_initial) 
      
    have "target ?hp (initial M) = io_target M xys (initial M)"
      using observable_path_io_target[OF assms(1) \<open>path M (initial M) ?hp\<close>] \<open>p_io ?hp = xys\<close> by auto

    obtain tf where "tf \<in> h M" and "t_source tf = io_target M xys (initial M)" and "t_input tf = fst xy" and "t_output tf = y"
      using \<open>[(fst xy, y)] \<in> LS M (io_target M xys (initial M))\<close> by auto
    
    have "\<not> tf \<in> h S"
    proof 
      assume "tf \<in> h S"
      moreover have "t_source tf = target ?hp (initial S)"
        using \<open>t_source tf = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) = io_target M xys (initial M)\<close> assms(2) by auto
      ultimately have "path S (initial S) (?hp@[tf])"
        by (metis \<open>path S (initial S) (butlast p)\<close> cons nil path_append)
      then have "xys@[(fst xy,y)] \<in> L S"
      proof -
        have "xys @ [(fst xy, y)] = p_io (butlast p @ [tf])"
          by (simp add: \<open>p_io (butlast p) = xys\<close> \<open>t_input tf = fst xy\<close> \<open>t_output tf = y\<close>)
        then have "\<exists>ps. xys @ [(fst xy, y)] = p_io ps \<and> path S (initial S) ps"
          by (meson \<open>path S (initial S) (butlast p @ [tf])\<close>)
        then show ?thesis
          by simp
      qed
        
      then show "False" using  \<open>\<not> xys@[(fst xy,y)] \<in> L S\<close> by auto
    qed

    show "False" using assms(2) unfolding is_preamble.simps
      by (metis (no_types, lifting) \<open>fst xy \<in> set (inputs S)\<close> \<open>last p \<in> h S\<close> \<open>t_input tf = fst xy\<close> \<open>t_source (last p) = target (butlast p) (initial S) \<and> t_input (last p) = fst xy\<close> \<open>t_source tf = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) \<in> nodes S\<close> \<open>tf \<in> h M\<close> \<open>tf \<notin> h S\<close> is_submachine.elims(2)) 
  next
    case f5 (* violates property that q is the only deadlock state *)
    then consider (f5a) "\<exists> xys \<in> L S . ((io_target M xys (initial M) = q \<and> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))" |
                  (f5b) "\<exists> xys \<in> L S . (\<not> io_target M xys (initial M) = q \<and> \<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys))" by blast
    then show "False"
    proof (cases)
      case f5a
      then obtain xys xys' where "xys \<in> L S" and "io_target M xys (initial M) = q"
                             and "xys' \<in> L S" and "length xys < length xys'" and "take (length xys) xys' = xys"
        by blast
      then obtain p where "path S (initial S) p" and "p_io p = xys'" by auto
      let ?tp = "take (length xys) p"
      let ?dp = "drop (length xys) p"
      let ?t = "hd ?dp"
      
      have "path S (initial S) ?tp"
        by (metis \<open>path S (initial S) p\<close> append_take_drop_id path_append_elim)
      then have "path M (initial M) ?tp"
        by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
      
      have "p_io ?tp = xys"
        by (metis \<open>p_io p = xys'\<close> \<open>take (length xys) xys' = xys\<close> take_map) 
      then have "io_target M xys (initial M) = target ?tp (initial M)" 
        using observable_path_io_target[OF assms(1) \<open>path M (initial M) ?tp\<close> ] by auto
      then have "target ?tp (initial M) = q" 
        using \<open>io_target M xys (initial M) = q\<close> by auto
      moreover have "initial M = initial S"
        using assms(2) by auto 
      ultimately have "target ?tp (initial S) = q" by auto
      
      have "path S (target ?tp (initial S)) ?dp"
        by (metis \<open>path S (initial S) p\<close> append_take_drop_id path_suffix)
      have "length ?dp > 0"
        using \<open>length xys < length xys'\<close> \<open>p_io p = xys'\<close> by auto
      have "?t \<in> h S"
        by (metis (no_types, lifting) \<open>0 < length (drop (length xys) p)\<close> \<open>path S (target (take (length xys) p) (initial S)) (drop (length xys) p)\<close> contra_subsetD hd_in_set length_greater_0_conv path_h) 
      moreover have "t_source ?t = target ?tp (initial S)"
        by (metis \<open>0 < length (drop (length xys) p)\<close> \<open>path S (target (take (length xys) p) (initial S)) (drop (length xys) p)\<close> hd_Cons_tl length_greater_0_conv path_cons_elim)
      ultimately have "\<not> deadlock_state S q"   
        using \<open>target ?tp (initial S) = q\<close>
        by (metis deadlock_state.elims(2)) 
      then show "False" using assms(2) unfolding is_preamble.simps by blast
    next
      case f5b
      then obtain xys where "xys \<in> L S" and "\<not> io_target M xys (initial M) = q" and "\<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)"
        by blast
      then obtain p where "path S (initial S) p" and "p_io p = xys"
        by auto
      then have "path M (initial M) p"
        by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
      then have "io_target M xys (initial M) = target p (initial M)"
        using observable_path_io_target[OF assms(1)] \<open>p_io p = xys\<close> by auto
      moreover have "io_target S xys (initial S) = io_target M xys (initial M)"
        using observable_submachine_io_target[OF assms(1) _ \<open>xys \<in> L S\<close>]
        by (metis assms(2) is_preamble.simps)
      ultimately have "io_target S xys (initial S) = target p (initial S)"
        using assms(2) by auto
        
      
      
      have "deadlock_state S (target p (initial S))"
        unfolding deadlock_state.simps proof 
        assume "\<exists>t\<in>h S. t_source t = target p (initial S)"  
        then obtain t where "t\<in>h S" and "t_source t = target p (initial S)"
          by blast
        then have "path S (initial S) (p@[t])" 
          using \<open>path S (initial S) p\<close> by (metis path.simps path_append) 
        then have "xys@[(t_input t,t_output t)] \<in> L S" 
          using \<open>p_io p = xys\<close>
        proof -
          have "xys @ [(t_input t, t_output t)] = p_io (p @ [t])"
            by (simp add: \<open>p_io p = xys\<close>)
          then have "\<exists>ps. xys @ [(t_input t, t_output t)] = p_io ps \<and> path S (initial S) ps"
            by (meson \<open>path S (initial S) (p @ [t])\<close>)
          then show ?thesis
            by simp
        qed 
        moreover have "length xys < length (xys @ [(t_input t, t_output t)]) \<and> take (length xys) (xys @ [(t_input t, t_output t)]) = xys"
          by simp
          
        ultimately show "False" 
          using \<open>\<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)\<close> by blast
      qed
        
      show "False" using assms(2) unfolding is_preamble.simps
        by (metis \<open>deadlock_state S (target p (initial S))\<close> \<open>io_target M xys (initial M) \<noteq> q\<close> \<open>io_target S xys (initial S) = io_target M xys (initial M)\<close> \<open>io_target S xys (initial S) = target p (initial S)\<close> \<open>path S (initial S) p\<close> nodes_path_initial)
    qed


    
  next
    case f6 (* violates property that q must be a reachable state *)
    have "\<not> q \<in> nodes S"
    proof 
      assume "q \<in> nodes S"
      then obtain p where "path S (initial S) p" and "target p (initial S) = q"
        by (metis path_to_nodes)
      then have "p_io p \<in> L S" 
        by auto
      moreover have "io_target M (p_io p) (initial M) = q"
        by (metis (no_types) \<open>path S (initial S) p\<close> \<open>target p (initial S) = q\<close> assms(1) assms(2) is_preamble.simps is_submachine.elims(2) observable_path_io_target submachine_path)
      ultimately show "False" using f6 by blast
    qed
        
    then show "False" using assms(2) unfolding is_preamble.simps by blast
  next
    case f7 (* violates path-prefix properties *)
    then obtain xys1 xys2 where "xys1@xys2 \<in> L S" and "\<not> xys1 \<in> L S" by blast
    then show "False" by (meson language_prefix) 
  qed
qed



lemma transition_filter_submachine :
  "is_submachine (M\<lparr> transitions := filter P (transitions M)\<rparr>) M"
  by auto

lemma preamble_set_shared_suffix :
  assumes "is_preamble_set M q P"
  and     "xys1@[xy] \<in> P"
  and     "xys2 \<in> P"
  and     "io_target M xys1 (initial M) = io_target M xys2 (initial M)"
  and     "observable M"
shows "xys2@[xy] \<in> P"
proof -
  have "xys1 \<in> P" using assms(1,2) unfolding is_preamble_set.simps by blast 
  moreover have "\<exists> xys' \<in> P. length xys1 < length xys' \<and> take (length xys1) xys' = xys1" 
    using assms(2) append_eq_conv_conj by fastforce 
  ultimately have "io_target M xys1 (initial M) \<noteq> q"
    using assms(1) unfolding is_preamble_set.simps by blast
  then have "io_target M xys2 (initial M) \<noteq> q"
    using assms(4) by auto
  then obtain xys2' where "xys2' \<in> P" and "length xys2 < length xys2'" and "take (length xys2) xys2' = xys2"
    using assms(1,3) unfolding is_preamble_set.simps by blast
  let ?xy = "hd (drop (length xys2) xys2')"
  have "xys2@[?xy]@(tl (drop (length xys2) xys2')) \<in> P"
    by (metis \<open>length xys2 < length xys2'\<close> \<open>take (length xys2) xys2' = xys2\<close> \<open>xys2' \<in> P\<close> append_Cons append_self_conv2 append_take_drop_id drop_eq_Nil hd_Cons_tl leD)
  then have "xys2@[?xy] \<in> P"
    using assms(1) unfolding is_preamble_set.simps by (metis (mono_tags, lifting) append_assoc) 
  then have "fst ?xy = fst xy"
    using assms(1,2,4) unfolding is_preamble_set.simps by (metis (no_types, lifting)) 


  have "xys1@[xy] \<in> L M"
    using assms(1,2) by auto
  then obtain p where "path M (initial M) p" and "p_io p = xys1@[xy]" 
    by auto
  let ?hp = "butlast p"
  let ?t = "last p"
  have "path M (initial M) ?hp"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> path_prefix snoc_eq_iff_butlast) 
  moreover have  "p_io ?hp = xys1"
    by (simp add: \<open>p_io p = xys1 @ [xy]\<close> map_butlast)
  ultimately have "target ?hp (initial M) = io_target M xys1 (initial M)"
    using assms(5) by (metis (mono_tags, lifting) observable_path_io_target) 
  then have "t_source ?t = io_target M xys1 (initial M)"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> path_cons_elim path_suffix snoc_eq_iff_butlast) 
  then have "path M (io_target M xys1 (initial M)) [?t]"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> \<open>target (butlast p) (initial M) = io_target M xys1 (initial M)\<close> path_suffix snoc_eq_iff_butlast)
  have "p_io [?t] = [(fst xy, snd xy)]"
    by (metis (mono_tags, lifting) \<open>p_io p = xys1 @ [xy]\<close> last_map list.simps(8) list.simps(9) prod.collapse snoc_eq_iff_butlast)
  
  have "[(fst xy, snd xy)] \<in> LS M (io_target M xys1 (initial M))"
  proof -
    have "\<exists>ps. [(fst xy, snd xy)] = p_io ps \<and> path M (io_target M xys1 (initial M)) ps"
      by (metis (no_types) \<open>p_io [last p] = [(fst xy, snd xy)]\<close> \<open>path M (io_target M xys1 (initial M)) [last p]\<close>)
    then show ?thesis
      by simp
  qed
  then have "[(fst xy, snd xy)] \<in> LS M (io_target M xys2 (initial M))"
    using assms(1) unfolding is_preamble_set.simps by (metis assms(4))

  then have "[(fst ?xy, snd xy)] \<in> LS M (io_target M xys2 (initial M))"
    using \<open>fst ?xy = fst xy\<close> by auto

  then have "xys2@[(fst xy, snd xy)] \<in> P" 
    using \<open>xys2@[?xy] \<in> P\<close> assms(1) unfolding is_preamble_set.simps
    by (metis (no_types, lifting) \<open>fst (hd (drop (length xys2) xys2')) = fst xy\<close>) 
  then show "xys2@[xy] \<in> P"
    by simp
qed


lemma preamble_set_implies_preamble :
  assumes "observable M" and "is_preamble_set M q P"
  shows "\<exists> S . is_preamble S M q \<and> L S = P"
proof -
  let ?is_preamble_transition = "\<lambda> t . \<exists> xys xy . xys@[xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy"
  let ?S = "M\<lparr> transitions := filter ?is_preamble_transition (transitions M) \<rparr>"

  have "is_submachine ?S M" by auto
  then have "L ?S \<subseteq> L M" 
    using submachine_language[of ?S M] by blast

  have "\<And> io . io \<in> L ?S \<longleftrightarrow> io \<in> P"
  proof -
    fix io
    show "io \<in> L ?S \<longleftrightarrow> io \<in> P"
    proof (induction io rule: rev_induct)
      case Nil
      have "[] \<in> P" using preamble_set_contains_empty_sequence[OF assms(2)] by auto
      moreover have "[] \<in> L ?S" by auto
      ultimately show ?case by blast
    next
      case (snoc xy io)
      have "io@[xy] \<in> L ?S \<Longrightarrow> io@[xy] \<in> P"
      proof -
        assume "io@[xy] \<in> L ?S"
        then have "io \<in> L ?S" using language_prefix[of io] by fastforce
        then have "io \<in> P" using snoc.IH by fastforce

        from \<open>io@[xy] \<in> L ?S\<close> obtain p where "path ?S (initial ?S) p" and "p_io p = io@[xy]" by auto
        let ?hp = "butlast p"
        let ?t = "last p"
        have "?t \<in> h ?S"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path (M\<lparr>transitions := filter ?is_preamble_transition (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter ?is_preamble_transition (transitions M)\<rparr>)) p\<close> append_is_Nil_conv contra_subsetD last_in_set not_Cons_self2 path_h) 
        then have "?is_preamble_transition ?t" 
          by auto
        then obtain xys xy' where "xys @ [xy'] \<in> P" 
                              and "t_source ?t = io_target M xys (initial M)" 
                              and "t_input ?t = fst xy'" 
                              and "t_output (last p) = snd xy'"
          by blast
        then have "xy' = xy"
          by (metis (mono_tags, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> append_is_Nil_conv last_map last_snoc not_Cons_self prod.collapse) 

        have "t_source ?t = target ?hp (initial ?S)"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p\<close> path_append_elim path_cons_elim snoc_eq_iff_butlast) 
        
        
        have "path ?S (initial ?S) ?hp" 
          using \<open>path ?S (initial ?S) p\<close>
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> append_butlast_last_id append_is_Nil_conv not_Cons_self2 path_prefix) 
        then have "path M (initial M) ?hp"
          using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto
        then have "io_target M io (initial M) = target ?hp (initial M)"
          by (metis (mono_tags, lifting) \<open>p_io p = io @ [xy]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)
          
        then have "io_target M xys (initial M) = io_target M io (initial M)"
          using \<open>t_source (last p) = io_target M xys (initial M)\<close> \<open>t_source (last p) = target (butlast p) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> by auto 
          
        then show "io@[xy] \<in> P"
          using preamble_set_shared_suffix[OF assms(2) \<open>xys @ [xy'] \<in> P\<close> \<open>io \<in> P\<close> _ assms(1)] \<open>xy' = xy\<close> by auto
      qed

      moreover have "io@[xy] \<in> P \<Longrightarrow> io@[xy] \<in> L ?S"
      proof -
        assume "io@[xy] \<in> P"
        then have "io \<in> P" and "io@[xy] \<in> L M" using assms(2) unfolding is_preamble_set.simps by blast+
        then have "io \<in> L ?S" using snoc.IH by auto

        from \<open>io@[xy] \<in> L M\<close> obtain p where "path M (initial M) p" and "p_io p = io@[xy]" by auto
        let ?hp = "butlast p"
        let ?t = "last p"

        have "t_source ?t = io_target M io (initial M) \<and> t_input ?t = fst xy \<and> t_output ?t = snd xy"
        proof - (* TODO: refactor auto-generated code *)
          have f1: "\<forall>ps p psa. (ps @ [p::integer \<times> integer] = psa) = (psa \<noteq> [] \<and> butlast psa = ps \<and> last psa = p)"
            using snoc_eq_iff_butlast by blast
          have f2: "p \<noteq> []"
            using \<open>p_io p = io @ [xy]\<close> by force
          then have f3: "butlast p @ [last p] = p"
            using append_butlast_last_id by blast
          then have f4: "path M (initial M) (butlast p)"
            by (metis (no_types) \<open>path M (initial M) p\<close> path_prefix)
          have f5: "p_io (butlast p) = io"
            by (simp add: \<open>p_io p = io @ [xy]\<close> map_butlast)
          have "\<forall>ps f. ps = [] \<or> last (map f ps) = (f (last ps::'a \<times> integer \<times> integer \<times> 'a)::integer \<times> integer)"
            using last_map by blast
          then have f6: "(t_input (last p), t_output (last p)) = last (p_io p)"
            using f2 by force
          have "io @ [xy] \<noteq> [] \<and> butlast (io @ [xy]) = io \<and> last (io @ [xy]) = xy"
            using f1 by blast
          then show ?thesis
            using f6 f5 f4 f3 by (metis (no_types) \<open>p_io p = io @ [xy]\<close> \<open>path M (initial M) p\<close> assms(1) fst_conv observable_path_io_target path_cons_elim path_suffix snd_conv)
        qed 

        then have "?is_preamble_transition ?t"
          using \<open>io@[xy] \<in> P\<close> by blast
        moreover have "?t \<in> h M"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path M (initial M) p\<close> contra_subsetD last_in_set path_h snoc_eq_iff_butlast)
        ultimately have "?t \<in> h ?S"
          by simp 
          

        from \<open>io \<in> L ?S\<close> obtain pS where "path ?S (initial ?S) pS" and "p_io pS = io" by auto
        then have "path M (initial M) pS"
          using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto
        then have "target pS (initial M) = io_target M io (initial M)"
          by (metis (mono_tags, lifting) \<open>p_io pS = io\<close> assms(1) observable_path_io_target)
        then have "path ?S (initial ?S) (pS@[?t])"
          by (metis (no_types, lifting) \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> \<open>last p \<in> h (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) pS\<close> \<open>t_source (last p) = io_target M io (initial M) \<and> t_input (last p) = fst xy \<and> t_output (last p) = snd xy\<close> cons is_submachine.elims(2) nil path_append)
        moreover have "p_io (pS@[?t]) = io@[xy]"
          by (simp add: \<open>p_io pS = io\<close> \<open>t_source (last p) = io_target M io (initial M) \<and> t_input (last p) = fst xy \<and> t_output (last p) = snd xy\<close>)  
        ultimately show "io@[xy] \<in> L ?S"
          unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
      qed

      ultimately show ?case by blast
    qed
  qed
  then have "L ?S = P" by auto

  have "acyclic ?S"
  proof (rule ccontr)
    assume "\<not> acyclic ?S"
    then obtain p where "path ?S (initial ?S) p" and "\<not> distinct (visited_states (initial ?S) p)"
      unfolding acyclic.simps by blast
    then have "path M (initial M) p" 
      using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto

    from \<open>path ?S (initial ?S) p\<close> have "p_io p \<in> L ?S" by auto
    then have "p_io p \<in> P" using \<open>L ?S = P\<close> by blast
    
    have "distinct (visited_states (initial M) p)"
      using assms(2) \<open>path M (initial M) p\<close> \<open>p_io p \<in> P\<close> unfolding is_preamble_set.simps by auto
    then show "False" 
      using \<open>\<not> distinct (visited_states (initial ?S) p)\<close> \<open>is_submachine ?S M\<close> by auto
  qed

  moreover have "single_input ?S"  
  proof (rule ccontr)
    assume "\<not> single_input ?S"
    then obtain t1 t2 where "t1 \<in> h ?S" and "t2 \<in> h ?S" and "t_source t1 = t_source t2" and "t_source t1 \<in> nodes ?S" and "t_input t1 \<noteq> t_input t2"
      unfolding single_input.simps by blast
    moreover from \<open>t_source t1 \<in> nodes ?S\<close> obtain p where "path ?S (initial ?S) p" and "target p (initial ?S) = t_source t1"
      by (metis (no_types, lifting) path_to_nodes)

    ultimately have "path ?S (initial ?S) (p@[t1])" and "path ?S (initial ?S) (p@[t2])"
      by (metis (no_types, lifting) cons nil path_append)+
    let ?xy1 = "(t_input t1, t_output t1)"
    let ?xy2 = "(t_input t2, t_output t2)"

    have "p_io (p@[t1]) = (p_io p)@[?xy1]" by auto
    have "p_io (p@[t2]) = (p_io p)@[?xy2]" by auto

    have "(p_io p)@[?xy1] \<in> L ?S"
      using \<open>path ?S (initial ?S) (p@[t1])\<close> \<open>p_io (p@[t1]) = (p_io p)@[?xy1]\<close> unfolding LS.simps
      by (metis (mono_tags, lifting) mem_Collect_eq) 
    moreover have "(p_io p)@[?xy2] \<in> L ?S"
      using \<open>path ?S (initial ?S) (p@[t2])\<close> \<open>p_io (p@[t2]) = (p_io p)@[?xy2]\<close> unfolding LS.simps
      by (metis (mono_tags, lifting) mem_Collect_eq) 
    ultimately have "(p_io p)@[?xy1] \<in> L ?S \<and> (p_io p)@[?xy2] \<in> L ?S \<and> fst ?xy1 \<noteq> fst ?xy2" 
      using \<open>t_input t1 \<noteq> t_input t2\<close> by auto
    then have "(p_io p)@[?xy1] \<in> L M \<and> (p_io p)@[?xy2] \<in> L M \<and> fst ?xy1 \<noteq> fst ?xy2" 
      using \<open>L ?S \<subseteq> L M\<close> by blast
    then have "\<not> (\<forall> xys xy1 xy2 . (xys@[xy1] \<in> L M \<and> xys@[xy2] \<in> L M) \<longrightarrow> fst xy1 = fst xy2)"
      by blast
    then show "False" using assms(2) unfolding is_preamble_set.simps
      by (metis (no_types, lifting) \<open>\<And>io. (io \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) = (io \<in> P)\<close> \<open>p_io p @ [(t_input t1, t_output t1)] \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) \<and> p_io p @ [(t_input t2, t_output t2)] \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) \<and> fst (t_input t1, t_output t1) \<noteq> fst (t_input t2, t_output t2)\<close>) 
  qed

  moreover have "is_submachine ?S M" by auto

  moreover have "q \<in> nodes ?S"
  proof -
    obtain ioq where "ioq \<in> P" and "io_target M ioq (initial M) = q"
      using assms(2) unfolding is_preamble_set.simps by blast
    then have "ioq \<in> L ?S" using \<open>L ?S = P\<close> by auto
    then obtain p where "path ?S (initial ?S) p" and "p_io p = ioq" by auto
    then have "target p (initial ?S) = io_target ?S ioq (initial ?S)"
      by (metis (mono_tags, lifting) assms(1) calculation(3) observable_path_io_target submachine_observable)
    moreover have "io_target ?S ioq (initial ?S) = io_target M ioq (initial M)"
      using \<open>ioq \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)\<close> \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> assms(1) observable_submachine_io_target by blast
    finally have "target p (initial ?S) = q"
      using \<open>io_target M ioq (initial M) = q\<close> by auto
    
    then show ?thesis
      using \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p\<close> nodes_path_initial by blast 
  qed

  moreover have "deadlock_state ?S q"
  proof (rule ccontr)
    assume "\<not> deadlock_state ?S q"
    then obtain t where "t \<in> h ?S" and "t_source t = q" 
      unfolding deadlock_state.simps by blast
    moreover from \<open>q \<in> nodes ?S\<close> obtain p where "path ?S (initial ?S) p" and "target p (initial ?S) = q"
      by (metis (no_types, lifting) path_to_nodes)
    ultimately have "path ?S (initial ?S) (p@[t])"
      by (metis (no_types, lifting) cons nil path_append) 
    then have "p_io (p@[t]) \<in> L ?S" unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
    then have "p_io (p@[t]) \<in> P" using \<open>L ?S = P\<close> by auto
    then have "p_io p \<in> P" using assms(2) unfolding is_preamble_set.simps
      by (metis (no_types, lifting) map_append) 

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine ?S M\<close>] \<open>path ?S (initial ?S) p\<close> by auto
    moreover have "target p (initial M) = q"
      using \<open>target p (initial ?S) = q\<close> \<open>is_submachine ?S M\<close> by auto
    ultimately have "io_target M (p_io p) (initial M) = q"
      by (metis (mono_tags, lifting) assms(1) observable_path_io_target)
      
    have "p_io (p@[t]) \<in> P \<and> length (p_io p) < length (p_io (p@[t])) \<and> take (length (p_io p)) (p_io (p@[t])) = p_io p"
      using \<open>p_io (p@[t]) \<in> P\<close> by simp

    then show "False" 
      using assms(2) unfolding is_preamble_set.simps 
      using \<open>p_io p \<in> P\<close> \<open>io_target M (p_io p) (initial M) = q\<close>
      by blast
  qed

  moreover have "(\<forall> q' \<in> nodes ?S . (q = q' \<or> \<not> deadlock_state ?S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)))"
  proof 
    fix q' assume "q' \<in> nodes ?S"
    then obtain p' where "path ?S (initial ?S) p'" and "target p' (initial ?S) = q'"
      by (metis (no_types, lifting) path_to_nodes)
    
    let ?ioq' = "p_io p'"

    have "?ioq' \<in> L ?S" 
      using \<open>path ?S (initial ?S) p'\<close> by auto
    then have "?ioq' \<in> P" using \<open>L ?S = P\<close> by auto

    have "path M (initial M) p'"
      using submachine_path[OF \<open>is_submachine ?S M\<close>] \<open>path ?S (initial ?S) p'\<close> by auto
    moreover have "target p' (initial M) = q'"
      using \<open>target p' (initial ?S) = q'\<close> \<open>is_submachine ?S M\<close> by auto
    ultimately have "io_target M ?ioq' (initial M) = q'"
      by (metis (mono_tags, lifting) assms(1) observable_path_io_target)
      

    have "(q = q' \<or> \<not> deadlock_state ?S q')"  
    proof (cases "q = q'")
      case True
      then show ?thesis by auto
    next
      case False
      then have "io_target M ?ioq' (initial M) \<noteq> q"
        using \<open>io_target M ?ioq' (initial M) = q'\<close> by auto
      then obtain xys' where "xys'\<in>P" and "length ?ioq' < length xys'" and "take (length ?ioq') xys' = ?ioq'"
        using assms(2) unfolding is_preamble_set.simps using \<open>?ioq' \<in> P\<close> by blast
      let ?xy' = "hd (drop (length ?ioq') xys')"
      have "?ioq'@[?xy']@(tl (drop (length ?ioq') xys')) \<in> P"
        using \<open>xys'\<in>P\<close> \<open>take (length ?ioq') xys' = ?ioq'\<close> \<open>length ?ioq' < length xys'\<close>
        by (metis (no_types, lifting) append_Cons append_Nil append_take_drop_id drop_eq_Nil hd_Cons_tl leD) 
      then have "?ioq'@[?xy'] \<in> P"
        using assms(2) unfolding is_preamble_set.simps by (metis (mono_tags, lifting) append_assoc) 
      then have "?ioq'@[?xy'] \<in> L ?S" using \<open>L ?S = P\<close> by auto
      then obtain p'' where "path ?S (initial ?S) p''" and "p_io p'' = ?ioq'@[?xy']" 
        by auto
      let ?hp'' = "butlast p''"
      let ?t'' = "last p''"
      have "p_io ?hp'' = ?ioq'"
        using \<open>p_io p'' = ?ioq'@[?xy']\<close> by (simp add: map_butlast) 
      then have "?hp'' = p'"
      proof - (* TODO: refactor auto-generated code *)
        have "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial M) p''"
          using \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> by auto
        then have "\<forall>f. path f (initial M) p'' \<or> \<not> is_submachine (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) f"
          by (meson submachine_path)
        then have f1: "path M (initial M) p''"
          using transition_filter_submachine by blast
        have "p'' \<noteq> []"
          using \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close> by force
        then show ?thesis
          using f1 by (metis (no_types) \<open>observable M\<close> \<open>p_io (butlast p'') = p_io p'\<close> \<open>path M (initial M) p'\<close> append_butlast_last_id observable_path_unique path_prefix)
      qed
        
        
        

      obtain t where "t \<in> h ?S" and "t_source t = q'" and "t_input t = fst ?xy'" and "t_output t = snd ?xy'"
      proof -
        assume a1: "\<And>t. \<lbrakk>t \<in> h (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>); t_source t = q'; t_input t = fst (hd (drop (length (p_io p')) xys')); t_output t = snd (hd (drop (length (p_io p')) xys'))\<rbrakk> \<Longrightarrow> thesis"
        have f2: "\<forall>f fa. is_submachine (f::('a, 'b) FSM_scheme) fa = (initial f = initial fa \<and> set (transitions f) \<subseteq> set (transitions fa) \<and> inputs f = inputs fa \<and> outputs f = outputs fa)"
          using is_submachine.simps by blast
        have f3: "p'' \<noteq> []"
          using \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close> by force
        then have "p' @ [last p''] = p''"
          using \<open>butlast p'' = p'\<close> append_butlast_last_id by blast
        then have "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial M) (p' @ [last p''])"
          using f2 \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> by presburger
        then have f4: "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) q' [last p'']"
          using \<open>target p' (initial M) = q'\<close> by force
        have "\<forall>f a ps. \<not> path (f::('a, 'b) FSM_scheme) a ps \<or> set ps \<subseteq> h f"
          by (meson path_h)
        then have f5: "last p'' \<in> h (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)"
          using f3 \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> last_in_set by blast
        have f6: "\<forall>ps f. ps = [] \<or> last (map f ps) = (f (last ps::'a \<times> integer \<times> integer \<times> 'a)::integer \<times> integer)"
          by (meson last_map)
        then have "last (p_io p'') = (t_input (last p''), t_output (last p''))"
          using f3 by blast
        then have f7: "t_input (last p'') = fst (hd (drop (length (p_io p')) xys'))"
          by (simp add: \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close>)
        have "(t_input (last p''), t_output (last p'')) = last (p_io p'')"
          using f6 f3 by fastforce
        then have "(t_input (last p''), t_output (last p'')) = hd (drop (length (p_io p')) xys')"
          by (simp add: \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close>)
        then have "t_output (last p'') = snd (hd (drop (length (p_io p')) xys'))"
          by (metis (no_types) snd_conv)
        then show ?thesis
          using f7 f5 f4 a1 by blast
      qed
        
      then have "\<not> deadlock_state ?S q'"
        unfolding deadlock_state.simps by blast

      then show ?thesis by auto
    qed

    moreover have "(\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
    proof 
      fix x assume "x \<in> set (inputs M)"
      show "(\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)"
      proof 
        assume "(\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x)"
        then obtain t where "t \<in> h ?S" and "t_source t = q'" and "t_input t = x" by blast
        then have "path ?S (initial ?S) (p'@[t])" 
          using \<open>path ?S (initial ?S) p'\<close> \<open>target p' (initial M) = q'\<close> by fastforce
        moreover have "p_io (p'@[t]) = ?ioq'@[(x,t_output t)]"
          using \<open>t_input t = x\<close> by auto
        ultimately have "?ioq'@[(x,t_output t)] \<in> L ?S"
        proof -
          have "\<exists>ps. p_io (p' @ [t]) = p_io ps \<and> path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) ps"
            by (metis (lifting) \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) (p' @ [t])\<close>)
          then show ?thesis
            using \<open>p_io (p' @ [t]) = p_io p' @ [(x, t_output t)]\<close> by auto
        qed
        then have "?ioq'@[(x,t_output t)] \<in> P"
          using \<open>L ?S = P\<close> by auto
          
        have "\<And> t' . t' \<in> h M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> h ?S"
        proof -
          fix t' assume "t' \<in> h M" and "t_source t' = q'" and "t_input t' = x" 
          then have "path M q' [t']" by auto
          then have "[(x, t_output t')] \<in> LS M q'"
            using \<open>t_input t' = x\<close> by force 
          then have "[(fst (x,t_output t), t_output t')] \<in> LS M (io_target M ?ioq' (initial M))"
            using \<open>io_target M ?ioq' (initial M) = q'\<close> by auto
          then have "?ioq'@[(x, t_output t')] \<in> P"
            using \<open>?ioq'@[(x,t_output t)] \<in> P\<close> assms(2) unfolding is_preamble_set.simps
            by (metis (no_types, lifting) fst_conv) 

          have "?is_preamble_transition t'"
            using \<open>io_target M (p_io p') (initial M) = q'\<close> \<open>p_io p' @ [(x, t_output t')] \<in> P\<close> \<open>t_input t' = x\<close> \<open>t_source t' = q'\<close> by auto
          then show "t' \<in> h ?S"
            using \<open>t' \<in> h M\<close> by auto
        qed
        then show "(\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)" by blast
      qed
    qed

    ultimately show "(q = q' \<or> \<not> deadlock_state ?S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
      by blast
  qed

  ultimately have "is_preamble ?S M q" 
    unfolding is_preamble.simps by blast
  then show ?thesis 
    using \<open>L ?S = P\<close> by blast
qed
      







fun output_completion :: "(Input \<times> Output) list set \<Rightarrow> Output set \<Rightarrow> (Input \<times> Output) list set" where
  "output_completion P Out = P \<union> {io@[(fst xy, y)] | io xy y . y \<in> Out \<and> io@[xy] \<in> P \<and> io@[(fst xy, y)] \<notin> P}"






fun output_complete_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_sequences M P = (\<forall> io \<in> P . io = [] \<or> (\<forall> y \<in> set (outputs M) . (butlast io)@[(fst (last io), y)] \<in> P))"

value "output_complete_sequences M_ex {}"  
value "output_complete_sequences M_ex {[]}"
value "output_complete_sequences M_ex {[],[(1,10)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,10),(1,20)],[(1,10),(1,30)]}"



fun acyclic_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences M P = (\<forall> p . (path M (initial M) p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states (initial M) p))"

fun acyclic_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences' M P = (\<forall> io \<in> P . \<forall> p \<in> set (paths_of_length M (initial M) (length io)) . (p_io p = io) \<longrightarrow> distinct (visited_states (initial M) p))"

lemma acyclic_sequences_alt_def[code] : "acyclic_sequences M P = acyclic_sequences' M P"
  unfolding acyclic_sequences'.simps acyclic_sequences.simps
  by (metis (no_types, lifting) length_map paths_of_length_containment paths_of_length_is_path(1))
  
value "acyclic_sequences M_ex {}"  
value "acyclic_sequences M_ex {[]}"
value "acyclic_sequences M_ex {[(1,30)]}"
value "acyclic_sequences M_ex {[(1,30),(2,20)]}"





fun single_input_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "single_input_sequences M P = (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)"

fun single_input_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "single_input_sequences' M P = (\<forall> io1 \<in> P . \<forall> io2 \<in> P . io1 = [] \<or> io2 = [] \<or> ((io_target M (butlast io1) (initial M) = io_target M (butlast io2) (initial M)) \<longrightarrow> fst (last io1) = fst (last io2)))"

lemma single_input_sequences_alt_def[code] : "single_input_sequences M P = single_input_sequences' M P"
  unfolding single_input_sequences.simps single_input_sequences'.simps
  by (metis append_butlast_last_id append_is_Nil_conv butlast_snoc last_snoc not_Cons_self)

value "single_input_sequences M_ex {}"
value "single_input_sequences M_ex {[]}"
value "single_input_sequences M_ex {[(1,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(2,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,20)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(1,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(2,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(1,30)],[(1,30),(2,30)]}"







fun output_complete_for_FSM_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences M P = (\<forall> io xy t . io@[xy] \<in> P \<and> t \<in> h M \<and> t_source t = io_target M io (initial M) \<and> t_input t = fst xy \<longrightarrow> io@[(fst xy, t_output t)] \<in> P)"
lemma output_complete_for_FSM_sequences_alt_def :
  shows "output_complete_for_FSM_sequences M P = (\<forall> xys xy y . (xys@[xy] \<in> P \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> P)"
proof -
  have "\<And> xys (xy :: (Input \<times> Output)) y .[(fst xy,y)] \<in> LS M (io_target M xys (initial M)) \<Longrightarrow> \<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
    then obtain p where "path M (io_target M xys (initial M)) p" and "p_io p = [(fst xy,y)]"
      unfolding LS.simps mem_Collect_eq by (metis (no_types, lifting)) 
    let ?t = "hd p"
    have "?t \<in> h M \<and> t_source ?t = io_target M xys (initial M) \<and> t_input ?t = fst xy \<and> t_output ?t = y"
      using \<open>p_io p = [(fst xy, y)]\<close> \<open>path M (io_target M xys (initial M)) p\<close> path'.simps(2) by auto
    
    then show "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
  qed
  have "\<And> xys (xy :: (Input \<times> Output)) y . \<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
    then obtain t where "t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
    then have "path M (io_target M xys (initial M)) [t] \<and> p_io [t] = [(fst xy, y)]"
      by (metis (no_types, lifting) list.simps(8) list.simps(9) path.simps)
      

    then show "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
      unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
  qed

  show ?thesis
  proof -
    have "\<forall>f P. output_complete_for_FSM_sequences f P = (\<forall>ps p pa. (ps @ [p] \<notin> P \<or> pa \<notin> h f \<or> (t_source pa::'a) \<noteq> io_target f ps (initial f) \<or> t_input pa \<noteq> fst p) \<or> ps @ [(fst p, t_output pa)] \<in> P)"
      by (meson output_complete_for_FSM_sequences.simps)
  then have "(\<not> output_complete_for_FSM_sequences M P) \<noteq> (\<forall>ps p n. (ps @ [p] \<notin> P \<or> [(fst p, n)] \<notin> LS M (io_target M ps (initial M))) \<or> ps @ [(fst p, n)] \<in> P)"
  by (metis (full_types) \<open>\<And>y xys xy. [(fst xy, y)] \<in> LS M (io_target M xys (initial M)) \<Longrightarrow> \<exists>t. t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y\<close> \<open>\<And>y xys xy. \<exists>t. t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy, y)] \<in> LS M (io_target M xys (initial M))\<close>)
    then show ?thesis
      by blast
  qed 
qed

fun output_complete_for_FSM_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences' M P = (\<forall> io\<in>P . \<forall> t \<in> h M . io = [] \<or> (t_source t = io_target M (butlast io) (initial M) \<and> t_input t = fst (last io) \<longrightarrow> (butlast io)@[(fst (last io), t_output t)] \<in> P))"

lemma output_complete_for_FSM_sequences_alt_def'[code] : "output_complete_for_FSM_sequences M P = output_complete_for_FSM_sequences' M P"
  unfolding output_complete_for_FSM_sequences.simps output_complete_for_FSM_sequences'.simps
  by (metis last_snoc snoc_eq_iff_butlast)
  

value "output_complete_for_FSM_sequences M_ex {}"
value "output_complete_for_FSM_sequences M_ex {[]}"
value "output_complete_for_FSM_sequences M_ex {[(1,20)]}"
value "output_complete_for_FSM_sequences M_ex {[(1,10)],[(1,20)]}"
value "output_complete_for_FSM_sequences M_ex {[(1,20)],[(1,30)]}"

  

fun deadlock_states_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "deadlock_states_sequences M Q P = (\<forall> xys \<in> P . 
                                        ((io_target M xys (initial M) \<in> Q 
                                          \<and> \<not> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
                                      \<or> (\<not> io_target M xys (initial M) \<in> Q 
                                          \<and> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))" 

value "deadlock_states_sequences M_ex {} {}"
value "deadlock_states_sequences M_ex {} {[]}"
value "deadlock_states_sequences M_ex {2} {[]}" 
value "deadlock_states_sequences M_ex {3} {[]}"
value "deadlock_states_sequences M_ex {3} {[(1,20)]}"
value "deadlock_states_sequences M_ex {2,3} {[(1,20)]}"
value "deadlock_states_sequences M_ex {2,3} {[(1,30)]}"
value "deadlock_states_sequences M_ex {2,4} {[],[(1,30)]}"
value "deadlock_states_sequences M_ex {2,4} {[(1,20)],[(1,30)]}"
value "deadlock_states_sequences M_ex {3,4} {[(1,20)],[(1,30)]}"



fun reachable_states_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "reachable_states_sequences M Q P = (\<forall> q \<in> Q . \<exists> xys \<in> P . io_target M xys (initial M) = q)"


value "reachable_states_sequences M_ex {} {}"
value "reachable_states_sequences M_ex {} {[]}"
value "reachable_states_sequences M_ex {2} {}"
value "reachable_states_sequences M_ex {2} {[]}"
value "reachable_states_sequences M_ex {3,4} {[(1,20)],[(1,30),(2,20)]}"
value "reachable_states_sequences M_ex {3,4} {[(1,20)],[(1,30)]}"
value "reachable_states_sequences M_ex {3,4,5} {[(1,20)],[(1,30)]}"


fun prefix_closed_sequences :: "(Input \<times> Output) list set \<Rightarrow> bool" where
  "prefix_closed_sequences P = (\<forall> xys1 xys2 . xys1@xys2 \<in> P \<longrightarrow> xys1 \<in> P)"

fun prefix_closed_sequences' :: "(Input \<times> Output) list set \<Rightarrow> bool" where
  "prefix_closed_sequences' P = (\<forall> io \<in> P . io = [] \<or> (butlast io) \<in> P)"

lemma prefix_closed_sequences_alt_def[code] : "prefix_closed_sequences P = prefix_closed_sequences' P"
proof 
  show "prefix_closed_sequences P \<Longrightarrow> prefix_closed_sequences' P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps
    by (metis append_butlast_last_id) 

  have "\<And>xys1 xys2. \<forall>io\<in>P. io = [] \<or> butlast io \<in> P \<Longrightarrow> xys1 @ xys2 \<in> P \<Longrightarrow> xys1 \<in> P"
  proof -
    fix xys1 xys2 assume "\<forall>io\<in>P. io = [] \<or> butlast io \<in> P" and "xys1 @ xys2 \<in> P"
    then show "xys1 \<in> P"
    proof (induction xys2 rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a xys2)
      then show ?case
        by (metis append.assoc snoc_eq_iff_butlast) 
    qed
  qed

  then show "prefix_closed_sequences' P \<Longrightarrow> prefix_closed_sequences P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps by blast 
qed

value "prefix_closed_sequences {}"
value "prefix_closed_sequences {[]}"
value "prefix_closed_sequences {[(1,20)]}"
value "prefix_closed_sequences {[],[(1,20)]}"



lemma is_preamble_set_alt_def :
  "is_preamble_set M q P = (
    P \<subseteq> L M
    \<and> acyclic_sequences M P
    \<and> single_input_sequences M P
    \<and> output_complete_for_FSM_sequences M P
    \<and> deadlock_states_sequences M {q} P
    \<and> reachable_states_sequences M {q} P
    \<and> prefix_closed_sequences P)"
  using output_complete_for_FSM_sequences_alt_def[of M P]
  unfolding is_preamble_set.simps 
            acyclic_sequences.simps 
            single_input_sequences.simps
            deadlock_states_sequences.simps
            reachable_states_sequences.simps
            prefix_closed_sequences.simps 
  by blast


fun list_max :: "nat list \<Rightarrow> nat" where
  "list_max [] = 0" |
  "list_max xs = Max (set xs)"

lemma list_max_is_max : "q \<in> set xs \<Longrightarrow> q \<le> list_max xs"
  by (metis List.finite_set Max_ge length_greater_0_conv length_pos_if_in_set list_max.elims) 




lemma language_contains_code : "(io \<in> L M) = (io \<in> (set (map p_io (paths_up_to_length M (initial M) (length io)))))"
proof -
  have "io \<in> L M \<Longrightarrow> \<exists>p. io = p_io p \<and> path M (initial M) p \<and> length p \<le> length io"
  proof -
    assume "io \<in> L M"
    then obtain p where "io = p_io p" and "path M (initial M) p" by auto
    then have "length p = length io" by auto
    show "\<exists>p. io = p_io p \<and> path M (initial M) p \<and> length p \<le> length io"
      using \<open>io = p_io p\<close> \<open>length p = length io\<close> \<open>path M (initial M) p\<close> eq_refl by blast      
  qed
  then have "(io \<in> L M) = (io \<in> image p_io {p . path M (initial M) p \<and> length p \<le> length io})"
    unfolding LS.simps by blast
  then show ?thesis 
    using paths_up_to_length_path_set[of M "initial M" "length io"] by simp 
qed
  
lemma language_subset_code : "((set P) \<subseteq> L M) = ((set P) \<subseteq> (set (map p_io (paths_up_to_length M (initial M) (list_max (map length P))))))"
proof -
  have "\<And>x. x \<in> set P \<Longrightarrow> x \<in> L M \<Longrightarrow> \<exists>p. x = p_io p \<and> path M (initial M) p \<and> length p \<le> list_max (map length P)"
  proof -
    fix x assume "x \<in> set P" and "x \<in> L M"
    then obtain p where "x = p_io p" and "path M (initial M) p" by auto
    then have "length p = length x" by auto
    moreover have "length x \<in> set (map length P)"
      using \<open>x \<in> set P\<close> by auto
    ultimately have "length p \<le> list_max (map length P)" 
      using list_max_is_max by auto
    show "\<exists>p. x = p_io p \<and> path M (initial M) p \<and> length p \<le> list_max (map length P)"
      using \<open>length p \<le> list_max (map length P)\<close> \<open>path M (initial M) p\<close> \<open>x = p_io p\<close> by auto 
  qed

  then have "((set P) \<subseteq> L M) = ((set P) \<subseteq> image p_io {p . path M (initial M) p \<and> length p \<le> (list_max (map length P))})"
    unfolding LS.simps by blast
  then show ?thesis 
    using paths_up_to_length_path_set[of M "initial M" "list_max (map length P)"] by simp 
qed

lemma is_preamble_set_code[code] :
  "is_preamble_set M q (set P) = (
    ((set P) \<subseteq> (set (map p_io (paths_up_to_length M (initial M) (list_max (map length P))))))
    \<and> acyclic_sequences M (set P)
    \<and> single_input_sequences M (set P)
    \<and> output_complete_for_FSM_sequences M (set P)
    \<and> deadlock_states_sequences M {q} (set P)
    \<and> reachable_states_sequences M {q} (set P)
    \<and> prefix_closed_sequences (set P))"
  by (metis (mono_tags, lifting) is_preamble_set_alt_def language_subset_code)










fun generate_selector_lists :: "nat \<Rightarrow> bool list list" where
  "generate_selector_lists k = lists_of_length [False,True] k"
  (*"generate_selector_lists k = lists_of_length [True,False] k"*)
  

value "generate_selector_lists 4"

lemma generate_selector_lists_set : "set (generate_selector_lists k) = {(bs :: bool list) . length bs = k}"
  using lists_of_length_list_set by auto 

fun generate_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> bool list \<Rightarrow> ('a, 'b) FSM_scheme" where
  "generate_submachine M bs = M\<lparr> transitions := map fst (filter snd (zip (transitions M) bs)) \<rparr>"

lemma generate_submachine_is_submachine : "is_submachine (generate_submachine M bs) M" 
proof -
  have "\<And> x . x \<in> set (map fst (filter snd (zip (transitions M) bs))) \<Longrightarrow> x \<in> set (transitions M)"
    by (metis (no_types, lifting) filter_eq_nths in_set_takeD map_fst_zip_take notin_set_nthsI nths_map)
  then show ?thesis  
    using generate_submachine.simps is_submachine.simps by fastforce
qed



lemma selector_list_index_set:
  assumes "length ms = length bs"
  shows "set (map fst (filter snd (zip ms bs))) = { ms ! i | i . i < length bs \<and> bs ! i}"
using assms proof (induction bs arbitrary: ms rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc b bs)
  let ?ms = "butlast ms"
  let ?m = "last ms"

  have "length ?ms = length bs" using snoc.prems by auto

  have "map fst (filter snd (zip ms (bs @ [b]))) = (map fst (filter snd (zip ?ms bs))) @ (map fst (filter snd (zip [?m] [b])))"
    by (metis \<open>length (butlast ms) = length bs\<close> append_eq_conv_conj filter_append length_0_conv map_append snoc.prems snoc_eq_iff_butlast zip_append2)
  then have *: "set (map fst (filter snd (zip ms (bs @ [b])))) = set (map fst (filter snd (zip ?ms bs))) \<union> set (map fst (filter snd (zip [?m] [b])))"
    by simp
    

  have "{ms ! i |i. i < length (bs @ [b]) \<and> (bs @ [b]) ! i} = {ms ! i |i. i \<le> (length bs) \<and> (bs @ [b]) ! i}"
    by auto
  moreover have "{ms ! i |i. i \<le> (length bs) \<and> (bs @ [b]) ! i} = {ms ! i |i. i < length bs \<and> (bs @ [b]) ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    by fastforce
  moreover have "{ms ! i |i. i < length bs \<and> (bs @ [b]) ! i} = {?ms ! i |i. i < length bs \<and> bs ! i}"
    using \<open>length ?ms = length bs\<close> by (metis butlast_snoc nth_butlast)  
  ultimately have **: "{ms ! i |i. i < length (bs @ [b]) \<and> (bs @ [b]) ! i} = {?ms ! i |i. i < length bs \<and> bs ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    by simp
  

  have "set (map fst (filter snd (zip [?m] [b]))) = {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
  proof (cases b)
    case True
    then have "set (map fst (filter snd (zip [?m] [b]))) = {?m}" by fastforce
    moreover have "{ms ! i |i. i = length bs \<and> (bs @ [b]) ! i} = {?m}" 
    proof -
      have "(bs @ [b]) ! length bs"
        by (simp add: True) 
      moreover have "ms ! length bs = ?m"
        by (metis last_conv_nth length_0_conv length_butlast snoc.prems snoc_eq_iff_butlast) 
      ultimately show ?thesis by fastforce
    qed
    ultimately show ?thesis by auto
  next
    case False
    then show ?thesis by auto
  qed

  then have "set (map fst (filter snd (zip (butlast ms) bs))) \<union> set (map fst (filter snd (zip [?m] [b])))
             = {butlast ms ! i |i. i < length bs \<and> bs ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    using snoc.IH[OF \<open>length ?ms = length bs\<close>] by blast

  then show ?case using * **
    by simp 
qed
    
    
    
  
 
    
    

    

lemma generate_submachine_transition_set_equality :
  assumes "set xs \<subseteq> set ms"
  shows "\<exists> bs . length bs = length ms \<and> set xs = set (map fst (filter snd (zip ms bs)))"
using assms proof (induction xs rule: rev_induct)
  case Nil
  let ?bs = "replicate (length ms) False"
  have "set [] = set (map fst (filter snd (zip ms ?bs)))"
    by (metis filter_False in_set_zip length_replicate list.simps(8) nth_replicate)
  moreover have "length ?bs = length ms" by auto
  ultimately show ?case by blast
next
  case (snoc a xs)
  then have "set xs \<subseteq> set ms" and "a \<in> set ms" by auto
  then obtain bs where "length bs = length ms" and "set xs = set (map fst (filter snd (zip ms bs)))" using snoc.IH by auto

  from \<open>a \<in> set ms\<close> obtain i where "i < length ms" and "ms ! i = a"
    by (meson in_set_conv_nth) 

  let ?bs = "list_update bs i True"
  have "length ms = length ?bs" using \<open>length bs = length ms\<close> by auto
  have "length ?bs = length bs" by auto

  have "set (map fst (filter snd (zip ms ?bs))) = {ms ! i |i. i < length ?bs \<and> ?bs ! i}"
    using selector_list_index_set[OF \<open>length ms = length ?bs\<close>] by assumption

  have "\<And> j . j < length ?bs \<Longrightarrow> j \<noteq> i \<Longrightarrow> ?bs ! j = bs ! j"
    by auto
  then have "{ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j} = {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}"
    using \<open>length ?bs = length bs\<close> by fastforce
  
  
  
  have "{ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j} = {a}"
    using \<open>length bs = length ms\<close> \<open>i < length ms\<close> \<open>ms ! i = a\<close> by auto
  then have "{ms ! i |i. i < length ?bs \<and> ?bs ! i} = insert a {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}"
    by fastforce
  

  have "{ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<subseteq> {ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j}"
    by (simp add: Collect_mono)
  then have "{ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<subseteq> {a}"
    using \<open>{ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j} = {a}\<close> by auto
  moreover have "{ms ! j |j. j < length bs \<and> bs ! j} = {ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<union> {ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j}"
    by fastforce

  ultimately have "{ms ! i |i. i < length ?bs \<and> ?bs ! i} = insert a {ms ! i |i. i < length bs \<and> bs ! i}"
    using \<open>{ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j} = {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}\<close>
    using \<open>{ms ! ia |ia. ia < length (bs[i := True]) \<and> bs[i := True] ! ia} = insert a {ms ! j |j. j < length (bs[i := True]) \<and> j \<noteq> i \<and> bs[i := True] ! j}\<close> by auto 

  moreover have "set (map fst (filter snd (zip ms bs))) = {ms ! i |i. i < length bs \<and> bs ! i}"
    using selector_list_index_set[of ms bs] \<open>length bs = length ms\<close> by auto

  ultimately have "set (a#xs) = set (map fst (filter snd (zip ms ?bs)))"
    using \<open>set (map fst (filter snd (zip ms ?bs))) = {ms ! i |i. i < length ?bs \<and> ?bs ! i}\<close> \<open>set xs = set (map fst (filter snd (zip ms bs)))\<close> by auto
  then show ?case
    using \<open>length ms = length ?bs\<close>
    by (metis Un_commute insert_def list.set(1) list.simps(15) set_append singleton_conv) 
qed


fun generate_submachines :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme list" where
  "generate_submachines M = map (generate_submachine M) (generate_selector_lists (length (transitions M)))"

lemma generate_submachines_containment :
  assumes "is_submachine S M"
  shows "\<exists> S' \<in> set (generate_submachines M) . (h S = h S')"
proof -
  have "set (transitions S) \<subseteq> set (transitions M)" using assms by auto
  then obtain bs where "length bs = length (transitions M)"  and "set (transitions S) = set (map fst (filter snd (zip (transitions M) bs)))" 
    using generate_submachine_transition_set_equality[of "transitions S" "transitions M"] by blast
  then have "bs \<in> set (generate_selector_lists (length (transitions M)))"
    using generate_selector_lists_set[of "length (transitions M)"] by blast
  then have *: "generate_submachine M bs \<in> set (generate_submachines M)" 
    by auto
  
  have "set (transitions S) = set (transitions (generate_submachine M bs))"
    using \<open>set (transitions S) = set (map fst (filter snd (zip (transitions M) bs)))\<close> unfolding generate_submachine.simps by auto
  moreover have "inputs S = inputs (generate_submachine M bs)"
    using assms by auto
  moreover have "outputs S = outputs (generate_submachine M bs)"
    using assms by auto
  ultimately have **: "h S = h (generate_submachine M bs)"
    by auto

  show ?thesis using * ** by blast
qed

lemma generate_submachines_are_submachines :
  assumes "S \<in> set (generate_submachines M)"
  shows "is_submachine S M"
  using assms generate_submachine_is_submachine[of M] unfolding generate_submachines.simps by fastforce
    
value "generate_submachines M_ex"


fun language_up_to_length :: "('a, 'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (Input \<times> Output) list list" where
  "language_up_to_length M k = map p_io (paths_up_to_length M (initial M) k)"

lemma language_up_to_length_set : "set (language_up_to_length M k) = { io \<in> L M . length io \<le> k }"
  using paths_up_to_length_path_set[of M "initial M" k] unfolding LS.simps language_up_to_length.simps by auto

lemma language_up_to_length_finite_language_fixpoint :
  assumes "language_up_to_length S (Suc n) = language_up_to_length S n"
  shows "L S = set (language_up_to_length S n)"
proof (rule ccontr)
  assume "L S \<noteq> set (language_up_to_length S n)"
  then obtain io where "io \<in> L S" and "io \<notin> set (language_up_to_length S n)" using language_up_to_length_set by blast
  then have "length io > n"
    using language_up_to_length_set leI by blast 
  then have "take (Suc n) io \<in> L S"
    by (metis \<open>io \<in> L S\<close> append_take_drop_id language_prefix)
  then have "take (Suc n) io \<in> set (language_up_to_length S (Suc n))"
    by (metis (no_types, lifting) Suc_leI \<open>n < length io\<close> language_contains_code language_up_to_length.simps length_take min.absorb2) 
  moreover have "take (Suc n) io \<notin> set (language_up_to_length S n)"
    by (metis (no_types, lifting) \<open>n < length io\<close> language_up_to_length_set length_take less_eq_Suc_le less_not_refl2 mem_Collect_eq min.absorb2)
  ultimately show "False" using assms by metis
qed
  
lemma distinct_io_path_length :
  assumes "path M (initial M) p"
  and     "distinct (visited_states (initial M) p)"
shows "length p < size M"
  by (metis (no_types, lifting) size_def Suc_less_SucD assms(1) assms(2) card_mono distinct_card le_simps(2) length_Cons length_map nodes.initial nodes_finite visited_states.simps visited_states_are_nodes)

lemma is_preamble_set_length :
  assumes "is_preamble_set M q P"
  shows "P \<subseteq> set (language_up_to_length M ( size M - 1 ))" 
proof 
  fix x assume "x \<in> P"
  then have "x \<in> L M" using assms by auto
  then obtain p where "p_io p = x" and "path M (initial M) p" by auto
  then have "distinct (visited_states (initial M) p)" using is_preamble_set_alt_def[of M q P] assms acyclic_sequences.simps
    using \<open>x \<in> P\<close> by blast 
  then have "length p < size M" using distinct_io_path_length[OF \<open>path M (initial M) p\<close>] by auto
  then have "p_io p \<in> { io \<in> L M . length io < size M }"
    using \<open>p_io p = x\<close> \<open>x \<in> L M\<close> by fastforce 
  moreover have "size M > 0"
    using \<open>length p < size M\<close> by auto 
  ultimately have "x \<in> { io \<in> L M . length io \<le> size M - 1 }"
    using \<open>p_io p = x\<close> by auto
  then show "x \<in> set (language_up_to_length M ( size M - 1 ))"
    using language_up_to_length_set[of M "size M - 1"]  by auto
qed


value "language_up_to_length M_ex 1"
value "language_up_to_length M_ex 5"





fun calculate_preamble_set_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set option" where
  "calculate_preamble_set_naive M q = (let n = size M - 1 in
    (case 
      (filter 
        (\<lambda> S . language_up_to_length S (Suc n) = language_up_to_length S n \<and>  is_preamble_set M q (set (language_up_to_length S n))) 
        (generate_submachines M)) of
    [] \<Rightarrow> None |
    SS \<Rightarrow> (Some (set (language_up_to_length (hd SS) n)))))" 



lemma calculate_preamble_set_naive_soundness :
  assumes "calculate_preamble_set_naive M q = Some P"
  shows "is_preamble_set M q P"
proof -
  have P_prop : "P = set (language_up_to_length (hd 
              (filter 
                (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
                (generate_submachines M))
              ) ( size M - 1 ))"
    using assms unfolding calculate_preamble_set_naive.simps
    by (metis (no_types, lifting) hd_Cons_tl list.case_eq_if option.discI option.inject)

  have *: "filter 
        (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
        (generate_submachines M) \<noteq> []"
    by (metis (mono_tags, lifting) assms calculate_preamble_set_naive.simps list.case_eq_if option.discI)

  let ?S = "hd (filter 
        (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
        (generate_submachines M))"

  have "?S \<in> set (generate_submachines M)"
    using * by (metis (no_types, lifting) filter_set hd_in_set member_filter) 
  then have "is_submachine ?S M"
    using generate_submachines_are_submachines[of ?S M] by fastforce
  
  have "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and> is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) ?S"
    using filter_list_set_not_contained[OF \<open>?S \<in> set (generate_submachines M)\<close>, of "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and> is_preamble_set M q (set (language_up_to_length S ( size M - 1 ))))"] hd_in_set[OF *] by fastforce
  then have "language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )" and "is_preamble_set M q (set (language_up_to_length ?S ( size M - 1 )))"
    by fastforce+
  
  have "set (language_up_to_length ?S ( size M - 1 )) = L ?S"
    using sym[OF language_up_to_length_finite_language_fixpoint[OF \<open>language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )\<close>]] by assumption
  moreover have "P = set (language_up_to_length ?S ( size M - 1 ))"
    using P_prop by fastforce
  ultimately have "P = L ?S"
    by metis
  moreover have "is_preamble_set M q (L ?S)"
    using \<open>is_preamble_set M q (set (language_up_to_length ?S ( size M - 1 )))\<close> sym[OF language_up_to_length_finite_language_fixpoint[OF \<open>language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )\<close>]] by metis
  ultimately show ?thesis by metis
qed


lemma calculate_preamble_set_naive_exhaustiveness :
  assumes "observable M"
  and     "is_preamble_set M q P"
  shows "calculate_preamble_set_naive M q \<noteq> None"
proof -

  obtain SP where "is_preamble SP M q" and "L SP = P"
    using preamble_set_implies_preamble[OF assms] by blast
  then have "is_submachine SP M"
    by auto

  then obtain S where "S \<in> set (generate_submachines M)" and "h S = h SP"
    using generate_submachines_containment by blast
  then have "is_submachine S M"
    using generate_submachines_are_submachines by blast 
  then have "L S \<subseteq> L M"
    using submachine_language by blast  

  have "L S = L SP"
    using \<open>is_submachine S M\<close> \<open>is_submachine SP M\<close> \<open>h S = h SP\<close> unfolding is_submachine.simps LS.simps
    by (metis (no_types, lifting) h_equivalence_path) 
  then have "L S = P"
    using \<open>L SP = P\<close> by simp
  then have "L S \<subseteq> set (language_up_to_length M ( size M - 1) )"
    using is_preamble_set_length[OF assms(2)] by auto
  then have "L S \<subseteq> {io \<in> L M. length io \<le> size M - 1}"
    using language_up_to_length_set[of M "size M - 1"] by blast
  moreover have "L S \<inter> {io \<in> L M. length io \<le> size M - 1} = {io \<in> L S. length io \<le> size M - 1}"
    using \<open>L S \<subseteq> L M\<close> by blast
  ultimately have "L S \<subseteq> {io \<in> L S. length io \<le> size M - 1}"
    by blast
  then have "L S = {io \<in> L S. length io \<le> size M - 1}"
    by auto
  then have "P = set (language_up_to_length S ( size M - 1) )"
    using language_up_to_length_set[of S "size M - 1"] \<open>L S = P\<close> by blast
  then have "is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))"
    using assms(2) by metis
  
  have "language_up_to_length S (Suc ( size M - 1 )) = (language_up_to_length S ( size M - 1 )) @ (map p_io (paths_of_length S (initial S) (Suc ( size M - 1 ))))"
  proof -
    have "language_up_to_length S (Suc ( size M - 1)) = map p_io (paths_up_to_length S (initial S) ( size M - 1)) @ map p_io (paths_of_length S (initial S) (Suc ( size M - 1)))"
      by (metis (no_types) language_up_to_length.simps map_append paths_up_to_length.simps(2))
    then show ?thesis
      by (metis (no_types) language_up_to_length.simps)
  qed
  moreover have "map p_io (paths_of_length S (initial S) (Suc ( size M - 1))) = []"
  proof (rule ccontr)
    assume "map p_io (paths_of_length S (initial S) (Suc ( size M - 1))) \<noteq> []"
    then have "(paths_of_length S (initial S) (Suc ( size M - 1))) \<noteq> []"
      by fastforce
    then obtain p where "p \<in> set (paths_of_length S (initial S) (Suc ( size M - 1)))" 
      using hd_in_set[of "paths_of_length S (initial S) (Suc ( size M - 1))"] by blast
    have "path S (initial S) p" and "length p = (Suc ( size M - 1))"
      using paths_of_length_is_path[OF \<open>p \<in> set (paths_of_length S (initial S) (Suc ( size M - 1)))\<close>] by auto
    then have "p_io p \<in> {io \<in> L S. length io = Suc ( size M - 1 )}" unfolding LS.simps by fastforce
    moreover have "{io \<in> L S. length io = Suc ( size M - 1 )} = {}"
      using \<open>L S \<subseteq> {io \<in> L S. length io \<le> size M - 1}\<close> by fastforce 
    ultimately show "False" by blast
  qed
  ultimately have "(language_up_to_length S (Suc ( size M - 1 ))) = (language_up_to_length S ( size M - 1 ))"
    by simp


  let ?f = "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 ))))"

  have "?f S"
    using \<open>(language_up_to_length S (Suc ( size M - 1 ))) = (language_up_to_length S ( size M - 1 ))\<close> \<open>is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))\<close> by metis
  then have "(filter ?f (generate_submachines M)) \<noteq> []"
    using \<open>S \<in> set (generate_submachines M)\<close> filter_empty_conv[of ?f "generate_submachines M"] by blast

  then show "calculate_preamble_set_naive M q \<noteq> None"
    unfolding calculate_preamble_set_naive.simps
    by (metis (mono_tags, lifting) list.case_eq_if option.distinct(1))   
qed






lemma calculate_preamble_set_naive_correctness : 
  assumes "observable M"
  shows "(\<exists> P . is_preamble_set M q P) = (\<exists> P . calculate_preamble_set_naive M q = Some P \<and> is_preamble_set M q P)"
  using calculate_preamble_set_naive_soundness[of M q] calculate_preamble_set_naive_exhaustiveness[OF assms, of q] by blast 


value[code] "calculate_preamble_set_naive M_ex 2"
value[code] "calculate_preamble_set_naive M_ex 3"
value[code] "calculate_preamble_set_naive M_ex 4"
value[code] "calculate_preamble_set_naive M_ex 5"

value[code] "calculate_preamble_set_naive M_ex_H 1"
value[code] "calculate_preamble_set_naive M_ex_H 2"
value[code] "calculate_preamble_set_naive M_ex_H 3"
value[code] "calculate_preamble_set_naive M_ex_H 4"



(* even more inefficient method to calculate preamble sets   
fun generate_sublist :: "'a list \<Rightarrow> bool list \<Rightarrow> 'a list" where
  "generate_sublist xs bs = map fst (filter snd (zip xs bs))"

value "generate_sublist [1::nat,2,3,4] [True,True,False,True]"

fun sublists_of_lists_of_length :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list list" where
  "sublists_of_lists_of_length xs k = map (generate_sublist (lists_of_length xs k)) (generate_selector_lists (length (lists_of_length xs k)))"

value "(lists_of_length [1::nat] 3)"
value "generate_selector_lists (length (lists_of_length [1::nat] 3))"
value "sublists_of_lists_of_length [1::nat] 3"

value "(lists_of_length [1::nat,2] 3)"
value "generate_selector_lists (length (lists_of_length [1::nat,2] 3))"
value "sublists_of_lists_of_length [1::nat,2] 3"


fun sublists_of_language_of_length :: "('a, 'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (Input \<times> Output) list list list" where
  "sublists_of_language_of_length M k = (let PS = paths_up_to_length M (initial M) k 
    in (map (\<lambda> sl . map p_io (generate_sublist PS sl)) (generate_selector_lists (length PS))))"

value "paths_up_to_length M_ex (initial M_ex) 7"
value "sublists_of_language_of_length M_ex 0"
value[code] "sublists_of_language_of_length M_ex 3"
value[code] "sublists_of_language_of_length M_ex_H 1"


fun calculate_preamble_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set option" where
  "calculate_preamble_naive M q = (case (filter (\<lambda> P . is_preamble_set M q (set P)) (sublists_of_language_of_length M  ( size M - 1 ) )) of
    [] \<Rightarrow> None |
    PS \<Rightarrow> (Some (set (hd PS))))" 

value[code] "calculate_preamble_naive M_ex 2"
value[code] "calculate_preamble_naive M_ex 3"
value[code] "calculate_preamble_naive M_ex 4"
value[code] "calculate_preamble_naive M_ex 5"
*)

fun trim_transitions :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme" where
  "trim_transitions M = M\<lparr> transitions := filter (\<lambda> t . t_source t \<in> nodes M) (wf_transitions M)\<rparr>"

lemma trim_transitions_paths : "path M (initial M) p = path (trim_transitions M) (initial (trim_transitions M)) p"
proof -
  have "h (trim_transitions M) \<subseteq> h M" by auto
  have "initial (trim_transitions M) = initial M" by auto
  
  have "path (trim_transitions M) (initial (trim_transitions M)) p \<Longrightarrow> path M (initial M) p"
    by (metis \<open>h (trim_transitions M) \<subseteq> h M\<close> \<open>initial (trim_transitions M) = initial M\<close> h_subset_path)
    
  moreover have "path M (initial M) p \<Longrightarrow> path (trim_transitions M) (initial (trim_transitions M)) p"
  proof (induction p rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc x xs)
    then have "path M (initial M) (xs)" and "path M (target xs (initial M)) [x]" 
      by auto
    
    have "x \<in> h M"
      using \<open>path M (target xs (initial M)) [x]\<close> by auto
    moreover have "t_source x \<in> nodes M"
      by (metis (no_types) \<open>path M (initial M) xs\<close> \<open>path M (target xs (initial M)) [x]\<close> nodes_path_initial path_cons_elim)
    ultimately have "x \<in> h (trim_transitions M)" 
      unfolding trim_transitions.simps by auto
    moreover have "path (trim_transitions M) (initial (trim_transitions M)) xs"
      using \<open>path M (initial M) (xs)\<close> snoc.IH by auto  
    ultimately show ?case
      using \<open>path M (target xs (initial M)) [x]\<close> by auto 
  qed

  ultimately show ?thesis by auto
qed

lemma trim_transitions_language : "L M = L (trim_transitions M)"
  using trim_transitions_paths unfolding LS.simps by blast


lemma is_submachine_from_filtering_wf_transitions :
  "is_submachine (M\<lparr>transitions := filter P (wf_transitions M)\<rparr>) M"
  by auto

lemma trim_transitions_nodes : "nodes M = nodes (trim_transitions M)"
  using trim_transitions_paths[of M] path_to_nodes[of _ M] path_to_nodes[of _ "trim_transitions M"]
  using is_submachine.elims(2) nodes.initial nodes_path subsetI subset_antisym is_submachine_from_filtering_wf_transitions trim_transitions.simps by metis
  
lemma trim_transitions_h : "h (trim_transitions M) \<subseteq> h M"
  unfolding trim_transitions.simps by auto


    
  



value "paths_up_to_length M_ex_H 1 5"
value "distinct_paths_up_to_length M_ex_H 1 100"
value "distinct_paths_up_to_length M_ex_H 1 1000"
value "distinct_paths_up_to_length M_ex_H 1 3 = distinct_paths_up_to_length M_ex_H 1 4"

value "nodes M_ex_H"
value "nodes_from_distinct_paths M_ex_H"

value "nodes_from_distinct_paths (product (from_FSM M_ex_H 1) (from_FSM M_ex_H 3))"
value "nodes (product (from_FSM M_ex_H 1) (from_FSM M_ex_H 3))"


(* state separator sets *)


definition canonical_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme" where
  "canonical_separator M q1 q2 = 
    (let PM = (product (from_FSM M q1) (from_FSM M q2)) in
      trim_transitions \<lparr> initial = Inl (initial PM),
        inputs = inputs M,
        outputs = outputs M,
        transitions = 
          (map (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t)) :: (('a \<times> 'a) + 'a) Transition) (transitions PM))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM)))))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM))))),
        \<dots> = FSM.more M \<rparr> :: (('a \<times> 'a) + 'a,'b) FSM_scheme)"



value[code] "(canonical_separator M_ex 2 3)"
value[code] "trim_transitions (canonical_separator M_ex 2 3)"

fun is_Inl :: "'a + 'b \<Rightarrow> bool" where
  "is_Inl (Inl x) = True" |
  "is_Inl (Inr x) = False"
fun is_state_separator_from_canonical_separator :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_state_separator_from_canonical_separator CSep q1 q2 S = (
    is_submachine S CSep 
    \<and> single_input S
    \<and> acyclic S
    \<and> deadlock_state S (Inr q1)
    \<and> deadlock_state S (Inr q2)
    \<and> ((Inr q1) \<in> nodes S)
    \<and> ((Inr q2) \<in> nodes S)
    \<and> (\<forall> q \<in> nodes S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (is_Inl q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> q \<in> nodes S . \<forall> x \<in> set (inputs CSep) . (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h CSep . t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))
)"


fun generate_choices :: "('a \<times> ('b list)) list \<Rightarrow> ('a \<times> 'b option) list list" where
  "generate_choices [] = [[]]" |
  "generate_choices (xys#xyss) = concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') (generate_choices xyss)) ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys))))"

value "generate_choices [(0::nat,[0::nat,1,2])]"
value "generate_choices [(0::nat,[0::nat,1,2]),(1,[10,20,30])]"

lemma concat_map_hd_tl_elem: 
  assumes "hd cs \<in> set P1"
  and     "tl cs \<in> set P2"
  and     "length cs > 0"
shows "cs \<in> set (concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') P2) P1))"
proof -
  have "hd cs # tl cs = cs" using assms(3) by auto
  moreover have "hd cs # tl cs \<in> set (concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') P2) P1))" using assms(1,2) by auto
  ultimately show ?thesis by auto
qed





lemma generate_choices_hd_tl : "cs \<in> set (generate_choices (xys#xyss)) = (length cs = length (xys#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices xyss)))"
proof (induction xyss arbitrary: cs xys)
  case Nil
  have "(cs \<in> set (generate_choices [xys])) = (cs \<in> set ([(fst xys, None)] # map (\<lambda>y. [(fst xys, Some y)]) (snd xys)))" 
    unfolding generate_choices.simps by auto
  moreover have "(length cs = length [xys] \<and>
     fst (hd cs) = fst xys \<and>
     (snd (hd cs) = None \<or> snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)) \<and>
     tl cs \<in> set (generate_choices [])) = (cs \<in> set ([(fst xys, None)] # map (\<lambda>y. [(fst xys, Some y)]) (snd xys)))"
    (* TODO: smt *)
    by (smt Suc_length_conv fst_conv generate_choices.simps(1) imageE image_eqI length_0_conv list.sel(1) list.sel(3) list.set_intros(1) list.set_sel(2) list.size(4) option.collapse option.sel prod.collapse set_ConsD set_map snd_conv tl_Nil)
    
  ultimately show ?case by blast
next
  case (Cons a xyss)

  have "length cs = length (xys#a#xyss) \<Longrightarrow> fst (hd cs) = fst xys \<Longrightarrow> (snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))) \<Longrightarrow> (tl cs \<in> set (generate_choices (a#xyss))) \<Longrightarrow> cs \<in> set (generate_choices (xys#a#xyss)) "
  proof -
    assume "length cs = length (xys#a#xyss)" and "fst (hd cs) = fst xys" and "(snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))" and "(tl cs \<in> set (generate_choices (a#xyss)))"
    then have "length cs > 0" by auto

    have "(hd cs) \<in> set ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys)))"
      using \<open>fst (hd cs) = fst xys\<close> \<open>(snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))\<close>
      by (metis (no_types, lifting) image_eqI list.set_intros(1) list.set_intros(2) option.collapse prod.collapse set_map)  
    
    show "cs \<in> set (generate_choices ((xys#(a#xyss))))"
      using generate_choices.simps(2)[of xys "a#xyss"] using concat_map_hd_tl_elem[OF \<open>(hd cs) \<in> set ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys)))\<close> \<open>(tl cs \<in> set (generate_choices (a#xyss)))\<close> \<open>length cs > 0\<close>] by auto
  qed

  moreover have "cs \<in> set (generate_choices (xys#a#xyss)) \<Longrightarrow> length cs = length (xys#a#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices (a#xyss)))"
  proof -
    assume "cs \<in> set (generate_choices (xys#a#xyss))"
    then have p3: "tl cs \<in> set (generate_choices (a#xyss))"
      using generate_choices.simps(2)[of xys "a#xyss"] by fastforce
    then have "length (tl cs) = length (a # xyss)" using Cons.IH[of "tl cs" "a"] by simp
    then have p1: "length cs = length (xys#a#xyss)" by auto

    have p2 : "fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))))"
      using \<open>cs \<in> set (generate_choices (xys#a#xyss))\<close> generate_choices.simps(2)[of xys "a#xyss"] by fastforce
    
    show ?thesis using p1 p2 p3 by simp
  qed

  ultimately show ?case by blast
qed 


lemma generate_choices_idx : "cs \<in> set (generate_choices xyss) = (length cs = length xyss \<and> (\<forall> i < length cs . (fst (cs ! i)) = (fst (xyss ! i)) \<and> ((snd (cs ! i)) = None \<or> ((snd (cs ! i)) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd (xyss ! i))))))"
proof (induction xyss arbitrary: cs)
  case Nil
  then show ?case by auto
next
  case (Cons xys xyss)


  have "(\<forall>i<length (tl cs).
                    fst (tl cs ! i) = fst (xyss ! i) \<and>
                    (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i))))
              = (\<forall>i<length (tl cs).
                    fst (cs ! (Suc i)) = fst ((xys#xyss) ! (Suc i)) \<and>
                    (snd (cs ! (Suc i)) = None \<or> snd (cs ! (Suc i)) \<noteq> None \<and> the (snd (cs ! (Suc i))) \<in> set (snd ((xys#xyss) ! (Suc i)))))" 
    using nth_tl by fastforce
  then have *: "(\<forall>i<length (tl cs).
                    fst (tl cs ! i) = fst (xyss ! i) \<and>
                    (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i))))
               = (\<forall>i<length cs. i > 0 \<longrightarrow>
                    (fst (cs ! i) = fst ((xys#xyss) ! i) \<and>
                      (snd (cs ! i) = None \<or> snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys#xyss) ! i)))))"
    (* TODO: smt *)
    by (smt Nitpick.size_list_simp(2) Suc_lessD Suc_mono Suc_pred less_SucE tl_Nil zero_less_Suc)

  have "cs \<in> set (generate_choices (xys#xyss)) = (length cs = length (xys#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices xyss)))"
    using generate_choices_hd_tl by metis

  then have "cs \<in> set (generate_choices (xys#xyss)) 
    = (length cs = length (xys#xyss) 
      \<and> fst (hd cs) = fst xys 
      \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) 
      \<and> (length (tl cs) = length xyss \<and>
        (\<forall>i<length (tl cs).
          fst (tl cs ! i) = fst (xyss ! i) \<and>
          (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i))))))"
    using Cons.IH[of "tl cs"] by blast
  then have "cs \<in> set (generate_choices (xys#xyss)) 
    = (length cs = length (xys#xyss) 
      \<and> fst (hd cs) = fst xys 
      \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) 
      \<and> (\<forall>i<length (tl cs).
          fst (tl cs ! i) = fst (xyss ! i) \<and>
          (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i)))))"
    by auto

  moreover have "length cs = length (xys#xyss) \<Longrightarrow> (fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))))) = 
          (fst (cs ! 0) = fst ((xys#xyss) ! 0) \<and> (snd (cs ! 0) = None \<or> snd (cs ! 0) \<noteq> None \<and> the (snd (cs ! 0)) \<in> set (snd ((xys#xyss) ! 0))))"
    by (metis hd_conv_nth length_greater_0_conv list.simps(3) nth_Cons_0)
    
  ultimately have "cs \<in> set (generate_choices (xys#xyss)) 
    = (length cs = length (xys#xyss)  
      \<and> (fst (cs ! 0) = fst ((xys#xyss) ! 0) \<and> (snd (cs ! 0) = None \<or> snd (cs ! 0) \<noteq> None \<and> the (snd (cs ! 0)) \<in> set (snd ((xys#xyss) ! 0))))
      \<and> (\<forall>i<length cs. i > 0 \<longrightarrow>
                    (fst (cs ! i) = fst ((xys#xyss) ! i) \<and>
                      (snd (cs ! i) = None \<or> snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys#xyss) ! i))))))"  
    using * by blast

  moreover have "length cs = length (xys#xyss) \<Longrightarrow> ((fst (cs ! 0) = fst ((xys#xyss) ! 0) \<and> (snd (cs ! 0) = None \<or> snd (cs ! 0) \<noteq> None \<and> the (snd (cs ! 0)) \<in> set (snd ((xys#xyss) ! 0))))
        \<and> (\<forall>i<length cs. i > 0 \<longrightarrow>
                      (fst (cs ! i) = fst ((xys#xyss) ! i) \<and>
                        (snd (cs ! i) = None \<or> snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys#xyss) ! i))))))
      = (\<forall>i<length cs.
           fst (cs ! i) = fst ((xys # xyss) ! i) \<and>
           (snd (cs ! i) = None \<or>
            snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys # xyss) ! i))))" 
    by fastforce

  ultimately show ?case by blast
qed



fun generate_submachine_from_assignment :: "('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> Input option) list \<Rightarrow> ('a, 'b) FSM_scheme" where
  "generate_submachine_from_assignment M assn = M\<lparr> transitions := filter (\<lambda> t . (t_source t, Some (t_input t)) \<in> set assn) (wf_transitions M)\<rparr>"

fun calculate_state_separator_from_canonical_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_from_canonical_separator_naive M q1 q2 = 
    (let CSep = canonical_separator M q1 q2 in
      find 
        (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) 
        (map 
          (\<lambda> assn . generate_submachine_from_assignment CSep assn) 
          (generate_choices 
            (map 
              (\<lambda>q . (q, filter 
                          (\<lambda>x . \<exists> t \<in> h CSep . t_source t = q \<and> t_input t = x) 
                          (inputs CSep))) 
              (nodes_from_distinct_paths CSep)))))"

value "(nodes_from_distinct_paths (canonical_separator M_ex_H 1 3))"
value "h (canonical_separator M_ex_H 1 3)"
value "(map (\<lambda>q . (q, filter (\<lambda>x . \<exists> t \<in> h (canonical_separator M_ex_H 1 3) . t_source t = q \<and> t_input t = x) (inputs (canonical_separator M_ex_H 1 3)))) (nodes_from_distinct_paths (canonical_separator M_ex_H 1 3)))"
value[code] "calculate_state_separator_from_canonical_separator_naive M_ex_H 1 4"



lemma trim_transitions_submachine : "is_submachine S M \<Longrightarrow> is_submachine (trim_transitions S) M"
  unfolding trim_transitions.simps is_submachine.simps by auto

lemma trim_transitions_single_input : "single_input S \<Longrightarrow> single_input (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_h[of S] unfolding trim_transitions.simps single_input.simps by blast

lemma trim_transitions_acyclic : "acyclic S \<Longrightarrow> acyclic (trim_transitions S)"
  using trim_transitions_paths[of S]  unfolding trim_transitions.simps acyclic.simps by simp

lemma trim_transitions_deadlock_state : "deadlock_state S q \<Longrightarrow> deadlock_state (trim_transitions S) q"
  using trim_transitions_h[of S] unfolding trim_transitions.simps deadlock_state.simps by blast

lemma trim_transitions_deadlock_state_nodes : assumes "q \<in> nodes S" shows "deadlock_state S q = deadlock_state (trim_transitions S) q"
proof -
  have "deadlock_state S q \<Longrightarrow> deadlock_state (trim_transitions S) q"
    using trim_transitions_deadlock_state by auto
  moreover have "deadlock_state (trim_transitions S) q \<Longrightarrow> deadlock_state S q" 
  proof (rule ccontr)
    assume "deadlock_state (trim_transitions S) q"  and "\<not> deadlock_state S q"
    then obtain t where "t\<in>h S" and "t_source t = q"
      unfolding deadlock_state.simps by blast
    then have "t \<in> h (trim_transitions S)"
      unfolding trim_transitions.simps using assms by auto
    then have "\<not>deadlock_state (trim_transitions S) q"
      unfolding deadlock_state.simps using \<open>t_source t = q\<close> by blast
    then show "False" 
      using \<open>deadlock_state (trim_transitions S) q\<close> by blast
  qed
  ultimately show ?thesis by blast
qed

lemma trim_transitions_t_source' : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes S"
  unfolding trim_transitions.simps by auto

lemma trim_transitions_t_source : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_t_source'[of t S] by blast

lemma trim_transitions_t_source_h : "t \<in> h (trim_transitions S) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_t_source[of t S] unfolding wf_transitions.simps by auto

lemma trim_transitions_transitions : "h (trim_transitions S) = set (transitions (trim_transitions S))"
  unfolding trim_transitions.simps by auto


  

lemma trim_transitions_state_separator_from_canonical_separator : 
  assumes "is_state_separator_from_canonical_separator CSep q1 q2 S"
  shows   "is_state_separator_from_canonical_separator CSep q1 q2 (trim_transitions S)"  
proof -
  have p1: "is_submachine (trim_transitions S) CSep \<and>
    single_input (trim_transitions S) \<and>
    FSM3.acyclic (trim_transitions S) \<and>
    deadlock_state (trim_transitions S) (Inr q1) \<and>
    deadlock_state (trim_transitions S) (Inr q2) \<and>
    Inr q1 \<in> nodes (trim_transitions S) \<and>
    Inr q2 \<in> nodes (trim_transitions S)"
    using assms unfolding is_state_separator_from_canonical_separator.simps  
    using trim_transitions_submachine[of S CSep]
    using trim_transitions_single_input[of S]
    using trim_transitions_acyclic[of S]
    using trim_transitions_deadlock_state[of S]
    using trim_transitions_nodes[of S] 
    by blast

  have "(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> is_Inl q \<and> \<not> deadlock_state S q)"
    using assms unfolding is_state_separator_from_canonical_separator.simps by blast
  then have p2: "(\<forall>q\<in>nodes (trim_transitions S). q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> is_Inl q \<and> \<not> deadlock_state (trim_transitions S) q)"
    using trim_transitions_nodes[of S]  trim_transitions_deadlock_state_nodes[of _ S] by blast

  have *: "(\<forall>q\<in>nodes S.
      \<forall>x\<in>set (inputs CSep).
         (\<exists>t\<in>h S. t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))"
    using assms unfolding is_state_separator_from_canonical_separator.simps by blast
  have p3: "\<And> q x . q\<in>nodes (trim_transitions S) \<Longrightarrow> x\<in>set (inputs CSep) \<Longrightarrow>
           (\<exists>t\<in>h (trim_transitions S). t_source t = q \<and> t_input t = x) \<Longrightarrow>
           (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h (trim_transitions S))"
    using trim_transitions_nodes[of S] trim_transitions_h[of S]
  proof -
    fix q x assume "q\<in>nodes (trim_transitions S)" and "x\<in>set (inputs CSep)" and "\<exists>t\<in>h (trim_transitions S). t_source t = q \<and> t_input t = x"
    then have "q \<in> nodes S" using  trim_transitions_nodes[of S]  by blast
    then have **: "(\<exists>t\<in>h S. t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S)"
      using \<open>x \<in> set (inputs CSep)\<close> * by blast
    
    obtain t where "t\<in>h (trim_transitions S)" and "t_source t = q" and "t_input t = x"
      using \<open>\<exists>t\<in>h (trim_transitions S). t_source t = q \<and> t_input t = x\<close> by blast
    then have "(\<exists>t\<in>h S. t_source t = q \<and> t_input t = x)" using trim_transitions_h[of S]  by blast
    then have "(\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S)" using ** by blast
    
    have "\<And> t' . t'\<in>h CSep \<Longrightarrow> t_source t' = q \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> h (trim_transitions S)"
    proof - 
      fix t' assume "t'\<in>h CSep" and "t_source t' = q" and "t_input t' = x"
      then have "t' \<in> h S"
        using \<open>(\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S)\<close> by blast
      then show "t' \<in> h (trim_transitions S)"
        unfolding trim_transitions.simps using \<open>t_source t' = q\<close> \<open>q \<in> nodes S\<close> \<open>t_input t' = x\<close> by auto
    qed
    then show "(\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h (trim_transitions S))" by blast
  qed

  from p1 p2 p3 show ?thesis unfolding  is_state_separator_from_canonical_separator.simps by blast
qed


lemma generate_submachine_for_contained_assn: "assn \<in> set assns \<Longrightarrow> generate_submachine_from_assignment CSep assn \<in> set (map (\<lambda> assn . generate_submachine_from_assignment CSep assn) assns)"
    by simp



lemma calculate_state_separator_from_canonical_separator_naive_soundness :
  assumes "calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S"
shows "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  using assms unfolding calculate_state_separator_from_canonical_separator_naive.simps 
  using find_condition[of "(is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2)"
                          "(map (generate_submachine_from_assignment (canonical_separator M q1 q2))
                             (generate_choices
                               (map (\<lambda>q. (q, filter (\<lambda>x. \<exists>t\<in>h (canonical_separator M q1 q2). t_source t = q \<and> t_input t = x) (inputs (canonical_separator M q1 q2))))
                                 (nodes_from_distinct_paths (canonical_separator M q1 q2)))))", of S] 
  by metis 

lemma calculate_state_separator_from_canonical_separator_naive_correctness :
  assumes "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  shows "\<exists> S' . calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S'"
proof -
  let ?CSep = "(canonical_separator M q1 q2)"
  from assms obtain S where "is_state_separator_from_canonical_separator ?CSep q1 q2 S" by blast
  let ?S = "trim_transitions S"

  have "is_state_separator_from_canonical_separator ?CSep q1 q2 ?S"
    using trim_transitions_state_separator_from_canonical_separator[OF \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 S\<close>] by assumption

  then have "is_submachine ?S ?CSep"
        and "single_input ?S"
        and "acyclic ?S"
        and "deadlock_state ?S (Inr q1)"
        and "deadlock_state ?S (Inr q2)"
        and "Inr q1 \<in> nodes ?S"
        and "Inr q2 \<in> nodes ?S"
        and "(\<forall>q\<in>nodes ?S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> is_Inl q \<and> \<not> deadlock_state ?S q)"
        and "(\<forall>q\<in>nodes ?S.
              \<forall>x\<in>set (inputs ?CSep).
                 (\<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h ?CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
    unfolding is_state_separator_from_canonical_separator.simps by linarith+

  let ?ncs = "nodes_from_distinct_paths ?CSep"
  let ?ns = "nodes_from_distinct_paths ?S"

  let ?cbc = "map (\<lambda>q. (q, filter (\<lambda>x. \<exists>t\<in>h ?CSep. t_source t = q \<and> t_input t = x) (inputs ?CSep)))"
  let ?cbs = "map (\<lambda>q. (q, filter (\<lambda>x. \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x) (inputs ?S)))"

  have "finite (nodes ?S)"
    by (simp add: nodes_finite) 
  moreover have "nodes ?S \<subseteq> nodes ?CSep"
    using submachine_nodes[OF \<open>is_submachine ?S ?CSep\<close>] by assumption
  moreover have "\<And> NS . finite NS \<Longrightarrow> NS \<subseteq> nodes ?CSep 
        \<Longrightarrow> \<exists> f . (\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
  proof -
    fix NS assume "finite NS" and "NS \<subseteq> nodes ?CSep"
    then show "\<exists> f . (\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
    proof (induction)
      case empty
      then show ?case by auto
    next
      case (insert s NS)
      then have "NS \<subseteq> nodes (canonical_separator M q1 q2)" by auto
      then obtain f where f_def : "(\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
        using insert.IH by blast
      
      show ?case proof (cases "s \<in> nodes ?S")
        case True
        then show ?thesis proof (cases "deadlock_state ?S s")
          case True
          let ?f = "f( s := None)"
          have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
          using \<open>s \<in> nodes ?S\<close> True f_def by auto
          then show ?thesis by blast
        next
          case False
          then obtain t where "t\<in>h ?S" and "t_source t = s"
            unfolding deadlock_state.simps by blast
          then have theEx: "\<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = t_input t" 
            using \<open>t_source t = s\<close> \<open>s \<in> nodes ?S\<close> by blast
          
          have "\<forall> t' \<in> h ?S . (t_source t' = s) \<longrightarrow> t_input t' = t_input t"
            using \<open>single_input ?S\<close> \<open>t_source t = s\<close> \<open>s \<in> nodes ?S\<close> unfolding single_input.simps
            by (metis \<open>t \<in> h ?S\<close>) 
          then have theAll: "\<And>x . (\<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x) \<Longrightarrow> x = t_input t"
            by blast


          let ?f = "f( s := Some (t_input t))"
          have "t_input t = (THE x .  \<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x)"
            using the_equality[of "\<lambda> x . \<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x" "t_input t", OF theEx theAll] by simp


          then have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> ?f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> ?f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
            using \<open>s \<in> nodes ?S\<close> False f_def by auto
          then show ?thesis by blast
        qed
      next
        case False
        let ?f = "f( s := None)"
        have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> ?f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> ?f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
            using False f_def by auto
        then show ?thesis by blast
      qed
    qed
  qed
  
  ultimately obtain f where f_def : "(\<forall> q . 
                                        (q \<notin> nodes ?S \<longrightarrow> f q = None) 
                                        \<and> (q \<in> nodes ?S \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) 
                                                            \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) 
                                                            \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
    by blast

  let ?assn = "map (\<lambda>q . (q,f q)) (nodes_from_distinct_paths ?CSep)"
  let ?possible_choices = "(map 
              (\<lambda>q . (q, filter 
                          (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = q \<and> t_input t = x) 
                          (inputs ?CSep))) 
              (nodes_from_distinct_paths ?CSep))"
  let ?filtered_transitions = "filter
        (\<lambda>t. (t_source t, Some (t_input t))
             \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep)))
        (wf_transitions ?CSep)"

  (* FSM equivalent to S but possibly with a different order of transitions *)
  let ?S' = "generate_submachine_from_assignment ?CSep ?assn"
  
  have p1: "length ?assn = length ?possible_choices" by auto

  have p2a: "(\<forall> i < length ?assn . (fst (?assn ! i)) = (fst (?possible_choices ! i)))"
    by auto
  have p2b: "(\<And> i . i < length ?assn \<Longrightarrow> ((snd (?assn ! i)) = None \<or> ((snd (?assn ! i)) \<noteq> None \<and> the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i)))))"
  proof -
    fix i assume "i < length ?assn"
    let ?q = "(fst (?assn ! i))"
    have "(fst (?possible_choices ! i)) = ?q" using p2a \<open>i < length ?assn\<close> by auto
    
    have "snd (?assn ! i) = f ?q"
      using \<open>i < length ?assn\<close> by auto 
    have "snd (?possible_choices ! i) = filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep)"
       using \<open>i < length ?assn\<close> p2a by auto 
    
     show "((snd (?assn ! i)) = None \<or> ((snd (?assn ! i)) \<noteq> None \<and> the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i))))" 
     proof (cases "?q \<in> nodes ?S")
      case True
      then show ?thesis proof (cases "deadlock_state ?S ?q")
        case True
        then have "f ?q = None" using f_def \<open>?q \<in> nodes ?S\<close> by blast
        then have "snd (?assn ! i) = None" using \<open>snd (?assn ! i) = f ?q\<close> by auto
        then show ?thesis by blast
      next
        case False
        then obtain x where "\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"
          unfolding deadlock_state.simps by blast
        then have "\<exists>! x . \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"
          using \<open>single_input ?S\<close> unfolding single_input.simps
          by (metis (mono_tags, lifting) True) 
        then have "(THE x .  \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x) = x"
          using the1_equality[of "\<lambda> x . \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"] \<open>\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x\<close> by blast
        moreover have "f ?q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x)"
          using False \<open>?q \<in> nodes ?S\<close> f_def by blast
        ultimately have "f ?q = Some x" 
          by auto

        moreover have "x \<in> set (filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep))"
          using \<open>is_submachine ?S ?CSep\<close>
        proof -
          obtain pp :: "('a \<times> 'a + 'a) \<times> integer \<times> integer \<times> ('a \<times> 'a + 'a)" where
            f1: "pp \<in> h ?S \<and> t_source pp = fst (map (\<lambda>s. (s, f s)) (nodes_from_distinct_paths (canonical_separator M q1 q2)) ! i) \<and> t_input pp = x"
            using \<open>\<exists>t\<in>h ?S. t_source t = fst (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths (canonical_separator M q1 q2)) ! i) \<and> t_input t = x\<close> by blast
          then have "(\<exists>p. p \<in> h (canonical_separator M q1 q2) \<and> t_source p = t_source pp \<and> t_input p = x) \<and> x \<in> set (inputs (canonical_separator M q1 q2))"
            by (metis (no_types) True \<open>is_submachine ?S (canonical_separator M q1 q2)\<close> \<open>nodes ?S \<subseteq> nodes (canonical_separator M q1 q2)\<close> h_contents(2) submachine_h subset_iff)
          then show ?thesis
            using f1 by auto
        qed 

        ultimately have "the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i))"
          using \<open>snd (?possible_choices ! i) = filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep)\<close> \<open>snd (?assn ! i) = f ?q\<close> by fastforce 

        then show ?thesis by auto
      qed
    next
      case False
      then have "snd (?assn ! i) = None" using \<open>snd (?assn ! i) = f ?q\<close> f_def by auto
      then show ?thesis by auto
    qed
  qed

  then have "?assn \<in> set (generate_choices ?possible_choices)"    
    using generate_choices_idx[of ?assn ?possible_choices] by auto


  have "set (transitions ?S) = set ?filtered_transitions"
  proof -
    have "\<And> t . t \<in> set (transitions ?S) \<Longrightarrow> t \<in> set (?filtered_transitions)"
    proof -
      fix t assume "t \<in> set (transitions ?S)"
      then have "t \<in> set (wf_transitions ?CSep)"
        using \<open>is_submachine ?S ?CSep\<close> unfolding is_submachine.simps by auto

      have "t \<in> h ?S"
        using trim_transitions_transitions \<open>t \<in> set (transitions ?S)\<close> by auto

      have "t_source t \<in> nodes ?S"
        using trim_transitions_t_source[OF \<open>t \<in> set (transitions ?S)\<close>] by assumption
      have "\<not> deadlock_state ?S (t_source t)"
        unfolding deadlock_state.simps using \<open>t \<in> h ?S\<close> by blast
      
      have the1: "\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t"
        using \<open>t \<in> h ?S\<close> by blast
      then have the2: "\<exists>! x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>single_input ?S\<close> unfolding single_input.simps
        by (metis (mono_tags, lifting) \<open>t_source t \<in> nodes ?S\<close>) 

      
      have "f (t_source t) = Some (t_input t)"
        using f_def \<open>t_source t \<in> nodes ?S\<close> \<open>\<not> deadlock_state ?S (t_source t)\<close> the1_equality[OF the2 the1] by fastforce 
      moreover have "t_source t \<in> nodes ?CSep"
        using \<open>t_source t \<in> nodes ?S\<close> submachine_nodes[OF \<open>is_submachine ?S ?CSep\<close>] by blast
      ultimately have "(t_source t, Some (t_input t)) \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep))"
        using nodes_code[of ?CSep] by fastforce
      
      then show "t \<in> set (?filtered_transitions)"
        using filter_list_set[OF \<open>t \<in> set (wf_transitions ?CSep)\<close>, of "(\<lambda> t . (t_source t, Some (t_input t)) \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep)))"] by blast
    qed

    moreover have "\<And> t . t \<in> set (?filtered_transitions) \<Longrightarrow> t \<in> set (transitions ?S)"
    proof -
      fix t assume a: "t\<in>set (?filtered_transitions)"
      then have "t \<in> set (wf_transitions ?CSep)" 
            and "(t_source t, Some (t_input t))
                        \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep))"
        by auto
      then have "f (t_source t) = Some (t_input t)" by auto 
      then have "f (t_source t) \<noteq> None" by auto
      moreover have "t_source t \<in> nodes ?S"
        using calculation f_def by auto
      moreover have "\<not>deadlock_state ?S (t_source t)"
      proof -
        show ?thesis
          by (meson calculation(1) f_def)
      qed
      ultimately have "f (t_source t) = Some (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)"
        using f_def by auto
      then have "t_input t = (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)"
        using \<open>f (t_source t) = Some (t_input t)\<close> by auto


      have "\<exists> x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>\<not>deadlock_state ?S (t_source t)\<close> unfolding deadlock_state.simps by blast
      then obtain x where the1: \<open>\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x\<close> by blast
      then have the2: "\<exists>! x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>single_input ?S\<close> unfolding single_input.simps
        by (metis (mono_tags, lifting) \<open>t_source t \<in> nodes ?S\<close>) 

      

      have "x = t_input t"
        using \<open>t_input t = (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)\<close> the1_equality[OF the2 the1] by auto
      then have "(\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t)"
        using the1 by blast

      have "t_input t \<in> set (inputs ?CSep)"
        using \<open>t \<in> set (wf_transitions ?CSep)\<close> by auto
      
      have "(\<forall>t'\<in>h ?CSep. t_source t' = t_source t \<and> t_input t' = t_input t \<longrightarrow> t' \<in> h ?S)"
        using \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 ?S\<close> unfolding is_state_separator_from_canonical_separator.simps
        using \<open>t_source t \<in> nodes ?S\<close>
              \<open>t_input t \<in> set (inputs ?CSep)\<close>
              \<open>\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t\<close> by blast
      then have "t \<in> h ?S"
        using \<open>t \<in> set (wf_transitions ?CSep)\<close> by blast
      then show "t \<in> set (transitions ?S)"
        using trim_transitions_transitions[of S] by blast
    qed

    ultimately show ?thesis by blast
  qed

  moreover have "set (transitions ?S') = set (?filtered_transitions)" 
    unfolding generate_submachine_from_assignment.simps by fastforce
  ultimately have "set (transitions ?S) = set (transitions ?S')"
    by blast
  then have "h ?S = h ?S'"
    using trim_transitions_transitions[of S] by fastforce


  

  have "?S' \<in> set (map (\<lambda> assn . generate_submachine_from_assignment ?CSep assn) (generate_choices ?possible_choices))"
    using generate_submachine_for_contained_assn[OF \<open>?assn \<in> set (generate_choices ?possible_choices)\<close>] by assumption


  have "is_state_separator_from_canonical_separator ?CSep q1 q2 ?S'"
    using \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 ?S\<close>

  
  
  have "calculate_state_separator_from_canonical_separator_naive M q1 q2\<noteq> None"
  




   

  ultimately have "?S \<in> set (map 
          (\<lambda> assn . generate_submachine_from_assignment ?CSep assn) 
          (generate_choices 
            (map 
              (\<lambda>q . (q, filter 
                          (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = q \<and> t_input t = x) 
                          (inputs ?CSep))) 
              (nodes_from_distinct_paths ?CSep))))"
        





  moreover have "?S = generate_submachine_from_assignment ?CSep ?assn"
    unfolding generate_submachine_from_assignment.simps

  have "  

  have 
  
  

  (* Idea: 
    - get choice from state_separator
    - show that choice is contained in generated choices
    - show that "equivalent" FSM is in generated submachines  
    *)








end (*



fun calculate_state_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = (let CSep = canonical_separator M q1 q2 in
    (case filter (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) (map trim_transitions (generate_submachines CSep)) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S))"


definition "M_ex_I = (\<lparr> 
                      initial = 2::integer, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (2,1,30,4),
                                      (3,1,10,5),
                                      (4,0,10,3),
                                      (4,2,20,2),
                                      (5,2,30,3)]\<rparr>) "
export_code calculate_state_separator_naive canonical_separator M_ex M_ex_H M_ex_I in Haskell module_name Main









fun these_list :: "'a option list \<Rightarrow> 'a list" where
  "these_list [] = []" |
  "these_list (x#xs) = (case x of
    None \<Rightarrow> these_list xs |
    Some x' \<Rightarrow> x'#(these_list xs))"

lemma these_list_set : "set (these_list xs) = Option.these (set xs)" 
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
     unfolding these_list.simps using Option.these_def[of "set xs"] by(cases "a = None"; auto)
qed


fun r_distinguishable_k_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) \<times> Input \<times> nat) list option" where
  "r_distinguishable_k_witness M q1 q2 0 = (case (find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M)) of
    None \<Rightarrow> None |
    Some x \<Rightarrow> Some [((q1,q2),x,0)])" |
  "r_distinguishable_k_witness M q1 q2 (Suc k) = (case r_distinguishable_k_witness M q1 q2 0 of 
    None \<Rightarrow> (case find (\<lambda> xr . \<not>(None \<in> set (snd xr))) (map (\<lambda> x . (x,(map (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) (filter (\<lambda>tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))))))) (inputs M)) of
              None \<Rightarrow> None |
              Some xrs \<Rightarrow> Some (((q1,q2), fst xrs,(Suc k))#(concat (these_list (snd xrs))))) |
    Some w \<Rightarrow> Some w)"
                    
value "r_distinguishable_k_witness M_ex_H 1 3 (size (product (from_FSM M_ex_H 1) (from_FSM M_ex_H 3)))"


fun r_distinguishable_k' :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k' M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k' M q1 q2 (Suc k) = (r_distinguishable_k' M q1 q2 0 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k))"


lemma r_distinguishable_0 : "r_distinguishable_k M q1 q2 0 \<Longrightarrow> r_distinguishable_k M q1 q2 k"
  using r_distinguishable_k.simps by (induction k; fast)

lemma r_distinguishable_inc : "r_distinguishable_k M q1 q2 k \<Longrightarrow> k' \<ge> k  \<Longrightarrow> r_distinguishable_k M q1 q2 k'"
proof (induction k arbitrary: q1 q2 k')
  case 0
  then show ?case using r_distinguishable_0[of M q1 q2] by auto 
next
  case (Suc k)
  then show ?case proof (cases "k' > Suc k")
    case True
    then obtain k'' where "Suc k'' = k'"
      using Suc_lessE by blast 
    then have "k \<le> k''" using True by auto
    
    have "r_distinguishable_k M q1 q2 k \<Longrightarrow> r_distinguishable_k M q1 q2 k''" 
      using Suc.IH[of _ _ k'', OF _ \<open>k \<le> k''\<close>] by blast
    moreover have "
      (\<exists>x\<in>set (inputs M).
        \<forall>t1\<in>h M.
           \<forall>t2\<in>h M.
              t_source t1 = q1 \<and>
              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
              r_distinguishable_k M (t_target t1) (t_target t2) k)
    \<Longrightarrow> 
      (\<exists>x\<in>set (inputs M).
        \<forall>t1\<in>h M.
           \<forall>t2\<in>h M.
              t_source t1 = q1 \<and>
              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
              r_distinguishable_k M (t_target t1) (t_target t2) k'')" 
      using Suc.IH[of _ _ k'', OF _ \<open>k <= k''\<close>] by blast
    ultimately have "r_distinguishable_k M q1 q2 (Suc k) \<Longrightarrow> r_distinguishable_k M q1 q2 (Suc k'')"
      unfolding r_distinguishable_k.simps(2) by blast
  
    then show ?thesis using \<open>Suc k'' = k'\<close> Suc.prems(1) by fast
  next
    case False
    then have "Suc k = k'" using Suc.prems(2) by auto
    then show ?thesis using Suc.prems(1) by simp
  qed
qed

lemma r_distinguishable_0' : "r_distinguishable_k' M q1 q2 0 \<Longrightarrow> r_distinguishable_k' M q1 q2 k"
  using r_distinguishable_k'.simps by (induction k; fast)

lemma r_distinguishable_inc' : "r_distinguishable_k' M q1 q2 k \<Longrightarrow> k' \<ge> k  \<Longrightarrow> r_distinguishable_k' M q1 q2 k'"
proof (induction k arbitrary: q1 q2 k')
  case 0
  then show ?case using r_distinguishable_0'[of M q1 q2] by auto 
next
  case (Suc k)
  then show ?case proof (cases "k' > Suc k")
    case True
    then obtain k'' where "Suc k'' = k'"
      using Suc_lessE by blast 
    then have "k \<le> k''" using True by auto
    
    have "
      (\<exists>x\<in>set (inputs M).
        \<forall>t1\<in>h M.
           \<forall>t2\<in>h M.
              t_source t1 = q1 \<and>
              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
              r_distinguishable_k' M (t_target t1) (t_target t2) k)
    \<Longrightarrow> 
      (\<exists>x\<in>set (inputs M).
        \<forall>t1\<in>h M.
           \<forall>t2\<in>h M.
              t_source t1 = q1 \<and>
              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
              r_distinguishable_k' M (t_target t1) (t_target t2) k'')" 
      using Suc.IH[of _ _ k'', OF _ \<open>k <= k''\<close>] by blast
    then have "r_distinguishable_k' M q1 q2 (Suc k) \<Longrightarrow> r_distinguishable_k' M q1 q2 (Suc k'')"
      unfolding r_distinguishable_k'.simps(2) by blast
  
    then show ?thesis using \<open>Suc k'' = k'\<close> Suc.prems(1) by fast
  next
    case False
    then have "Suc k = k'" using Suc.prems(2) by auto
    then show ?thesis using Suc.prems(1) by simp
  qed
qed

lemma r_distinguishable_k'_eq : "r_distinguishable_k M q1 q2 k = r_distinguishable_k' M q1 q2 k"
proof (induct k arbitrary: q1 q2)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then have "r_distinguishable_k' M q1 q2 0 \<Longrightarrow> r_distinguishable_k M q1 q2 0" by auto
  then have "r_distinguishable_k' M q1 q2 0 \<Longrightarrow> r_distinguishable_k M q1 q2 k" using r_distinguishable_inc[of M _ _ 0 k] by auto
  moreover have *: "((\<exists>x\<in>set (inputs M).
         \<forall>t1\<in>h M.
            \<forall>t2\<in>h M.
               t_source t1 = q1 \<and>
               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
               r_distinguishable_k' M (t_target t1) (t_target t2) k))
        = ((\<exists>x\<in>set (inputs M).
           \<forall>t1\<in>h M.
              \<forall>t2\<in>h M.
                 t_source t1 = q1 \<and>
                 t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                 r_distinguishable_k M (t_target t1) (t_target t2) k))"
    using Suc.hyps by blast
  ultimately have **: "r_distinguishable_k' M q1 q2 (Suc k) \<Longrightarrow> r_distinguishable_k M q1 q2 (Suc k)"
    using r_distinguishable_k'.simps(2)[of M q1 q2 k] r_distinguishable_k.simps(2)[of M q1 q2 k] by blast

  have "r_distinguishable_k M q1 q2 k \<Longrightarrow> r_distinguishable_k' M q1 q2 (Suc k)" using Suc.hyps[of q1 q2] r_distinguishable_inc'[of M q1 q2 k "Suc k"] by auto
  then have "r_distinguishable_k M q1 q2 (Suc k) \<Longrightarrow> r_distinguishable_k' M q1 q2 (Suc k)"
    using r_distinguishable_k'.simps(2)[of M q1 q2 k] r_distinguishable_k.simps(2)[of M q1 q2 k] * by blast
    
  then show ?case using ** by fast
qed


(*
fun r_distinguishable_k_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) \<times> Input) list option" where
  "r_distinguishable_k_witness M q1 q2 0 = (case (find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M)) of
    None \<Rightarrow> None |
    Some x \<Rightarrow> Some [((q1,q2),x)])" |
  "r_distinguishable_k_witness M q1 q2 (Suc k) = (case r_distinguishable_k_witness M q1 q2 0 of 
    None \<Rightarrow> (case find (\<lambda> xr . \<not>(None \<in> set (snd xr))) (map (\<lambda> x . (x,(map (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) (filter (\<lambda>tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))))))) (inputs M)) of
              None \<Rightarrow> None |
              Some (x,rs) \<Rightarrow> Some (((q1,q2),x)#(concat (these_list rs)))) |
    Some w \<Rightarrow> Some w)"
*)

lemma image_elem_2: "z \<notin> {f x y | x y . P x y} \<Longrightarrow> \<forall> x y . P x y \<longrightarrow> f x y \<noteq> z"
  by blast 

lemma image_elem_2': "\<forall> x y . P x y \<longrightarrow> f x y \<noteq> z \<Longrightarrow> z \<notin> {f x y | x y . P x y}"
  by blast 

lemma find_not_None_elem : "(find P xs \<noteq> None) = (\<exists> x \<in> set xs . P x)"
  by (metis find_None_iff)

lemma r_distinguishable_k_witness_ex_set_helper : "\<And> x f XS P . (\<exists> xfx \<in> {(x,f x) | x . x \<in> XS} . P (snd xfx)) = (\<exists> x \<in> XS . P (f x))"
  by auto 

lemma r_distinguishable_k_witness_ex_find_helper : "((case find P XS of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x)) = None) = (find P XS = None)"
  by (simp add: option.case_eq_if) 
  

lemma r_distinguishable_k_witness_ex' : 
  shows  "r_distinguishable_k' M q1 q2 k = (r_distinguishable_k_witness M q1 q2 k \<noteq> None)"
proof (induction k arbitrary: q1 q2 rule: less_induct)
  case (less k')
  then show ?case proof (cases k')
    case 0
    then show ?thesis unfolding r_distinguishable_k'.simps r_distinguishable_k_witness.simps 
      using find_None_iff[of "(\<lambda>x. \<not> (\<exists>t1\<in>h M.
                        \<exists>t2\<in>h M.
                           t_source t1 = q1 \<and>
                           t_source t2 = q2 \<and>
                           t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" "(inputs M)"] by fastforce  
  next
    case (Suc k)
    then have "0 < k'" by auto
    have "k < k'" using Suc by auto

    show ?thesis proof (cases "r_distinguishable_k' M q1 q2 0")
      case True
      then have "r_distinguishable_k_witness M q1 q2 0 \<noteq> None" using less[OF \<open>0 < k'\<close>, of q1 q2] by auto
      then have "r_distinguishable_k_witness M q1 q2 (Suc k) \<noteq> None" 
        using r_distinguishable_k_witness.simps(2)[of M q1 q2 k] by auto
      moreover have "r_distinguishable_k' M q1 q2 (Suc k)"
        using r_distinguishable_0' True by auto
      ultimately show ?thesis using Suc by auto   
    next
      case False
      then have "r_distinguishable_k_witness M q1 q2 0 = None" using less[OF \<open>0 < k'\<close>, of q1 q2] by auto
      then have rdw_def : "r_distinguishable_k_witness M q1 q2 (Suc k) = 
                  (case find (\<lambda>xr. None \<notin> set (snd xr))
                    (map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt))
                                              (t_target (snd tt)) k)
                                    (filter
                                      (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                            t_source (snd tt) = q2 \<and>
                                            t_input (fst tt) = x \<and>
                                            t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                                      (concat
                                        (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
                       (inputs M)) of
                    None \<Rightarrow> None | Some xrs \<Rightarrow> Some (((q1, q2), fst xrs, (Suc k)) # concat (these_list (snd xrs))))" 
        using r_distinguishable_k_witness.simps(2)[of M q1 q2 k] by auto

      let ?tts = "(concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M)))"
      let ?ttsf = "\<lambda> x . (filter (\<lambda>tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)) ?tts)"
      let ?ttsfd = "\<lambda> x . map (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) (?ttsf x)"
      let ?xtt = "map (\<lambda> x . (x,?ttsfd x)) (inputs M)"
      let ?fxtt = "find (\<lambda> xr . \<not>(None \<in> set (snd xr))) ?xtt"
      
      have "set ?tts = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M}"
        by (metis (no_types) cartesian_product_list.simps cartesian_product_list_set)
      then have "\<And> x . set (?ttsf x) = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
        by auto
      then have "\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
        by auto
      then have "\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
      proof -
        fix x     
        have "set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          using \<open>\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . (t1,t2) \<in> {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }}"
          by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by force
        finally show "set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by fast
      qed
      
      have *: "\<And> x . \<not>(None \<in> set (?ttsfd x)) \<Longrightarrow> \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k"
      proof -
        fix x assume "\<not>(None \<in> set (?ttsfd x))"
        then have "None \<notin> {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          using \<open>\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
        then have "\<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None"
          using image_elem_2[of None "\<lambda> t1 t2 . r_distinguishable_k_witness M (t_target t1) (t_target t2) k" "\<lambda> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"] by blast
        then show "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k"    
          using less[OF \<open>k < k'\<close>] by blast
      qed
      moreover have **: "\<And> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k \<Longrightarrow> \<not>(None \<in> set (?ttsfd x))"
      proof -
        fix x assume "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k"
        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None"
          using less[OF \<open>k < k'\<close>] by blast
        then show "\<not>(None \<in> set (?ttsfd x))"
          using image_elem_2'[of "\<lambda> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2" "\<lambda> t1 t2 . r_distinguishable_k_witness M (t_target t1) (t_target t2) k" None] 
          \<open>\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
      qed
      
      

      

          
      have "set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}"      
        by auto
      have "(?fxtt \<noteq> None) = (\<exists> xtt \<in> set ?xtt . None \<notin> set (snd xtt))" 
        using find_not_None_elem[of "(\<lambda>xr. None \<notin> set (snd xr))" ?xtt] by blast
      then have "(?fxtt \<noteq> None) = (\<exists> x \<in> set (inputs M) . \<not>(None \<in> set (?ttsfd x)))"
        using \<open>set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}\<close> r_distinguishable_k_witness_ex_set_helper[of ?ttsfd "set (inputs M)" "\<lambda> sd . None \<notin> set sd"] by blast

      moreover have "(r_distinguishable_k_witness M q1 q2 (Suc k) = None) = (?fxtt = None)"
        using r_distinguishable_k_witness_ex_find_helper[of "\<lambda> xrs . Some (((q1, q2), fst xrs, Suc k) # concat (these_list (snd xrs)))" "(\<lambda>xr. None \<notin> set (snd xr))"  "(map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt))
                                    k)
                          (filter
                            (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                  t_source (snd tt) = q2 \<and>
                                  t_input (fst tt) = x \<and>
                                  t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                            (concat (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
             (inputs M))" ] using rdw_def  by fastforce
      ultimately have "r_distinguishable_k_witness M q1 q2 (Suc k) \<noteq> None = (\<exists> x \<in> set (inputs M) . \<not>(None \<in> set (?ttsfd x)))" 
        by auto

      also have "\<dots> = (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k)"
        using * ** by blast
      also have "\<dots> = r_distinguishable_k' M q1 q2 (Suc k)"
        unfolding r_distinguishable_k'.simps by blast
      finally show ?thesis using \<open>k' = Suc k\<close> by simp
    qed
  qed
qed

lemma r_distinguishable_k_witness_ex : 
  "r_distinguishable_k M q1 q2 k = (r_distinguishable_k_witness M q1 q2 k \<noteq> None)"
  using r_distinguishable_k_witness_ex' r_distinguishable_k'_eq by metis


(*
(* note: k is off-by-one w.r.t. standard definition *)
fun r_distinguishable_k'' ::  "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k'' M q1 q2 0 = False" |
  "r_distinguishable_k'' M q1 q2 (Suc k) = (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k'' M (t_target t1) (t_target t2) k)"

value "r_distinguishable_k'' M_ex_H 1 3 10"
*)



lemma r_distinguishable_k_witness_hd: 
  assumes "r_distinguishable_k_witness M q1 q2 k = Some wt"
  shows   "wt \<noteq> [] \<and> fst (fst (hd wt)) = q1 \<and> snd (fst (hd wt)) = q2 \<and> fst (snd (hd wt)) \<in> set (inputs M) \<and> snd (snd (hd wt)) \<le> k \<and>
            (\<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst (snd (hd wt)) \<and> t_input t2 = fst (snd (hd wt)) \<and> t_output t1 = t_output t2) 
            \<or> (k > 0 \<and> (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst (snd (hd wt)) \<and> t_input t2 = fst (snd (hd wt)) \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (snd (snd (hd wt)) - 1))))"
using assms proof (induction k arbitrary: q1 q2 wt rule: less_induct)
  case (less k')
  then show ?case proof (cases k')
    case 0
    then obtain x where x_ob : "find (\<lambda>x. \<not> (\<exists>t1\<in>h M. \<exists>t2\<in>h M. t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x"
      using less.prems r_distinguishable_k_witness.simps(1)[of M q1 q2]
      by fastforce
    then have *: "\<not> (\<exists>t1\<in>h M.
                       \<exists>t2\<in>h M.
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)" and "x \<in> set (inputs M)"
      using find_condition[OF x_ob] find_set[OF x_ob] by linarith+
    

    have "wt = [((q1, q2), x, 0)]"
      using x_ob 0 less.prems r_distinguishable_k_witness.simps(1)[of M q1 q2] by simp
    then have "wt \<noteq> [] \<and>
                fst (fst (hd wt)) = q1 \<and>
                snd (fst (hd wt)) = q2 \<and>
                fst (snd (hd wt)) \<in> set (inputs M) \<and> snd (snd (hd wt)) \<le> k'" and "fst (snd (hd wt)) = x" using \<open>x \<in> set (inputs M)\<close> by simp+
    then show ?thesis using * by auto
  next
    case (Suc k)
    then have "0 < k'" and "k < k'" and "Suc k = k'" and "0-1 \<le> k'-1" and "k' - 1 = k"  by auto
    then have "r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt" using less.prems by auto

    show ?thesis proof (cases "r_distinguishable_k_witness M q1 q2 0 \<noteq> None")
      case True
      then have "r_distinguishable_k_witness M q1 q2 0 = Some wt"
        using \<open>r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt\<close> unfolding r_distinguishable_k_witness.simps(2) by auto
      show ?thesis
        using less.IH[OF \<open>0 < k'\<close> \<open>r_distinguishable_k_witness M q1 q2 0 = Some wt\<close>] \<open>0 < k'\<close> by auto
    next
      case False

      let ?tts = "(concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M)))"
      let ?ttsf = "\<lambda> x . (filter (\<lambda>tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)) ?tts)"
      let ?ttsfd = "\<lambda> x . map (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) (?ttsf x)"
      let ?xtt = "map (\<lambda> x . (x,?ttsfd x)) (inputs M)"
      let ?fxtt = "find (\<lambda> xr . \<not>(None \<in> set (snd xr))) ?xtt"

      (* TODO: refactor code-duplication *)
      have "set ?tts = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M}"
        by (metis (no_types) cartesian_product_list.simps cartesian_product_list_set)
      then have "\<And> x . set (?ttsf x) = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
        by auto
      then have "\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
        by auto
      then have ***: "\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
      proof -
        fix x     
        have "set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          using \<open>\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . (t1,t2) \<in> {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }}"
          by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by blast
        also have "\<dots> = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by force
        finally show "set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by fast
      qed

      have ****: "set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}"      
        by auto


      from False have "r_distinguishable_k_witness M q1 q2 (Suc k) = (case ?fxtt of
                        None \<Rightarrow> None | Some xrs \<Rightarrow> Some (((q1, q2), fst xrs, Suc k) # concat (these_list (snd xrs))))"
        using \<open>r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt\<close> unfolding r_distinguishable_k_witness.simps(2) by auto
      then have *: "(case ?fxtt of
                        None \<Rightarrow> None | Some xrs \<Rightarrow> Some (((q1, q2), fst xrs, Suc k) # concat (these_list (snd xrs)))) = Some wt"
        using \<open>r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt\<close> by auto
      then obtain xrs where **: "?fxtt = Some xrs"
        by (metis (no_types, lifting) option.case_eq_if option.collapse option.distinct(1)) 
      
      have "None \<notin> set (snd xrs)" and "xrs \<in> set ?xtt"
        using find_condition[OF **] find_set[OF **] by fast+
      then have "xrs \<in> {(x,?ttsfd x) | x . x \<in> set (inputs M)}"
        using **** by metis
      then have "xrs = (fst xrs, ?ttsfd (fst xrs))" and "fst xrs \<in> set (inputs M)"  by fastforce+
      have "snd xrs = ?ttsfd (fst xrs)" 
        using BNF_Def.sndI[OF \<open>xrs = (fst xrs, ?ttsfd (fst xrs))\<close>] by assumption
      then have "set (snd xrs) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst xrs \<and> t_input t2 = fst xrs \<and> t_output t1 = t_output t2 }"  
        using *** by metis      
      then have "None \<notin> {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst xrs \<and> t_input t2 = fst xrs \<and> t_output t1 = t_output t2 }"
        using \<open>None \<notin> set (snd xrs)\<close> by auto

      have "wt = ((q1, q2), fst xrs, Suc k) # concat (these_list (snd xrs))"
        using * ** by fastforce
      then have "fst (snd (hd wt)) = fst xrs" and "snd (snd (hd wt)) = Suc k" by auto

      have p2: "snd (snd (hd wt)) \<le> k'" and "k' - 1 = snd (snd (hd wt)) - 1"
        using \<open>snd (snd (hd wt)) = Suc k\<close>  \<open>Suc k = k'\<close> by auto

      have "\<And> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst xrs \<and> t_input t2 = fst xrs \<and> t_output t1 = t_output t2) \<Longrightarrow> (r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None)"
        using FSM3.image_elem_2[OF \<open>None \<notin> {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst xrs \<and> t_input t2 = fst xrs \<and> t_output t1 = t_output t2 }\<close>] by blast
      
      then have "\<And> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst xrs \<and> t_input t2 = fst xrs \<and> t_output t1 = t_output t2) \<Longrightarrow> (r_distinguishable_k' M (t_target t1) (t_target t2) k)"
        using r_distinguishable_k_witness_ex'[of M _ _ k] by blast
      then have "(\<forall>t1\<in>h M. \<forall>t2\<in>h M. t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst (snd (hd wt)) \<and> t_input t2 = fst (snd (hd wt)) \<and> t_output t1 = t_output t2 \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) (k' - 1))"
        using \<open>k' - 1 = k\<close> \<open>fst (snd (hd wt)) = fst xrs\<close> by fastforce
      then have p3 : "(\<forall>t1\<in>h M. \<forall>t2\<in>h M. t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = fst (snd (hd wt)) \<and> t_input t2 = fst (snd (hd wt)) \<and> t_output t1 = t_output t2 \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (snd (snd (hd wt)) - 1))"
        using r_distinguishable_k'_eq \<open>k' - 1 = snd (snd (hd wt)) - 1\<close> by fastforce
      
      have p1:  "wt \<noteq> [] \<and> fst (fst (hd wt)) = q1 \<and> snd (fst (hd wt)) = q2 \<and> fst (snd (hd wt)) \<in> set (inputs M)"
        using \<open>wt = ((q1, q2), fst xrs, Suc k) # concat (these_list (snd xrs))\<close> \<open>fst xrs \<in> set (inputs M)\<close> by auto

      
      
      show ?thesis using p1 p2 \<open>0 < k'\<close> p3 by auto
    qed
  qed
qed
      
      
      
      

      

fun construct_r_distinguishing_set_from_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> (('a \<times> 'a) \<times> Input \<times> nat) list \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme" where
  "construct_r_distinguishing_set_from_witness M q1 q2 w = (let CSep = canonical_separator M q1 q2 in
    CSep\<lparr> transitions := filter (\<lambda> t . (t_source t, t_input t) \<in> set (map (\<lambda> wt . (Inl (fst wt),fst (snd wt)))  w)) (transitions CSep)\<rparr>)"     

fun construct_r_distinguishing_set_by_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme option" where
  "construct_r_distinguishing_set_by_witness M q1 q2 = (case r_distinguishable_k_witness M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) of
    None \<Rightarrow> None |
    Some w \<Rightarrow> Some (construct_r_distinguishing_set_from_witness M q1 q2 w))"

value "construct_r_distinguishing_set_by_witness M_ex_H 1 1"
value "construct_r_distinguishing_set_by_witness M_ex_H 1 3"
value "construct_r_distinguishing_set_by_witness M_ex_9 0 3"
          


lemma x: 
  assumes "construct_r_distinguishing_set_by_witness M q1 q2 = Some S"
  shows "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"








end (*

(*
fun r_distinguishable_k' :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k' M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k' M q1 q2 (Suc k) = (r_distinguishable_k' M q1 q2 0 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k))"
*)

fun r_distinguishable_by :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) \<times> Input) list \<Rightarrow> bool" where
  "r_distinguishable_by M q1 q2 0 [] = False" |
  "r_distinguishable_by M q1 q2 0 (qqx#qqxs) =
    (qqxs = [] \<and> fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M) \<and> \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_by M q1 q2 (Suc k) wt = ((r_distinguishable_by M q1 q2 0 wt) \<or> 
    (case filter (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
      [] \<Rightarrow> False |
      qqx#qqxs \<Rightarrow> qqxs = [] 
                  \<and> (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt))))"

value "r_distinguishable_by M_ex_H 1 3 1 [((1,3),1),((4,3),0)]"
value "r_distinguishable_by M_ex_H 1 3 1 [((1,3),1),((4,3),0),((2,3),5)]"

lemma r_distinguishable_by_minimal : 
  assumes "r_distinguishable_by M q1 q2 k wt"
shows "\<forall> qqx \<in> set wt . (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst qqx) \<and> t_source t2 = snd (fst qqx) \<and> t_input t1 = (snd qqx) \<and> t_input t2 = (snd qqx) \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> j \<le> k . r_distinguishable_k' M (t_target t1) (t_target t2) j))"
using assms proof (induction k arbitrary: q1 q2 wt rule: less_induct)
  case (less k')
  then show ?case proof (cases k')
    case 0
    then have "wt \<noteq> []" using r_distinguishable_by.simps[of M q1 q2] less.prems(1) by auto
    let ?qqx = "hd wt"
    have "wt = [?qqx]" using \<open>r_distinguishable_by M q1 q2 k' wt\<close> r_distinguishable_by.simps(1-2)[of M q1 q2]
      by (metis "0" hd_Cons_tl)
       
    then have "fst (fst ?qqx) = q1 \<and>
               snd (fst ?qqx) = q2 \<and>
               snd ?qqx \<in> set (inputs M) \<and>
               \<not> (\<exists>t1\<in>h M.
                      \<exists>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                 t_input t1 = snd ?qqx \<and> t_input t2 = snd ?qqx \<and> t_output t1 = t_output t2)" 
      using 0 \<open>r_distinguishable_by M q1 q2 k' wt\<close> r_distinguishable_by.simps(2)[of M q1 q2 ?qqx "[]"]
      by auto
    then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst ?qqx) \<and> t_source t2 = snd (fst ?qqx) \<and> t_input t1 = (snd ?qqx) \<and> t_input t2 = (snd ?qqx) \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) 0"
      by blast
    moreover have "set wt = {?qqx}" using \<open>wt = [?qqx]\<close>
      by (metis list.set(1) list.simps(15))   
    ultimately show ?thesis by auto
  next
    case (Suc k)
    then have "0 < k'" and "k < k'" and "k < Suc k" by auto
    

    show ?thesis proof (cases "(r_distinguishable_by M q1 q2 0 wt)")
      case True
      show ?thesis using less.IH[OF \<open>0 < k'\<close> True] by blast
    next
      case False
      moreover have "r_distinguishable_by M q1 q2 (Suc k) wt" using less.prems(1) Suc by auto
      ultimately have c: "(case filter (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
        [] \<Rightarrow> False |
        qqx#qqxs \<Rightarrow> qqxs = [] 
                    \<and> (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt)))"
        unfolding r_distinguishable_by.simps(3) by auto
      then obtain qqx where "filter (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt = [qqx]"
        by (smt hd_Cons_tl list.case_eq_if)   (* TODO: smt *)
      then have "(\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt))"
        using c by auto
      then have "(\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt))"
        using less.IH[OF \<open>k < k'\<close>, of _ _ "removeAll qqx wt"] 
      
      have "\<And> t1 t2 . t1 \<in> h M \<Longrightarrow> t2 \<in> h M \<Longrightarrow> (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<Longrightarrow> (\<exists> j \<le> k . r_distinguishable_k' M (t_target t1) (t_target t2) j)"
      proof -
        fix t1 t2 assume "t1 \<in> h M" and "t2 \<in> h M" and "(t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2)"
        then have "r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt)"
          using \<open>(\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt))\<close>
          by blast
        then have "(removeAll qqx wt) \<noteq> []" using r_distinguishable_by.simps[of M "t_target t1" "t_target t2"]
          by (metis (no_types, lifting) \<open>k < Suc k\<close> filter.simps(1) less_Suc_eq_0_disj list.simps(4))

        show "(\<exists> j \<le> k . r_distinguishable_k' M (t_target t1) (t_target t2) j)" 
        proof (cases k)
          case 0
          then have "r_distinguishable_by M (t_target t1) (t_target t2) 0 (removeAll qqx wt)"
            using \<open>r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt)\<close> by auto
          let ?qqx = "hd (removeAll qqx wt)"
          have "(removeAll qqx wt) = [?qqx]"
            using \<open>(removeAll qqx wt) \<noteq> []\<close> \<open>r_distinguishable_by M (t_target t1) (t_target t2) 0 (removeAll qqx wt)\<close> r_distinguishable_by.simps(1-2)[of M "t_target t1" "t_target t2" ]
            by (metis (no_types) hd_Cons_tl)
          then have "fst (fst ?qqx) = t_target t1 \<and>
               snd (fst ?qqx) = t_target t2 \<and>
               snd ?qqx \<in> set (inputs M) \<and>
               \<not> (\<exists>t1a\<in>h M.
                      \<exists>t2a\<in>h M.
                         t_source t1a = t_target t1 \<and>
                         t_source t2a = t_target t2 \<and>
                 t_input t1a = snd ?qqx \<and> t_input t2a = snd ?qqx \<and> t_output t1a = t_output t2a)" 
            using 0 \<open>r_distinguishable_by M (t_target t1) (t_target t2) 0 (removeAll qqx wt)\<close> r_distinguishable_by.simps(2)[of M "t_target t1" "t_target t2" ?qqx "[]"]
            by auto
          

          then show ?thesis 
            using less.IH[OF \<open>k < k'\<close> \<open>r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt)\<close>] 
        next
          case (Suc nat)
          then show ?thesis sorry
        qed
        
        
        
        then obtain qqx' where "qqx' \<in> set (removeAll qqx wt)"
          using last_in_set by blast 
        

      then have "(\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> j \<le> k . r_distinguishable_k' M (t_target t1) (t_target t2) j))"
        using less.IH[OF \<open>k < k'\<close> \<open>r_distinguishable_by M (t_target t1) (t_target t2) k (removeAll qqx wt)\<close>] 
        


      then show ?thesis sorry
    qed
    
  qed
qed 



fun r_distinguishable_k'_by :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) \<times> Input) list \<Rightarrow> bool" where
  "r_distinguishable_k'_by M q1 q2 0 wt = (case find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
    None \<Rightarrow> False |
    Some qqx \<Rightarrow> \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k'_by M q1 q2 (Suc k) wt = ((r_distinguishable_k'_by M q1 q2 0 wt) \<or> 
    (case find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
      None \<Rightarrow> False |
      Some qqx \<Rightarrow> \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt))"



lemma sublist_property_cover_ex : "(\<forall> x \<in> set xs . \<forall> y \<in> set xs . \<exists> xs' . P x y xs') \<Longrightarrow> (\<exists> xs'' . (\<forall> x \<in> set xs . \<forall> y \<in> set xs . \<exists> xs' . set xs' \<subseteq> set xs'' \<and> P x y xs') \<and> (\<forall> x'' \<in> set xs'' . \<exists> x \<in> set xs . \<exists> y \<in> set xs . \<exists> xs' . set xs' \<subseteq> set xs'' \<and> P x y xs' \<and> x'' \<in> set xs'))"
proof -
  assume "(\<forall> x \<in> set xs . \<forall> y \<in> set xs . \<exists> xs' . P x y xs')"
  then obtain f where "f =(\<lambda> xy . (SOME xs' . P (fst xy) (snd xy) xs'))" by blast

  let ?xsp = "{Pair x y | x y . x \<in> set xs \<and> y \<in> set xs}"
  have "finite ?xsp"
    by simp 

  then obtain xs'' where "set xs'' = image f ?xsp"
    by (metis (no_types, lifting) finite_list set_map) 
  then have "\<And> x y . x \<in> set xs  \<Longrightarrow> y \<in> set xs \<Longrightarrow> set (f(x,y)) \<subseteq> set (concat xs'') \<and> P x y (f(x,y))" 
  proof -
    fix x y assume "x \<in> set xs" and "y \<in> set xs"
    then have "(x,y) \<in> ?xsp" by blast
    then have "\<exists> xs' . P x y xs'" using \<open>(\<forall> x \<in> set xs . \<forall> y \<in> set xs . \<exists> xs' . P x y xs')\<close> by blast
    moreover have "f (x,y) = (SOME xs' . P x y xs')" using \<open>f =(\<lambda> xy . (SOME xs' . P (fst xy) (snd xy) xs'))\<close> by auto
    ultimately have "P x y (f (x,y))" by (simp add: someI_ex)
    moreover have "set (f (x,y)) \<subseteq> set (concat xs'')" using \<open>set xs'' = image f ?xsp\<close>  \<open>(x,y) \<in> ?xsp\<close> by auto
    ultimately show "set (f(x,y)) \<subseteq> set (concat xs'') \<and> P x y (f(x,y))" by blast
  qed

  then have *: "\<And> x y . x \<in> set xs  \<Longrightarrow> y \<in> set xs \<Longrightarrow> \<exists> xs' . set xs' \<subseteq> set (concat xs'') \<and> P x y xs'" by blast

  moreover have "\<And> x'' . x'' \<in> set (concat xs'') \<Longrightarrow> \<exists> x \<in> set xs . \<exists> y \<in> set xs . set (f(x,y)) \<subseteq> set (concat xs'') \<and> P x y (f(x,y)) \<and> x'' \<in> set (f(x,y))"
  proof -
    fix x'' assume "x'' \<in> set (concat xs'')"
    then obtain fxs where "fxs \<in> set xs''" and "x'' \<in> set fxs"
      by auto
    then obtain x y where "(x,y) \<in> ?xsp" and "fxs = f(x,y)"
      using \<open>set xs'' = image f ?xsp\<close> by auto
    then have "x \<in> set xs" and "y \<in> set xs" by auto
    then have "set (f(x,y)) \<subseteq> set (concat xs'')" and "P x y (f(x,y))"
      using \<open>\<And> x y . x \<in> set xs  \<Longrightarrow> y \<in> set xs \<Longrightarrow> set (f(x,y)) \<subseteq> set (concat xs'') \<and> P x y (f(x,y))\<close> by auto
    moreover have "x'' \<in> set (f(x,y))" 
      using \<open>x'' \<in> set fxs\<close> \<open>fxs = f(x,y)\<close> by auto
    ultimately show "\<exists> x \<in> set xs . \<exists> y \<in> set xs . set (f(x,y)) \<subseteq> set (concat xs'') \<and> P x y (f(x,y)) \<and> x'' \<in> set (f(x,y))"
      using \<open>x \<in> set xs\<close> \<open>y \<in> set xs\<close> by blast
  qed

  then have **: "\<And> x'' . x'' \<in> set (concat xs'') \<Longrightarrow> \<exists> x \<in> set xs . \<exists> y \<in> set xs . \<exists> xs' . set xs' \<subseteq> set (concat xs'') \<and> P x y xs' \<and> x'' \<in> set xs'" by blast

  show ?thesis using * ** by blast
qed
    
  
  
lemma r_distinguishable_k'_by_inc : "r_distinguishable_k'_by M q1 q2 k wt \<Longrightarrow> k < k' \<Longrightarrow> r_distinguishable_k'_by M q1 q2 k' wt"
proof (induction k arbitrary: q1 q2 k')
  case 0
  then obtain k'' where "k' = Suc k''"
    using gr0_implies_Suc by blast 
  then have "r_distinguishable_k'_by M q1 q2 (Suc k'') wt"
    unfolding r_distinguishable_k'_by.simps using 0 by auto
  then show ?case using \<open>k' = Suc k''\<close> by auto
next
  case (Suc k)
  then show ?case (* TODO: remove smt *)
    by (smt Suc_lessE option.case_eq_if r_distinguishable_k'_by.simps(2)) 
qed

(*
lemma r_distinguishable_k'_by_asdf :
  assumes " \<not> (\<exists>j\<le>k. \<exists> wt . r_distinguishable_k'_by M q1 q2 j wt)"
  and     "r_distinguishable_k'_by M q1 q2 (Suc k) wt"
shows "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . \<exists> wt . ((t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)) \<and> (find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2) wt = None)"
using assms proof (induction k)
  case 0
  then show ?case unfolding r_distinguishable_k'_by.simps 
next
  case (Suc k)
  then show ?case sorry
qed
*)

lemma "r_distinguishable_k' M q1 q2 k = (\<exists> wt . r_distinguishable_k'_by M q1 q2 k wt)" 
proof (induction k arbitrary: q1 q2 rule: less_induct)
  case (less k')
  then show ?case proof (cases k')

    case 0
    have "r_distinguishable_k' M q1 q2 0 \<Longrightarrow> \<exists>wt. r_distinguishable_k'_by M q1 q2 0 wt"
    proof -
      assume "r_distinguishable_k' M q1 q2 0" 
      then obtain x where *: "x \<in> set (inputs M)" and **: "\<not> (\<exists>t1\<in>h M. \<exists>t2\<in>h M. t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
        unfolding r_distinguishable_k'.simps by blast
      let ?wt = "[((q1,q2),x)]"
      have "r_distinguishable_k'_by M q1 q2 0 ?wt"
        unfolding r_distinguishable_k'_by.simps using ** * by auto
      then show ?thesis by blast
    qed
    moreover have "\<exists>wt. r_distinguishable_k'_by M q1 q2 0 wt \<Longrightarrow> r_distinguishable_k' M q1 q2 0"
    proof -
      assume "\<exists>wt. r_distinguishable_k'_by M q1 q2 0 wt"
      then obtain wt where "r_distinguishable_k'_by M q1 q2 0 wt" by blast
      then obtain qqx where "find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt = Some qqx" 
        unfolding r_distinguishable_k'_by.simps
      proof -
        assume a1: "\<And>qqx. find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt = Some qqx \<Longrightarrow> thesis"
        assume "case find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of None \<Rightarrow> False | Some qqx \<Rightarrow> \<not> (\<exists>t1\<in>h M. \<exists>t2\<in>h M. t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2)"
        then have "find (\<lambda>p. fst (fst p) = q1 \<and> snd (fst p) = q2 \<and> snd p \<in> set (inputs M)) wt \<noteq> None"
          by (metis option.case_eq_if)
        then show ?thesis
          using a1 by blast
      qed 
      then have "\<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2)"
        using \<open>r_distinguishable_k'_by M q1 q2 0 wt\<close> unfolding r_distinguishable_k'_by.simps
        by auto
      moreover have "snd qqx \<in> set (inputs M)"
        using find_condition[OF\<open>find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt = Some qqx\<close>] by auto 
      ultimately have "r_distinguishable_k' M q1 q2 0"
        unfolding r_distinguishable_k'.simps by blast
      then show ?thesis by blast
    qed
  next
    case (Suc k)
    then have "k' = Suc k" and "0 < k'" and "k < k'" by auto

    have "r_distinguishable_k' M q1 q2 (Suc k) = (\<exists> wt . r_distinguishable_k'_by M q1 q2 (Suc k) wt)" 
    proof (cases "\<exists> j \<le> k . r_distinguishable_k' M q1 q2 j")
      case True
      then obtain j where "j \<le> k" and "r_distinguishable_k' M q1 q2 j" by blast
      then have "j < k'" and "j < Suc k" and "j \<le> Suc k" using \<open>k < k'\<close> by auto
      show ?thesis using less.IH[OF \<open>j < k'\<close>, of q1 q2]  
        r_distinguishable_inc'[OF _ \<open>j \<le> Suc k\<close>, of M q1 q2] 
        r_distinguishable_k'_by_inc[OF _ \<open>j < Suc k\<close>, of M q1 q2]
        using \<open>r_distinguishable_k' M q1 q2 j\<close> by blast
    next
      case False
      then have rd1: "r_distinguishable_k' M q1 q2 (Suc k) = (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k)"
        unfolding r_distinguishable_k'.simps by fastforce

      have "\<not> (\<exists> wt . r_distinguishable_k'_by M q1 q2 0 wt)"
        using False less.IH[OF \<open>0 < k'\<close>] by blast
      then have rd2: "(\<exists> wt . r_distinguishable_k'_by M q1 q2 (Suc k) wt) = (\<exists> wt . (case find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
                            None \<Rightarrow> False |
                            Some qqx \<Rightarrow> \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt))"
        by fastforce

      let ?rd1 = "(\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k)"
      let ?rd2 = "(\<exists> wt . (case find (\<lambda> qqx . fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) wt of
                            None \<Rightarrow> False |
                            Some qqx \<Rightarrow> \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt))"

      have "?rd1 \<Longrightarrow> ?rd2"
      proof -
        assume ?rd1
        then obtain x where "x \<in> set (inputs M)" and "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k' M (t_target t1) (t_target t2) k"
          by blast
        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> wt . r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)"
          using less.IH[OF \<open>k < k'\<close>] by blast
        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . \<exists> wt . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)"
          by blast
        then obtain wts where wts_def : "(\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> wt . set wt \<subseteq> set wts \<and> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)) \<and> ((\<forall>x''\<in>set wts.
           \<exists>xa\<in>h M.
              \<exists>y\<in>h M.
                 \<exists>xs'. set xs' \<subseteq> set wts \<and>
                       (t_source xa = q1 \<and>
                        t_source y = q2 \<and> t_input xa = x \<and> t_input y = x \<and> t_output xa = t_output y \<longrightarrow>
                        r_distinguishable_k'_by M (t_target xa) (t_target y) k xs') \<and>
                       x'' \<in> set xs'))"
          using sublist_property_cover_ex[OF \<open>\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . \<exists> wt . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)\<close>] by blast

        
        


        let ?wts' = "((q1,q2),x) # wts"
        have "find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) ?wts' = Some ((q1,q2),x)" 
          using List.find.simps(2)[of "(\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M))" "((q1,q2),x)" wts] \<open>x \<in> set (inputs M)\<close> by auto
        moreover have "\<forall>t1\<in>h M.
                      \<forall>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                         t_input t1 = snd ((q1,q2),x) \<and> t_input t2 = snd ((q1,q2),x) \<and> t_output t1 = t_output t2 \<longrightarrow>
                         r_distinguishable_k'_by M (t_target t1) (t_target t2) k ?wts'"
          using wts_def 

        have "case find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) ?wts' of
               None \<Rightarrow> False
               | Some qqx \<Rightarrow>
                   \<forall>t1\<in>h M.
                      \<forall>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                         t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2 \<longrightarrow>
                         r_distinguishable_k'_by M (t_target t1) (t_target t2) k ?wts'"










        obtain wts' where "set wts' = {qqx \<in> set wts . r_distinguishable_k'_by M (fst (fst qqx)) (snd (fst qqx)) k wts}"
          by (metis (full_types) set_filter)

        then have "\<And> t1 t2 . t1 \<in> h M \<Longrightarrow> t2 \<in> h M \<Longrightarrow> (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<Longrightarrow> (\<exists> wt . set wt \<subseteq> set wts' \<and> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)"
        proof -
          fix t1 t2 assume "t1 \<in> h M" and "t2 \<in> h M" and "(t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
          then obtain wt where "set wt \<subseteq> set wts" and "r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt"
            using wts_def by blast
          then have "\<And> qqx . qqx \<in> set wt \<Longrightarrow> r_distinguishable_k'_by M (fst (fst qqx)) (snd (fst qqx)) k wts"
          then have "set wt \<subseteq> set wts'" using \<open>set wts' = {qqx \<in> set wts . r_distinguishable_k'_by M (fst (fst qqx)) (snd (fst qqx)) k wts}\<close> 

        then have "\<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> wt . set wt \<subseteq> set wts' \<and> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)"
          using wts_def 
      
      
        (* TODO: handle ((q1,q2),?) in wts *)


        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> (\<exists> wt . set wt \<subseteq> set wts' \<and> r_distinguishable_k'_by M (t_target t1) (t_target t2) k wt)"
          using wts_def proof

        let ?wts' = "((q1,q2),x) # wts"
        have "find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) ?wts' = Some ((q1,q2),x)" 
          using List.find.simps(2)[of "(\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M))" "((q1,q2),x)" wts] \<open>x \<in> set (inputs M)\<close> by auto
        moreover have "\<forall>t1\<in>h M.
                      \<forall>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                         t_input t1 = snd ((q1,q2),x) \<and> t_input t2 = snd ((q1,q2),x) \<and> t_output t1 = t_output t2 \<longrightarrow>
                         r_distinguishable_k'_by M (t_target t1) (t_target t2) k ?wts'"
          using wts_def 

        have "case find (\<lambda>qqx. fst (fst qqx) = q1 \<and> snd (fst qqx) = q2 \<and> snd qqx \<in> set (inputs M)) ?wts' of
               None \<Rightarrow> False
               | Some qqx \<Rightarrow>
                   \<forall>t1\<in>h M.
                      \<forall>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                         t_input t1 = snd qqx \<and> t_input t2 = snd qqx \<and> t_output t1 = t_output t2 \<longrightarrow>
                         r_distinguishable_k'_by M (t_target t1) (t_target t2) k ?wts'"
        then have ?rd2
      

      then show ?thesis sorry
    qed
  
  
  
    have "r_distinguishable_k' M q1 q2 (Suc k) \<Longrightarrow> (\<exists>wt. r_distinguishable_k'_by M q1 q2 (Suc k) wt)"
    proof -
      assume "r_distinguishable_k' M q1 q2 (Suc k)"
      
  
    
  qed
qed





end (*


lemma r_distinguishable_k_witnesses_find_helper : "((case find P XS of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x)) = Some wt) \<Longrightarrow> (\<exists> w . find P XS = Some w \<and> f w = wt)"
  by (metis option.case_eq_if option.collapse option.distinct(1) option.inject)

lemma r_distinguishable_k_witnesses_not_elem_helper : "x \<notin> XS \<Longrightarrow> y \<in> XS \<Longrightarrow> y \<noteq> x" 
  by blast

lemma r_distinguishable_k_witnesses :
  assumes "r_distinguishable_k_witness M q1 q2 k = Some wt"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  shows     "\<forall> w \<in> set wt . 
                  (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))
                \<and> (\<not>(\<exists> w' \<in> set wt . w' \<noteq> w \<and> fst w' = fst w))
                \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M))"
  and     "\<exists> w12 \<in> set wt . fst (fst w12) = q1 \<and> snd (fst w12) = q2"  
proof -
  have "(\<forall> w \<in> set wt . 
                  (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))
                \<and> (\<not>(\<exists> w' \<in> set wt . w' \<noteq> w \<and> fst w' = fst w))
                \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)))
        \<and> (\<exists> w12 \<in> set wt . fst (fst w12) = q1 \<and> snd (fst w12) = q2)"
    using assms proof (induct k arbitrary: q1 q2 wt rule: less_induct)
    case (less k')
    assume a1: "r_distinguishable_k_witness M q1 q2 k' = Some wt"

    

    then show ?case proof (cases k')
      case 0
      then obtain x where "find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x"
        using a1 unfolding r_distinguishable_k_witness.simps
        by fastforce
      then have "wt = [((q1, q2), x)]"
        using \<open>r_distinguishable_k_witness M q1 q2 k' = Some wt\<close> 0 by fastforce

      have "(\<forall> w \<in> set wt . 
                    (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k'-1))
                  \<and> (\<not>(\<exists> w' \<in> set wt . w' \<noteq> w \<and> fst w' = fst w))
                  \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)))"
      proof 
        fix w assume "w \<in> set wt"
        then have "w = ((q1,q2),x)"
          using \<open>wt = [((q1, q2), x)]\<close> by auto

        have "x \<in> set (inputs M)"
          using \<open>find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x\<close>
          by (simp add: find_set)
        have "\<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
          using \<open>find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x\<close>
          using find_condition by fastforce
        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0" 
          using \<open>w = ((q1,q2),x)\<close> by fastforce
        then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k'-1)"
          using 0 by auto
        moreover have "\<not>(\<exists> w' \<in> set wt . w' \<noteq> w \<and> fst w' = fst w)"
          using \<open>wt = [((q1, q2), x)]\<close> \<open>w = ((q1,q2),x)\<close> by auto
        moreover have "fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)" 
          using \<open>w = ((q1,q2),x)\<close> \<open>q1 \<in> nodes M\<close> \<open>q2 \<in> nodes M\<close> \<open>x \<in> set (inputs M)\<close> by simp
        ultimately show "(\<forall>t1\<in>h M.
                             \<forall>t2\<in>h M.
                                t_source t1 = fst (fst w) \<and>
                                t_source t2 = snd (fst w) \<and>
                                t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2 \<longrightarrow>
                                r_distinguishable_k M (t_target t1) (t_target t2) (k' - 1)) \<and>
                         (\<not> (\<exists>w'\<in>set wt. w' \<noteq> w \<and> fst w' = fst w)) \<and>
                         (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M))"
          by blast
      qed
      moreover have "(\<exists> w12 \<in> set wt . fst (fst w12) = q1 \<and> snd (fst w12) = q2)"
        using \<open>wt = [((q1, q2), x)]\<close> by fastforce
      ultimately show ?thesis using 0 by blast
    next
      case (Suc k)
      then have "k < k'" and "0 < k'" and "k'-1 = k" by auto

      have "r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt" 
        using Suc a1 by auto

      then show ?thesis  
      proof (cases "r_distinguishable_k_witness M q1 q2 0")
        case None
        
        then have "r_distinguishable_k_witness M q1 q2 (Suc k) = 
                    (case find (\<lambda>xr. None \<notin> set (snd xr))
                      (map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt))
                                                (t_target (snd tt)) k)
                                      (filter
                                        (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                              t_source (snd tt) = q2 \<and>
                                              t_input (fst tt) = x \<and>
                                              t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                                        (concat
                                          (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
                         (inputs M)) of
                      None \<Rightarrow> None | Some xrs \<Rightarrow> Some (((q1, q2), fst xrs) # concat (these_list (snd xrs))))" 
          using r_distinguishable_k_witness.simps(2)[of M q1 q2 k] by auto
        then have rdw_def : "(case find (\<lambda>xr. None \<notin> set (snd xr))
                      (map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt))
                                                (t_target (snd tt)) k)
                                      (filter
                                        (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                              t_source (snd tt) = q2 \<and>
                                              t_input (fst tt) = x \<and>
                                              t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                                        (concat
                                          (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
                         (inputs M)) of
                      None \<Rightarrow> None | Some xrs \<Rightarrow> Some (((q1, q2), fst xrs) # concat (these_list (snd xrs)))) = Some wt"
          using \<open>r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt\<close> by fastforce
  
        let ?tts = "(concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M)))"
        let ?ttsf = "\<lambda> x . (filter (\<lambda>tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt)) ?tts)"
        let ?ttsfd = "\<lambda> x . map (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) (?ttsf x)"
        let ?xtt = "map (\<lambda> x . (x,?ttsfd x)) (inputs M)"
        let ?fxtt = "find (\<lambda> xr . \<not>(None \<in> set (snd xr))) ?xtt"
        
        have "set ?tts = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M}"
          by (metis (no_types) cartesian_product_list.simps cartesian_product_list_set)
        then have "\<And> x . set (?ttsf x) = {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by auto
        then have "\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
          by auto
        then have "\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
        proof -
          fix x     
          have "set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
            using \<open>\<And> x . set (?ttsfd x) = image (\<lambda>tt . r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt)) k) {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
          also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . (t1,t2) \<in> {(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }}"
            by blast
          also have "\<dots> = {r_distinguishable_k_witness M (t_target (fst (t1,t2))) (t_target (snd (t1,t2))) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
            by blast
          also have "\<dots> = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
            by force
          finally show "set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
            by fast
        qed


        

        have *: "\<And> x . \<not>(None \<in> set (?ttsfd x)) \<Longrightarrow> (\<forall> fw \<in> set (?ttsfd x) . \<forall> w \<in> set (the fw) .
                                                          (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))
                                                        \<and> (\<not>(\<exists> w' \<in> set (the fw) . w' \<noteq> w \<and> fst w' = fst w))
                                                        \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)))"
        proof 
          fix x fw assume "\<not>(None \<in> set (?ttsfd x))" and "fw \<in> set (?ttsfd x)"
          then have "fw \<noteq> None" 
            using r_distinguishable_k_witnesses_not_elem_helper[of None "set (?ttsfd x)" fw] by blast
          then obtain fw' where "fw = Some fw'" by blast
          then have "(the fw) = fw'" by simp 

          from \<open>fw \<in> set (?ttsfd x)\<close> obtain t1 t2 where "r_distinguishable_k_witness M (t_target t1) (t_target t2) k = fw" 
                                                    and "t1 \<in> h M" and "t2 \<in> h M" and "t_source t1 = q1" and "t_source t2 = q2" 
                                                    and "t_input t1 = x" and "t_input t2 = x" and "t_output t1 = t_output t2"
            using * by fastforce

          have "t_target t1 \<in> nodes M"
            using \<open>t_source t1 = q1\<close> \<open>q1 \<in> nodes M\<close> \<open>t1 \<in> h M\<close> by auto
          have "t_target t2 \<in> nodes M"
            using \<open>t_source t2 = q2\<close> \<open>q2 \<in> nodes M\<close> \<open>t2 \<in> h M\<close> by auto
          have "r_distinguishable_k_witness M (t_target t1) (t_target t2) k = Some fw'"
            using \<open>r_distinguishable_k_witness M (t_target t1) (t_target t2) k = fw\<close> \<open>fw = Some fw'\<close> by auto

          have "(\<forall>w\<in>set fw'.
                    (\<forall>t1\<in>h M.
                        \<forall>t2\<in>h M.
                           t_source t1 = fst (fst w) \<and>
                           t_source t2 = snd (fst w) \<and>
                           t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2 \<longrightarrow>
                           r_distinguishable_k M (t_target t1) (t_target t2) (k - 1)) \<and>
                    \<not> (\<exists>w'\<in>set fw'. w' \<noteq> w \<and> fst w' = fst w) \<and>
                    fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M))" 
            using less.hyps[OF \<open>k < k'\<close> \<open>r_distinguishable_k_witness M (t_target t1) (t_target t2) k = Some fw'\<close> \<open>t_target t1 \<in> nodes M\<close> \<open>t_target t2 \<in> nodes M\<close>] by auto
          then show "\<forall>w\<in>set (the fw).
                      (\<forall>t1\<in>h M.
                          \<forall>t2\<in>h M.
                             t_source t1 = fst (fst w) \<and>
                             t_source t2 = snd (fst w) \<and>
                             t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2 \<longrightarrow>
                             r_distinguishable_k M (t_target t1) (t_target t2) (k - 1)) \<and>
                      \<not> (\<exists>w'\<in>set (the fw). w' \<noteq> w \<and> fst w' = fst w) \<and>
                      fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)"
            using \<open>(the fw) = fw'\<close> by blast
        qed


        obtain xrs where "?fxtt = Some xrs" and "wt = (((q1, q2), fst xrs) # concat (these_list (snd xrs)))"
          using r_distinguishable_k_witnesses_find_helper[of "\<lambda> xrs . (((q1, q2), fst xrs) # concat (these_list (snd xrs)))" "(\<lambda>xr. None \<notin> set (snd xr))" "(map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt))
                                    k)
                          (filter
                            (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                  t_source (snd tt) = q2 \<and>
                                  t_input (fst tt) = x \<and>
                                  t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                            (concat (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
             (inputs M))" wt] rdw_def by blast

        let ?x = "fst xrs"
        
        have "xrs \<in> set ?xtt"
          using \<open>?fxtt = Some xrs\<close> by (meson find_set)    
        then have "snd xrs = ?ttsfd ?x"
          by fastforce
        moreover have "None \<notin> set (snd xrs)" 
          using find_condition[OF \<open>?fxtt = Some xrs\<close>] by assumption 
        ultimately have "None \<notin> set (?ttsfd ?x)" by auto
          
        then have "(\<forall> fw \<in> set (?ttsfd ?x) . \<forall> w \<in> set (the fw) .
                                                    (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))
                                                  \<and> (\<not>(\<exists> w' \<in> set (the fw) . w' \<noteq> w \<and> fst w' = fst w))
                                                  \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)))"
          using * by blast

        then have "(\<forall> w \<in> set (((q1, q2), fst xrs) # concat (these_list (?ttsfd ?x))) .
                                                    (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))
                                                  \<and> (\<not>(\<exists> w' \<in> set (((q1, q2), fst xrs) # concat (these_list (?ttsfd ?x))) . w' \<noteq> w \<and> fst w' = fst w))
                                                  \<and> (fst (fst w) \<in> nodes M \<and> snd (fst w) \<in> nodes M \<and> snd w \<in> set (inputs M)))"

        

            
        have "set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}"      
          by auto
        have "(?fxtt \<noteq> None) = (\<exists> xtt \<in> set ?xtt . None \<notin> set (snd xtt))" 
          using find_not_None_elem[of "(\<lambda>xr. None \<notin> set (snd xr))" ?xtt] by blast
        then have "(?fxtt \<noteq> None) = (\<exists> x \<in> set (inputs M) . \<not>(None \<in> set (?ttsfd x)))"
          using \<open>set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}\<close> r_distinguishable_k_witness_ex_set_helper[of ?ttsfd "set (inputs M)" "\<lambda> sd . None \<notin> set sd"] by blast



        (*
        moreover have **: "\<And> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k \<Longrightarrow> \<not>(None \<in> set (?ttsfd x))"
        proof -
          fix x assume "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
          then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None"
            using r_distinguishable_k_witness_ex[of M _ _ k] by blast
          then show "\<not>(None \<in> set (?ttsfd x))"
            using image_elem_2'[of "\<lambda> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2" "\<lambda> t1 t2 . r_distinguishable_k_witness M (t_target t1) (t_target t2) k" None] 
            \<open>\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
        qed*)


end (*

        have *: "\<And> x . \<not>(None \<in> set (?ttsfd x)) \<Longrightarrow> \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
        proof -
          fix x assume "\<not>(None \<in> set (?ttsfd x))"
          then have "None \<notin> {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"
            using \<open>\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
          then have "\<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None"
            using image_elem_2[of None "\<lambda> t1 t2 . r_distinguishable_k_witness M (t_target t1) (t_target t2) k" "\<lambda> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"] by blast
          then show "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"    
            using r_distinguishable_k_witness_ex[of M _ _ k] by blast
        qed
        moreover have **: "\<And> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k \<Longrightarrow> \<not>(None \<in> set (?ttsfd x))"
        proof -
          fix x assume "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
          then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k_witness M (t_target t1) (t_target t2) k \<noteq> None"
            using r_distinguishable_k_witness_ex[of M _ _ k] by blast
          then show "\<not>(None \<in> set (?ttsfd x))"
            using image_elem_2'[of "\<lambda> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2" "\<lambda> t1 t2 . r_distinguishable_k_witness M (t_target t1) (t_target t2) k" None] 
            \<open>\<And> x . set (?ttsfd x) = {r_distinguishable_k_witness M (t_target t1) (t_target t2) k | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }\<close> by blast
        qed
      
      

        obtain xrs where "?fxtt = Some xrs" and "wt = (((q1, q2), fst xrs) # concat (these_list (snd xrs)))"
          using r_distinguishable_k_witnesses_find_helper[of "\<lambda> xrs . (((q1, q2), fst xrs) # concat (these_list (snd xrs)))" "(\<lambda>xr. None \<notin> set (snd xr))" "(map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt))
                                    k)
                          (filter
                            (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                  t_source (snd tt) = q2 \<and>
                                  t_input (fst tt) = x \<and>
                                  t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                            (concat (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
             (inputs M))" wt] rdw_def by blast

        



        

            
        have "set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}"      
          by auto
        have "(?fxtt \<noteq> None) = (\<exists> xtt \<in> set ?xtt . None \<notin> set (snd xtt))" 
          using find_not_None_elem[of "(\<lambda>xr. None \<notin> set (snd xr))" ?xtt] by blast
        then have "(?fxtt \<noteq> None) = (\<exists> x \<in> set (inputs M) . \<not>(None \<in> set (?ttsfd x)))"
          using \<open>set ?xtt = {(x,?ttsfd x) | x . x \<in> set (inputs M)}\<close> r_distinguishable_k_witness_ex_set_helper[of ?ttsfd "set (inputs M)" "\<lambda> sd . None \<notin> set sd"] by blast


        
        









      moreover have "(r_distinguishable_k_witness M q1 q2 (Suc k) = None) = (?fxtt = None)"
        using r_distinguishable_k_witness_ex_find_helper[of "\<lambda> xrs . Some (((q1, q2), fst xrs) # concat (these_list (snd xrs)))" "(\<lambda>xr. None \<notin> set (snd xr))"  "(map (\<lambda>x. (x, map (\<lambda>tt. r_distinguishable_k_witness M (t_target (fst tt)) (t_target (snd tt))
                                    k)
                          (filter
                            (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                  t_source (snd tt) = q2 \<and>
                                  t_input (fst tt) = x \<and>
                                  t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt))
                            (concat (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))))))
             (inputs M))" ] using rdw_def  by fastforce
      ultimately have "r_distinguishable_k_witness M q1 q2 (Suc k) \<noteq> None = (\<exists> x \<in> set (inputs M) . \<not>(None \<in> set (?ttsfd x)))" 
        by auto

      also have "\<dots> = (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        using * ** by blast
      also have "\<dots> = r_distinguishable_k M q1 q2 (Suc k)"
        unfolding r_distinguishable_k'.simps by blast
      finally show ?thesis using \<open>k' = Suc k\<close> by simp



      next
        case (Some a)
        then have "wt = a" 
          using \<open>r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt\<close> unfolding r_distinguishable_k_witness.simps(2) by auto
        then have "w \<in> set a"
          using \<open>w \<in> set wt\<close> by auto
        
        
        show ?thesis 
          using less.hyps[OF \<open>0 < k'\<close> Some \<open>w \<in> set a\<close>] \<open>wt = a\<close> r_distinguishable_0[of M _ _ k']  by blast
          
      qed


      
    qed
  qed
    

    case 0
    assume "r_distinguishable_k_witness M q1 q2 0 = Some wt"
       and "w \<in> set wt"
  
    then obtain x where "find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x"
      unfolding r_distinguishable_k_witness.simps
      by fastforce
    then have "wt = [((q1, q2), x)]"
      using \<open>r_distinguishable_k_witness M q1 q2 0 = Some wt\<close> by fastforce
    then have "w = ((q1,q2),x)"
      using \<open>w \<in> set wt\<close> by auto
  
    have "x \<in> set (inputs M)"
      using \<open>find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x\<close>
      by (simp add: find_set)
    have "\<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
      using \<open>find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) = Some x\<close>
      using find_condition by fastforce
    then have "\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = fst (fst w) \<and> t_source t2 = snd (fst w) \<and> t_input t1 = snd w \<and> t_input t2 = snd w \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0" 
      using \<open>w = ((q1,q2),x)\<close> by fastforce
    moreover have "\<not>(\<exists> w' \<in> set wt . w' \<noteq> w \<and> fst w' = fst w)"
      using \<open>wt = [((q1, q2), x)]\<close> \<open>w = ((q1,q2),x)\<close> by auto
    ultimately show ?case by blast 
      
  next
    case (Suc k)
    assume a1: "r_distinguishable_k_witness M q1 q2 (Suc k) = Some wt"
       and a2: "w \<in> set wt"
    
  
  
    then show ?case 
    proof (cases "r_distinguishable_k_witness M q1 q2 0")
      case None
      then show ?thesis using a1 
    next
      case (Some a)
      then show ?thesis sorry
    qed
  qed
  





end (*


fun construct_r_distinguishing_set_from_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a  \<Rightarrow> (('a \<times> 'a) \<times> Input) list \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme" where
  "construct_r_distinguishing_set_from_witness M q1 q2 w = (let CSep = canonical_separator M q1 q2 in
    CSep\<lparr> transitions := filter (\<lambda> t . (t_source t, t_input t) \<in> set (map (\<lambda> wt . (Inl (fst wt),snd wt))  w)) (transitions CSep)\<rparr>)"     

fun construct_r_distinguishing_set_by_witness :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme option" where
  "construct_r_distinguishing_set_by_witness M q1 q2 = (case r_distinguishable_k_witness M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) of
    None \<Rightarrow> None |
    Some w \<Rightarrow> Some (construct_r_distinguishing_set_from_witness M q1 q2 w))"

value "construct_r_distinguishing_set_by_witness M_ex_H 1 3"

end (*

\<lparr> initial = Inl (q1,q2),
      inputs = inputs M,
      outputs = outputs M,
      transitions := (map (\<lambda>t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) (filter (\<lambda> t . (t_source t, t_input t, False) \<in> set w) (transitions PM)))
                     @                       
@ (map (\<lambda>t . (Inl (t_source t), t_input t, t_output t, Inr q1)) (filter (\<lambda> t . (t_source t, t_input t, True) \<in> set w) (transitions PM)))
    





































fun generate_sublists :: "'a list \<Rightarrow> 'a list list" where
  "generate_sublists xs = map (\<lambda> bs . map fst (filter snd (zip xs bs))) (generate_selector_lists (length xs))"

value "generate_sublists [1,2,3,4::nat]"


lemma apply_selector_list_result: 
  shows "set (map fst (filter snd (zip xs bs))) \<subseteq> set xs"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a xs)

  have *:"(map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd (zip xs bs)))) 
        \<or> (map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd (zip xs bs)))@[a])"
  proof (cases "length bs \<le> length xs")
    case True
    then have "(zip (xs @ [a]) bs) = (zip xs bs)"
      by (simp add: zip_append1)
    then have "(map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd (zip xs bs))))" by simp
    then show ?thesis by auto
  next
    case False
    then have "length xs = length (take (length xs) bs)" by auto

    let ?bs = "take (length (xs@[a])) bs"
    

    have "(zip (xs @ [a]) bs) = (zip (xs@[a]) ?bs)"
      by (metis append_Nil2 zip_Nil zip_append1) 
    moreover have "length (xs@[a]) = length ((butlast ?bs)@[last ?bs])" using False by auto
    ultimately have "(zip (xs @ [a]) bs) = (zip xs (butlast ?bs))@(zip [a] [last ?bs])"
      by (metis False One_nat_def append_butlast_last_id butlast.simps(1) butlast_snoc eq_iff length_append_singleton length_butlast less_numeral_extra(1) less_numeral_extra(3) list.size(3) take_eq_Nil zip_append)
    then have "(map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd ((zip xs (butlast ?bs))@(zip [a] [last ?bs])))))"
      by auto
    then have "(map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd ((zip xs (butlast ?bs)))))@(map fst (filter snd ((zip [a] [last ?bs])))))"
      by auto
    moreover have "zip xs (butlast ?bs) = zip xs bs"
      by (metis False append_Nil2 butlast_take diff_Suc_1 length_append_singleton not_less_eq_eq zip_Nil zip_append1)
    moreover have "(map fst (filter snd ((zip [a] [last ?bs])))) = [] \<or> (map fst (filter snd ((zip [a] [last ?bs])))) = [a]"
      by auto
    ultimately show ?thesis 
      by auto 
  qed

  then show ?case using snoc.IH by (cases "(map fst (filter snd (zip (xs @ [a]) bs)) = (map fst (filter snd (zip xs bs))))"; fastforce)
qed 


lemma "set (map set (generate_sublists xs)) = {xs' . xs' \<subseteq> set xs}"
proof -
  have "\<And> x . x \<in> set (map set (generate_sublists xs)) \<Longrightarrow> x \<subseteq> set xs"
    unfolding generate_sublists.simps using apply_selector_list_result[of xs] by fastforce
  moreover have "\<And> x . x \<subseteq> set xs \<Longrightarrow> x \<in> set (map set (generate_sublists xs))"
  proof -
    fix x assume "x \<subseteq> set xs"
    then have "finite x"
      using infinite_super by auto 
    then obtain x' where "set x' = x" 
      using List.finite_list by blast
    then have "set x' \<subseteq> set xs"
      using \<open>x \<subseteq> set xs\<close> by blast
    then obtain bs where "length bs = length xs" and "set x' = set (map fst (filter snd (zip xs bs)))"
      using generate_submachine_transition_set_equality[of x' xs] by auto
    then have "bs \<in> set (generate_selector_lists (length xs))" 
      using generate_selector_lists_set[of "length xs"] by auto
    then show "x \<in> set (map set (generate_sublists xs))"
      unfolding generate_sublists.simps using \<open>set x' = set (map fst (filter snd (zip xs bs)))\<close> \<open>set x' = x\<close> by fastforce
  qed
  ultimately show ?thesis by blast
qed



(* state preamble calculation as given by Petrenko & Yevtushenko *)
fun construct_state_preamble_data :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a Transition list \<Rightarrow> ('a list \<times> 'a Transition list) option" where
  "construct_state_preamble_data M 0 q r hs = Some (r,hs)" |
  "construct_state_preamble_data M (Suc n) q r hs = 
    (case 
      (find 
        (\<lambda> qI . snd qI \<noteq> [] \<and> (\<forall> t \<in> h M . t_source t = fst qI \<and> t_input t \<in> set (snd qI) \<longrightarrow> t_target t \<in> set r)) 
        (concat (map (\<lambda>q . map (\<lambda>x . (q,x)) (generate_sublists (inputs M))) (filter (\<lambda> q . \<not>(q \<in> set r)) (nodes_from_distinct_paths M))))) of
      None \<Rightarrow> (if (initial M \<in> set r) then Some (r,hs) else None) |
      Some qI \<Rightarrow> construct_state_preamble_data M n q (r@[fst qI]) (hs@(filter (\<lambda> t . t_source t = fst qI \<and> t_input t \<in> set (snd qI)) (wf_transitions M))))" 

fun construct_state_preamble_from_data :: "('a,'b) FSM_scheme \<Rightarrow> 'a list \<Rightarrow> 'a Transition list \<Rightarrow> ('a,'b) FSM_scheme" where
  "construct_state_preamble_from_data M r hs = 
    (let qi = map (\<lambda>q . (q, (find (\<lambda> x . \<exists> t \<in> set hs . t_source t = q \<and> t_input t = x) (inputs M)))) r in 
    (let hs' = filter (\<lambda> t . (t_source t, Some (t_input t)) \<in> set qi) hs in
    trim_transitions (M\<lparr> transitions := hs' \<rparr>)))"



fun construct_state_preamble :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a,'b) FSM_scheme option" where
  "construct_state_preamble M q = 
    (if q = initial M 
      then Some (M\<lparr> transitions := [] \<rparr>)
      else (if \<not>(q \<in> nodes M)
        then None
        else (case construct_state_preamble_data M (size M) q [q] [] of
          None \<Rightarrow> None |
          Some (r,hs) \<Rightarrow> Some (construct_state_preamble_from_data M r hs))))"


value "construct_state_preamble_data M_ex_H (size M_ex_H) 3 [3] []"
value "construct_state_preamble M_ex_H 3"
value "calculate_preamble_set_naive M_ex_H 3"








value[code] "calculate_state_separator_naive M_ex 2 3"
value[code] "calculate_state_separator_naive M_ex_H 2 3


fun canonical_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme" where
  "canonical_separator M q1 q2 = 
    (let PM = (product (from_FSM M q1) (from_FSM M q2)) in
    (let tPM = map (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t)) :: (('a \<times> 'a) + 'a) Transition) (transitions PM) in
    (let tq1 = map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_list PM)))) in
    (*(let tq1 = filter (\<lambda> t . \<exists> t1 \<in> set (transitions M) . t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> \<not> (\<exists> t2 \<in> set (transitions M) . t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t)) (transitions PM) in*)
    (let tq2 = filter (\<lambda> t . \<exists> t2 \<in> set (transitions M) . t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> \<not> (\<exists> t1 \<in> set (transitions M) . t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t)) (transitions PM) in

      \<lparr> initial = Inl (initial PM),
        inputs = inputs M,
        outputs = outputs M,
        transitions = tPM @ tq1 @ (map (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inr q2)) tq2),
        \<dots> = FSM.more M \<rparr> :: (('a \<times> 'a) + 'a,'b) FSM_scheme))))

value "canonical_separator M_ex 2 3"
value "canonical_separator M_ex_H 1 2"
value "language_up_to_length (canonical_separator M_ex_H 1 2) 2"

end (*

(*
(acyclic S \<and> single_input S \<and> is_submachine S M \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h S))))"
*)

fun is_Inl :: "'a + 'b \<Rightarrow> bool" where
  "is_Inl (Inl x) = True" |
  "is_Inl (Inr x) = False"

fun is_state_separator_from_canonical_separator :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_state_separator_from_canonical_separator CSep q1 q2 S = (
    is_submachine S CSep 
    \<and> single_input S
    (*\<and> acyclic S*)
    \<and> language_up_to_length S (size CSep) = language_up_to_length S (size CSep - 1)
    \<and> deadlock_state S (Inr q1)
    \<and> deadlock_state S (Inr q2)
    \<and> (\<forall> q \<in> nodes S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (is_Inl q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> q \<in> nodes S . \<forall> x \<in> set (inputs CSep) . (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h CSep . t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))
)"

(*
definition calculate_state_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = (let CSep = canonical_separator M q1 q2 in
    (case filter (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) (generate_submachines CSep) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S))"

value "calculate_state_separator_naive M_ex 5 2"
*)


fun calculate_state_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = 
    (case filter (\<lambda> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S) (generate_submachines (canonical_separator M q1 q2)) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S)"




function calculate_state_separator_naive :: "(nat, nat) FSM_scheme \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat \<times> nat) + nat,nat) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = 
    (case generate_submachines (canonical_separator M q1 q2) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S)"
  sorry 
termination
  using "termination" by blast 



function calculate_state_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = (let CSep = canonical_separator M q1 q2 in
    (case filter (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) (generate_submachines CSep) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S))"
using Product_Type.prod_cases3
proof -
  fix P :: bool and x :: "('a, 'b) FSM_scheme \<times> 'a \<times> 'a"
  assume "\<And>M q1 q2. x = (M, q1, q2) \<Longrightarrow> P"
  then show P
    using prod_cases3 by blast
next 
  fix M :: "('a, 'b) FSM_scheme"
  fix q1 :: "'a"
  fix q2 :: "'a"
  fix Ma q1a q2a 
  assume "(M, q1, q2) = (Ma, q1a, q2a)"
  then show "(let CSep = canonical_separator M q1 q2
        in case filter (is_state_separator_from_canonical_separator CSep q1 q2)
                 (generate_submachines CSep) of
           [] \<Rightarrow> None | S # SS \<Rightarrow> Some S) =
       (let CSep = canonical_separator Ma q1a q2a
        in case filter (is_state_separator_from_canonical_separator CSep q1a q2a)
                 (generate_submachines CSep) of
           [] \<Rightarrow> None | S # SS \<Rightarrow> Some S)" by blast
qed
termination 
  
  
proof -

fun calculate_state_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_naive M q1 q2 = (let CSep = canonical_separator M q1 q2 in
    (case filter (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) (generate_submachines CSep) of
      [] \<Rightarrow> None |
      S#SS \<Rightarrow> Some S))
    
lemma asdf: "2 = 3"


end (*






type_synonym IO = "(Input \<times> Output)"
type_synonym 'a Separator_set = "(IO list set \<times> (IO list \<Rightarrow> 'a option))" (* second value maps io sequences to their reached deadlock state, if any *)
datatype 'a Separator_state = NonSep nat | Sep 'a

fun isNonSep :: "'a Separator_state \<Rightarrow> bool" where
  "isNonSep (NonSep x) = True" |
  "isNonSep (Sep x) = False"

fun is_state_separator :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a Separator_state) FSM \<Rightarrow> bool" where
  "is_state_separator M q1 q2 S = (
    single_input S
    \<and> acyclic S
    \<and> deadlock_state S (Sep q1)
    \<and> deadlock_state S (Sep q2)
    \<and> (\<forall> q \<in> nodes S . (q \<noteq> Sep q1 \<and> q \<noteq> Sep q2) \<longrightarrow> (isNonSep q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> io \<in> L S . ((io_target S io (initial S) = Sep q1) \<longrightarrow> io \<in> (LS M q1 - LS M q2)))
    \<and> (\<forall> io \<in> L S . ((io_target S io (initial S) = Sep q2) \<longrightarrow> io \<in> (LS M q2 - LS M q1)))
    (*\<and> (\<forall> io \<in> L S . \<forall> t \<in> h S . (t_source t = (io_target S io (initial S)) \<longrightarrow> ([(t_input t, t_output t)] \<in> (LS M (io_target M io q1) \<union> LS M (io_target M io q2))))) *)
    \<and> (L S \<subseteq> LS M q1 \<union> LS M q2)
)"


(* TODO: express state_separators as submachines of (product (from_FSM M q1) (from_FSM M q2)) *)

fun deadlock_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> ((Input \<times> Output) list \<Rightarrow> bool) \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "deadlock_sequences M isDL P = (\<forall> io \<in> P . 
                                        (isDL io \<and> \<not> (\<exists> io' \<in> P . length io < length io' \<and> take (length io) io' = io))
                                      \<or> (\<not> isDL io \<and> (\<exists> io' \<in> P . length io < length io' \<and> take (length io) io' = io)))" 

fun is_state_separator_set :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Separator_set \<Rightarrow> bool" where
  "is_state_separator_set M q1 q2 P = (
    (*acyclic_sequences M (fst P)*)
    (\<forall> p . (path M (initial M) p \<and> p_io p \<in> {io \<in> fst P . \<exists> io' \<in> fst P . length io < length io' \<and> take (length io) io' = io}) \<longrightarrow> distinct (visited_states (initial M) p))
    (*\<and> single_input_sequences M (fst P)*)
    \<and> single_input_sequences (product (from_FSM M q1) (from_FSM M q2)) {io \<in> fst P . \<exists> io' \<in> fst P . length io < length io' \<and> take (length io) io' = io}
    \<and> deadlock_sequences M (\<lambda> io . (snd P) io \<noteq> None) (fst P)
    \<and> (\<forall> io \<in> (fst P) . (snd P) io = Some q1 \<or> (snd P) io = Some q2 \<or> (snd P) io = None)
    \<and> (\<forall> io \<in> (fst P) . ((snd P) io = Some q1) \<longrightarrow> io \<in> (LS M q1 - LS M q2))
    \<and> (\<forall> io \<in> (fst P) . ((snd P) io = Some q2) \<longrightarrow> io \<in> (LS M q2 - LS M q1))
    (*\<and> (\<forall> io \<in> (fst P) . io = [] \<or> ([last io] \<in> (LS M (io_target M (butlast io) q1) \<union> LS M (io_target M (butlast io) q2))))*)    
    \<and> (fst P \<subseteq> LS M q1 \<union> LS M q2)
    \<and> prefix_closed_sequences (fst P)
)"


(*
lemma acyclic_sequences_of_acyclic_FSM :
  "acyclic S = acyclic_sequences S (L S)"
  unfolding acyclic.simps acyclic_sequences.simps LS.simps by blast

lemma single_input_sequences_of_single_input_FSM :
  "single_input S = single_input_sequences S (L S)"
  unfolding single_input.simps single_input_sequences.simps LS.simps
*)  



end (*



(* test cases *)

(* type for designated fail-state *)
datatype TC_state = TS nat | Fail

fun test_case :: "TC_state FSM \<Rightarrow> bool" where
  "test_case U = (acyclic U \<and> single_input U \<and> output_complete U \<and> deadlock_state U Fail)"

fun test_suite :: "TC_state FSM set \<Rightarrow> bool" where
  "test_suite U = (\<forall> u \<in> U . test_case u)"

fun pass :: "('a, 'b) FSM_scheme \<Rightarrow> TC_state FSM \<Rightarrow> bool" where
  "pass M U = (\<forall> q \<in> nodes (product M U). snd q \<noteq> Fail)"


type_synonym IO = "(Input \<times> Output)"
type_synonym TC_set = "(IO list set \<times> (IO list \<Rightarrow> bool))" (* second value maps io sequences to whether they reach the fail deadlock state *)
type_synonym 'a separator_set = "(IO list set \<times> (IO list \<Rightarrow> 'a option))" (* second value maps io sequences to their reached deadlock state, if any *)

fun is_test_case_set :: "('a, 'b) FSM_scheme \<Rightarrow> 



end (*


fun tc_node_id :: "TC_state \<Rightarrow> nat" where
  "tc_node_id Fail = 0" |
  "tc_node_id (TS k) = k"

fun tc_next_node_id :: "TC_state FSM \<Rightarrow> nat" where
  "tc_next_node_id U = Suc (sum_list ((tc_node_id (initial U)) # (map (\<lambda> t . tc_node_id (t_target t)) (transitions U))))"
lemma tc_next_node_id_lt : 
  assumes "q \<in> nodes U" 
  shows "tc_node_id q < tc_next_node_id U"
proof -
  show ?thesis
  proof (cases "q = initial U")
    case True
    then show ?thesis by auto
  next
    case False
    then have "(\<exists> t \<in> h U . t_target t = q)"
      by (metis assms nodes.cases)
    then obtain t where "t\<in> set (transitions U)" and "t_target t = q" by auto
    then have "tc_node_id q \<in> set (map (\<lambda> t . tc_node_id (t_target t)) (transitions U))"
      by auto
    then have "sum_list (map (\<lambda> t . tc_node_id (t_target t)) (transitions U)) \<ge> tc_node_id q" 
      using member_le_sum_list by blast
    then show ?thesis 
      by auto
  qed
qed


fun tc_shift_id :: "nat \<Rightarrow> nat \<Rightarrow> TC_state \<Rightarrow> TC_state" where
  "tc_shift_id t k' Fail = Fail" |
  "tc_shift_id t k' (TS k) = (if (t = k) then TS k else TS (k + k'))"
fun tc_shift_transition :: "nat \<Rightarrow> nat \<Rightarrow> TC_state Transition \<Rightarrow> TC_state Transition" where
  "tc_shift_transition t k' tr = (tc_shift_id t k' (t_source tr), t_input tr, t_output tr, tc_shift_id t k' (t_target tr))"
fun test_case_concat :: "TC_state FSM \<Rightarrow> nat \<Rightarrow> TC_state FSM \<Rightarrow> TC_state FSM" where
  "test_case_concat U1 t U2 = (if (deadlock_state U1 (TS t))
    then U1\<lparr> transitions := (transitions U1) @ (map (tc_shift_transition t (tc_next_node_id U1)) (transitions U2)) \<rparr>
    else U1)"
        
(* TODO: rev *)
lemma tc_concat_pass :
  assumes "pass M (test_case_concat U1 t U2)"
  shows "pass M U1"
    and "\<forall> p . path (product M U1) (initial (product M U1)) p \<and> snd (target p (initial (product M U1))) = S t \<longrightarrow> pass (from_FSM M (fst (target p (initial (product M U1))))) U2" 
  sorry


fun definitely_reachable :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<forall> S . completely_specified S \<and> is_submachine S M \<longrightarrow> q \<in> nodes S)"

fun is_preamble :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_preamble S M q = (acyclic S \<and> single_input S \<and> is_submachine S M \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h S))))"

lemma definitely_reachable_alt_def :
  "definitely_reachable M q = (\<exists> S . acyclic S \<and> single_input S \<and> is_submachine S M \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h S))))"
  sorry

fun get_output_complete_transition :: "TC_state FSM \<Rightarrow> TC_state \<Rightarrow> Input \<Rightarrow> Output \<Rightarrow> TC_state Transition" where
  "get_output_complete_transition U q x y = (if (\<exists> t . t \<in> h U \<and> t_source t = q \<and> t_input t = x \<and> t_output t = y)
    then (SOME t . t \<in> h U \<and> t_source t = q \<and> t_input t = x \<and> t_output t = y)
    else (q,x,y,Fail))"

fun make_output_complete :: "TC_state FSM \<Rightarrow> TC_state FSM" where
  "make_output_complete U = U \<lparr> transitions := transitions U @ map  \<rparr>" 

end