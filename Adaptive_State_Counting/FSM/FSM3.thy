theory FSM3
imports Main
begin

(*type_synonym State = nat*)
type_synonym Input = nat
type_synonym Output = nat
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



fun is_wf_transition :: "'state FSM \<Rightarrow> 'state Transition \<Rightarrow> bool" where
  "is_wf_transition M t = ((t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun wf_transitions :: "'state FSM \<Rightarrow> 'state Transition list" where
  "wf_transitions M = filter (is_wf_transition M) (transitions M)"

abbreviation "h M \<equiv> set (wf_transitions M)"



fun pairwise_immediately_reachable :: "'state FSM \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_immediately_reachable M =  image (\<lambda> t. (t_source t, t_target t)) (h M)"

lemma wf_transrel_transition_ob : 
  assumes "(q,q') \<in> pairwise_immediately_reachable M"
  obtains t
  where "t \<in> h M"
    and "t_source t = q"
    and "t_target t = q'"
    and "is_wf_transition M t"
  using assms by auto

fun pairwise_reachable :: "'state FSM \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_reachable M = trancl (pairwise_immediately_reachable M)"

fun reachable :: "'state FSM \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
  "reachable M q q' = (q = q' \<or> (q, q') \<in> pairwise_reachable M)"

fun initially_reachable :: "'state FSM \<Rightarrow> 'state \<Rightarrow> bool" where
  "initially_reachable M q = reachable M (initial M) q"

fun nodes' :: "'state FSM \<Rightarrow> 'state set" where
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




inductive path :: "'state FSM \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "path M q []" |
  cons[intro!] : "t \<in> h M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"


fun path' :: "'state FSM \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
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
                      initial = 2::nat, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (2,1,30,4),
                                      (3,1,10,5),
                                      (4,0,10,3),
                                      (4,2,20,2),
                                      (5,2,30,3)]\<rparr>)"

definition "M_ex' = (\<lparr> 
                      initial = 1000::nat, 
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
  

    

value "lists_of_length [1,2,3::nat] 3"

fun paths_of_length :: "'state FSM \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state Transition list list" where
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

fun language_state_for_input :: "'state FSM \<Rightarrow> 'state \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "language_state_for_input M q xs = map p_io (filter (\<lambda> ts . xs = map t_input ts) (paths_of_length M q (length xs)))"

value "language_state_for_input M_ex 2 [1]"
value "language_state_for_input M_ex 2 [1,2]"
value "language_state_for_input M_ex 3 [1,2,1,2,1,2]"

fun language_state_for_inputs :: "'state FSM \<Rightarrow> 'state \<Rightarrow> Input list list \<Rightarrow> (Input \<times> Output) list list" where
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



fun LS\<^sub>i\<^sub>n :: "'state FSM \<Rightarrow> 'state \<Rightarrow> Input list set \<Rightarrow> (Input \<times> Output) list set" where 
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


fun visited_states :: "'state \<Rightarrow> 'state Transition list \<Rightarrow> 'state list" where
  "visited_states q p = (q # map t_target p)"

fun target :: "'state Transition list \<Rightarrow> 'state \<Rightarrow> 'state" where
  "target p q = last (visited_states q p)"



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


fun LS :: "'state FSM \<Rightarrow> 'state \<Rightarrow> (Input \<times> Output) list set" where
  "LS M q = { p_io p | p . path M q p }"

abbreviation "L M \<equiv> LS M (initial M)"



fun cartesian_product_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where 
  "cartesian_product_list xs ys = concat (map (\<lambda> x . map (\<lambda> y . (x,y)) ys) xs)"

value "cartesian_product_list [1,2,3::nat] [10,20,30::nat]"

lemma cartesian_product_list_set : "set (cartesian_product_list xs ys) = {(x,y) | x y . x \<in> set xs \<and> y \<in> set ys}"
  by auto

fun product_transitions :: "'state1 FSM \<Rightarrow> 'state2 FSM \<Rightarrow> ('state1 \<times> 'state2) Transition list" where
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


fun product :: "'state1 FSM \<Rightarrow> 'state2 FSM \<Rightarrow> ('state1 \<times> 'state2) FSM" where
  "product A B =
  \<lparr>
    initial = (initial A, initial B),
    inputs = (inputs A) @ (inputs B),
    outputs = (outputs A) @ (outputs B),
    transitions = product_transitions A B    
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


inductive_set nodes :: "'state FSM \<Rightarrow> 'state set" for M :: "'state FSM" where
  initial[intro!]: "initial M \<in> nodes M" |
  step[intro!]: "t \<in> h M \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_target t \<in> nodes M"

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


  


lemma nodes_code[code] : "nodes M = nodes' M"
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
  
lemma path_to_nodes : 
  assumes "q \<in> nodes M"
  obtains p where "path M (initial M) p"
            and   "q = (target p (initial M))"
proof -
  have "q \<in> nodes' M"
    using assms nodes_code by force  
  then have "reachable M (initial M) q" 
    by auto
  then show ?thesis
    by (metis path_reachable that)
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











fun completely_specified :: "'a FSM \<Rightarrow> bool" where
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

fun deterministic :: "'a FSM \<Rightarrow> bool" where
  "deterministic M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<longrightarrow> t_output t1 = t_output t2 \<and> t_target t1 = t_target t2)" 
abbreviation "deterministicH M \<equiv> (\<forall> q1 x y' y''  q1' q1'' . (q1,x,y',q1') \<in> h M \<and> (q1,x,y'',q1'') \<in> h M \<longrightarrow> y' = y'' \<and> q1' = q1'')"

lemma deterministic_alt_def : "deterministic M = deterministicH M" by auto



fun observable :: "'a FSM \<Rightarrow> bool" where
  "observable M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<longrightarrow> t_target t1 = t_target t2)" 
abbreviation "observableH M \<equiv> (\<forall> q1 x y q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x,y,q1'') \<in> h M \<longrightarrow> q1' = q1'')"

lemma observable_alt_def : "observable M = observableH M" by auto


fun single_input :: "'a FSM \<Rightarrow> bool" where
  "single_input M = (\<forall> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = t_source t2 \<longrightarrow> t_input t1 = t_input t2)" 
abbreviation "single_inputH M \<equiv> (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x',y',q1'') \<in> h M \<longrightarrow> x = x')"

lemma single_input_alt_def : "single_input M = single_inputH M" by force 


fun output_complete :: "'a FSM \<Rightarrow> bool" where
  "output_complete M = (\<forall> t \<in> h M . \<forall> y \<in> set (outputs M) . \<exists> t' \<in> h M . t_source t = t_source t' \<and> t_input t = t_input t' \<and> t_output t' = y)" 
abbreviation "output_completeH M \<equiv> (\<forall> q x . (\<exists> y q' . (q,x,y,q') \<in> h M) \<longrightarrow> (\<forall> y \<in> set (outputs M) . \<exists> q' . (q,x,y,q') \<in> h M))"

lemma output_complete_alt_def : "output_complete M = output_completeH M" by (rule; fastforce)


fun acyclic :: "'a FSM \<Rightarrow> bool" where
  "acyclic M = finite (L M)"

fun deadlock_state :: "'a FSM \<Rightarrow> 'a \<Rightarrow> bool" where 
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

  


fun io_in :: "(Input \<times> Output) list \<Rightarrow> Input list" where
  "io_in io = map fst io"

fun io_out :: "(Input \<times> Output) list \<Rightarrow> Input list" where
  "io_out io = map snd io"

lemma io_zip : "zip (io_in io) (io_out io) = io" 
  by (induction io; simp)





fun fst_io_target' :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "fst_io_target' M [] q = Some q" |
  "fst_io_target' M (xy#io) q = (case (find (\<lambda> t' . t_source t' = q \<and> t_input t' = fst xy \<and> t_output t' = snd xy) (wf_transitions M)) of
    None \<Rightarrow> None |
    Some t' \<Rightarrow> fst_io_target' M io (t_target t'))"

fun fst_io_target :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
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



fun is_io_target :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_io_target M [] q q' = (q = q')" |
  "is_io_target M (xy#io) q q' = (\<exists> t \<in> h M . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy \<and> is_io_target M io (t_target t) q')"

value "is_io_target M_ex [(1,20)] (initial M_ex) 4"
value "is_io_target M_ex [(1,20)] (initial M_ex) 3"

fun is_io_target' :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
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








fun io_targets :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets M io q = {target p q | p . path M q p \<and> p_io p = io}"

fun io_targets' :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets' M io q = set (map (\<lambda> p . target p q) (filter (\<lambda> p . p_io p = io) (paths_of_length M q (length io))))"

fun io_targets_list :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
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



    


fun minimal :: "'a FSM \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> nodes M . \<forall> q' \<in> nodes M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"


abbreviation "size_FSM M \<equiv> card (nodes M)" 
notation 
  size_FSM ("(|_|)")


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
              and "length p < |M|"
proof -
  obtain p where "path M q1 p"
             and "target p q1 = q2"
             and "distinct (visited_states q1 p)"
    using distinct_path_ob[OF assms(1)] by blast

  have "set (visited_states q1 p) \<subseteq> nodes M"
    using visited_states_are_nodes
    by (metis \<open>path M q1 p\<close> assms(2))
  then have "length (visited_states q1 p) \<le> |M|"
    using nodes_finite
    by (metis \<open>distinct (visited_states q1 p)\<close> card_mono distinct_card) 
  then have "length p < |M|"
    by simp 

  show ?thesis
    using \<open>length p < |M|\<close> \<open>path M q1 p\<close> \<open>target p q1 = q2\<close> that by blast
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
             and "length p' < |M|"
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






fun is_io_reduction_state :: "'a FSM \<Rightarrow> 'a \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state A a B b = (LS A a \<subseteq> LS B b)"

abbreviation "is_io_reduction A B \<equiv> is_io_reduction_state A (initial A) B (initial B)" 
notation 
  is_io_reduction ("_ \<preceq> _")


fun is_io_reduction_state_on_inputs :: "'a FSM \<Rightarrow> 'a \<Rightarrow> Input list set \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state_on_inputs A a U B b = (LS\<^sub>i\<^sub>n A a U \<subseteq> LS\<^sub>i\<^sub>n B b U)"

abbreviation "is_io_reduction_on_inputs A U B \<equiv> is_io_reduction_state_on_inputs A (initial A) U B (initial B)" 
notation 
  is_io_reduction_on_inputs ("_ \<preceq>\<lbrakk>_\<rbrakk> _")
  
(* extends Petrenko's definition to explicitly require same inputs and outputs *)
fun is_submachine :: "'a FSM \<Rightarrow> 'a FSM \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> h A \<subseteq> h B \<and> inputs A = inputs B \<and> outputs A = outputs B)"

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

fun from_FSM :: "'a FSM \<Rightarrow> 'a \<Rightarrow> 'a FSM" where
  "from_FSM M q = \<lparr> initial = q, inputs = inputs M, outputs = outputs M, transitions = transitions M \<rparr>"


fun r_compatible :: "'a FSM \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "r_compatible M q1 q2 = ((\<exists> S . completely_specified S \<and> is_submachine S (product (from_FSM M q1) (from_FSM M q2))))"

abbreviation "r_distinguishable M q1 q2 \<equiv> \<not> r_compatible M q1 q2"


fun r_distinguishable_k :: "'a FSM \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"

lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M))"
  by auto

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  by auto



lemma io_targets_are_nodes :
  assumes "q' \<in> io_targets M io q"
      and "q \<in> nodes M"
  shows "q' \<in> nodes M"              
  by (meson assms contra_subsetD io_targets_nodes)
  


lemma completely_specified_io_targets : 
  assumes "completely_specified M"
  shows "\<forall> q \<in> io_targets M io (initial M) . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x"
  by (meson assms completely_specified_alt_def io_targets_are_nodes nodes.initial)


fun completely_specified_state :: "'a FSM \<Rightarrow> 'a \<Rightarrow> bool" where
  "completely_specified_state M q = (\<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_states :
  "completely_specified M = (\<forall> q \<in> nodes M . completely_specified_state M q)"
  unfolding completely_specified.simps completely_specified_state.simps by force 

(* nodes that are reachable in at most k transitions *)
fun reachable_k :: "'a FSM \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target p q | p . path M q p \<and> length p \<le> n}" 

lemma reachable_k_0 : "reachable_k M q 0 = {q}" 
  by auto

lemma reachable_k_nodes : "nodes M = reachable_k M (initial M) ( |M| - 1)"
proof -
  have "\<And>q. q \<in> nodes M \<Longrightarrow> q \<in> reachable_k M (initial M) ( |M| - 1)"
  proof -
    fix q assume "q \<in> nodes M"
    then obtain p where "path M (initial M) p" and "target p (initial M) = q"
      by (metis path_to_nodes) 
    then obtain p' where "path M (initial M) p'"
                     and "target p' (initial M) = target p (initial M)" 
                     and "length p' < |M|"
      using distinct_path_length[of M "initial M" p] by auto
    then show "q \<in> reachable_k M (initial M) ( |M| - 1)"
      using \<open>target p (initial M) = q\<close> list.size(3) mem_Collect_eq not_less_eq_eq reachable_k.simps by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( |M| - 1) \<Longrightarrow> x \<in> nodes M"
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
  then have "h ?P = h ?P'" 
    unfolding product.simps
    by (metis FSM3.product.simps \<open>inputs (from_FSM M q1) = inputs (from_FSM M q1')\<close> \<open>inputs (from_FSM M q2) = inputs (from_FSM M q2')\<close> \<open>outputs (from_FSM M q1) = outputs (from_FSM M q1')\<close> \<open>outputs (from_FSM M q2) = outputs (from_FSM M q2')\<close> from_FSM.simps from_FSM_h product_simps(2) product_simps(3) product_simps(4))  
  then have **: "h ?F \<subseteq> h ?P'"
    by (metis (no_types, lifting) assms(1) from_FSM_h is_submachine.simps) 


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
  
      have "\<not>(\<exists> x \<in> set (inputs M) . \<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
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














lemma asdf_movie5: 
  assumes "r_distinguishable M q1 q2"
  shows "\<exists>k. r_distinguishable_k M q1 q2 k"
proof (rule ccontr)
  assume c_assm: "\<nexists>k. r_distinguishable_k M q1 q2 k"

  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  (* use only transitions to non-r-distinguishable states *)
  let ?f = "\<lambda> t . \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)"
  let ?ft = "filter ?f (transitions ?P)"
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
      then have "t \<in> set (transitions ?P)" and "(\<lambda> t . ?f t) t" and "is_wf_transition ?P t" 
        by (metis filter_set member_filter wf_transitions.simps)+
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



  have "\<And> k q . q \<in> reachable_k ?PC (q1,q2) k \<Longrightarrow> completely_specified_state ?PC q"  
  proof -
    fix k q assume "q \<in> reachable_k ?PC (q1,q2) k"
    then show "completely_specified_state ?PC q"
    proof (induction k)
      case 0

      have "reachable_k ?PC (q1,q2) 0 = {(q1,q2)}"
        using reachable_k_0[of ?PC "(q1,q2)"] by assumption
      then have "q = (q1,q2)" 
        using "0.prems" by blast

      moreover have "completely_specified_state ?PC (q1,q2)"
      proof (rule ccontr)
        assume "\<not> completely_specified_state ?PC (q1,q2)"
        then obtain x where "x \<in> set (inputs ?PC)"
                        and "\<not> (\<exists>t\<in>h ?PC. t_source t = (q1, q2) \<and> t_input t = x)" 
          unfolding completely_specified_state.simps by blast

        have "\<not> (\<exists>t\<in>h ?P. t_source t = (q1, q2) \<and> t_input t = x \<and> ?f t)"
          using h_ft \<open>\<not> (\<exists>t\<in>h ?PC. t_source t = (q1, q2) \<and> t_input t = x)\<close> mem_Collect_eq
          by blast

        then have *: "\<nexists>t1 t2.
                      t1 \<in> h M \<and>
                      t2 \<in> h M \<and>
                      t_source t1 = q1 \<and>
                      t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2
                      \<and> \<not> r_distinguishable_k M q1 q2 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (t_target t1) (t_target t2) k)"
          by (metis from_FSM_h fst_conv prod.exhaust_sel product_transition snd_conv)
        then have  "\<And> t1 t2.
                      (t1 \<in> h M \<and>
                       t2 \<in> h M \<and>
                       t_source t1 = q1 \<and>
                       t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)
                      \<Longrightarrow> r_distinguishable_k M q1 q2 0 \<or> (\<exists> k . r_distinguishable_k M (t_target t1) (t_target t2) k)"
          by blast
          
        
        have "\<exists> k . r_distinguishable_k M q1 q2 k"
        proof (cases "r_distinguishable_k M q1 q2 0")
          case True
          then show ?thesis by blast
        next
          case False
          

          let ?tp = "{(t1,t2) | t1 t2 . t1 \<in> h M \<and>
                                         t2 \<in> h M \<and>
                                         t_source t1 = q1 \<and>
                                         t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 }"

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
                                 t_source ?t1 = q1 \<and>
                                 t_source ?t2 = q2 \<and> t_input ?t1 = x \<and> t_input ?t2 = x \<and> t_output ?t1 = t_output ?t2" by auto
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
                using k_ex someI_ex by smt (* TODO *)
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
                       t_source t1 = q1 \<and>
                       t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)
                      \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) kMax"
            using * by blast
          then have "r_distinguishable_k M q1 q2 (Suc kMax)"
            unfolding r_distinguishable_k.simps
            by (metis (no_types, lifting) FSM3.product.simps \<open>x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>t. \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> (\<nexists>k. r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>))\<close> from_FSM_product_inputs select_convs(2) update_convs(4)) 
          then show ?thesis by blast  
        qed

        then show "False" using c_assm by blast


            
            
            

          then have "\<exists> k . \<forall> t1 t2 . 
                      (t1 \<in> h M \<and>
                       t2 \<in> h M \<and>
                       t_source t1 = q1 \<and>
                       t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)
                       \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
            
          then show ?thesis unfolding r_distinguishable_k.simps sorry
        qed 
          
        then have "r_distinguishable_k M q1 q2 ( |?P| + 1 )"
          by (smt FSM3.product.simps \<open>x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>t. \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) |product (from_FSM M q1) (from_FSM M q2)| ) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>))\<close> add.commute from_FSM_product_inputs plus_1_eq_Suc r_distinguishable_k.simps(2) select_convs(2) update_convs(4))
          (* TODO*)
        then show "False" using * by blast
      qed


      then show ?case sorry
    next
      case (Suc k)
      then show ?case sorry
    qed


















lemma asdf_movie4: 
  assumes "r_distinguishable M q1 q2"
  shows "\<exists>k. r_distinguishable_k M q1 q2 k"
proof (rule ccontr)
  assume *: "\<nexists>k. r_distinguishable_k M q1 q2 k"

  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  (* witness list *)
  let ?f = "\<lambda> t . (filter (\<lambda> t' . t_source t' = t_source t \<and> t_input t' = t_input t \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) 0) (transitions ?P))"
  let ?ft = "filter (\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)) (transitions ?P)"
  let ?PC = "?P\<lparr> transitions := ?ft \<rparr>"  
  (*let ?ct = "filter (\<lambda> t . \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) |?P| ) (transitions ?P)"
  let ?PC = "?P\<lparr> transitions := ?ct \<rparr>"*)
  

  have h_ft : "h ?PC = { t \<in> h ?P . ?f t \<noteq> [] \<and> t = hd (?f t) }"
  proof -
    have wf_eq: "\<And> t . is_wf_transition ?PC t = is_wf_transition ?P t"
      by (metis (no_types, lifting) FSM3.product.simps is_wf_transition.simps select_convs(2) select_convs(3) update_convs(4))
    have "transitions ?PC = ?ft"
        by (metis (mono_tags, lifting) select_convs(4) surjective update_convs(4))

    have "\<And> t . t \<in> h ?PC \<Longrightarrow> t \<in> h ?P \<and> ?f t \<noteq> [] \<and> t = hd (?f t)"
    proof -
      fix t assume "t \<in> h ?PC"
      then have "t \<in> h ?P" 
        by (metis (no_types, lifting) FSM3.product.simps filter_set member_filter product_transitions_wf select_convs(4) update_convs(4) wf_transitions.simps)
      moreover have "?f t \<noteq> [] \<and> t = hd (?f t)"
      proof (rule ccontr)
        assume "\<not>(?f t \<noteq> [] \<and> t = hd (?f t))"
        then have "\<not>((\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)) t)" by metis
        have  "t \<in> set (transitions ?P)"
          using \<open>t \<in> h ?P\<close> unfolding wf_transitions.simps
          by (metis (no_types, lifting) filter_set member_filter)
        have "t \<notin> set ?ft" 
          using filter_list_set_not_contained[OF \<open>t \<in> set (transitions ?P)\<close>, of "(\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t))", OF \<open>\<not>((\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)) t)\<close> ] by assumption
        then have "t \<notin> set (transitions ?PC)"
          using \<open>transitions ?PC = ?ft\<close> by metis
        then have "t \<notin> h ?PC" 
          unfolding wf_transitions.simps
          by (metis (no_types, lifting) filter_set member_filter)   
        then show "False" using \<open>t \<in> h ?PC\<close> by blast
      qed
      ultimately show "t \<in> h ?P \<and> ?f t \<noteq> [] \<and> t = hd (?f t)" by fastforce
    qed

    moreover have "\<And> t . t \<in> h ?P \<and> ?f t \<noteq> [] \<and> t = hd (?f t) \<Longrightarrow> t \<in> h ?PC"
    proof -
      fix t assume "t \<in> h ?P \<and> ?f t \<noteq> [] \<and> t = hd (?f t)"
      then have "t \<in> set (transitions ?P)" and "((\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)) t)" and "is_wf_transition ?P t"
        by (metis filter_set member_filter wf_transitions.simps)+
      have "t \<in> set ?ft"
        using filter_list_set[OF \<open>t \<in> set (transitions ?P)\<close>, of "((\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)))", OF \<open>((\<lambda> t . ?f t \<noteq> [] \<and> t = hd (?f t)) t)\<close>] by assumption
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
        
      

    


  have "\<And> k q . q \<in> reachable_k ?PC (q1,q2) k \<Longrightarrow> completely_specified_state ?PC q"
  proof -
    fix k 
    show "\<And> q . q \<in> reachable_k ?PC (q1,q2) k \<Longrightarrow> completely_specified_state ?PC q"
    using * proof (induction k) (* arbitrary: q1 q2) *)
      case 0

      have "reachable_k ?PC (q1,q2) 0 = {(q1,q2)}"
        using reachable_k_0[of ?PC "(q1,q2)"] by assumption
      then have "q = (q1,q2)" 
        using "0.prems" by blast

      moreover have "completely_specified_state ?PC (q1,q2)"
      proof (rule ccontr)
        assume "\<not> completely_specified_state ?PC (q1,q2)"
        then obtain x where "x \<in> set (inputs ?PC)"
                        and "\<not> (\<exists>t\<in>h ?PC. t_source t = (q1, q2) \<and> t_input t = x)" 
          unfolding completely_specified_state.simps by blast

        have "\<not> (\<exists>t\<in>h ?P. t_source t = (q1, q2) \<and> t_input t = x \<and> ?f t \<noteq> [] \<and> t = hd (?f t) )"
          using h_ft \<open>\<not> (\<exists>t\<in>h ?PC. t_source t = (q1, q2) \<and> t_input t = x)\<close> mem_Collect_eq by smt (*TODO*)

        then have "\<nexists>t1 t2.
                      t1 \<in> h M \<and>
                      t2 \<in> h M \<and>
                      t_source t1 = q1 \<and>
                      t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2
                      \<and> \<not> r_distinguishable_k M (t_target t1) (t_target t2) |?P| "
          by (metis from_FSM_h fst_conv prod.exhaust_sel product_transition snd_conv)
        then have "r_distinguishable_k M q1 q2 ( |?P| + 1 )"
          by (smt FSM3.product.simps \<open>x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>t. \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) |product (from_FSM M q1) (from_FSM M q2)| ) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>))\<close> add.commute from_FSM_product_inputs plus_1_eq_Suc r_distinguishable_k.simps(2) select_convs(2) update_convs(4))
          (* TODO*)
        then show "False" using * by blast
      qed

      ultimately show ?case by fastforce
    next
      case (Suc k)

      
      
      then show ?case 
      proof (cases "q \<in> reachable_k ?PC (q1,q2) k")
        case True
        then show ?thesis
          using Suc.prems Suc.IH[of q] by fastforce
      next
        case False
        then obtain p where "path ?PC (q1,q2) p"
                        and "target p (q1,q2) = q"
                        and "length p = Suc k"
          using Suc.prems(1)
          by (smt le_SucE mem_Collect_eq reachable_k.simps) (*TODO*)
        
        
        then show ?thesis sorry
      qed

      
    qed
  qed

  then have "\<forall> q \<in> nodes ?PC . completely_specified_state ?PC q"
    sorry

  then have "completely_specified ?PC" 
    using completely_specified_states[of ?PC] by fastforce
  moreover have "is_submachine ?PC ?P"
    unfolding is_submachine.simps
    by (smt FSM3.product.simps filter_filter filter_is_subset product_transitions_wf select_convs(1) select_convs(2) select_convs(3) select_convs(4) update_convs(4) wf_transitions.simps) 
    (* TODO *)
  ultimately have "r_compatible M q1 q2"
    unfolding r_compatible.simps by blast
  then show "False" 
    using assms by fastforce
qed



fun completely_specified_k :: "'a FSM \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "completely_specified_k M q k = (\<forall> p . (path M q p \<and> length p \<le> k) \<longrightarrow> completely_specified_state M (target p q))"

lemma asdf_movie: 
  assumes "\<not> r_distinguishable_k M q1 q2 k"
  shows "\<exists> f . \<forall> q \<in> reachable_k (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) k . \<forall> x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2))) . f q x \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source (f q x) = q \<and> t_input (f q x) = x"
using assms proof (induction k arbitrary: q1 q2)
  case 0
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  
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
      using 0 by simp
  qed
  then have "\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
    unfolding completely_specified_state.simps by blast

  show "\<exists> f . \<forall> q \<in> reachable_k ?P (q1,q2) 0 . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = q \<and> t_input (f q x) = x"
  proof 

    let ?f = "\<lambda> q x . SOME t . t \<in> h ?P \<and> t_source t = q \<and> t_input t = x"

    have "reachable_k ?P (q1,q2) 0 = {(q1,q2)}"
      using reachable_k_0[of ?P "(q1,q2)"] by assumption
    moreover have "\<forall> x \<in> set (inputs ?P) . ?f (q1,q2) x \<in> h ?P \<and> t_source (?f (q1,q2) x) = (q1,q2) \<and> t_input (?f (q1,q2) x) = x"
      using \<open>\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x\<close>
      by (metis (mono_tags, lifting) someI_ex)
    ultimately show "\<forall> q \<in> reachable_k ?P (q1,q2) 0 . \<forall> x \<in> set (inputs ?P) . ?f q x \<in> h ?P \<and> t_source (?f q x) = q \<and> t_input (?f q x) = x"
    proof -
      { fix nn :: nat and pp :: "'a \<times> 'a"
      { assume "(SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = (q1, q2) \<and> t_input p = nn) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
        { assume "(q1, q2) \<noteq> pp"
          then have "nn \<notin> set (inputs (product (from_FSM M q1) (from_FSM M q2))) \<or> pp \<notin> reachable_k (product (from_FSM M q1) (from_FSM M q2)) (q1, q2) 0 \<or> (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_input (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = nn \<and> t_source (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = pp"
            by (metis (no_types) \<open>reachable_k (product (from_FSM M q1) (from_FSM M q2)) (q1, q2) 0 = {(q1, q2)}\<close> singletonD) }
        then have "nn \<notin> set (inputs (product (from_FSM M q1) (from_FSM M q2))) \<or> pp \<notin> reachable_k (product (from_FSM M q1) (from_FSM M q2)) (q1, q2) 0 \<or> (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_input (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = nn \<and> t_source (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = pp"
          using \<open>\<forall>x\<in>set (inputs (product (from_FSM M q1) (from_FSM M q2))). (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) = (q1, q2) \<and> t_input (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) = x\<close> by fastforce }
      then have "nn \<notin> set (inputs (product (from_FSM M q1) (from_FSM M q2))) \<or> pp \<notin> reachable_k (product (from_FSM M q1) (from_FSM M q2)) (q1, q2) 0 \<or> (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_input (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = nn \<and> t_source (SOME p. p \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source p = pp \<and> t_input p = nn) = pp"
        using \<open>\<forall>x\<in>set (inputs (product (from_FSM M q1) (from_FSM M q2))). (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) = (q1, q2) \<and> t_input (SOME t. t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and> t_source t = (q1, q2) \<and> t_input t = x) = x\<close> by blast }
      then show ?thesis
        by blast
    qed
  qed
next
  case (Suc k)
  then show ?case sorry
qed




lemma asdf':
  assumes "completely_specified_state M q"
  and "\<forall> t \<in> h M . t_source t = q \<longrightarrow> (\<exists> S . is_submachine S (from_FSM M (t_target t)) \<and> completely_specified_k S (t_target t) k)"
shows "\<exists> S . is_submachine S M \<and> completely_specified_k S q (Suc k)"
proof -
  have "\<forall> p . (path M q p \<and> length p \<le> k) \<longrightarrow> completely_specified_state M (target p q)"


lemma asdf':
  assumes "completely_specified_state M q"
  and "\<forall> t \<in> h M . t_source t = q \<longrightarrow> (\<exists> S . is_submachine S (from_FSM M (t_target t)) \<and> (\<forall> q \<in> reachable_k S (q1,q2) k . completely_specified_state S q))"
shows "\<exists> S . is_submachine S M \<and> (\<forall> q \<in> reachable_k S q (Suc k) . completely_specified_state S q)"
using assms proof (induction k arbitrary: q)
  case 0
  then show ?case sorry
next
  case (Suc k)
  then show ?case sorry
qed



lemma asdf :
  assumes "\<not> (\<exists> S . is_submachine S (product (from_FSM M q1) (from_FSM M q2)) \<and> (\<forall> q \<in> reachable_k S (q1,q2) k . completely_specified_state S q))"
  shows "r_distinguishable_k M q1 q2 k"
using assms proof (induction k arbitrary: q1 q2)
  case 0
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  have "\<not> completely_specified_state ?P (q1,q2)" 
  proof 
    assume "completely_specified_state ?P (q1,q2)"
    moreover have "reachable_k ?P (q1,q2) 0 = {(q1,q2)}"
      by (meson reachable_k_0) 
    ultimately have "\<forall> q \<in> reachable_k ?P (q1,q2) 0 . completely_specified_state ?P q"
      by (metis singletonD) 
    moreover have "is_submachine ?P ?P" 
      unfolding is_submachine.simps by fast
    ultimately show "False" 
      using "0.prems" by blast
  qed
  
  then show ?case
    unfolding r_distinguishable_k.simps completely_specified_state.simps
    by (metis from_FSM_h from_FSM_product_inputs fst_conv prod.exhaust_sel product_transition snd_conv)
next
  case (Suc k)
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  (* initial state incomplete or reaches some state for which ex. no k-complete submachine *)
  show ?case 
  proof (cases "completely_specified_state ?P (q1,q2)")
    case True
    then 
    then show ?thesis 
  next
    case False
    then show ?thesis 
      unfolding r_distinguishable_k.simps completely_specified_state.simps
      by (metis from_FSM_h from_FSM_product_inputs fst_conv prod.exhaust_sel product_transition snd_conv)
  qed
qed


lemma r_distinguishable_alt_def :
  assumes "completely_specified M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  shows "r_distinguishable M q1 q2 \<longleftrightarrow> (\<exists> k . r_distinguishable_k M q1 q2 k)"
proof 
  show "r_distinguishable M q1 q2 \<Longrightarrow> \<exists>k. r_distinguishable_k M q1 q2 k" 
  proof (rule ccontr)

    assume "r_distinguishable M q1 q2" 
       and "\<nexists>k. r_distinguishable_k M q1 q2 k"

    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    (*
    have "\<And>k . (\<not> r_distinguishable_k M q1 q2 k) \<Longrightarrow> \<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (q1,q2) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (q1,q2) \<and> t_input (f q x) = x"
    *)
    have "\<And>k . (\<not> r_distinguishable_k M q1 q2 k) \<Longrightarrow> \<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (q1,q2) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (q1,q2) \<and> t_input (f q x) = x"
    proof -
      fix k assume "(\<not> r_distinguishable_k M q1 q2 k)"
      then show "\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (q1,q2) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (q1,q2) \<and> t_input (f q x) = x"
      proof (induction k arbitrary: q1 q2)
        case 0
        let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
        
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
            using 0 by simp
        qed
        then have "\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
          unfolding completely_specified_state.simps by blast

        show "\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (q1,q2) 0 . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (q1,q2) \<and> t_input (f q x) = x"
        proof 

          let ?f = "\<lambda> q x . SOME t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
          let ?PF = "(?P\<lparr>transitions := filter (\<lambda> t . ?f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>)"
      
          have "reachable_k ?PF (q1,q2) 0 = {(q1,q2)}"
            using reachable_k_0[of ?PF "(q1,q2)"] by assumption
          moreover have "\<forall> x \<in> set (inputs ?P) . ?f (q1,q2) x \<in> h ?P \<and> t_source (?f (q1,q2) x) = (q1,q2) \<and> t_input (?f (q1,q2) x) = x"
            using \<open>\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x\<close>
            by (metis (mono_tags, lifting) someI_ex) 
          ultimately show "\<forall> q \<in> reachable_k ?PF (q1,q2) 0 . \<forall> x \<in> set (inputs ?P) . ?f q x \<in> h ?P \<and> t_source (?f q x) = (q1,q2) \<and> t_input (?f q x) = x"
            by (metis (no_types, lifting) singletonD)
        qed
      next
        case (Suc k)
        let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
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
          then have "r_distinguishable_k M q1 q2 k"
            by (metis nat_induct r_distinguishable_k_Suc_k_alt_def)
          then show "False"
            using Suc.prems by simp
        qed
        then have "\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
          unfolding completely_specified_state.simps by blast



        
        
        have "\<forall> x \<in> set (inputs M) . \<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
        proof 
          fix x assume "x \<in> set (inputs M)"

          have "\<not>(\<exists> x \<in> set (inputs M) . \<forall> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
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

        
        have "\<forall> x \<in> set (inputs M) . \<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> (\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (t_target t) \<and> t_input (f q x) = x)"
        proof 
          fix x assume "x \<in> set (inputs M)"
          then obtain t where *: "t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x" 
                          and "\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
            using \<open>\<forall> x \<in> set (inputs M) . \<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close> by blast
          let ?PT = "(product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))"
          have "(fst (t_target t), snd (t_target t)) = t_target t"
            by auto
          then have "(\<exists> f . \<forall> q \<in> reachable_k (?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>) (t_target t) k . \<forall> x \<in> set (inputs ?PT) . f q x \<in> h ?PT \<and> t_source (f q x) = (t_target t) \<and> t_input (f q x) = x)"
            using Suc.IH[OF \<open>\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close>] 
            by presburger 
          have "transitions ?PT = transitions ?P" 
            using from_FSM_product_transitions by metis
          then have "\<And> f . filter f (transitions ?PT) = filter f (transitions ?P)" 
            by metis
          then have "\<And> f . transitions (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) = transitions (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>)"
            by (metis FSM3.product.simps select_convs(4) update_convs(4)) 
          then have "\<And> f . h (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) = h (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>)"
          proof -
            have "\<And> f . set (inputs (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>)) = set (inputs (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>))"
              by (metis (no_types, lifting) from_FSM.simps product_simps(2) select_convs(2) surjective update_convs(4))
            moreover have "\<And> f . set (outputs (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>)) = set (outputs (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>))"
              by (metis (no_types, lifting) from_FSM.simps product_simps(3) select_convs(3) surjective update_convs(4))

            ultimately have "\<And> t f . is_wf_transition (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) t = is_wf_transition (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>) t"
              by (metis is_wf_transition.simps)
            then show "\<And> f . h (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) = h (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>)" 
              by (metis \<open>\<And> f . transitions (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) = transitions (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>)\<close> filter_cong wf_transitions.simps)
          qed           

            
          then have "\<And> f . reachable_k (?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>) (t_target t) k = reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k"
          proof -
            fix f
            have "h (?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>) = h (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>)"
              using \<open>\<And> f . h (?PT\<lparr>transitions := filter f (transitions ?PT)\<rparr>) = h (?P\<lparr>transitions := filter f (transitions ?P)\<rparr>)\<close> by blast
            then show "reachable_k (?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>) (t_target t) k = reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k"
              unfolding reachable_k.simps using h_equivalence_path[of "(?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>)" "(?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>)"] Collect_cong by smt (* TODO *)
          qed
          
          have "(\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (t_target t) \<and> t_input (f q x) = x)"
            using Suc.IH[OF \<open>\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close>]
                  \<open>\<And> f . reachable_k (?PT\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?PT)\<rparr>) (t_target t) k = reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k\<close> 
                  \<open>\<exists>f. \<forall>q\<in>reachable_k (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))) \<lparr>transitions := filter (\<lambda>t. f (t_source t) (t_input t) = t) (transitions (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))))\<rparr>) (t_target t) k. \<forall>x\<in>set (inputs (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))). f q x \<in> h (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))) \<and> t_source (f q x) = t_target t \<and> t_input (f q x) = x\<close> from_FSM_product_h from_FSM_product_inputs
            by smt (* TODO *)

          show "\<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> (\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (t_target t) \<and> t_input (f q x) = x)"
            using "*" \<open>(\<exists> f . \<forall> q \<in> reachable_k (?P\<lparr>transitions := filter (\<lambda> t . f (t_source t) (t_input t) = t) (transitions ?P)\<rparr>) (t_target t) k . \<forall> x \<in> set (inputs ?P) . f q x \<in> h ?P \<and> t_source (f q x) = (t_target t) \<and> t_input (f q x) = x)\<close> by smt
        qed


        

        



        let ?f0 = "\<lambda> q x . SOME t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"

        (*let ?f0 = "\<lambda> q x . SOME t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"*)
        have "\<forall> x \<in> set (inputs ?P) . \<not> r_distinguishable ?f0 (q1,q2) x 


        

      qed



    
    have "\<And>k . (\<not> r_distinguishable_k M q1 q2 k) \<Longrightarrow> \<exists> H . H \<subseteq> h ?P \<and> (\<forall> xs . ((set xs \<subseteq> set (inputs ?P) \<and> length xs \<le> k) \<longrightarrow> (\<exists> p . set p \<subseteq> H \<and> map fst (p_io p) = xs \<and> (p = [] \<or> t_source (hd p) = (q1,q2)) \<and> (\<forall> x \<in> set (inputs ?P) . \<exists> t \<in> H . t_source t = (q1,q2) \<and> t_input t = x))))"
    proof -
      fix k assume "(\<not> r_distinguishable_k M q1 q2 k)"
      then show "\<exists> H . H \<subseteq> h ?P \<and> (\<forall> xs . ((set xs \<subseteq> set (inputs ?P) \<and> length xs \<le> k) \<longrightarrow> (\<exists> p . set p \<subseteq> H \<and> map fst (p_io p) = xs \<and> (p = [] \<or> t_source (hd p) = (q1,q2)) \<and> (\<forall> x \<in> set (inputs ?P) . \<exists> t \<in> H . t_source t = (q1,q2) \<and> t_input t = x))))"
      proof (induction k arbitrary: q1 q2)
        case 0
        let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
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
            using 0 by simp
        qed
            
        moreover have "reachable_k ?P (q1,q2) 0 = {(q1,q2)}" by auto
        
        ultimately show ?case sorry 
      next
        case (Suc k)
        then show ?case sorry
      qed
    qed

    moreover have "\<not> r_distinguishable_k M q1 q2 ( |?P| - 1 )"
      using \<open>\<nexists>k. r_distinguishable_k M q1 q2 k\<close> by blast

    ultimately obtain H :" "\<exists> H . H \<subseteq> h ?P \<and> (\<forall> xs . ((set xs \<subseteq> set (inputs ?P) \<and> length xs \<le> k) \<longrightarrow> (\<exists> p . set p \<subseteq> H \<and> map fst (p_io p) = xs \<and> (p = [] \<or> t_source (hd p) = (q1,q2)) \<and> (\<forall> x \<in> set (inputs ?P) . \<exists> t \<in> H . t_source t = (q1,q2) \<and> t_input t = x))))"

    show "False" 
    


    have "\<And>k xs . (\<not> r_distinguishable_k M q1 q2 k) \<Longrightarrow> set xs \<subseteq> set (inputs ?P) \<Longrightarrow> length xs \<le> k \<Longrightarrow> \<exists> S p . is_submachine S ?P \<and> path ?P (q1,q2) p \<and> map fst (p_io p) = xs \<and> completely_specified_state ?P (target p (q1,q2))"
    proof -
      fix k assume a1 : "\<not> r_distinguishable_k M q1 q2 k"
      fix xs assume a2 : "set xs \<subseteq> set (inputs ?P)"
                and a3 : "length xs \<le> k"
      from a1 a2 a3 show "\<exists> S p . is_submachine S ?P \<and> path ?P (q1,q2) p \<and> map fst (p_io p) = xs \<and> completely_specified_state ?P (target p (q1,q2))"
      proof (induction k arbitrary: q1 q2)
        case 0
        let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
        let 
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
            using 0 by simp
        qed
            
        moreover have "reachable_k ?P (q1,q2) 0 = {(q1,q2)}" by auto
        
        ultimately show ?case
          by (metis singletonD) 
      next
        case (Suc k)
        from Suc.prems have "\<forall> x \<in> set (inputs M) . \<exists> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<and> \<not> r_distinguishable_k M q1' q2' k"
          by auto
        then show ?case sorry
      qed
  
  proof (rule ccontr)
    assume "r_distinguishable M q1 q2"
    assume "\<nexists>k. r_distinguishable_k M q1 q2 k"
    
    then show "False" sorry
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
          using Suc.prems(1) by auto

        from Suc obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                            and "completely_specified S"
          by (meson r_compatible.elims(2)) 

        have "x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2)))"
          using \<open>x \<in> set (inputs M)\<close> by auto
        then have "x \<in> set (inputs S)" 
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis is_submachine.elims(2)) 

        moreover have "initial S = (q1,q2)"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close> by auto
        ultimately obtain y q1' q2' where "((q1,q2),x,y,(q1',q2')) \<in> h S"
          using \<open>completely_specified S\<close> using nodes.initial by fastforce 
        then have "((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (meson contra_subsetD is_submachine.elims(2)) 
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

        


end