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


definition product :: "'state1 FSM \<Rightarrow> 'state2 FSM \<Rightarrow> ('state1 \<times> 'state2) FSM" where
  "product A B \<equiv>
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

lemma h_contents :
  assumes "t \<in> h M"
  and     "t_source t \<in> nodes M"
shows "t_target t \<in> nodes M" 
and   "t_input t \<in> set (inputs M)"
and   "t_output t \<in> set (outputs M)"
  using assms by auto

fun deterministic :: "'a FSM \<Rightarrow> bool" where
  "deterministic M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . card { t \<in> h M . t_source t = q \<and> t_input t = x} \<le> 1)" 

(*
lemma deterministic_alt_def :
  "deterministic M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . 
                       ((\<exists> q' y . (q,x,y,q') \<in> h M \<and> (\<forall> q'' y' . (q' \<noteq> q'' \<or> y \<noteq> y') \<longrightarrow> (q,x,y',q'') \<notin> h M)) 
                       \<or> \<not>(\<exists> q' y . (q,x,y,q') \<in> h M )))" 
*)
    
fun observable :: "'a FSM \<Rightarrow> bool" where
  "observable M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<forall> y . card { t \<in> h M . t_source t = q \<and> t_input t = x \<and> t_output t = y} \<le> 1)"

lemma t_source_alt_def : "t_source (q,x,y,q') = q" by auto
lemma t_input_alt_def  : "t_input  (q,x,y,q') = x" by auto
lemma t_output_alt_def : "t_output (q,x,y,q') = y" by auto
lemma t_target_alt_def : "t_target (q,x,y,q') = q'" by auto

lemma h_access : "(q,x,y,q') \<in> h M \<longleftrightarrow> (\<exists> t \<in> h M . (t_source t = q \<and> t_input t = x \<and> t_output t = y \<and> t_target t = q'))" by auto
lemma h_access' : "t \<in> h M \<longleftrightarrow> (t_source t, t_input t, t_output t, t_target t) \<in> h M" by auto

lemma observable_alt_def :
  "observable M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<forall> y . card { (q,x,y,q') | q' . (q,x,y,q') \<in> h M } \<le> 1)"
proof -
  have "\<And> q x y. {(q,x,y,q') | q' . (q,x,y,q') \<in> h M } = { t \<in> h M . t_source t = q \<and> t_input t = x \<and> t_output t = y}" by auto
  then have "\<And> q x y. card {(q,x,y,q') | q' . (q,x,y,q') \<in> h M } = card { t \<in> h M . t_source t = q \<and> t_input t = x \<and> t_output t = y}" by auto
  then show  ?thesis unfolding observable.simps
    by presburger 
qed
    


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


fun io_targets :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets M io q = {target p q | p . path M q p \<and> p_io p = io}"

fun io_targets' :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets' M io q = set (map (\<lambda> p . target p q) (filter (\<lambda> p . p_io p = io) (paths_of_length M q (length io))))"

fun fst_io_target'' :: "'a FSM \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "fst_io_target'' M io q = (case (map (\<lambda> p . target p q) (filter (\<lambda> p . p_io p = io) (paths_of_length M q (length io)))) of
     [] \<Rightarrow> None |
     xs \<Rightarrow> Some (hd xs))"

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

lemma io_targets_nodes :
  assumes "q \<in> nodes M"
  shows "io_targets M io q \<subseteq> nodes M"
  using assms nodes_path by fastforce

lemma nodes_finite :
  "finite (nodes M)"
  by (metis (no_types) List.finite_set finite_insert nodes'.simps nodes_code) 

lemma observable_io_targets : 
  assumes "observable M"
  and "io \<in> LS M q"
obtains q'
where "io_targets M io q = {q'}"
using assms proof (induction io arbitrary: q)
case Nil
then show ?case by auto
next
  case (Cons a io)
  then show ?case 
qed
 



value "fst_io_target' M_ex [(1,20),(1,10)] (initial M_ex)"



end