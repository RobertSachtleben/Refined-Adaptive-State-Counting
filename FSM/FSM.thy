theory FSM
imports Util

begin

section \<open>Finite State Machines\<close>

subsection \<open>Types\<close>

type_synonym Input = integer
type_synonym Output = integer

type_synonym 'state Transition = "('state \<times> Input \<times> Output \<times> 'state)"

abbreviation "t_source (a :: 'state Transition) \<equiv> fst a" 
abbreviation "t_input  (a :: 'state Transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: 'state Transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: 'state Transition) \<equiv> snd (snd (snd a))"

abbreviation "p_io (p :: 'state Transition list) \<equiv> map (\<lambda> t . (t_input t, t_output t)) p"

value "t_source (1,2,3,4::nat)"
value "t_input  (1,2,3,4::nat)"
value "t_output (1,2,3,4::nat)"
value "t_target (1,2,3,4::nat)"

record 'state FSM = 
  initial :: 'state 
  inputs  :: "Input list"
  outputs  :: "Output list"  
  transitions :: "('state Transition) list" 



subsection \<open>Example FSMs\<close>

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

definition "M_ex'' = (\<lparr> 
                      initial = 2::integer, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (3,1,10,5),
                                      (4,0,10,3),
                                      (4,2,20,2),
                                      (5,2,30,3)]\<rparr>) "

definition "M_ex''' = (\<lparr> 
                      initial = 2::integer, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (2,1,20,4),
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



subsection \<open>Nodes\<close>

(* TODO: refactor for use of h *)
inductive_set nodes :: "('state, 'b) FSM_scheme \<Rightarrow> 'state set" for M :: "('state, 'b) FSM_scheme" where
  initial[intro!]: "initial M \<in> nodes M" |
  step[intro!]: "t \<in> set (transitions M) \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_input t \<in> set (inputs M) \<Longrightarrow> t_output t \<in> set (outputs M) \<Longrightarrow> t_target t \<in> nodes M"

instantiation FSM_ext  :: (type,type) size 
begin

definition size where [simp, code]: "size (m::('a, 'b) FSM_ext) = card (nodes m)"

instance ..

end



subsection \<open>Transition Relation as a List of IO-Valid Transitions Originating From Nodes (Well-Formed Transitions)\<close>

abbreviation(input) "is_io_valid_transition M t \<equiv> ((t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun io_valid_transitions :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition list" where
  "io_valid_transitions M = filter (is_io_valid_transition M) (transitions M)"

abbreviation(input) "hIO M \<equiv> set (io_valid_transitions M)"


abbreviation(input) "is_wf_transition M t \<equiv> ((t_source t \<in> nodes M) \<and> (t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun wf_transitions :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition list" where
  "wf_transitions M = filter (is_wf_transition M) (transitions M)"

lemma wf_transitions_alt_def : "wf_transitions M = filter (\<lambda>t . t_source t \<in> nodes M) (io_valid_transitions M)"
  using filter_filter[of "(\<lambda>t. t_source t \<in> nodes M)" "(\<lambda>t. t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))" "transitions M"]
  unfolding wf_transitions.simps io_valid_transitions.simps 
  by (metis (no_types, lifting) filter_cong) 

lemma wf_transition_iff[iff] : "t \<in> set (wf_transitions M) \<longleftrightarrow> (t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  


lemma io_valid_transition_simp : "t \<in> set (io_valid_transitions M) = (t \<in> set (transitions M) \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  
lemma wf_transition_simp : "t \<in> set (wf_transitions M) = (t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  

abbreviation(input) "h M \<equiv> set (wf_transitions M)"

lemma hIO_alt_def : "hIO M = { t . t \<in> set (transitions M) \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M)}"
  by auto

lemma h_alt_def : "h M = { t . t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M)}"
  by auto





subsection \<open>Paths\<close>

inductive path :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "q \<in> nodes M \<Longrightarrow> path M q []" |
  consIO[intro!] : "t \<in> set (transitions M) \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_input t \<in> set (inputs M) \<Longrightarrow> t_output t \<in> set (outputs M) \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_nil_elim[elim!]: "path M q []"
inductive_cases path_consIO_elim[elim!]: "path M q (t#ts)"

inductive path' :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "q \<in> nodes M \<Longrightarrow> path' M q []" |
  cons[intro!] : "t \<in> h M \<Longrightarrow> path' M (t_target t) ts \<Longrightarrow> path' M (t_source t) (t#ts)"

inductive_cases path'_nil_elim[elim!]: "path' M q []"
inductive_cases path'_consIO_elim[elim!]: "path' M q (t#ts)"

lemma path_alt_def : "path M q p = path' M q p" 
  by (induction p arbitrary: q; auto)

fun visited_states :: "'state \<Rightarrow> 'state Transition list \<Rightarrow> 'state list" where
  "visited_states q p = (q # map t_target p)"

fun target :: "'state Transition list \<Rightarrow> 'state \<Rightarrow> 'state" where
  "target p q = last (visited_states q p)"

lemma path_begin_node :
  assumes "path M q p"
  shows   "q \<in> nodes M" 
  using assms by (cases; auto)



lemma path_append[intro!] :
  assumes "path M q p1"
      and "path M (target p1 q) p2"
  shows "path M q (p1@p2)"
using assms by (induct p1 arbitrary: p2; auto)

lemma path_target_is_node :
  assumes "path M q p"
  shows   "target p q \<in> nodes M"
using assms by (induct p; auto)

lemma path_suffix :
  assumes "path M q (p1@p2)"
  shows "path M (target p1 q) p2"
using assms by (induction p1 arbitrary: q; auto)

lemma path_prefix :
  assumes "path M q (p1@p2)"
  shows "path M q p1"
using assms by (induction p1 arbitrary: q; auto; (metis path_begin_node))


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


lemma path_h :
  assumes "path M q p"
  shows "set p \<subseteq> h M"
  using assms by (induct p arbitrary: q; fastforce)


fun paths_of_length :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state Transition list list" where
  "paths_of_length M q n = filter (path M q) (lists_of_length (wf_transitions M) n)"

lemma paths_of_length_containment : 
  assumes "path M q p"
  shows "p \<in> set (paths_of_length M q (length p))"
  by (metis (no_types, lifting) assms filter_set lists_of_length_containment member_filter path_h paths_of_length.simps)


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

fun paths_up_to_length :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> nat \<Rightarrow> 'state Transition list list" where
  "paths_up_to_length M q 0 = [[]]" |
  "paths_up_to_length M q (Suc n) = (paths_up_to_length M q n) @ (paths_of_length M q (Suc n))"


lemma paths_up_to_length_path_set :
  assumes "q \<in> nodes M"
  shows "set (paths_up_to_length M q k) = { p . path M q p \<and> length p \<le> k }"
using assms proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)

  have "set (paths_up_to_length M q (Suc k)) = set (paths_up_to_length M q k) \<union> set (paths_of_length M q (Suc k))"
    using paths_up_to_length.simps(2) by (metis set_append) 
  
  moreover have "{p. path M q p \<and> length p \<le> Suc k} = {p. path M q p \<and> length p \<le> k} \<union> {p. path M q p \<and> length p = Suc k}"
    by auto

  ultimately show ?case using Suc.IH
    by (metis (no_types, lifting) Collect_cong assms paths_of_length_path_set)
qed


subsection \<open> Nodes and Paths \<close>

lemma nodes_path : 
  assumes "path M q p"
shows "(target p q) \<in> nodes M"
  using assms proof (induction p arbitrary: q rule: list.induct) 
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

lemma path_to_node : 
  assumes "q \<in> nodes M"
  shows "\<exists> p . path M (initial M) p \<and> q = target p (initial M)"
using assms proof (induction rule: nodes.induct)
  case initial
  then show "\<exists>p. path M (initial M) p \<and> initial M = target p (initial M)" by auto
next
  case (step t)
  obtain p where "path M (initial M) p" and "t_source t = target p (initial M)"
    using step.IH by blast
  then have "path M (initial M) (p@[t])"
    using step.hyps
    by (metis consIO nodes.step path.nil path_append) 
  moreover have "t_target t = target (p@[t]) (initial M)" by auto
  ultimately show "\<exists>p. path M (initial M) p \<and> t_target t = target p (initial M)"
    by meson 
qed





subsection \<open>Properties of Paths Visiting Distinct Nodes Only\<close>

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
  case (consIO t M ts)
  then show ?case 
  proof (cases "distinct (visited_states (t_target t) ts)")
    case True
    then have "q \<in> set (visited_states (t_target t) ts)"
      using consIO.prems by simp 
    then obtain p2 p3 where "ts = p2@p3" and "target p2 (t_target t) = q" 
      using visited_states_prefix[of q "t_target t" ts] by blast
    then have "(t#ts) = []@(t#p2)@p3 \<and> (t#p2) \<noteq> [] \<and> target [] q = target ([]@(t#p2)) q"
      using consIO.hyps by auto
    then show ?thesis by blast
  next
    case False
    then obtain p1 p2 p3 where "ts = p1@p2@p3" and "p2 \<noteq> []" and "target p1 (t_target t) = target (p1@p2) (t_target t)" 
      using consIO.IH by blast
    then have "t#ts = (t#p1)@p2@p3 \<and> p2 \<noteq> [] \<and> target (t#p1) q = target ((t#p1)@p2) q"
      by simp
    then show ?thesis by blast    
  qed
qed


lemma nondistinct_path_pumping :
  assumes "path M (initial M) p" 
      and "\<not> distinct (visited_states (initial M) p)"
  shows "\<exists> p . path M (initial M) p \<and> length p \<ge> n"
proof -
  from assms obtain p1 p2 p3 where "p = p1 @ p2 @ p3" and "p2 \<noteq> []" and "target p1 (initial M) = target (p1 @ p2) (initial M)"
    using nondistinct_path_loop[of M "initial M" p] by blast
  then have "path M (target p1 (initial M)) p3"
    using path_suffix[of M "initial M" "p1@p2" p3] \<open>path M (initial M) p\<close> by auto
  
  have "path M (initial M) p1"
    using path_prefix[of M "initial M" p1 "p2@p3"] \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> by auto
  have "path M (initial M) ((p1@p2)@p3)"
    using \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> by auto
  have "path M (target p1 (initial M)) p2" 
    using path_suffix[of M "initial M" p1 p2, OF path_prefix[of M "initial M" "p1@p2" p3, OF \<open>path M (initial M) ((p1@p2)@p3)\<close>]] by assumption
  have "target p2 (target p1 (initial M)) = (target p1 (initial M))"
    using path_append_target \<open>target p1 (initial M) = target (p1 @ p2) (initial M)\<close> by auto
  
  have "path M (initial M) (p1 @ (concat (replicate n p2)) @ p3)"  
  proof (induction n)
    case 0 
    then show ?case using path_append[OF \<open>path M (initial M) p1\<close> \<open>path M (target p1 (initial M)) p3\<close>]  by auto
  next
    case (Suc n)
    then show ?case
      using \<open>path M (target p1 (initial M)) p2\<close> \<open>target p2 (target p1 (initial M)) = target p1 (initial M)\<close> by auto 
  qed
  moreover have "length (p1 @ (concat (replicate n p2)) @ p3) \<ge> n"
  proof -
    have "length (concat (replicate n p2)) = n * (length p2)" 
      using concat_replicate_length by metis
    moreover have "length p2 > 0"
      using \<open>p2 \<noteq> []\<close> by auto
    ultimately have "length (concat (replicate n p2)) \<ge> n"
      by (simp add: Suc_leI)
    then show ?thesis by auto
  qed
  ultimately show "\<exists> p . path M (initial M) p \<and> length p \<ge> n" by blast
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

lemma visited_states_are_nodes :
  assumes "path M q1 p"
  shows "set (visited_states q1 p) \<subseteq> nodes M"
  by (metis assms nodes_path path_prefix subsetI visited_states_prefix)

lemma nodes_finite : "finite (nodes M)"
proof -
  have "\<And> q . q \<in> nodes M \<Longrightarrow> q = initial M \<or> q \<in> set (map t_target (transitions M))"
  proof -
    fix q assume "q \<in> nodes M"
    then show "q = initial M \<or> q \<in> set (map t_target (transitions M))"
      by (cases; simp)
  qed
  then have "nodes M \<subseteq> insert (initial M) (set (map t_target (transitions M)))"
    by auto
  moreover have "finite (set (map t_target (transitions M)))" 
    by auto
  ultimately show ?thesis
    by (simp add: finite_subset)  
qed



lemma distinct_path_length_limit_nodes :
  assumes "path M q p"
  and     "distinct (visited_states q p)"
shows "length p < size M"
proof (rule ccontr)
  assume *: "\<not> length p < size M"

  have "length (visited_states q p) = Suc (length p)"
    by simp
  then have "length (visited_states q p) \<ge> size M"
    using "*" by linarith
  moreover have "set (visited_states q p) \<subseteq> nodes M"
    by (metis assms(1) nodes_path path_prefix subsetI visited_states_prefix)
  ultimately have "\<not>distinct (visited_states q p)"
    using nodes_finite unfolding size_def
    by (metis "*" Suc_le_lessD \<open>length (visited_states q p) = Suc (length p)\<close> card_mono distinct_card size_def)
  then show "False" using assms(2) by auto
qed



subsection \<open> Calculating the Node Set by Enumerating All Paths Visiting Distinct Nodes \<close>


lemma distinct_path_to_node:
  assumes "q \<in> nodes M"
  shows "\<exists> p . path M (initial M) p \<and> q = target p (initial M) \<and> distinct (visited_states (initial M) p)"
  using path_to_node[OF assms] distinct_path_from_nondistinct_path
  by metis 



fun distinct_paths_up_to_length_from_initial :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "distinct_paths_up_to_length_from_initial M 0 = [[]]" |
  "distinct_paths_up_to_length_from_initial M (Suc n) = (let pn= distinct_paths_up_to_length_from_initial M n in
    pn @ map (\<lambda> pt . (fst pt)@[(snd pt)]) (filter (\<lambda>pt . (t_source (snd pt) = target (fst pt) (initial M)) \<and> distinct ((visited_states (initial M) (fst pt))@[(t_target (snd pt))])) (concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (io_valid_transitions M)) (filter (\<lambda>p . length p = n) pn)))))"



lemma distinct_paths_up_to_length_path_set : "set (distinct_paths_up_to_length_from_initial M n) = {p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> n}"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)

  let ?q0 = "initial M"
  let ?pn = "distinct_paths_up_to_length_from_initial M n"
  let ?pnS = "map (\<lambda> pt . (fst pt)@[(snd pt)]) (filter (\<lambda>pt . (t_source (snd pt) = target (fst pt) (initial M)) \<and> distinct ((visited_states (initial M) (fst pt))@[(t_target (snd pt))])) (concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (io_valid_transitions M)) (filter (\<lambda>p . length p = n) ?pn))))"

  

  have "distinct_paths_up_to_length_from_initial M (Suc n) = ?pn @ ?pnS"
    unfolding distinct_paths_up_to_length_from_initial.simps(2)[of M n] by metis
  then have "set (distinct_paths_up_to_length_from_initial M (Suc n)) = set ?pn \<union> set ?pnS"
    using set_append by metis

  have "\<And> p . p \<in> set ?pn \<Longrightarrow> length p \<le> n" using Suc.IH by blast
  then have "\<And> p . p \<in> set ?pn \<Longrightarrow> length p \<noteq> Suc n" by fastforce 
  moreover have "\<And> p . p \<in> set ?pnS \<Longrightarrow> length p = Suc n"  by auto
  ultimately have "set ?pn \<inter> set ?pnS = {}" by blast

  let ?sn = "{p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> n}"
  let ?snS = "{p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p = Suc n}"

  have "{p. path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> Suc n} = ?sn \<union> ?snS" by fastforce
  have "?sn \<inter> ?snS = {}" by fastforce

  

  let ?fc = "(\<lambda> pt . (fst pt)@[(snd pt)])"
  let ?ff = "(\<lambda>pt . (t_source (snd pt) = target (fst pt) ?q0) \<and> distinct ((visited_states ?q0 (fst pt))@[(t_target (snd pt))]))"
  let ?fp = "(concat (map (\<lambda>p . map (\<lambda> t . (p,t)) (io_valid_transitions M)) (filter (\<lambda>p . length p = n) ?pn)))"

  have "?pnS = map ?fc (filter ?ff ?fp)" by presburger
  have "set ?fp = {(p,t) | p t . p \<in> set ?pn \<and> t \<in> hIO M \<and> length p = n}" by fastforce
  then have "set ?fp = {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> hIO M \<and> length p = n}" 
    using Suc.IH by fastforce
  moreover have "set (filter ?ff ?fp) = {(p,t) \<in> set ?fp . t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"
    by fastforce
  ultimately have fffp : "set (filter ?ff ?fp) = {(p,t) \<in> {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> hIO M \<and> length p = n} . t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"    
    by presburger
  
  have fffp' : "\<dots> = {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> hIO M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"
    by blast
  
  have "\<And> p t . (path M ?q0 p \<and> t \<in> hIO M \<and> t_source t = target p ?q0) = (path M ?q0 p \<and> t \<in> h M \<and> t_source t = target p ?q0)"
    using wf_transition_simp[of _ M] io_valid_transition_simp[of _ M] path_target_is_node[of M "initial M"]
  proof -
    fix p :: "('a \<times> integer \<times> integer \<times> 'a) list" and t :: "'a \<times> integer \<times> integer \<times> 'a"
    show "(path M (initial M) p \<and> t \<in> set (io_valid_transitions M) \<and> t_source t = target p (initial M)) = (path M (initial M) p \<and> t \<in> set (wf_transitions M) \<and> t_source t = target p (initial M))"
      by (metis (no_types) \<open>\<And>p. path M (initial M) p \<Longrightarrow> target p (initial M) \<in> nodes M\<close> \<open>\<And>t. (t \<in> set (io_valid_transitions M)) = (t \<in> set (transitions M) \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))\<close> \<open>\<And>t. (t \<in> set (wf_transitions M)) = (t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))\<close>)
  qed
  then have fffp'': "{(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> hIO M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])} = {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"    
    by blast
  
  have "set (filter ?ff ?fp) = {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"
    using fffp fffp' fffp'' by presburger
  then have "set (filter ?ff ?fp) = {(p,t) | p t . path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t])}"
    by fastforce    
  moreover have "\<And> p t . (path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> t \<in> h M \<and> length p = n \<and> t_source t = target p ?q0 \<and> distinct ((visited_states ?q0 p)@[t_target t]))
                   = (path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n)"
  proof 
    have "\<And> p t . (visited_states ?q0 p)@[t_target t] = visited_states ?q0 (p@[t])" by auto
    then have *: "\<And> p t . distinct (visited_states ?q0 p @ [t_target t]) = (distinct (visited_states ?q0 p) \<and> distinct (visited_states ?q0 (p @ [t])))" by auto
    have **: "\<And> p t . (path M ?q0 p \<and> t \<in> h M \<and> t_source t = target p ?q0) = path M ?q0 (p @ [t])"
      using wf_transition_simp[of _ M] path_alt_def by (metis consIO nil nodes.step path_append path_consIO_elim path_prefix path_suffix) 

    

    show "\<And> p t .path M (initial M) p \<and>
           distinct (visited_states (initial M) p) \<and>
           t \<in> set (wf_transitions M) \<and>
           length p = n \<and>
           t_source t = target p (initial M) \<and>
           distinct (visited_states (initial M) p @ [t_target t]) \<Longrightarrow>
           path M (initial M) (p @ [t]) \<and>
           distinct (visited_states (initial M) (p @ [t])) \<and>
           length (p @ [t]) = Suc n"
      using * **
      by (meson length_append_singleton path_target_is_node) 

    show "\<And> p t .path M (initial M) (p @ [t]) \<and>
           distinct (visited_states (initial M) (p @ [t])) \<and>
           length (p @ [t]) = Suc n \<Longrightarrow>
           path M (initial M) p \<and>
           distinct (visited_states (initial M) p) \<and>
           t \<in> set (wf_transitions M) \<and>
           length p = n \<and>
           t_source t = target p (initial M) \<and> distinct (visited_states (initial M) p @ [t_target t])"
      using * **
      by fastforce
  qed

  ultimately have "set (filter ?ff ?fp) = {(p,t) | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
    by presburger
  then have "set (filter ?ff ?fp) = {(p,t) | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
    by auto
  moreover have "set ?pnS = image (\<lambda>pt. fst pt @ [snd pt]) (set (filter ?ff ?fp))" by auto
  ultimately have "set ?pnS = image (\<lambda>pt. fst pt @ [snd pt]) {(p,t) | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
    by presburger

  then have "set ?pnS = {(\<lambda>pt. fst pt @ [snd pt]) pt | pt . pt \<in> {(p,t) | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}}"
    using Setcompr_eq_image by metis
  then have "set ?pnS = {p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
    by auto
  moreover have "{p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n} = ?snS"
  proof 
    show "{p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n} \<subseteq> ?snS"
      by blast
    show "?snS \<subseteq> {p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
    proof 
      fix p assume "p \<in> ?snS"
      then have "length p > 0" by auto
      then have "p = (butlast p)@[last p]" by auto

      have "path M ?q0 ((butlast p)@[last p]) \<and> distinct (visited_states ?q0 ((butlast p)@[last p])) \<and> length ((butlast p)@[last p]) = Suc n"
        using \<open>p \<in> ?snS\<close> \<open>p = (butlast p)@[last p]\<close> by auto
      then have "(butlast p)@[last p] \<in> {p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
        by fastforce
      then show "p \<in> {p@[t] | p t . path M ?q0 (p@[t]) \<and> distinct (visited_states ?q0 (p@[t])) \<and> length (p@[t]) = Suc n}"
        using \<open>p = (butlast p)@[last p]\<close> by auto
    qed
  qed
  ultimately have "set ?pnS = ?snS" by presburger
    
  show ?case 
    using \<open>set (distinct_paths_up_to_length_from_initial M (Suc n)) = set ?pn \<union> set ?pnS\<close> 
          \<open>{p. path M ?q0 p \<and> distinct (visited_states ?q0 p) \<and> length p \<le> Suc n} = ?sn \<union> ?snS\<close>
          Suc.IH
          \<open>set ?pnS = ?snS\<close>
    by blast
qed  


fun nodes_from_distinct_paths :: "('a,'b) FSM_scheme \<Rightarrow> 'a list" where
  "nodes_from_distinct_paths M = remdups (map (\<lambda>p . target p (initial M)) (distinct_paths_up_to_length_from_initial M (length (io_valid_transitions M))))"


lemma nodes_code[code]: "nodes M = set (nodes_from_distinct_paths M)"
proof -
  have "set (nodes_from_distinct_paths M) = image (\<lambda>p . target p (initial M)) {p. path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> length (io_valid_transitions M)}"
    using distinct_paths_up_to_length_path_set[of M "length (io_valid_transitions M)"] by auto
  moreover have "{p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> length (io_valid_transitions M)} 
        = {p . path M (initial M) p \<and> distinct (visited_states (initial M) p)}" 
    using distinct_path_length_limit
    by (metis (no_types, lifting) le_trans length_filter_le wf_transitions_alt_def) 
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
        by (metis distinct_path_from_nondistinct_path path_to_node)
      then show "q \<in> {target ps (initial M) |ps. path M (initial M) ps \<and> distinct (visited_states (initial M) ps)}"
        by blast
    qed      
    ultimately show ?thesis by blast
  qed
      

  ultimately show ?thesis by fast
qed

value[code] "transitions M_ex_9"
value[code] "io_valid_transitions M_ex_9"
value[code] "wf_transitions M_ex_9"
value[code] "nodes M_ex_9"




subsection \<open> Calculating Paths \<close>

fun is_path :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "is_path M q [] = (q \<in> nodes M)" |
  "is_path M q (t#p) = (t_source t = q \<and> t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M) \<and> path M (t_target t) p)"

lemma path_code[code] : "path M q p = is_path M q p"
  by (induction p arbitrary: q; auto)
  
















(*
subsection \<open>Reachability by Transitive Closure and by Path\<close>

fun pairwise_immediately_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_immediately_reachable M =  image (\<lambda> t. (t_source t, t_target t)) (set (io_valid_transitions M))"

lemma wf_transrel_transition_ob : 
  assumes "(q,q') \<in> pairwise_immediately_reachable M"
  obtains t
  where "t \<in> set (io_valid_transitions M)"
    and "t_source t = q"
    and "t_target t = q'"
    and "is_io_valid_transition M t"
  using assms by auto

fun pairwise_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> ('state  \<times> 'state ) set" where
  "pairwise_reachable M = trancl (pairwise_immediately_reachable M)"

fun reachable :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
  "reachable M q q' = (q = q' \<or> (q, q') \<in> pairwise_reachable M)"

fun initially_reachable :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> bool" where
  "initially_reachable M q = reachable M (initial M) q"

fun nodes' :: "('state, 'b) FSM_scheme \<Rightarrow> 'state set" where
  "nodes' M = insert (initial M) (set (filter (initially_reachable M) (map t_target (io_valid_transitions M))))"



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
    then obtain t where "t \<in> hIO M"
                  and   "a = t_source t"
                  and   "b = t_target t"
      by auto
    then have "path M a [t] \<and> target [t] a = b" by auto
    then show ?case by force 
  next
    case (trancl_into_trancl a b c)
    then obtain p t where "t \<in> hIO M"
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

lemma reachable_next :
  assumes "reachable M q (t_source t)"
  and     "t \<in> hIO M"
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
  and     "t \<in> hIO M"
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
  and     "t \<in> hIO M"
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
*)







subsection \<open>Language\<close>

fun language_state_for_input :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "language_state_for_input M q xs = map p_io (filter (\<lambda> ts . xs = map t_input ts) (paths_of_length M q (length xs)))"

value "language_state_for_input M_ex_H 2 [1]"
value "language_state_for_input M_ex_9 0 [1,0]"

fun language_state_for_inputs :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list list \<Rightarrow> (Input \<times> Output) list list" where
  "language_state_for_inputs M q xss = concat (map (language_state_for_input M q) xss)" 

value "language_state_for_inputs M_ex_H 3 [[1]]"
value "language_state_for_inputs M_ex_H 3 [[1], [1,0]]"



lemma language_state_for_inputs_from_language_state_for_input :
  assumes "io \<in> set (language_state_for_inputs M q xss)"
  obtains xs 
  where "xs \<in> set xss"
    and "io \<in> set (language_state_for_input M q xs)"
   using concat_map_elem[of io "language_state_for_input M q" xss] assms unfolding language_state_for_inputs.simps by blast



fun LS\<^sub>i\<^sub>n :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> Input list set \<Rightarrow> (Input \<times> Output) list set" where 
  "LS\<^sub>i\<^sub>n M q U = { map (\<lambda> t . (t_input t, t_output t)) p | p . path M q p \<and> map t_input p \<in> U }"

abbreviation(input) "L\<^sub>i\<^sub>n M \<equiv> LS\<^sub>i\<^sub>n M (initial M)"


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
value "LS\<^sub>i\<^sub>n M_ex_9 2 {[1,1,1,1,1]}"


fun LS :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> (Input \<times> Output) list set" where
  "LS M q = { p_io p | p . path M q p }"

abbreviation(input) "L M \<equiv> LS M (initial M)"




subsection \<open> Basic FSM properties \<close>

fun completely_specified :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_alt_def : "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> q' y . (q,x,y,q') \<in> h M)"
  by force

value "completely_specified M_ex"
value "completely_specified M_ex_9"


fun deterministic :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "deterministic M = (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<longrightarrow> t_output t1 = t_output t2 \<and> t_target t1 = t_target t2)" 

lemma deterministic_alt_def : "deterministic M = (\<forall> q1 x y' y''  q1' q1'' . (q1,x,y',q1') \<in> h M \<and> (q1,x,y'',q1'') \<in> h M \<longrightarrow> y' = y'' \<and> q1' = q1'')" 
  by auto

value "deterministic M_ex"
value "deterministic M_ex''"


fun observable :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "observable M = (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<longrightarrow> t_target t1 = t_target t2)" 

lemma observable_alt_def : "observable M = (\<forall> q1 x y q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x,y,q1'') \<in> h M \<longrightarrow> q1' = q1'')" 
  by auto

value "observable M_ex"
value "observable M_ex'''"


fun single_input :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "single_input M = (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<longrightarrow> t_input t1 = t_input t2)" 

lemma single_input_alt_def : "single_input M = (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x',y',q1'') \<in> h M \<and> q1 \<in> nodes M \<longrightarrow> x = x')"
  unfolding single_input.simps by fastforce 
  

(* slightly more efficient method of deciding the single input property,
   avoids checking the same pair of transitions twice *)
fun single_input_by_transition_list :: "('a, 'b) FSM_scheme \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "single_input_by_transition_list M [] = True" |
  "single_input_by_transition_list M (t1#ts) = (case find (\<lambda> t2 . t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_source t1 \<in> nodes M \<and> t_input t1 \<noteq> t_input t2) ts of
    None \<Rightarrow> single_input_by_transition_list M ts | 
    Some _ \<Rightarrow> False)"


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

lemma single_input_code[code] : "single_input M = single_input_by_transition_list M (remdups (wf_transitions M))"
  unfolding single_input.simps using single_input_by_transition_list_correctness[of "remdups (wf_transitions M)" M]
  using set_remdups[of "wf_transitions M"] 
  by (metis order_refl)

value "single_input M_ex"



fun output_complete :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "output_complete M = (\<forall> t \<in> h M . \<forall> y \<in> set (outputs M) . \<exists> t' \<in> h M . t_source t = t_source t' \<and> t_input t = t_input t' \<and> t_output t' = y)" 

lemma output_complete_alt_def : "output_complete M = (\<forall> q x . (\<exists> y q' . (q,x,y,q') \<in> h M) \<longrightarrow> (\<forall> y \<in> set (outputs M) . \<exists> q' . (q,x,y,q') \<in> h M))" by (rule; fastforce)

value "output_complete M_ex"


fun acyclic :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "acyclic M = (\<forall> p . path M (initial M) p \<longrightarrow> distinct (visited_states (initial M) p))"


fun contains_cyclic_path :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "contains_cyclic_path M = (\<exists> p \<in> set (distinct_paths_up_to_length_from_initial M (size M)) . \<exists> t \<in> h M . path M (initial M) (p@[t]) \<and> \<not>distinct (visited_states (initial M) (p@[t]))) "


lemma acyclic_code[code] : "acyclic M = (\<not>contains_cyclic_path M)"
proof 
  show "FSM.acyclic M \<Longrightarrow> \<not> contains_cyclic_path M"
    by (meson acyclic.elims(2) contains_cyclic_path.elims(2))

  have "\<not> FSM.acyclic M \<Longrightarrow> contains_cyclic_path M"
  proof -
    assume "\<not> FSM.acyclic M"
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

    then have "(butlast ?minPath) \<in> set (distinct_paths_up_to_length_from_initial M (size M))"
      using \<open>path M (initial M) (butlast ?minPath)\<close> distinct_path_length_limit_nodes
      by (metis (no_types, lifting) distinct_paths_up_to_length_path_set less_imp_le mem_Collect_eq)
    moreover have "(last ?minPath) \<in> h M"
      by (metis (no_types, lifting) \<open>0 < length (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> \<open>path M (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> contra_subsetD last_in_set length_greater_0_conv path_h) 
    moreover have "path M (initial M) ((butlast ?minPath)@[(last ?minPath)]) \<and> \<not>distinct (visited_states (initial M) ((butlast ?minPath)@[(last ?minPath)]))"
      using \<open>0 < length (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> \<open>\<not> distinct (visited_states (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p}))\<close> \<open>path M (initial M) (ARG_MIN length io. io \<in> {p'. path M (initial M) p' \<and> \<not> distinct (visited_states (initial M) p') \<and> length p' \<le> length p})\<close> by auto
    ultimately show "contains_cyclic_path M"
      unfolding contains_cyclic_path.simps
      by meson 
  qed
  then show "\<not> contains_cyclic_path M \<Longrightarrow> FSM.acyclic M" by blast
qed



lemma acyclic_alt_def : "acyclic M = finite (L M)"
proof 
  show "acyclic M \<Longrightarrow> finite (L M)"
  proof -
    assume "acyclic M"
    then have "{ p . path M (initial M) p} \<subseteq> set (paths_up_to_length M (initial M) (size M))"
      using distinct_path_length_limit_nodes[of M "initial M"] paths_up_to_length_path_set[OF nodes.initial[of M], of "size M"]
      by fastforce 
    moreover have "finite (set (paths_up_to_length M (initial M) (size M)))"
      by auto
    ultimately have "finite { p . path M (initial M) p}"
      using finite_subset by blast
    then show "finite (L M)"
      unfolding LS.simps by auto
  qed

  show "finite (L M) \<Longrightarrow> acyclic M"
  proof (rule ccontr)
    assume "finite (L M)"
    assume "\<not> acyclic M"
    
    obtain max_io_len where "\<forall>io \<in> L M . length io < max_io_len"
      using finite_maxlen[OF \<open>finite (L M)\<close>] by blast
    then have "\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len"
    proof -
      fix p assume "path M (initial M) p"
      show "length p < max_io_len"
      proof (rule ccontr)
        assume "\<not> length p < max_io_len"
        then have "\<not> length (p_io p) < max_io_len" by auto
        moreover have "p_io p \<in> L M"
          unfolding LS.simps using \<open>path M (initial M) p\<close> by blast
        ultimately show "False"
          using \<open>\<forall>io \<in> L M . length io < max_io_len\<close> by blast
      qed
    qed

    obtain p where "path M (initial M) p" and "\<not> distinct (visited_states (initial M) p)"
      using \<open>\<not> acyclic M\<close> unfolding acyclic.simps by blast
    then obtain pL where "path M (initial M) pL" and "max_io_len \<le> length pL"
      using nondistinct_path_pumping[of M p max_io_len] by blast
    then show "False"
      using \<open>\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len\<close>
      using not_le by blast 
  qed
qed

    
   
fun deadlock_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where 
  "deadlock_state M q = (q \<in> nodes M \<and> (\<not>(\<exists> t \<in> h M . t_source t = q)))"

lemma deadlock_state_alt_def : "deadlock_state M q = (LS M q = {[]})" 
proof 
  show "deadlock_state M q \<Longrightarrow> LS M q = {[]}" 
  proof (rule ccontr)
    assume "deadlock_state M q" and "LS M q \<noteq> {[]}"
    moreover have "[] \<in> LS M q" 
      using \<open>deadlock_state M q\<close> by auto
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
    then have "q \<in> nodes M" unfolding LS.simps by auto
    then obtain t where "t \<in> h M \<and> t_source t = q" using \<open>\<not> deadlock_state M q\<close> by auto
    then have "p_io [t] \<in> LS M q"
    proof -
      have "path M q [t]"
        using \<open>t \<in> set (wf_transitions M) \<and> t_source t = q\<close> by blast
      then have "path M q [t]"
        by meson
      then have "\<exists>ps. p_io [t] = p_io ps \<and> path M q ps"
        by blast
      then show ?thesis
        by simp
    qed
    then show "False" using \<open>LS M q = {[]}\<close>
      by blast
  qed
qed

fun completed_path :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "completed_path M q p = deadlock_state M (target p q)"

fun minimal :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> nodes M . \<forall> q' \<in> nodes M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"



subsection \<open>IO Targets and Observability\<close>

fun fst_io_target' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "fst_io_target' M [] q = Some q" |
  "fst_io_target' M (xy#io) q = (case (find (\<lambda> t' . t_source t' = q \<and> t_input t' = fst xy \<and> t_output t' = snd xy) (wf_transitions M)) of
    None \<Rightarrow> None |
    Some t' \<Rightarrow> fst_io_target' M io (t_target t'))"

fun fst_io_target :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "fst_io_target M io q = (case (fst_io_target' M io q) of 
    None \<Rightarrow> {} |
    Some t \<Rightarrow> {t})"

lemma fst_io_target'_path :
  assumes "fst_io_target' M io q = Some q'"
      and "q \<in> nodes M"
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
      using "**" Cons.IH \<open>t \<in> set (wf_transitions M)\<close> by blast
  
  
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
  "(q \<in> nodes M \<and> is_io_target M io q q') \<longleftrightarrow> (\<exists> p . path M q p \<and> target p q = q' \<and> p_io p = io)"
proof (induction io arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons xy io)
  have "q \<in> nodes M \<and> is_io_target M (xy # io) q q' \<Longrightarrow> (\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io)"
  proof -
    assume "q \<in> nodes M \<and> is_io_target M (xy # io) q q'"
    then obtain t where "t \<in> h M" 
                    and "t_source t = q" 
                    and "t_input t = fst xy" 
                    and "t_output t = snd xy" 
                    and "is_io_target M io (t_target t) q'"
      by auto
    then obtain p where "path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io"
      using Cons.IH by fastforce

    have "path M q (t#p)"
      using \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> \<open>t \<in> h M\<close> \<open>t_source t = q\<close> by blast
    moreover have "target (t#p) q = q'"
      using \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> by auto
    moreover have "p_io (t#p) = xy # io"
      by (simp add: \<open>path M (t_target t) p \<and> target p (t_target t) = q' \<and> p_io p = io\<close> \<open>t_input t = fst xy\<close> \<open>t_output t = snd xy\<close>)
    ultimately have "path M q (t#p) \<and> target (t#p) q = q' \<and> p_io (t#p) = xy # io" 
      by auto
    then show "q \<in> nodes M \<and> is_io_target M (xy # io) q q' \<Longrightarrow> (\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io)"
      by (metis (no_types, lifting)) 
  qed

  moreover have "(\<exists>p. path M q p \<and> target p q = q' \<and> p_io p = xy # io) \<Longrightarrow> q \<in> nodes M \<and> is_io_target M (xy # io) q q'"
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

    then show "q \<in> nodes M \<and> is_io_target M (xy#io) q q'"
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

lemma io_targets_from_list[code] :
  "io_targets M io q = (if q \<in> nodes M then set (io_targets_list M io q) else {})"
proof (cases "q \<in> nodes M")
  case True

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
      by (metis (mono_tags, lifting) io_targets.simps mem_Collect_eq)
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

  moreover have "\<And>x. x \<in> set (io_targets_list M io q) \<Longrightarrow> q \<in> nodes M \<Longrightarrow> x \<in> io_targets M io q"
   proof (induction io arbitrary: q)
    case Nil
    then have "x = q" unfolding io_targets_list.simps by auto  
    then show ?case using Nil.prems(2) by auto
  next
    case (Cons xy io) 
    then obtain t where "x \<in> set (io_targets_list M io (t_target t))"
                    and *: "t \<in> set (filter (\<lambda> t . t_source t = q \<and> t_input t = fst xy \<and> t_output t = snd xy) (wf_transitions M))"
      by auto
    then have "x \<in> io_targets M io (t_target t)"
      by (meson Cons.IH filter_is_subset nodes.step subset_code(1) wf_transition_simp)
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

  ultimately show ?thesis using True
    by (meson equalityI subsetI)
next
  case False
  then have "io_targets M io q = {}" unfolding io_targets.simps
    using path_begin_node by fastforce 
  then show ?thesis 
    using False by auto
qed


value "io_targets M_ex [] (initial M_ex)"

lemma io_targets_nodes :
  assumes "q \<in> nodes M"
  shows "io_targets M io q \<subseteq> nodes M"
  using assms nodes_path by fastforce


lemma io_targets_is_io_target :
  "io_targets M io q = {q' . q \<in> nodes M \<and> is_io_target M io q q'}"
  using is_io_target_path[of q M io] by fastforce 


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
    proof -
      have "\<not> io_targets M io q \<subseteq> {target p q}"
        using \<open>\<nexists>q'. io_targets M io q = {q'}\<close> \<open>target p q \<in> io_targets M io q\<close> by blast
      then show ?thesis
        by blast
    qed       
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


abbreviation(input) "io_target M io q \<equiv> hd (io_targets_list M io q)"

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





subsection \<open>Conformity Relations\<close>

fun is_io_reduction_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state A a B b = (LS A a \<subseteq> LS B b)"

abbreviation(input) "is_io_reduction A B \<equiv> is_io_reduction_state A (initial A) B (initial B)" 
notation 
  is_io_reduction ("_ \<preceq> _")


fun is_io_reduction_state_on_inputs :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> Input list set \<Rightarrow> 'b FSM \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_io_reduction_state_on_inputs A a U B b = (LS\<^sub>i\<^sub>n A a U \<subseteq> LS\<^sub>i\<^sub>n B b U)"

abbreviation(input) "is_io_reduction_on_inputs A U B \<equiv> is_io_reduction_state_on_inputs A (initial A) U B (initial B)" 
notation 
  is_io_reduction_on_inputs ("_ \<preceq>\<lbrakk>_\<rbrakk> _")



subsection \<open>Submachines\<close>

(* extends Petrenko's definition to explicitly require same inputs and outputs *)
fun is_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> set (transitions A) \<subseteq> set (transitions B) \<and> inputs A = inputs B \<and> outputs A = outputs B)"
  

lemma submachine_path_initial :
  assumes "is_submachine A B"
  and     "path A (initial A) p"
shows "path B (initial B) p"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a p)
  then show ?case
  proof -
    have f1: "initial A = initial B \<and> set (transitions A) \<subseteq> set (transitions B) \<and> inputs A = inputs B \<and> outputs A = outputs B"
      using assms(1) is_submachine.simps by blast
    then have f2: "t_source a = target p (initial B) \<and> a \<in> set (transitions A) \<and> t_source a \<in> nodes A \<and> t_input a \<in> set (inputs A) \<and> t_output a \<in> set (outputs A) \<and> path A (t_target a) []"
      using snoc.prems(2) by force
    then have f3: "a \<in> set (transitions B)"
      using f1 by blast
    have f4: "t_input a \<in> set (inputs B)"
      using f2 f1 by metis
    have f5: "t_output a \<in> set (outputs B)"
      using f2 f1 by auto
    have "t_target a \<in> nodes B"
      using f3 f2 f1 by (metis (no_types) assms(1) nodes.step path_prefix path_target_is_node snoc.IH snoc.prems(2))
    then show ?thesis
      using f5 f4 f3 f2 by (metis (no_types) assms(1) is_path.simps(2) path.nil path_append path_code path_prefix path_target_is_node snoc.IH snoc.prems(2))
  qed 
qed

lemma submachine_nodes :
  assumes "is_submachine A B"
  shows "nodes A \<subseteq> nodes B"
  by (metis (no_types, lifting) assms is_submachine.elims(2) nodes_path path_to_node submachine_path_initial subsetI) 

lemma submachine_path :
  assumes "is_submachine A B"
  and     "path A q p"
shows "path B q p"
  by (metis (no_types, lifting) assms(1) assms(2) distinct_path_to_node is_submachine.elims(2) path_append path_begin_node path_suffix submachine_path_initial)

lemma submachine_h :
  assumes "is_submachine A B"
  shows "h A \<subseteq> h B" 
  using assms submachine_nodes by auto

lemma submachine_reduction : 
  assumes "is_submachine A B"
  shows "is_io_reduction A B"
  using submachine_path[OF assms] assms by auto 



subsection \<open>Changing Initial States\<close>

fun from_FSM :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme" where
  "from_FSM M q = \<lparr> initial = q, inputs = inputs M, outputs = outputs M, transitions = transitions M, \<dots> = FSM.more M \<rparr>"



end