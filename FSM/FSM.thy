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


subsection \<open>Transition Filtering\<close>

fun is_io_valid_transition :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition \<Rightarrow> bool" where
  "is_io_valid_transition M t = ((t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun io_valid_transitions :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition list" where
  "io_valid_transitions M = filter (is_io_valid_transition M) (transitions M)"

abbreviation(input) "hIO M \<equiv> set (io_valid_transitions M)"



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

fun is_wf_transition :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition \<Rightarrow> bool" where
  "is_wf_transition M t = ((t_source t \<in> nodes M) \<and> (t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun wf_transitions :: "('state, 'b) FSM_scheme \<Rightarrow> 'state Transition list" where
  "wf_transitions M = filter (is_wf_transition M) (transitions M)"

lemma wf_transitions_alt_def : "wf_transitions M = filter (\<lambda>t . t_source t \<in> nodes M) (io_valid_transitions M)"
  using filter_filter[of "(\<lambda>t. t_source t \<in> nodes M)" "(\<lambda>t. t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))" "transitions M"]
  unfolding wf_transitions.simps io_valid_transitions.simps is_wf_transition.simps is_io_valid_transition.simps
  by (metis (no_types, lifting) filter_cong) 
(*
lemma wf_transition_iff[iff] : "t \<in> set (wf_transitions M) \<longleftrightarrow> (t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  
*)

lemma io_valid_transition_simp : "t \<in> set (io_valid_transitions M) = (t \<in> set (transitions M) \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  
lemma wf_transition_simp : "t \<in> set (wf_transitions M) = (t \<in> set (transitions M) \<and> t_source t \<in> nodes M \<and> t_input t \<in> set (inputs M) \<and> t_output t \<in> set (outputs M))"
  by auto  

abbreviation(input) "h M \<equiv> set (wf_transitions M)"





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
  by (metis (no_types, lifting) assms dual_order.trans filter_is_subset filter_set lists_of_length_containment member_filter path_h paths_of_length.simps wf_transitions_alt_def)


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
  ultimately have "\<not>distinct (visited_states q p)"
    using nodes_finite unfolding size_def
    by (metis "*" Suc_le_lessD \<open>length (visited_states q p) = Suc (length p)\<close> card_mono distinct_card size_def)
  then show "False" using assms(3) by auto
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

















subsection \<open>Product Machine\<close>

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


value "product M_ex M_ex'"

abbreviation(input) "left_path p \<equiv> map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p"
abbreviation(input) "right_path p \<equiv> map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p"
abbreviation(input) "zip_path p1 p2 \<equiv> (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))"


lemma product_simps[simp]:
  "initial (product A B) = (initial A, initial B)"  
  "inputs (product A B) = inputs A @ inputs B"
  "outputs (product A B) = outputs A @ outputs B"
  "transitions (product A B) = product_transitions A B"
unfolding product_def by simp+




lemma product_transitions_io_valid :
  "set (product_transitions A B) = hIO (product A B)"
proof -
  have "\<And> t . t \<in> set (product_transitions A B) \<Longrightarrow> t \<in> hIO (product A B)"
  proof -
    fix t assume *: "t \<in> set (product_transitions A B)"
    then obtain t1 t2 where "t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)"
                        and "t1 \<in> h A \<and> t2 \<in> h B \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
      using product_transitions_alt2[of A B] by blast
    then have "is_io_valid_transition (product A B) t"
      unfolding is_io_valid_transition.simps by auto
    then show "t \<in> hIO (product A B)" using *
      by (metis filter_set member_filter product_simps(4) io_valid_transitions.simps) 
  qed
  moreover have "\<And> t . t \<in> hIO (product A B) \<Longrightarrow>  t \<in> set (product_transitions A B)"
    by (metis filter_set member_filter product_simps(4) io_valid_transitions.simps) 
  ultimately show ?thesis by blast
qed
  

lemma product_transition :
  "((q1,q2),x,y,(q1',q2')) \<in> hIO (product A B) \<longleftrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B"
  using product_transitions_io_valid[of A B] product_transitions_alt3[of A B] by blast


lemma rev_induct2[consumes 1, case_names Nil snoc]: 
  assumes "length xs = length ys" 
      and "P [] []"
      and "(\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))"
    shows "P xs ys"
using assms proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case proof (cases ys)
    case Nil
    then show ?thesis
      using snoc.prems(1) by auto 
  next
    case (Cons a list)
    then show ?thesis
      by (metis append_butlast_last_id diff_Suc_1 length_append_singleton list.distinct(1) snoc.hyps snoc.prems) 
  qed
qed


lemma zip_path_last : "length xs = length ys \<Longrightarrow> (zip_path (xs @ [x]) (ys @ [y])) = (zip_path xs ys)@(zip_path [x] [y])"
  by (induction xs ys rule: list_induct2; simp)

lemma product_path_from_paths :
  assumes "path A (initial A) p1"
      and "path B (initial B) p2"
      and "p_io p1 = p_io p2"
    shows "path (product A B) (initial (product A B)) (zip_path p1 p2)"
      and "target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))"
proof -
  have "initial (product A B) = (initial A, initial B)" by auto
  then have "(initial A, initial B) \<in> nodes (product A B)"
    by (metis nodes.initial) 

  have "length p1 = length p2" using assms(3)
    using map_eq_imp_length_eq by blast 
  then have c: "path (product A B) (initial (product A B)) (zip_path p1 p2) \<and> target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))"
    using assms proof (induction p1 p2 rule: rev_induct2)
    case Nil
    
    then have "path (product A B) (initial (product A B)) (zip_path [] [])" 
      using \<open>initial (product A B) = (initial A, initial B)\<close> \<open>(initial A, initial B) \<in> nodes (product A B)\<close>
      by (metis Nil_is_map_conv path.nil zip_Nil)
    moreover have "target (zip_path [] []) (initial (product A B)) = (target [] (initial A), target [] (initial B))"
      using \<open>initial (product A B) = (initial A, initial B)\<close> by auto
    ultimately show ?case by fast
  next
    case (snoc x xs y ys)
    
    have "path A (initial A) xs" using snoc.prems(1) by auto
    moreover have "path B (initial B) ys" using snoc.prems(2) by auto
    moreover have "p_io xs = p_io ys" using snoc.prems(3) by auto
    ultimately have *:"path (product A B) (initial (product A B)) (zip_path xs ys)" 
                and **:"target (zip_path xs ys) (initial (product A B)) = (target xs (initial A), target ys (initial B))" 
      using snoc.IH by blast+
    then have "(target xs (initial A), target ys (initial B)) \<in> nodes (product A B)"
      by (metis (no_types, lifting) path_target_is_node)
    then have "(t_source x, t_source y) \<in> nodes (product A B)"
      using snoc.prems(1-2)  by (metis path_consIO_elim path_suffix) 

    have "x \<in> h A" using snoc.prems(1) by auto
    moreover have "y \<in> h B" using snoc.prems(2) by auto
    moreover have "t_input x = t_input y" using snoc.prems(3) by auto
    moreover have "t_output x = t_output y" using snoc.prems(3) by auto
    ultimately have "((t_source x, t_source y), t_input x, t_output x, (t_target x, t_target y)) \<in> hIO (product A B)"
    proof -
      have f1: "{((t_source p, t_source pa), t_input p, t_output p, t_target p, t_target pa) | p pa. p \<in> set (wf_transitions A) \<and> pa \<in> set (wf_transitions B) \<and> t_input p = t_input pa \<and> t_output p = t_output pa} = set (io_valid_transitions (product A B))"
        using product_transitions_alt2[of A B] product_transitions_io_valid by blast
      have "\<exists>p pa. ((t_source x, t_source y), t_input x, t_output x, t_target x, t_target y) = ((t_source p, t_source pa), t_input p, t_output p, t_target p, t_target pa) \<and> p \<in> set (wf_transitions A) \<and> pa \<in> set (wf_transitions B) \<and> t_input p = t_input pa \<and> t_output p = t_output pa"
        using \<open>t_input x = t_input y\<close> \<open>t_output x = t_output y\<close> \<open>x \<in> set (wf_transitions A)\<close> \<open>y \<in> set (wf_transitions B)\<close> by blast
      then show ?thesis
        using f1 by blast
    qed 
    
    moreover have "t_source x = target xs (initial A)" using snoc.prems(1) by auto
    moreover have "t_source y = target ys (initial B)" using snoc.prems(2) by auto
    ultimately have "((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y)) \<in> h (product A B)"
      using \<open>(t_source x, t_source y) \<in> nodes (product A B)\<close>
      by (metis fst_conv io_valid_transition_simp wf_transition_simp)
    then have ***: "path (product A B) (initial (product A B)) ((zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))])"
      using * **
    proof -
      have "\<forall>p f. p \<notin> nodes (f::('a \<times> 'c, 'b) FSM_scheme) \<or> path f p []"
        by blast
      then have "path (product A B) (t_source ((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)) [((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)]"
        by (meson \<open>((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y) \<in> set (wf_transitions (product A B))\<close> consIO nodes.step wf_transition_simp)
      then have "path (product A B) (target (map (\<lambda>p. ((t_source (fst p), t_source (snd p)), t_input (fst p), t_output (fst p), t_target (fst p), t_target (snd p))) (zip xs ys)) (initial (product A B))) [((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)]"
        by (metis (no_types) "**" fst_conv)
      then show ?thesis
        using "*" by blast
    qed     

    have "t_target x = target (xs@[x]) (initial A)" by auto
    moreover have "t_target y = target (ys@[y]) (initial B)" by auto
    ultimately have ****: "target ((zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]) (initial (product A B)) = (target (xs@[x]) (initial A), target (ys@[y]) (initial B))"
      by fastforce


    have "(zip_path [x] [y]) = [((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]"
      using \<open>t_source x = target xs (initial A)\<close> \<open>t_source y = target ys (initial B)\<close> by auto
    moreover have "(zip_path (xs @ [x]) (ys @ [y])) = (zip_path xs ys)@(zip_path [x] [y])"
      using zip_path_last[of xs ys x y, OF snoc.hyps]  by assumption
    ultimately have *****:"(zip_path (xs@[x]) (ys@[y])) = (zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]"
      by auto
    then have "path (product A B) (initial (product A B)) (zip_path (xs@[x]) (ys@[y]))"
      using *** by presburger 
    moreover have "target (zip_path (xs@[x]) (ys@[y])) (initial (product A B)) = (target (xs@[x]) (initial A), target (ys@[y]) (initial B))"
      using **** ***** by auto
    ultimately show ?case by linarith
  qed

  from c show "path (product A B) (initial (product A B)) (zip_path p1 p2)" by auto
  from c show "target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))" by auto
qed


lemma product_transitions_elem :
  assumes "t \<in> set (product_transitions A B)"
  shows "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
    and "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
proof -
  obtain t1 t2 where *:   "t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)" 
                 and **:  "t1 \<in> h A"
                 and ***: "t2 \<in> h B"
                 and ****: "t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
    using assms product_transitions_alt2[of A B] by blast
 
  from * ** show "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A" by auto
  from * *** **** show "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B" by auto
qed


lemma paths_from_product_path :
  assumes "path (product A B) (initial (product A B)) p"
  shows   "path A (initial A) (left_path p)"
      and "path B (initial B) (right_path p)"
      and "target (left_path p) (initial A) = fst (target p (initial (product A B)))"
      and "target (right_path p) (initial B) = snd (target p (initial (product A B)))"
proof -
  have c: "path A (initial A) (left_path p)
            \<and> path B (initial B) (right_path p)
            \<and> target (left_path p) (initial A) = fst (target p (initial (product A B)))
            \<and> target (right_path p) (initial B) = snd (target p (initial (product A B)))"
  using assms proof (induction p rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc t p)
    then have "path (product A B) (initial (product A B)) p" by fast
    then have "path A (initial A) (left_path p)"
      and "path B (initial B) (right_path p)"
      and "target (left_path p) (initial A) = fst (target p (initial (product A B)))"
      and "target (right_path p) (initial B) = snd (target p (initial (product A B)))" 
      using snoc.IH  by fastforce+

    then have "t_source t = (target (left_path p) (initial A), target (right_path p) (initial B))"
      using snoc.prems by (metis (no_types, lifting) path_consIO_elim path_suffix prod.collapse) 

    have "t \<in> h (product A B)" using snoc.prems
      by (meson path_consIO_elim path_suffix wf_transition_simp) 
    then have "t \<in> set (product_transitions A B)" 
      using product_transitions_io_valid[of A B]
      by (metis io_valid_transition_simp wf_transition_simp) 
    have "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A" 
      using product_transitions_elem[OF \<open>t \<in> set (product_transitions A B)\<close>] by simp
    have "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
      using product_transitions_elem[OF \<open>t \<in> set (product_transitions A B)\<close>] by simp

  (* TODO*)

    then show ?case 
  qed
  



lemma product_transition' :
  "((q1,q2),x,y,(q1',q2')) \<in> h (product A B) \<longleftrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B \<and> (\<exists> p1 p2 . path A q1 p1 \<and> path B q2 p2 \<and> p_io p1 = p_io p2)"




lemma product_path:
  "path (product A B) (q1,q2) p \<longleftrightarrow> (path A q1 (left_path p) \<and> path B q2 (right_path p))"
proof (induction p arbitrary: q1 q2)
  case Nil
  then show ?case by aut
next
  case (Cons t p)
  then show ?case 
  proof (cases "path (product A B) (q1, q2) [t]")
    case True
    then have "t \<in> h (product A B)"
      by (meson path_consIO_elim wf_transition_simp)
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
      have "fst (t_source t) = q1"
        by (metis True path_consIO_elim prod.sel(1))
      then show ?thesis
        by (metis (no_types) \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> set (wf_transitions A)\<close> consIO nodes.step path.nil prod.sel(1) wf_transition_simp)
    qed

    then have *: "path A q1 (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) (t # p)) = path A (fst (t_target t)) (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p)"
      by auto

    have "t2 = (snd (t_source t), t_input t, t_output t, snd (t_target t))" 
      using \<open>t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2))\<close> \<open>t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close> by auto
    then have "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
      using \<open>t2 \<in> set (wf_transitions B)\<close> by auto
    have "path B q2 [(snd (t_source t), t_input t, t_output t, snd (t_target t))]"
    proof -
      have "t_source t2 = q2"
        by (metis (no_types) True \<open>t2 = (snd (t_source t), t_input t, t_output t, snd (t_target t))\<close> fst_conv path_consIO_elim snd_conv)
      then show ?thesis
        by (metis \<open>t2 = (snd (t_source t), t_input t, t_output t, snd (t_target t))\<close> \<open>t2 \<in> set (wf_transitions B)\<close> consIO nodes.step path.nil wf_transition_simp)
    qed

    then have **: "path B q2 (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) (t # p)) = path B (snd (t_target t)) (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p)"
      by auto

    have ***: "path (product A B) (q1, q2) (t # p) = path (product A B) (t_target t) p"
      by (metis True consIO path_consIO_elim)
      
      

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
        by (metis \<open>q1 = fst (t_source t)\<close> \<open>q2 = snd (t_source t)\<close> \<open>t \<in> h (product A B)\<close> path.simps prod.collapse
        
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
      using product_path[of A B q1 q2 p] by auto
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








end