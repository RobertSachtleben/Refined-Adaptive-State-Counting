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

lemma wf_transition_target : "t \<in> h M \<Longrightarrow> t_target t \<in> nodes M" by auto




subsection \<open>Paths\<close>

inductive path :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "q \<in> nodes M \<Longrightarrow> path M q []" |
  cons[intro!] : "t \<in> h M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_nil_elim[elim!]: "path M q []"
inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"


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


lemma path_prepend_t : "path M q' p \<Longrightarrow> (q,x,y,q') \<in> h M \<Longrightarrow> path M q ((q,x,y,q')#p)" 
  by (metis (mono_tags, lifting) fst_conv path.intros(2) prod.sel(2)) 
lemma path_append_last : "path M q p \<Longrightarrow> t \<in> h M \<Longrightarrow> t_source t = target p q \<Longrightarrow> path M q (p@[t])"
  by (metis cons path.nil path_append wf_transition_target) 



lemma path_target_append : "target p1 q1 = q2 \<Longrightarrow> target p2 q2 = q3 \<Longrightarrow> target (p1@p2) q1 = q3" by auto

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
    by (simp add: path_append_last) 
  moreover have "t_target t = target (p@[t]) (initial M)" by auto
  ultimately show "\<exists>p. path M (initial M) p \<and> t_target t = target p (initial M)"
    by meson 
qed



lemma h_nodes :
  "nodes M = insert (initial M) {t_target t | t . t \<in> h M}"
proof -
  have "\<And> q . q \<in> nodes M \<Longrightarrow> q \<in> insert (initial M) {t_target t | t . t \<in> h M}"
  proof -
    fix q assume "q \<in> nodes M"
    then show "q \<in> insert (initial M) {t_target t | t . t \<in> h M}"
    proof (cases "q = initial M")
      case True
      then show ?thesis by blast
    next
      case False
      
      then obtain t where "t \<in> set (transitions M)" 
                      and "t_source t \<in> nodes M" 
                      and "t_input t \<in> set (inputs M)"
                      and "t_output t \<in> set (outputs M)" 
                      and "t_target t = q"
        by (metis \<open>q \<in> nodes M\<close> nodes.cases)

      then have "t \<in> h M" by auto
      then show ?thesis using \<open>t_target t = q\<close> by blast
    qed
  qed
  then show ?thesis by blast
qed
    

lemma h_subset_path : 
  assumes "h A \<subseteq> h B"
  and "path A q p"
  and "q \<in> nodes B"
shows "path B q p"
using assms(2) proof (induction p rule: rev_induct)
  case Nil
  show ?case using assms(3) by auto
next
  case (snoc t p)
  then show ?case using assms(1) path_suffix by auto  
qed

lemma h_subset_path_non_initial :
  assumes "h A \<subseteq> h B"
  and "path A q p"
  and "q \<noteq> initial A"
shows "path B q p"
proof -
  have "q \<in> nodes A" using assms(2)
    by (meson path_begin_node) 
  then have "q \<in> {t_target t | t . t \<in> h A}"
    using assms(3) h_nodes[of A] by blast
  then have "q \<in> {t_target t | t . t \<in> h B}"
    using assms(1) by blast
  then have "q \<in> nodes B" by blast
  then show ?thesis using h_subset_path[OF assms(1,2)] by auto
qed

lemma nodes_initial_or_target :
  assumes "q \<in> nodes M"
  shows "q = initial M \<or> (\<exists> t \<in> h M . t_target t = q)"
proof (cases "q = initial M")
  case True
  then show ?thesis by auto
next
  case False
  obtain p where "path M (initial M) p" and "target p (initial M) = q"
    by (metis path_to_node assms)
  have "p \<noteq> []"
    using \<open>target p (initial M) = q\<close> False by auto
  have "(last p) \<in> h M"
    using \<open>path M (initial M) p\<close> \<open>p \<noteq> []\<close> by (meson contra_subsetD last_in_set path_h) 
  moreover have "t_target (last p) = q"
    using \<open>target p (initial M) = q\<close> \<open>p \<noteq> []\<close> unfolding target.simps visited_states.simps
    by (simp add: last_map) 
  ultimately have "\<exists> t \<in> h M . t_target t = q"
    by blast
  then show ?thesis by linarith
qed




lemma h_equivalence_path :
  assumes "h A = h B"
  and "q \<in> nodes A" and "q \<in> nodes B"
shows "path A q p \<longleftrightarrow> path B q p"
  using h_subset_path[OF _ _ assms(2), of B p]
  using h_subset_path[OF _ _ assms(3), of A p]
  by (metis assms(1) subset_code(1))

lemma path_equivalence_by_h :
  assumes "path A q (p@[t])" and "path B q p" 
  shows "((path B q (p@[t])) = (t \<in> h B))"
using assms by (induction p arbitrary: q; fastforce)

lemma single_transition_path : "t \<in> h M \<Longrightarrow> path M (t_source t) [t]" by auto

lemma nodes_set_alt_def : "nodes M = { target p (initial M) | p . path M (initial M) p }" 
  using path_to_node[of _ M]  path_target_is_node[of M "initial M"] by blast

lemma nodes_paths_by_same_h_initial :
  assumes "initial A = initial B"
      and "h A = h B"
    shows "nodes A = nodes B"
      and "path A q p = path B q p"
proof -
  show "nodes A = nodes B"
  proof -
    have "insert (initial A) {t_target p |p. p \<in> set (wf_transitions B)} = nodes B"
      using assms(1) h_nodes by force
    then show ?thesis
      by (metis (no_types) assms(2) h_nodes)
  qed 

  then show "path A q p = path B q p" using assms by (induction p arbitrary: q; fast)
qed


lemma path_source_target_index :
  assumes "Suc i < length p"
  and     "path M q p"
shows "t_target (p ! i) = t_source (p ! (Suc i))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t ps)
  then have "path M q ps" and "t_source t = target ps q" and "t \<in> h M" by auto
  
  show ?case proof (cases "Suc i < length ps")
    case True
    then have "t_target (ps ! i) = t_source (ps ! Suc i)" 
      using snoc.IH \<open>path M q ps\<close> by auto
    then show ?thesis
      by (simp add: Suc_lessD True nth_append) 
  next
    case False
    then have "Suc i = length ps"
      using snoc.prems(1) by auto
    then have "(ps @ [t]) ! Suc i = t"
      by auto

    show ?thesis proof (cases "ps = []")
      case True
      then show ?thesis using \<open>Suc i = length ps\<close> by auto
    next
      case False
      then have "target ps q = t_target (last ps)"
        unfolding target.simps visited_states.simps
        by (simp add: last_map) 
      then have "target ps q = t_target (ps ! i)"
        using \<open>Suc i = length ps\<close>
        by (metis False diff_Suc_1 last_conv_nth) 
      then show ?thesis 
        using \<open>t_source t = target ps q\<close>
        by (metis \<open>(ps @ [t]) ! Suc i = t\<close> \<open>Suc i = length ps\<close> lessI nth_append) 
    qed
  qed   
qed


subsection \<open>Properties of Paths Visiting Distinct Nodes Only\<close>

lemma visited_states_prefix :
  assumes "q' \<in> set (visited_states q p)"
  shows   "\<exists> p1 p2 . p = p1@p2 \<and> target p1 q = q'"
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

lemma distinct_path_length :
  assumes "path M q p"
obtains p' where "path M q p'"
             and "target p' q = target p q"
             and "length p' < size M"
  using distinct_path_length_limit_nodes
        distinct_path_from_nondistinct_path[OF assms]
  by (metis assms)
  



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
      by (metis path_append path_append_elim path_cons_elim path_equivalence_by_h single_transition_path) 

    

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

lemma language_contains_empty_sequence : "[] \<in> L M" by auto
  
(* TODO: rename *)
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
    using paths_up_to_length_path_set[OF nodes.initial[of M], of "length io"] by simp 
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
    using paths_up_to_length_path_set[OF nodes.initial[of M], of "list_max (map length P)"] by simp 
qed




fun language_up_to_length :: "('a, 'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (Input \<times> Output) list list" where
  "language_up_to_length M k = map p_io (paths_up_to_length M (initial M) k)"

lemma language_up_to_length_set : "set (language_up_to_length M k) = { io \<in> L M . length io \<le> k }"
  using paths_up_to_length_path_set[OF nodes.initial[of M], of k] unfolding LS.simps language_up_to_length.simps by auto

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



lemma LS\<^sub>i\<^sub>n_alt_def : "LS\<^sub>i\<^sub>n M q U = {io \<in> LS M q . (map fst io) \<in> U}"
proof -
  have p_io_io : "\<And>p . map t_input p = map fst (map (\<lambda>t . (t_input t, t_output t)) p)" by auto

  have "\<And> io . io \<in> LS\<^sub>i\<^sub>n M q U \<Longrightarrow> io \<in> {io \<in> LS M q. map fst io \<in> U}"
    unfolding LS\<^sub>i\<^sub>n.simps LS.simps 
  proof -
    fix io :: "(integer \<times> integer) list"
    assume "io \<in> {p_io p |p. path M q p \<and> map t_input p \<in> U}"
    then obtain pps :: "(integer \<times> integer) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
      f1: "io = p_io (pps io) \<and> path M q (pps io) \<and> map t_input (pps io) \<in> U"
      by moura
    then have "map fst io = map t_input (pps io)"
      by (simp add: p_io_io)
    then have "map fst io \<in> U"
      using f1 by simp
    then show "io \<in> {ps \<in> {p_io ps |ps. path M q ps}. map fst ps \<in> U}"
      using f1 by blast
  qed 
  moreover have "\<And> io . io \<in> {io \<in> LS M q. map fst io \<in> U} \<Longrightarrow> io \<in> LS\<^sub>i\<^sub>n M q U"
    unfolding LS\<^sub>i\<^sub>n.simps LS.simps
  proof -
    fix io :: "(integer \<times> integer) list"
    assume a1: "io \<in> {io \<in> {p_io p |p. path M q p}. map fst io \<in> U}"
    then have "\<exists>ps. io = p_io ps \<and> path M q ps"
      by blast
    then obtain pps :: "(integer \<times> integer) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
      f2: "io = p_io (pps io) \<and> path M q (pps io)"
      by moura
    then have "map t_input (pps io) \<in> U"
      using a1 by (simp add: p_io_io)
    then show "io \<in> {p_io ps |ps. path M q ps \<and> map t_input ps \<in> U}"
      using f2 by blast
  qed
  ultimately show ?thesis by blast
qed

lemma language_by_same_h_initial :
  assumes "initial A = initial B"
      and "h A = h B"
    shows "L A = L B"
  unfolding LS.simps using nodes_paths_by_same_h_initial(2)[OF assms]
  using assms(1) by auto 



subsection \<open> Basic FSM properties \<close>

fun completely_specified :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_alt_def : "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> set (inputs M) . \<exists> q' y . (q,x,y,q') \<in> h M)"
  by force

value "completely_specified M_ex"
value "completely_specified M_ex_9"

fun completely_specified_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "completely_specified_state M q = (\<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_states :
  "completely_specified M = (\<forall> q \<in> nodes M . completely_specified_state M q)"
  unfolding completely_specified.simps completely_specified_state.simps by force


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
  "single_input M = (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . t_source t1 = t_source t2 \<longrightarrow> t_input t1 = t_input t2)" 


lemma single_input_alt_def : "single_input M = (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> h M \<and> (q1,x',y',q1'') \<in> h M \<longrightarrow> x = x')"
  unfolding single_input.simps by fastforce 
  

(* slightly more efficient method of deciding the single input property,
   avoids checking the same pair of transitions twice *)
fun single_input_by_transition_list :: "('a, 'b) FSM_scheme \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "single_input_by_transition_list M [] = True" |
  "single_input_by_transition_list M (t1#ts) = (case find (\<lambda> t2 . t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2) ts of
    None \<Rightarrow> single_input_by_transition_list M ts | 
    Some _ \<Rightarrow> False)"


lemma single_input_by_transition_list_correctness :
  assumes "set xs \<subseteq> h M"
  shows "single_input_by_transition_list M xs = (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2))"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then have "a \<in> h M" by auto

  let ?P = "(\<forall> t1 \<in> set (a#xs) . \<not>(\<exists> t2 \<in> set (a#xs) .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2))"

  have "?P = (\<forall> t1 \<in> set (a#xs) . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2))"
    using set_subset_Cons by auto
  then have *: "?P = ((\<not>(\<exists> t2 \<in> set xs .a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_input a \<noteq> t_input t2)) \<and> (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2)))"
    by auto
  
  
  show ?case
  proof (cases "find (\<lambda> t2 . a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_input a \<noteq> t_input t2) xs")
    case None
    
    have "\<not>(\<exists> t2 \<in> set xs .a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_input a \<noteq> t_input t2)"
      using find_None_iff[of "(\<lambda> t2 . a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_input a \<noteq> t_input t2)" xs] None by blast
    then have "?P = (\<forall> t1 \<in> set xs . \<not>(\<exists> t2 \<in> set xs .t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2))"
      using * by blast
    moreover have "single_input_by_transition_list M (a#xs) = single_input_by_transition_list M xs"
      unfolding single_input_by_transition_list.simps None by auto
    ultimately show ?thesis using Cons by auto
  next
    case (Some a2)
    then have "a2 \<in> set xs" using find_result_props(1) by fast
    moreover have "a \<noteq> a2 \<and> t_source a = t_source a2 \<and> t_input a \<noteq> t_input a2"
      using find_result_props(2)[OF Some] by assumption
    ultimately have "\<not>?P"
      using \<open>(\<forall>t1\<in>set (a # xs). \<not> (\<exists>t2\<in>set (a # xs). t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2)) = (\<not> (\<exists>t2\<in>set xs. a \<noteq> t2 \<and> t_source a = t_source t2 \<and> t_input a \<noteq> t_input t2) \<and> (\<forall>t1\<in>set xs. \<not> (\<exists>t2\<in>set xs. t1 \<noteq> t2 \<and> t_source t1 = t_source t2 \<and> t_input t1 \<noteq> t_input t2)))\<close> \<open>a2 \<in> set xs\<close> by blast 
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

lemma acyclic_finite_paths :
  assumes "acyclic M"
    shows "finite {p . path M q p}"
proof -
  from assms have "{ p . path M (initial M) p} \<subseteq> set (paths_up_to_length M (initial M) (size M))"
    using distinct_path_length_limit_nodes[of M "initial M"] paths_up_to_length_path_set[OF nodes.initial[of M], of "size M"]
    by fastforce 
  moreover have "finite (set (paths_up_to_length M (initial M) (size M)))"
    by auto
  ultimately have "finite { p . path M (initial M) p}"
    using finite_subset by blast

  show "finite {p . path M q p}"
  proof (cases "q \<in> nodes M")
    case True
    then obtain p where "path M (initial M) p" and "target p (initial M) = q" 
      by (metis path_to_node)
    
    have "image (\<lambda>p' . p@p') {p' . path M q p'} \<subseteq> {p' . path M (initial M) p'}"
    proof 
      fix x assume "x \<in> image (\<lambda>p' . p@p') {p' . path M q p'}"
      then obtain p' where "x = p@p'" and "p' \<in> {p' . path M q p'}"
        by blast
      then have "path M q p'" by auto
      then have "path M (initial M) (p@p')"
        using path_append[OF \<open>path M (initial M) p\<close>] \<open>target p (initial M) = q\<close> by auto
      then show "x \<in> {p' . path M (initial M) p'}" using \<open>x = p@p'\<close> by blast
    qed
    
    then have "finite (image (\<lambda>p' . p@p') {p' . path M q p'})"
      using \<open>finite { p . path M (initial M) p}\<close> finite_subset by auto 
    show ?thesis using finite_imageD[OF \<open>finite (image (\<lambda>p' . p@p') {p' . path M q p'})\<close>]
      by (meson inj_onI same_append_eq) 
  next
    case False
    then show ?thesis
      by (meson not_finite_existsD path_begin_node) 
  qed
qed

lemma acyclic_paths_from_nodes :
  assumes "acyclic M" 
      and "path M q p"
    shows "distinct (visited_states q p)"
proof -
  have "q \<in> nodes M"
    using assms(2) path_begin_node by metis
  then obtain p' where "path M (initial M) p'" and "target p' (initial M) = q"
    using path_to_node by metis
  then have "path M (initial M) (p'@p)"
    using assms(2) path_append by metis
  then have "distinct (visited_states (initial M) (p'@p))"
    using assms(1) unfolding acyclic.simps by blast
  then have "distinct (initial M # (map t_target p') @ map t_target p)"
    by auto
  moreover have "initial M # (map t_target p') @ map t_target p = (butlast (initial M # map t_target p')) @ ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  ultimately have "distinct ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  then show ?thesis 
    using \<open>target p' (initial M) = q\<close> unfolding visited_states.simps target.simps by simp
qed




definition LS_acyclic :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set" where
  "LS_acyclic M q = set (map p_io (paths_up_to_length M q (card (h M))))"

lemma distinct_path_length_limit_card :
  assumes "path M q p"
  and     "distinct (visited_states q p)"
shows "length p \<le> card (h M)"
proof (rule ccontr)
  assume *: "\<not> length p \<le> card (h M)"

  have "set p \<subseteq> h M" 
    using assms(1) by (meson path_h) 
  
  have "\<not> distinct p"
    by (metis (no_types, lifting) "*" List.finite_set  \<open>set p \<subseteq> h M\<close> card_mono distinct_card)
  then have "\<not> distinct (map t_target p)"
    by (simp add: distinct_map)
  then have "\<not>distinct (visited_states q p)"
    unfolding visited_states.simps by auto
  then show "False" using assms(2) by auto
qed

lemma LS_acyclic_complete :
  assumes "acyclic M"
      and "q \<in> nodes M"
  shows "LS M q = LS_acyclic M q"
proof -
  have "LS_acyclic M q = {p_io p | p . path M q p \<and> length p \<le> (card (h M))}"
    using paths_up_to_length_path_set[OF assms(2)] unfolding LS_acyclic_def by force
  moreover have "LS M q = {p_io p | p . path M q p \<and> length p \<le> card (h M)}"
    unfolding LS.simps using acyclic_paths_from_nodes[OF assms(1), of q] distinct_path_length_limit_card[of M q] by blast
  ultimately show ?thesis by blast
qed


lemma acyclic_path_length :
  assumes "acyclic M" 
  and     "path M (initial M) p" 
  shows "length p < size M"
  using distinct_path_length_limit_nodes[OF assms(2) acyclic_paths_from_nodes[OF assms]] by assumption


lemma cyclic_cycle :
  assumes "\<not> acyclic M"
  shows "\<exists> q p . path M q p \<and> p \<noteq> [] \<and> target p q = q" 
proof -
  have "(\<exists> p \<in> set (distinct_paths_up_to_length_from_initial M (size M)) . \<exists> t \<in> h M . path M (initial M) (p@[t]) \<and> \<not>distinct (visited_states (initial M) (p@[t])))"
    using assms FSM.acyclic_code unfolding contains_cyclic_path.simps by metis
  then obtain p t where "path M (initial M) (p@[t])" and "\<not>distinct (visited_states (initial M) (p@[t]))"
    by meson

  show ?thesis
  proof (cases "initial M \<in> set (map t_target (p@[t]))")
    case True
    then obtain i where "last (take i (map t_target (p@[t]))) = initial M" and "i \<le> length (map t_target (p@[t]))" and "0 < i"
      using list_contains_last_take by metis

    let ?p = "take i (p@[t])"
    have "path M (initial M) (?p@(drop i (p@[t])))" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis append_take_drop_id)  
    then have "path M (initial M) ?p" by auto
    moreover have "?p \<noteq> []" using \<open>0 < i\<close> by auto
    moreover have "target ?p (initial M) = initial M"
      using \<open>last (take i (map t_target (p@[t]))) = initial M\<close> unfolding target.simps visited_states.simps
      by (metis (no_types, lifting) calculation(2) last_ConsR list.map_disc_iff take_map) 
    ultimately show ?thesis by blast
  next
    case False
    then have "\<not> distinct (map t_target (p@[t]))"
      using \<open>\<not>distinct (visited_states (initial M) (p@[t]))\<close> unfolding visited_states.simps by auto
    then obtain i j where "i < j" and "j < length (map t_target (p@[t]))" and "(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j"
      using non_distinct_repetition_indices by blast

    let ?pre_i = "take (Suc i) (p@[t])"
    let ?p = "take ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"
    let ?post_j = "drop ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"

    have "p@[t] = ?pre_i @ ?p @ ?post_j"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close>
      by (metis append_take_drop_id) 
    then have "path M (target ?pre_i (initial M)) ?p" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis path_prefix path_suffix) 

    have "?p \<noteq> []"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto

    have "i < length (map t_target (p@[t]))"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto
    have "(target ?pre_i (initial M)) = (map t_target (p@[t])) ! i"
      unfolding target.simps visited_states.simps  
      using take_last_index[OF \<open>i < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>i < length (map t_target (p @ [t]))\<close> last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    
    have "?pre_i@?p = take (Suc j) (p@[t])"
      by (metis (no_types) \<open>i < j\<close> add_Suc add_diff_cancel_left' less_SucI less_imp_Suc_add take_add)
    moreover have "(target (take (Suc j) (p@[t])) (initial M)) = (map t_target (p@[t])) ! j"
      unfolding target.simps visited_states.simps  
      using take_last_index[OF \<open>j < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>j < length (map t_target (p @ [t]))\<close> last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    ultimately have "(target (?pre_i@?p) (initial M)) = (map t_target (p@[t])) ! j"
      by auto
    then have "(target (?pre_i@?p) (initial M)) = (map t_target (p@[t])) ! i"
      using \<open>(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j\<close> by simp
    moreover have "(target (?pre_i@?p) (initial M)) = (target ?p (target ?pre_i (initial M)))"
      unfolding target.simps visited_states.simps last.simps by auto
    ultimately have "(target ?p (target ?pre_i (initial M))) = (map t_target (p@[t])) ! i"
      by auto
    then have "(target ?p (target ?pre_i (initial M))) = (target ?pre_i (initial M))"
      using \<open>(target ?pre_i (initial M)) = (map t_target (p@[t])) ! i\<close> by auto

    show ?thesis
      using \<open>path M (target ?pre_i (initial M)) ?p\<close> \<open>?p \<noteq> []\<close> \<open>(target ?p (target ?pre_i (initial M))) = (target ?pre_i (initial M))\<close>
      by blast
  qed
qed

lemma cyclic_cycle_rev :
  assumes "\<exists> q p . path M q p \<and> p \<noteq> [] \<and> target p q = q"
  shows "\<not> acyclic M"
  using assms unfolding acyclic.simps target.simps visited_states.simps
proof -
  assume "\<exists>q p. path M q p \<and> p \<noteq> [] \<and> last (q # map t_target p) = q"
  then obtain aa :: 'a and pps :: "('a \<times> integer \<times> integer \<times> 'a) list" where
    f1: "path M aa pps \<and> pps \<noteq> [] \<and> last (aa # map t_target pps) = aa"
    by blast
  then have "map t_target pps \<noteq> []"
    by blast
  then show "\<not> (\<forall>ps. path M (initial M) ps \<longrightarrow> distinct (initial M # map t_target ps))"
    using f1 by (metis (no_types) acyclic.elims(3) acyclic_paths_from_nodes distinct.simps(2) last.simps last_in_set visited_states.simps)
qed 

lemma acyclic_initial :
  assumes "acyclic M"
  shows "\<not> (\<exists> t \<in> h M . t_target t = initial M)" 
proof 
  assume "\<exists>t\<in>set (wf_transitions M). t_target t = initial M"
  then obtain t where "t \<in> h M" and "t_target t = initial M"
    by blast
  then have "t_source t \<in> nodes M" by auto
  then obtain p where "path M (initial M) p" and "target p (initial M) = t_source t" 
    using path_to_node by metis
  then have "path M (initial M) (p@[t])" 
    using \<open>t \<in> h M\<close> by auto
  moreover have "p@[t] \<noteq> []" by simp
  moreover have "target (p@[t]) (initial M) = initial M"
    using \<open>t_target t = initial M\<close> unfolding target.simps visited_states.simps by auto
  ultimately have "\<not> acyclic M"
    using cyclic_cycle_rev by metis
  then show "False"
    using assms by auto
qed

lemma cyclic_path_shift : 
  assumes "path M q p"
  and     "target p q = q"
shows "path M (target (take i p) q) ((drop i p) @ (take i p))"
  and "target ((drop i p) @ (take i p)) (target (take i p) q) = (target (take i p) q)"
proof -
  show "path M (target (take i p) q) ((drop i p) @ (take i p))"
    by (metis append_take_drop_id assms(1) assms(2) path_append path_append_elim path_append_target)
  show "target ((drop i p) @ (take i p)) (target (take i p) q) = (target (take i p) q)"
    by (metis append_take_drop_id assms(2) path_append_target)
qed

lemma cyclic_path_transition_source_property :
  assumes "\<exists> t \<in> set p . P (t_source t)"
  and     "\<forall> t \<in> set p . P (t_source t) \<longrightarrow> P (t_target t)"
  and     "path M q p"
  and     "target p q = q"
shows "\<forall> t \<in> set p . P (t_source t)"
  and "\<forall> t \<in> set p . P (t_target t)"
proof -
  obtain t0 where "t0 \<in> set p" and "P (t_source t0)"
    using assms(1) by blast
  then obtain i where "i < length p" and "p ! i = t0"
    by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target (take i p) q) ?p"
    using cyclic_path_shift(1)[OF assms(3,4), of i] by assumption
  
  have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed
  then have "\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)"
    using assms(2) by blast
  
  have "\<And> j . j < length ?p \<Longrightarrow> P (t_source (?p ! j))"
  proof -
    fix j assume "j < length ?p"
    then show "P (t_source (?p ! j))"
    proof (induction j)
      case 0
      then show ?case 
        using \<open>p ! i = t0\<close> \<open>P (t_source t0)\<close>
        by (metis \<open>i < length p\<close> drop_eq_Nil hd_append2 hd_conv_nth hd_drop_conv_nth leD length_greater_0_conv)  
    next
      case (Suc j)
      then have "P (t_source (?p ! j))"
        by auto
      then have "P (t_target (?p ! j))"
        using Suc.prems \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        using Suc_lessD nth_mem by blast 
      moreover have "t_target (?p ! j) = t_source (?p ! (Suc j))"
        using path_source_target_index[OF Suc.prems \<open>path M (target (take i p) q) ?p\<close>] by assumption
      ultimately show ?case 
        using \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        by simp
    qed
  qed
  then have "\<forall> t \<in> set ?p . P (t_source t)"
    by (metis in_set_conv_nth)
  then show "\<forall> t \<in> set p . P (t_source t)"
    using \<open>set ?p = set p\<close> by blast
  then show "\<forall> t \<in> set p . P (t_target t)"
    using assms(2) by blast
qed




lemma cycle_incoming_transition_ex :
  assumes "path M q p"
  and     "p \<noteq> []"
  and     "target p q = q"
  and     "t \<in> set p"
shows "\<exists> tI \<in> set p . t_target tI = t_source t"
proof -
  obtain i where "i < length p" and "p ! i = t"
    using assms(4) by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target (take i p) q) ?p"
  and  "target ?p (target (take i p) q) = target (take i p) q"
    using cyclic_path_shift[OF assms(1,3), of i] by linarith+

  have "p = (take i p @ drop i p)" by auto
  then have "path M (target (take i p) q) (drop i p)" 
    using path_suffix assms(1) by metis
  moreover have "t = hd (drop i p)"
    using \<open>i < length p\<close> \<open>p ! i = t\<close>
    by (simp add: hd_drop_conv_nth) 
  ultimately have "path M (target (take i p) q) [t]"
    by (metis \<open>i < length p\<close> append_take_drop_id assms(1) path_append_elim take_hd_drop)
  then have "t_source t = (target (take i p) q)"
    by auto  
  moreover have "t_target (last ?p) = (target (take i p) q)"
    using \<open>path M (target (take i p) q) ?p\<close> \<open>target ?p (target (take i p) q) = target (take i p) q\<close> assms(2)
    unfolding target.simps visited_states.simps last.simps
  proof -
    assume a1: "(if map t_target (drop i p @ take i p) = [] then if map t_target (take i p) = [] then q else last (map t_target (take i p)) else last (map t_target (drop i p @ take i p))) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
    have "drop i p @ take i p \<noteq> [] \<and> map t_target (drop i p @ take i p) \<noteq> []"
      using \<open>p \<noteq> []\<close> by fastforce
    moreover
    { assume "map t_target (take i p) \<noteq> [] \<and> map t_target (drop i p @ take i p) \<noteq> []"
      then have "t_target (last (drop i p @ take i p)) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
        by (simp add: last_map) }
    ultimately show "t_target (last (drop i p @ take i p)) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
      using a1 by (metis (no_types) last_map)
  qed
    
  
  moreover have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed

  ultimately show ?thesis
    by (metis \<open>i < length p\<close> append_is_Nil_conv drop_eq_Nil last_in_set leD) 
qed





    
(* note: does not require q to actually be a state of M *)   
fun deadlock_state :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where 
  "deadlock_state M q = (\<not>(\<exists> t \<in> h M . t_source t = q))"

lemma deadlock_state_alt_def : "deadlock_state M q = (LS M q \<subseteq> {[]})" 
proof 
  show "deadlock_state M q \<Longrightarrow> LS M q \<subseteq> {[]}" 
  proof -
    assume "deadlock_state M q"
    moreover have "\<And> p . deadlock_state M q \<Longrightarrow> path M q p \<Longrightarrow> p = []"
      unfolding deadlock_state.simps by (metis path.cases) 
    ultimately show "LS M q \<subseteq> {[]}"
      unfolding LS.simps by blast
  qed
  show "LS M q \<subseteq> {[]} \<Longrightarrow> deadlock_state M q"
    unfolding LS.simps deadlock_state.simps using path.cases[of M q] by blast
qed

lemma acyclic_deadlock_states :
  assumes "acyclic M"
  shows "\<exists> q \<in> nodes M . deadlock_state M q"
proof (rule ccontr)
  assume "\<not> (\<exists>q\<in>nodes M. deadlock_state M q)"
  then have *: "\<And> q . q \<in> nodes M \<Longrightarrow> (\<exists> t \<in> h M . t_source t = q)"
    unfolding deadlock_state.simps by blast

  let ?p = "arg_max_on length {p. path M (initial M) p}"
  

  have "finite {p. path M (initial M) p}"
    using acyclic_finite_paths assms by auto
  moreover have "{p. path M (initial M) p} \<noteq> {}" 
    by auto
  ultimately obtain p where "path M (initial M) p" and "\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p" 
    using max_length_elem
    by (metis mem_Collect_eq not_le_imp_less)

  then obtain t where "t \<in> h M" and "t_source t = target p (initial M)"
    using * path_target_is_node by metis

  then have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close>
    by (simp add: path_append_last) 

  then show "False"
    using \<open>\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p\<close>
    by (metis impossible_Cons length_rotate1 rotate1.simps(2)) 
qed


lemma deadlock_prefix :
  assumes "path M q p"
  and     "t \<in> set (butlast p)"
shows "\<not> (deadlock_state M (t_target t))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t' p')
  
  show ?case proof (cases "t \<in> set (butlast p')")
    case True
    show ?thesis 
      using snoc.IH[OF _ True] snoc.prems(1)
      by blast 
  next
    case False
    then have "p' = (butlast p')@[t]"
      using snoc.prems(2) by (metis append_butlast_last_id append_self_conv2 butlast_snoc in_set_butlast_appendI list_prefix_elem set_ConsD)
    then have "path M q ((butlast p'@[t])@[t'])"
      using snoc.prems(1)
      by auto 
    
    have "t' \<in> h M" and "t_source t' = target (butlast p'@[t]) q"
      using path_suffix[OF \<open>path M q ((butlast p'@[t])@[t'])\<close>]
      by auto
    then have "t' \<in> h M \<and> t_source t' = t_target t"
      unfolding target.simps visited_states.simps by auto
    then show ?thesis 
      unfolding deadlock_state.simps using \<open>t' \<in> h M\<close> by blast
  qed
qed


fun completed_path :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a Transition list \<Rightarrow> bool" where
  "completed_path M q p = deadlock_state M (target p q)"

fun minimal :: "('a, 'b) FSM_scheme \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> nodes M . \<forall> q' \<in> nodes M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"

definition retains_outputs_for_states_and_inputs :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> bool" where
  "retains_outputs_for_states_and_inputs M S = (\<forall> tS \<in> h S . \<forall> tM \<in> h M . (t_source tS = t_source tM \<and> t_input tS = t_input tM) \<longrightarrow> tM \<in> h S)"


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
    assume "\<not>(\<exists>q'. io_targets M io q = {q'})"
    then have "\<exists> q' . q' \<noteq> target p q \<and> q' \<in> io_targets M io q"
    proof -
      have "\<not> io_targets M io q \<subseteq> {target p q}"
        using \<open>\<not>(\<exists>q'. io_targets M io q = {q'})\<close> \<open>target p q \<in> io_targets M io q\<close> by blast
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

lemma io_targets_are_nodes :
  assumes "q' \<in> io_targets M io q"
      and "q \<in> nodes M"
  shows "q' \<in> nodes M"              
  by (meson assms contra_subsetD io_targets_nodes)
  


lemma completely_specified_io_targets : 
  assumes "completely_specified M"
  shows "\<forall> q \<in> io_targets M io (initial M) . \<forall> x \<in> set (inputs M) . \<exists> t \<in> h M . t_source t = q \<and> t_input t = x"
  by (meson assms completely_specified.elims(2) io_targets_are_nodes nodes.initial)
  

lemma observable_path_language_step :
  assumes "observable M"
      and "path M q p"
      and "\<not> (\<exists>t\<in>h M.
               t_source t = target p q \<and>
               t_input t = x \<and> t_output t = y)"
    shows "(p_io p)@[(x,y)] \<notin> LS M q"
using assms proof (induction p rule: rev_induct)
  case Nil
  show ?case proof
    assume "p_io [] @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = [(x,y)]" unfolding LS.simps
      by force 
    then obtain t where "p' = [t]" by blast
    
    have "t\<in>h M" and "t_source t = target [] q"
      using \<open>path M q p'\<close> \<open>p' = [t]\<close> by auto
    moreover have "t_input t = x \<and> t_output t = y"
      using \<open>p_io p' = [(x,y)]\<close> \<open>p' = [t]\<close> by auto
    ultimately show "False"
      using Nil.prems(3) by blast
  qed
next
  case (snoc t p)
  then have "path M q p" and "t_source t = target p q" and "t \<in> h M" by auto

  show ?case proof
    assume "p_io (p @ [t]) @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = p_io (p @ [t]) @ [(x, y)]"
      by auto
    then obtain p'' t' t'' where "p' = p''@[t']@[t'']"
      by (metis (no_types, lifting) append.assoc map_butlast map_is_Nil_conv snoc_eq_iff_butlast)
    then have "path M q p''" 
      using \<open>path M q p'\<close> by blast
    
    
    have "p_io p'' = p_io p"
      using \<open>p' = p''@[t']@[t'']\<close> \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> by auto
    then have "p'' = p"
      using observable_path_unique[OF assms(1) \<open>path M q p''\<close> \<open>path M q p\<close>] by blast

    have "t_source t' = target p'' q" and "t' \<in> h M"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    then have "t_source t' = t_source t"
      using \<open>p'' = p\<close> \<open>t_source t = target p q\<close> by auto 
    moreover have "t_input t' = t_input t \<and> t_output t' = t_output t"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> h M\<close> \<open>t' \<in> h M\<close> assms(1) unfolding observable.simps by (meson prod.expand) 

    have "t''\<in>h M" and "t_source t'' = target (p@[t]) q"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> \<open>t' = t\<close> by auto
    moreover have "t_input t'' = x \<and> t_output t'' = y"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    ultimately show "False"
      using snoc.prems(3) by blast
  qed
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

fun is_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> h A \<subseteq> h B \<and> inputs A = inputs B \<and> outputs A = outputs B)"
  

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
    have f1: "initial A = initial B \<and> h A \<subseteq> h B \<and> inputs A = inputs B \<and> outputs A = outputs B"
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
  using assms by auto

lemma submachine_reduction : 
  assumes "is_submachine A B"
  shows "is_io_reduction A B"
  using submachine_path[OF assms] assms by auto 


lemma complete_submachine_initial :
  assumes "is_submachine A B"
      and "completely_specified A"
  shows "completely_specified_state B (initial B)"
proof -
  have "initial B = initial A"
    using assms(1) by auto

  moreover have "completely_specified_state A (initial A)"
    using assms(2) by (meson completely_specified_states nodes.initial) 

  moreover have "inputs A = inputs B"
    using assms(1) by auto

  moreover have "h A \<subseteq> h B"
    using submachine_h[OF assms(1)] by assumption

  ultimately show ?thesis 
    unfolding completely_specified_state.simps by fastforce
qed

lemma submachine_language :
  assumes "is_submachine S M"
  shows "L S \<subseteq> L M"
proof - (* TODO: refactor auto-generated code *)
  obtain pps :: "(integer \<times> integer) list set \<Rightarrow> (integer \<times> integer) list set \<Rightarrow> (integer \<times> integer) list" where
    f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
    by moura
  obtain ppsa :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
    f2: "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (ppsa x0 x1 x2) \<and> path x2 x1 (ppsa x0 x1 x2))"
    by moura
  { assume "path M (initial M) (ppsa (pps (LS M (initial M)) (LS S (initial S))) (initial M) S)"
    moreover
    { assume "\<exists>ps. pps (LS M (initial M)) (LS S (initial S)) = p_io ps \<and> path M (initial M) ps"
      then have "pps (LS M (initial M)) (LS S (initial S)) \<notin> LS S (initial S) \<or> pps (LS M (initial M)) (LS S (initial S)) \<in> LS M (initial M)"
        by simp
      then have ?thesis
        using f1 by blast }
    ultimately have "LS S (initial S) \<subseteq> LS M (initial M) \<or> pps (LS M (initial M)) (LS S (initial S)) \<noteq> p_io (ppsa (pps (LS M (initial M)) (LS S (initial S))) (initial M) S) \<or> \<not> path S (initial M) (ppsa (pps (LS M (initial M)) (LS S (initial S))) (initial M) S)"
      by blast }
  moreover
  { assume "pps (LS M (initial M)) (LS S (initial S)) \<noteq> p_io (ppsa (pps (LS M (initial M)) (LS S (initial S))) (initial M) S) \<or> \<not> path S (initial M) (ppsa (pps (LS M (initial M)) (LS S (initial S))) (initial M) S)"
    then have "\<not>(\<exists> ps. pps (LS M (initial M)) (LS S (initial S)) = p_io ps \<and> path S (initial M) ps)"
      using f2 by blast
    then have "~(\<exists>ps. pps (LS M (initial M)) (LS S (initial S)) = p_io ps \<and> path S (initial S) ps)"
      by (metis (no_types) assms is_submachine.simps)
    then have "pps (LS M (initial M)) (LS S (initial S)) \<notin> {p_io ps |ps. path S (initial S) ps}"
      by force
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


lemma submachine_transitive :
  assumes "is_submachine S M"
  and     "is_submachine S' S"
shows "is_submachine S' M"
  using assms unfolding is_submachine.simps by force

lemma transitions_subset_path :
  assumes "set p \<subseteq> h M"
  and     "p \<noteq> []"
  and     "path S q p"
shows "path M q p"
  using assms by (induction p arbitrary: q; auto)


lemma transition_subset_paths :
  assumes "set (transitions S) \<subseteq> set (transitions M)"
  and "initial S \<in> nodes M"
  and "inputs S = inputs M"
  and "outputs S = outputs M"
  and "path S (initial S) p"
shows "path M (initial S) p"
  using assms(5) proof (induction p rule: rev_induct)
case Nil
  then show ?case using assms(2) by auto
next
  case (snoc t p)
  then have "path S (initial S) p" 
        and "t \<in> h S" 
        and "t_source t = target p (initial S)" 
        and "path M (initial S) p"
    by auto

  have "t \<in> set (transitions M)"
    using assms(1) \<open>t \<in> h S\<close> by auto
  moreover have "t_source t \<in> nodes M"
    using \<open>t_source t = target p (initial S)\<close> \<open>path M (initial S) p\<close>
    using path_target_is_node by fastforce 
  ultimately have "t \<in> h M"
    using \<open>t \<in> h S\<close> assms(3,4) by auto
  then show ?case
    using \<open>path M (initial S) p\<close>
    using snoc.prems by auto 
qed 

lemma transition_subset_h :
  assumes "set (transitions S) \<subseteq> set (transitions M)"
  and "initial S \<in> nodes M"
  and "inputs S = inputs M"
  and "outputs S = outputs M"
shows "h S \<subseteq> h M"
proof 
  fix t assume "t \<in> h S"
  then obtain p where "path S (initial S) p" and "target p (initial S) = t_source t"
    by (metis path_begin_node path_to_node single_transition_path)
  then have "t_source t \<in> nodes M"
    using transition_subset_paths[OF assms, of p] path_target_is_node[of M "initial S" p] by auto
  then show "t \<in> h M"
    using \<open>t \<in> h S\<close> assms(1,3,4) by auto
qed



subsection \<open>Changing Initial States\<close>

fun from_FSM :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme" where
  "from_FSM M q = \<lparr> initial = q, inputs = inputs M, outputs = outputs M, transitions = transitions M, \<dots> = FSM.more M \<rparr>"

lemma from_FSM_simps[simp]:
  "initial (from_FSM M q) = q"  
  "inputs (from_FSM M q) = inputs M"
  "outputs (from_FSM M q) = outputs M"
  "transitions (from_FSM M q) = transitions M"
  by simp+


lemma from_FSM_path_initial :
  assumes "q \<in> nodes M"
  shows "path M q p = path (from_FSM M q) (initial (from_FSM M q)) p"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by blast 
next
  case (snoc x xs)
  then have *: "path M q xs = path (from_FSM M q) (initial (from_FSM M q)) xs" by auto

  have "path M q (xs @ [x]) \<Longrightarrow> path (from_FSM M q) (initial (from_FSM M q)) (xs @ [x])"
  proof -
    assume "path M q (xs @ [x])"
    then have "path (from_FSM M q) (initial (from_FSM M q)) xs" using * by auto
    then show ?thesis
    proof -
      have f1: "\<forall>f a p ps. is_path (f::('a, 'b) FSM_scheme) a (p # ps) = (t_source p = a \<and> p \<in> set (transitions f) \<and> t_source p \<in> nodes f \<and> t_input p \<in> set (inputs f) \<and> t_output p \<in> set (outputs f) \<and> path f (t_target p) ps)"
        using is_path.simps(2) by blast
      have f2: "t_source x = target xs q \<and> x \<in> set (transitions M) \<and> t_source x \<in> nodes M \<and> t_input x \<in> set (inputs M) \<and> t_output x \<in> set (outputs M) \<and> path M (t_target x) []"
        using \<open>path M q (xs @ [x])\<close> by force
      then have "x \<in> set (transitions (from_FSM M q))"
        by simp
      then have "is_path (from_FSM M q) (target xs q) [x]"
        using f2 f1 by (metis \<open>path (from_FSM M q) (initial (from_FSM M q)) xs\<close> from_FSM_simps(1) from_FSM_simps(2) from_FSM_simps(3) nodes.step path.nil path_target_is_node)
      then show ?thesis
        by (metis \<open>path (from_FSM M q) (initial (from_FSM M q)) xs\<close> from_FSM_simps(1) path_append path_code)
    qed
  qed
  moreover have "path (from_FSM M q) (initial (from_FSM M q)) (xs @ [x]) \<Longrightarrow> path M q (xs @ [x])"
  proof -
    assume "path (from_FSM M q) (initial (from_FSM M q)) (xs @ [x])"
    then have "path M q xs" using * by auto
    then show ?thesis
    proof -
      have f1: "\<forall>f a p ps. is_path (f::('a, 'b) FSM_scheme) a (p # ps) = (t_source p = a \<and> p \<in> set (transitions f) \<and> t_source p \<in> nodes f \<and> t_input p \<in> set (inputs f) \<and> t_output p \<in> set (outputs f) \<and> path f (t_target p) ps)"
        using is_path.simps(2) by blast
      have f2: "t_source x = target xs q \<and> x \<in> set (transitions (from_FSM M q)) \<and> t_source x \<in> nodes (from_FSM M q) \<and> t_input x \<in> set (inputs (from_FSM M q)) \<and> t_output x \<in> set (outputs (from_FSM M q)) \<and> path (from_FSM M q) (t_target x) []"
        using \<open>path (from_FSM M q) (initial (from_FSM M q)) (xs @ [x])\<close> by force
      then have "t_source x \<in> nodes M"
        by (metis (full_types) \<open>path M q xs\<close> path_target_is_node)
      then show ?thesis
        using f2 f1 by (metis \<open>path M q xs\<close> from_FSM_simps(2) from_FSM_simps(3) from_FSM_simps(4) nodes.step path.nil path_append path_code)
    qed 
  qed
  ultimately show ?case
    by linarith 
qed

lemma from_FSM_nodes :
  assumes "q \<in> nodes M"
  shows "nodes (from_FSM M q) \<subseteq> nodes M"
  by (metis assms distinct_path_to_node from_FSM_path_initial from_FSM_simps(1) path_target_is_node subsetI) 

lemma from_FSM_path :
  assumes "q \<in> nodes M"
      and "path (from_FSM M q) q' p"
    shows "path M q' p"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case
    by (meson from_FSM_nodes path.nil path_begin_node subsetCE) 
next
  case (snoc x xs)
  then show ?case
    by (metis from_FSM_simps(2) from_FSM_simps(3) from_FSM_simps(4) path_cons_elim path_equivalence_by_h path_prefix path_suffix path_target_is_node wf_transition_simp) 
qed


lemma from_FSM_h :
  assumes "q \<in> nodes M"
  shows "h (from_FSM M q) \<subseteq> h M"
  using assms from_FSM_nodes by fastforce

    
lemma submachine_from :
  assumes "is_submachine S M"
      and "q \<in> nodes S"
  shows "is_submachine (from_FSM S q) (from_FSM M q)"
proof -
  have "q \<in> nodes M" using submachine_nodes[OF assms(1)] assms(2) by blast

  have "\<And> p . path (from_FSM S q) q p  \<Longrightarrow> path (from_FSM M q) q p" 
  proof -
    fix p assume "path (from_FSM S q) q p"
    then show "path (from_FSM M q) q p"
    proof (induction p rule: rev_induct)
      case Nil
      then show ?case
        by (metis from_FSM_simps(1) nodes.initial path.nil) 
    next
      case (snoc x xs)
      then show ?case
        by (metis (no_types, lifting) \<open>q \<in> nodes M\<close> assms(1) assms(2) from_FSM_path_initial from_FSM_simps(1) submachine_path) 
    qed
  qed
  then have "nodes (from_FSM S q) \<subseteq> nodes (from_FSM M q)"
    by (metis from_FSM_simps(1) nodes_path_initial path_to_node subsetI)
    

  then have "h (from_FSM S q) \<subseteq> h (from_FSM M q)"
  proof -
    have f1: "initial S = initial M \<and> set (wf_transitions S) \<subseteq> set (wf_transitions M) \<and> inputs S = inputs M \<and> outputs S = outputs M"
      by (metis (no_types) assms(1) is_submachine.simps)
    obtain aa :: "('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> 'a" and pp :: "('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> integer \<times> integer \<times> 'a" where
      f2: "\<forall>x0 x1. (\<exists>v2 v3. (v2, v3) \<in> x1 \<and> (v2, v3) \<notin> x0) = ((aa x0 x1, pp x0 x1) \<in> x1 \<and> (aa x0 x1, pp x0 x1) \<notin> x0)"
      by moura
    have f3: "\<forall>p f. (p \<in> set (wf_transitions (f::('a, 'b) FSM_scheme))) = (p \<in> set (transitions f) \<and> t_source p \<in> nodes f \<and> t_input p \<in> set (inputs f) \<and> t_output p \<in> set (outputs f))"
      by blast
    moreover
    { assume "(aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (transitions M)"
      then have "(aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (transitions (from_FSM M q))"
        by (metis from_FSM_simps(4))
      moreover
      { assume "t_input (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (inputs (from_FSM M q))"
        then have "(aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (transitions (from_FSM S q)) \<or> t_source (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> nodes (from_FSM S q) \<or> t_input (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (inputs (from_FSM S q)) \<or> t_output (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (outputs (from_FSM S q))"
          using f1 by (metis from_FSM_simps(2)) }
        moreover
        { assume "t_output (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (outputs (from_FSM M q))"
          then have "(aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (transitions (from_FSM S q)) \<or> t_source (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> nodes (from_FSM S q) \<or> t_input (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (inputs (from_FSM S q)) \<or> t_output (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (outputs (from_FSM S q))"
            using f1 by (metis (no_types) from_FSM_simps(3)) }
        moreover
        { assume "(aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (transitions (from_FSM M q)) \<and> t_source (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> nodes (from_FSM M q) \<and> t_input (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (inputs (from_FSM M q)) \<and> t_output (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (outputs (from_FSM M q))"
          then have ?thesis
            using f3 f2 by (metis (no_types) subrelI) }
      ultimately have "set (wf_transitions (from_FSM S q)) \<subseteq> set (wf_transitions (from_FSM M q)) \<or> (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (wf_transitions (from_FSM S q)) \<or> (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (wf_transitions (from_FSM M q))"
        using \<open>nodes (from_FSM S q) \<subseteq> nodes (from_FSM M q)\<close> by blast }
    ultimately have "set (wf_transitions (from_FSM S q)) \<subseteq> set (wf_transitions (from_FSM M q)) \<or> (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<notin> set (wf_transitions (from_FSM S q)) \<or> (aa (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q))), pp (set (wf_transitions (from_FSM M q))) (set (wf_transitions (from_FSM S q)))) \<in> set (wf_transitions (from_FSM M q))"
      using f1 by (meson assms(2) from_FSM_h set_rev_mp)
    then show ?thesis
      using f2 by (meson subrelI)
  qed

  then show ?thesis using assms(1) by auto
qed
    
   

lemma from_FSM_next_h :
  assumes "t \<in> h M"
      and "t_source t = initial M"
    shows "h (from_FSM M (t_target t)) \<subseteq> h M"
  by (meson assms(1) from_FSM_h nodes.step wf_transition_simp)


lemma from_FSM_nodes_transitions : 
  "t \<in> h M \<Longrightarrow> t_source t \<in> nodes (from_FSM M q) \<Longrightarrow> t \<in> h (from_FSM M q)"
  by simp

lemma from_FSM_path_rev_initial :
  assumes "path M q p"
  shows "path (from_FSM M q) q p"
using assms proof (induction p rule: rev_induct)
  case Nil
  have "q \<in> nodes M" using path_begin_node[OF assms] by assumption
  have "initial (from_FSM M q) \<in> nodes (from_FSM M q)" using nodes.initial[of "from_FSM M q"] by assumption
  show ?case using path.nil[OF nodes.initial[of "from_FSM M q"]] by simp
next
  case (snoc t p)
  then have "path (from_FSM M q) q p" by auto

  have "t \<in> h M" and "t_source t = target p q" using snoc.prems by auto

  from \<open>t \<in> h M\<close> have "t \<in> hIO (from_FSM M q)" by auto
  moreover have "t_source t \<in> nodes (from_FSM M q)"
    using path_target_is_node[OF \<open>path (from_FSM M q) q p\<close>] \<open>t_source t = target p q\<close> by auto
  ultimately have "t \<in> h (from_FSM M q)" by auto
  then show ?case 
    using \<open>path (from_FSM M q) q p\<close> \<open>t_source t = target p q\<close> path_append_last by metis
qed

lemma from_FSM_transition_initial:
  assumes "t \<in> h M" 
  shows "t \<in> h (from_FSM M (t_source t))" 
proof -
  have "t_source t \<in> nodes M" using assms by auto
  show ?thesis using assms
    by (meson \<open>t \<in> set (wf_transitions M)\<close> \<open>t_source t \<in> nodes M\<close> from_FSM_nodes_transitions from_FSM_path_rev_initial path.nil path_begin_node) 
qed


lemma submachine_from_h_origin :
  assumes "t \<in> h S"
  and     "is_submachine S (from_FSM M q)"
  and     "q \<in> nodes M"
shows "t \<in> h M"
  by (meson assms contra_subsetD from_FSM_h submachine_h)

subsection \<open>Filtering Transitions\<close>

lemma transition_filter_path_initial :
  assumes "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) p"
  shows "path M (initial M) p"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t p)
  then have "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)" by auto
  then have "t \<in> set (filter f (transitions M))" by auto
  then have "t \<in> set (transitions M)" by auto

  have "target p (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = t_source t"
    using snoc.prems by auto
  then have "target p (initial M) = t_source t" by auto
  moreover have "path M (initial M) p" using snoc.prems snoc.IH by auto
  ultimately have "t_source t \<in> nodes M"
    using path_target_is_node by metis
  then have "t \<in> h M"
    using \<open>t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)\<close> by auto
  then show "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close> \<open>target p (initial M) = t_source t\<close> by auto
qed

lemma transition_filter_path :
  assumes "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) q p"
  shows "path M q p"
proof -
  have "q \<in> nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>)"
    using assms path_begin_node by metis
  then obtain pQ where "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) pQ"
                   and "target pQ (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = q"
    by (metis path_to_node)
  then have "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) (pQ@p)"
    using assms path_append by metis
  then have "path M (initial M) (pQ@p)"
    using transition_filter_path_initial by auto
  then show "path M q p"
    using \<open>target pQ (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = q\<close> by auto
qed

lemma transition_filter_path_initial_rev :
  assumes "path M (initial M) p" 
      and "list_all f p"
    shows "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) p"
          (is "path ?M (initial ?M) p")
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by blast 
next
  case (snoc t p)
  then have "path ?M (initial ?M) p" and "f t" by auto

  have "target p (initial ?M) = t_source t" using snoc.prems(1) by auto
  then have "t_source t \<in> nodes ?M"
    using path_target_is_node[OF \<open>path ?M (initial ?M) p\<close>] by auto

  have "t \<in> h M" using snoc.prems(1) by auto
  then have "t \<in> h ?M"
    using \<open>f t\<close> \<open>t_source t \<in> nodes ?M\<close> by auto

  show ?case
    using \<open>path ?M (initial ?M) p\<close> \<open>target p (initial ?M) = t_source t\<close> \<open>t \<in> h ?M\<close> by auto
qed

lemma transition_filter_h :
  assumes "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)"  (is "t \<in> h ?M")
  shows "t \<in> h M" and "f t"
proof -
  from assms have "t_source t \<in> nodes ?M" by auto
  then obtain p where "path ?M (initial ?M) p"
                  and "target p (initial ?M) = t_source t"
    by (metis path_to_node)
  then have "path M (initial M) p"
    by (metis transition_filter_path_initial)
  have "t_source t \<in> nodes M"
    using path_target_is_node[OF \<open>path M (initial M) p\<close>] \<open>target p (initial ?M) = t_source t\<close> by auto
  then show "t \<in> h M"
    using \<open>t \<in> h ?M\<close> by auto
  from assms show "f t" by auto
qed

lemma transition_filter_nodes :
  "nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>) \<subseteq> nodes M" (is "nodes ?M \<subseteq> nodes M")
proof 
  fix q assume "q \<in> nodes ?M"
  then obtain p where "path ?M (initial ?M) p" 
                  and "target p (initial ?M) = q"
    by (metis path_to_node)
  then have "path M (initial M) p"
    using transition_filter_path_initial by metis
  show "q \<in> nodes M"
    using path_target_is_node[OF \<open>path M (initial M) p\<close>] \<open>target p (initial ?M) = q\<close> by auto
qed


lemma transition_filter_state_transitions :
  assumes "t_source t \<in> nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>)"
      and "t \<in> h M"
      and "f t"
    shows "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)" (is "t \<in> h ?M")
  using assms by auto

lemma transition_filter_submachine :
  "is_submachine (M\<lparr> transitions := filter f (transitions M)\<rparr>) M" 
proof -
  let ?M = "(M\<lparr> transitions := filter f (transitions M)\<rparr>)"
  have "set (transitions ?M) \<subseteq> set (transitions M)"
    by auto
  then have "h ?M \<subseteq> h M" unfolding wf_transitions.simps
  proof -
    have "\<forall>ps P. \<exists>p. (set ps \<subseteq> P \<or> (p::'a \<times> integer \<times> integer \<times> 'a) \<in> set ps) \<and> (p \<notin> P \<or> set ps \<subseteq> P)"
      by (meson subset_code(1))
    then obtain pp :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> 'a \<times> integer \<times> integer \<times> 'a" where
      f1: "\<And>ps P. (set ps \<subseteq> P \<or> pp ps P \<in> set ps) \<and> (pp ps P \<notin> P \<or> set ps \<subseteq> P)"
      by metis
    moreover
    { assume "pp (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) (set (wf_transitions M)) \<notin> set (wf_transitions M)"
      then have "pp (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) (set (wf_transitions M)) \<notin> set (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>))"
        by (metis transition_filter_h(1))
      then have "set (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) \<subseteq> set (filter (\<lambda>p. t_source p \<in> nodes M \<and> t_input p \<in> set (inputs M) \<and> t_output p \<in> set (outputs M)) (transitions M))"
        using f1 by (metis (no_types) wf_transitions.elims) }
    ultimately show "set (filter (\<lambda>p. t_source p \<in> nodes (M\<lparr>transitions := filter f (transitions M)\<rparr>) \<and> t_input p \<in> set (inputs (M\<lparr>transitions := filter f (transitions M)\<rparr>)) \<and> t_output p \<in> set (outputs (M\<lparr>transitions := filter f (transitions M)\<rparr>))) (transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>))) \<subseteq> set (filter (\<lambda>p. t_source p \<in> nodes M \<and> t_input p \<in> set (inputs M) \<and> t_output p \<in> set (outputs M)) (transitions M))"
      by (metis (no_types) wf_transitions.elims)
  qed
     
  then show ?thesis unfolding is_submachine.simps by auto
qed



lemma h_equality :
  assumes "initial A = initial B"
      and "inputs A = inputs B"
      and "outputs A = outputs B"
      and "set (transitions A) = set (transitions B)"
    shows "h A = h B"
proof -
  have "\<And> p . path A (initial A) p = path B (initial B) p"
  proof -
    fix p 
    show "path A (initial A) p = path B (initial B) p"
      using assms proof (induction p rule: rev_induct)
      case Nil
      then show ?case
        by blast 
    next
      case (snoc t p)
      then have "path A (initial A) p = path B (initial B) p" by auto
      then show ?case using assms
        by (metis path_append_elim path_cons_elim path_equivalence_by_h path_target_is_node wf_transition_simp) 
    qed
  qed
  then have "nodes A = nodes B"
    using path_to_node
    by (metis assms(1) path_target_is_node subsetI subset_antisym) 
  then show "h A = h B"
    using assms(2-4) by auto
qed
    
  
lemma h_equality' :
  assumes "initial A = initial B"
      and "inputs A = inputs B"
      and "outputs A = outputs B"
      and "h A = set (transitions B)"
    shows "h A = h B"
proof -
  have "\<And> p . path A (initial A) p = path B (initial B) p"
  proof -
    fix p 
    show "path A (initial A) p = path B (initial B) p"
      using assms proof (induction p rule: rev_induct)
      case Nil
      then show ?case
        by blast 
    next
      case (snoc t p)
      then have "path A (initial A) p = path B (initial B) p" by auto
      then show ?case using assms
        by (metis path_append_elim path_cons_elim path_equivalence_by_h path_target_is_node wf_transition_simp) 
    qed
  qed
  then have "nodes A = nodes B"
    using path_to_node
    by (metis assms(1) path_target_is_node subsetI subset_antisym) 
  then show "h A = h B"
    using assms(2-4) by auto
qed



fun trim_transitions :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme" where
  "trim_transitions M = M\<lparr> transitions := wf_transitions M\<rparr>"

lemma trim_transitions_simps[simp]:
    "initial (trim_transitions M) = initial M"
    "inputs (trim_transitions M) = inputs M" 
    "outputs (trim_transitions M) = outputs M"
    "h (trim_transitions M) = h M"
proof -
  show "initial (trim_transitions M) = initial M" by auto
  moreover show "inputs (trim_transitions M) = inputs M" by auto
  moreover show "outputs (trim_transitions M) = outputs M" by auto
  ultimately have "initial M = initial (trim_transitions M)"
    and "inputs M = inputs (trim_transitions M)"
    and "outputs M = outputs (trim_transitions M)"
    and "set (wf_transitions M) = set (transitions (trim_transitions M))" by auto
  
  then show "h (trim_transitions M) = h M" using h_equality'[of M "trim_transitions M"] by presburger
qed

lemma trim_transitions_paths : "path M q p = path (trim_transitions M) q p"
  by (metis eq_iff h_equivalence_path h_subset_path_non_initial nodes.simps trim_transitions_simps(1) trim_transitions_simps(4))

lemma trim_transitions_paths_initial : "path M (initial M) p = path (trim_transitions M) (initial (trim_transitions M)) p"
  by (metis trim_transitions_paths trim_transitions_simps(1))

lemma trim_transitions_language : "L M = L (trim_transitions M)"
  using trim_transitions_paths_initial unfolding LS.simps by blast
  
lemma trim_transitions_nodes : "nodes M = nodes (trim_transitions M)"
  using h_nodes[of M] h_nodes[of "trim_transitions M"] trim_transitions_simps(1)[of M] trim_transitions_simps(4)[of M] by presburger

lemma trim_transitions_submachine : "is_submachine S M \<Longrightarrow> is_submachine (trim_transitions S) M"
  unfolding trim_transitions.simps is_submachine.simps by auto

lemma trim_transitions_single_input : "single_input S \<Longrightarrow> single_input (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_simps(4)[of S] unfolding trim_transitions.simps single_input.simps by blast

lemma trim_transitions_acyclic : "acyclic S \<Longrightarrow> acyclic (trim_transitions S)"
  using trim_transitions_paths[of S]  unfolding trim_transitions.simps acyclic.simps by simp

lemma trim_transitions_deadlock_state_nodes : "deadlock_state S q = deadlock_state (trim_transitions S) q"
  by (metis deadlock_state.simps trim_transitions_simps(4))

lemma trim_transitions_t_source' : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes S"
  unfolding trim_transitions.simps by auto

lemma trim_transitions_t_source : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_t_source'[of t S] by blast

lemma trim_transitions_t_source_h : "t \<in> h (trim_transitions S) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_t_source[of t S] unfolding wf_transitions.simps by auto

lemma trim_transitions_transitions : "h (trim_transitions S) = set (transitions (trim_transitions S))"
  unfolding trim_transitions.simps 
proof -
  show "set (wf_transitions (S\<lparr>transitions := wf_transitions S\<rparr>)) = set (transitions (S\<lparr>transitions := wf_transitions S\<rparr>))"
    by (metis (no_types) select_convs(4) surjective trim_transitions.simps trim_transitions_simps(4) update_convs(4))
qed  

lemma transitions_reorder :  
  assumes     "initial S' = initial S"
  and     "inputs S' = inputs S"
  and     "outputs S' = outputs S"
  and     "set (transitions S') = set (transitions S)"
shows "h S' = h S"
  and "path S' q p = path S q p"
  and "nodes S' = nodes S"
proof-
  show "h S' = h S"
    using h_equality[OF assms] by assumption

  show "path S' q p = path S q p"
    by (metis \<open>h S' = h S\<close> assms(1) h_subset_path h_subset_path_non_initial nodes.initial order_refl)
    
  show "nodes S' = nodes S"
  proof -
    have "insert (initial S') {t_target p |p. p \<in> set (wf_transitions S)} = nodes S"
      by (metis (no_types) assms(1) h_nodes)
    then show ?thesis
      by (metis \<open>set (wf_transitions S') = set (wf_transitions S)\<close> h_nodes)
  qed
qed

subsection \<open>Further Reachability Formalisations\<close>

(* nodes that are reachable in at most k transitions *)
fun reachable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target p q | p . path M q p \<and> length p \<le> n}" 


lemma reachable_k_0_initial : "reachable_k M (initial M) 0 = {initial M}" 
  by auto

lemma reachable_k_nodes : "nodes M = reachable_k M (initial M) ( size M - 1)"
proof -
  have "\<And>q. q \<in> nodes M \<Longrightarrow> q \<in> reachable_k M (initial M) ( size M - 1)"
  proof -
    fix q assume "q \<in> nodes M"
    then obtain p where "path M (initial M) p" and "target p (initial M) = q"
      by (metis path_to_node) 
    then obtain p' where "path M (initial M) p'"
                     and "target p' (initial M) = target p (initial M)" 
                     and "length p' < size M"
      using distinct_path_length_limit_nodes[of "M" "initial M" p]
      using distinct_path_length[of M "initial M" p] by auto
    then show "q \<in> reachable_k M (initial M) ( size M - 1)"
      using \<open>target p (initial M) = q\<close> list.size(3) mem_Collect_eq not_less_eq_eq reachable_k.simps by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( size M - 1) \<Longrightarrow> x \<in> nodes M"
    using nodes_path_initial by auto
  
  ultimately show ?thesis by blast
qed


subsection \<open>Generating Submachines\<close>

lemma nodes_from_transition_targets :
  "nodes M \<subseteq> insert (initial M) (set (map t_target (transitions M)))"
proof -
  have "nodes M \<subseteq> insert (initial M) (set (map t_target (wf_transitions M)))"
    using image_iff nodes_initial_or_target by fastforce
  moreover have "(set (map t_target (wf_transitions M))) \<subseteq> (set (map t_target (transitions M)))"
    by auto
  ultimately show ?thesis by blast
qed


lemma submachine_by_transitions :
  assumes "set ts \<subseteq> set (transitions M)"
  shows "is_submachine (M\<lparr> transitions := ts \<rparr>) M"
proof -
  let ?M = "(M\<lparr> transitions := ts \<rparr>)"
  let ?MF = "M\<lparr> transitions := filter (\<lambda> t . t \<in> set ts) (transitions M) \<rparr>"
  
  have "set (transitions ?M) = set (transitions ?MF)"
    using assms by auto
  have "h ?M = h ?MF"
    using h_equality[OF _ _ _ \<open>set (transitions ?M) = set (transitions ?MF)\<close>] by auto
  moreover have "is_submachine ?MF M"
    using transition_filter_submachine by metis
  ultimately show ?thesis by auto
qed

subsubsection \<open>Generate all Submachines up to h-Equivalence\<close> 

fun generate_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> bool list \<Rightarrow> ('a, 'b) FSM_scheme" where
  "generate_submachine M bs = M\<lparr> transitions := map fst (filter snd (zip (transitions M) bs)) \<rparr>"

lemma generate_submachine_is_submachine : "is_submachine (generate_submachine M bs) M" 
proof -
  have "\<And> x . x \<in> set (map fst (filter snd (zip (transitions M) bs))) \<Longrightarrow> x \<in> set (transitions M)"
    by (metis (no_types, lifting) filter_eq_nths in_set_takeD map_fst_zip_take notin_set_nthsI nths_map)
  then show ?thesis  
    using generate_submachine.simps by (metis submachine_by_transitions subsetI) 
qed

fun generate_submachines :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme list" where
  "generate_submachines M = map (generate_submachine M) (generate_selector_lists (length (transitions M)))"

lemma generate_submachines_containment :
  assumes "is_submachine S M"
  shows "\<exists> S' \<in> set (generate_submachines M) . (h S = h S')"
proof -
  let ?ts = "filter (\<lambda> t . t \<in> h S) (transitions M)"
  have "h S \<subseteq> set (transitions M)" using assms by auto
  then have "h S = set ?ts" by auto
  
  have "set ?ts \<subseteq> set (transitions M)" by auto
  then obtain bs where "length bs = length (transitions M)"  and "set ?ts = set (map fst (filter snd (zip (transitions M) bs)))"
    using selector_list_ex[of "?ts" "transitions M"] by blast
  then have "bs \<in> set (generate_selector_lists (length (transitions M)))"
    using generate_selector_lists_set[of "length (transitions M)"] by blast
  then have *: "generate_submachine M bs \<in> set (generate_submachines M)" 
    by auto
  
  have "set ?ts = set (transitions (generate_submachine M bs))"
    using \<open>set ?ts = set (map fst (filter snd (zip (transitions M) bs)))\<close> unfolding generate_submachine.simps by auto
  then have "h S = set (transitions (generate_submachine M bs))"
    using \<open>h S = set ?ts\<close> by auto

  have **: "h S = h (generate_submachine M bs)"
    using h_equality'[OF _ _ _ \<open>h S = set (transitions (generate_submachine M bs))\<close>] assms by auto

  show ?thesis using * ** by blast
qed

lemma generate_submachines_are_submachines :
  assumes "S \<in> set (generate_submachines M)"
  shows "is_submachine S M"
  using assms generate_submachine_is_submachine[of M] unfolding generate_submachines.simps by fastforce

value "generate_submachines M_ex"





subsubsection \<open>Generate all Single-Input Submachines up to h-Equivalence\<close> 

fun generate_submachine_from_assignment :: "('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> Input option) list \<Rightarrow> ('a, 'b) FSM_scheme" where
  "generate_submachine_from_assignment M assn = M\<lparr> transitions := filter (\<lambda> t . (t_source t, Some (t_input t)) \<in> set assn) (wf_transitions M)\<rparr>"

lemma generate_submachine_for_contained_assn: "assn \<in> set assns \<Longrightarrow> generate_submachine_from_assignment CSep assn \<in> set (map (\<lambda> assn . generate_submachine_from_assignment CSep assn) assns)"
  by simp

  
subsubsection \<open>Induction Schemes\<close>





lemma acyclic_induction [consumes 1, case_names node]:
  assumes "acyclic M"
      and "\<And> q . q \<in> nodes M \<Longrightarrow> (\<And> t . t \<in> h M \<Longrightarrow> ((t_source t = q) \<Longrightarrow> P (t_target t))) \<Longrightarrow> P q"
    shows "\<forall> q \<in> nodes M . P q"
proof 
  fix q assume "q \<in> nodes M"

  let ?k = "Max (image length {p . path M q p})"
  have "finite {p . path M q p}" using acyclic_finite_paths[OF assms(1)] by auto
  then have k_prop: "(\<forall> p . path M q p \<longrightarrow> length p \<le> ?k)" by auto

  moreover have "\<And> q k . q \<in> nodes M \<Longrightarrow> (\<forall> p . path M q p \<longrightarrow> length p \<le> k) \<Longrightarrow> P q"
  proof -
    fix q k assume "q \<in> nodes M" and "(\<forall> p . path M q p \<longrightarrow> length p \<le> k)"
    then show "P q" 
    proof (induction k arbitrary: q)
      case 0
      then have "{p . path M q p} = {[]}" by blast 
      then have "LS M q \<subseteq> {[]}" unfolding LS.simps by blast
      then have "deadlock_state M q" using deadlock_state_alt_def by metis
      then show ?case using assms(2)[OF \<open>q \<in> nodes M\<close>] unfolding deadlock_state.simps by blast
    next
      case (Suc k)
      have "\<And> t . t \<in> h M \<Longrightarrow> (t_source t = q) \<Longrightarrow> P (t_target t)"
      proof -
        fix t assume "t \<in> h M" and "t_source t = q" 
        then have "t_target t \<in> nodes M"
          using wf_transition_target by metis
        moreover have "\<forall>p. path M (t_target t) p \<longrightarrow> length p \<le> k"
          using Suc.prems(2) \<open>t \<in> set (wf_transitions M)\<close> \<open>t_source t = q\<close> by auto
        ultimately show "P (t_target t)" 
          using Suc.IH by auto
      qed
      then show ?case using assms(2)[OF Suc.prems(1)] by blast
    qed
  qed

  ultimately show "P q" using \<open>q \<in> nodes M\<close> by blast
qed



subsection \<open>Further Path Enumeration Algorithms\<close>

fun paths_for_input :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> Input list \<Rightarrow> 'a Transition list list" where
  "paths_for_input M q [] = [[]]" |
  "paths_for_input M q (x#xs) = 
    concat (map 
      (\<lambda>y . concat (map 
              (\<lambda> t . (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs)))
              (filter (\<lambda> t . t_source t = q \<and> t_input t = x \<and> t_output t = y) (wf_transitions M)))) 
      (outputs M))"



value "paths_for_input M_ex_9 0 []"
value "paths_for_input M_ex_9 0 [1]"
value "paths_for_input M_ex_9 0 [1,1]"
value "paths_for_input M_ex_9 0 [1,1,1]"
value "paths_for_input M_ex_9 0 [1,1,1,1,1,1,1,1]"


lemma paths_for_input_path_set : 
  assumes "q \<in> nodes M"
  shows "set (paths_for_input M q xs) = {p . path M q p \<and> map t_input p = xs}"
using assms proof (induction xs arbitrary: q)
  case Nil
  then show ?case unfolding paths_for_input.simps by auto
next
  case (Cons x xs)

  have *: "{p . path M q p \<and> map t_input p = x#xs} = {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
  proof -
    have "\<And> p . p \<in> {p . path M q p \<and> map t_input p = x#xs} \<Longrightarrow> p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"    
      using Collect_cong Cons_eq_map_D[of x xs t_input] list.simps(9)[of t_input] by blast
    moreover have "\<And> p . p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}} \<Longrightarrow> p \<in> {p . path M q p \<and> map t_input p = x#xs}"
    proof -
      fix p :: "('a \<times> integer \<times> integer \<times> 'a) list"
      assume "p \<in> {t # p |t p. t \<in> set (wf_transitions M) \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p'. path M (t_target t) p' \<and> map t_input p' = xs}}"
      then obtain pp :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> 'a \<times> integer \<times> integer \<times> 'a" and pps :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
        f1: "p = pp p # pps p \<and> pp p \<in> set (wf_transitions M) \<and> t_source (pp p) = q \<and> t_input (pp p) = x \<and> pps p \<in> {ps. path M (t_target (pp p)) ps \<and> map t_input ps = xs}"
        by fastforce
      then have f2: "path M (t_target (pp p)) (pps p) \<and> map t_input (pps p) = xs"
        by force
      have f3: "path M (t_source (pp p)) (pp p # pps p)"
        using f1 by blast
      have "map t_input p = x # xs"
        using f2 f1 by (metis (no_types) list.simps(9)[of t_input])
      then show "p \<in> {ps. path M q ps \<and> map t_input ps = x # xs}"
        using f3 f1 by simp
    qed
    ultimately show ?thesis by blast
  qed
      
  have "set (paths_for_input M q (x#xs)) \<subseteq> {p . path M q p \<and> map t_input p = x#xs}"
  proof 
    fix p assume "p \<in> set (paths_for_input M q (x#xs))"
    then obtain y where "y \<in> set (outputs M)"
                    and "p \<in> set (concat (map 
                                    (\<lambda> t . (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs)))
                                    (filter (\<lambda> t . t_source t = q \<and> t_input t = x \<and> t_output t = y) (wf_transitions M))))"
      unfolding paths_for_input.simps by force
    then obtain t where "t \<in> h M" and "t_source t = q \<and> t_input t = x" and "t_output t = y"
                    and "p \<in> set (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs))"
      by force
    then obtain p' where "p = t#p'"
                     and "p' \<in> set (paths_for_input M (t_target t) xs)"
      by force

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> h M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      using \<open>p' \<in> set (paths_for_input M (t_target t) xs)\<close> by blast
  
    then have "(t#p') \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using \<open>t \<in> h M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by blast
    then show "p \<in> {p . path M q p \<and> map t_input p = x#xs}" 
      using \<open>p = t#p'\<close> * by blast
  qed
  moreover have "{p . path M q p \<and> map t_input p = x#xs} \<subseteq> set (paths_for_input M q (x#xs))"
  proof 
    fix p assume "p \<in> {p . path M q p \<and> map t_input p = x#xs}"
    then have "p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using * by blast
    then obtain t p' where "p = t#p'" and "t \<in> h M" and "t_source t = q \<and> t_input t = x" and "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      by blast

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> h M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> set (paths_for_input M (t_target t) xs)" 
      using \<open>p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}\<close> by blast
    moreover have "t_output t \<in> set (outputs M)" 
      using \<open>t \<in> h M\<close> by auto
    ultimately have "t#p' \<in> set (paths_for_input M q (x#xs))"
      unfolding paths_for_input.simps 
      using \<open>t \<in> h M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by force
    then show "p \<in> set (paths_for_input M q (x#xs))"
      using \<open>p = t#p'\<close> by blast
  qed
  
  ultimately show ?case ..
qed





fun paths_up_to_length_or_condition :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a Transition list \<Rightarrow> bool) \<Rightarrow> 'a Transition list \<Rightarrow> 'a Transition list list" where
  "paths_up_to_length_or_condition M q 0 f pref = (if f pref
    then [pref]
    else [])" | 
  "paths_up_to_length_or_condition M q (Suc k) f pref = (if f pref
    then [pref]
    else (concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))"




lemma paths_up_to_length_or_condition_path_set :
  assumes "path M q pref" 
  shows "set (paths_up_to_length_or_condition M q k f pref) = {(pref@p) | p . path M q (pref@p) \<and> length p \<le> k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
using assms proof (induction k arbitrary: q pref)
  case 0
  then show ?case 
      using 0 assms unfolding paths_up_to_length_or_condition.simps by force  
next
  case (Suc k)

  show ?case proof (cases "f pref")
    case True
    then show ?thesis using Suc.prems unfolding paths_up_to_length_or_condition.simps by force
  next
    case False
    then have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    also have "\<dots> = \<Union>{set (paths_up_to_length_or_condition M q k f (pref@[t])) | t . t \<in> h M \<and> t_source t = target pref q}"
      by force
    

    have *: "\<And> t . t \<in> h M \<Longrightarrow> t_source t = target pref q \<Longrightarrow> set (paths_up_to_length_or_condition M q k f (pref@[t])) 
                                                            =  {((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
    proof -
      fix t :: "'a \<times> integer \<times> integer \<times> 'a"
      assume a1: "t_source t = target pref q"
      assume "t \<in> set (wf_transitions M)"
      then have "path M (t_source t) [t]"
        by blast
      then show "set (paths_up_to_length_or_condition M q k f (pref @ [t])) = {(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))}"
        using a1 by (simp add: Suc.IH Suc.prems path_append)
    qed

    

    from False have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    moreover have "\<dots> = \<Union>{set (paths_up_to_length_or_condition M q k f (pref@[t])) | t . t \<in> h M \<and> t_source t = target pref q}"
      by force
    moreover have "\<dots> = \<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> h M \<and> t_source t = target pref q}"
      using * by (metis (no_types, lifting))
    ultimately have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = \<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> h M \<and> t_source t = target pref q}"
      by simp
    moreover have "\<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> h M \<and> t_source t = target pref q}
                  = {(pref@p) | p . path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
    proof -
      let ?UN = "{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> h M \<and> t_source t = target pref q}"
      let ?UN' = "{((pref @ [t]) @ p) |p t.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"

      have **: "\<And> p t . path M q ((pref @ [t]) @ p) \<Longrightarrow> t \<in> h M \<and> t_source t = target pref q"
        by auto
      
      have "\<Union>?UN = ?UN'"
      proof -
        have "\<Union>?UN \<subseteq> ?UN'"
        proof 
          fix p assume "p \<in> \<Union>?UN"
          then obtain P where "p \<in> P" and "P \<in> ?UN"
            by (meson UnionE)
            
          then obtain t where "t \<in> h M \<and> t_source t = target pref q"
                          and "P = {((pref @ [t]) @ p) |p .
                                     path M q ((pref @ [t]) @ p) \<and>
                                     length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
            by auto
          then obtain p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))"
            using \<open>p \<in> P\<close>
          proof -
            assume a1: "\<And>p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps. p = (pref @ [t]) @ ps \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))"
              using \<open>P = {(pref @ [t]) @ p |p. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> \<open>p \<in> P\<close> by force
            then show ?thesis
              using a1 by moura
          qed

          show "p \<in> ?UN'"
            using \<open>length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<close> \<open>p = (pref @ [t]) @ p'\<close> \<open>path M q ((pref @ [t]) @ p')\<close> by fastforce
        qed

        moreover have "?UN' \<subseteq> \<Union>?UN"
        proof 
          fix p assume "p \<in> ?UN'"
          then obtain t p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))"
          proof -
          assume a1: "\<And>t p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<rbrakk> \<Longrightarrow> thesis"
          have "\<exists>ps pa. p = (pref @ [pa]) @ ps \<and> path M q ((pref @ [pa]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [pa]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [pa]) @ psa))"
            using \<open>p \<in> {(pref @ [t]) @ p |p t. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> by force
            then show ?thesis
              using a1 by (metis (no_types))
          qed 
          then have "p \<in> {(pref @ [t]) @ p |p.
                      path M q ((pref @ [t]) @ p) \<and>
                      length p \<le> k \<and>
                      f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}" 
            by auto
          then show "p \<in> \<Union>?UN"
            using **[OF \<open> path M q ((pref @ [t]) @ p')\<close>]
          proof -
          have f1: "\<exists>ps. p = (pref @ [t]) @ ps \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))"
          using \<open>p \<in> {(pref @ [t]) @ p |p. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> by force
            have f2: "{(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))} \<in> {{(pref @ [p]) @ ps |ps. path M q ((pref @ [p]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [p]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [p]) @ psa))} | p. p \<in> set (wf_transitions M) \<and> t_source p = target pref q}"
              using \<open>t \<in> set (wf_transitions M) \<and> t_source t = target pref q\<close> by blast
            have "p \<in> {(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))}"
              using f1 by fastforce
            then show ?thesis
              using f2 by (meson Union_iff)
          qed 
        qed
        
        ultimately show ?thesis by blast
      qed



      let ?UN'' = "{((pref @ [t]) @ p) |p t.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))}"
      have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p')) \<Longrightarrow> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))"
        using False by (metis (no_types, hide_lams) append.assoc append_Nil append_Nil2 append_eq_Cons_conv) 
      moreover have "\<And> t p . (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p')) \<Longrightarrow> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))"
        using False by (metis (no_types, hide_lams) append.assoc append_Nil append_eq_Cons_conv)
      ultimately have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p')) = (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))"
        by auto
      then have "?UN' = ?UN''" by auto
      

      let ?P = "{(pref@p) | p . path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
      have "?UN'' = ?P"
      proof -
        have "?UN'' \<subseteq> ?P" 
        proof 
          fix p assume "p \<in> ?UN''"
          then obtain t p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
          proof -
            assume a1: "\<And>t p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps pa. p = (pref @ [pa]) @ ps \<and> path M q ((pref @ [pa]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [pa]) @ ps) \<and> (\<forall>psa psb. pa # ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f (pref @ psa))"
              using \<open>p \<in> {(pref @ [t]) @ p |p t. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. t # p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))}\<close> by blast
            then show ?thesis
              using a1 by (metis (no_types))
          qed 
          then have "path M q (pref @ ([t] @ p')) \<and>
                    length ([t] @ p') \<le> Suc k \<and> f (pref @ ([t] @ p')) \<and> (\<forall>p'' p'''. ([t] @ p') = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
            by auto
          moreover have "p = pref @ ([t] @ p')" using \<open>p = (pref @ [t]) @ p'\<close> by simp
          ultimately show "p \<in> ?P" by auto
        qed
        moreover have "?P \<subseteq> ?UN''"
        proof 
          fix p assume "p \<in> ?P"
          then obtain p' where "p = pref @ p'" 
                           and ***: "path M q (pref @ p')
                                       \<and> length p' \<le> Suc k
                                       \<and> f (pref @ p')
                                       \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
            by blast
          
          then have "p' \<noteq> []"
            using False by auto
          then obtain t p'' where "p' = [t] @ p''"
            by (metis append_Cons append_Nil list.exhaust) 
          then have "path M q ((pref @ [t]) @ p'') 
                      \<and> length p'' \<le> k
                      \<and> f ((pref @ [t]) @ p'') \<and> (\<forall>p''' p''''. t # p'' = p''' @ p'''' \<and> p'''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'''))"
            using *** by auto
          then have "(pref @ [t]) @ p'' \<in> ?UN''"
            by fastforce
          then show "p \<in> ?UN''"
            using \<open>p = pref @ p'\<close> \<open>p' = [t] @ p''\<close> by auto
        qed
        ultimately show ?thesis by blast
      qed
          
      show "\<Union>?UN = ?P"
        using \<open>\<Union>?UN = ?UN'\<close> \<open>?UN' = ?UN''\<close> \<open>?UN'' = ?P\<close> by auto
    qed
    ultimately show ?thesis by auto
  qed
qed
    

lemma paths_up_to_length_or_condition_path_set_nil :
  assumes "q \<in> nodes M" 
  shows "set (paths_up_to_length_or_condition M q k f []) = { p . path M q p \<and> length p \<le> k \<and> f p \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f p')}"
proof -
  have "path M q []"
    using assms by auto
  show ?thesis
    using paths_up_to_length_or_condition_path_set[OF \<open>path M q []\<close>] by auto
qed


end