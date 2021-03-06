theory TODO
imports State_Separator
begin

section \<open>Proof Notes\<close>

(*
- prove algorithm not for all sets of pairwise r-d states, but instead for some
  set PRD of sets of pairwise r-d states that is assumed to contain the singleton
  sets for each state of the model FSM
  \<rightarrow> this avoids having to prove that a state separator exists if states are r-d



*)



section \<open>Unfinished Proofs of Interest\<close>

subsection \<open>Generating a State Separator from R-Distinguishable States of an Observable FSM\<close>


fun calculate_separator' :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) + 'a) set \<Rightarrow> ((('a \<times> 'a) + 'a) Transition list) \<Rightarrow> ((('a \<times> 'a) + 'a) Transition list) option" where
  "calculate_separator' C 0 Q T = None" |
  "calculate_separator' C (Suc k) Q T = 
    (case find (\<lambda> qx . (fst qx \<notin> Q) \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t) \<in> Q)) (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
      of Some qx \<Rightarrow> (if fst qx = initial C 
        then Some (T@(filter (\<lambda>t . t_source t = fst qx \<and> t_input t = snd qx) (wf_transitions C)))
        else calculate_separator' C k (insert (fst qx) Q) (T@(filter (\<lambda>t . t_source t = fst qx \<and> t_input t = snd qx) (wf_transitions C)))) | 
         None \<Rightarrow> None)"

(* Algorithm with some sort of "logging" *)
fun calculate_separator'' :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) + 'a) set \<Rightarrow> ((('a \<times> 'a) + 'a) Transition list) \<Rightarrow> ((('a \<times> 'a) + 'a) set \<times> ((('a \<times> 'a) + 'a) Transition list)) list \<Rightarrow> ((('a \<times> 'a) + 'a) set \<times> ((('a \<times> 'a) + 'a) Transition list)) list \<times> bool" where
  "calculate_separator'' C 0 Q T prev = (prev,False)" |
  "calculate_separator'' C (Suc k) Q T prev = 
    (case find (\<lambda> qx . (fst qx \<notin> Q) \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t) \<in> Q)) (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
      of Some qx \<Rightarrow> (if fst qx = initial C 
        then (prev@[(insert (fst qx) Q, (T@(filter (\<lambda>t . t_source t = fst qx \<and> t_input t = snd qx) (wf_transitions C))))],True)
        else calculate_separator'' C k (insert (fst qx) Q) (T@(filter (\<lambda>t . t_source t = fst qx \<and> t_input t = snd qx) (wf_transitions C))) (prev@[(insert (fst qx) Q, (T@(filter (\<lambda>t . t_source t = fst qx \<and> t_input t = snd qx) (wf_transitions C))))])) | 
         None \<Rightarrow> (prev,False))"

(* Algorithm for calculating separators based on the rought description given by Petrenko *)
fun calculate_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ((('a \<times> 'a) + 'a), 'b) FSM_scheme option" where
  "calculate_separator M q1 q2 = (case calculate_separator' (canonical_separator M q1 q2) (size (canonical_separator M q1 q2)) {Inr q1, Inr q2} [] of
    Some T \<Rightarrow> Some \<lparr> initial = Inl (q1,q2), inputs = inputs (canonical_separator M q1 q2), outputs = outputs (canonical_separator M q1 q2), transitions = T, \<dots> = FSM.more M\<rparr> |
    None \<Rightarrow> None)" 






fun calculate_separator_states :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> Input) set \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> Input) set option" where
  "calculate_separator_states C 0 Q = None" |
  "calculate_separator_states C (Suc k) Q = 
    (case find 
            (\<lambda> qx . (\<forall> qx' \<in> Q . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> Q . fst qx' = (t_target t)))) 
            (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
      of Some qx \<Rightarrow> (if fst qx = initial C 
                        then Some (insert qx Q)
                        else calculate_separator_states C k (insert qx Q)) | 
         None \<Rightarrow> None)"

(* Variation that calculates the transition relation only after selecting states and corresponding inputs *)
fun calculate_separator_from_states :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ((('a \<times> 'a) + 'a), 'b) FSM_scheme option" where
(* TODO: replace dummy inputs for Inr-values *)
  "calculate_separator_from_states M q1 q2 = (let C = (canonical_separator M q1 q2) in 
    (case calculate_separator_states C (size C) {(Inr q1,0), (Inr q2,0)} of 
      Some Q \<Rightarrow> Some \<lparr> initial = Inl (q1,q2), inputs = inputs C, outputs = outputs C, transitions = filter (\<lambda> t . (t_source t,t_input t) \<in> Q) (wf_transitions C), \<dots> = FSM.more M\<rparr> |
    None \<Rightarrow> None))" 


value "calculate_separator_from_states M_ex_9 0 3"
value "is_state_separator_from_canonical_separator (canonical_separator M_ex_9 0 3) 0 3 (the (calculate_separator_from_states M_ex_9 0 3))"

value "calculate_separator M_ex_9 0 3"
value "is_state_separator_from_canonical_separator (canonical_separator M_ex_9 0 3) 0 3 (the (calculate_separator M_ex_9 0 3))"
value "calculate_separator M_ex_H 1 3"
value "calculate_separator'' (canonical_separator M_ex_9 0 3) (size (canonical_separator M_ex_9 0 3)) {Inr 0, Inr 3} [] []"





subsection \<open>Merging Single-Input FSMs\<close>


definition merge_sub_intersection_transitions :: "'a Transition list \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> 'a Transition list" where
  "merge_sub_intersection_transitions ts M2 = ts @ (filter (\<lambda> t2 . \<not> (\<exists> t1 \<in> set ts . t_source t1 = t_source t2)) (wf_transitions M2))"


abbreviation(input) "merge_FSMs M S \<equiv> (\<lparr> initial = initial M, 
                                          inputs = inputs M, 
                                          outputs = outputs M, 
                                          transitions = (wf_transitions M) @ (filter (\<lambda> t2 . (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)) (wf_transitions S)),
                                          \<dots> = more M \<rparr>)"

fun merge_sub_intersections :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme list \<Rightarrow> ('a,'b) FSM_scheme" where
  "merge_sub_intersections M [] = M" |
  "merge_sub_intersections M (S#SS) = merge_sub_intersections (merge_FSMs M S) SS"

value "merge_sub_intersections 
          \<lparr> initial = 0::nat, inputs = [0,1], outputs = [0,1], transitions = [(0,0,0,1),(0,0,1,2)] \<rparr>
          [\<lparr> initial = 1,
             inputs = [0,1],
             outputs = [0,1],
             transitions = [(1,1,0,10),(1,1,1,11)]\<rparr>,
           \<lparr> initial = 2,
             inputs = [0,1],
             outputs = [0,1],
             transitions = [(2,0,0,20),(2,0,1,1),(1,0,0,21)]\<rparr>]"





lemma merge_FSMs_paths_initial :
  assumes "path M (initial M) p"
  shows   "path (merge_FSMs M S) (initial M) p"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case
    by (metis (no_types, lifting) nil nodes.initial select_convs(1)) 
next
  case (snoc t p)

  have "path M (initial M) p" and "t \<in> h M" and "t_source t = target p (initial M)"
    using snoc.prems by auto
  
  have "path (merge_FSMs M S) (initial M) p"
    using snoc.IH[OF \<open>path M (initial M) p\<close>] by assumption

  then have "target p (initial M) \<in> nodes (merge_FSMs M S)" 
    using path_target_is_node by (metis (no_types, lifting)) 
  then have "t \<in> h (merge_FSMs M S)"
    using \<open>t_source t = target p (initial M)\<close> \<open>t \<in> h M\<close> by auto
  then show ?case 
    using \<open>path (merge_FSMs M S) (initial M) p\<close>
    by (meson path_equivalence_by_h snoc.prems) 
qed

lemma merge_FSMs_nodes_left : "nodes M \<subseteq> nodes (merge_FSMs M S)"
proof 
  fix q assume "q \<in> nodes M"
  then obtain p where "path M (initial M) p" and "target p (initial M) = q"
    using path_to_node by metis
  have "path (merge_FSMs M S) (initial (merge_FSMs M S)) p"
    using merge_FSMs_paths_initial[OF \<open>path M (initial M) p\<close>] by auto
  then show "q \<in> nodes (merge_FSMs M S)"
    using path_target_is_node \<open>target p (initial M) = q\<close>
    by (metis (no_types, lifting) select_convs(1)) 
qed 



lemma merge_FSMs_h :
  assumes "inputs M = inputs S"
      and "outputs M = outputs S"
  shows "h (merge_FSMs M S) = (h M) \<union> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
proof -
  have "h (merge_FSMs M S) \<subseteq> (h M) \<union> {t2 \<in> h S . \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}" by auto
  moreover have "\<And> t . t \<notin> h M \<Longrightarrow> \<not>(t_source t = initial S \<or> t_source t \<notin> nodes M) \<Longrightarrow> t \<notin> h (merge_FSMs M S)" by auto
  ultimately have "h (merge_FSMs M S) \<subseteq> (h M) \<union> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}" by blast
    

  moreover have "h M \<subseteq> h (merge_FSMs M S)"
  proof 
    fix t assume "t \<in> h M"
    then have "t_source t \<in> nodes M" by auto
    then have "t_source t \<in> nodes (merge_FSMs M S)"
      using merge_FSMs_nodes_left[of M S] by blast
    then show "t \<in> h (merge_FSMs M S)"
      using \<open>t \<in> h M\<close> by auto
  qed

  moreover have "{t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)} \<subseteq> h (merge_FSMs M S)"
  proof 
    fix t assume "t \<in> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
    then have "t \<in> h S" and "(t_source t = initial S \<or> t_source t \<notin> nodes M)" and "\<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t)" and "(t_source t \<in> nodes (merge_FSMs M S))"
      by blast+

    

    then have "t \<in> set (transitions (merge_FSMs M S))" by force
    moreover have "t_input t \<in> set (inputs (merge_FSMs M S))"
      using assms(1) \<open>t \<in> h S\<close> by auto
    moreover have "t_output t \<in> set (outputs (merge_FSMs M S))"
      using assms(2) \<open>t \<in> h S\<close> by auto
    ultimately show "t \<in> h (merge_FSMs M S)"
      using \<open>t_source t \<in> nodes (merge_FSMs M S)\<close> by blast
  qed
  
  ultimately show ?thesis by blast
qed




 

lemma merge_FSMs_single_input :
  assumes "single_input M"
  and     "single_input S"
shows "single_input (merge_FSMs M S)"
  using assms unfolding single_input.simps
  by (metis (mono_tags, lifting) filter_set list_concat_non_elem member_filter select_convs(4) wf_transition_simp) 

lemma merge_FSMs_retains_outputs_for_states_and_inputs :
  assumes "retains_outputs_for_states_and_inputs PM M"
      and "retains_outputs_for_states_and_inputs PM S"
  assumes "inputs M = inputs S"
      and "outputs M = outputs S"  
shows "retains_outputs_for_states_and_inputs PM (merge_FSMs M S)"
proof -
  have "\<And> t tPM . t \<in> h (merge_FSMs M S) \<Longrightarrow> tPM \<in> h PM \<Longrightarrow> t_source t = t_source tPM \<Longrightarrow> t_input t = t_input tPM \<Longrightarrow> tPM \<in> h (merge_FSMs M S)"
  proof -
    fix t tPM assume "t \<in> h (merge_FSMs M S)" 
                 and p1: "tPM \<in> h PM" 
                 and p2: "t_source t = t_source tPM" 
                 and p3: "t_input t = t_input tPM"
    
    

    show "tPM \<in> h (merge_FSMs M S)"
    proof (cases "t \<in> h M")
      case True
      then have "tPM \<in> h M"
        using p1 p2 p3 assms(1) unfolding retains_outputs_for_states_and_inputs_def by blast
      then show ?thesis
        using merge_FSMs_h[OF assms(3,4)] by blast
    next
      case False
      moreover have "t \<in> (h M) \<union> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
        using \<open>t \<in> h (merge_FSMs M S)\<close> merge_FSMs_h[OF assms(3,4)] by blast
      ultimately have "t \<in> h S"
                  and "t_source t \<in> nodes (merge_FSMs M S)"
                  and "t_source t = initial S \<or> t_source t \<notin> nodes M"
                  and "\<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t)"
        by blast+
      then have "tPM \<in> h S"
        using p1 p2 p3 assms(2) unfolding retains_outputs_for_states_and_inputs_def by blast
      moreover have "t_source tPM \<in> nodes (merge_FSMs M S)"
        using p2 \<open>t_source t \<in> nodes (merge_FSMs M S)\<close> by auto
      moreover have "\<not> (\<exists> t1 \<in> h M . t_source t1 = t_source tPM)" 
        using p2 \<open>\<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t)\<close> by auto
      moreover have "t_source tPM = initial S \<or> t_source tPM \<notin> nodes M"
        using p2 \<open>t_source t = initial S \<or> t_source t \<notin> nodes M\<close> by auto
      ultimately show ?thesis 
        using merge_FSMs_h[OF assms(3,4)] by blast
    qed
  qed
    
  then show ?thesis 
    unfolding retains_outputs_for_states_and_inputs_def by blast
qed



lemma merge_FSMs_nodes :
  assumes "inputs M = inputs S"
  and     "outputs M = outputs S"
shows "nodes (merge_FSMs M S) \<subseteq> nodes M \<union> nodes S"
proof -
  have "nodes (merge_FSMs M S) = insert (initial M) {t_target t | t . t \<in> h (merge_FSMs M S)}"
    using h_nodes[of "merge_FSMs M S"] by (metis select_convs(1)) 
  moreover have "nodes M = insert (initial M) {t_target t | t . t \<in> h M}"
    using h_nodes[of M] by auto
  moreover have "nodes S = insert (initial S) {t_target t | t . t \<in> h S}"
    using h_nodes[of S] by auto
  ultimately show ?thesis 
    using merge_FSMs_h[OF assms(1,2)]
    by blast 
qed



(* Proof sketch for strengthened assumptions on acyclicity and construction:

  - assume MS acyclic
  - then obtain cycle
  - must contain nodes from M and S as M and S are acyclic on their own
  - must contain transition from node of M to node of S
  - only possible from (initial S)
  - (initial S) can only be reached by the designated transition from (initial M)
  - there must exist an incoming transition for (initial M)
  - contradiction
*)

lemma merge_FSMs_acyclic :
  assumes "\<exists> t \<in> h M . t_source t = initial M \<and> t_target t = initial S \<and> (\<forall> t' \<in> h M . t_target t' = initial S \<longrightarrow> t' = t)"
  and "initial M \<notin> nodes S"
  and "acyclic M"
  and "acyclic S"
  and "inputs M = inputs S"
  and "outputs M = outputs S"  
shows "acyclic (merge_FSMs M S)" (is "acyclic ?MS")
proof (rule ccontr)
  assume "\<not> acyclic ?MS"
  then obtain q p where "path ?MS q p" and "p \<noteq> []" and "target p q = q"
    using cyclic_cycle by blast

  have "\<exists> tS \<in> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)} - (h M) . tS \<in> set p"
  proof (rule ccontr)
    assume "\<not> (\<exists>tS\<in> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)} - (h M). tS \<in> set p)"
    moreover have "set p \<subseteq> h ?MS"
      using \<open>path ?MS q p\<close> by (meson path_h) 
    ultimately have "set p \<subseteq> h M"
      using merge_FSMs_h[OF assms(5,6)] by blast
    
    have "path M q p"
      using transitions_subset_path[OF \<open>set p \<subseteq> h M\<close> \<open>p \<noteq> []\<close> \<open>path ?MS q p\<close>] by assumption
    then have "\<not> acyclic M"
      using \<open>p \<noteq> []\<close> \<open>target p q = q\<close> cyclic_cycle_rev by metis
    then show "False"
      using assms(3) by blast
  qed


  have "\<exists> tM \<in> (h M) - {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)} . tM \<in> set p"
  proof (rule ccontr)
    assume "\<not> (\<exists>tM\<in> (h M) - {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}. tM \<in> set p)"
    moreover have "set p \<subseteq> h ?MS"
      using \<open>path ?MS q p\<close> by (meson path_h) 
    ultimately have "set p \<subseteq> h S"
      using merge_FSMs_h[OF assms(5,6)] by blast
    
    have "path S q p"
      using transitions_subset_path[OF \<open>set p \<subseteq> h S\<close> \<open>p \<noteq> []\<close> \<open>path ?MS q p\<close>] by assumption
    then have "\<not> acyclic S"
      using \<open>p \<noteq> []\<close> \<open>target p q = q\<close> cyclic_cycle_rev by metis
    then show "False"
      using assms(4) by blast
  qed

  
  have "\<exists> t \<in> set p . t_source t = initial S"
  proof (rule ccontr)
    assume "\<not> (\<exists>t\<in>set p. t_source t = initial S)"
    then have "\<And> t . t \<in> set p \<Longrightarrow> t_source t \<noteq> initial S" 
      by blast
    then have "\<And> t . t \<in> set p \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_target t \<in> nodes M"
      using merge_FSMs_h[OF assms(5,6)] path_h[OF \<open>path ?MS q p\<close>] by blast

    have "\<exists> t \<in> set p . t_source t \<in> nodes M"
      using \<open>\<exists> tS \<in> (h M) - {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}. tS \<in> set p\<close> by blast
    
    have "\<And> t . t \<in> set p \<Longrightarrow> t_source t \<in> nodes M"
      using cyclic_path_transition_source_property(1)[OF \<open>\<exists> t \<in> set p . t_source t \<in> nodes M\<close> _ \<open>path ?MS q p\<close> \<open>target p q = q\<close>]
            \<open>\<And> t . t \<in> set p \<Longrightarrow> t_source t \<in> nodes M \<Longrightarrow> t_target t \<in> nodes M\<close> 
      by metis
    then have "\<And> t . t \<in> set p \<Longrightarrow> t_source t \<in> nodes M \<and> t_source t \<noteq> initial S"
      using \<open>\<not> (\<exists>t\<in>set p. t_source t = initial S)\<close> by blast
    moreover have "\<exists> t \<in> set p . t_source t = initial S \<or> t_source t \<notin> nodes M"
      using \<open>\<exists> tS \<in> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)} - (h M) . tS \<in> set p\<close> by blast
    ultimately show "False"
      by blast
  qed

  then have "\<exists> t \<in> set p . t_target t = initial S"
    using cycle_incoming_transition_ex[OF \<open>path ?MS q p\<close> \<open>p \<noteq> []\<close> \<open>target p q = q\<close>] by auto
  then have "\<exists> t \<in> set p . t \<in> h ?MS \<and> t_target t = initial S"
    using path_h[OF \<open>path ?MS q p\<close>] by blast
  then have "\<exists> t \<in> set p . t \<in> h M \<and> t_target t = initial S"
    using acyclic_initial[OF assms(4)] merge_FSMs_h[OF assms(5,6)] by blast
  
  moreover obtain tM where "tM \<in> h M" and "t_source tM = initial M" and "t_target tM = initial S" and "(\<forall> t' \<in> h M . t_target t' = initial S \<longrightarrow> t' = tM)"
    using assms(1) by blast

  ultimately have "tM \<in> set p" 
    by blast
  then have "\<exists> t \<in> set p . t_target t = initial M"
    using cycle_incoming_transition_ex[OF \<open>path ?MS q p\<close> \<open>p \<noteq> []\<close> \<open>target p q = q\<close>, of tM] \<open>t_source tM = initial M\<close> by auto
  then obtain t where "t \<in> set p" and "t_target t = initial M"
    by blast
  then consider (a) "t \<in> h M" | (b) "t \<in> h S" 
    using path_h[OF \<open>path ?MS q p\<close>] merge_FSMs_h[OF assms(5,6)] by blast
  then show "False" proof cases
    case a
    then show "False" 
      using acyclic_initial[OF assms(3)] \<open>t_target t = initial M\<close> by blast
  next
    case b
    then show ?thesis 
      using \<open>t_target t = initial M\<close> wf_transition_target[OF b] assms(2) by auto
  qed
qed



lemma merge_FSMs_submachines :
  assumes "is_submachine M (product Q1 Q2)"
  assumes "is_submachine S (from_FSM (product Q1 Q2) (initial S))"
  assumes "\<exists> t \<in> h M . t_source t = initial M \<and> t_target t = initial S \<and> (\<forall> t' \<in> h M . t_target t' = initial S \<longrightarrow> t' = t)"
  and "initial M \<notin> nodes S"
  and "acyclic M"
  and "acyclic S"  
shows "is_submachine (merge_FSMs M S) (product Q1 Q2)" (is "is_submachine ?MS ?PQ")
proof -
  have "inputs M = inputs S"
    using assms(1,2) unfolding is_submachine.simps from_FSM.simps
    by (metis select_convs(2)) 

  have "outputs M = outputs S"
    using assms(1,2) unfolding is_submachine.simps from_FSM.simps
    by (metis select_convs(3))

  have "initial ?MS = initial ?PQ" 
    using assms(1) unfolding is_submachine.simps
    by (metis select_convs(1)) 
  moreover have "inputs ?MS = inputs ?PQ"
    using assms(1) unfolding is_submachine.simps
    by (metis select_convs(2)) 
  moreover have "outputs ?MS = outputs ?PQ"
    using assms(1) unfolding is_submachine.simps
    by (metis select_convs(3)) 
  moreover have "h ?MS \<subseteq> h ?PQ" 
  proof -
    have "h ?MS \<subseteq> h M \<union> h S"
      using merge_FSMs_h[OF \<open>inputs M = inputs S\<close> \<open>outputs M = outputs S\<close>] by blast
    moreover have "h M \<subseteq> h ?PQ"
      using submachine_h[OF assms(1)] by assumption
    moreover have "h S \<subseteq> h ?PQ"
    proof -
      have "initial S \<in> nodes M"
        using assms(3) wf_transition_target by metis
      then have "initial S \<in> nodes ?PQ"
        using submachine_nodes[OF assms(1)] by blast
      then have "h (from_FSM ?PQ (initial S)) \<subseteq> h ?PQ"
        using from_FSM_h by metis
      moreover have "h S \<subseteq> h (from_FSM ?PQ (initial S))"
        using submachine_h[OF assms(2)] by assumption
      ultimately show ?thesis by blast
    qed
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis
    unfolding is_submachine.simps by presburger
qed
  




fun calculate_separator_states_list :: "('a \<times> 'a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a) \<times> Input) list \<Rightarrow> ((('a \<times> 'a) \<times> Input) list \<times> (('a \<times> 'a) \<times> Input) list) option" where
  "calculate_separator_states_list C 0 Q = None" |
  "calculate_separator_states_list C (Suc k) Q = 
    (case find 
            (\<lambda> qx . (\<forall> qx' \<in> set Q . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set Q . fst qx' = (t_target t)))) 
            (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
      of Some qx \<Rightarrow> (if fst qx = initial C 
                        then Some (filter (\<lambda>qx' . \<not>(\<exists> t \<in> h C . t_source t = fst qx' \<and> t_input t = snd qx')) (Q@[qx]), filter (\<lambda>qx' . \<exists> t \<in> h C . t_source t = fst qx' \<and> t_input t = snd qx') (Q@[qx]))
                        else calculate_separator_states_list C k (Q@[qx])) | 
         None \<Rightarrow> None)"

(* Variation that calculates the transition relation only after selecting states and corresponding inputs *)
fun calculate_separator_merge :: "(('a \<times> 'a), 'b) FSM_scheme \<Rightarrow> 'a \<times> 'a \<Rightarrow> Input \<Rightarrow> (('a \<times> 'a) \<Rightarrow> ((('a \<times> 'a), 'b) FSM_scheme option)) \<Rightarrow> (('a \<times> 'a), 'b) FSM_scheme" where
  "calculate_separator_merge M qq x f = 
    foldl 
      merge_FSMs 
      \<lparr> initial = qq, inputs = inputs M, outputs = outputs M, transitions = filter (\<lambda>t . t_source t = qq \<and> t_input t = x) (wf_transitions M), \<dots> = more M \<rparr>
      (map 
        (\<lambda> t . (case f (t_target t) of
                    Some S \<Rightarrow> S |
                    None \<Rightarrow> \<lparr> initial = t_target t, inputs = inputs M, outputs = outputs M, transitions = [], \<dots> = more M \<rparr>))
        (filter
          (\<lambda>t . t_source t = qq \<and> t_input t = x) (wf_transitions M)))" 

fun calculate_separator_merge_list :: "(('a \<times> 'a), 'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) \<times> Input) list \<Rightarrow> (('a \<times> 'a) \<Rightarrow> ((('a \<times> 'a), 'b) FSM_scheme option))" where
  "calculate_separator_merge_list M [] = (\<lambda> qq . None)" |
  "calculate_separator_merge_list M (qqx#qqxs) = (let f = calculate_separator_merge_list M qqxs in
    f(fst qqx := Some (calculate_separator_merge M (fst qqx) (snd qqx) f)))"

fun calculate_separator_merge_alg :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a), 'b) FSM_scheme option" where
  "calculate_separator_merge_alg M q1 q2 = (let PR = (product (from_FSM M q1) (from_FSM M q2)) in 
    (case (calculate_separator_states_list PR (size PR) []) of
      Some qqxs \<Rightarrow> (calculate_separator_merge_list PR (fst qqxs @ snd qqxs)) (q1,q2) |
      None \<Rightarrow> None))"

fun calculate_separator_merge_alg_full :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ((('a \<times> 'a) + 'a), 'b) FSM_scheme option" where
  "calculate_separator_merge_alg_full M q1 q2 = (let PR = (product (from_FSM M q1) (from_FSM M q2)) in 
    (case (calculate_separator_states_list PR (size PR) []) of
      Some qqxs \<Rightarrow> (let f = (calculate_separator_merge_list PR (fst qqxs @ snd qqxs)) in
        (case f (q1,q2) of
          Some S \<Rightarrow> Some \<lparr> initial = Inl (q1,q2), 
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = (map shift_Inl (transitions S)) 
                                            @ (concat (map (\<lambda> qqx . map (\<lambda>t . (Inl (fst qqx), t_input t, t_output t, Inr q1)) (filter (\<lambda>t. t_source t = fst (fst qqx) \<and> t_input t = snd qqx) (wf_transitions M))) (fst qqxs))) 
                                            @ (concat (map (\<lambda> qqx . map (\<lambda>t . (Inl (fst qqx), t_input t, t_output t, Inr q2)) (filter (\<lambda>t. t_source t = snd (fst qqx) \<and> t_input t = snd qqx) (wf_transitions M))) (fst qqxs))), 
                            \<dots> = more M\<rparr> |
          None \<Rightarrow> None)) |
      None \<Rightarrow> None))"


value "(let PR = (product (from_FSM M_ex_9 0) (from_FSM M_ex_9 3)) in (calculate_separator_states_list PR (size PR) []))"
value "calculate_separator_merge_alg M_ex_9 1 3"
value "calculate_separator_merge_alg_full M_ex_9 0 3"
value "h (the (calculate_separator_merge_alg_full M_ex_9 0 3))"




subsection \<open>R-Distinguishability Implies Existence of State Separators\<close>

(*
(* Note: requires observability, a (per definition) states in non-observable FSMs may still be r-d, but this might require different inputs *)
lemma state_separator_from_r_distinguishable_k :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
  assumes "observable M"
  assumes "q1 \<in> nodes M" and "q2 \<in> nodes M"
  shows "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
proof (rule ccontr) 
  let ?CSep = "canonical_separator M q1 q2"

  let ?fk = "\<lambda> q1 q2 . case r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) of
              Some (k,x) \<Rightarrow> Some x |
              None \<Rightarrow> None"
  let ?tsInl_pairs = "(filter (\<lambda> tt . t_input (fst tt) = t_input (snd tt) \<and> t_output (fst tt) = t_output (snd tt) \<and> ?fk (t_source (fst tt)) (t_source (snd tt)) = Some (t_input (fst tt)))
                  (concat (map (\<lambda>t1 . map (\<lambda> t2 . (t1,t2)) (transitions M)) (transitions M))))"    
  let ?tsInl = "map shift_Inl (map (\<lambda> tt . ((t_source (fst tt), t_source (snd tt)),t_input (fst tt),t_output (fst tt), (t_target (fst tt), t_target (snd tt)))) ?tsInl_pairs)"

  let ?tsLeft = "(map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 )) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> (r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some (0,t_input (snd qqt)))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))))"
  let ?tsRight = "(map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2 )) (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> (r_distinguishable_k_least M q1 q2 (size (product (from_FSM M q1) (from_FSM M q2))) = Some (0,t_input (snd qqt)))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))))"

  let ?S = "?CSep \<lparr> transitions := filter (\<lambda> t . t \<in> set (?tsInl @ ?tsLeft @ ?tsRight)) (transitions ?CSep) \<rparr>"

  have tsInl_subset: "set ?tsInl \<subseteq> set (shifted_transitions M q1 q2)" unfolding shifted_transitions_def
    sorry
  have tsLeft_subset: "set ?tsLeft \<subseteq> set (distinguishing_transitions_left M q1 q2)"
    sorry
  have tsRight_subset: "set ?tsRight \<subseteq> set (distinguishing_transitions_right M q1 q2)"
    sorry

  have "set (?tsInl @ ?tsLeft @ ?tsRight) \<subseteq> set (shifted_transitions M q1 q2
          @ distinguishing_transitions_left M q1 q2
          @ distinguishing_transitions_right M q1 q2)"
    using list_append_subset3[OF tsInl_subset tsLeft_subset tsRight_subset] by assumption 
  then have "set (?tsInl @ ?tsLeft @ ?tsRight) \<subseteq> set (transitions ?CSep)"
    unfolding canonical_separator_def
    by (metis select_convs(4)) 
  have "set (?tsInl @ ?tsLeft @ ?tsRight) = set (filter (\<lambda> t . t \<in> set (?tsInl @ ?tsLeft @ ?tsRight)) (transitions ?CSep))" 
    using subset_filter[OF \<open>set (?tsInl @ ?tsLeft @ ?tsRight) \<subseteq> set (transitions ?CSep)\<close>] by assumption
  then have "is_submachine ?S ?CSep" 
    using transition_filter_submachine by metis

  have "deadlock_state ?S (Inr q1)"
    sorry
  have "deadlock_state ?S (Inr q2)"
    sorry

  have "\<And> p t q1' q2'  . path ?S (Inl (q1',q2')) (p@[t]) \<Longrightarrow> t_target t = Inr q1 \<or> t_target t = Inr q2 \<Longrightarrow> \<exists> p' . is_least_r_d_k_path M q1' q2' p' \<and> map fst p = (map Inl (map fst p'))"
  proof - 
    fix p t q1' q2' assume "path ?S (Inl (q1',q2')) (p@[t])" and "t_target t = Inr q1 \<or> t_target t = Inr q2"
    then show "\<exists> p' . is_least_r_d_k_path M q1' q2' p' \<and> map fst p = (map Inl (map fst p'))"
    proof (induction p arbitrary: q1' q2' rule: rev_induct)
      case Nil
      then show ?case sorry
    next
      case (snoc x xs)
      then show ?case sorry
    qed

*)


end