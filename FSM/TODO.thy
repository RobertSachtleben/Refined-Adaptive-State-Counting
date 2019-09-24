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

 

lemma list_append_subset3 : "set xs1 \<subseteq> set ys1 \<Longrightarrow> set xs2 \<subseteq> set ys2 \<Longrightarrow> set xs3 \<subseteq> set ys3 \<Longrightarrow> set (xs1@xs2@xs3) \<subseteq> set(ys1@ys2@ys3)" by auto
lemma subset_filter : "set xs \<subseteq> set ys \<Longrightarrow> set xs = set (filter (\<lambda> x . x \<in> set xs) ys)"
  by auto


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
  "calculate_separator_from_states M q1 q2 = (let C = (canonical_separator M q1 q2) in 
    (case calculate_separator_states C (size C) {(Inr q1,0), (Inr q2,0)} of (* TODO: replace dummy inputs for Inr-values *)
      Some Q \<Rightarrow> Some \<lparr> initial = Inl (q1,q2), inputs = inputs C, outputs = outputs C, transitions = filter (\<lambda> t . (t_source t,t_input t) \<in> Q) (wf_transitions C), \<dots> = FSM.more M\<rparr> |
    None \<Rightarrow> None))" 


value "calculate_separator_from_states M_ex_9 0 3"
value "is_state_separator_from_canonical_separator (canonical_separator M_ex_9 0 3) 0 3 (the (calculate_separator_from_states M_ex_9 0 3))"

value "calculate_separator M_ex_9 0 3"
value "is_state_separator_from_canonical_separator (canonical_separator M_ex_9 0 3) 0 3 (the (calculate_separator M_ex_9 0 3))"
value "calculate_separator M_ex_H 1 3"
value "calculate_separator'' (canonical_separator M_ex_9 0 3) (size (canonical_separator M_ex_9 0 3)) {Inr 0, Inr 3} [] []"

(* TODO: move *)
lemma submachine_transitive :
  assumes "is_submachine S M"
  and     "is_submachine S' S"
shows "is_submachine S' M"
  using assms unfolding is_submachine.simps by force





(* merging single-input FSMs *)
definition merge_sub_intersection_transitions :: "'a Transition list \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> 'a Transition list" where
  "merge_sub_intersection_transitions ts M2 = ts @ (filter (\<lambda> t2 . \<not> (\<exists> t1 \<in> set ts . t_source t1 = t_source t2)) (wf_transitions M2))"

(*
fun merge_sub_intersections :: "Input list \<Rightarrow> Output list \<Rightarrow> 'a \<Rightarrow> 'a Transition list \<Rightarrow> ('a,'b) FSM_scheme list \<Rightarrow> ('a,'b) FSM_scheme" where
  "merge_sub_intersections ins outs q qts [] = undefined " |
  "merge_sub_intersections ins outs q qts [M] = \<lparr> initial = q, inputs = ins, outputs = outs, transitions = merge_sub_intersection_transitions qts M, \<dots> = more M \<rparr>" |
  "merge_sub_intersections ins outs q qts (M1#M2#MS) = merge_sub_intersections ins outs q (merge_sub_intersection_transitions qts M1) (M2#MS)"  

value "merge_sub_intersections 
          [0,1]
          [0,1]
          (0::nat)
          [(0,0,0,1),(0,0,1,2)]
          [\<lparr> initial = 1,
             inputs = [0,1],
             outputs = [0,1],
             transitions = [(1,1,0,10),(1,1,1,11)]\<rparr>,
           \<lparr> initial = 2,
             inputs = [0,1],
             outputs = [0,1],
             transitions = [(2,0,0,20),(2,0,1,1),(1,0,0,21)]\<rparr>]"
*)


abbreviation "merge_FSMs M S \<equiv> (\<lparr> initial = initial M, 
                                          inputs = inputs M, 
                                          outputs = outputs M, 
                                          (*transitions = (wf_transitions M) @ (filter (\<lambda> t2 . \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)) (wf_transitions S)), *)
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




(* possible approach to showing that a separator can be constructed from sub-separators *)
definition retains_outputs_for_states_and_inputs :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> bool" where
  "retains_outputs_for_states_and_inputs M S = (\<forall> tS \<in> h S . \<forall> tM \<in> h M . (t_source tS = t_source tM \<and> t_input tS = t_input tM) \<longrightarrow> tM \<in> h S)"

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



(* TODO: move *)
lemma non_distinct_repetition_indices :
  assumes "\<not> distinct xs"
  shows "\<exists> i j . i < j \<and> j < length xs \<and> xs ! i = xs ! j"
  by (metis assms distinct_conv_nth le_neq_implies_less not_le)

lemma list_contains_last_take :
  assumes "x \<in> set xs"
  shows "\<exists> i . 0 < i \<and> i \<le> length xs \<and> last (take i xs) = x"
  by (metis Suc_leI assms hd_drop_conv_nth in_set_conv_nth last_snoc take_hd_drop zero_less_Suc)
  
lemma take_last_index :
  assumes "i < length xs"
  shows "last (take (Suc i) xs) = xs ! i"
  by (simp add: assms take_Suc_conv_app_nth)


(* TODO: move *)
lemma acyclic_cycle :
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

lemma x :
  assumes "\<not> (\<exists> t \<in> h M . t_target t = initial M)"
  and "\<exists> t \<in> h M . t_source t = initial M \<and> t_target t = initial S \<and> (\<forall> t' \<in> h M . t_target t = initial S \<longrightarrow> t' = t)"
  and 
shows "False"

end (*

lemma merge_FSMs_path_right :
  assumes "path (merge_FSMs M S) q p"
  and     "q = initial S \<or> q \<notin> nodes M"
  and     "deadlock_state M (initial S)"
  assumes "inputs M = inputs S"
  and     "outputs M = outputs S"
shows "path S q p" 
using assms(1-3) proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then have "q \<in> nodes S" using merge_FSMs_nodes[OF assms(4,5)] by blast
  then show ?case by auto
next
  case (Cons t p)

  have "t \<in> h (merge_FSMs M S)" and "t_source t = q" and "path (merge_FSMs M S) (t_target t) p"
    using Cons.prems by blast+

  have "t \<in> (h M) \<union> {t2 \<in> h S . (t_source t2 \<in> nodes (merge_FSMs M S)) \<and> (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
    using \<open>t \<in> h (merge_FSMs M S)\<close> merge_FSMs_h[OF assms(4,5)] by blast
  moreover have "t \<notin> h M"
    using Cons.prems(2,3) \<open>t_source t = q\<close> unfolding deadlock_state.simps by blast
  ultimately have "t \<in> h S" and "t_source t \<in> nodes (merge_FSMs M S)" and "t_source t = initial S \<or> t_source t \<notin> nodes M" and "\<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t)"
    by blast+

  then have 

  
  
  

  then show ?case 
qed


end (*

(* companion lemma for right, use together to prove finit path length *)
lemma merge_FSMs_path_left :
  assumes "path (merge_FSMs M S) (initial (merge_FSMs M S)) p"
  and     "q \<in> nodes M"
  assumes "inputs M = inputs S"
  and     "outputs M = outputs S"
shows "path M (initial M) p"





lemma merge_FSMs_path :
  assumes "path (merge_FSMs M S) q p"
  shows "\<exists> p1 p2 . p = p1@p2 \<and> path (merge_FSMs M S) q p1 \<and> path (merge_FSMs M S) (target  p1

end (*


nitpick_params[timeout= 120]


(* incorrect *)
(* instead cut off transitions if a state has no defined input in either M or S *)
(*
                                          transitions = (wf_transitions M) @ (filter (\<lambda> t2 . (t_source t2 = initial S \<or> t_source t2 \<notin> nodes M) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)) (wf_transitions S)),
*)
lemma merge_FSMs_path_left :
  assumes "path (merge_FSMs M S) q p"
  and     "q \<in> nodes M"
  and     "\<not> deadlock_state M q"
  assumes "inputs M = inputs S"
      and "outputs M = outputs S" 
shows "path M q p" nitpic
  using assms proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons t p)

  have "t \<in> h (merge_FSMs M S)" and "t_source t = q" and "path (merge_FSMs M S) (t_target t) p"
    using Cons.prems by blast+
  then have "t \<in> (h M) \<union> {t2 \<in> h S . t_source t2 \<in> nodes (merge_FSMs M S) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
    using merge_FSMs_h[OF assms(4,5)] by blast
  then have "t \<in> h M"
    using Cons.prems(3) \<open>t_source t = q\<close> unfolding deadlock_state.simps by auto
  then have "t_target t \<in> nodes M"
    by blast
  
  moreover have "path M (t_target t) p"
  proof (cases p)
    case Nil
    then show ?thesis by (simp add: \<open>t_target t \<in> nodes M\<close> nil) 
  next
    case (Cons t' p')
    then have "t' \<in> h (merge_FSMs M S)" 
      using \<open>path (merge_FSMs M S) (t_target t) p\<close> by blast
    then have "t' \<in> (h M) \<union> {t2 \<in> h S . t_source t2 \<in> nodes (merge_FSMs M S) \<and> \<not> (\<exists> t1 \<in> h M . t_source t1 = t_source t2)}"
      using merge_FSMs_h[OF assms(4,5)] by blast
    then have "t' \<in> h M"
      

    moreover have "t_source t' = t_target t"
      using \<open>path (merge_FSMs M S) (t_target t) p\<close>
      by (metis (no_types, lifting) list.distinct(1) list.sel(1) local.Cons path.cases) 
    ultimately have "\<not> deadlock_state M (t_target t)"
      unfolding deadlock_state.simps 
    then show ?thesis 
  qed

  show ?case proof (cases p)
    case Nil
    then show ?thesis 
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed


lemma merge_FSMs_acyclic :
  assumes "acyclic S"
      and "acyclic M"
  assumes "inputs M = inputs S"
      and "outputs M = outputs S"  
shows "acyclic (merge_FSMs M S)"
  
  
  
  
  

end (*



lemma x :
  assumes "\<And> S . S \<in> set SS \<Longrightarrow> 
                inputs S = inputs M \<and> 
                outputs S = outputs M \<and> 
                single_input S \<and> 
                acyclic S \<and>
                h S \<subseteq> h (product (from_FSM M q1) (from_FSM M q2)) \<and> 
                retains_outputs_for_states_and_inputs (product (from_FSM M q1) (from_FSM M q2)) S \<and>
                (\<forall> q \<in> nodes S . deadlock_state S q \<longrightarrow> ((\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = (fst q) \<and> t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))))"
  and "SS \<noteq> []"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
  and "(filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) \<noteq> []" 
  and "\<And> t . t \<in> h (product (from_FSM M q1) (from_FSM M q2)) 
              \<Longrightarrow> t_source t = (q1,q2) 
              \<Longrightarrow> (\<exists> S \<in> set SS . initial S = t_target t)"
shows " inputs (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) = inputs M \<and> 
        outputs (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) = outputs M \<and> 
        single_input (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) \<and> 
        acyclic (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) \<and>
        h (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) \<subseteq> h (product (from_FSM M q1) (from_FSM M q2)) \<and> 
        retains_outputs_for_states_and_inputs (product (from_FSM M q1) (from_FSM M q2)) (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) \<and>
        (\<forall> q \<in> nodes (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) . deadlock_state (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) SS) q \<longrightarrow> ((\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = (fst q) \<and> t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))))"  

using assms proof (induction SS rule: rev_induct)
  case Nil
  show ?case using \<open>[] \<noteq> []\<close> by presburger
next
  case (snoc S SS)

  let ?merge = "(merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) (SS@[S]))"
  
  show ?case proof (cases "SS = []")
    case True
    then have "?merge = (merge_sub_intersections (inputs M) (outputs M) (q1,q2) (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) [S])"
      by (metis append_self_conv2)
    then have "?merge = \<lparr>initial = (q1,q2), inputs = inputs M, outputs = outputs M,
                         transitions = merge_sub_intersection_transitions (filter (\<lambda>t . t_source t = (q1,q2) \<and> t_input = x) (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))) S , \<dots> = more S \<rparr>"
      using merge_sub_intersections.simps(2) by metis
    then show ?thesis 
  next
    case False
    then show ?thesis sorry
  qed
    

qed






lemma y : 
  assumes "r_distinguishable M q1 q2"
  assumes "observable M"
  assumes "q1 \<in> nodes M" and "q2 \<in> nodes M"
  shows "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
proof -

  have *: "\<And> S . is_submachine S (product (from_FSM M q1) (from_FSM M q2)) \<Longrightarrow> \<exists> q \<in> nodes S . \<exists> x \<in> set (inputs M) . \<not> (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x)"
    using assms(1) unfolding r_compatible_def completely_specified.simps
    by (metis from_FSM_product_inputs is_submachine.elims(2))  

  have **: "\<And> S S' . is_submachine S (product (from_FSM M q1) (from_FSM M q2)) \<Longrightarrow> is_submachine S' S \<Longrightarrow>  \<not> completely_specified S'"
    using assms(1) submachine_transitive unfolding r_compatible_def by blast

  obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))" 
    unfolding is_submachine.simps by blast

  then obtain q x where "q \<in> nodes S" and "x \<in> set (inputs M)" and "\<not> (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x)"
    using * by blast

  (* choose arbitrary   


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