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


(* TODO: move *)
lemma transitions_subset_path :
  assumes "set p \<subseteq> h M"
  and     "p \<noteq> []"
  and     "path S q p"
shows "path M q p"
  using assms by (induction p arbitrary: q; auto)


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

(* TODO: move *)
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


(*
lemma list_transition_property :
  assumes "P (xs ! i)"
  and     "\<And> j . Suc j < length xs \<Longrightarrow> P (xs ! j) \<Longrightarrow> P (xs ! (Suc j))"
  and     "i < length xs"
shows "\<forall> x \<in> set (drop i xs) . P x"
  using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  show ?case proof (cases xs rule: rev_cases)
    case Nil
    then show ?thesis using snoc by auto
  next
    case (snoc xs' x')
    show ?thesis proof (cases "i < length xs")
      case True
      then show ?thesis using snoc snoc.prems snoc.IH sorry
    next
      case False
      then show ?thesis using snoc snoc.prems snoc.IH
        by (metis append_eq_conv_conj in_set_conv_nth length_append_singleton less_SucE list.size(3) not_less_zero nth_append_length set_ConsD) 
    qed   
  qed
qed
*)

lemma list_set_sym :
  "set (x@y) = set (y@x)" by auto

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



(*
  definition is_state_separator_from_canonical_separator :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_state_separator_from_canonical_separator CSep q1 q2 S = (
    is_submachine S CSep 
    \<and> single_input S
    \<and> acyclic S
    \<and> deadlock_state S (Inr q1)
    \<and> deadlock_state S (Inr q2)
    \<and> ((Inr q1) \<in> nodes S)
    \<and> ((Inr q2) \<in> nodes S)
    \<and> (\<forall> q \<in> nodes S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (isl q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> q \<in> nodes S . \<forall> x \<in> set (inputs CSep) . (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h CSep . t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))
)"
*)

definition induces_state_separator :: "('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> 'a, 'b) FSM_scheme \<Rightarrow> bool" where
  "induces_state_separator M S = (
    
    is_submachine S (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))
    \<and> single_input S
    \<and> acyclic S
    \<and> (\<forall> qq \<in> nodes S . deadlock_state S qq \<longrightarrow> (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = fst qq \<and> t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) )
    \<and> retains_outputs_for_states_and_inputs (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))) S
)"



fun s_states :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ('a \<times> Input) list" where
  "s_states C 0 = []" |
  "s_states C (Suc k) =  
    (if length (s_states C k) < k 
      then (s_states C k)
      else (case find 
                  (\<lambda> qx . (\<forall> qx' \<in> set (s_states C k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states C k) . fst qx' = (t_target t)))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
            of Some qx \<Rightarrow> (s_states C k)@[qx] | 
               None \<Rightarrow> (s_states C k)))"

fun s_states' :: "('a \<times> Input) list \<Rightarrow> 'a Transition set \<Rightarrow> nat \<Rightarrow> ('a \<times> Input) list" where
  "s_states' QX H 0 = []" |
  "s_states' QX H (Suc k) = (let Q = s_states' QX H k in 
    (if length Q < k 
      then Q
      else (case find (\<lambda> qx . (\<forall> qx' \<in> set Q . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> H . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set Q . fst qx' = (t_target t)))) QX
            of Some qx \<Rightarrow> Q@[qx] | 
               None \<Rightarrow> Q)))"

fun s_states_opt :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ('a \<times> Input) list" where
  "s_states_opt C k = s_states' (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C))) (h C) k"

value "(let PR = (product (from_FSM M_ex_9 0) (from_FSM M_ex_9 3)) in s_states_opt PR (size PR))"



lemma s_states_code[code] : "s_states M k = s_states_opt M k"  
proof (induction k)
  case 0
  then show ?case 
    unfolding s_states.simps s_states_opt.simps s_states'.simps by blast
next
  case (Suc k)
  then show ?case 
    unfolding s_states.simps s_states_opt.simps s_states'.simps Let_def
    by presburger 
qed
  

lemma s_states_length :
  "length (s_states M k) \<le> k"
proof (induction k)
  case 0
  then show ?case by auto 
next
  case (Suc k)
  show ?case
  proof (cases "length (s_states M k) < k")
    case True
    then show ?thesis unfolding s_states.simps
      by simp 
  next
    case False
    then have "s_states M (Suc k) = (case find
                    (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and>
                          (\<forall>t\<in>set (wf_transitions M).
                              t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                              (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t)))
                    (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of
              None \<Rightarrow> (s_states M k) | Some qx \<Rightarrow> (s_states M k) @ [qx])" 
      unfolding s_states.simps by presburger
    then show ?thesis using Suc
      by (metis (mono_tags, lifting) False Suc_lessD eq_iff leI length_append_singleton option.case_eq_if)
  qed
qed

lemma s_states_prefix :
  assumes "i \<le> k"
  shows "take i (s_states M k) = s_states M i"
  using assms proof (induction k)
  case 0
  then show ?case unfolding s_states.simps
    by (metis le_zero_eq  s_states.simps(1) s_states_length take_all) 
next
  case (Suc k)
  then show ?case proof (cases "i < Suc k")
    case True
    then have "take i (s_states M k) = s_states M i"
      using Suc by auto
    then have "length (s_states M i) \<le> length (s_states M k)"
      by (metis dual_order.trans nat_le_linear s_states_length take_all)
    moreover have "take (length (s_states M k)) (s_states M (Suc k)) = s_states M k"
      unfolding s_states.simps
      by (simp add: option.case_eq_if) 
    ultimately have "take i (s_states M (Suc k)) = take i (s_states M k)"
      unfolding s_states.simps (* TODO: refactor auto-generated proof *)
    proof -
      have f1: "\<forall>ps f z. if z = None then (case z of None \<Rightarrow> ps::('a \<times> integer) list | Some (x::'a \<times> integer) \<Rightarrow> f x) = ps else (case z of None \<Rightarrow> ps | Some x \<Rightarrow> f x) = f (the z)"
        by force
      { assume "\<not> i < length (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])"
        then have "length (s_states M k) \<noteq> k \<or> length (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) \<noteq> Suc (length (s_states M k))"
          using True by linarith
        then have "(if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = s_states M k @ [the (find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))] \<longrightarrow> take i (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = take i (s_states M k)"
          using nat_less_le s_states_length by auto }
      moreover
      { assume "(if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) \<noteq> s_states M k @ [the (find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))]"
        moreover
        { assume "(case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) \<noteq> s_states M k @ [the (find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))]"
          then have "find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = None"
            using f1 by meson
          then have "take i (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = take i (s_states M k)"
            using f1 by presburger }
        ultimately have "take i (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = take i (s_states M k)"
          by presburger }
      ultimately have "take i (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = take i (s_states M k)"
        by fastforce
        then show "take i (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa\<in>set (s_states M k). fst p \<noteq> fst pa) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p\<in>set (s_states M k). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = take i (s_states M k)"
      proof -
        have f1: "\<forall>ps psa psb psc. (take (length (psc::('a \<times> integer) list)) psa = psc \<or> ps @ psb \<noteq> psa) \<or> take (length psc) ps \<noteq> psc"
          by force
        { assume "take i (s_states M (Suc k)) = take i (s_states M k)"
          then have ?thesis
            by simp }
        moreover
        { assume "\<exists>n. take n (s_states M (Suc k)) \<noteq> take n (s_states M k) \<and> n \<le> k"
          then have "\<exists>n. take (min k n) (s_states M (Suc k)) \<noteq> take n (s_states M k) \<and> take (min k n) (s_states M k) = take n (s_states M k)"
            by (metis min.absorb2)
          then have "length (s_states M k) \<noteq> k"
            using f1 by (metis (no_types) \<open>take (length (s_states M k)) (s_states M (Suc k)) = s_states M k\<close> append_eq_conv_conj length_take)
          then have ?thesis
            by (simp add: nat_less_le s_states_length) }
        ultimately show ?thesis
          using True less_Suc_eq_le by blast
      qed
          
        
    qed 
    then show ?thesis 
      using \<open>take i (s_states M k) = s_states M i\<close> by simp
  next
    case False 
    then have "i = Suc k" using Suc.prems by auto
    
    then show ?thesis
      using s_states_length take_all by blast
  qed
qed

lemma s_states_self_length :
  "s_states M k = s_states M (length (s_states M k))" 
  using s_states_prefix 
  by (metis (no_types) nat_le_linear s_states_length s_states_prefix take_all)

(* TODO: move *)
lemma concat_pair_set :
  "set (concat (map (\<lambda>x. map (Pair x) ys) xs)) = {xy . fst xy \<in> set xs \<and> snd xy \<in> set ys}"
  by auto

lemma s_states_index_properties : 
  assumes "i < length (s_states M k)"
shows "fst (s_states M k ! i) \<in> nodes M" 
      "snd (s_states M k ! i) \<in> set (inputs M)"
      "(\<forall> qx' \<in> set (take i (s_states M k)) . fst (s_states M k ! i) \<noteq> fst qx')" 
      "(\<forall> t \<in> h M . (t_source t = fst (s_states M k ! i) \<and> t_input t = snd (s_states M k ! i)) \<longrightarrow> (\<exists> qx' \<in> set (take i (s_states M k)) . fst qx' = (t_target t)))"
proof -
  have combined_properties: "fst (s_states M k ! i) \<in> nodes M 
       \<and> snd (s_states M k ! i) \<in> set (inputs M)
       \<and> (\<forall> qx' \<in> set (take i (s_states M k)) . fst (s_states M k ! i) \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst (s_states M k ! i) \<and> t_input t = snd (s_states M k ! i)) \<longrightarrow> (\<exists> qx' \<in> set (take i (s_states M k)) . fst qx' = (t_target t)))"
    using assms proof (induction k)
    case 0
    then have "i = 0" by auto 
    then have "s_states M 0 \<noteq> []"
      using 0 by auto
    then obtain qx where qx_def : "s_states M 0 = [qx]"
      unfolding s_states.simps
      by (metis (no_types, lifting) option.case_eq_if) 
    then have *: "find 
            (\<lambda> qx . \<not> (\<exists> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx))) 
            (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
      unfolding s_states.simps
      by (metis (mono_tags, lifting) \<open>s_states M 0 = [qx]\<close> \<open>s_states M 0 \<noteq> []\<close>)
    
    have "\<not> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)"
      using find_condition[OF *] by assumption
    have "qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
      using find_set[OF *] by assumption
    then have "fst qx \<in> nodes M \<and> snd qx \<in> set (inputs M)"
      using nodes_code[of M]
      by (metis (no_types, lifting) concat_map_elem fst_conv list_map_source_elem snd_conv)
    moreover have "(\<forall> qx' \<in> set (take i (s_states M 0)) . fst (s_states M 0 ! i) \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst (s_states M 0 ! i) \<and> t_input t = snd (s_states M 0 ! i)) \<longrightarrow> (\<exists> qx' \<in> set (take i (s_states M 0)) . fst qx' = (t_target t)))"
      using \<open>i = 0\<close>
      using \<open>\<not> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)\<close> qx_def by auto     
    moreover have "s_states M 0 ! i = qx"
      using \<open>i = 0\<close> qx_def by simp
    ultimately show ?case by blast
  next
    case (Suc k)
    show ?case proof (cases "i < length (s_states M k)")
      case True
      then have "s_states M k ! i = s_states M (Suc k) ! i"
        using s_states_prefix[of i]
      proof -
        have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
          by (meson Suc_leI)
        then show ?thesis
          by (metis Suc.prems \<open>i < length (s_states M k)\<close> s_states_prefix s_states_self_length take_last_index)
      qed
      moreover have "take i (s_states M k) = take i (s_states M (Suc k))"
        by (metis Suc.prems Suc_leI less_le_trans nat_less_le not_le s_states_length s_states_prefix)
      ultimately show ?thesis using Suc.IH[OF True] by presburger
    next
      case False
      then have "i = length (s_states M k)"
      proof -
        have "length (s_states M k) = k"
          by (metis (no_types) False Suc.prems nat_less_le s_states.simps(2) s_states_length)
        then show ?thesis
          by (metis (no_types) False Suc.prems Suc_leI leI less_le_trans nat_less_le s_states_length)
      qed
      then have "(s_states M (Suc k)) ! i = last (s_states M (Suc k))"
        by (metis (no_types, lifting) Suc.prems nat_less_le s_states.simps(2) s_states_code s_states_length take_all take_last_index)
      then have "(s_states M (Suc k)) = (s_states M k)@[last (s_states M (Suc k))]"
      proof -
        have "i = k"
          by (metis (no_types) Suc.prems \<open>i = length (s_states M k)\<close> nat_less_le s_states.simps(2) s_states_length)
        then show ?thesis
          by (metis Suc.prems Suc_n_not_le_n \<open>s_states M (Suc k) ! i = last (s_states M (Suc k))\<close> nat_le_linear s_states_prefix take_Suc_conv_app_nth)
      qed 
      then have *: "find 
                  (\<lambda> qx . (\<forall> qx' \<in> set (s_states M k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states M k) . fst qx' = (t_target t)))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) = Some (last (s_states M (Suc k)))"
        unfolding s_states.simps(2)
      proof -
        assume "(if length (s_states M k) < k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx]) = s_states M k @ [last (if length (s_states M k) < k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx])]"
        then have f1: "\<not> length (s_states M k) < k"
          by force
        then have f2: "last (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = last (case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])"
          by presburger
        have "\<not> length (s_states M k) < k \<and> s_states M k @ [last (s_states M k)] \<noteq> s_states M k"
          using f1 by simp
        then have "find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
        proof -
          have "s_states M k @ [last (if length (s_states M k) < k then s_states M k else case None of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])] \<noteq> (case None of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])"
            by force
          then show ?thesis
            by (metis (full_types, lifting) \<open>(if length (s_states M k) < k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx]) = s_states M k @ [last (if length (s_states M k) < k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx])]\<close> \<open>\<not> length (s_states M k) < k \<and> s_states M k @ [last (s_states M k)] \<noteq> s_states M k\<close>)
        qed
        then have "Some (last (case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])) = find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M)))"
          using option.collapse by fastforce
        then show "find (\<lambda>p. (\<forall>pa\<in>set (s_states M k). fst p \<noteq> fst pa) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p\<in>set (s_states M k). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = Some (last (if length (s_states M k) < k then s_states M k else case find (\<lambda>p. (\<forall>pa\<in>set (s_states M k). fst p \<noteq> fst pa) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p\<in>set (s_states M k). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]))"
          using f2 by metis
      qed

      
      let ?qx = "last (s_states M (Suc k))"
      
      have "(\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and>
         (\<forall>t\<in>set (wf_transitions M).
             t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
             (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) ?qx"
        using find_condition[OF *] \<open>(s_states M (Suc k)) ! i = last (s_states M (Suc k))\<close> by force


      
      

      have "?qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
        using find_set[OF *] by assumption
      then have "fst ?qx \<in> nodes M \<and> snd ?qx \<in> set (inputs M)"
        using nodes_code[of M] concat_pair_set[of "inputs M" "nodes_from_distinct_paths M"] by blast
      moreover have "(\<forall>qx'\<in>set (take i (s_states M (Suc k))). fst ?qx \<noteq> fst qx')"
        by (metis find_condition[OF *] \<open>i = length (s_states M k)\<close> \<open>s_states M (Suc k) = s_states M k @ [last (s_states M (Suc k))]\<close> append_eq_conv_conj)
      moreover have "(\<forall>t\<in>set (wf_transitions M).
        t_source t = fst (s_states M (Suc k) ! i) \<and> t_input t = snd (s_states M (Suc k) ! i) \<longrightarrow>
        (\<exists>qx'\<in>set (take i (s_states M (Suc k))). fst qx' = t_target t))"
        using find_condition[OF *] \<open>(s_states M (Suc k)) ! i = last (s_states M (Suc k))\<close>
        by (metis \<open>i = length (s_states M k)\<close> le_imp_less_Suc less_or_eq_imp_le s_states_length s_states_prefix s_states_self_length) 
      ultimately show ?thesis by (presburger add: \<open>(s_states M (Suc k)) ! i = last (s_states M (Suc k))\<close>)
    qed
  qed

  show "fst (s_states M k ! i) \<in> nodes M" 
       "snd (s_states M k ! i) \<in> set (inputs M)"
       "(\<forall> qx' \<in> set (take i (s_states M k)) . fst (s_states M k ! i) \<noteq> fst qx')" 
       "(\<forall> t \<in> h M . (t_source t = fst (s_states M k ! i) \<and> t_input t = snd (s_states M k ! i)) \<longrightarrow> (\<exists> qx' \<in> set (take i (s_states M k)) . fst qx' = (t_target t)))"
    using combined_properties by presburger+
qed


  


(* TODO: move *)
lemma list_distinct_prefix :
  assumes "\<And> i . i < length xs \<Longrightarrow> xs ! i \<notin> set (take i xs)"
  shows "distinct xs"
proof -
  have "\<And> j . distinct (take j xs)"
  proof -
    fix j 
    show "distinct (take j xs)"
    proof (induction j)
      case 0
      then show ?case by auto
    next
      case (Suc j)
      then show ?case proof (cases "Suc j \<le> length xs")
        case True
        then have "take (Suc j) xs = (take j xs) @ [xs ! j]"
          by (simp add: Suc_le_eq take_Suc_conv_app_nth)
        then show ?thesis using Suc.IH assms[of j] True by auto
      next
        case False
        then have "take (Suc j) xs = take j xs" by auto
        then show ?thesis using Suc.IH by auto
      qed
    qed 
  qed
  then have "distinct (take (length xs) xs)"
    by blast
  then show ?thesis by auto 
qed



lemma s_states_distinct_states :
  "distinct (map fst (s_states M k))" 
proof -
  have "(\<And>i. i < length (map fst (s_states M k)) \<Longrightarrow>
          map fst (s_states M k) ! i \<notin> set (take i (map fst (s_states M k))))"
    using s_states_index_properties(3)[of _ M k]
    by (metis (no_types, lifting) length_map list_map_source_elem nth_map take_map) 
  then show ?thesis
    using list_distinct_prefix[of "map fst (s_states M k)"] by blast
qed

(* TODO: move *)
lemma list_property_from_index_property :
  assumes "\<And> i . i < length xs \<Longrightarrow> P (xs ! i)"
  shows "\<And> x . x \<in> set xs \<Longrightarrow> P x"
  by (metis assms in_set_conv_nth) 

lemma s_states_nodes : 
  "set (map fst (s_states M k)) \<subseteq> nodes M"
  using s_states_index_properties(1)[of _ M k]  list_property_from_index_property[of "map fst (s_states M k)" "\<lambda>q . q \<in> nodes M"]
  by fastforce

lemma s_states_size :
  "length (s_states M k) \<le> size M"
proof -
  show ?thesis 
    using s_states_nodes[of M k]
          s_states_distinct_states[of M k]
          nodes_finite[of M]
    by (metis card_mono distinct_card length_map size_def) 
qed
  
lemma s_states_max_iterations :
  assumes "k \<ge> size M"
  shows "s_states M k = s_states M (size M)"
  using s_states_size[of M k] s_states_prefix[OF assms, of M]
  by simp 



lemma s_states_by_index :
  assumes "i < length (s_states M k)"
  shows "(s_states M k) ! i = last (s_states M (Suc i))"
  by (metis Suc_leI assms s_states_prefix s_states_self_length take_last_index) 




(* TODO: check *)
declare from_FSM.simps[simp del]
declare product.simps[simp del]
declare from_FSM_simps[simp del]
declare product_simps[simp del]

(* TODO: move *)
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

(* TODO: remove/move *)
lemma submachine_from_h_origin :
  assumes "t \<in> h S"
  and     "is_submachine S (from_FSM M q)"
  and     "q \<in> nodes M"
shows "t \<in> h M"
  by (meson assms contra_subsetD from_FSM_h submachine_h)


(* TODO: move *)

lemma product_deadlock :
  assumes "\<not> (\<exists> t \<in> h (product (from_FSM M q1) (from_FSM M q2)).
               t_source t = qq \<and> t_input t = x)"
  and "qq \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
  and "x \<in> set (inputs M)"
shows "\<not> (\<exists> t1 \<in> h M. \<exists> t2 \<in> h M.
                 t_source t1 = fst qq \<and>
                 t_source t2 = snd qq \<and>
                 t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)" 
proof 
  assume "\<exists> t1 \<in> h M. \<exists> t2 \<in> h M.
                 t_source t1 = fst qq \<and>
                 t_source t2 = snd qq \<and>
                 t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
  then obtain t1 t2 where "t1 \<in> h M"
                      and "t2 \<in> h M"
                      and "t_source t1 = fst qq"
                      and "t_source t2 = snd qq"
                      and "t_input t1 = x"
                      and "t_input t2 = x" 
                      and "t_output t1 = t_output t2"
    by blast

  have "fst qq \<in> nodes (from_FSM M q1)" and "snd qq \<in> nodes (from_FSM M q2)"
    using product_nodes assms(2)
    by fastforce+

 
  have "t_source t1 \<in> nodes (from_FSM M q1)"
    using \<open>fst qq \<in> nodes (from_FSM M q1)\<close> \<open>t_source t1 = fst qq\<close> by simp
  then have *: "(fst qq, x, t_output t1, t_target t1) \<in> h (from_FSM M q1)"
    using from_FSM_nodes_transitions[OF \<open>t1 \<in> h M\<close>] \<open>t_input t1 = x\<close> \<open>t_source t1 = fst qq\<close>
    by (metis prod.collapse) 

  have "t_source t2 \<in> nodes (from_FSM M q2)"
    using \<open>snd qq \<in> nodes (from_FSM M q2)\<close> \<open>t_source t2 = snd qq\<close> by simp
  have **: "(snd qq, x, t_output t1, t_target t2) \<in> h (from_FSM M q2)"
    using from_FSM_nodes_transitions[OF \<open>t2 \<in> h M\<close> \<open>t_source t2 \<in> nodes (from_FSM M q2)\<close>] \<open>t_source t2 = snd qq\<close> \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> \<open>t_source t2 = snd qq\<close> \<open>t_output t1 = t_output t2\<close> 
    by (metis prod.collapse)

  have ***: "(\<exists>p1 p2.
        path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
        path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
        target p1 (initial (from_FSM M q1)) = fst qq \<and>
        target p2 (initial (from_FSM M q2)) = snd qq \<and> p_io p1 = p_io p2)"
    using assms(2) product_node_from_path[of "fst qq" "snd qq" "from_FSM M q1" "from_FSM M q2"]
          prod.collapse[of qq] 
    by auto
  
  have "(qq, x, t_output t1, (t_target t1, t_target t2)) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
    using product_transition[of "fst qq" "snd qq" "x" "t_output t1" "t_target t1" "t_target t2" "from_FSM M q1" "from_FSM M q2"]
    using * ** *** prod.collapse[of qq] by auto
  moreover have "t_source (qq, x, t_output t1, (t_target t1, t_target t2)) = qq"
            and "t_input (qq, x, t_output t1, (t_target t1, t_target t2)) = x"
    by auto
  ultimately show "False"
    using assms(1) by blast
qed




lemma s_states_induces_state_separator_helper_h :
  assumes "t \<in> h \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                      inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                      outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                      transitions = 
                         filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>"
  shows "(t_source t, t_input t) \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k)" 
  using assms by force

lemma s_states_induces_state_separator_helper_single_input :
  "single_input \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                      inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                      outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                      transitions = 
                         filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>"
  (is "single_input ?S")
proof -
  have "\<And> t1 t2 . t1 \<in> h ?S \<Longrightarrow> t2 \<in> h ?S \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2"
  proof -
    fix t1 t2 assume "t1 \<in> h ?S"
                 and "t2 \<in> h ?S"
                 and "t_source t1 = t_source t2"

    have "(t_source t1, t_input t1) \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k)"
      using s_states_induces_state_separator_helper_h[OF \<open>t1 \<in> h ?S\<close>] by assumption
    moreover have "(t_source t1, t_input t2) \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k)"
      using s_states_induces_state_separator_helper_h[OF \<open>t2 \<in> h ?S\<close>] \<open>t_source t1 = t_source t2\<close> by auto
    ultimately show "t_input t1 = t_input t2"
      using s_states_distinct_states[of "product (from_FSM M q1) (from_FSM M q2)" k]
      by (meson eq_key_imp_eq_value) 
  qed
  then show ?thesis
    unfolding single_input.simps by blast
qed


lemma s_states_induces_state_separator_helper_retains_outputs :
  "retains_outputs_for_states_and_inputs 
          (product (from_FSM M q1) (from_FSM M q2)) 
              \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                transitions = 
                   filter 
                     (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>"
  (is "retains_outputs_for_states_and_inputs ?PM ?S")
proof -
  have "\<And> tS tM . tS \<in> h ?S \<Longrightarrow> tM \<in> h ?PM \<Longrightarrow> t_source tS = t_source tM \<Longrightarrow> t_input tS = t_input tM \<Longrightarrow> tM \<in> h ?S"
  proof -
    fix tS tM assume "tS \<in> h ?S" 
                 and "tM \<in> h ?PM" 
                 and "t_source tS = t_source tM" 
                 and "t_input tS = t_input tM"

    have "(t_source tS, t_input tS) \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k)"
      using s_states_induces_state_separator_helper_h[OF \<open>tS \<in> h ?S\<close>] by assumption
    then have "\<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source tS = fst qqx \<and> t_input tS = snd qqx"
      by force
    then have "\<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source tM = fst qqx \<and> t_input tM = snd qqx"
      using \<open>t_source tS = t_source tM\<close> \<open>t_input tS = t_input tM\<close> by simp
    then have "tM \<in> set (transitions ?S)"
      using \<open>tM \<in> h ?PM\<close> by force
    moreover have "t_source tM \<in> nodes ?S"
      using \<open>t_source tS = t_source tM\<close> \<open>tS \<in> h ?S\<close>
      by (metis (no_types, lifting) wf_transition_simp) 
    ultimately show "tM \<in> h ?S"
      by simp
  qed
  then show ?thesis
    unfolding retains_outputs_for_states_and_inputs_def by blast
qed

(*
lemma s_states_transitions_nil :
  "\<not>(\<exists> t \<in> h M . (t_source t, t_input t) \<in> set (s_states M 0))"
  proof (cases "find (\<lambda>qx. \<not> (\<exists>t\<in>set (wf_transitions M).
                                         t_source t = fst qx \<and> t_input t = snd qx))
                         (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))")
  case None
  then show ?thesis unfolding s_states.simps by auto
next
  case (Some qx)
  then have "set (s_states M 0) = {qx}"
    unfolding s_states.simps by auto
  moreover have "\<not> (\<exists>t\<in>set (wf_transitions M). (t_source t, t_input t) \<in> {qx})"
    using find_condition[OF Some]
    by fastforce 
  ultimately show ?thesis 
    by blast
qed
*)

lemma s_states_subset :
  "set (s_states M k) \<subseteq> set (s_states M (Suc k))"
  unfolding s_states.simps
  by (simp add: option.case_eq_if subsetI) 

lemma s_states_last :
  assumes "s_states M (Suc k) \<noteq> s_states M k"
  shows "\<exists> qx . s_states M (Suc k) = (s_states M k)@[qx]
                \<and> (\<forall> qx' \<in> set (s_states M k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states M k) . fst qx' = (t_target t)))
                \<and> fst qx \<in> nodes M
                \<and> snd qx \<in> set (inputs M)"
proof -
  have *: "\<not> (length (s_states M k) < k) \<and> find
          (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t)))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
    using assms unfolding s_states.simps
    by (metis (no_types, lifting) option.simps(4))

  then obtain qx where qx_find: "find
          (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t)))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
    by blast

  then have "s_states M (Suc k) = (s_states M k)@[qx]"
    using * by auto
  moreover have "(\<forall> qx' \<in> set (s_states M k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states M k) . fst qx' = (t_target t)))"
    using find_condition[OF qx_find] by assumption
  moreover have "fst qx \<in> nodes M
                \<and> snd qx \<in> set (inputs M)"
    using find_set[OF qx_find]
  proof -
    have "fst qx \<in> set (nodes_from_distinct_paths M) \<and> snd qx \<in> set (inputs M)"
      using \<open>qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))\<close> concat_pair_set by blast
    then show ?thesis
      by (metis (no_types) nodes_code)
  qed 
  ultimately show ?thesis by blast
qed
  

lemma s_states_transition_target :
  assumes "(t_source t, t_input t) \<in> set (s_states M k)"
  and     "t \<in> h M"
shows "t_target t \<in> set (map fst (s_states M (k-1)))"
  and "t_target t \<noteq> t_source t"
proof -
  have "t_target t \<in> set (map fst (s_states M (k-1))) \<and> t_target t \<noteq> t_source t"
    using assms(1) proof (induction k)
    case 0 
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "(t_source t, t_input t) \<in> set (s_states M k)")
      case True
      then have "t_target t \<in> set (map fst (s_states M (k - 1))) \<and> t_target t \<noteq> t_source t"
        using Suc.IH by auto
      moreover have "set (s_states M (k - 1)) \<subseteq> set (s_states M (Suc k - 1))"
        using s_states_subset
        by (metis Suc_pred' diff_Suc_1 diff_is_0_eq' nat_less_le order_refl zero_le) 
      ultimately show ?thesis by auto
    next
      case False
      then have "set (s_states M k) \<noteq> set (s_states M (Suc k))"
        using Suc.prems by blast
      then have "s_states M (Suc k) \<noteq> s_states M k"
        by auto
      
      obtain qx where    "s_states M (Suc k) = s_states M k @ [qx]"
                  and    "(\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx')"
                  and *: "(\<forall>t\<in>set (wf_transitions M).
                                 t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))"
                  and    "fst qx \<in> nodes M \<and> snd qx \<in> set (inputs M)"
        using s_states_last[OF \<open>s_states M (Suc k) \<noteq> s_states M k\<close>] by blast
      
      have "qx = (t_source t, t_input t)"
        using Suc.prems False \<open>s_states M (Suc k) = s_states M k @ [qx]\<close>
        by auto
      then have "(\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t)"
        using assms(2) by (simp add: "*")
      then have "t_target t \<in> set (map fst (s_states M (Suc k-1)))"
        by (metis diff_Suc_1 in_set_zipE prod.collapse zip_map_fst_snd) 
      moreover have \<open>t_target t \<noteq> t_source t\<close>
        using \<open>\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t\<close> \<open>\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx'\<close> \<open>qx = (t_source t, t_input t)\<close> by fastforce
      ultimately show ?thesis by blast
    qed
  qed
  then show "t_target t \<in> set (map fst (s_states M (k-1)))"
        and "t_target t \<noteq> t_source t" by simp+
qed



fun pathlike :: "'a Transition list \<Rightarrow> bool" where
 "pathlike [] = True" |
 "pathlike [t] = True" |
 "pathlike (t1#t2#ts) = ((t_source t2 = t_target t1) \<and> pathlike (t2#ts))"

lemma pathlike_paths :
  assumes "path M q p"
  shows "pathlike p"
using assms proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons t1 ts)
  show ?case proof (cases ts)
    case Nil
    then show ?thesis by auto
  next
    case (Cons t2 ts')
    then have "path M q (t1 # t2 # ts')"
      using \<open>path M q (t1 # ts)\<close> by auto
    then have "path M (t_target t1) (t2#ts')" and "t_source t2 = t_target t1"
      by auto
    then have "pathlike ts"
      using Cons \<open>\<And> q . path M q ts \<Longrightarrow> pathlike ts\<close> by auto
    then show ?thesis 
      using \<open>t_source t2 = t_target t1\<close> Cons by auto    
  qed
qed

lemma pathlike_property :
  assumes "\<And> p . pathlike p \<Longrightarrow> set p \<subseteq> h M \<Longrightarrow> P p"
  and     "path M q p"
shows "P p"
  using assms(1)[OF pathlike_paths[OF assms(2)] path_h[OF assms(2)]] by assumption





(* TODO: move *)
fun find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index f []  = None" |
  "find_index f (x#xs) = (if f x then Some 0 else (case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None))" 

lemma find_index_index :
  assumes "find_index f xs = Some k"
  shows "k < length xs" and "f (xs ! k)" and "\<And> j . j < k \<Longrightarrow> \<not> f (xs ! j)"
proof -
  have "(k < length xs) \<and> (f (xs ! k)) \<and> (\<forall> j < k . \<not> (f (xs ! j)))"
    using assms proof (induction xs arbitrary: k)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs)
    
    show ?case proof (cases "f x")
      case True
      then show ?thesis using Cons.prems by auto
    next
      case False
      then have "find_index f (x#xs) = (case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None)"
        by auto
      then have "(case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None) = Some k"
        using Cons.prems by auto
      then obtain k' where "find_index f xs = Some k'" and "k = Suc k'"
        by (metis option.case_eq_if option.collapse option.distinct(1) option.sel)
        
      have "k < length (x # xs) \<and> f ((x # xs) ! k)" using Cons.IH[OF \<open>find_index f xs = Some k'\<close>] using \<open>k = Suc k'\<close> by auto
      moreover have "(\<forall>j<k. \<not> f ((x # xs) ! j))"
        using Cons.IH[OF \<open>find_index f xs = Some k'\<close>] using \<open>k = Suc k'\<close> False
        using less_Suc_eq_0_disj by auto 
      ultimately show ?thesis by presburger
    qed
  qed
  then show "k < length xs" and "f (xs ! k)" and "\<And> j . j < k \<Longrightarrow> \<not> f (xs ! j)" by simp+
qed

lemma find_index_exhaustive : 
  assumes "\<exists> x \<in> set xs . f x"
  shows "find_index f xs \<noteq> None"
  using assms proof (induction xs)
case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case by (cases "f x"; auto)
qed




lemma s_states_last_ex :
  assumes "qx1 \<in> set (s_states M k)"
  shows "\<exists> k' . k' \<le> k \<and> k' > 0 \<and> qx1 \<in> set (s_states M k') \<and> qx1 = last (s_states M k') \<and> (\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (s_states M k''))"
proof -

  obtain k' where k'_find: "find_index (\<lambda> qqt . qqt = qx1) (s_states M k) = Some k'"
    using find_index_exhaustive[of "s_states M k" "(\<lambda> qqt . qqt = qx1)"] assms
    by blast 

  have "Suc k' \<le> k"
    using find_index_index(1)[OF k'_find] s_states_length[of M k] by presburger
  moreover have "Suc k' \<ge> 0" 
    by auto
  moreover have "qx1 \<in> set (s_states M (Suc k'))"
    using find_index_index(2)[OF k'_find]
    by (metis Suc_neq_Zero \<open>Suc k' \<le> k\<close> assms find_index_index(1) k'_find last_in_set s_states_by_index s_states_prefix take_eq_Nil) 
  moreover have "qx1 = last (s_states M (Suc k'))"
    using find_index_index(1,2)[OF k'_find]  k'_find s_states_by_index by blast 
  moreover have "(\<forall> k'' < Suc k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (s_states M k''))"
    using find_index_index(3)[OF k'_find] s_states_prefix[of _ k' M]
  proof -
    assume a1: "\<And>j. j < k' \<Longrightarrow> s_states M k ! j \<noteq> qx1"
    { fix nn :: nat
      have ff1: "\<And>n. Some k' \<noteq> Some n \<or> n < length (s_states M k)"
        using find_index_index(1) k'_find by blast
      obtain nna :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
        ff2: "\<And>n na. (\<not> n < Suc na \<or> n = 0 \<or> Suc (nna n na) = n) \<and> (\<not> n < Suc na \<or> nna n na < na \<or> n = 0)"
        by (metis less_Suc_eq_0_disj)
      moreover
      { assume "nn \<le> k \<and> s_states M k ! nna nn k' \<noteq> qx1"
        then have "Suc (nna nn k') = nn \<longrightarrow> nn = 0 \<or> (\<exists>n\<ge>Suc k'. \<not> nn < n) \<or> (\<exists>n. Suc n = nn \<and> n \<noteq> nna nn k') \<or> \<not> 0 < nn \<or> \<not> nn < Suc k' \<or> last (s_states M nn) \<noteq> qx1"
          using ff1 by (metis (no_types) Suc_less_eq nat_less_le s_states_prefix take_last_index) }
      ultimately have "Suc (nna nn k') = nn \<longrightarrow> nn = 0 \<or> \<not> 0 < nn \<or> \<not> nn < Suc k' \<or> last (s_states M nn) \<noteq> qx1"
        using a1 by (metis Suc_leI Suc_n_not_le_n \<open>Suc k' \<le> k\<close> less_le_trans nat.inject nat_le_linear)
      then have "\<not> 0 < nn \<or> \<not> nn < Suc k' \<or> last (s_states M nn) \<noteq> qx1"
        using ff2 by blast }
    then show ?thesis
      by blast
  qed
  ultimately show ?thesis by blast
qed


lemma s_states_last_least : 
  assumes "qx1 \<in> set (s_states M k')"
  and "qx1 = last (s_states M k')"
  and "(\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (s_states M k''))"
shows "(k' = (LEAST k' . qx1 \<in> set (s_states M k')))" 
proof (rule ccontr)
  assume "k' \<noteq> (LEAST k'. qx1 \<in> set (s_states M k'))"
  then obtain k'' where "k'' < k'" and "qx1 \<in> set (s_states M k'')"
    by (metis (no_types, lifting) LeastI assms(1) nat_neq_iff not_less_Least)

  obtain k''' where "k''' \<le> k''" and "k'''>0" and "qx1 = last (s_states M k''')" and "(\<forall>k''<k'''. 0 < k'' \<longrightarrow> qx1 \<noteq> last (s_states M k''))"
    using s_states_last_ex[OF \<open>qx1 \<in> set (s_states M k'')\<close>] by blast

  have "k''' < k'"
    using \<open>k''' \<le> k''\<close> \<open>k'' < k'\<close> by simp

  show "False"
    using assms(3) \<open>k'''>0\<close> \<open>k''' < k'\<close> \<open>qx1 = last (s_states M k''')\<close>  by blast
qed

(*
lemma s_states_last_least : 
  assumes "qx1 \<in> set (s_states M k)"
  shows "(k' = (LEAST k' . qx1 \<in> set (s_states M k'))) \<longleftrightarrow> (qx1 = last (s_states M k') \<and> (\<forall> k'' < k' . qx1 \<noteq> last (s_states M k'')))" 
proof 
  show "k' = (LEAST k'. qx1 \<in> set (s_states M k')) \<Longrightarrow> qx1 = last (s_states M k') \<and> (\<forall> k'' < k' . qx1 \<noteq> last (s_states M k''))"
  proof -
    assume "k' = (LEAST k'. qx1 \<in> set (s_states M k'))"
    then have "qx1 \<in> set (s_states M k')" 
      using assms by (meson LeastI)
    then have "\<forall> k'' . k'' < k' \<longrightarrow> \<not>(qx1 \<in> set (s_states M k''))"
      using \<open>k' = (LEAST k'. qx1 \<in> set (s_states M k'))\<close>
      using not_less_Least by blast 
    have "qx1 = last (s_states M k') "
    proof (rule ccontr)
      assume "qx1 \<noteq> last (s_states M k')"
      then have "qx1 \<in> set (butlast (s_states M k'))"
        using \<open>qx1 \<in> set (s_states M k')\<close>
        by (metis Un_iff append_butlast_last_id insert_iff list.simps(15) set_append) 
      then have "qx1 \<in> set (s_states M (k'-1))"
        by (metis \<open>\<forall>k''<k'. qx1 \<notin> set (s_states M k'')\<close> \<open>qx1 \<in> set (s_states M k')\<close> butlast_conv_take diff_le_self eq_iff leI s_states_length s_states_prefix s_states_self_length)
      then show "False"
        using \<open>\<forall> k'' . k'' < k' \<longrightarrow> \<not>(qx1 \<in> set (s_states M k''))\<close>
        by (metis \<open>qx1 \<in> set (butlast (s_states M k'))\<close> butlast_conv_take diff_less in_set_conv_nth less_numeral_extra(1) list.size(3) not_gr0 not_less0 s_states_prefix take_eq_Nil zero_le)
    qed
    moreover have "\<And> k'' . Suc k'' < k' \<Longrightarrow> qx1 \<noteq> last (s_states M (Suc k''))"
      using \<open>\<forall> k'' . k'' < k' \<longrightarrow> \<not>(qx1 \<in> set (s_states M k''))\<close>

    moreover have "(\<forall> k'' < k' . qx1 \<noteq> last (s_states M k''))"
      using \<open>\<forall> k'' . k'' < k' \<longrightarrow> \<not>(qx1 \<in> set (s_states M k''))\<close>

    proof -
      have "\<And> (xs::'a list) x i . (\<And> j . Suc j < i \<Longrightarrow> \<not> (x \<in> set (take (Suc j) xs))) \<Longrightarrow> (\<And> j . Suc j < i \<Longrightarrow> x \<noteq> last (take (Suc j) xs))"  
      proof 
        fix xs :: "'a list"
        fix x i j assume "(\<And> j . Suc j < i \<Longrightarrow> \<not> (x \<in> set (take (Suc j) xs)))" and "Suc j < i" and "x = last (take (Suc j) xs)"
        then show "False" proof (induction i)
          case 0
          then show ?case by auto
        next
          case (Suc i)
          then show ?case proof (cases "Suc j < Suc i")
            case True
            then show ?thesis 
          next
            case False
            then show ?thesis sorry
          qed 
        qed
        
        then show "False" proof (induction xs rule: rev_induct)
          case Nil 
          then show ?case  
        next
          case (snoc a xs) 
          then show ?case proof (cases "x = last (take i xs)")
            case True
            then have "x \<in> set (take i xs)" by auto
            show ?thesis using snoc.IH[OF] snoc.prems(1,2,5) snoc.prems(3)[OF snoc.prems(4)] 
          next
            case False
            then show ?thesis sorry
          qed
        qed

 
    ultimately show "qx1 = last (s_states M k') \<and> (\<forall> k'' < k' . qx1 \<noteq> last (s_states M k''))"
      by blast
  qed


  have "qx1 = last (s_states M k') \<Longrightarrow> (\<forall>k''<k'. qx1 \<noteq> last (s_states M k'')) \<Longrightarrow> k' = (LEAST k'. qx1 \<in> set (s_states M k'))"
  proof -
    assume "qx1 = last (s_states M k')" and "(\<forall>k''<k'. qx1 \<noteq> last (s_states M k''))"
    
    have "qx1 \<in> set (s_states M k')" using \<open>qx1 = last (s_states M k')\<close> assms
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_le_self diff_less last_conv_nth less_numeral_extra(1) not_le not_less_eq_eq nth_mem s_states_prefix take_all take_eq_Nil) 
    moreover have "(\<forall>k''<k'. qx1 \<notin> set (s_states M k''))"
      using \<open>(\<forall>k''<k'. qx1 \<noteq> last (s_states M k''))\<close>
      by (metis Suc_lessI ex_least_nat_le in_set_conv_nth lessI less_le_trans not_less0 s_states_by_index s_states_length) 
    ultimately show ?thesis
      by (meson LeastI nat_neq_iff not_less_Least) 
  qed
  then show "qx1 = last (s_states M k') \<and> (\<forall>k''<k'. qx1 \<noteq> last (s_states M k'')) \<Longrightarrow> k' = (LEAST k'. qx1 \<in> set (s_states M k'))" 
    by blast
qed

*)


lemma s_states_distinct_least :
  assumes "t \<in> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states M k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  shows "(LEAST k' . t_target t \<in> set (map fst (s_states M k'))) < (LEAST k' . t_source t \<in> set (map fst (s_states M k')))"
    and "t_source t \<in> set (map fst (s_states M k))"
    and "t_target t \<in> set (map fst (s_states M k))"
proof -
  have "(LEAST k' . t_target t \<in> set (map fst (s_states M k'))) < (LEAST k' . t_source t \<in> set (map fst (s_states M k')))
         \<and> t_source t \<in> set (map fst (s_states M k))
         \<and> t_target t \<in> set (map fst (s_states M k))"
  using assms proof (induction k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "s_states M (Suc k) = s_states M k")
      case True
      then show ?thesis using Suc by auto
    next
      case False
  
      obtain qx where "s_states M (Suc k) = s_states M k @ [qx]"
                      "(\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx')"
                      "(\<forall>t\<in>set (wf_transitions M).
                         t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                         (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))"
                      "fst qx \<in> nodes M \<and> snd qx \<in> set (inputs M)"
        using s_states_last[OF False] by blast
  
      
  
      then show ?thesis proof (cases "t_source t = fst qx")
        case True
  
        
        
        have "fst qx \<notin> set (map fst (s_states M k))"
          using \<open>\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx'\<close> by auto
        then have "\<And> k' . k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (s_states M k'))"
          using s_states_prefix[of _ k M]
          by (metis \<open>\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx'\<close> in_set_takeD less_Suc_eq_le list_map_source_elem) 
        moreover have "fst qx \<in> set (map fst (s_states M (Suc k)))"
          using \<open>s_states M (Suc k) = s_states M k @ [qx]\<close> by auto
          
        ultimately have "(LEAST k' . fst qx \<in> set (map fst (s_states M k'))) = Suc k"
        proof -
          have "\<not> (LEAST n. fst qx \<in> set (map fst (s_states M n))) < Suc k"
            by (meson LeastI_ex \<open>\<And>k'. k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (s_states M k'))\<close> \<open>fst qx \<in> set (map fst (s_states M (Suc k)))\<close>)
          then show ?thesis
            by (meson \<open>fst qx \<in> set (map fst (s_states M (Suc k)))\<close> not_less_Least not_less_iff_gr_or_eq)
        qed 
  
  
        have "(t_source t, t_input t) \<in> set (s_states M (Suc k)) \<and> t \<in> set (wf_transitions M)"
          using Suc.prems by auto 
        then have "t_target t \<in> set (map fst (s_states M k))"
          using s_states_transition_target(1)[of t M "Suc k"] by auto
        then have "(LEAST k' . t_target t \<in> set (map fst (s_states M k'))) \<le> k"
          by (simp add: Least_le)
        then have "(LEAST k'. t_target t \<in> set (map fst (s_states M k'))) < (LEAST k'. t_source t \<in> set (map fst (s_states M k')))" 
          using \<open>(LEAST k' . fst qx \<in> set (map fst (s_states M k'))) = Suc k\<close> True by force
        then show ?thesis
          using \<open>fst qx \<in> set (map fst (s_states M (Suc k)))\<close> True 
                \<open>t_target t \<in> set (map fst (s_states M k))\<close>
                \<open>s_states M (Suc k) = s_states M k @ [qx]\<close> by auto
      next
        case False
        then show ?thesis
          using Suc.IH Suc.prems \<open>s_states M (Suc k) = s_states M k @ [qx]\<close> by fastforce 
      qed
    qed
  qed

  then show "(LEAST k' . t_target t \<in> set (map fst (s_states M k'))) < (LEAST k' . t_source t \<in> set (map fst (s_states M k')))"
        and "t_source t \<in> set (map fst (s_states M k))"
        and "t_target t \<in> set (map fst (s_states M k))" by simp+
qed




(* TODO: move *)
lemma ordered_list_distinct :
  fixes xs :: "('a::preorder) list"
  assumes "\<And> i . Suc i < length xs \<Longrightarrow> (xs ! i) < (xs ! (Suc i))"
  shows "distinct xs"
proof -
  have "\<And> i j . i < j \<Longrightarrow> j < length xs \<Longrightarrow> (xs ! i) < (xs ! j)"
  proof -
    fix i j assume "i < j" and "j < length xs"
    then show "xs ! i < xs ! j"
      using assms proof (induction xs arbitrary: i j rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a xs)
      show ?case proof (cases "j < length xs")
        case True
        show ?thesis using snoc.IH[OF snoc.prems(1) True] snoc.prems(3)
        proof -
          have f1: "i < length xs"
            using True less_trans snoc.prems(1) by blast
          have f2: "\<forall>is isa n. if n < length is then (is @ isa) ! n = (is ! n::integer) else (is @ isa) ! n = isa ! (n - length is)"
            by (meson nth_append)
          then have f3: "(xs @ [a]) ! i = xs ! i"
            using f1
            by (simp add: nth_append)
          have "xs ! i < xs ! j"
            using f2
            by (metis Suc_lessD \<open>(\<And>i. Suc i < length xs \<Longrightarrow> xs ! i < xs ! Suc i) \<Longrightarrow> xs ! i < xs ! j\<close> butlast_snoc length_append_singleton less_SucI nth_butlast snoc.prems(3)) 
          then show ?thesis
            using f3 f2 True
            by (simp add: nth_append) 
        qed
      next
        case False
        then have "(xs @ [a]) ! j = a"
          using snoc.prems(2)
          by (metis length_append_singleton less_SucE nth_append_length)  
        
        consider "j = 1" | "j > 1"
          using \<open>i < j\<close>
          by linarith 
        then show ?thesis proof cases
          case 1
          then have "i = 0" and "j = Suc i" using \<open>i < j\<close> by linarith+ 
          then show ?thesis 
            using snoc.prems(3)
            using snoc.prems(2) by blast 
        next
          case 2
          then consider "i < j - 1" | "i = j - 1" using \<open>i < j\<close> by linarith+
          then show ?thesis proof cases
            case 1
            
            have "(\<And>i. Suc i < length xs \<Longrightarrow> xs ! i < xs ! Suc i) \<Longrightarrow> xs ! i < xs ! (j - 1)"
              using snoc.IH[OF 1] snoc.prems(2) 2 by simp 
            then have le1: "(xs @ [a]) ! i < (xs @ [a]) ! (j -1)"
              using snoc.prems(2)
              by (metis "2" False One_nat_def Suc_diff_Suc Suc_lessD diff_zero length_append_singleton less_SucE not_less_eq nth_append snoc.prems(1) snoc.prems(3))
            moreover have le2: "(xs @ [a]) ! (j -1) < (xs @ [a]) ! j"
              using snoc.prems(2,3) 2
              by (metis (full_types) One_nat_def Suc_diff_Suc diff_zero less_numeral_extra(1) less_trans)  
            ultimately show ?thesis 
              using less_trans by blast
          next
            case 2
            then have "j = Suc i" using \<open>1 < j\<close> by linarith
            then show ?thesis 
              using snoc.prems(3)
              using snoc.prems(2) by blast
          qed
        qed
      qed
    qed 
  qed

  then show ?thesis
    by (metis less_asym non_distinct_repetition_indices)
qed



(* TODO: move *)
lemma ordered_list_distinct_rev :
  fixes xs :: "('a::preorder) list"
  assumes "\<And> i . Suc i < length xs \<Longrightarrow> (xs ! i) > (xs ! (Suc i))"
  shows "distinct xs"
proof -
  have "\<And> i . Suc i < length (rev xs) \<Longrightarrow> ((rev xs) ! i) < ((rev xs) ! (Suc i))"
    using assms
  proof -
    fix i :: nat
    assume a1: "Suc i < length (rev xs)"
    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
      by moura
    then have f2: "\<forall>n na. (\<not> n < Suc na \<or> n = 0 \<or> n = Suc (nn na n) \<and> nn na n < na) \<and> (n < Suc na \<or> n \<noteq> 0 \<and> (\<forall>nb. n \<noteq> Suc nb \<or> \<not> nb < na))"
      by (meson less_Suc_eq_0_disj)
    have f3: "Suc (length xs - Suc (Suc i)) = length (rev xs) - Suc i"
      using a1 by (simp add: Suc_diff_Suc)
    have "i < length (rev xs)"
      using a1 by (meson Suc_lessD)
    then have "i < length xs"
      by simp
    then show "rev xs ! i < rev xs ! Suc i"
      using f3 f2 a1 by (metis (no_types) assms diff_less length_rev not_less_iff_gr_or_eq rev_nth)
  qed 
  then have "distinct (rev xs)" 
    using ordered_list_distinct[of "rev xs"] by blast
  then show ?thesis by auto
qed




lemma s_states_induces_state_separator_helper_distinct_pathlikes :
  assumes (*"pathlike p"*)
          "\<And> i . (Suc i) < length (t#p) \<Longrightarrow> t_source ((t#p) ! (Suc i)) = t_target ((t#p) ! i)"
  assumes "set (t#p) \<subseteq> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states M k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  
  shows "distinct ((t_source t) # map t_target (t#p))" 
proof - 

  (*let ?f = "(\<lambda> t . LEAST k' . t_target t \<in> set (map fst (s_states M k')))"*) 
  let ?f = "\<lambda> q . LEAST k' . q \<in> set (map fst (s_states M k'))"
  let ?p = "(t_source t) # map t_target (t#p)"

  have "\<And> i . (Suc i) < length ?p \<Longrightarrow> ?f (?p ! i) > ?f (?p ! (Suc i))"
  proof -
    fix i assume "Suc i < length ?p"
    
    
    let ?t1 = "(t#t#p) ! i"
    let ?t2 = "(t#t#p) ! (Suc i)"

    have "length (t#t#p) = length ?p" by auto
    



    show "?f (?p ! i) > ?f (?p ! (Suc i))" proof (cases i)
      case 0
      then have "?t1 = ?t2"
        by auto

      have "?t1 \<in> h M"
        using assms(2) 
        by (metis (no_types, lifting) Suc_lessD \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>length (t # t # p) = length (t_source t # map t_target (t # p))\<close> filter_is_subset list.set_intros(1) nth_mem set_ConsD subsetD)  
      have "?t1 \<in> set (t#t#p)"
        using \<open>length (t#t#p) = length ?p\<close>
              \<open>Suc i < length ?p\<close>
        by (metis Suc_lessD nth_mem)
      have "?t1 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (s_states M k). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t1 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then have **: "(LEAST k'. t_target ?t1 \<in> set (map fst (s_states M k')))
            < (LEAST k'. t_source ?t1 \<in> set (map fst (s_states M k')))"
        using s_states_distinct_least(1)[of ?t1 M k] by presburger
      then show ?thesis using \<open>?t1 = ?t2\<close>
        by (simp add: "0") 
    next
      case (Suc m)

      have "?t2 \<in> set (t#t#p)"
        using \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (metis nth_mem) 
      
      have "?t2 \<in> h M"
        using assms(2) using \<open>(t#t#p) ! (Suc i) \<in> set (t#t#p)\<close> by auto 
  
      have "?t2 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (s_states M k). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t2 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then have **: "(LEAST k'. t_target ?t2 \<in> set (map fst (s_states M k')))
            < (LEAST k'. t_source ?t2 \<in> set (map fst (s_states M k')))"
        using s_states_distinct_least(1)[of ?t2 M k] by presburger

      have "t_source ?t2 = t_target ?t1"
        using assms(1) \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (simp add: Suc) 

      then have " t_target ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! Suc i"
        by (metis Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> length_Cons length_map nth_Cons_Suc nth_map)
      moreover have "t_source ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! i"
        by (metis Suc Suc_lessD Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>t_source ((t # t # p) ! Suc i) = t_target ((t # t # p) ! i)\<close> length_Cons length_map nth_Cons_Suc nth_map)  
        
      ultimately show "?f (?p ! i) > ?f (?p ! (Suc i))" using ** by simp
    qed
  qed
  then have f1: "\<And> i . (Suc i) < length (map ?f ?p) \<Longrightarrow> ?f (?p ! (Suc i)) < ?f (?p ! i)"
    by auto

  moreover have f2: "\<And> i . i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! i = (LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (s_states M k')))"
  proof -
    fix i assume "i < length (map ?f ?p)"
    have map_index : "\<And> xs f i . i < length (map f xs) \<Longrightarrow> (map f xs) ! i = f (xs ! i)"
      by simp
    show "map ?f ?p ! i = (LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (s_states M k')))"
      using map_index[OF \<open>i < length (map ?f ?p)\<close>] by assumption
  qed

  ultimately have "(\<And>i. Suc i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! Suc i < map ?f ?p ! i)"
    using Suc_lessD by presburger 

  then have "distinct (map ?f ?p)"
    using ordered_list_distinct_rev[of "map ?f ?p"] by blast

  then show "distinct ?p"
    by (metis distinct_map) 
qed


lemma s_states_induces_state_separator_helper_distinct_paths :
  assumes "path \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                      inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                      outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                      transitions = 
                         filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>
                 q
                 p"
    (is "path ?S q p")
  shows "distinct (visited_states q p)" 
proof (cases p)
  case Nil
  then show ?thesis by auto
next
  case (Cons t p')

  then have *: "\<And> i . (Suc i) < length (t#p') \<Longrightarrow> t_source ((t#p') ! (Suc i)) = t_target ((t#p') ! i)"
    using assms(1) by (simp add: path_source_target_index) 
  
  have "set (t#p') \<subseteq> set (transitions ?S)"
    using Cons path_h[OF assms(1)] unfolding wf_transitions.simps 
    by (meson filter_is_subset subset_code(1)) 
  then have **: "set (t#p') \<subseteq> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))))"
    by simp

  have "distinct (t_source t # map t_target (t # p'))"
    using s_states_induces_state_separator_helper_distinct_pathlikes[OF * **]
    by auto
  moreover have "visited_states q p = (t_source t # map t_target (t # p'))"
    using Cons assms(1) unfolding visited_states.simps target.simps
    by blast 
  ultimately show "distinct (visited_states q p)"
    by auto
qed
  

lemma s_states_induces_state_separator_helper_acyclic :
  shows "acyclic \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                      inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                      outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                      transitions = 
                         filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>"
    (is "acyclic ?S")

proof -
  have "\<And> p . path ?S (initial ?S) p \<Longrightarrow> distinct (visited_states (initial ?S) p)"
  proof -
    fix p assume "path ?S (initial ?S) p"
    show "distinct (visited_states (initial ?S) p)"
      using s_states_induces_state_separator_helper_distinct_paths[OF \<open>path ?S (initial ?S) p\<close>] by assumption
  qed
  then show ?thesis unfolding acyclic.simps by blast
qed
  
  


(*



lemma s_states_induces_state_separator_helper_h_prefix :
  assumes "t \<in> h \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))),
                      inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                      outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                      transitions = 
                         filter 
                           (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions (product (from_FSM M q1) (from_FSM M q2))) \<rparr>"
    (is "t \<in> h ?S")
  shows "t_target t \<in> set (map fst (s_states (product (from_FSM M q1) (from_FSM M q2)) k))" 
proof -
*)



(* slightly modified version *)
definition induces_state_separator_for_prod :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a, 'b) FSM_scheme \<Rightarrow> bool" where
  "induces_state_separator_for_prod M q1 q2 S = (
    is_submachine S (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))
    \<and> single_input S
    \<and> acyclic S
    \<and> (\<forall> qq \<in> nodes S . deadlock_state S qq \<longrightarrow> (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = fst qq \<and> t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) )
    \<and> retains_outputs_for_states_and_inputs (product (from_FSM M q1) (from_FSM M q2)) S
)"




lemma s_states_last_ex_k :
  assumes "qqx \<in> set (s_states M k)"  
  shows "\<exists> k' . s_states M (Suc k') = (s_states M k') @ [qqx]"
proof -
  obtain k' where "k'\<le>k" and "0 < k'" and "qqx = last (s_states M k')" 
                  "(\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (s_states M k''))"
    using s_states_last_ex[OF assms] by blast

  have "k' = (LEAST k' . qqx \<in> set (s_states M k'))"
    by (metis \<open>0 < k'\<close> \<open>\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (s_states M k'')\<close> \<open>qqx = last (s_states M k')\<close> assms nat_neq_iff s_states_last_ex s_states_last_least)

  from \<open>0 < k'\<close> obtain k'' where Suc: "k' = Suc k''"
    using gr0_conv_Suc by blast 

  then have "qqx = last (s_states M (Suc k''))"
    using \<open>qqx = last (s_states M k')\<close> by auto
  have "Suc k'' = (LEAST k' . qqx \<in> set (s_states M k'))"
    using \<open>k' = (LEAST k' . qqx \<in> set (s_states M k'))\<close> Suc by auto
  then have "qqx \<notin> set (s_states M k'')"
    by (metis lessI not_less_Least)
  then have "(s_states M (Suc k'')) \<noteq> (s_states M k'')"
    using \<open>Suc k'' = (LEAST k' . qqx \<in> set (s_states M k'))\<close>
    by (metis Suc Suc_neq_Zero \<open>k' \<le> k\<close> \<open>qqx = last (s_states M (Suc k''))\<close> assms last_in_set s_states_prefix take_eq_Nil)

  have "s_states M (Suc k'') = s_states M k'' @ [qqx]"
    by (metis \<open>qqx = last (s_states M (Suc k''))\<close> \<open>s_states M (Suc k'') \<noteq> s_states M k''\<close> last_snoc s_states_last)
  then show ?thesis by blast
qed




(* TODO: remove repetitions and results in x = 0 that can be replaced by _helper lemmata *)
lemma s_states_induces_state_separator :
  assumes "(s_states (product (from_FSM M q1) (from_FSM M q2)) k) \<noteq> []" 
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
  and "q1 \<noteq> q2"
shows "induces_state_separator_for_prod M q1 q2 \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                                                  inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                                                  outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                                                  transitions = 
                                                     filter 
                                                       (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                                                  (wf_transitions (product (from_FSM M q1) (from_FSM M q2))),
                                                  \<dots> = more M\<rparr>"
using assms(1) proof (induction k rule: less_induct)
  case (less x)
  then show ?case proof (cases x)
    case 0
    then have "s_states (product (from_FSM M q1) (from_FSM M q2)) x = s_states (product (from_FSM M q1) (from_FSM M q2)) 0"
              "s_states (product (from_FSM M q1) (from_FSM M q2)) 0 \<noteq> []"
      using less.prems by auto

    let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"
    let ?S = " \<lparr> initial = fst (last (s_states ?PM 0)),
                                     inputs = inputs ?PM,
                                     outputs = outputs ?PM,
                                     transitions = 
                                        filter 
                                          (\<lambda>t . \<exists> qqx \<in> set (s_states ?PM 0) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                                          (wf_transitions ?PM), \<dots> = more M \<rparr>"
  
    (* avoid handling the entire term of ?S *)
    obtain S where "S = ?S" by blast
    
    obtain qx where qx_def: "s_states ?PM 0 = [qx]"
      using \<open>s_states ?PM 0 \<noteq> []\<close> unfolding s_states.simps
      by (metis (mono_tags, lifting) option.case_eq_if) 
    then have "(s_states ?PM 0) ! 0 = qx" and "last (s_states ?PM 0) = qx"
      by auto
    then have "initial ?S = fst qx"
      by auto
      
    have "0 < length (s_states ?PM 0)"
      using less 0 by blast
    have "fst qx \<in> nodes ?PM"
      using s_states_index_properties(1)[OF \<open>0 < length (s_states ?PM 0)\<close>] \<open>(s_states ?PM 0) ! 0 = qx\<close> by auto
    have "snd qx \<in> set (inputs ?PM)"
      using s_states_index_properties(2)[OF \<open>0 < length (s_states ?PM 0)\<close>] \<open>(s_states ?PM 0) ! 0 = qx\<close> by auto 
    then have "snd qx \<in> set (inputs M)"
      by (simp add: product_simps(2) from_FSM_simps(2))
    have "\<not>(\<exists> t \<in> h ?PM. t_source t = fst qx \<and> t_input t = snd qx)"
      using s_states_index_properties(4)[OF \<open>0 < length (s_states ?PM 0)\<close>] \<open>(s_states ?PM 0) ! 0 = qx\<close>
      by (metis length_pos_if_in_set less_numeral_extra(3) list.size(3) take_eq_Nil) 
  
    have "(last (s_states (product (from_FSM M q1) (from_FSM M q2)) 0)) = qx"
      using qx_def 
      by (metis last.simps)  
  
    (* is_submachine *)
    let ?PS = "product (from_FSM M (fst (fst qx))) (from_FSM M (snd (fst qx)))" 
    have "initial ?S = initial ?PS"
      using \<open>(last (s_states (product (from_FSM M q1) (from_FSM M q2)) 0)) = qx\<close>
      by (simp add: from_FSM_simps(1) product_simps(1)) 
    moreover have "inputs ?S = inputs ?PS"
      by (simp add: from_FSM_simps(2) product_simps(2)) 
    moreover have "outputs ?S = outputs ?PS"
      by (simp add: from_FSM_simps(3) product_simps(3)) 
    moreover have "h ?S \<subseteq> h ?PS"
    proof -
      have "initial ?S \<in> nodes ?PS"
        using calculation(1) nodes.initial
        by (metis (no_types, lifting)) 
      have *: "set (transitions ?S) \<subseteq> set (transitions (from_FSM ?PM (fst qx)))"
        by (metis (no_types, lifting) filter_filter filter_is_subset from_FSM_transitions select_convs(4) wf_transitions.simps)
      have **: "h ?PS = h (from_FSM ?PM (fst qx))"
        using \<open>fst qx \<in> nodes ?PM\<close> from_product_from_h by (metis prod.collapse)
      show ?thesis
        by (metis (no_types, lifting) "*" "**" \<open>last (s_states (product (from_FSM M q1) (from_FSM M q2)) 0) = qx\<close> from_FSM_simps(1) from_FSM_simps(2) from_FSM_simps(3) nodes.simps select_convs(1) select_convs(2) select_convs(3) transition_subset_h) 
    qed
    ultimately have is_sub : "is_submachine ?S ?PS"
      unfolding is_submachine.simps by blast
  
  
    (* single_input *)
  
    have is_single_input : "single_input ?S" 
      using qx_def unfolding single_input.simps by auto
  
  
  
    (* acyclic *)
  
    from qx_def have qx_find : "find
                (\<lambda>qx. \<not> (\<exists>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                          t_source t = fst qx \<and> t_input t = snd qx))
                 (concat
                   (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                     (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) = Some qx "
      unfolding s_states.simps 
      by (metis (mono_tags, lifting) \<open>s_states ?PM 0 = [qx]\<close> \<open>s_states ?PM 0 \<noteq> []\<close>)
  
  
    have "transitions ?S = filter
                           (\<lambda>t. t_source t = fst qx \<and> t_input t = snd qx)
                           (wf_transitions ?PM)"
      using qx_def
      by auto 
    then have "\<And> t . t \<in> set (transitions ?S) \<Longrightarrow> t \<in> h ?PM \<and> t_source t = fst qx \<and> t_input t = snd qx"
      by (metis (mono_tags, lifting) filter_set member_filter)
    then have "\<And> t . t \<in> h ?S \<Longrightarrow> t \<in> h ?PM \<and> t_source t = fst qx \<and> t_input t = snd qx"
      unfolding wf_transitions.simps
      by (metis (no_types, lifting) filter_set member_filter) 
    then have "\<And> t . t \<in> h ?S \<Longrightarrow> False"
      using find_condition[OF qx_find] by blast
    then have "h ?S = {}"
      using last_in_set by blast
    then have "\<And> p . path ?S (initial ?S) p \<Longrightarrow> set p = {}"
      using path_h[of ?S "initial ?S"]
      by (metis (no_types, lifting) subset_empty) 
    then have "L ?S = {[]}"
      unfolding LS.simps by blast
    moreover have "finite {[]}"
      by auto
    ultimately have is_acyclic: "acyclic ?S"
      using acyclic_alt_def[of ?S] by metis
  
    
    (* deadlock_states r(0)-distinguish *)
  
    
  
    from \<open>S = ?S\<close> have "\<And> p . path S (initial S) p \<Longrightarrow> p = []"
      using \<open>\<And> p . path ?S (initial ?S) p \<Longrightarrow> set p = {}\<close> by blast
    then have "{ target p (initial S) | p . path S (initial S) p } = {initial S}"
      unfolding target.simps visited_states.simps by auto
    then have "nodes S = {initial S}"
      using nodes_set_alt_def[of S] by blast
    then have "nodes S = {fst qx}"
      using \<open>initial ?S = fst qx\<close> \<open>S = ?S\<close> by metis
    then have "(\<forall>qq\<in>nodes S.
            deadlock_state S qq \<longrightarrow>
              (\<exists>x\<in>set (inputs M).
                  \<not> (\<exists>t1\<in>set (wf_transitions M).
                         \<exists>t2\<in>set (wf_transitions M).
                            t_source t1 = fst qq \<and>
                            t_source t2 = snd qq \<and>
                            t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)))"
      using product_deadlock[OF find_condition[OF qx_find] \<open>fst qx \<in> nodes ?PM\<close> \<open>snd qx \<in> set (inputs M)\<close>] 
            \<open>snd qx \<in> set (inputs M)\<close>
      by auto 
    then have has_deadlock_property: "(\<forall>qq\<in>nodes ?S.
            deadlock_state ?S qq \<longrightarrow>
              (\<exists>x\<in>set (inputs M).
                  \<not> (\<exists>t1\<in>set (wf_transitions M).
                         \<exists>t2\<in>set (wf_transitions M).
                            t_source t1 = fst qq \<and>
                            t_source t2 = snd qq \<and>
                            t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)))"
      using \<open>S = ?S\<close> by blast
  
  
    (* retains outputs *)
  
    have retains_outputs : "retains_outputs_for_states_and_inputs ?PM ?S"
      unfolding retains_outputs_for_states_and_inputs_def
      using \<open>\<And>t. t \<in> set (wf_transitions \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) 0)), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) 0). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>) \<Longrightarrow> False\<close> by blast 
    
  
    (* collect properties *)
  
    show ?thesis 
      unfolding induces_state_separator_for_prod_def
      using is_sub
            is_single_input
            is_acyclic
            has_deadlock_property
            retains_outputs
      using \<open>initial ?S = fst qx\<close> \<open>s_states ?PM x = s_states ?PM 0\<close> by presburger 

  next
    case (Suc k)

    then show ?thesis proof (cases "length (s_states (product (from_FSM M q1) (from_FSM M q2)) x) < x")
      case True
      then have "s_states (product (from_FSM M q1) (from_FSM M q2)) x = s_states (product (from_FSM M q1) (from_FSM M q2)) k"
        using Suc
        by (metis le_SucI less_Suc_eq_le nat_le_linear s_states_prefix take_all) 
      
      show ?thesis
        using Suc \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) x = s_states (product (from_FSM M q1) (from_FSM M q2)) k\<close> less.IH less.prems lessI by presburger
    next
      case False

      then have "s_states (product (from_FSM M q1) (from_FSM M q2)) x = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)"
                "s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k) \<noteq> []"
        using Suc less.prems by auto

      then have "s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k) \<noteq> s_states (product (from_FSM M q1) (from_FSM M q2)) k"
        by (metis False Suc le_imp_less_Suc s_states_length)

      let ?PM = "product (from_FSM M q1) (from_FSM M q2)"
      let ?S = "\<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))),
                  inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                  outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                  transitions = 
                     filter 
                       (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                  (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M \<rparr>"


      obtain qx where "s_states ?PM (Suc k) = s_states ?PM k @ [qx]"
                  and "(\<forall>qx'\<in>set (s_states ?PM k). fst qx \<noteq> fst qx')"
                  and "(\<forall>t\<in> h ?PM.
                           t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          (\<exists>qx'\<in>set (s_states ?PM k). fst qx' = t_target t))"
                   and "fst qx \<in> nodes ?PM"
                   and "snd qx \<in> set (inputs ?PM)"
        using s_states_last[OF \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k) \<noteq> s_states (product (from_FSM M q1) (from_FSM M q2)) k\<close>]
        by blast
      then have "qx = (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)))"
        by auto

      

      (* avoid handling the entire term of ?S *)
      obtain S where "S = ?S" by blast
    
      
    
      (* single input *)
      have is_single_input : "single_input ?S"
        using s_states_induces_state_separator_helper_single_input by metis
      (* retains outputs *)
      have retains_outputs : "retains_outputs_for_states_and_inputs ?PM ?S"
        using s_states_induces_state_separator_helper_retains_outputs by metis
      (* acyclic *)
      have is_acyclic : "acyclic ?S"
        using s_states_induces_state_separator_helper_acyclic by metis

      (* is_submachine *)
      let ?PS = "product (from_FSM M (fst (fst qx))) (from_FSM M (snd (fst qx)))" 
      have "initial ?S = initial ?PS"
        using \<open>qx = (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)))\<close>
        by (simp add: from_FSM_simps(1) product_simps(1)) 
      moreover have "inputs ?S = inputs ?PS"
        by (simp add: from_FSM_simps(2) product_simps(2)) 
      moreover have "outputs ?S = outputs ?PS"
        by (simp add: from_FSM_simps(3) product_simps(3)) 
      moreover have "h ?S \<subseteq> h ?PS"
      proof -
        have "initial ?S \<in> nodes ?PS"
          using calculation(1) nodes.initial
          by (metis (no_types, lifting)) 
        have *: "set (transitions ?S) \<subseteq> set (transitions (from_FSM ?PM (fst qx)))"
          by (metis (no_types, lifting) filter_filter filter_is_subset from_FSM_transitions select_convs(4) wf_transitions.simps)
        have **: "h ?PS = h (from_FSM ?PM (fst qx))"
          using \<open>fst qx \<in> nodes ?PM\<close> from_product_from_h by (metis prod.collapse)
        show ?thesis
          by (metis (no_types, lifting) "*" "**" \<open>qx = last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))\<close> from_FSM_simps(1) from_FSM_simps(2) from_FSM_simps(3) nodes.simps select_convs(1) select_convs(2) select_convs(3) transition_subset_h) 
      qed
      ultimately have is_sub : "is_submachine ?S ?PS"
        unfolding is_submachine.simps by blast
    

      (* has deadlock property *)
      have "\<And> qq . qq \<in> nodes ?S \<Longrightarrow> deadlock_state ?S qq \<Longrightarrow> (\<exists>x\<in>set (inputs M).
                                                                \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                                       \<exists>t2\<in>set (wf_transitions M).
                                                                          t_source t1 = fst qq \<and>
                                                                          t_source t2 = snd qq \<and>
                                                                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))"
      proof -
        fix qq assume "qq \<in> nodes ?S"
                  and "deadlock_state ?S qq"

        have "qq = fst qx \<or> (\<exists> t \<in> h ?S . t_target t = qq)" 
          using \<open>qq \<in> nodes ?S\<close>
                nodes_from_transition_targets[of ?S]
          by (metis (no_types, lifting) \<open>qx = last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))\<close> nodes_initial_or_target select_convs(1)) 
        
        have "qq \<in> set (map fst (s_states ?PM (Suc k)))"
        proof (cases "qq = fst qx")
          case True
          then show ?thesis using \<open>qx = last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))\<close>
            using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k) \<noteq> []\<close> by auto 
        next
          case False
          then obtain t where "t \<in> h ?S" and "t_target t = qq"
            using \<open>qq = fst qx \<or> (\<exists> t \<in> h ?S . t_target t = qq)\<close> by blast

          have "(t_source t, t_input t) \<in> set (s_states ?PM (Suc k))"
            using s_states_induces_state_separator_helper_h[OF \<open>t \<in> h ?S\<close>] by assumption
          have "t \<in> h ?PM"
            using \<open>t \<in> h ?S\<close>
          proof -
            have f1: "t \<in> set (wf_transitions \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>p. \<exists>pa. pa \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)) \<and> t_source p = fst pa \<and> t_input p = snd pa) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>)"
              by (metis \<open>t \<in> set (wf_transitions \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>)\<close>)
            have "set (wf_transitions \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>p. \<exists>pa. pa \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)) \<and> t_source p = fst pa \<and> t_input p = snd pa) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>) \<subseteq> set (wf_transitions (product (from_FSM M (fst (fst qx))) (from_FSM M (snd (fst qx)))))"
              by (metis (full_types) \<open>set (wf_transitions \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>) \<subseteq> set (wf_transitions (product (from_FSM M (fst (fst qx))) (from_FSM M (snd (fst qx)))))\<close>)
            then have f2: "t \<in> set (wf_transitions (product (from_FSM M (fst (fst qx))) (from_FSM M (snd (fst qx)))))"
              using f1 by blast
            have "(fst (fst qx), snd (fst qx)) = fst qx"
              by simp
            then show ?thesis
              using f2 by (metis (no_types) \<open>fst qx \<in> nodes (product (from_FSM M q1) (from_FSM M q2))\<close> product_from_transition_shared_node)
          qed 

          have "set (map fst (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k - 1))) \<subseteq> set (map fst (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)))"
            using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k) = s_states (product (from_FSM M q1) (from_FSM M q2)) k @ [qx]\<close> by auto
          then show ?thesis 
            using s_states_transition_target(1)[OF \<open>(t_source t, t_input t) \<in> set (s_states ?PM (Suc k))\<close> \<open>t \<in> h ?PM\<close>]
                  \<open>t_target t = qq\<close>
            by blast  
        qed


        (* TODO: extract and move *)
        moreover have "\<And> xs x . x \<in> set (map fst xs) \<Longrightarrow> (\<exists> y . (x,y) \<in> set xs)"
          by auto

        

        ultimately obtain x where "(qq,x) \<in> set (s_states ?PM (Suc k))"
          by auto 

        then obtain i where "i < length (s_states ?PM (Suc k))" and "(s_states ?PM (Suc k)) ! i = (qq,x)"
          by (meson in_set_conv_nth)

        have "qq \<in> nodes ?PM"
          using s_states_index_properties(1)[OF \<open>i < length (s_states ?PM (Suc k))\<close>] \<open>(s_states ?PM (Suc k)) ! i = (qq,x)\<close> by auto
        have "x \<in> set (inputs ?PM)"
          using s_states_index_properties(2)[OF \<open>i < length (s_states ?PM (Suc k))\<close>] \<open>(s_states ?PM (Suc k)) ! i = (qq,x)\<close> by auto
        then have "x \<in> set (inputs M)"
          by (simp add: from_FSM_product_inputs)
        have "\<forall>qx'\<in> set (take i (s_states ?PM (Suc k))). qq \<noteq> fst qx'"
          using s_states_index_properties(3)[OF \<open>i < length (s_states ?PM (Suc k))\<close>] \<open>(s_states ?PM (Suc k)) ! i = (qq,x)\<close> by auto
        have "\<forall> t \<in> h ?PM.
                 t_source t = qq \<and>
                 t_input t = x \<longrightarrow>
                 (\<exists> qx' \<in> set (take i (s_states ?PM (Suc k))). fst qx' = t_target t)"
          using s_states_index_properties(4)[OF \<open>i < length (s_states ?PM (Suc k))\<close>] \<open>(s_states ?PM (Suc k)) ! i = (qq,x)\<close> by auto
        then have "\<forall> t \<in> h ?PM.
                 t_source t = qq \<and>
                 t_input t = x \<longrightarrow>
                 (\<exists> qx' \<in> set (s_states ?PM (Suc k)). fst qx' = t_target t)"
          by (meson in_set_takeD) 
          

        have "\<not> (\<exists> t \<in> h ?PM. t_source t = qq \<and> t_input t = x)"
        proof 
          assume "(\<exists> t \<in> h ?PM. t_source t = qq \<and> t_input t = x)"
          then obtain t where "t \<in> h ?PM" and "t_source t = qq" and "t_input t = x" by blast
          then have "\<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)).
                             t_source t = fst qqx \<and> t_input t = snd qqx"
            using \<open>(qq,x) \<in> set (s_states ?PM (Suc k))\<close> prod.collapse[of "(qq,x)"]
            by force 
          then have "t \<in> set (transitions ?S)"
            using \<open>t \<in> h ?PM\<close>
            by simp 
          then have "t \<in> h ?S"
            using \<open>t \<in> h ?PM\<close>
            by (metis (no_types, lifting) \<open>qq \<in> nodes \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k)). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>\<close> \<open>t_source t = qq\<close> select_convs(2) select_convs(3) wf_transition_simp) 
          then have "\<not> (deadlock_state ?S qq)"
            unfolding deadlock_state.simps using \<open>t_source t = qq\<close>
            by blast 
          then show "False"
            using \<open>deadlock_state ?S qq\<close> by blast
        qed

        then have "\<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M.
                                t_source t1 = fst qq \<and>
                                t_source t2 = snd qq \<and>
                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
          using product_deadlock[OF _ \<open>qq \<in> nodes ?PM\<close> \<open>x \<in> set (inputs M)\<close>] by blast
        then show "(\<exists>x\<in>set (inputs M).
                    \<not> (\<exists>t1\<in>set (wf_transitions M).
                           \<exists>t2\<in>set (wf_transitions M).
                              t_source t1 = fst qq \<and>
                              t_source t2 = snd qq \<and>
                              t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))"
          using \<open>x \<in> set (inputs M)\<close> by blast
      qed


      then have has_deadlock_property: "(\<forall>qq\<in>nodes ?S.
          deadlock_state ?S qq \<longrightarrow>
            (\<exists>x\<in>set (inputs M).
                \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = fst qq \<and>
                          t_source t2 = snd qq \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)))"
      by blast
      
    
    
      (* collect properties *)
      have "initial ?S = fst qx"
        by (metis \<open>qx = last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc k))\<close> select_convs(1))
        

      show ?thesis 
        unfolding induces_state_separator_for_prod_def
        using is_sub
              is_single_input
              is_acyclic
              has_deadlock_property
              retains_outputs
        using \<open>initial ?S = fst qx\<close>  \<open>s_states ?PM x = s_states ?PM (Suc k)\<close>
        by presburger 
    qed
  qed
qed




definition s_states_deadlock_input :: "('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> 'a, 'b) FSM_scheme \<Rightarrow> ('a \<times> 'a) \<Rightarrow> Input option" where
  "s_states_deadlock_input M S qq = (if (qq \<in> nodes S \<and> deadlock_state S qq) 
    then (find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = fst qq \<and> t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M))
    else None)"




definition state_separator_from_product_submachine :: "('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> 'a, 'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme" where
  "state_separator_from_product_submachine M S =
    \<lparr> initial = Inl (initial S),
      inputs = inputs M,
      outputs = outputs M,
      transitions = (let
                        t_old = (map shift_Inl (wf_transitions S));
                    t_left = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                                   (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                           (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                        (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))));
                    t_right = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                                     (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                             (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                          (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
        in (t_old 
            @ t_left 
            @ t_right 
            @ (filter (\<lambda>t . t \<notin> set t_old \<union> set t_left \<union> set t_right \<and>
                              (\<exists> t' \<in> set t_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                       (distinguishing_transitions_left M (fst (initial S)) (snd (initial S))))     
            @ (filter (\<lambda>t . t \<notin> set t_old \<union> set t_left \<union> set t_right \<and>
                              (\<exists> t' \<in> set t_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                       (distinguishing_transitions_right M (fst (initial S)) (snd (initial S)))))), 
                                        
      \<dots> = more M \<rparr>"

(*
transitions = (let
                        t_old = (map shift_Inl (wf_transitions S));
                    t_left = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                                   (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                           (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                        (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))));
                    t_right = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                                     (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                             (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                          (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
        in (t_old 
            @ t_left 
            @ t_right 
            @ (filter (\<lambda>t . t \<notin> set t_old \<union> set t_left \<union> set t_right \<and>
                              (\<exists> t' \<in> set t_old \<union> set t_left \<union> set t_right . t_source t = t_source t' \<and> t_input t = t_input t'))
                       (distinguishing_transitions_left M (fst (initial S)) (snd (initial S))))     
            @ (filter (\<lambda>t . t \<notin> set t_old \<union> set t_left \<union> set t_right \<and>
                              (\<exists> t' \<in> set t_old \<union> set t_left \<union> set t_right . t_source t = t_source t' \<and> t_input t = t_input t'))
                       (distinguishing_transitions_right M (fst (initial S)) (snd (initial S)))))),
*)

(*
transitions = (let
                        t_old = (map shift_Inl (wf_transitions S));
                    t_left = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                                   (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                           (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                        (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))));
                    t_right = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                                     (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                             (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                          (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
        in (t_old @ t_left @ t_right @ (filter (\<lambda>t . t \<notin> set t_old \<union> set t_left \<union> set t_right \<and>
                                                      (\<exists> t' \<in> set t_old \<union> set t_left \<union> set t_right . t_source t = t_source t' \<and> t_input t = t_input t'))
                                               (wf_transitions (canonical_separator M (fst (initial S)) (snd (initial S))))))),
*)

(*
distinguishing_transitions_left M ?q1 ?q2
*)

(* TODO: move *)
lemma max_length_elem :
  fixes xs :: "'a list set"
  assumes "finite xs"
  and     "xs \<noteq> {}"
shows "\<exists> x \<in> xs . \<not>(\<exists> y \<in> xs . length y > length x)" 
using assms proof (induction xs)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case proof (cases "F = {}")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> F" and "\<not>(\<exists> y' \<in> F . length y' > length y)"
      using insert.IH by blast
    then show ?thesis using dual_order.strict_trans by (cases "length x > length y"; auto)
  qed
qed

(* TODO: move *)
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

(* TODO: move *)
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



lemma state_separator_from_induces_state_separator :
  fixes M :: "('a,'b) FSM_scheme"
  assumes "induces_state_separator M S"
  and "fst (initial S) \<in> nodes M"
  and "snd (initial S) \<in> nodes M"
  and "fst (initial S) \<noteq> snd (initial S)"
  and "completely_specified M"
  shows "is_state_separator_from_canonical_separator
            (canonical_separator M (fst (initial S)) (snd (initial S)))
            (fst (initial S))
            (snd (initial S))
            (state_separator_from_product_submachine M S)"

proof -

  let ?q1 = "fst (initial S)"
  let ?q2 = "snd (initial S)"
  let ?CSep = "canonical_separator M ?q1 ?q2"
  let ?SSep = "state_separator_from_product_submachine M S"
  let ?PM = "(product (from_FSM M ?q1) (from_FSM M ?q2))"


  
  obtain SSep where ssep_var: "SSep = ?SSep" by blast
  obtain CSep where csep_var: "CSep = ?CSep" by blast

  have "is_submachine S ?PM"
   and "single_input S"
   and "acyclic S"
   and dl: "\<And> qq . qq \<in> nodes S \<Longrightarrow>
          deadlock_state S qq \<Longrightarrow>
          (\<exists>x\<in>set (inputs M).
              \<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))"
   and "retains_outputs_for_states_and_inputs ?PM S"
    using assms unfolding induces_state_separator_def by blast+

  have "initial S = initial ?PM"
       "inputs S = inputs ?PM"
       "outputs S = outputs ?PM"
       "h S \<subseteq> h ?PM"
    using \<open>is_submachine S ?PM\<close> unfolding is_submachine.simps by blast+

  have "set (map shift_Inl (wf_transitions S)) \<subseteq> set (transitions ?SSep)"
    unfolding state_separator_from_product_submachine_def
    by (metis list_prefix_subset select_convs(4)) 
  moreover have "set (map shift_Inl (wf_transitions S)) \<subseteq> set (map shift_Inl (wf_transitions ?PM))"
    using \<open>h S \<subseteq> h ?PM\<close> by auto
  moreover have "set (map shift_Inl (wf_transitions ?PM)) \<subseteq> set (transitions ?CSep)"
    unfolding canonical_separator_def
    by (metis canonical_separator_product_transitions_subset canonical_separator_simps(4) select_convs(4))
  ultimately have subset_shift: "set (map shift_Inl (wf_transitions S)) \<subseteq> set (transitions ?CSep)"
    by blast


  have subset_left: "set (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                           (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
       \<subseteq> set (distinguishing_transitions_left M ?q1 ?q2)"
  proof -
    have *: "\<And> qq t . qq \<in> nodes ?PM \<Longrightarrow> t \<in> h M \<Longrightarrow> t_source t = fst qq \<Longrightarrow> s_states_deadlock_input M S qq = Some (t_input t) 
            \<Longrightarrow> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd qq \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
    proof -
      fix qq t assume "qq \<in> nodes ?PM" and "t \<in> h M" and "t_source t = fst qq" and "s_states_deadlock_input M S qq = Some (t_input t)"


      have "qq \<in> nodes S" and "deadlock_state S qq" and f: "find
         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
         (inputs M) = Some (t_input t)"
        using \<open>s_states_deadlock_input M S qq = Some (t_input t)\<close> unfolding s_states_deadlock_input_def
        
        by (meson option.distinct(1))+

      have "qq \<in> nodes S" and "deadlock_state S qq" and f: "find
         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
         (inputs M) = Some (t_input t)"
        using \<open>s_states_deadlock_input M S qq = Some (t_input t)\<close> unfolding s_states_deadlock_input_def
        
        by (meson option.distinct(1))+
      have "\<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2)"
        using find_condition[OF f] by blast
      then have "\<not> (\<exists>t2\<in>set (wf_transitions M).
                        t_source t2 = snd qq \<and> t_input t2 = t_input t \<and> t_output t = t_output t2)"
        using \<open>t \<in> h M\<close> \<open>t_source t = fst qq\<close> by blast
      moreover have "\<And> t' . t' \<in> set (transitions M) \<Longrightarrow> t_source t' = snd qq \<Longrightarrow> t_input t' = t_input t \<Longrightarrow> t_output t' = t_output t\<Longrightarrow> t' \<in> h M"
      proof -
        fix t' assume "t' \<in> set (transitions M)" and "t_source t' = snd qq" and "t_input t' = t_input t" and "t_output t' = t_output t"        

        have "snd qq \<in> nodes M"
          using \<open>qq \<in> nodes ?PM\<close>  product_nodes[of "from_FSM M ?q1" "from_FSM M ?q2"] from_FSM_nodes[OF assms(3)] by force
        then have "t_source t' \<in> nodes M"
          using \<open>t_source t' = snd qq\<close> by auto
        then show "t' \<in> h M"
          using \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> \<open>t \<in> h M\<close>
          by (simp add: \<open>t' \<in> set (transitions M)\<close>) 
      qed

      ultimately show "\<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd qq \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
        by auto
    qed

    moreover have "\<And> qqt . qqt \<in> set (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))
                    \<Longrightarrow> fst qqt \<in> nodes ?PM \<and> snd qqt \<in> h M"
      using concat_pair_set[of "wf_transitions M" "(nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))"]
            nodes_code[of ?PM]
      by blast 
    ultimately have **: "\<And> qqt . qqt \<in> set (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))
                  \<Longrightarrow> t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))
                  \<Longrightarrow> t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
      by blast
            
    
    have filter_strengthening:  "\<And> xs f1 f2 . (\<And> x .x \<in> set xs \<Longrightarrow> f1 x \<Longrightarrow> f2 x) \<Longrightarrow> set (filter f1 xs) \<subseteq> set (filter f2 xs)"
      by auto

    have ***: "set ((filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
                    \<subseteq> set (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) (nodes_from_distinct_paths (product (from_FSM M ?q1) (from_FSM M ?q2))))))"
      using filter_strengthening[of "(concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))"
                                    "\<lambda>qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))"
                                    "\<lambda>qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))", OF **] by blast
    
    have map_subset: "\<And> xs xs' f . set xs \<subseteq> set xs' \<Longrightarrow> set (map f xs) \<subseteq> set (map f xs')"
      by auto

    show ?thesis 
      using map_subset[OF ***, of "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))"]
      unfolding distinguishing_transitions_left_def  by blast
  qed


  have subset_right: "set (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                           (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
       \<subseteq> set (distinguishing_transitions_right M ?q1 ?q2)"
  proof -
    have *: "\<And> qq t . qq \<in> nodes ?PM \<Longrightarrow> t \<in> h M \<Longrightarrow> t_source t = snd qq \<Longrightarrow> s_states_deadlock_input M S qq = Some (t_input t) 
            \<Longrightarrow> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst qq \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
    proof -
      fix qq t assume "qq \<in> nodes ?PM" and "t \<in> h M" and "t_source t = snd qq" and "s_states_deadlock_input M S qq = Some (t_input t)"

      have "qq \<in> nodes S" and "deadlock_state S qq" and f: "find
         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
         (inputs M) = Some (t_input t)"
        using \<open>s_states_deadlock_input M S qq = Some (t_input t)\<close> unfolding s_states_deadlock_input_def
        by (meson option.distinct(1))+
      have "\<not> (\<exists>t1\<in>set (wf_transitions M).
                     \<exists>t2\<in>set (wf_transitions M).
                        t_source t1 = fst qq \<and>
                        t_source t2 = snd qq \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2)"
        using find_condition[OF f] by blast
      then have "\<not> (\<exists>t2\<in>set (wf_transitions M).
                        t_source t2 = fst qq \<and> t_input t2 = t_input t \<and> t_output t = t_output t2)"
        using \<open>t \<in> h M\<close> \<open>t_source t = snd qq\<close>
        by metis 
      moreover have "\<And> t' . t' \<in> set (transitions M) \<Longrightarrow> t_source t' = fst qq \<Longrightarrow> t_input t' = t_input t \<Longrightarrow> t_output t' = t_output t\<Longrightarrow> t' \<in> h M"
      proof -
        fix t' assume "t' \<in> set (transitions M)" and "t_source t' = fst qq" and "t_input t' = t_input t" and "t_output t' = t_output t"        

        have "fst qq \<in> nodes M"
          using \<open>qq \<in> nodes ?PM\<close>  product_nodes[of "from_FSM M ?q1" "from_FSM M ?q2"] from_FSM_nodes[OF assms(2)] by force
        then have "t_source t' \<in> nodes M"
          using \<open>t_source t' = fst qq\<close> by auto
        then show "t' \<in> h M"
          using \<open>t_input t' = t_input t\<close> \<open>t_output t' = t_output t\<close> \<open>t \<in> h M\<close>
          by (simp add: \<open>t' \<in> set (transitions M)\<close>) 
      qed

      ultimately show "\<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst qq \<and> t_input t' = t_input t \<and> t_output t' = t_output t)"
        by auto
    qed

    moreover have "\<And> qqt . qqt \<in> set (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))
                    \<Longrightarrow> fst qqt \<in> nodes ?PM \<and> snd qqt \<in> h M"
      using concat_pair_set[of "wf_transitions M" "(nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))"]
            nodes_code[of ?PM]
      by blast 
    ultimately have **: "\<And> qqt . qqt \<in> set (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))
                  \<Longrightarrow> t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))
                  \<Longrightarrow> t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
      by blast
            
    
    have filter_strengthening:  "\<And> xs f1 f2 . (\<And> x .x \<in> set xs \<Longrightarrow> f1 x \<Longrightarrow> f2 x) \<Longrightarrow> set (filter f1 xs) \<subseteq> set (filter f2 xs)"
      by auto

    have ***: "set ((filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
                    \<subseteq> set (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) (nodes_from_distinct_paths (product (from_FSM M ?q1) (from_FSM M ?q2))))))"
      using filter_strengthening[of "(concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))"
                                    "\<lambda>qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))"
                                    "\<lambda>qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))", OF **] by blast
    
    have map_subset: "\<And> xs xs' f . set xs \<subseteq> set xs' \<Longrightarrow> set (map f xs) \<subseteq> set (map f xs')"
      by auto

    show ?thesis 
      using map_subset[OF ***, of "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))"]
      unfolding distinguishing_transitions_right_def  by blast
  qed
        
  


  let ?d_old = "map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) (wf_transitions S)"
  let ?d_left = "map (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                   (filter
                     (\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                            s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))
                     (concat
                       (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                         (nodes_from_distinct_paths
                           (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))"
  let ?d_right = "map (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                   (filter
                     (\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                            s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))
                     (concat
                       (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                         (nodes_from_distinct_paths
                           (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))"

  let ?d_old_dist_left = "(filter (\<lambda>t . t \<notin> set ?d_old \<union> set ?d_left \<union> set ?d_right \<and>
                                          (\<exists> t' \<in> set ?d_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                                   (distinguishing_transitions_left M (fst (initial S)) (snd (initial S))))"

  let ?d_old_dist_right = "(filter (\<lambda>t . t \<notin> set ?d_old \<union> set ?d_left \<union> set ?d_right \<and>
                                          (\<exists> t' \<in> set ?d_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                                   (distinguishing_transitions_right M (fst (initial S)) (snd (initial S))))"

  
  
  obtain d_right::"(('a \<times> 'a) + 'a) Transition list"  where d_right_var: "d_right = ?d_right" by blast
  obtain d_left::"(('a \<times> 'a) + 'a) Transition list"  where d_left_var: "d_left = ?d_left" by blast
  obtain d_old::"(('a \<times> 'a) + 'a) Transition list"  where d_old_var: "d_old = ?d_old" by blast
  obtain d_old_dist_left::"(('a \<times> 'a) + 'a) Transition list" where d_old_dist_left_var: "d_old_dist_left = (filter (\<lambda>t . t \<notin> set d_old \<union> set d_left \<union> set d_right \<and>
                                          (\<exists> t' \<in> set d_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                                   (distinguishing_transitions_left M (fst (initial S)) (snd (initial S))))" by blast
  obtain d_old_dist_right::"(('a \<times> 'a) + 'a) Transition list" where d_old_dist_right_var: "d_old_dist_right = (filter (\<lambda>t . t \<notin> set d_old \<union> set d_left \<union> set d_right \<and>
                                          (\<exists> t' \<in> set d_old . t_source t = t_source t' \<and> t_input t = t_input t'))
                                   (distinguishing_transitions_right M (fst (initial S)) (snd (initial S))))" by blast

  
      



  have "set ((map shift_Inl (wf_transitions S))
                    @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))
                           (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))))
                    @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))
                           (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) 
                                   (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (wf_transitions M)) 
                                                (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))))
        \<subseteq> set (shifted_transitions M ?q1 ?q2
                @ distinguishing_transitions_left M ?q1 ?q2
                @ distinguishing_transitions_right M ?q1 ?q2)"
    using subset_shift subset_right subset_left
  proof -
    have "set (map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) (wf_transitions S)) \<subseteq> set (shifted_transitions M (fst (initial S)) (snd (initial S)))"
      by (metis (no_types) \<open>set (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) (wf_transitions S)) \<subseteq> set (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) (wf_transitions (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))\<close> shifted_transitions_def)
    then show ?thesis
      using list_append_subset3 subset_left subset_right by blast
  qed 
  then have "set (d_old @ d_left @ d_right) \<subseteq> set (shifted_transitions M ?q1 ?q2
                @ distinguishing_transitions_left M ?q1 ?q2
                @ distinguishing_transitions_right M ?q1 ?q2)"
    using d_old_var d_left_var d_right_var by blast
  then have "set (d_old @ d_left @ d_right) \<subseteq> set (transitions ?CSep)"
    unfolding canonical_separator_def by auto
  
  have "set ?d_old_dist_left \<subseteq> set (transitions ?CSep)"
  proof 
    fix t assume "t \<in> set ?d_old_dist_left"
    have *: "\<And> f xs x . x \<in> set (filter f xs) \<Longrightarrow> x \<in> set xs" by auto
    show "t \<in> set (transitions ?CSep)" using *[OF \<open>t \<in> set ?d_old_dist_left\<close>] unfolding canonical_separator_def by auto
  qed
  then have "set d_old_dist_left \<subseteq> set (transitions ?CSep)"
    using d_old_dist_left_var d_old_var d_left_var d_right_var by blast
  then have "set (d_old @ d_left @ d_right @ d_old_dist_left) \<subseteq> set (transitions ?CSep)"
    using \<open>set (d_old @ d_left @ d_right) \<subseteq> set (transitions ?CSep)\<close> by force

  have "set ?d_old_dist_right \<subseteq> set (transitions ?CSep)"
  proof 
    fix t assume "t \<in> set ?d_old_dist_right"
    have *: "\<And> f xs x . x \<in> set (filter f xs) \<Longrightarrow> x \<in> set xs" by auto
    show "t \<in> set (transitions ?CSep)" using *[OF \<open>t \<in> set ?d_old_dist_right\<close>] unfolding canonical_separator_def by auto
  qed
  then have "set d_old_dist_right \<subseteq> set (transitions ?CSep)"
    using d_old_dist_right_var d_old_var d_left_var d_right_var by blast
  then have "set (d_old @ d_left @ d_right @ d_old_dist_left @ d_old_dist_right) \<subseteq> set (transitions ?CSep)"
    using \<open>set (d_old @ d_left @ d_right @ d_old_dist_left) \<subseteq> set (transitions ?CSep)\<close> by force

  have "set (transitions ?SSep) = set (?d_old @ ?d_left @ ?d_right @ ?d_old_dist_left @ ?d_old_dist_right)"
    unfolding Let_def state_separator_from_product_submachine_def by (simp only: select_convs)
  then have "set (transitions ?SSep) = set (d_old @ d_left @ d_right @ d_old_dist_left @ d_old_dist_right)"
    using d_old_dist_left_var d_old_dist_right_var d_old_var d_left_var d_right_var by blast
  then have "set (transitions ?SSep) \<subseteq> set (transitions ?CSep)"
    using \<open>set (d_old @ d_left @ d_right @ d_old_dist_left @ d_old_dist_right) \<subseteq> set (transitions ?CSep)\<close> by blast
  

  

  (* is_submachine *)

  have "inputs S = inputs ?PM"
    using assms(1) unfolding induces_state_separator_def is_submachine.simps
    by (simp only: from_FSM_simps(2) product_simps(2))

  have "initial ?SSep = initial ?CSep"
    unfolding canonical_separator_def state_separator_from_product_submachine_def
    by (simp only: from_FSM_simps(1) product_simps(1) select_convs prod.collapse) 
  moreover have "inputs ?SSep = inputs ?CSep"
    unfolding canonical_separator_def state_separator_from_product_submachine_def
    by (simp only: from_FSM_simps(2) product_simps(2)  select_convs)  
  moreover have "outputs ?SSep = outputs ?CSep"
    unfolding canonical_separator_def state_separator_from_product_submachine_def
    by (simp only: from_FSM_simps(3) product_simps(3)  select_convs) 
  moreover have "h ?SSep \<subseteq> h ?CSep"
    using \<open>set (transitions ?SSep) \<subseteq> set (transitions ?CSep)\<close> calculation
    by (metis nodes.initial transition_subset_h) 
  ultimately have is_sub: "is_submachine ?SSep ?CSep"
    unfolding is_submachine.simps by blast


  (* has deadlock states *)

  have isl_source: "\<And> t . t \<in> h ?SSep \<Longrightarrow> isl (t_source t)"
    using \<open>set (transitions ?SSep) \<subseteq> set (transitions ?CSep)\<close> 
    using canonical_separator_t_source_isl
    by (metis (no_types, hide_lams) subset_iff wf_transition_simp) 

  have has_deadlock_left: "deadlock_state ?SSep (Inr ?q1)" 
    using isl_source unfolding deadlock_state.simps
    by (metis sum.disc(2)) 

  have has_deadlock_right: "deadlock_state ?SSep (Inr ?q2)" 
    using isl_source unfolding deadlock_state.simps
    by (metis sum.disc(2)) 

  

  have d_left_targets: "\<And> t . t \<in> set d_left \<Longrightarrow> t_target t = Inr ?q1" 
  and  d_right_targets: "\<And> t . t \<in> set d_right \<Longrightarrow> t_target t = Inr ?q2"
  and  d_old_dist_left_targets: "\<And> t . t \<in> set d_old_dist_left \<Longrightarrow> t_target t = Inr ?q1"
  and  d_old_dist_right_targets: "\<And> t . t \<in> set d_old_dist_right \<Longrightarrow> t_target t = Inr ?q2"
  proof -
    have *: "\<And> xs t q . t \<in> set (map (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), q)) xs) \<Longrightarrow> t_target t = q" by auto
    show "\<And> t . t \<in> set d_left \<Longrightarrow> t_target t = Inr ?q1"
      using * d_left_var by blast
    show "\<And> t . t \<in> set d_right \<Longrightarrow> t_target t = Inr ?q2"
      using * d_right_var by blast

    have **: "\<And> xs t q f . t \<in> set (filter f (map (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), q)) xs)) \<Longrightarrow> t_target t = q" by auto
    show "\<And> t . t \<in> set d_old_dist_left \<Longrightarrow> t_target t = Inr ?q1"
      using ** d_old_dist_left_var unfolding distinguishing_transitions_left_def by blast
    show "\<And> t . t \<in> set d_old_dist_right \<Longrightarrow> t_target t = Inr ?q2"
      using ** d_old_dist_right_var unfolding distinguishing_transitions_right_def by blast
  qed

  

  have d_old_targets : "\<And> t . t \<in> set d_old \<Longrightarrow> isl (t_target t) \<and> (\<exists> t' \<in> h S . t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t')))"
    using d_old_var by auto

  
      
  
    
  have d_containment_var : "set (transitions SSep) = set d_old \<union> set d_left \<union> set d_right \<union> set d_old_dist_left \<union> set d_old_dist_right"
    using \<open>set (transitions ?SSep) = set (d_old @ d_left @ d_right @ d_old_dist_left @ d_old_dist_right)\<close>
    using ssep_var by auto
  then have d_containment : "set (transitions ?SSep) = set ?d_old \<union> set ?d_left \<union> set ?d_right \<union> set ?d_old_dist_left \<union> set ?d_old_dist_right"
    using ssep_var d_old_dist_left_var d_old_dist_right_var d_old_var d_left_var d_right_var by blast

  have "\<And> qs x y qt . (Inl qs,x,y,Inl qt) \<in> set d_old \<Longrightarrow> (qs,x,y,qt) \<in> h S"
    using d_old_targets
    by auto 
  moreover have "\<And> qs x y qt . (Inl qs,x,y,Inl qt) \<in> set (transitions SSep) \<Longrightarrow> (Inl qs,x,y,Inl qt) \<in> set d_old"
    using d_containment_var d_left_targets d_right_targets d_old_dist_left_targets d_old_dist_right_targets
    by fastforce 
  ultimately have d_old_origins: "\<And> qs x y qt . (Inl qs,x,y,Inl qt) \<in> h SSep \<Longrightarrow> (qs,x,y,qt) \<in> h S"
    by blast

  

  have "initial SSep = Inl (initial S)"
    using ssep_var unfolding state_separator_from_product_submachine_def
    by (simp only: select_convs)
  have "inputs SSep = inputs M"
    using ssep_var unfolding state_separator_from_product_submachine_def
    by (simp only: select_convs)
  then have "set (inputs SSep) = set (inputs S)"
    using \<open>inputs S = inputs ?PM\<close>
    by (simp add: from_FSM_product_inputs) 
  have "outputs SSep = outputs M"
    using ssep_var unfolding state_separator_from_product_submachine_def
    by (simp only: select_convs)
  then have "set (outputs SSep) = set (outputs S)"
    using \<open>outputs S = outputs ?PM\<close>
    by (simp add: from_FSM_product_outputs)   
    

  have ssep_path_from_old : "\<And> p . path S (initial S) p \<Longrightarrow> path SSep (initial SSep) (map shift_Inl p)"
  proof - 
    fix p assume "path S (initial S) p"
    then show "path SSep (initial SSep) (map shift_Inl p)" proof (induction p rule: rev_induct)
      case Nil
      then show ?case by auto 
    next
      case (snoc t p) 
      then have "path S (initial S) p" and "t \<in> h S" and "t_source t = target p (initial S)"
        by auto

      have "shift_Inl t \<in> set d_old"
        using d_old_var \<open>t \<in> h S\<close> by auto

      have "target (map shift_Inl p) (Inl (initial S)) \<in> nodes SSep"
        using snoc.IH[OF \<open>path S (initial S) p\<close>] \<open>initial SSep = Inl (initial S)\<close>
        using path_target_is_node by fastforce 
      moreover have "target (map shift_Inl p) (Inl (initial S)) = Inl (t_source t)"
        using \<open>t_source t = target p (initial S)\<close> by (cases p rule: rev_cases; auto) 
      ultimately have "Inl (t_source t) \<in> nodes SSep" 
        using \<open>t_source t = target p (initial S)\<close>
        by (metis \<open>target (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p) (Inl (initial S)) = Inl (t_source t)\<close> \<open>target (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p) (Inl (initial S)) \<in> nodes SSep\<close>)
      then have "t_source (shift_Inl t) \<in> nodes SSep"
        by auto
      moreover have "t_input (shift_Inl t) \<in> set (inputs SSep)"
        using \<open>t \<in> h S\<close> \<open>set (inputs SSep) = set (inputs S)\<close> by auto
      moreover have "t_output (shift_Inl t) \<in> set (outputs SSep)"
        using \<open>t \<in> h S\<close> \<open>set (outputs SSep) = set (outputs S)\<close> by auto
      ultimately have "shift_Inl t \<in> h SSep"
        using \<open>shift_Inl t \<in> set d_old\<close> d_containment_var by auto
      
      then show ?case 
        using snoc.IH[OF \<open>path S (initial S) p\<close>]  \<open>target (map shift_Inl p) (Inl (initial S)) = Inl (t_source t)\<close> \<open>initial SSep = Inl (initial S)\<close>
      proof -
        have f1: "path SSep (Inl (t_source t)) [(Inl (t_source t), t_input t, t_output t, Inl (t_target t))]"
          by (meson \<open>(Inl (t_source t), t_input t, t_output t, Inl (t_target t)) \<in> set (wf_transitions SSep)\<close> single_transitions_path)
        have "map (\<lambda>p. (Inl (t_source p)::'a \<times> 'a + 'a, t_input p, t_output p, Inl (t_target p)::'a \<times> 'a + 'a)) [t] = [(Inl (t_source t), t_input t, t_output t, Inl (t_target t))]"
          by auto
        then have "path SSep (target (map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) p) (Inl (initial S))) (map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) [t])"
          using f1 by (metis (no_types) \<open>target (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p) (Inl (initial S)) = Inl (t_source t)\<close>)
        then have "path SSep (Inl (initial S)) (map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) p @ map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) [t])"
          using \<open>initial SSep = Inl (initial S)\<close> \<open>path SSep (initial SSep) (map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p)\<close> by force
        then show ?thesis
          using \<open>initial SSep = Inl (initial S)\<close> by auto
      qed 
    qed
  qed

  have ssep_transitions_from_old : "\<And> t . t \<in> h S \<Longrightarrow> shift_Inl t \<in> h SSep"
  proof -
    fix t assume "t \<in> h S"
    then obtain p where "path S (initial S) p" and "target p (initial S) = t_source t"
      using path_to_node by force
    then have "path S (initial S) (p@[t])"
      using \<open>t \<in> h S\<close> by auto
    
    show "shift_Inl t \<in> h SSep" using ssep_path_from_old[OF \<open>path S (initial S) (p@[t])\<close>]
      using \<open>path S (initial S) p\<close> by auto 
  qed
  then have ssep_transitions_from_old' : "set (map shift_Inl (wf_transitions S)) \<subseteq> h SSep"
    using d_old_targets d_old_var by blast

  have ssep_nodes_from_old : "\<And> qq . qq \<in> nodes S \<Longrightarrow> Inl qq \<in> nodes SSep"
    using nodes_initial_or_target \<open>initial SSep = Inl (initial S)\<close> ssep_transitions_from_old
    by (metis nodes.initial snd_conv wf_transition_target) 

  

  have s_deadlock_transitions_left: "\<And> qq . qq \<in> nodes S \<Longrightarrow> deadlock_state S qq \<Longrightarrow> (\<exists> x y . (Inl qq, x, y, Inr (fst (initial S))) \<in> h SSep)"
  proof -
    fix qq assume "qq \<in> nodes S"
              and "deadlock_state S qq"
    then have "qq \<in> nodes S \<and> deadlock_state S qq" by simp
    then have *: "\<exists>x\<in>set (inputs M).
                 \<not> (\<exists>t1\<in>set (wf_transitions M).
                        \<exists>t2\<in>set (wf_transitions M).
                           t_source t1 = fst qq \<and>
                           t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
      using dl by blast


    have "s_states_deadlock_input M S qq \<noteq> None"
      unfolding s_states_deadlock_input_def using \<open>qq \<in> nodes S \<and> deadlock_state S qq\<close> using find_from[OF *] by force
    then obtain x where "s_states_deadlock_input M S qq = Some x"
      by auto
    then have "x \<in> set (inputs M)"
      unfolding s_states_deadlock_input_def
      by (meson \<open>deadlock_state S qq\<close> \<open>qq \<in> nodes S\<close> find_set)
    then have "x \<in> set (inputs S)"
      using \<open>inputs S = inputs ?PM\<close>
      using \<open>inputs SSep = inputs M\<close> \<open>set (inputs SSep) = set (inputs S)\<close> by auto 

    have "qq \<in> nodes ?PM"
      using \<open>qq \<in> nodes S\<close> submachine_nodes[OF \<open>is_submachine S ?PM\<close>] by blast
    then have "fst qq \<in> nodes M"
      using product_nodes[of "from_FSM M ?q1" "from_FSM M ?q2"] from_FSM_nodes[OF \<open>fst (initial S) \<in> nodes M\<close>]
      by (meson \<open>nodes (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))) \<subseteq> nodes (from_FSM M (fst (initial S))) \<times> nodes (from_FSM M (snd (initial S)))\<close> \<open>qq \<in> nodes (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))\<close> in_mono mem_Times_iff)
    
      

    obtain t where "t \<in> h M" 
               and "t_source t = fst qq"
               and "t_input t = x"
      using \<open>completely_specified M\<close> unfolding completely_specified.simps 
      using \<open>x \<in> set (inputs M)\<close> \<open>fst qq \<in> nodes M\<close> by blast
    then have "t_output t \<in> set (outputs M)"
      by auto

    have p1: "(qq,t) \<in> set (concat
                         (map (\<lambda>qq'. map (Pair qq') (wf_transitions M)) 
                         (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))"
      using \<open>qq \<in> nodes ?PM\<close> nodes_code[of ?PM] \<open>t \<in> h M\<close> by auto
    have p2: "(\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) (qq,t)"
      using \<open>t_source t = fst qq\<close> \<open>s_states_deadlock_input M S qq = Some x\<close> \<open>t_input t = x\<close>
      by auto

    have l1: "\<And> x f xs . x \<in> set xs \<Longrightarrow> f x \<Longrightarrow> x \<in> set (filter f xs)" by auto

    have p3: "(qq,t) \<in> set (filter (\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))
       (concat
         (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
           (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))" 
      using l1[OF p1, of "(\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))", OF p2] by assumption
    
    have l2: "\<And> f xs x . x \<in> set xs \<Longrightarrow> (f x) \<in> set (map f xs)"
      by auto

    let ?t = "(Inl (fst (qq, t)), t_input (snd (qq, t)), t_output (snd (qq, t)), Inr (fst (initial S)))"
    have "?t \<in> set ?d_left"
      using l2[OF p3, of "(\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))"] by assumption
      
    then have "?t \<in> set d_left"
      using d_left_var by meson
    



    then have "?t \<in> set (transitions SSep)"
      using d_containment_var by blast
    then have "(Inl qq, x, t_output t, Inr (fst (initial S))) \<in> set (transitions SSep)"
      using \<open>t_input t = x\<close> by auto
    moreover have "Inl qq \<in> nodes SSep"
      using ssep_nodes_from_old[OF \<open>qq \<in> nodes S\<close>] by assumption
    moreover have "x \<in> set (inputs SSep)"
      using \<open>x \<in> set (inputs S)\<close> \<open>set (inputs SSep) = set (inputs S)\<close> by blast
    moreover have "t_output t \<in> set (outputs SSep)"
      using \<open>t_output t \<in> set (outputs M)\<close> \<open>outputs SSep = outputs M\<close>
      by simp 
    ultimately have "(Inl qq, x, t_output t, Inr ?q1) \<in> h SSep"
      by auto
    then show "(\<exists> x y . (Inl qq, x, y, Inr ?q1) \<in> h SSep)" 
      by blast
  qed


  have s_deadlock_transitions_right: "\<And> qq . qq \<in> nodes S \<Longrightarrow> deadlock_state S qq \<Longrightarrow> (\<exists> x y . (Inl qq, x, y, Inr ?q2) \<in> h SSep)"
  proof -
    fix qq assume "qq \<in> nodes S"
              and "deadlock_state S qq"
    then have "qq \<in> nodes S \<and> deadlock_state S qq" by simp
    then have *: "\<exists>x\<in>set (inputs M).
                 \<not> (\<exists>t1\<in>set (wf_transitions M).
                        \<exists>t2\<in>set (wf_transitions M).
                           t_source t1 = fst qq \<and>
                           t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
      using dl by blast


    have "s_states_deadlock_input M S qq \<noteq> None"
      unfolding s_states_deadlock_input_def using \<open>qq \<in> nodes S \<and> deadlock_state S qq\<close> using find_from[OF *] by force
    then obtain x where "s_states_deadlock_input M S qq = Some x"
      by auto
    then have "x \<in> set (inputs M)"
      unfolding s_states_deadlock_input_def
      by (meson \<open>deadlock_state S qq\<close> \<open>qq \<in> nodes S\<close> find_set)
    then have "x \<in> set (inputs S)"
      using \<open>inputs S = inputs ?PM\<close>
      using \<open>inputs SSep = inputs M\<close> \<open>set (inputs SSep) = set (inputs S)\<close> by auto 

    have "qq \<in> nodes ?PM"
      using \<open>qq \<in> nodes S\<close> submachine_nodes[OF \<open>is_submachine S ?PM\<close>] by blast
    then have "snd qq \<in> nodes M"
      using product_nodes[of "from_FSM M ?q1" "from_FSM M ?q2"] from_FSM_nodes[OF \<open>snd (initial S) \<in> nodes M\<close>]
      by (meson \<open>nodes (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))) \<subseteq> nodes (from_FSM M (fst (initial S))) \<times> nodes (from_FSM M (snd (initial S)))\<close> \<open>qq \<in> nodes (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))\<close> in_mono mem_Times_iff)
    
      

    obtain t where "t \<in> h M" 
               and "t_source t = snd qq"
               and "t_input t = x"
      using \<open>completely_specified M\<close> unfolding completely_specified.simps 
      using \<open>x \<in> set (inputs M)\<close> \<open>snd qq \<in> nodes M\<close> by blast
    then have "t_output t \<in> set (outputs M)"
      by auto

    have p1: "(qq,t) \<in> set (concat
                         (map (\<lambda>qq'. map (Pair qq') (wf_transitions M)) 
                         (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))"
      using \<open>qq \<in> nodes ?PM\<close> nodes_code[of ?PM] \<open>t \<in> h M\<close> by auto
    have p2: "(\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) (qq,t)"
      using \<open>t_source t = snd qq\<close> \<open>s_states_deadlock_input M S qq = Some x\<close> \<open>t_input t = x\<close>
      by auto

    have l1: "\<And> x f xs . x \<in> set xs \<Longrightarrow> f x \<Longrightarrow> x \<in> set (filter f xs)" by auto

    have p3: "(qq,t) \<in> set (filter (\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))
       (concat
         (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
           (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))" 
      using l1[OF p1, of "(\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and> s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))", OF p2] by assumption
    
    have l2: "\<And> f xs x . x \<in> set xs \<Longrightarrow> (f x) \<in> set (map f xs)"
      by auto

    let ?t = "(Inl (fst (qq, t)), t_input (snd (qq, t)), t_output (snd (qq, t)), Inr ?q2)"
    have "?t \<in> set ?d_right"
      using l2[OF p3, of "(\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr ?q2))"] by assumption
      
    then have "?t \<in> set d_right"
      using d_right_var by meson
    



    then have "?t \<in> set (transitions SSep)"
      using d_containment_var by blast
    then have "(Inl qq, x, t_output t, Inr ?q2) \<in> set (transitions SSep)"
      using \<open>t_input t = x\<close> by auto
    moreover have "Inl qq \<in> nodes SSep"
      using ssep_nodes_from_old[OF \<open>qq \<in> nodes S\<close>] by assumption
    moreover have "x \<in> set (inputs SSep)"
      using \<open>x \<in> set (inputs S)\<close> \<open>set (inputs SSep) = set (inputs S)\<close> by blast
    moreover have "t_output t \<in> set (outputs SSep)"
      using \<open>t_output t \<in> set (outputs M)\<close> \<open>outputs SSep = outputs M\<close>
      by simp 
    ultimately have "(Inl qq, x, t_output t, Inr ?q2) \<in> h SSep"
      by auto
    then show "(\<exists> x y . (Inl qq, x, y, Inr ?q2) \<in> h SSep)" 
      by blast
  qed
    

  
  (* no additional deadlock states (or other Inr-states) exist *) 

  have inl_prop: "\<And> q . q \<in> nodes SSep \<Longrightarrow> q \<noteq> Inr ?q1 \<Longrightarrow> q \<noteq> Inr ?q2 \<Longrightarrow>
                        isl q \<and> \<not> deadlock_state SSep q" 
  proof -
    fix q assume "q \<in> nodes SSep" 
             and "q \<noteq> Inr ?q1"
             and "q \<noteq> Inr ?q2"

   have g1: "isl q" proof (cases "q = initial SSep")
      case True
      then have "q = Inl (initial S)"
        unfolding state_separator_from_product_submachine_def \<open>initial SSep = Inl (initial S)\<close> by (simp only: select_convs)
      then show ?thesis by auto 
    next
      case False 
      then obtain t where "t \<in> h SSep" and "t_target t = q"
        by (meson \<open>q \<in> nodes SSep\<close> nodes_initial_or_target)
        
      show ?thesis using \<open>q \<noteq> Inr ?q1\<close> \<open>q \<noteq> Inr ?q2\<close>
        by (metis UnE \<open>t \<in> set (wf_transitions SSep)\<close> \<open>t_target t = q\<close> d_containment_var d_left_targets d_old_targets d_right_targets d_old_dist_left_targets d_old_dist_right_targets wf_transition_simp) 
    qed

    have "\<And> qq . Inl qq \<in> nodes SSep \<Longrightarrow> \<not> (deadlock_state SSep (Inl qq))"
    proof -
      fix qq assume "Inl qq \<in> nodes SSep"
      
      have "qq \<in> nodes S" proof (cases "Inl qq = initial SSep")
        case True
        then have "Inl qq = Inl (initial S)"
          using \<open>initial SSep = Inl (initial S)\<close>
          by (metis sum.sel(1))
        then show ?thesis by auto
      next
        case False
        then obtain t where "t \<in> h SSep" and "t_target t = Inl qq"
          using nodes_initial_or_target \<open>Inl qq \<in> nodes SSep\<close> by metis
        
        obtain qq' where "t_source t = Inl qq'"
          by (metis \<open>t \<in> set (wf_transitions SSep)\<close> isl_def isl_source ssep_var)

        have "(Inl qq',t_input t, t_output t, Inl qq) \<in> h SSep"
          using \<open>t \<in> h SSep\<close> \<open>t_source t = Inl qq'\<close> \<open>t_target t = Inl qq\<close> using prod.collapse by metis

        then have "(qq',t_input t, t_output t,qq) \<in> h S" 
          using ssep_var d_old_origins by blast 
        then show ?thesis using wf_transition_target
          by fastforce 
      qed
      
      show "\<not> (deadlock_state SSep (Inl qq))"
      proof (cases "deadlock_state S qq")
        case True
        show ?thesis using s_deadlock_transitions_left[OF \<open>qq \<in> nodes S\<close> True]
          unfolding deadlock_state.simps
          by auto  
      next
        case False 
        then obtain t where "t \<in> h S" and "t_source t = qq"
          unfolding deadlock_state.simps by blast
        then have "shift_Inl t \<in> h SSep"
          using ssep_transitions_from_old by blast 
        then show ?thesis 
          unfolding deadlock_state.simps
          using \<open>t_source t = qq\<close> by auto 
      qed
    qed
    then have "\<not> deadlock_state SSep q"
      by (metis \<open>q \<in> nodes SSep\<close> g1 isl_def) 

    then show "isl q \<and> \<not> deadlock_state SSep q"
      using g1 by simp
  qed

  then have has_inl_property: "\<forall>q\<in>nodes ?SSep.
        q \<noteq> Inr ?q1 \<and> q \<noteq> Inr ?q2 \<longrightarrow>
        isl q \<and> \<not> deadlock_state ?SSep q" using ssep_var by blast



  have d_left_sources : "\<And> t . t \<in> set d_left \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst q \<and>
                                                                t_source t2 = snd q \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M) = Some (t_input t))
                                               \<and> t_input t \<in> set (inputs SSep)
                                               \<and> t_output t \<in> set (outputs SSep))"
  proof -
    fix t assume "t \<in> set d_left"

    have f1: "\<And> t xs f . t \<in> set (map f xs) \<Longrightarrow> (\<exists> x \<in> set xs . t = f x)" by auto
    have f2: "\<And> x xs f . x \<in> set (filter f xs) \<Longrightarrow> f x" by auto
    have f3: "\<And> x xs f . x \<in> set (filter f xs) \<Longrightarrow> x \<in> set xs" by auto

    obtain qqt where *:  "t = (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S)))) qqt" 
                 and **: "qqt \<in> set (filter
                                   (\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                                          (if fst qqt \<in> nodes S \<and> deadlock_state S (fst qqt)
                                           then find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst (fst qqt) \<and>
                                                                t_source t2 = snd (fst qqt) \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M)
                                           else None) =
                                          Some (t_input (snd qqt)))
                                   (concat
                                     (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                       (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))"
      using \<open>t \<in> set d_left\<close> \<open>d_left = ?d_left\<close> unfolding s_states_deadlock_input_def 
      using f1[of t "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))"] by blast

    have "snd qqt \<in> h M"
      using f3[OF **] concat_pair_set by blast
    then have "t_input (snd qqt) \<in> set (inputs M)" and "t_output (snd qqt) \<in> set (outputs M)"
      by auto
    then have "t_input (snd qqt) \<in> set (inputs SSep)" and "t_output (snd qqt) \<in> set (outputs SSep)"
      by (simp only: \<open>inputs SSep = inputs M\<close> \<open>outputs SSep = outputs M\<close>)+
      

    then have "t_source (snd qqt) = fst (fst qqt) \<and> (fst qqt) \<in> nodes S \<and> deadlock_state S (fst qqt) \<and> find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = fst (fst qqt) \<and>
                          t_source t2 = snd (fst qqt) \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) = Some (t_input (snd qqt))
          \<and> t_input (snd qqt) \<in> set (inputs SSep)
          \<and> t_output (snd qqt) \<in> set (outputs SSep)"
      using f2[OF **]
      by (meson option.distinct(1)) 
    then have "t_source t = Inl (fst qqt) \<and> (fst qqt) \<in> nodes S \<and> deadlock_state S (fst qqt) \<and> find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = fst (fst qqt) \<and>
                          t_source t2 = snd (fst qqt) \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) = Some (t_input t)
          \<and> t_input t \<in> set (inputs SSep)
          \<and> t_output t \<in> set (outputs SSep)"
      using * by auto
    then show "(\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> deadlock_state S q \<and> find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst q \<and>
                                                                t_source t2 = snd q \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M) = Some (t_input t)
                                                 \<and> t_input t \<in> set (inputs SSep)
                                                 \<and> t_output t \<in> set (outputs SSep))" by blast
      
  qed

  have d_right_sources : "\<And> t . t \<in> set d_right \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst q \<and>
                                                                t_source t2 = snd q \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M) = Some (t_input t))
                                               \<and> t_input t \<in> set (inputs SSep)
                                               \<and> t_output t \<in> set (outputs SSep))"
  proof -
    fix t assume "t \<in> set d_right"

    have f1: "\<And> t xs f . t \<in> set (map f xs) \<Longrightarrow> (\<exists> x \<in> set xs . t = f x)" by auto
    have f2: "\<And> x xs f . x \<in> set (filter f xs) \<Longrightarrow> f x" by auto
    have f3: "\<And> x xs f . x \<in> set (filter f xs) \<Longrightarrow> x \<in> set xs" by auto

    obtain qqt where *:  "t = (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S)))) qqt" 
                 and **: "qqt \<in> set (filter
                                   (\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                                          (if fst qqt \<in> nodes S \<and> deadlock_state S (fst qqt)
                                           then find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst (fst qqt) \<and>
                                                                t_source t2 = snd (fst qqt) \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M)
                                           else None) =
                                          Some (t_input (snd qqt)))
                                   (concat
                                     (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                       (nodes_from_distinct_paths (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))))))"
      using \<open>t \<in> set d_right\<close> \<open>d_right = ?d_right\<close> unfolding s_states_deadlock_input_def 
      using f1[of t "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))"] by blast

    have "snd qqt \<in> h M"
      using f3[OF **] concat_pair_set by blast
    then have "t_input (snd qqt) \<in> set (inputs M)" and "t_output (snd qqt) \<in> set (outputs M)"
      by auto
    then have "t_input (snd qqt) \<in> set (inputs SSep)" and "t_output (snd qqt) \<in> set (outputs SSep)"
      by (simp only: \<open>inputs SSep = inputs M\<close> \<open>outputs SSep = outputs M\<close>)+
      

    then have "t_source (snd qqt) = snd (fst qqt) \<and> (fst qqt) \<in> nodes S \<and> deadlock_state S (fst qqt) \<and> find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = fst (fst qqt) \<and>
                          t_source t2 = snd (fst qqt) \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) = Some (t_input (snd qqt))
          \<and> t_input (snd qqt) \<in> set (inputs SSep)
          \<and> t_output (snd qqt) \<in> set (outputs SSep)"
      using f2[OF **]
      by (meson option.distinct(1)) 
    then have "t_source t = Inl (fst qqt) \<and> (fst qqt) \<in> nodes S \<and> deadlock_state S (fst qqt) \<and> find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = fst (fst qqt) \<and>
                          t_source t2 = snd (fst qqt) \<and>
                          t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) = Some (t_input t)
          \<and> t_input t \<in> set (inputs SSep)
          \<and> t_output t \<in> set (outputs SSep)"
      using * by auto
    then show "(\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> deadlock_state S q \<and> find
                                                 (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                                             \<exists>t2\<in>set (wf_transitions M).
                                                                t_source t1 = fst q \<and>
                                                                t_source t2 = snd q \<and>
                                                                t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                                                 (inputs M) = Some (t_input t)
                                                 \<and> t_input t \<in> set (inputs SSep)
                                                 \<and> t_output t \<in> set (outputs SSep))" by blast
      
  qed



  



  have d_old_sources : "\<And> t . t \<in> set d_old \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
  proof -
    fix t assume "t \<in> set d_old"
    then have "isl (t_target t)"
      by (simp add: d_old_targets) 
    then obtain qt where "t_target t = Inl qt"
      by (metis sum.collapse(1)) 
    
    have "isl (t_source t)"
      using \<open>t \<in> set d_old\<close> d_old_targets isl_source ssep_transitions_from_old ssep_var by blast
    then obtain qs where "t_source t = Inl qs"
      by (metis sum.collapse(1)) 

    have "(qs,t_input t,t_output t,qt) \<in> h S"
      using d_old_origins
      by (metis \<open>\<And>y x qt qs. (Inl qs, x, y, Inl qt) \<in> set d_old \<Longrightarrow> (qs, x, y, qt) \<in> set (wf_transitions S)\<close> \<open>t \<in> set d_old\<close> \<open>t_source t = Inl qs\<close> \<open>t_target t = Inl qt\<close> prod.collapse)
    then have "\<not> (deadlock_state S qs)"
      unfolding deadlock_state.simps
      by (meson fst_conv) 

    show "(\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
      using \<open>t_source t = Inl qs\<close> \<open>(qs,t_input t,t_output t,qt) \<in> h S\<close> \<open>\<not> (deadlock_state S qs)\<close> by auto
  qed

  have d_old_dist_left_sources : "\<And> t . t \<in> set d_old_dist_left \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
  proof -
    fix t assume "t \<in> set d_old_dist_left"
    then obtain t' where "t' \<in> set d_old" and "t_source t = t_source t'" and "t_input t = t_input t'"
      using d_old_dist_left_var by auto
    then show "(\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
      using d_old_sources by auto
  qed

  have d_old_dist_right_sources : "\<And> t . t \<in> set d_old_dist_right \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
  proof -
    fix t assume "t \<in> set d_old_dist_right"
    then obtain t' where "t' \<in> set d_old" and "t_source t = t_source t'" and "t_input t = t_input t'"
      using d_old_dist_right_var by auto
    then show "(\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
      using d_old_sources by auto
  qed

  have d_non_deadlock_sources : "\<And> t . t \<in> set d_old \<or> t \<in> set d_old_dist_left \<or> t \<in> set d_old_dist_right \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> \<not>deadlock_state S q)"
    using d_old_sources d_old_dist_left_sources d_old_dist_right_sources by blast

  have d_deadlock_sources : "\<And> t . t \<in> set d_left \<or> t \<in> set d_right \<Longrightarrow> (\<exists> q . t_source t = Inl q \<and> q \<in> nodes S \<and> deadlock_state S q)"
    using d_left_sources d_right_sources by blast


  have d_old_dist_left_d_old : "\<And> t . t \<in> set d_old_dist_left \<Longrightarrow> (\<exists> t' \<in> set d_old . t_source t = t_source t' \<and> t_input t = t_input t')"
    using d_old_dist_left_var by auto

  have d_old_dist_right_d_old : "\<And> t . t \<in> set d_old_dist_right \<Longrightarrow> (\<exists> t' \<in> set d_old . t_source t = t_source t' \<and> t_input t = t_input t')"
    using d_old_dist_right_var by auto



     
  have "set d_old \<inter> set d_left = {}"
    using d_old_targets \<open>d_left = ?d_left\<close>
    by (metis (no_types, lifting) Inr_Inl_False d_left_targets disjoint_iff_not_equal prod.collapse prod.inject)
  have "set d_old \<inter> set d_right = {}"
    using d_old_targets \<open>d_right = ?d_right\<close>
    by (metis (no_types, lifting) Inr_Inl_False d_right_targets disjoint_iff_not_equal prod.collapse prod.inject)
  have "set d_left \<inter> set d_right = {}"
    using d_left_targets d_right_targets \<open>fst (initial S) \<noteq> snd (initial S)\<close>
    by fastforce 

  
  have d_source_split : "\<And> t1 t2 . t1 \<in> set d_old \<Longrightarrow> t2 \<in> set d_left \<or> t2 \<in> set d_right \<Longrightarrow> t_source t1 \<noteq> t_source t2"
  proof -
    fix t1 t2 assume "t1 \<in> set d_old" 
                 and "t2 \<in> set d_left \<or> t2 \<in> set d_right"

    then consider "t2 \<in> set d_left" | "t2 \<in> set d_right" by blast
    then show "t_source t1 \<noteq> t_source t2" proof cases
      case 1
      show ?thesis 
        using d_old_sources[OF \<open>t1 \<in> set d_old\<close>] d_left_sources[OF 1]
        by fastforce 
    next
      case 2
      show ?thesis 
        using d_old_sources[OF \<open>t1 \<in> set d_old\<close>] d_right_sources[OF 2]
        by fastforce 
    qed
  qed

  have d_source_split_deadlock : "\<And> t1 t2 . t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right \<Longrightarrow> t2 \<in> set d_left \<or> t2 \<in> set d_right \<Longrightarrow> t_source t1 \<noteq> t_source t2"
  proof -
    fix t1 t2 assume *:  "t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right"
                 and **: "t2 \<in> set d_left \<or> t2 \<in> set d_right"

    obtain q1 where "t_source t1 = Inl q1" and "\<not> (deadlock_state S q1)"
      using d_non_deadlock_sources[OF *] by blast
    obtain q2 where "t_source t2 = Inl q2" and "(deadlock_state S q2)"
      using d_deadlock_sources[OF **] by blast

    have "q1 \<noteq> q2"
      using \<open>\<not> (deadlock_state S q1)\<close> \<open>(deadlock_state S q2)\<close> by blast
    then show "t_source t1 \<noteq> t_source t2" 
      using \<open>t_source t1 = Inl q1\<close> \<open>t_source t2 = Inl q2\<close> by auto
  qed
         



  have d_old_same_sources: "\<And> t1 t2 . t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right \<Longrightarrow> t2 \<in> h SSep \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t2 \<in> set d_old \<or> t2 \<in> set d_old_dist_left \<or> t2 \<in> set d_old_dist_right"
  proof -
    fix t1 t2 assume "t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right" and "t2 \<in> h SSep" and "t_source t1 = t_source t2"

    have "\<not>(t2 \<in> set d_left \<or> t2 \<in> set d_right)"
      using d_source_split_deadlock[OF \<open>t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right\<close>, of t2] \<open>t_source t1 = t_source t2\<close> by auto
    then show "t2 \<in> set d_old \<or> t2 \<in> set d_old_dist_left \<or> t2 \<in> set d_old_dist_right"
      using d_containment_var \<open>t2 \<in> h SSep\<close> by blast 
  qed


  have d_left_right_same_sources: "\<And> t1 t2 . t1 \<in> set d_left \<or> t1 \<in> set d_right \<Longrightarrow> t2 \<in> h SSep \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t2 \<in> set d_left \<or> t2 \<in> set d_right"
  proof -
    fix t1 t2 assume "t1 \<in> set d_left \<or> t1 \<in> set d_right" and "t2 \<in> h SSep" and "t_source t1 = t_source t2"

    have "\<not>(t2 \<in> set d_old \<or> t2 \<in> set d_old_dist_left \<or> t2 \<in> set d_old_dist_right)"
      using d_source_split_deadlock[OF _ \<open>t1 \<in> set d_left \<or> t1 \<in> set d_right\<close>, of t2] \<open>t_source t1 = t_source t2\<close> by auto
    then show "t2 \<in> set d_left \<or> t2 \<in> set d_right"
      using d_containment_var \<open>t2 \<in> h SSep\<close> by blast
  qed


  


  
  have d_old_transitions : "\<And> t . t \<in> set d_old \<Longrightarrow> (\<exists> qs qt . t = (Inl qs,t_input t, t_output t, Inl qt) \<and> (qs,t_input t, t_output t, qt) \<in> h S)"
  proof -
    fix t assume "t \<in> set d_old"
    then have "isl (t_target t)"
      by (simp add: d_old_targets) 
    then obtain qt where "t_target t = Inl qt"
      by (metis sum.collapse(1)) 
    have "isl (t_source t)"
      using \<open>t \<in> set d_old\<close> d_old_sources isl_def by blast
    then obtain qs where "t_source t = Inl qs"
      by (metis sum.collapse(1)) 
    have "(qs,t_input t,t_output t,qt) \<in> h S"
      using d_old_origins
      by (metis \<open>\<And>y x qt qs. (Inl qs, x, y, Inl qt) \<in> set d_old \<Longrightarrow> (qs, x, y, qt) \<in> set (wf_transitions S)\<close> \<open>t \<in> set d_old\<close> \<open>t_source t = Inl qs\<close> \<open>t_target t = Inl qt\<close> prod.collapse)
    then show "(\<exists> qs qt . t = (Inl qs,t_input t, t_output t, Inl qt) \<and> (qs,t_input t, t_output t, qt) \<in> h S)"
      using \<open>t_target t = Inl qt\<close> \<open>t_source t = Inl qs\<close>
      by (metis prod.collapse) 
  qed


  (* is single input *)

  have "\<And> t1 t2 . t1 \<in> h SSep \<Longrightarrow> t2 \<in> h SSep \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2"
  proof -
    fix t1 t2 assume "t1 \<in> h SSep"
                 and "t2 \<in> h SSep"
                 and "t_source t1 = t_source t2"

    let ?q = "t_source t1"

    consider "t1 \<in> set d_old \<or> t1 \<in> set d_old_dist_left \<or> t1 \<in> set d_old_dist_right" | "t1 \<in> set d_left \<or> t1 \<in> set d_right"
      using d_containment_var \<open>t1 \<in> h SSep\<close> by auto
    then show "t_input t1 = t_input t2" proof cases
      case 1
      then have "t2 \<in> set d_old \<or> t2 \<in> set d_old_dist_left \<or> t2 \<in> set d_old_dist_right"
        using d_old_same_sources \<open>t2 \<in> h SSep\<close> \<open>t_source t1 = t_source t2\<close> by blast
      then obtain t2' where "t2' \<in> set d_old" and "t_source t2 = t_source t2'" and "t_input t2 = t_input t2'"
        using d_old_dist_left_d_old d_old_dist_right_d_old by metis 
  
      from 1 obtain t1' where "t1' \<in> set d_old" and "t_source t1 = t_source t1'" and "t_input t1 = t_input t1'"
        using d_old_dist_left_d_old d_old_dist_right_d_old by blast

      


      obtain qs1 qt1 where "t1' = (Inl qs1, t_input t1, t_output t1', Inl qt1)" 
                       and "(qs1, t_input t1, t_output t1', qt1) \<in> h S"
        using d_old_transitions[OF \<open>t1' \<in> set d_old\<close>] \<open>t_source t1 = t_source t1'\<close> \<open>t_input t1 = t_input t1'\<close> by metis

      obtain qs2 qt2 where "t2' = (Inl qs2, t_input t2, t_output t2', Inl qt2)" 
                       and "(qs2, t_input t2, t_output t2', qt2) \<in> h S"
        using d_old_transitions[OF \<open>t2' \<in> set d_old\<close>] \<open>t_source t2 = t_source t2'\<close> \<open>t_input t2 = t_input t2'\<close> by metis

      have "qs1 = qs2"
        using \<open>t1' = (Inl qs1, t_input t1, t_output t1', Inl qt1)\<close>
              \<open>t_source t1 = t_source t1'\<close>
              \<open>t_source t1 = t_source t2\<close>
              \<open>t_source t2 = t_source t2'\<close>
              \<open>t2' = (Inl qs2, t_input t2, t_output t2', Inl qt2)\<close>
        by (metis fst_conv old.sum.inject(1))
        
      then have "(qs1, t_input t2, t_output t2', qt2) \<in> h S"
        using \<open>(qs2, t_input t2, t_output t2', qt2) \<in> h S\<close> by auto

      show ?thesis
        using \<open>single_input S\<close> unfolding single_input.simps
        using \<open>(qs1, t_input t1, t_output t1', qt1) \<in> h S\<close> \<open>(qs1, t_input t2, t_output t2', qt2) \<in> h S\<close>
        by (metis fst_conv snd_conv)


    next
      case 2 
      then have "t2 \<in> set d_left \<or> t2 \<in> set d_right"
        using \<open>\<And> t1 t2 . t1 \<in> set d_left \<or> t1 \<in> set d_right \<Longrightarrow> t2 \<in> h SSep \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t2 \<in> set d_left \<or> t2 \<in> set d_right\<close> \<open>t2 \<in> h SSep\<close> \<open>t_source t1 = t_source t2\<close> by blast

      obtain q1 where "t_source t1 = Inl q1"
                  and "q1 \<in> nodes S"
                  and "deadlock_state S q1"
                  and f1: "find
                         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                     \<exists>t2\<in>set (wf_transitions M).
                                        t_source t1 = fst q1 \<and>
                                        t_source t2 = snd q1 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                         (inputs M) = Some (t_input t1)"
        using d_left_sources[of t1] d_right_sources[of t1]
        using "2" by blast 

      obtain q2 where "t_source t2 = Inl q2"
                  and "q2 \<in> nodes S"
                  and "deadlock_state S q2"
                  and f2 : "find
                         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                     \<exists>t2\<in>set (wf_transitions M).
                                        t_source t1 = fst q2 \<and>
                                        t_source t2 = snd q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                         (inputs M) = Some (t_input t2)"
        using d_left_sources[of t2] d_right_sources[of t2]
        using \<open>t2 \<in> set d_left \<or> t2 \<in> set d_right\<close> by blast 

      

      show ?thesis
        using f1 f2 \<open>t_source t1 = t_source t2\<close>
        using \<open>t_source t1 = Inl q1\<close> \<open>t_source t2 = Inl q2\<close> by auto 
    qed
  qed
  then have "single_input SSep"
    unfolding single_input.simps by blast
  
  then have is_single_input : "single_input ?SSep" 
    using ssep_var by blast


  (* desired deadlock states are reachable *)

  have "Inr ?q1 \<in> nodes SSep"
  proof -
    obtain qd where "qd \<in> nodes S" and "deadlock_state S qd"
      using acyclic_deadlock_states[OF \<open>acyclic S\<close>] by blast
    show ?thesis
      using s_deadlock_transitions_left[OF \<open>qd \<in> nodes S\<close> \<open>deadlock_state S qd\<close>] 
      using wf_transition_target
      by fastforce
  qed
  then have has_node_left: "Inr ?q1 \<in> nodes ?SSep" 
    using \<open>SSep = ?SSep\<close> by blast

  have "Inr ?q2 \<in> nodes SSep"
  proof -
    obtain qd where "qd \<in> nodes S" and "deadlock_state S qd"
      using acyclic_deadlock_states[OF \<open>acyclic S\<close>] by blast
    show ?thesis
      using s_deadlock_transitions_right[OF \<open>qd \<in> nodes S\<close> \<open>deadlock_state S qd\<close>] 
      using wf_transition_target
      by fastforce
  qed
  then have has_node_right: "Inr ?q2 \<in> nodes ?SSep" 
    using \<open>SSep = ?SSep\<close> by blast



  have "\<And> q . q \<in> nodes SSep \<Longrightarrow> \<not> isl q \<Longrightarrow> deadlock_state SSep q"
  proof -
    fix q assume "q \<in> nodes SSep" and "\<not> isl q"
    have "q = Inr ?q1 \<or> q = Inr ?q2"
      using inl_prop[OF \<open>q \<in> nodes SSep\<close>] \<open>\<not> isl q\<close> by blast
    then show "deadlock_state SSep q" 
      using has_deadlock_left has_deadlock_right \<open>SSep = ?SSep\<close> by blast
  qed

  have isl_target_paths : "\<And> p . path SSep (initial SSep) p \<Longrightarrow> isl (target p (initial SSep)) \<Longrightarrow> (\<exists> p' . path S (initial S) p' \<and> p = map shift_Inl p')"
  proof -
    fix p assume "path SSep (initial SSep) p" and "isl (target p (initial SSep))"
    then show "(\<exists> p' . path S (initial S) p' \<and> p = map shift_Inl p')" 
    proof (induction p rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc t p)
      then have "path SSep (initial SSep) p" by auto
      moreover have "\<not> (deadlock_state SSep (target p (initial SSep)))"
        using deadlock_prefix[OF snoc.prems(1)]
        by (metis calculation deadlock_state.simps path_cons_elim path_equivalence_by_h path_suffix snoc.prems(1))  
      ultimately have "isl (target p (initial SSep))"
        using \<open>\<And> q . q \<in> nodes SSep \<Longrightarrow> \<not> isl q \<Longrightarrow> deadlock_state SSep q\<close>
        using nodes_path_initial by blast 

      then obtain p' where "path S (initial S) p'" and "p = map shift_Inl p'"
        using snoc.IH[OF \<open>path SSep (initial SSep) p\<close>] by blast

      have "isl (t_source t)"
        using \<open>isl (target p (initial SSep))\<close> snoc.prems(1)
        by auto 
      moreover have "isl (t_target t)"
        using snoc.prems(2) unfolding target.simps visited_states.simps by auto

      ultimately obtain qs qt where "t = (Inl qs, t_input t, t_output t, Inl qt)"
        by (metis prod.collapse sum.collapse(1))
      then have "(Inl qs, t_input t, t_output t, Inl qt) \<in> h SSep"
        using snoc.prems(1) by auto
      then have "(qs, t_input t, t_output t, qt) \<in> h S"
        using d_old_origins by blast


      have "map t_target p = map Inl (map t_target p')"
        using \<open>p = map shift_Inl p'\<close> by auto
      then have "(target p (initial SSep)) = Inl (target p' (initial S))"
        using \<open>initial SSep = Inl (initial S)\<close> unfolding target.simps visited_states.simps
        by (simp add: last_map) 


      then have "path S (initial S) (p'@[(qs, t_input t, t_output t, qt)])" 
        using \<open>path S (initial S) p'\<close> snoc.prems(1)
        by (metis (no_types, lifting) Inl_inject \<open>(qs, t_input t, t_output t, qt) \<in> set (wf_transitions S)\<close> \<open>t = (Inl qs, t_input t, t_output t, Inl qt)\<close> fst_conv list.inject not_Cons_self2 path.cases path_append_last path_suffix) 

      moreover have "p@[t] = map shift_Inl (p'@[(qs, t_input t, t_output t, qt)])"
        using \<open>p = map shift_Inl p'\<close> \<open>t = (Inl qs, t_input t, t_output t, Inl qt)\<close> by auto
      ultimately show ?case
        by meson 
    qed
  qed

  (* is acylic *)

  have "\<And> p . path SSep (initial SSep) p \<Longrightarrow> distinct (visited_states (initial SSep) p)"
  proof -
    fix p assume "path SSep (initial SSep) p"
    show "distinct (visited_states (initial SSep) p)"
    proof (cases "isl (target p (initial SSep))")
      case True
      then obtain p' where "path S (initial S) p'" and "p = map shift_Inl p'"
        using \<open>\<And> p . path SSep (initial SSep) p \<Longrightarrow> isl (target p (initial SSep)) \<Longrightarrow> (\<exists> p' . path S (initial S) p' \<and> p = map shift_Inl p')\<close>
              \<open>path SSep (initial SSep) p\<close> 
        by blast

      have "map t_target p = map Inl (map t_target p')"
        using \<open>p = map shift_Inl p'\<close> by auto
      then have "visited_states (initial SSep) p = map Inl (visited_states (initial S) p')"
        using \<open>initial SSep = Inl (initial S)\<close> unfolding target.simps visited_states.simps
        by simp 
      moreover have "distinct (visited_states (initial S) p')"
        using \<open>acyclic S\<close> \<open>path S (initial S) p'\<close> unfolding acyclic.simps by blast
      moreover have "\<And> xs :: ('a \<times> 'a) list . distinct xs = distinct (map Inl xs)" 
      proof -
        fix xs :: "('a \<times> 'a) list"
        show "distinct xs = distinct (map Inl xs)" by (induction xs; auto)
      qed
      ultimately show ?thesis
        by force         
    next
      case False 

      have "deadlock_state SSep (target p (initial SSep))"
        using False \<open>\<And> q . q \<in> nodes SSep \<Longrightarrow> \<not> isl q \<Longrightarrow> deadlock_state SSep q\<close>
        using \<open>path SSep (initial SSep) p\<close> nodes_path_initial by blast

      have "target p (initial SSep) \<noteq> initial SSep"
        using False \<open>initial SSep = Inl (initial S)\<close> by auto
      then have "p \<noteq> []"
        by auto
      then obtain t p' where "p = p'@[t]"
        using rev_exhaust by blast
      then have "\<not> (isl (t_target t))"
        using False unfolding target.simps visited_states.simps by auto

      have "path SSep (initial SSep) p'"
        using \<open>p = p'@[t]\<close> \<open>path SSep (initial SSep) p\<close> by auto
      
      show ?thesis proof (cases p' rule: rev_cases)
        case Nil
        then show ?thesis 
          using \<open>\<not> (isl (t_target t))\<close> \<open>p = p'@[t]\<close> unfolding target.simps visited_states.simps
          using \<open>target p (initial SSep) \<noteq> initial SSep\<close> by auto 
      next
        case (snoc p'' t')
        


        then have "isl (target p' (initial SSep))" 
          using \<open>p = p'@[t]\<close> deadlock_prefix[OF \<open>path SSep (initial SSep) p\<close>, of t']
          by (metis \<open>path SSep (initial SSep) p\<close> isl_source not_Cons_self2 path.cases path_suffix ssep_var)
        then obtain pS where "path S (initial S) pS" and "p' = map shift_Inl pS"
          using \<open>\<And> p . path SSep (initial SSep) p \<Longrightarrow> isl (target p (initial SSep)) \<Longrightarrow> (\<exists> p' . path S (initial S) p' \<and> p = map shift_Inl p')\<close>
                [OF \<open>path SSep (initial SSep) p'\<close>] by blast

        have "map t_target p' = map Inl (map t_target pS)"
          using \<open>p' = map shift_Inl pS\<close> by auto
        then have "visited_states (initial SSep) p' = map Inl (visited_states (initial S) pS)"
          using \<open>initial SSep = Inl (initial S)\<close> unfolding target.simps visited_states.simps
          by simp 
        moreover have "distinct (visited_states (initial S) pS)"
          using \<open>acyclic S\<close> \<open>path S (initial S) pS\<close> unfolding acyclic.simps by blast
        moreover have "\<And> xs :: ('a \<times> 'a) list . distinct xs = distinct (map Inl xs)" 
        proof -
          fix xs :: "('a \<times> 'a) list"
          show "distinct xs = distinct (map Inl xs)" by (induction xs; auto)
        qed
        ultimately have "distinct (visited_states (initial SSep) p')"
          by force
        moreover have "t_target t \<notin> set (visited_states (initial SSep) p')"
          using \<open>visited_states (initial SSep) p' = map Inl (visited_states (initial S) pS)\<close> \<open>\<not> (isl (t_target t))\<close>
          by auto 
        ultimately have "distinct ((visited_states (initial SSep) p')@[t_target t])"
          by auto
        then show ?thesis using \<open>p = p'@[t]\<close> unfolding target.simps visited_states.simps
          by simp 
      qed  
    qed
  qed 
  

  then have "acyclic SSep"
    unfolding acyclic.simps by blast
    
  
  then have is_acyclic : "acyclic ?SSep" 
    using \<open>SSep = ?SSep\<close> by blast

  (* all relevant transitions of the canonical separator are retained *)

  have inl_prop_prep: "\<And> t t' . t \<in> h SSep \<Longrightarrow> t' \<in> h CSep \<Longrightarrow> t_source t = t_source t' \<Longrightarrow> t_input t = t_input t' \<Longrightarrow> t' \<in> h SSep"
  proof -
    fix t t' assume "t \<in> h SSep" and "t' \<in> h CSep" and "t_source t = t_source t'" and "t_input t = t_input t'"

    have "t' \<in> h ?CSep"
          using \<open>t' \<in> h CSep\<close> \<open>CSep = ?CSep\<close> by auto

    show "t' \<in> h SSep"
    proof (cases "isl (t_target t')")
      case True

      obtain tP where "tP \<in> h ?PM" and "t' = (Inl (t_source tP), t_input tP, t_output tP, Inl (t_target tP))"
        using canonical_separator_product_h_isl[OF _ True]
        using \<open>t' \<in> h CSep\<close> \<open>CSep = ?CSep\<close>
        by metis

      from \<open>t \<in> h SSep\<close> consider 
        (old)         "t \<in> set d_old \<or> t \<in> set d_old_dist_left \<or> t \<in> set d_old_dist_right"  |
        (left_right)  "t \<in> set d_left \<or> t \<in> set d_right"
        using d_containment_var by blast
      then show "t' \<in> h SSep" proof cases
        case old

        then obtain tO where "tO \<in> set d_old" and "t_source t = t_source tO" and "t_input t = t_input tO"
          using d_old_dist_left_d_old d_old_dist_right_d_old by blast

        obtain tS where "tS \<in> h S" and "tO = (Inl (t_source tS), t_input tS, t_output tS, Inl (t_target tS))"
          using d_old_targets[OF \<open>tO \<in> set d_old\<close>] by auto
        
        have "t_source t = Inl (t_source tS)"
          using \<open>t_source t = t_source tO\<close> 
                \<open>tO = (Inl (t_source tS), t_input tS, t_output tS, Inl (t_target tS))\<close> by (metis fst_conv)

        have "t_source tS = t_source tP"
          using \<open>t_source t = Inl (t_source tS)\<close>
                \<open>t_source t = t_source t'\<close> 
                \<open>t' = (Inl (t_source tP), t_input tP, t_output tP, Inl (t_target tP))\<close>
          by auto

        have "t_input tS = t_input tP"
          using \<open>t_input t = t_input t'\<close>
                \<open>t_input t = t_input tO\<close>
                \<open>tO = (Inl (t_source tS), t_input tS, t_output tS, Inl (t_target tS))\<close>
                \<open>t' = (Inl (t_source tP), t_input tP, t_output tP, Inl (t_target tP))\<close>
          by auto

        have "tP \<in> h S"
          using \<open>retains_outputs_for_states_and_inputs ?PM S\<close>
          unfolding retains_outputs_for_states_and_inputs_def 
          using \<open>tS \<in> h S\<close> \<open>tP \<in> h ?PM\<close> \<open>t_source tS = t_source tP\<close> \<open>t_input tS = t_input tP\<close> by blast
        then have "shift_Inl tP \<in> h SSep"
          using ssep_transitions_from_old by blast   
        then show ?thesis
          using \<open>t' = (Inl (t_source tP), t_input tP, t_output tP, Inl (t_target tP))\<close> by blast  
      next
        case left_right
        then obtain q1 where "t_source t = Inl q1"
                  and "q1 \<in> nodes S"
                  and "deadlock_state S q1"
                  and f1: "find
                         (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                                     \<exists>t2\<in>set (wf_transitions M).
                                        t_source t1 = fst q1 \<and>
                                        t_source t2 = snd q1 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                         (inputs M) = Some (t_input t)"
          using d_left_sources[of t] d_right_sources[of t]
          by blast 
        have "\<not> (\<exists>t1\<in>set (wf_transitions M).
                         \<exists>t2\<in>set (wf_transitions M).
                            t_source t1 = fst q1 \<and>
                            t_source t2 = snd q1 \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2)"
          using f1
          using find_condition by force 
        then have "\<not> (\<exists>t1\<in>set (wf_transitions (from_FSM M ?q1)).
                         \<exists>t2\<in>set (wf_transitions (from_FSM M ?q2)).
                            t_source t1 = fst q1 \<and>
                            t_source t2 = snd q1 \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2)" 
          using from_FSM_h[OF assms(2)] from_FSM_h[OF assms(3)] by blast
        then have "\<not> (\<exists> tPM \<in> h ?PM . t_source tPM = q1 \<and> t_input tPM = t_input t)"
          by (metis product_transition_split_ob)

        
        moreover have "\<exists> tPM \<in> h ?PM . t_source tPM = q1 \<and> t_input tPM = t_input t" 
          using canonical_separator_product_h_isl[OF \<open>t' \<in> h ?CSep\<close> True] 
          using \<open>t_source t = t_source t'\<close> \<open>t_source t = Inl q1\<close> \<open>t_input t = t_input t'\<close>
          by force 
        ultimately have "False" by blast
        then show ?thesis by blast
      qed
    next
      case False

      have "t_target t' \<in> nodes CSep"
        using \<open>t' \<in> h CSep\<close> by auto

      
      have "t' \<notin> (set (shifted_transitions M ?q1 ?q2))"
        using False by (meson shifted_transitions_targets) 

      
      
      
      
      have *: "set (transitions ?CSep) = (set (shifted_transitions M ?q1 ?q2)) \<union> (set (distinguishing_transitions_left M ?q1 ?q2)) \<union> (set (distinguishing_transitions_right M ?q1 ?q2))"
        using canonical_separator_simps(4)[of M ?q1 ?q2] by auto
      then have t'_cases : "t' \<in> set (distinguishing_transitions_left M ?q1 ?q2) \<or> t' \<in> set (distinguishing_transitions_right M ?q1 ?q2)"
        using \<open>CSep = ?CSep\<close> \<open>t' \<in> h CSep\<close> 
        using canonical_separator_targets(1)[OF \<open>t' \<in> h ?CSep\<close> assms(2,3,4)] False
        by (metis UnE shifted_transitions_targets wf_transition_simp)

      from \<open>t \<in> h SSep\<close> consider 
          (old)         "t \<in> set d_old \<or> t \<in> set d_old_dist_left \<or> t \<in> set d_old_dist_right" |
          (left_right)  "t \<in> set d_left \<or> t \<in> set d_right"
        using d_containment_var by blast
      then have "t' \<in> set (transitions SSep)" proof cases
        case old
        
        show ?thesis proof (cases "t' \<in> set d_old \<union> set d_left \<union> set d_right")
          case True
          then show ?thesis using d_containment_var by blast
        next
          case False
          moreover have "(\<exists>t''\<in>set d_old. t_source t' = t_source t'' \<and> t_input t' = t_input t'')"
            using old \<open>t_source t = t_source t'\<close> \<open>t_input t = t_input t'\<close> 
            using d_old_dist_left_d_old 
            using d_old_dist_right_d_old by metis
          ultimately have "t' \<in> set d_old_dist_left \<or> t' \<in> set d_old_dist_right"
            using t'_cases d_old_dist_left_var d_old_dist_right_var by auto
          then show ?thesis using d_containment_var by blast
        qed
      next
        case left_right
        
        then obtain q where "t_source t = Inl q"
                  and "q \<in> nodes S"
                  and "deadlock_state S q"
                  and "find
                   (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                               \<exists>t2\<in>set (wf_transitions M).
                                  t_source t1 = fst q \<and>
                                  t_source t2 = snd q \<and>
                                  t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                   (inputs M) = Some (t_input t)"
                  and "t_input t \<in> set (inputs SSep)"
                  and "t_output t \<in> set (outputs SSep)"
          using d_left_sources d_right_sources by blast

        then have "s_states_deadlock_input M S q = Some (t_input t)"
          unfolding s_states_deadlock_input_def by auto

        from t'_cases consider
          (t'_left)  "t' \<in> set (distinguishing_transitions_left M ?q1 ?q2)" | 
          (t'_right) "t' \<in> set (distinguishing_transitions_right M ?q1 ?q2)" by blast
        then show ?thesis proof cases
          case t'_left

          obtain q1' q2' tC where "t_source t' = Inl (q1', q2')"
                             and "q1' \<in> nodes M"
                             and "q2' \<in> nodes M"
                             and "tC \<in> set (wf_transitions M)"
                             and "t_source tC = q1'"
                             and "t_input tC = t_input t'"
                             and "t_output tC = t_output t'"
                             and "\<not> (\<exists>t''\<in>set (wf_transitions M). t_source t'' = q2' \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t')"
            using distinguishing_transitions_left_sources_targets[OF t'_left assms(2,3)] by blast
  
          have "q = (q1',q2')"
            using \<open>t_source t = Inl q\<close> \<open>t_source t' = Inl (q1',q2')\<close> \<open>t_source t = t_source t'\<close> by auto
          moreover have "q \<in> nodes ?PM"
            using \<open>q \<in> nodes S\<close> submachine_nodes[OF \<open>is_submachine S ?PM\<close>] by blast
          ultimately have "(q1',q2') \<in> nodes ?PM"
            by auto
  
          have "t_target t' = Inr ?q1"
            using t'_left unfolding distinguishing_transitions_left_def by force
  
  
          have p1: "((q1',q2'), tC) \<in> set (concat
                    (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                      (nodes_from_distinct_paths
                        (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))" 
            using concat_pair_set[of "wf_transitions M" "nodes_from_distinct_paths ?PM"] 
                  \<open>(q1',q2') \<in> nodes ?PM\<close> nodes_code[of ?PM]   \<open>tC \<in> set (wf_transitions M)\<close> by fastforce
  
          have p2: "(\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                         s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) ((q1',q2'), tC)"
          proof
            show "t_source (snd ((q1', q2'), tC)) = fst (fst ((q1', q2'), tC))"
              using \<open>t_source tC = q1'\<close> by simp
            show "s_states_deadlock_input M S (fst ((q1', q2'), tC)) = Some (t_input (snd ((q1', q2'), tC)))"
              using \<open>t_input tC = t_input t'\<close> \<open>s_states_deadlock_input M S q = Some (t_input t)\<close> \<open>q = (q1',q2')\<close> \<open>t_input t = t_input t'\<close> by force
          qed
  
          have p3: "t' = (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S)))) ((q1',q2'), tC)"
          proof -
            let ?t = "(Inl (fst ((q1', q2'), tC)), t_input (snd ((q1', q2'), tC)), t_output (snd ((q1', q2'), tC)), Inr (fst (initial S)))"
  
            have *: "\<And> t1 t2 . t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2 \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> t_target t1 = t_target t2 \<Longrightarrow> t1 = t2"
              by auto
  
            have "t_source t' = t_source ?t" using \<open>t_source t' = Inl (q1', q2')\<close> by auto
            moreover have "t_input t' = t_input ?t" using \<open>t_input tC = t_input t'\<close> by auto
            moreover have "t_output t' = t_output ?t" using \<open>t_output tC = t_output t'\<close> by auto
            moreover have "t_target t' = t_target ?t" using \<open>t_target t' = Inr ?q1\<close>  by auto
            ultimately show "t' = ?t" 
              using *[of t' ?t] by simp
          qed
  
          have f_scheme : "\<And> x x' f g xs . x \<in> set xs \<Longrightarrow> g x \<Longrightarrow> x' = f x \<Longrightarrow> x' \<in> set (map f (filter g xs))" 
            by auto
  
          have "t' \<in> set ?d_left"               
            using f_scheme[of "((q1',q2'), tC)", OF p1, of "(\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                         s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))" t', OF p2,
                         of "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (fst (initial S))))", OF p3]
            by assumption
          then have "t' \<in> set d_left"
            using d_left_var by blast
          then show ?thesis using d_containment_var by blast
        next
          case t'_right

          obtain q1' q2' tC where "t_source t' = Inl (q1', q2')"
                             and "q1' \<in> nodes M"
                             and "q2' \<in> nodes M"
                             and "tC \<in> set (wf_transitions M)"
                             and "t_source tC = q2'"
                             and "t_input tC = t_input t'"
                             and "t_output tC = t_output t'"
                             and "\<not> (\<exists>t''\<in>set (wf_transitions M). t_source t'' = q1' \<and> t_input t'' = t_input t' \<and> t_output t'' = t_output t')"
            using distinguishing_transitions_right_sources_targets[OF t'_right assms(2,3)] by blast
  
          have "q = (q1',q2')"
            using \<open>t_source t = Inl q\<close> \<open>t_source t' = Inl (q1',q2')\<close> \<open>t_source t = t_source t'\<close> by auto
          moreover have "q \<in> nodes ?PM"
            using \<open>q \<in> nodes S\<close> submachine_nodes[OF \<open>is_submachine S ?PM\<close>] by blast
          ultimately have "(q1',q2') \<in> nodes ?PM"
            by auto
  
          have "t_target t' = Inr ?q2"
            using t'_right unfolding distinguishing_transitions_right_def by force
  
  
          have p1: "((q1',q2'), tC) \<in> set (concat
                    (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                      (nodes_from_distinct_paths
                        (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))))))" 
            using concat_pair_set[of "wf_transitions M" "nodes_from_distinct_paths ?PM"] 
                  \<open>(q1',q2') \<in> nodes ?PM\<close> nodes_code[of ?PM]   \<open>tC \<in> set (wf_transitions M)\<close> by fastforce
  
          have p2: "(\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                         s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt))) ((q1',q2'), tC)"
          proof
            show "t_source (snd ((q1', q2'), tC)) = snd (fst ((q1', q2'), tC))"
              using \<open>t_source tC = q2'\<close> by simp
            show "s_states_deadlock_input M S (fst ((q1', q2'), tC)) = Some (t_input (snd ((q1', q2'), tC)))"
              using \<open>t_input tC = t_input t'\<close> \<open>s_states_deadlock_input M S q = Some (t_input t)\<close> \<open>q = (q1',q2')\<close> \<open>t_input t = t_input t'\<close> by force
          qed
  
          have p3: "t' = (\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S)))) ((q1',q2'), tC)"
          proof -
            let ?t = "(Inl (fst ((q1', q2'), tC)), t_input (snd ((q1', q2'), tC)), t_output (snd ((q1', q2'), tC)), Inr (snd (initial S)))"
  
            have *: "\<And> t1 t2 . t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2 \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> t_target t1 = t_target t2 \<Longrightarrow> t1 = t2"
              by auto
  
            have "t_source t' = t_source ?t" using \<open>t_source t' = Inl (q1', q2')\<close> by auto
            moreover have "t_input t' = t_input ?t" using \<open>t_input tC = t_input t'\<close> by auto
            moreover have "t_output t' = t_output ?t" using \<open>t_output tC = t_output t'\<close> by auto
            moreover have "t_target t' = t_target ?t" using \<open>t_target t' = Inr ?q2\<close>  by auto
            ultimately show "t' = ?t" 
              using *[of t' ?t] by simp
          qed
  
          have f_scheme : "\<And> x x' f g xs . x \<in> set xs \<Longrightarrow> g x \<Longrightarrow> x' = f x \<Longrightarrow> x' \<in> set (map f (filter g xs))" 
            by auto
  
          have "t' \<in> set ?d_right"               
            using f_scheme[of "((q1',q2'), tC)", OF p1, of "(\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                         s_states_deadlock_input M S (fst qqt) = Some (t_input (snd qqt)))" t', OF p2,
                         of "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr (snd (initial S))))", OF p3]
            by assumption
          then have "t' \<in> set d_right"
            using d_right_var by blast
          then show ?thesis using d_containment_var by blast
        qed
      qed

      have "t_source t' \<in> nodes SSep"
        using \<open>t_source t = t_source t'\<close> \<open>t \<in> h SSep\<close> by auto

      have "inputs SSep = inputs CSep"
        using \<open>inputs SSep = inputs M\<close>
        using csep_var unfolding canonical_separator_def by simp
      then have "t_input t' \<in> set (inputs SSep)"
        using \<open>t' \<in> h CSep\<close> unfolding wf_transitions.simps by auto 
      
      have "outputs SSep = outputs CSep"
        using \<open>outputs SSep = outputs M\<close>
        using csep_var unfolding canonical_separator_def by simp
      then have "t_output t' \<in> set (outputs SSep)"
        using \<open>t' \<in> h CSep\<close> unfolding wf_transitions.simps by auto

      show ?thesis 
        using \<open>t' \<in> set (transitions SSep)\<close>
        using \<open>t_source t' \<in> nodes SSep\<close> 
        using \<open>t_input t' \<in> set (inputs SSep)\<close>
        using \<open>t_output t' \<in> set (outputs SSep)\<close> by auto
    qed
  qed

  

  have "\<And> q x t t' . q \<in> nodes SSep \<Longrightarrow>
                             x \<in> set (inputs CSep) \<Longrightarrow>
                             t \<in> h SSep \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow>
                             t' \<in> h CSep \<Longrightarrow>
                                 t_source t' = q \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> h SSep" 
  proof -
    fix q x t t' assume "q \<in> nodes SSep"
                    and "x \<in> set (inputs CSep)"
                    and "t \<in> h SSep" and "t_source t = q" and "t_input t = x"
                    and "t' \<in> h CSep" 
                    and "t_source t' = q" and "t_input t' = x"
    then have "t \<in> h SSep \<and> t' \<in> h CSep \<and> t_source t = t_source t' \<and> t_input t = t_input t'"
      by auto
    then show "t' \<in> h SSep"
      using inl_prop_prep by blast
  qed
    


  then have has_retains_property: "\<forall>q\<in>nodes ?SSep.
        \<forall>x\<in>set (inputs ?CSep).
           (\<exists>t \<in> h ?SSep . t_source t = q \<and> t_input t = x) \<longrightarrow>
           (\<forall>t' \<in> h ?CSep.
               t_source t' = q \<and> t_input t' = x \<longrightarrow>
               t' \<in> h ?SSep)" 
    using ssep_var csep_var by blast
    
  show ?thesis
    unfolding is_state_separator_from_canonical_separator_def
    using is_sub is_single_input is_acyclic has_deadlock_left has_deadlock_right has_node_left has_node_right has_inl_property has_retains_property
    by presburger
qed



lemma induces_from_prod: "induces_state_separator M S = induces_state_separator_for_prod M (fst (initial S)) (snd (initial S)) S"
  unfolding induces_state_separator_def induces_state_separator_for_prod_def by blast



  
                                                           
(*
  is_state_separator_from_canonical_separator
            (canonical_separator M (fst (initial S)) (snd (initial S)))
            (fst (initial S))
            (snd (initial S))
            (state_separator_from_product_submachine M S)



  induces_state_separator_for_prod M q1 q2 \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                                                  inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
                                                  outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
                                                  transitions = 
                                                     filter 
                                                       (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                                                  (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))
*)






definition calculate_state_separator_from_s_states :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a, 'b) FSM_scheme option" where
  "calculate_state_separator_from_s_states M q1 q2 = 
    (let PR = product (from_FSM M q1) (from_FSM M q2); SS = (s_states_opt PR (size PR))  in
      (case find_index (\<lambda>qqt . fst qqt = (q1,q2)) SS of
        Some i \<Rightarrow> Some (state_separator_from_product_submachine M \<lparr> initial = (q1,q2),
                                                    inputs = inputs PR,
                                                    outputs = outputs PR,
                                                    transitions = 
                                                       filter 
                                                         (\<lambda>t . \<exists> qqx \<in> set (take (Suc i) SS) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                                                       (wf_transitions PR),
                                                    \<dots> = more M\<rparr>) |
        None \<Rightarrow> None))"


value "calculate_state_separator_from_s_states M_ex_9 0 1"
value "calculate_state_separator_from_s_states M_ex_9 0 2"
value "calculate_state_separator_from_s_states M_ex_9 0 3"
value "calculate_state_separator_from_s_states M_ex_9 3 1"
value "calculate_state_separator_from_canonical_separator_naive M_ex_9 0 3"



lemma calculate_state_separator_from_s_states_soundness :
  assumes "calculate_state_separator_from_s_states M q1 q2 = Some S"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
  and "q1 \<noteq> q2"
  and "completely_specified M"
  shows "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
proof -
  let ?PR = " product (from_FSM M q1) (from_FSM M q2)"
  let ?SS = "(s_states_opt ?PR (size ?PR))"

  obtain i where i_def: "find_index (\<lambda>qqt . fst qqt = (q1,q2)) ?SS = Some i"
    using assms unfolding calculate_state_separator_from_s_states_def Let_def
    by fastforce 
  then have s1: "S = 
        (state_separator_from_product_submachine M
          \<lparr>initial = (q1, q2), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)),
             outputs = outputs (product (from_FSM M q1) (from_FSM M q2)),
             transitions =
               filter
                (\<lambda>t. \<exists>qqx\<in>set (take (Suc i)
                                 (s_states_opt (product (from_FSM M q1) (from_FSM M q2))
                                   (FSM.size (product (from_FSM M q1) (from_FSM M q2))))).
                        t_source t = fst qqx \<and> t_input t = snd qqx)
                (wf_transitions (product (from_FSM M q1) (from_FSM M q2))),
             \<dots> = more M\<rparr>)"
    using assms(1) unfolding calculate_state_separator_from_s_states_def Let_def
    by (metis (mono_tags, lifting) option.inject option.simps(5)) 
  
  
  have "(s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))
                 = s_states ?PR (size ?PR)"
    using s_states_code by metis
  then have "take i (s_states ?PR (size ?PR)) = take i (s_states ?PR (size ?PR))"
    by force
  
  have "i < length (s_states_opt ?PR (size ?PR))"
    using find_index_index(1)[OF i_def] by metis
  then have "i < length (s_states ?PR (size ?PR))"
    using s_states_code by metis
  moreover have "length (s_states ?PR (size ?PR)) \<le> size ?PR"
    using s_states_size by blast
  ultimately have "i < size ?PR" by force


  have "fst (last (take (Suc i) (s_states_opt ?PR (size ?PR)))) = (q1,q2)"
    using find_index_index(2)[OF i_def]
    using take_last_index[OF \<open>i < length (s_states_opt ?PR (size ?PR))\<close>]
    by force

  have "Suc i \<le> size ?PR"
    using \<open>i < size ?PR\<close> by simp
  have "(take (Suc i) (s_states_opt ?PR (size ?PR))) = s_states ?PR (Suc i)"
    using s_states_prefix[OF \<open>Suc i \<le> size ?PR\<close>] s_states_code by metis

  let ?S = "\<lparr>initial = fst (last (s_states ?PR (Suc i))), inputs = inputs ?PR,
             outputs = outputs ?PR,
             transitions =
               filter
                (\<lambda>t. \<exists>qqx\<in>set (s_states ?PR (Suc i)).
                        t_source t = fst qqx \<and> t_input t = snd qqx)
                (wf_transitions ?PR),
             \<dots> = more M\<rparr>"

  have s2 : "S = (state_separator_from_product_submachine M ?S)"
    using s1 
  proof -
    have "fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i))) = (q1, q2)"
      by (metis \<open>fst (last (take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))) = (q1, q2)\<close> \<open>take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)\<close>)
    then show ?thesis
      using \<open>S = state_separator_from_product_submachine M \<lparr>initial = (q1, q2), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>\<close> \<open>take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)\<close> by presburger
  qed 

  have "s_states ?PR (Suc i) \<noteq> []"
    using \<open>i < length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))\<close> \<open>s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))\<close> \<open>take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)\<close> by auto

  have "induces_state_separator_for_prod M q1 q2 ?S"
    using  s_states_induces_state_separator[OF \<open>s_states ?PR (Suc i) \<noteq> []\<close> assms(2,3,4)] by assumption

  then have "induces_state_separator M ?S" 
    using \<open>fst (last (take (Suc i) (s_states_opt ?PR (size ?PR)))) = (q1,q2)\<close> \<open>(take (Suc i) (s_states_opt ?PR (size ?PR))) = s_states ?PR (Suc i)\<close> 
    using induces_from_prod
    by (metis (no_types, lifting) fst_conv select_convs(1) snd_conv) 




  have "fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i) )) = (q1,q2)"
    using \<open>fst (last (take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))) = (q1, q2)\<close> \<open>take (Suc i) (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)\<close> by auto 
  
  have "fst (initial ?S) = q1"
    using \<open>fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i))) = (q1,q2)\<close> by force
  then have "fst (initial ?S) \<in> nodes M"
    using assms(2) by auto

  have "snd (initial ?S) = q2"
    using \<open>fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i))) = (q1,q2)\<close> by force
  then have "snd (initial ?S) \<in> nodes M"
    using assms(3) by auto

  have "fst (initial ?S) \<noteq> snd (initial ?S)"
    using \<open>fst (initial ?S) = q1\<close> \<open>snd (initial ?S) = q2\<close> assms(4) by auto

  have "is_state_separator_from_canonical_separator
   (canonical_separator M (fst (initial ?S)) (snd (initial ?S))) (fst (initial ?S)) (snd (initial ?S))
   (state_separator_from_product_submachine M ?S)"
    using state_separator_from_induces_state_separator
          [OF \<open>induces_state_separator M ?S\<close>
              \<open>fst (initial ?S) \<in> nodes M\<close>
              \<open>snd (initial ?S) \<in> nodes M\<close>
              \<open>fst (initial ?S) \<noteq> snd (initial ?S)\<close>
              \<open>completely_specified M\<close>] by assumption

  then show ?thesis using s2
    by (metis \<open>fst (initial \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>) = q1\<close> \<open>snd (initial \<lparr>initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i))), inputs = inputs (product (from_FSM M q1) (from_FSM M q2)), outputs = outputs (product (from_FSM M q1) (from_FSM M q2)), transitions = filter (\<lambda>t. \<exists>qqx\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc i)). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions (product (from_FSM M q1) (from_FSM M q2))), \<dots> = more M\<rparr>) = q2\<close>) 
qed





lemma s_states_exhaustiveness :
  assumes "r_distinguishable_k M q1 q2 k"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
  and "q1 \<noteq> q2"
shows "\<exists> qqt \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (size (product (from_FSM M q1) (from_FSM M q2)))) . fst qqt = (q1,q2)" 
using assms proof (induction k arbitrary: q1 q2)
  case 0

  let ?PM = "product (from_FSM M q1) (from_FSM M q2)"

  from 0 obtain x where "x \<in> set (inputs M)"
                  and "\<not> (\<exists>t1\<in>set (wf_transitions M).
                            \<exists>t2\<in>set (wf_transitions M).
                               t_source t1 = q1 \<and>
                               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    unfolding r_distinguishable_k.simps by blast
  then have *: "\<not> (\<exists>t1 \<in> h (from_FSM M q1).
                            \<exists>t2 \<in> h (from_FSM M q2).
                               t_source t1 = q1 \<and>
                               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    using from_FSM_h[OF "0.prems"(2)] from_FSM_h[OF "0.prems"(3)] by blast

  then have "\<And> t . t \<in> h ?PM \<Longrightarrow> \<not>(t_source t = (q1,q2) \<and> t_input t = x)"
  proof -
    fix t assume "t \<in> h ?PM"
    show "\<not>(t_source t = (q1,q2) \<and> t_input t = x)"
    proof 
      assume "t_source t = (q1, q2) \<and> t_input t = x"
      then have "(q1, x, t_output t, fst (t_target t)) \<in> set (wf_transitions (from_FSM M q1))"
            and "(q2, x, t_output t, snd (t_target t)) \<in> set (wf_transitions (from_FSM M q2))"
        using product_transition_split[OF \<open>t \<in> h ?PM\<close>] by auto
      then show "False"
        using * by force
    qed
  qed

  have "(q1,q2) \<in> set (nodes_from_distinct_paths ?PM)"
    using nodes_code nodes.initial product_simps(1) from_FSM_simps(1) by metis
  
  have p_find_1: "\<And> k' . (\<forall> t \<in> h ?PM . (t_source t = fst ((q1,q2),x) \<and> t_input t = snd ((q1,q2),x) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM k') . fst qx' = (t_target t))))"
    by (simp add: \<open>\<And>t. t \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))) \<Longrightarrow> \<not> (t_source t = (q1, q2) \<and> t_input t = x)\<close>)

  have p_find_2: "((q1,q2),x) \<in> set (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))"
    using concat_pair_set \<open>x \<in> set (inputs M)\<close> \<open>(q1,q2) \<in> set (nodes_from_distinct_paths ?PM)\<close>
  proof -
    have f1: "\<forall>a ps aa f. set (concat (map (\<lambda>p. map (Pair (p::'a \<times> 'a)) (inputs (product (from_FSM (f::('a, 'b) FSM_scheme) a) (from_FSM f aa)))) ps)) = set (concat (map (\<lambda>p. map (Pair p) (inputs f)) ps))"
      by (simp add: from_FSM_product_inputs)
    have "\<forall>is p ps. p \<in> set (concat (map (\<lambda>p. map (Pair (p::'a \<times> 'a)) is) ps)) \<or> \<not> (fst p \<in> set ps \<and> (snd p::integer) \<in> set is)"
      using concat_pair_set by blast
    then show ?thesis
      using f1 by (metis \<open>(q1, q2) \<in> set (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))\<close> \<open>x \<in> set (inputs M)\<close> fst_conv snd_conv)
  qed 


  have p_find: "\<And> k . (\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx') \<Longrightarrow>
               ((\<lambda> qx . (\<forall> qx' \<in> set (s_states ?PM k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h ?PM . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM k) . fst qx' = (t_target t)))) ((q1,q2),x))
                \<and> ((q1,q2),x) \<in> set (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))"
    using p_find_1 p_find_2
    by (metis fst_conv) 

  have p_find_alt : "\<And> k . (\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx') \<Longrightarrow>
                            find
                              (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k).
                                        fst qx \<noteq> fst qx') \<and>
                                    (\<forall>t\<in>set (wf_transitions ?PM).
                                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                                        (\<exists>qx'\<in>set (s_states ?PM k).
                                            fst qx' = t_target t)))
                              (concat
                                (map (\<lambda>q. map (Pair q) (inputs ?PM))
                                  (nodes_from_distinct_paths ?PM))) \<noteq> None" 
    
  proof -
    fix k assume assm: "(\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx')"
    show "find
            (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions ?PM). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states ?PM k). fst qx' = t_target t)))
            (concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM))) \<noteq> None"
      using find_None_iff[of "(\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions ?PM). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states ?PM k). fst qx' = t_target t)))"
                             "(concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))" ]
            p_find[OF assm] by blast
  qed
          






  have "\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM))"
  proof (rule ccontr)
    assume "\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM)))"
    
    let ?l = "length (s_states ?PM (size ?PM))"
    have "s_states ?PM (size ?PM) = s_states ?PM ?l"
      by (metis (no_types, hide_lams) s_states_self_length)

    then have l_assm: "\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM ?l))"
      using \<open>\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM)))\<close> by auto
    
    then have "(q1,q2) \<notin> set (map fst (s_states ?PM ?l))" by auto

    have "?l \<le> size ?PM"
      using s_states_length by blast
      

    then consider  
      (a) "?l = 0" |
      (b) "0 < ?l \<and> ?l < size ?PM" |
      (c) "?l = size ?PM"
      using nat_less_le by blast
    then show "False" proof cases
      case a 
      
      then have "(s_states ?PM (Suc 0)) = []"
        by (metis s_states_prefix s_states_self_length s_states_size take_eq_Nil)
      then have *: "find
              (\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t)))
              (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) = None"
        unfolding s_states.simps
        using find_None_iff by fastforce 
      then have "\<not>(\<exists> qqt \<in> set (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) . (\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t))) qqt)"
        unfolding s_states.simps
        using find_None_iff[of "(\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t)))" "(concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))" ] by blast
      then have "\<not>(\<exists> qqt \<in> set (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) . (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM 0). fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set (s_states ?PM 0). fst qx' = t_target t))) qqt)"
        unfolding s_states.simps by assumption

      then show "False"
        using p_find[of 0]
        by (metis \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> a length_0_conv length_greater_0_conv length_pos_if_in_set)  

    next 
      case b
      
      then obtain l' where Suc: "?l = Suc l'" using gr0_conv_Suc by blast
      moreover obtain l where "l = ?l" by auto
      ultimately have "l = Suc l'" by auto

      have "s_states ?PM ?l = s_states ?PM (Suc ?l)"
        using s_states_prefix[of ?l "Suc ?l"] s_states_max_iterations
      proof -
        have "\<forall>n. n \<le> Suc n"
          by simp
        then show ?thesis
          by (metis Suc_le_mono \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> s_states_length s_states_max_iterations s_states_prefix take_all)
      qed 

      have "length (s_states ?PM l') < length (s_states ?PM ?l)" using Suc
        using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> less_Suc_eq_le s_states_length by auto

      have "length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) = l"
        using \<open>l = length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))\<close> \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> by auto
      then have "\<not>(length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) < l)"
        by force

      have "\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). (q1, q2) \<noteq> fst qx'"
        using l_assm \<open>l = ?l\<close>
        by auto 

      have "s_states ?PM l = s_states ?PM (Suc l)"
      proof -
        show ?thesis
          using \<open>length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = Suc l'\<close> \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))))\<close> 
          using \<open>l = Suc l'\<close>
          by presburger
      qed
      then have "s_states ?PM l = (case find
                (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                          fst qx \<noteq> fst qx') \<and>
                      (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                              fst qx' = t_target t)))
                (concat
                  (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) of
          None \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l
          | Some qx \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [qx])"
        unfolding s_states.simps
        using \<open>\<not>(length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) < l)\<close> by force

      then have "find
                (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                          fst qx \<noteq> fst qx') \<and>
                      (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                              fst qx' = t_target t)))
                (concat
                  (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) = None"
      proof -
        have "s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [the (find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) l) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) l) \<and> fst p = t_target pa))) (concat (map (\<lambda>p. map (Pair p) (inputs (product (from_FSM M q1) (from_FSM M q2)))) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))] \<noteq> s_states (product (from_FSM M q1) (from_FSM M q2)) l"
          by force
        then show ?thesis
          using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) l = (case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2)))) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) of None \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l | Some qx \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [qx])\<close> by force
      qed 

      then show "False" using p_find_alt[OF \<open>\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). (q1, q2) \<noteq> fst qx'\<close>] by blast
    next
      case c
      have "distinct (map fst (s_states ?PM ?l))"
        using s_states_distinct_states by blast
      then have "card (set (map fst (s_states ?PM ?l))) = size ?PM"
        using c distinct_card by fastforce 
      moreover have "set (map fst (s_states ?PM ?l)) \<subseteq> nodes ?PM"
        using s_states_nodes by metis
      ultimately have "set (map fst (s_states ?PM ?l)) = nodes ?PM"
        using nodes_finite[of ?PM]
        by (simp add: card_subset_eq) 

      then  have "(q1,q2) \<notin> nodes ?PM"
        using \<open>(q1,q2) \<notin> set (map fst (s_states ?PM ?l))\<close>
        by blast 
      moreover have "(q1,q2) \<in> nodes ?PM"
        using nodes.initial[of ?PM] product_simps(1) from_FSM_simps(1) by metis
      ultimately show "False" 
        by blast
    qed 
  qed

  then show ?case
    by (meson fst_conv)
next
  case (Suc k)
  (* sketch: 
    \<longrightarrow> cases Suc k = LEAST,
      \<longrightarrow> FALSE: then also k \<longrightarrow> by IH
      \<longrightarrow> TRUE
        \<longrightarrow> \<noteq> 0
        \<longrightarrow> exists input x such that for every ((q1,q2),x,y,(s1,s2)) \<in> h ?PM , s1 and s2 are r(k)-d
          \<longrightarrow> (s1,s2) is contained in s_states for product for s1 s2
          \<longrightarrow> also: (s1,s2) (initial state of the above) is a node of product for q1 q2
          \<longrightarrow> (TODO: proof) then (s1,s2) is in s_states for product for q1 q2
          \<longrightarrow> moreover (s1,s2) \<noteq> (q1,q2) due to Suc k being the LEAST (case "=" also directly satisfies the goal)
          \<longrightarrow> by construction there must then exist some x' s.t. ((q1,q2),x') \<in> s_states 
  *)
  then show ?case sorry
qed


end (*
OPT: 
  shows "\<exists> qqt \<in> set (s_states_opt (product (from_FSM M q1) (from_FSM M q2)) (size (product (from_FSM M q1) (from_FSM M q2)))) . fst qqt = (q1,q2)"

product (from_FSM M q1) (from_FSM M q2); SS = (s_states_opt PR (size PR)) 

lemma calculate_state_separator_from_s_states_exhaustiveness

find_index (\<lambda>qqt . fst qqt = (q1,q2)) SS

end (*
          



(* TODO:
  - Show that r-d implies that this alg produces a result (?)
*)




          
end (*




(*
lemma induces_from_prod :
  assumes "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
shows "induces_state_separator M S = induces_state_separator_for_prod M q1 q2 S"
proof -

  let ?PMS = "(product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))"
  let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"

  obtain P where P_def: "P = (is_submachine S ?PMS \<and>
                                single_input S \<and>
                                FSM.acyclic S \<and>
                                (\<forall>qq\<in>nodes S.
                                    deadlock_state S qq \<longrightarrow>
                                    (\<exists>x\<in>set (inputs M).
                                        \<not> (\<exists>t1\<in>set (wf_transitions M).
                                               \<exists>t2\<in>set (wf_transitions M).
                                                  t_source t1 = fst qq \<and>
                                                  t_source t2 = snd qq \<and>
                                                  t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))))" by blast

  have p1: "induces_state_separator M S = (P \<and> (retains_outputs_for_states_and_inputs ?PMS S))"
    unfolding induces_state_separator_def using P_def by blast
  
  have p2: "induces_state_separator_for_prod M q1 q2 S = (P \<and> retains_outputs_for_states_and_inputs ?PM S)"
    unfolding induces_state_separator_for_prod_def using P_def by blast


  show ?thesis proof (cases P)
    case True
    then have "is_submachine S ?PMS" using P_def by blast
    

    have "(retains_outputs_for_states_and_inputs (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))) S) = (retains_outputs_for_states_and_inputs (product (from_FSM M q1) (from_FSM M q2)) S)"
      unfolding retains_outputs_for_states_and_inputs_def
    proof 
       

    ultimately show ?thesis using p1 p2 by blast
  next
    case False
    then show ?thesis using p1 p2 by blast
  qed
qed

*)



lemma calculate_separator_merge_induces_state_separator :
  assumes "\<And> qq S. f qq = Some S \<Longrightarrow> induces_state_separator Q S"
  and     "\<And> t . t \<in> h (product (from_FSM Q q1) (from_FSM Q q2)) 
                \<Longrightarrow> t_source t = (q1,q2) 
                \<Longrightarrow> t_input t = x 
                \<Longrightarrow> f (t_target t) \<noteq> None"
shows "induces_state_separator Q (calculate_separator_merge M (q1,q2) x f)"
  (* TODO? *)

end (*

lemma merge_FSMs_induces_state_separator :
  assumes "\<exists> t \<in> h M . t_source t = initial M \<and> t_target t = initial S \<and> (\<forall> t' \<in> h M . t_target t' = initial S \<longrightarrow> t' = t)"
  and "\<forall> t \<in> h M . t_source t = initial M \<longrightarrow> induces_state_separator Q (from_FSM M (t_target t))
  and "initial M \<notin> nodes S"
  and "acyclic M"
  and "acyclic S"
  and "inputs M = inputs S"
  and "outputs M = outputs S"  





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