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
    (* initial S = (q1,q2) *)
    is_submachine S (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S))))
    \<and> single_input S
    \<and> acyclic S
    \<and> (\<forall> qq \<in> nodes S . deadlock_state S qq \<longrightarrow> (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = fst qq \<and> t_source t2 = snd qq \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) )
    \<and> retains_outputs_for_states_and_inputs (product (from_FSM M (fst (initial S))) (from_FSM M (snd (initial S)))) S
)"



fun s_states :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ('a \<times> Input) list" where
  "s_states C 0 = (case find 
            (\<lambda> qx . \<not> (\<exists> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx))) 
            (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
      of Some qx \<Rightarrow> [qx] | 
         None \<Rightarrow> [])" |
  "s_states C (Suc k) =  
    (if length (s_states C k) \<le> k 
      then (s_states C k)
      else (case find 
                  (\<lambda> qx . (\<forall> qx' \<in> set (s_states C k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h C . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states C k) . fst qx' = (t_target t)))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs C)) (nodes_from_distinct_paths C)))
            of Some qx \<Rightarrow> (s_states C k)@[qx] | 
               None \<Rightarrow> (s_states C k)))"

fun s_states' :: "('a \<times> Input) list \<Rightarrow> 'a Transition set \<Rightarrow> nat \<Rightarrow> ('a \<times> Input) list" where
  "s_states' QX H 0 = (case find (\<lambda> qx . \<not> (\<exists> t \<in> H . (t_source t = fst qx \<and> t_input t = snd qx))) QX
      of Some qx \<Rightarrow> [qx] | 
         None \<Rightarrow> [])" |
  "s_states' QX H (Suc k) = (let Q = s_states' QX H k in 
    (if length Q \<le> k 
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
  "length (s_states M k) \<le> Suc k"
proof (induction k)
  case 0
  then show ?case unfolding s_states.simps
    by (metis (no_types, lifting) eq_iff le_SucI length_Cons list.size(3) option.case_eq_if) 
next
  case (Suc k)
  show ?case
  proof (cases "length (s_states M k) \<le> k")
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
      by (metis (mono_tags, lifting) False eq_iff le_SucE le_SucI length_append_singleton option.case_eq_if) 
  qed
qed

lemma s_states_prefix :
  assumes "i \<le> k"
  shows "take (Suc i) (s_states M k) = s_states M i"
  using assms proof (induction k)
  case 0
  then show ?case unfolding s_states.simps
    by (metis le_zero_eq  s_states.simps(1) s_states_length take_all) 
next
  case (Suc k)
  then show ?case proof (cases "i \<le> k")
    case True
    then have "take (Suc i) (s_states M k) = s_states M i"
      using Suc by auto
    then have "length (s_states M i) \<le> length (s_states M k)"
      by (metis dual_order.trans nat_le_linear s_states_length take_all)
    moreover have "take (length (s_states M k)) (s_states M (Suc k)) = s_states M k"
      unfolding s_states.simps
      by (simp add: option.case_eq_if) 
    ultimately have "take (Suc i) (s_states M (Suc k)) = take (Suc i) (s_states M k)"
      using True \<open>take (Suc i) (s_states M k) = s_states M i\<close>
    proof -
      have f1: "\<forall>ps psa psb. take (length (psb::('a \<times> integer) list)) (ps @ psa) = psb \<or> take (length psb) ps \<noteq> psb"
        by force
      have "s_states M (Suc k) = s_states M k \<or> length (s_states M i) = Suc i"
        by (metis (no_types) Suc_le_mono \<open>i \<le> k\<close> \<open>take (Suc i) (s_states M k) = s_states M i\<close> le_SucE length_take min.absorb2 s_states.simps(2) s_states_length)
      then show ?thesis
        using f1 by (metis (no_types) \<open>take (Suc i) (s_states M k) = s_states M i\<close> \<open>take (length (s_states M k)) (s_states M (Suc k)) = s_states M k\<close> append_eq_conv_conj)
    qed
    then show ?thesis 
      using \<open>take (Suc i) (s_states M k) = s_states M i\<close> by simp
  next
    case False 
    then have "i = Suc k" using Suc.prems by auto
    
    then show ?thesis
      using s_states_length take_all by blast 
  qed
qed

lemma s_states_self_length :
  "s_states M (Suc k) = s_states M (length (s_states M k))" 
  using s_states_prefix 
  by (metis (no_types) Suc_n_not_le_n le_SucE nat_le_linear s_states.simps(2) s_states_length s_states_prefix take_all)

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
    then have "i = 0"
      unfolding s_states.simps 
      by (meson "0.prems" less_Suc0 less_le_trans s_states_length) 
    then have "s_states M 0 \<noteq> []"
      using 0 by auto
    then obtain qx where qx_def : "s_states M 0 = [qx]"
      unfolding s_states.simps
      by (metis (no_types, lifting) option.case_eq_if) 
    then have *: "find 
            (\<lambda> qx . \<not> (\<exists> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx))) 
            (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
      unfolding s_states.simps
      by (metis (mono_tags, lifting) \<open>s_states M 0 = [qx]\<close> \<open>s_states M 0 \<noteq> []\<close> list.sel(1) option.case_eq_if option.collapse)
    
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
        have "\<forall>n f na. length (s_states (f::('a, 'b) FSM_scheme) na) \<le> n \<or> \<not> na < n"
          by (meson Suc_leI dual_order.trans s_states_length)
        then show ?thesis
          by (metis Suc.prems \<open>\<And>k M. i \<le> k \<Longrightarrow> take (Suc i) (s_states M k) = s_states M i\<close> \<open>i < length (s_states M k)\<close> not_le take_last_index)
      qed 
      moreover have "take i (s_states M k) = take i (s_states M (Suc k))"
      proof -
        obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
          "\<forall>x0 x1. (\<exists>v2. x0 = Suc (x1 + v2)) = (x0 = Suc (x1 + nn x0 x1))"
        by moura
        then have "\<forall>n na. \<not> n < na \<or> na = Suc (n + nn na n)"
          using less_imp_Suc_add by presburger
        then have "Suc (i + nn (length (s_states M k)) i) \<le> Suc k"
          by (simp add: True s_states_length)
        then have "i \<le> k"
          by linarith
        then have "take i (s_states M k) @ [hd (drop i (s_states M k))] = take i (s_states M (Suc k)) @ [hd (drop i (s_states M k))]"
          by (metis (no_types) Suc.prems True \<open>s_states M k ! i = s_states M (Suc k) ! i\<close> hd_drop_conv_nth le_Suc_eq s_states_prefix take_hd_drop)
        then show ?thesis
          by blast
      qed
        
      ultimately show ?thesis using Suc.IH[OF True] by presburger
    next
      case False
      then have "i = length (s_states M k)"
      proof -
        have f1: "length (s_states M k) \<le> i"
          using False leI by blast
        have f2: "i < Suc (Suc k)"
          by (meson Suc.prems dual_order.strict_trans1 s_states_length)
        have "\<not> length (s_states M k) \<le> k"
          using False Suc.prems by force
        then show ?thesis
          using f2 f1 by linarith
      qed 
      then have "(s_states M (Suc k)) ! i = last (s_states M (Suc k))"
      proof -
        have "s_states M (Suc k) = s_states M i"
          using \<open>i = length (s_states M k)\<close> s_states_self_length by blast
        then show ?thesis
          by (metis (no_types) \<open>i < length (s_states M (Suc k))\<close> append_Nil2 append_eq_conv_conj le_SucE not_le s_states_length take_last_index)
      qed 
      then have "(s_states M (Suc k)) = (s_states M k)@[last (s_states M (Suc k))]"
      proof -
        have "\<forall>n na. (Suc n = na \<or> \<not> Suc n \<le> na) \<or> \<not> na \<le> n"
          by (meson eq_iff le_SucI)
        then have "Suc k = i"
          by (metis (no_types) Suc.prems \<open>i = length (s_states M k)\<close> eq_iff leI not_less_eq s_states.simps(2) s_states_length)
        then show ?thesis
          by (metis (no_types) Suc.prems \<open>s_states M (Suc k) ! i = last (s_states M (Suc k))\<close> eq_iff le_SucI s_states_prefix take_Suc_conv_app_nth)
      qed
      then have *: "find 
                  (\<lambda> qx . (\<forall> qx' \<in> set (s_states M k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states M k) . fst qx' = (t_target t)))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) = Some (last (s_states M (Suc k)))"
        unfolding s_states.simps(2)
      proof -
        assume "(if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx]) = s_states M k @ [last (if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx])]"
        then have f1: "\<not> length (s_states M k) \<le> k"
          by force
        then have f2: "last (if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]) = last (case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])"
          by presburger
        have "\<not> length (s_states M k) \<le> k \<and> s_states M k @ [last (s_states M k)] \<noteq> s_states M k"
          using f1 by blast
        then have "find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
        proof -
          have "s_states M k @ [last (if length (s_states M k) \<le> k then s_states M k else case None of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])] \<noteq> (case None of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])"
            by auto
          then show ?thesis
            by (metis (full_types, lifting) \<open>(if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx]) = s_states M k @ [last (if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states M k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states M k). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some qx \<Rightarrow> s_states M k @ [qx])]\<close> \<open>\<not> length (s_states M k) \<le> k \<and> s_states M k @ [last (s_states M k)] \<noteq> s_states M k\<close>)
        qed
        then have "Some (last (case find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p])) = find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states M k) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states M k) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M)))"
          by force
        then show "find (\<lambda>p. (\<forall>pa\<in>set (s_states M k). fst p \<noteq> fst pa) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p\<in>set (s_states M k). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = Some (last (if length (s_states M k) \<le> k then s_states M k else case find (\<lambda>p. (\<forall>pa\<in>set (s_states M k). fst p \<noteq> fst pa) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p\<in>set (s_states M k). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> s_states M k | Some p \<Rightarrow> s_states M k @ [p]))"
          using f2 by metis
      qed

      let ?qx = "last (s_states M (Suc k))"
      

      have "?qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
        using find_set[OF *] by assumption
      then have "fst ?qx \<in> nodes M \<and> snd ?qx \<in> set (inputs M)"
        using nodes_code[of M] concat_pair_set[of "inputs M" "nodes_from_distinct_paths M"] by blast
      moreover have "(\<forall>qx'\<in>set (take i (s_states M (Suc k))). fst ?qx \<noteq> fst qx')"
        by (metis find_condition[OF *] \<open>i = length (s_states M k)\<close> \<open>s_states M (Suc k) = s_states M k @ [last (s_states M (Suc k))]\<close> append_eq_conv_conj)
      moreover have "(\<forall>t\<in>set (wf_transitions M).
        t_source t = fst (s_states M (Suc k) ! i) \<and> t_input t = snd (s_states M (Suc k) ! i) \<longrightarrow>
        (\<exists>qx'\<in>set (take i (s_states M (Suc k))). fst qx' = t_target t))"
      proof -
        obtain pp :: "'a \<times> integer \<times> integer \<times> 'a \<Rightarrow> 'a \<times> integer" where
          f1: "\<forall>p. (p \<notin> set (wf_transitions M) \<or> t_source p \<noteq> fst (last (s_states M (Suc k))) \<or> t_input p \<noteq> snd (last (s_states M (Suc k)))) \<or> pp p \<in> set (s_states M k) \<and> fst (pp p) = t_target p"
          by (metis (full_types) find_condition[OF *])
        have f2: "length (s_states M k) \<le> k \<or> length (s_states M k) = Suc k"
          by (meson le_SucE s_states_length)
        have f3: "\<not> length (s_states M k) \<le> k \<longrightarrow> k \<le> k"
          by simp
        have "s_states M (Suc k) \<noteq> s_states M k"
          using \<open>s_states M (Suc k) = s_states M k @ [last (s_states M (Suc k))]\<close> by force
        then have "\<not> length (s_states M k) \<le> k"
          by force
        then show ?thesis
          using f3 f2 f1 by (metis (no_types) \<open>i = length (s_states M k)\<close> \<open>s_states M (Suc k) ! i = last (s_states M (Suc k))\<close> \<open>s_states M (Suc k) = s_states M k @ [last (s_states M (Suc k))]\<close> butlast_snoc length_append_singleton lessI s_states_prefix take_butlast)
      qed
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

lemma s_states_size :
  "length (s_states M k) \<le> size M"
proof -
  have "set (map fst (s_states M k)) \<subseteq> nodes M"
    using s_states_index_properties(1)[of _ M k]  list_property_from_index_property[of "map fst (s_states M k)" "\<lambda>q . q \<in> nodes M"]
    by fastforce
  then show ?thesis 
    using s_states_distinct_states[of M k]
          nodes_finite[of M]
    by (metis card_mono distinct_card length_map size_def) 
qed
  
lemma s_states_max_iterations :
  assumes "k \<ge> size M"
  shows "s_states M k = s_states M (size M)"
  using s_states_size[of M k] s_states_prefix[OF assms, of M]
  by simp 


nitpick_params[timeout= 180]

lemma s_states_induce_state_separator :
  assumes "(s_states (product (from_FSM M q1) (from_FSM M q2)) k) \<noteq> []"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
  and "q1 \<noteq> q2"
shows "induces_state_separator M \<lparr> initial = fst (last (s_states (product (from_FSM M q1) (from_FSM M q2)) k)),
                                   inputs = inputs M,
                                   outputs = outputs M,
                                   transitions = 
                                      filter 
                                        (\<lambda>t . \<exists> qqx \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) k) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                                        (wf_transitions (product (from_FSM M q1) (from_FSM M q2))) \<rparr>" 
  nitpick
using assms proof (induction i)
  case 0
  then show ?case sorry
next
  case (Suc i)
  then show ?case sorry
qed








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