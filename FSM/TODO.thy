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

definition retains_outputs_for_states_and_inputs :: "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> bool" where
  "retains_outputs_for_states_and_inputs M S = (\<forall> tS \<in> h S . \<forall> tM \<in> h M . (t_source tS = t_source tM \<and> t_input tS = t_input tM) \<longrightarrow> tM \<in> h S)"

(* possible approach to showing that a separator can be constructed from sub-separators *)
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
  and "\<And> t . t \<in> set qts \<Longrightarrow> 
                    t \<in> h (product (from_FSM M q1) (from_FSM M q2)) \<and>
                    t_source t = (q1,q2) \<and>
                    (\<exists> S \<in> set SS . initial S = t_target t)"
shows " inputs (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) = inputs M \<and> 
        outputs (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) = outputs M \<and> 
        single_input (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) \<and> 
        acyclic (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) \<and>
        h (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) \<subseteq> h (product (from_FSM M q1) (from_FSM M q2)) \<and> 
        retains_outputs_for_states_and_inputs (product (from_FSM M q1) (from_FSM M q2)) (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) \<and>
        (\<forall> q \<in> nodes (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) . deadlock_state (merge_sub_intersections (inputs M) (outputs M) (q1,q2) qts SS) q \<longrightarrow> ((\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = (fst q) \<and> t_source t2 = (snd q) \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))))"  

using assms proof (induction SS rule: rev_induct)
  case Nil
  show ?case using \<open>[] \<noteq> []\<close> by presburger
next
  case (snoc S SS)
  then show ?case proof (cases "SS = []")
    case True
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