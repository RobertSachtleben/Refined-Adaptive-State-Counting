theory Helper_Algorithms
imports R_Distinguishability State_Preamble
begin

value "Pow {1::nat,2}"

(* calculate all pairs of r_distinguishable states *)
fun r_distinguishable_state_pairs :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> 'a) list" where
  "r_distinguishable_state_pairs M = filter (\<lambda> qq . is_r_distinguishable M (fst qq) (snd qq)) (concat (map (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (nodes_from_distinct_paths M)) (nodes_from_distinct_paths M)))"

value "r_distinguishable_state_pairs M_ex_H"
value "r_distinguishable_state_pairs M_ex_9"

lemma r_distinguishable_state_pairs_set : "set (r_distinguishable_state_pairs M) = {(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> is_r_distinguishable M q1 q2}"
  (is "set ?CalcPairs = ?DistPairs")
proof -
  let ?Concs = "(concat (map (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (nodes_from_distinct_paths M)) (nodes_from_distinct_paths M)))"
  let ?Pairs = "{(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M}"
  
  have "set ?Concs = ?Pairs"
    by (metis (no_types) cartesian_product_list.simps cartesian_product_list_set nodes_code)
  moreover have "set ?CalcPairs = {qq . qq \<in> set ?Concs \<and> is_r_distinguishable M (fst qq) (snd qq)}"
    by (metis r_distinguishable_state_pairs.simps set_filter)
  moreover have "?DistPairs = {qq . qq \<in> ?Pairs \<and> is_r_distinguishable M (fst qq) (snd qq)}"
    using prod.collapse by auto 
  ultimately show ?thesis by blast
qed
    
    

(* calculate sets of pairwise r_distinguishable states *)
fun pairwise_r_distinguishable_state_sets :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets M = {S \<in> Pow (set (nodes_from_distinct_paths M)) . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> set (r_distinguishable_state_pairs M)}"
  
value "pairwise_r_distinguishable_state_sets M_ex_H"


fun maximal_pairwise_r_distinguishable_state_sets :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "maximal_pairwise_r_distinguishable_state_sets M = (let PR = pairwise_r_distinguishable_state_sets M in {S \<in> PR . \<not>(\<exists> S' \<in> PR . S \<subset> S')})"

value "maximal_pairwise_r_distinguishable_state_sets M_ex_H"


(* calculate d-reachable states and a fixed assignment of preambles *)
fun d_reachable_states_with_preambles :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> ((Input \<times> Output) list set)) list" where
  "d_reachable_states_with_preambles M = map (\<lambda> qp . (fst qp, the (snd qp))) (filter (\<lambda> qp . snd qp \<noteq> None) (map (\<lambda> q . (q,calculate_preamble_set_naive M q)) (nodes_from_distinct_paths M)))"

value "d_reachable_states_with_preambles M_ex_H"

fun d_reachable_states :: "('a,'b) FSM_scheme \<Rightarrow> 'a list" where
  "d_reachable_states M = (map fst (d_reachable_states_with_preambles M))"

value "d_reachable_states M_ex_H"

(* calculate maximal sets of pairwise r_distinguishable states and their respective subsets of d-reachable states *)
fun maximal_repetition_sets :: "('a,'b) FSM_scheme \<Rightarrow> ('a set \<times> 'a set) set" where
  "maximal_repetition_sets M = image (\<lambda> S . (S, {q \<in> S . q \<in> set (d_reachable_states M)})) (maximal_pairwise_r_distinguishable_state_sets M)"

value "maximal_repetition_sets M_ex_H"
end