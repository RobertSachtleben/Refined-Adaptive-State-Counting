theory Adaptive_Test_Case
imports State_Separator 
begin

definition is_ATC :: "('a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_ATC M = (single_input M \<and> acyclic M)"

fun pass_ATC' :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> nat \<Rightarrow> bool" where
  "pass_ATC' M A fail_states 0 = (\<not> (initial A \<in> fail_states))" |
  "pass_ATC' M A fail_states (Suc k) = ((\<not> (initial A \<in> fail_states)) \<and> (case find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) of
    None \<Rightarrow> True |
    Some x \<Rightarrow> \<forall> t \<in> h M . (t_input t = x \<and> t_source t = initial M) \<longrightarrow> (\<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<and> t_output t' = t_output t \<and> pass_ATC' (from_FSM M (t_target t)) (from_FSM A (t_target t')) fail_states k)))"

fun pass_ATC :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> bool" where
  "pass_ATC M A fail_states = pass_ATC' M A fail_states (size A)"

fun pass_separator_ATC :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pass_separator_ATC M S q1 q2 = pass_ATC (from_FSM M q1) S {Inr q2}"

value "the (calculate_state_separator_from_s_states M_ex_H 1 4)"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 4)) 1 4"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 4)) 4 1"

value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 4}"
value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 1}"
value "pass_ATC (from_FSM M_ex_H 4) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 4}"
value "pass_ATC (from_FSM M_ex_H 4) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 1}"

value "the (calculate_state_separator_from_s_states M_ex_H 1 3)"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 3)) 1 3"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 3)) 3 1"

value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 3}"
value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 1}"
value "pass_ATC (from_FSM M_ex_H 3) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 3}"
value "pass_ATC (from_FSM M_ex_H 3) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 1}"


end