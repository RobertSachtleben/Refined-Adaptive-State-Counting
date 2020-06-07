section \<open>Code Export\<close>

text \<open>This theory exports the two test suite generation algorithms given in @{text "Test_Suite_Calculation"}.\<close>

theory Test_Generator_Code_Export
  imports Test_Suite_Calculation_Refined
          "HOL-Library.Code_Target_Nat"
begin


subsection \<open>Generating the Test Suite as a List of Input-Output Sequences\<close>

derive linorder list

(* the call to sorted_list_of_set should not produce any significant overhead as the RBT-set is 
   already 'sorted' *)
definition generate_test_suite_naive :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> String.literal + (integer\<times>integer) list list" where
  "generate_test_suite_naive M m = (case (calculate_test_suite_naive_as_io_sequences_with_assumption_check M (nat_of_integer m)) of
    Inl err \<Rightarrow> Inl err |
    Inr ts \<Rightarrow> Inr (sorted_list_of_set ts))"

definition generate_test_suite_greedy :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> String.literal + (integer\<times>integer) list list" where
  "generate_test_suite_greedy M m = (case (calculate_test_suite_greedy_as_io_sequences_with_assumption_check M (nat_of_integer m)) of
    Inl err \<Rightarrow> Inl err |
    Inr ts \<Rightarrow> Inr (sorted_list_of_set ts))"



export_code Inl
            fsm_from_list 
            size 
            integer_of_nat 
            generate_test_suite_naive
            generate_test_suite_greedy
in Haskell module_name AdaptiveTestSuiteGenerator

end