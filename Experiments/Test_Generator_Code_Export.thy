section \<open>Code Export\<close>

text \<open>This theory exports the two test suite generation algorithms given in @{text "Test_Suite_Calculation"}.\<close>

theory Test_Generator_Code_Export
  imports Test_Suite_Calculation_Refined
          "HOL-Library.Code_Target_Nat"
begin



derive linorder list

definition generate_test_suite_naive :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list set" where
  "generate_test_suite_naive M m = calculate_test_suite_naive_as_io_sequences M (nat_of_integer m)"

definition generate_test_suite_greedy :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list set" where
  "generate_test_suite_greedy M m = calculate_test_suite_greedy_as_io_sequences M (nat_of_integer m)"

definition count_maximal_repetition_sets_from_separators_naive :: "(integer,integer,integer) fsm \<Rightarrow> integer" where
  "count_maximal_repetition_sets_from_separators_naive M = integer_of_nat (length (maximal_repetition_sets_from_separators_list_naive M))"

definition count_maximal_repetition_sets_from_separators_greedy :: "(integer,integer,integer) fsm \<Rightarrow> integer" where
  "count_maximal_repetition_sets_from_separators_greedy M = integer_of_nat (length (maximal_repetition_sets_from_separators_list_greedy M))"

definition count_test_suite_naive :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> integer" where
  "count_test_suite_naive M m = integer_of_nat (card (generate_test_suite_naive M m))"

definition count_test_suite_greedy :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> integer" where
  "count_test_suite_greedy M m = integer_of_nat (card (generate_test_suite_greedy M m))"


definition generate_test_suite_naive_list :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list list" where
  "generate_test_suite_naive_list M m = sorted_list_of_set (calculate_test_suite_naive_as_io_sequences M (nat_of_integer m))"

definition generate_test_suite_greedy_list :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list list" where
  "generate_test_suite_greedy_list M m = sorted_list_of_set (calculate_test_suite_greedy_as_io_sequences M (nat_of_integer m))"



export_code generate_test_suite_naive 
            generate_test_suite_greedy 
            count_test_suite_naive 
            count_maximal_repetition_sets_from_separators_naive 
            count_test_suite_greedy 
            count_maximal_repetition_sets_from_separators_greedy
            fsm_from_list 
            size 
            integer_of_nat 
            generate_test_suite_naive_list
            generate_test_suite_greedy_list
in Haskell module_name AdaptiveTestSuiteGenerator

end