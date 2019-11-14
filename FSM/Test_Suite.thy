theory Test_Suite
imports Traversal_Set State_Preamble State_Separator
begin

type_synonym IO_Sequence = "(Input \<times> Output) list"
type_synonym Preamble_Sequence = IO_Sequence
type_synonym Traversal_Sequence = IO_Sequence
type_synonym Test_Sequences = "IO_Sequence list"

type_synonym Test_Case = "(Preamble_Sequence \<times> ((Traversal_Sequence \<times> Test_Sequences) list))"
type_synonym Test_Case' = "(Preamble_Sequence set \<times> ((Traversal_Sequence \<times> Test_Sequences) list))"

(* after each traversal sequence all state separators that r-d the reached state from some other state are added *)
(* TODO: add only relevant separators *)
fun test_suite_naive :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> Test_Case' list" where
  "test_suite_naive M m = (let qqSS = r_distinguishable_state_pairs_with_separators_naive M; 
                               MRS = maximal_repetition_sets_from_separators M;
                               Q = map 
                                    (\<lambda> qp . (snd qp, map 
                                              (\<lambda> t . (p_io t, concat (map 
                                                          (\<lambda> qqS . LS_acyclic_opt (snd qqS))
                                                          (filter 
                                                                  (\<lambda> qqS . fst (fst qqS) = fst qp)                                                        
                                                                  qqSS))))
                                              (m_traversal_paths M (fst qp) MRS m))) 
                                    (d_reachable_states_with_preambles M) 

                          in Q)"

value "test_suite_naive M_ex_H 4"
value "test_suite_naive M_ex_9 4"

end