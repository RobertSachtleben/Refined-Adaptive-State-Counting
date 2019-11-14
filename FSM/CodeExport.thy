theory CodeExport
imports Test_Suite
begin 

export_code set
            nat (* TODO: how to automatically export constructors?*)
      	    FSM_ext
            r_distinguishable_state_pairs_with_separators_naive
            maximal_pairwise_r_distinguishable_state_sets_from_separators
            d_reachable_states_with_preambles
            maximal_repetition_sets_from_separators
            test_suite_naive
            M_ex_DR
            M_ex_H
            M_ex_9
  in Haskell module_name FSM file_prefix fsm


end
