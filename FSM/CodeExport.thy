theory CodeExport
imports R_Distinguishability Helper_Algorithms
begin 

export_code set
	    FSM_ext
            r_distinguishable_state_pairs_with_separators_naive
            maximal_pairwise_r_distinguishable_state_sets_from_separators
            d_reachable_states_with_preambles
            maximal_repetition_sets_from_separators
            M_ex_DR
  in Haskell module_name FSM file_prefix fsm


end
