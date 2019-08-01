theory CodeExport
imports R_Distinguishability
begin 

export_code path 
            nodes 
            acyclic in Haskell module_name FSM file_prefix fsm

end