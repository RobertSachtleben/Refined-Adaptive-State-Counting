theory ASC_Hoare
  imports ASC_Sufficiency "HOL-Hoare.Hoare_Logic" "HOL-Hoare.Arith2" (*"Abstract-Hoare-Logics/While/Hoare"*)
begin

(*

(* Theorem 7.3.2 *)
lemma asc_main_theorem :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_R M2 M1 FAIL PM V \<Omega>"
  and     "final_iteration M2 M1 \<Omega> V m i"
shows     "M1 \<preceq> M2 \<longleftrightarrow> is_reduction_on_sets M1 M2 (TS M2 M1 \<Omega> V m i) \<Omega>"

*)



lemma performRefinedAdaptiveStateCounting: "VARS tsN cN rmN obs obsI iter
  {OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>}
  tsN := {};
  cN  := {};
  rmN := {};
  obs := \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) tsN));
  obsI := \<Union> (image (\<lambda> io . append_io_B M1 io \<Omega>) (language_state_in M1 (initial M1) tsN));
  iter := 0;
  WHILE (csN \<noteq> {} \<and> obsI \<subseteq> obs)
  INV {
    tsN = TS M2 M1 \<Omega> V m iter
    \<and> cN = C M2 M1 \<Omega> V m iter
    \<and> rmN = RM M2 M1 \<Omega> V m iter
    \<and> obs = \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) tsN))
    \<and> obsI = \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M1 (initial M1) tsN))
    \<and> OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>
  }
  DO 
    iter := iter + 1;
    rmN := {xs' \<in> cN .
      (\<not> (language_state_in M1 (initial M1) {xs'} \<subseteq> language_state_in M2 (initial M2) {xs'}))
      \<or> (\<forall> io \<in> language_state_in M1 (initial M1) {xs'} .
          (\<exists> V'' \<in> N io M1 V .  
            (\<exists> S1 . 
              (\<exists> vs xs .
                io = (vs@xs)
                \<and> mcp (vs@xs) V'' vs
                \<and> S1 \<subseteq> nodes M2
                \<and> (\<forall> s1 \<in> S1 . \<forall> s2 \<in> S1 .
                  s1 \<noteq> s2 \<longrightarrow> 
                    (\<forall> io1 \<in> RP M2 s1 vs xs V'' .
                       \<forall> io2 \<in> RP M2 s2 vs xs V'' .
                         B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega> ))
                \<and> m < LB M2 M1 vs xs tsN S1 \<Omega> V'' ))))};
    cN := append_set (cN - rmN) (inputs M2) - tsN;
    tsN := tsN \<union> cN;
    obs := obs \<union> \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) cN));
    obsI := obsI \<union> \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M1 (initial M1) cN))
  OD
  {
    (tsN = TS M2 M1 \<Omega> V m iter \<or> \<not> obsI \<subseteq> obs)
    \<and> obs = \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) tsN))
    \<and> obsI = \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M1 (initial M1) tsN))    
  }"  
  apply vcg 
    apply clarify
    apply simp


   apply clarify
  apply simp

proof 
  show "\<And>tsN cN rmN obs obsI iter.
       OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega> \<Longrightarrow>
       {} = TS M2 M1 \<Omega> V m 0" by simp




end