theory ASC_Hoare
  imports ASC_Sufficiency "HOL-Hoare.Hoare_Logic" (*"HOL-Hoare.Arith2"*) (*"Abstract-Hoare-Logics/While/Hoare"*)
begin




lemma language_state_in_union : 
  shows "language_state_in M q T1 \<union> language_state_in M q T2 = language_state_in M q (T1 \<union> T2)"
  unfolding language_state_in.simps by blast


lemma performRefinedAdaptiveStateCounting: "VARS tsN cN rmN obs obsI iter
  {OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>}
  tsN := {};
  cN  := V;
  rmN := {};
  obs := \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) cN));
  obsI := \<Union> (image (\<lambda> io . append_io_B M1 io \<Omega>) (language_state_in M1 (initial M1) cN));
  iter := 1;
  WHILE (cN \<noteq> {} \<and> obsI \<subseteq> obs)
  INV {
    0 < iter
    \<and> tsN = TS M2 M1 \<Omega> V m (iter-1)
    \<and> cN = C M2 M1 \<Omega> V m iter
    \<and> rmN = RM M2 M1 \<Omega> V m (iter-1)
    \<and> obs = \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) (tsN \<union> cN)))
    \<and> obsI = \<Union> (image (\<lambda> io . append_io_B M1 io \<Omega>) (language_state_in M1 (initial M1) (tsN \<union> cN)))
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
                \<and> m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'' ))))};
    tsN := tsN \<union> cN;
    cN := append_set (cN - rmN) (inputs M2) - tsN;
    obs := obs \<union> \<Union> (image (\<lambda> io . append_io_B M2 io \<Omega>) (language_state_in M2 (initial M2) cN));
    obsI := obsI \<union> \<Union> (image (\<lambda> io . append_io_B M1 io \<Omega>) (language_state_in M1 (initial M1) cN))
  OD
  {
    M1 \<preceq> M2 \<longleftrightarrow> is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>    
  }"  

  apply vcg 
proof -
  assume precond : "OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>"
  have "{} = TS M2 M1 \<Omega> V m (1-1)"
       "V = C M2 M1 \<Omega> V m 1"
       "{} = RM M2 M1 \<Omega> V m (1-1)" 
        "(\<Union>io\<in>language_state_in M2 (initial M2) V. append_io_B M2 io \<Omega>) =
            (\<Union>io\<in>language_state_in M2 (initial M2) ({} \<union> V). append_io_B M2 io \<Omega>)"
        "(\<Union>io\<in>language_state_in M1 (initial M1) V. append_io_B M1 io \<Omega>) =
            (\<Union>io\<in>language_state_in M1 (initial M1) ({} \<union> V). append_io_B M1 io \<Omega>)"
    using precond by auto
  moreover have "OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega> "
    using precond by assumption
  ultimately show "0 < (1::nat) \<and> 
                   {} = TS M2 M1 \<Omega> V m (1 - 1) \<and>
                   V = C M2 M1 \<Omega> V m 1 \<and>
                   {} = RM M2 M1 \<Omega> V m (1 - 1) \<and>
                   (\<Union>io\<in>language_state_in M2 (initial M2) V. append_io_B M2 io \<Omega>) =
                   (\<Union>io\<in>language_state_in M2 (initial M2) ({} \<union> V). append_io_B M2 io \<Omega>) \<and>
                   (\<Union>io\<in>language_state_in M1 (initial M1) V. append_io_B M1 io \<Omega>) =
                   (\<Union>io\<in>language_state_in M1 (initial M1) ({} \<union> V). append_io_B M1 io \<Omega>) \<and>
                   OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>" by blast
next 
  fix tsN cN rmN obs obsI iter
  assume precond : "(0 < iter \<and>
        tsN = TS M2 M1 \<Omega> V m (iter - 1) \<and>
        cN = C M2 M1 \<Omega> V m iter \<and>
        rmN = RM M2 M1 \<Omega> V m (iter - 1) \<and>
        obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>) \<and>
        obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<and>
        OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>) \<and>
       cN \<noteq> {} \<and> obsI \<subseteq> obs"
  then have "0 < iter"
            "OFSM M1" 
            "OFSM M2"
            "fault_model M2 M1 m"
            "test_tools_R M2 M1 FAIL PM V \<Omega>"
            "cN \<noteq> {}"
            "obsI \<subseteq> obs"
            "tsN = TS M2 M1 \<Omega> V m (iter-1)"
            "cN = C M2 M1 \<Omega> V m iter"
            "rmN = RM M2 M1 \<Omega> V m (iter-1)"
            "obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)"
            "obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>)"
    by linarith+


  obtain k where "iter = Suc k" 
    using gr0_implies_Suc[OF \<open>0 < iter\<close>] by blast
  then have "cN = C M2 M1 \<Omega> V m (Suc k)"
            "tsN = TS M2 M1 \<Omega> V m k" 
    using \<open>cN = C M2 M1 \<Omega> V m iter\<close> \<open>tsN = TS M2 M1 \<Omega> V m (iter-1)\<close> by auto
  have "TS M2 M1 \<Omega> V m iter = TS M2 M1 \<Omega> V m (Suc k)"
           "C M2 M1 \<Omega> V m iter = C M2 M1 \<Omega> V m (Suc k)"
           "RM M2 M1 \<Omega> V m iter = RM M2 M1 \<Omega> V m (Suc k)"
    using \<open>iter = Suc k\<close> by presburger+
        
  
  have rmN_calc[simp] : "{xs' \<in> cN.
        \<not> io_reduction_on M1 {xs'} M2 \<or>
        (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
            \<exists>V''\<in>N io M1 V.
               \<exists>S1 vs xs.
                  io = vs @ xs \<and>
                  mcp (vs @ xs) V'' vs \<and>
                  S1 \<subseteq> nodes M2 \<and>
                  (\<forall>s1\<in>S1.
                      \<forall>s2\<in>S1.
                         s1 \<noteq> s2 \<longrightarrow>
                         (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                  m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')} =
       RM M2 M1 \<Omega> V m iter" 
  proof -


    have "{xs' \<in> cN.
          \<not> io_reduction_on M1 {xs'} M2 \<or>
          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
              \<exists>V''\<in>N io M1 V.
                 \<exists>S1 vs xs.
                    io = vs @ xs \<and>
                    mcp (vs @ xs) V'' vs \<and>
                    S1 \<subseteq> nodes M2 \<and>
                    (\<forall>s1\<in>S1.
                        \<forall>s2\<in>S1.
                           s1 \<noteq> s2 \<longrightarrow>
                           (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')} =
          {xs' \<in> C M2 M1 \<Omega> V m (Suc k).
          \<not> io_reduction_on M1 {xs'} M2 \<or>
          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
              \<exists>V''\<in>N io M1 V.
                 \<exists>S1 vs xs.
                    io = vs @ xs \<and>
                    mcp (vs @ xs) V'' vs \<and>
                    S1 \<subseteq> nodes M2 \<and>
                    (\<forall>s1\<in>S1.
                        \<forall>s2\<in>S1.
                           s1 \<noteq> s2 \<longrightarrow>
                           (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                    m < LB M2 M1 vs xs ((TS M2 M1 \<Omega> V m k) \<union> V) S1 \<Omega> V'')}"
      using \<open>cN = C M2 M1 \<Omega> V m (Suc k)\<close> \<open>tsN = TS M2 M1 \<Omega> V m k\<close> by blast
    
    moreover have "{xs' \<in> C M2 M1 \<Omega> V m (Suc k).
                    \<not> io_reduction_on M1 {xs'} M2 \<or>
                    (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                        \<exists>V''\<in>N io M1 V.
                           \<exists>S1 vs xs.
                              io = vs @ xs \<and>
                              mcp (vs @ xs) V'' vs \<and>
                              S1 \<subseteq> nodes M2 \<and>
                              (\<forall>s1\<in>S1.
                                  \<forall>s2\<in>S1.
                                     s1 \<noteq> s2 \<longrightarrow>
                                     (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                              m < LB M2 M1 vs xs ((TS M2 M1 \<Omega> V m k) \<union> V) S1 \<Omega> V'')} = 
                    RM M2 M1 \<Omega> V m (Suc k)"
      using RM.simps(2)[of M2 M1 \<Omega> V m k] by blast
    ultimately have "{xs' \<in> cN.
                      \<not> io_reduction_on M1 {xs'} M2 \<or>
                      (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                          \<exists>V''\<in>N io M1 V.
                             \<exists>S1 vs xs.
                                io = vs @ xs \<and>
                                mcp (vs @ xs) V'' vs \<and>
                                S1 \<subseteq> nodes M2 \<and>
                                (\<forall>s1\<in>S1.
                                    \<forall>s2\<in>S1.
                                       s1 \<noteq> s2 \<longrightarrow>
                                       (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')} =
                      RM M2 M1 \<Omega> V m (Suc k)"
      by presburger
    then show ?thesis
      using \<open>iter = Suc k\<close> by presburger
  qed
  moreover have "RM M2 M1 \<Omega> V m iter = RM M2 M1 \<Omega> V m (iter + 1 - 1)" by simp
  ultimately have rmN_calc' : "{xs' \<in> cN.
        \<not> io_reduction_on M1 {xs'} M2 \<or>
        (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
            \<exists>V''\<in>N io M1 V.
               \<exists>S1 vs xs.
                  io = vs @ xs \<and>
                  mcp (vs @ xs) V'' vs \<and>
                  S1 \<subseteq> nodes M2 \<and>
                  (\<forall>s1\<in>S1.
                      \<forall>s2\<in>S1.
                         s1 \<noteq> s2 \<longrightarrow>
                         (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                  m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')} =
       RM M2 M1 \<Omega> V m (iter + 1 - 1)" by presburger

  have "tsN \<union> cN = TS M2 M1 \<Omega> V m (Suc k)"
  proof (cases k)
    case 0
    then show ?thesis 
      using \<open>tsN = TS M2 M1 \<Omega> V m k\<close> \<open>cN = C M2 M1 \<Omega> V m (Suc k)\<close> by auto
  next
    case (Suc nat)
    then have "TS M2 M1 \<Omega> V m (Suc k) = TS M2 M1 \<Omega> V m k \<union> C M2 M1 \<Omega> V m (Suc k)"
      using TS.simps(3) by blast
    moreover have "tsN \<union> cN = TS M2 M1 \<Omega> V m k \<union> C M2 M1 \<Omega> V m (Suc k)"
      using \<open>tsN = TS M2 M1 \<Omega> V m k\<close> \<open>cN = C M2 M1 \<Omega> V m (Suc k)\<close> by auto
    ultimately show ?thesis 
      by auto
  qed
  then have tsN_calc : "tsN \<union> cN = TS M2 M1 \<Omega> V m iter"
    using \<open>iter = Suc k\<close> by presburger
 
  
  have cN_calc : "append_set
        (cN -
         {xs' \<in> cN.
          \<not> io_reduction_on M1 {xs'} M2 \<or>
          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
              \<exists>V''\<in>N io M1 V.
                 \<exists>S1 vs xs.
                    io = vs @ xs \<and>
                    mcp (vs @ xs) V'' vs \<and>
                    S1 \<subseteq> nodes M2 \<and>
                    (\<forall>s1\<in>S1.
                        \<forall>s2\<in>S1.
                           s1 \<noteq> s2 \<longrightarrow>
                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
        (inputs M2) -
       (tsN \<union> cN) =
       C M2 M1 \<Omega> V m (iter + 1)"
  proof -
    have "append_set
          (cN -
           {xs' \<in> cN.
            \<not> io_reduction_on M1 {xs'} M2 \<or>
            (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                \<exists>V''\<in>N io M1 V.
                   \<exists>S1 vs xs.
                      io = vs @ xs \<and>
                      mcp (vs @ xs) V'' vs \<and>
                      S1 \<subseteq> nodes M2 \<and>
                      (\<forall>s1\<in>S1.
                          \<forall>s2\<in>S1.
                             s1 \<noteq> s2 \<longrightarrow>
                             (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                 \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                      m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
          (inputs M2) -
         (tsN \<union> cN) = 
         append_set
          ((C M2 M1 \<Omega> V m iter) -
           (RM M2 M1 \<Omega> V m iter))
          (inputs M2) -
         (TS M2 M1 \<Omega> V m iter) "
      using \<open>cN = C M2 M1 \<Omega> V m iter\<close> \<open>tsN \<union> cN = TS M2 M1 \<Omega> V m iter\<close> rmN_calc by presburger
    moreover have "append_set
          ((C M2 M1 \<Omega> V m iter) -
           (RM M2 M1 \<Omega> V m iter))
          (inputs M2) -
         (TS M2 M1 \<Omega> V m iter) = C M2 M1 \<Omega> V m (iter + 1)" 
    proof -
      have "C M2 M1 \<Omega> V m (iter + 1) = C M2 M1 \<Omega> V m ((Suc k) + 1)"
        using \<open>iter = Suc k\<close> by presburger+
      moreover have "(Suc k) + 1 = Suc (Suc k)"
        by simp
      ultimately have "C M2 M1 \<Omega> V m (iter + 1) = C M2 M1 \<Omega> V m (Suc (Suc k))" 
        by presburger

      have "C M2 M1 \<Omega> V m (Suc (Suc k)) = append_set (C M2 M1 \<Omega> V m (Suc k) - RM M2 M1 \<Omega> V m (Suc k)) (inputs M2) - TS M2 M1 \<Omega> V m (Suc k)" 
        using C.simps(3)[of M2 M1 \<Omega> V m k] by linarith
      show ?thesis
        using Suc_eq_plus1 \<open>C M2 M1 \<Omega> V m (Suc (Suc k)) = append_set (C M2 M1 \<Omega> V m (Suc k) - RM M2 M1 \<Omega> V m (Suc k)) (inputs M2) - TS M2 M1 \<Omega> V m (Suc k)\<close> \<open>iter = Suc k\<close> by presburger
    qed  

    ultimately show ?thesis
      by presburger 
  qed
      
  have obs_calc : "obs \<union>
       (\<Union>io\<in>language_state_in M2 (initial M2)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M2 io \<Omega>) =
       (\<Union>io\<in>language_state_in M2 (initial M2)
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                       \<exists>V''\<in>N io M1 V.
                          \<exists>S1 vs xs.
                             io = vs @ xs \<and>
                             mcp (vs @ xs) V'' vs \<and>
                             S1 \<subseteq> nodes M2 \<and>
                             (\<forall>s1\<in>S1.
                                 \<forall>s2\<in>S1.
                                    s1 \<noteq> s2 \<longrightarrow>
                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                 (inputs M2) -
                (tsN \<union> cN))).
           append_io_B M2 io \<Omega>)"      
  proof - 
    have "obs \<union>
       (\<Union>io\<in>language_state_in M2 (initial M2)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M2 io \<Omega>) =
        (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>) \<union>
        (\<Union>io\<in>language_state_in M2 (initial M2)
                      (append_set
                        (cN -
                         {xs' \<in> cN.
                          \<not> io_reduction_on M1 {xs'} M2 \<or>
                          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                              \<exists>V''\<in>N io M1 V.
                                 \<exists>S1 vs xs.
                                    io = vs @ xs \<and>
                                    mcp (vs @ xs) V'' vs \<and>
                                    S1 \<subseteq> nodes M2 \<and>
                                    (\<forall>s1\<in>S1.
                                        \<forall>s2\<in>S1.
                                           s1 \<noteq> s2 \<longrightarrow>
                                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                        (inputs M2) -
                       (tsN \<union> cN)).
                   append_io_B M2 io \<Omega>)"
      using \<open>obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)\<close>
      by blast

    moreover have "(\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>) \<union>
        (\<Union>io\<in>language_state_in M2 (initial M2)
                      (append_set
                        (cN -
                         {xs' \<in> cN.
                          \<not> io_reduction_on M1 {xs'} M2 \<or>
                          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                              \<exists>V''\<in>N io M1 V.
                                 \<exists>S1 vs xs.
                                    io = vs @ xs \<and>
                                    mcp (vs @ xs) V'' vs \<and>
                                    S1 \<subseteq> nodes M2 \<and>
                                    (\<forall>s1\<in>S1.
                                        \<forall>s2\<in>S1.
                                           s1 \<noteq> s2 \<longrightarrow>
                                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                        (inputs M2) -
                       (tsN \<union> cN)).
                   append_io_B M2 io \<Omega>) = 
                (\<Union>io\<in>language_state_in M2 (initial M2)
                              (tsN \<union> cN \<union>
                               (append_set
                                 (cN -
                                  {xs' \<in> cN.
                                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                                       \<exists>V''\<in>N io M1 V.
                                          \<exists>S1 vs xs.
                                             io = vs @ xs \<and>
                                             mcp (vs @ xs) V'' vs \<and>
                                             S1 \<subseteq> nodes M2 \<and>
                                             (\<forall>s1\<in>S1.
                                                 \<forall>s2\<in>S1.
                                                    s1 \<noteq> s2 \<longrightarrow>
                                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                                 (inputs M2) -
                                (tsN \<union> cN))).
                           append_io_B M2 io \<Omega>)"
      using language_state_in_union[of M2 "initial M2" "tsN \<union> cN"] by blast
    
    ultimately show ?thesis by presburger
  qed


  have obsI_calc : "obsI \<union>
       (\<Union>io\<in>language_state_in M1 (initial M1)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M1 io \<Omega>) =
       (\<Union>io\<in>language_state_in M1 (initial M1)
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                       \<exists>V''\<in>N io M1 V.
                          \<exists>S1 vs xs.
                             io = vs @ xs \<and>
                             mcp (vs @ xs) V'' vs \<and>
                             S1 \<subseteq> nodes M2 \<and>
                             (\<forall>s1\<in>S1.
                                 \<forall>s2\<in>S1.
                                    s1 \<noteq> s2 \<longrightarrow>
                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                 (inputs M2) -
                (tsN \<union> cN))).
           append_io_B M1 io \<Omega>)"      
  proof - 
    have "obsI \<union>
       (\<Union>io\<in>language_state_in M1 (initial M1)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M1 io \<Omega>) =
        (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<union>
        (\<Union>io\<in>language_state_in M1 (initial M1)
                      (append_set
                        (cN -
                         {xs' \<in> cN.
                          \<not> io_reduction_on M1 {xs'} M2 \<or>
                          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                              \<exists>V''\<in>N io M1 V.
                                 \<exists>S1 vs xs.
                                    io = vs @ xs \<and>
                                    mcp (vs @ xs) V'' vs \<and>
                                    S1 \<subseteq> nodes M2 \<and>
                                    (\<forall>s1\<in>S1.
                                        \<forall>s2\<in>S1.
                                           s1 \<noteq> s2 \<longrightarrow>
                                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                        (inputs M2) -
                       (tsN \<union> cN)).
                   append_io_B M1 io \<Omega>)"
      using \<open>obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>)\<close>
      by blast

    moreover have "(\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<union>
        (\<Union>io\<in>language_state_in M1 (initial M1)
                      (append_set
                        (cN -
                         {xs' \<in> cN.
                          \<not> io_reduction_on M1 {xs'} M2 \<or>
                          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                              \<exists>V''\<in>N io M1 V.
                                 \<exists>S1 vs xs.
                                    io = vs @ xs \<and>
                                    mcp (vs @ xs) V'' vs \<and>
                                    S1 \<subseteq> nodes M2 \<and>
                                    (\<forall>s1\<in>S1.
                                        \<forall>s2\<in>S1.
                                           s1 \<noteq> s2 \<longrightarrow>
                                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                        (inputs M2) -
                       (tsN \<union> cN)).
                   append_io_B M1 io \<Omega>) = 
                (\<Union>io\<in>language_state_in M1 (initial M1)
                              (tsN \<union> cN \<union>
                               (append_set
                                 (cN -
                                  {xs' \<in> cN.
                                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                                       \<exists>V''\<in>N io M1 V.
                                          \<exists>S1 vs xs.
                                             io = vs @ xs \<and>
                                             mcp (vs @ xs) V'' vs \<and>
                                             S1 \<subseteq> nodes M2 \<and>
                                             (\<forall>s1\<in>S1.
                                                 \<forall>s2\<in>S1.
                                                    s1 \<noteq> s2 \<longrightarrow>
                                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                                 (inputs M2) -
                                (tsN \<union> cN))).
                           append_io_B M1 io \<Omega>)"
      using language_state_in_union[of M1 "initial M1" "tsN \<union> cN"] by blast
    
    ultimately show ?thesis by presburger
  qed



  have "0 < iter + 1"
    using \<open>0 < iter\<close> by simp
  have "tsN \<union> cN = TS M2 M1 \<Omega> V m (iter + 1 - 1)"
    using tsN_calc by simp


  (* putting the above results together *)
  

  from \<open>0 < iter + 1\<close>
       \<open>tsN \<union> cN = TS M2 M1 \<Omega> V m (iter + 1 - 1)\<close>
       cN_calc
       rmN_calc'
       obs_calc
       obsI_calc
       \<open>OFSM M1\<close>
       \<open>OFSM M2\<close>
       \<open>fault_model M2 M1 m\<close>
       \<open>test_tools_R M2 M1 FAIL PM V \<Omega>\<close>
  show "0 < iter + 1 \<and>
       tsN \<union> cN = TS M2 M1 \<Omega> V m (iter + 1 - 1) \<and>
       append_set
        (cN -
         {xs' \<in> cN.
          \<not> io_reduction_on M1 {xs'} M2 \<or>
          (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
              \<exists>V''\<in>N io M1 V.
                 \<exists>S1 vs xs.
                    io = vs @ xs \<and>
                    mcp (vs @ xs) V'' vs \<and>
                    S1 \<subseteq> nodes M2 \<and>
                    (\<forall>s1\<in>S1.
                        \<forall>s2\<in>S1.
                           s1 \<noteq> s2 \<longrightarrow>
                           (\<forall>io1\<in>RP M2 s1 vs xs V''.
                               \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                    m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
        (inputs M2) -
       (tsN \<union> cN) =
       C M2 M1 \<Omega> V m (iter + 1) \<and>
       {xs' \<in> cN.
        \<not> io_reduction_on M1 {xs'} M2 \<or>
        (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
            \<exists>V''\<in>N io M1 V.
               \<exists>S1 vs xs.
                  io = vs @ xs \<and>
                  mcp (vs @ xs) V'' vs \<and>
                  S1 \<subseteq> nodes M2 \<and>
                  (\<forall>s1\<in>S1.
                      \<forall>s2\<in>S1.
                         s1 \<noteq> s2 \<longrightarrow>
                         (\<forall>io1\<in>RP M2 s1 vs xs V''. \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                  m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')} =
       RM M2 M1 \<Omega> V m (iter + 1 - 1) \<and>
       obs \<union>
       (\<Union>io\<in>language_state_in M2 (initial M2)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M2 io \<Omega>) =
       (\<Union>io\<in>language_state_in M2 (initial M2)
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                       \<exists>V''\<in>N io M1 V.
                          \<exists>S1 vs xs.
                             io = vs @ xs \<and>
                             mcp (vs @ xs) V'' vs \<and>
                             S1 \<subseteq> nodes M2 \<and>
                             (\<forall>s1\<in>S1.
                                 \<forall>s2\<in>S1.
                                    s1 \<noteq> s2 \<longrightarrow>
                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                 (inputs M2) -
                (tsN \<union> cN))).
           append_io_B M2 io \<Omega>) \<and>
       obsI \<union>
       (\<Union>io\<in>language_state_in M1 (initial M1)
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> io_reduction_on M1 {xs'} M2 \<or>
                  (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                      \<exists>V''\<in>N io M1 V.
                         \<exists>S1 vs xs.
                            io = vs @ xs \<and>
                            mcp (vs @ xs) V'' vs \<and>
                            S1 \<subseteq> nodes M2 \<and>
                            (\<forall>s1\<in>S1.
                                \<forall>s2\<in>S1.
                                   s1 \<noteq> s2 \<longrightarrow>
                                   (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                       \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                            m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                (inputs M2) -
               (tsN \<union> cN)).
           append_io_B M1 io \<Omega>) =
       (\<Union>io\<in>language_state_in M1 (initial M1)
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> io_reduction_on M1 {xs'} M2 \<or>
                   (\<forall>io\<in>language_state_in M1 (initial M1) {xs'}.
                       \<exists>V''\<in>N io M1 V.
                          \<exists>S1 vs xs.
                             io = vs @ xs \<and>
                             mcp (vs @ xs) V'' vs \<and>
                             S1 \<subseteq> nodes M2 \<and>
                             (\<forall>s1\<in>S1.
                                 \<forall>s2\<in>S1.
                                    s1 \<noteq> s2 \<longrightarrow>
                                    (\<forall>io1\<in>RP M2 s1 vs xs V''.
                                        \<forall>io2\<in>RP M2 s2 vs xs V''. B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega>)) \<and>
                             m < LB M2 M1 vs xs (tsN \<union> V) S1 \<Omega> V'')})
                 (inputs M2) -
                (tsN \<union> cN))).
           append_io_B M1 io \<Omega>) \<and>
       OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>"
    by linarith
next
  fix tsN cN rmN obs obsI iter
  assume precond : "(0 < iter \<and>
        tsN = TS M2 M1 \<Omega> V m (iter - 1) \<and>
        cN = C M2 M1 \<Omega> V m iter \<and>
        rmN = RM M2 M1 \<Omega> V m (iter - 1) \<and>
        obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>) \<and>
        obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<and>
        OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>) \<and>
       \<not> (cN \<noteq> {} \<and> obsI \<subseteq> obs)"
  then have "0 < iter"
            "OFSM M1" 
            "OFSM M2"
            "fault_model M2 M1 m"
            "test_tools_R M2 M1 FAIL PM V \<Omega>"
            "cN = {} \<or> \<not> obsI \<subseteq> obs"
            "tsN = TS M2 M1 \<Omega> V m (iter-1)"
            "cN = C M2 M1 \<Omega> V m iter"
            "rmN = RM M2 M1 \<Omega> V m (iter-1)"
            "obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)"
            "obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>)"
    by linarith+

  


  show "M1 \<preceq> M2 = is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega> "
  proof (cases "cN = {}")
    case True
    then have "C M2 M1 \<Omega> V m iter = {}"
      using \<open>cN = C M2 M1 \<Omega> V m iter\<close> by auto

    have "is_det_state_cover M2 V" 
      using \<open>test_tools_R M2 M1 FAIL PM V \<Omega>\<close> by auto
    then have "[] \<in> V" 
      using det_state_cover_initial[of M2 V] by simp 
    then have "V \<noteq> {}"
      by blast
    have "Suc 0 < iter" 
    proof (rule ccontr)
      assume "\<not> Suc 0 < iter"
      then have "iter = Suc 0" 
        using \<open>0 < iter\<close> by auto
      then have "C M2 M1 \<Omega> V m (Suc 0) = {}"
        using \<open>C M2 M1 \<Omega> V m iter = {}\<close> by auto
      moreover have "C M2 M1 \<Omega> V m (Suc 0) = V" 
        by auto
      ultimately show"False" 
        using \<open>V \<noteq> {}\<close> by blast
    qed

    obtain k where "iter = Suc k" 
      using gr0_implies_Suc[OF \<open>0 < iter\<close>] by blast
    then have "Suc 0 < Suc k"
      using \<open>Suc 0 < iter\<close> by auto
    then have "0 < k" 
      by simp
    then obtain k' where "k = Suc k'" 
      using gr0_implies_Suc by blast
    have "iter = Suc (Suc k')"
      using \<open>iter = Suc k\<close> \<open>k = Suc k'\<close> by simp

    have "TS M2 M1 \<Omega> V m (Suc (Suc k')) = TS M2 M1 \<Omega> V m (Suc k') \<union> C M2 M1 \<Omega> V m (Suc (Suc k'))" 
      using TS.simps(3)[of M2 M1 \<Omega> V m k'] by blast
    then have "TS M2 M1 \<Omega> V m iter = TS M2 M1 \<Omega> V m (Suc k')"
      using True \<open>cN = C M2 M1 \<Omega> V m iter\<close> \<open>iter = Suc (Suc k')\<close> by blast
    moreover have "Suc k' = iter - 1"
      using \<open>iter = Suc (Suc k')\<close> by presburger
    ultimately have "TS M2 M1 \<Omega> V m iter = TS M2 M1 \<Omega> V m (iter - 1)"
      by auto 
    then have "tsN = TS M2 M1 \<Omega> V m iter"
      using \<open>tsN = TS M2 M1 \<Omega> V m (iter-1)\<close> by simp
    
    then  have "TS M2 M1 \<Omega> V m iter = TS M2 M1 \<Omega> V m (iter - 1)"
      using \<open>tsN = TS M2 M1 \<Omega> V m (iter - 1)\<close> by auto
    then have "final_iteration M2 M1 \<Omega> V m (iter-1)" 
      using \<open>0 < iter\<close> by auto
    
    have "M1 \<preceq> M2 = is_reduction_on_sets M1 M2 tsN \<Omega>" 
      using asc_main_theorem[OF \<open>OFSM M1\<close> \<open>OFSM M2\<close> \<open>fault_model M2 M1 m\<close> \<open>test_tools_R M2 M1 FAIL PM V \<Omega>\<close> \<open>final_iteration M2 M1 \<Omega> V m (iter-1)\<close>]
      using \<open>tsN = TS M2 M1 \<Omega> V m (iter - 1)\<close>
      by blast
    moreover have "tsN \<union> cN = tsN"
      using \<open>cN = {}\<close> by blast
    ultimately show ?thesis 
      by presburger
      
  next
    case False

    then have "\<not> obsI \<subseteq> obs"
      using \<open>cN = {} \<or> \<not> obsI \<subseteq> obs\<close> by auto

    then have "\<not> (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)"
      using \<open>obs = (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)\<close>
      using \<open>obsI = (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>)\<close>
      by blast

    have "\<not> is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>" 
    proof  
      assume "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
      have "(\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)"
        using is_reduction_on_sets_via_language_state_in[OF \<open>is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>\<close>]
        by assumption
      then show "False"  
        using \<open>\<not> (\<Union>io\<in>language_state_in M1 (initial M1) (tsN \<union> cN). append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>language_state_in M2 (initial M2) (tsN \<union> cN). append_io_B M2 io \<Omega>)\<close>
        by blast
    qed
    then have f1 : "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega> = False" 
      by simp
  
    have "\<not> M1 \<preceq> M2"
    proof 
      assume "M1 \<preceq> M2"
      have "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
        using asc_soundness[OF \<open>M1 \<preceq> M2\<close> \<open>OFSM M1\<close> \<open>OFSM M2\<close>] by blast
      then show "False"
        using \<open>\<not> is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>\<close> by blast
    qed
    then have f2 : "M1 \<preceq> M2 = False"
      by simp
    
    show ?thesis 
      using f2 f1 by simp

  qed
qed



end