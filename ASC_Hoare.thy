theory ASC_Hoare
  imports ASC_Sufficiency "HOL-Hoare.Hoare_Logic" 
begin




lemma language_state_in_union : 
  shows "language_state_in M q T1 \<union> language_state_in M q T2 = language_state_in M q (T1 \<union> T2)"
  unfolding language_state_in.simps by blast

lemma is_reduction_on_sets_from_obs :
  assumes "L\<^sub>i\<^sub>n M1 T \<subseteq> L\<^sub>i\<^sub>n M2 T" 
  and "(\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)" 
shows "is_reduction_on_sets M1 M2 T \<Omega>"
  unfolding is_reduction_on_sets.simps is_reduction_on.simps
proof 
  fix iseq assume "iseq \<in> T"
  have "L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq}"
    by (metis \<open>iseq \<in> T\<close> assms(1) bot.extremum insert_mono io_reduction_on_subset mk_disjoint_insert)
  moreover have "\<forall>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>"
  proof
    fix io assume "io \<in> L\<^sub>i\<^sub>n M1 {iseq}"
    then have "io \<in> L\<^sub>i\<^sub>n M2 {iseq}"
      using calculation by blast 
    show "append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega> "
    proof
      fix x assume "x \<in> append_io_B M1 io \<Omega>"

      have "io \<in> L\<^sub>i\<^sub>n M1 T"
        using \<open>io \<in> L\<^sub>i\<^sub>n M1 {iseq}\<close> \<open>iseq \<in> T\<close> by auto 
      moreover have "(io,x) \<in> {io} \<times> append_io_B M1 io \<Omega>"
        using \<open>x \<in> append_io_B M1 io \<Omega>\<close> by blast 
      ultimately have "(io,x) \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>)" 
        by blast

      then have "(io,x) \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)"
        using assms(2) by blast
      then have "(io,x) \<in> {io} \<times> append_io_B M2 io \<Omega>"
        by blast 
      then show "x \<in> append_io_B M2 io \<Omega>"
        by blast
    qed
  qed
  ultimately show "L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq} \<and>
       (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>)" by linarith
qed


lemma is_reduction_on_sets_to_obs :   
  assumes "is_reduction_on_sets M1 M2 T \<Omega>"
shows "L\<^sub>i\<^sub>n M1 T \<subseteq> L\<^sub>i\<^sub>n M2 T" 
  and "(\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)"
proof 
  fix x assume "x \<in> L\<^sub>i\<^sub>n M1 T"
  show "x \<in> L\<^sub>i\<^sub>n M2 T"
    using assms unfolding is_reduction_on_sets.simps is_reduction_on.simps
  proof -
    assume a1: "\<forall>iseq\<in>T. L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq} \<and> (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>)"
    have f2: "x \<in> UNION T (language_state_for_input M1 (initial M1))"
      by (metis (no_types) \<open>x \<in> L\<^sub>i\<^sub>n M1 T\<close> language_state_in_alt_def)
    obtain aas :: "'a list set \<Rightarrow> ('a list \<Rightarrow> ('a \<times> 'b) list set) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a list" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 \<in> x1 v3) = (aas x0 x1 x2 \<in> x0 \<and> x2 \<in> x1 (aas x0 x1 x2))"
      by moura
    then have "\<forall>ps f A. (ps \<notin> UNION A f \<or> aas A f ps \<in> A \<and> ps \<in> f (aas A f ps)) \<and> (ps \<in> UNION A f \<or> (\<forall>as. as \<notin> A \<or> ps \<notin> f as))"
      by blast
    then show ?thesis
      using f2 a1 by (metis (no_types) contra_subsetD language_state_for_input_alt_def language_state_in_alt_def)
  qed
next  
  show "(\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)"   
  proof 
    fix iox assume "iox \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>)"
    then obtain io x where "iox = (io,x)" 
      by blast

    have "io \<in> L\<^sub>i\<^sub>n M1 T"
      using \<open>iox = (io, x)\<close> \<open>iox \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>)\<close> by blast
    have "(io,x) \<in> {io} \<times> append_io_B M1 io \<Omega>"
      using \<open>iox = (io, x)\<close> \<open>iox \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 T. {io} \<times> append_io_B M1 io \<Omega>)\<close> by blast
    then have "x \<in> append_io_B M1 io \<Omega>" 
      by blast

    then have "x \<in> append_io_B M2 io \<Omega>"
      using assms unfolding is_reduction_on_sets.simps is_reduction_on.simps
      by (metis (no_types, lifting) UN_E \<open>io \<in> L\<^sub>i\<^sub>n M1 T\<close> language_state_for_input_alt_def language_state_in_alt_def subsetCE) 
    then have "(io,x) \<in> {io} \<times> append_io_B M2 io \<Omega>"
      by blast
    then have "(io,x) \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)"
      using \<open>io \<in> L\<^sub>i\<^sub>n M1 T\<close> by auto 
    then show "iox \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 T. {io} \<times> append_io_B M2 io \<Omega>)"
      using \<open>iox = (io, x)\<close> by auto
  qed
qed
  


        


lemma performRefinedAdaptiveStateCounting: "VARS tsN cN rmN obs obsI obs\<^sub>\<Omega> obsI\<^sub>\<Omega> iter isReduction
  {OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>}
  tsN := {};
  cN  := V;
  rmN := {};
  obs := L\<^sub>i\<^sub>n M2 cN;
  obsI := L\<^sub>i\<^sub>n M1 cN;
  obs\<^sub>\<Omega> := \<Union> (image (\<lambda> io . {io} \<times> append_io_B M2 io \<Omega>) (L\<^sub>i\<^sub>n M2 cN));
  obsI\<^sub>\<Omega> := \<Union> (image (\<lambda> io . {io} \<times> append_io_B M1 io \<Omega>) (L\<^sub>i\<^sub>n M1 cN));
  iter := 1;
  WHILE (cN \<noteq> {} \<and> obsI \<subseteq> obs)
  INV {
    0 < iter
    \<and> tsN = TS M2 M1 \<Omega> V m (iter-1)
    \<and> cN = C M2 M1 \<Omega> V m iter
    \<and> rmN = RM M2 M1 \<Omega> V m (iter-1)
    \<and> obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN)
    \<and> obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN)
    \<and> obs\<^sub>\<Omega> = \<Union> (image (\<lambda> io . {io} \<times> append_io_B M2 io \<Omega>) (L\<^sub>i\<^sub>n M2 (tsN \<union> cN)))
    \<and> obsI\<^sub>\<Omega> = \<Union> (image (\<lambda> io . {io} \<times> append_io_B M1 io \<Omega>) (L\<^sub>i\<^sub>n M1 (tsN \<union> cN)))
    \<and> OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>
  }
  DO 
    iter := iter + 1;
    rmN := {xs' \<in> cN .
      (\<not> (L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'}))
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
    obs := obs \<union> L\<^sub>i\<^sub>n M2 cN;
    obsI := obsI \<union> L\<^sub>i\<^sub>n M1 cN;
    obs\<^sub>\<Omega> := obs\<^sub>\<Omega> \<union> \<Union> (image (\<lambda> io . {io} \<times> append_io_B M2 io \<Omega>) (L\<^sub>i\<^sub>n M2 cN));
    obsI\<^sub>\<Omega> := obsI\<^sub>\<Omega> \<union> \<Union> (image (\<lambda> io . {io} \<times> append_io_B M1 io \<Omega>) (L\<^sub>i\<^sub>n M1 cN))
  OD;
  isReduction := ((obsI \<subseteq> obs) \<and> (obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>))
  {
    isReduction = M1 \<preceq> M2   \<comment>\<open>variable isReduction is used only as a return value, it is true if and only if M1 is a reduction of M2\<close> 
  }"  
proof (vcg)
  assume precond : "OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>"
  have "{} = TS M2 M1 \<Omega> V m (1-1)"
       "V = C M2 M1 \<Omega> V m 1"
       "{} = RM M2 M1 \<Omega> V m (1-1)" 
       "L\<^sub>i\<^sub>n M2 V = L\<^sub>i\<^sub>n M2 ({} \<union> V)"
       "L\<^sub>i\<^sub>n M1 V = L\<^sub>i\<^sub>n M1 ({} \<union> V)"
        "(\<Union>io\<in>L\<^sub>i\<^sub>n M2 V. {io} \<times> append_io_B M2 io \<Omega>) = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 ({} \<union> V). {io} \<times> append_io_B M2 io \<Omega>)"
        "(\<Union>io\<in>L\<^sub>i\<^sub>n M1 V. {io} \<times> append_io_B M1 io \<Omega>) = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 ({} \<union> V). {io} \<times> append_io_B M1 io \<Omega>)"
    using precond by auto
  moreover have "OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega> "
    using precond by assumption
  ultimately show "0 < (1::nat) \<and>
                   {} = TS M2 M1 \<Omega> V m (1 - 1) \<and>
                   V = C M2 M1 \<Omega> V m 1 \<and>
                   {} = RM M2 M1 \<Omega> V m (1 - 1) \<and>
                   L\<^sub>i\<^sub>n M2 V = L\<^sub>i\<^sub>n M2 ({} \<union> V) \<and>
                   L\<^sub>i\<^sub>n M1 V = L\<^sub>i\<^sub>n M1 ({} \<union> V) \<and>
                   (\<Union>io\<in>L\<^sub>i\<^sub>n M2 V. {io} \<times> append_io_B M2 io \<Omega>) = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 ({} \<union> V). {io} \<times> append_io_B M2 io \<Omega>) \<and>
                   (\<Union>io\<in>L\<^sub>i\<^sub>n M1 V. {io} \<times> append_io_B M1 io \<Omega>) = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 ({} \<union> V). {io} \<times> append_io_B M1 io \<Omega>) \<and>
                   OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>" by linarith+
next 
  fix tsN cN rmN obs obsI obs\<^sub>\<Omega> obsI\<^sub>\<Omega> iter isReduction
  assume precond : "(0 < iter \<and>
                      tsN = TS M2 M1 \<Omega> V m (iter - 1) \<and>
                      cN = C M2 M1 \<Omega> V m iter \<and>
                      rmN = RM M2 M1 \<Omega> V m (iter - 1) \<and>
                      obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN) \<and>
                      obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN) \<and>
                      obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>) \<and>
                      obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>) \<and>
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
            "obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN)"
            "obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN)"
            "obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)"
            "obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>)"
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
       L\<^sub>i\<^sub>n M2
        (append_set
          (cN -
           {xs' \<in> cN.
            \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
            (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
         (tsN \<union> cN)) =
       L\<^sub>i\<^sub>n M2
        (tsN \<union> cN \<union>
         (append_set
           (cN -
            {xs' \<in> cN.
             \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
             (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
          (tsN \<union> cN)))"
  proof -
    have "\<And>A. L\<^sub>i\<^sub>n M2 (tsN \<union> cN \<union> A) = obs \<union> L\<^sub>i\<^sub>n M2 A"
      by (metis (no_types) language_state_in_union precond)
    then show ?thesis
      by blast
  qed


  have obsI_calc : "obsI \<union>
       L\<^sub>i\<^sub>n M1
        (append_set
          (cN -
           {xs' \<in> cN.
            \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
            (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
         (tsN \<union> cN)) =
       L\<^sub>i\<^sub>n M1
        (tsN \<union> cN \<union>
         (append_set
           (cN -
            {xs' \<in> cN.
             \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
             (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
          (tsN \<union> cN)))"
  proof -
    have "\<And>A. L\<^sub>i\<^sub>n M1 (tsN \<union> cN \<union> A) = obsI \<union> L\<^sub>i\<^sub>n M1 A"
      by (metis (no_types) language_state_in_union precond)
    then show ?thesis
      by blast
  qed

  have obs\<^sub>\<Omega>_calc : "obs\<^sub>\<Omega> \<union>
       (\<Union>io\<in>L\<^sub>i\<^sub>n M2
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                  (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M2 io \<Omega>) =
       (\<Union>io\<in>L\<^sub>i\<^sub>n M2
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                   (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M2 io \<Omega>)"
    using \<open>obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN)\<close> \<open>obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)\<close> obs_calc by blast

  have obsI\<^sub>\<Omega>_calc : "obsI\<^sub>\<Omega> \<union>
       (\<Union>io\<in>L\<^sub>i\<^sub>n M1
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                  (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M1 io \<Omega>) =
       (\<Union>io\<in>L\<^sub>i\<^sub>n M1
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                   (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M1 io \<Omega>)"
    using \<open>obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN)\<close> \<open>obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>)\<close> obsI_calc by blast












  



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
       obs\<^sub>\<Omega>_calc
       obsI\<^sub>\<Omega>_calc
       \<open>OFSM M1\<close>
       \<open>OFSM M2\<close>
       \<open>fault_model M2 M1 m\<close>
       \<open>test_tools_R M2 M1 FAIL PM V \<Omega>\<close>
  show "0 < iter + 1 \<and>
       tsN \<union> cN = TS M2 M1 \<Omega> V m (iter + 1 - 1) \<and>
       append_set
        (cN -
         {xs' \<in> cN.
          \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
          (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
        \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
        (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
       L\<^sub>i\<^sub>n M2
        (append_set
          (cN -
           {xs' \<in> cN.
            \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
            (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
         (tsN \<union> cN)) =
       L\<^sub>i\<^sub>n M2
        (tsN \<union> cN \<union>
         (append_set
           (cN -
            {xs' \<in> cN.
             \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
             (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
          (tsN \<union> cN))) \<and>
       obsI \<union>
       L\<^sub>i\<^sub>n M1
        (append_set
          (cN -
           {xs' \<in> cN.
            \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
            (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
         (tsN \<union> cN)) =
       L\<^sub>i\<^sub>n M1
        (tsN \<union> cN \<union>
         (append_set
           (cN -
            {xs' \<in> cN.
             \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
             (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
          (tsN \<union> cN))) \<and>
       obs\<^sub>\<Omega> \<union>
       (\<Union>io\<in>L\<^sub>i\<^sub>n M2
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                  (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M2 io \<Omega>) =
       (\<Union>io\<in>L\<^sub>i\<^sub>n M2
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                   (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M2 io \<Omega>) \<and>
       obsI\<^sub>\<Omega> \<union>
       (\<Union>io\<in>L\<^sub>i\<^sub>n M1
              (append_set
                (cN -
                 {xs' \<in> cN.
                  \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                  (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M1 io \<Omega>) =
       (\<Union>io\<in>L\<^sub>i\<^sub>n M1
              (tsN \<union> cN \<union>
               (append_set
                 (cN -
                  {xs' \<in> cN.
                   \<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'} \<or>
                   (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {xs'}.
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
           {io} \<times> append_io_B M1 io \<Omega>) \<and>
       OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>"
    by linarith
next
  fix tsN cN rmN obs obsI obs\<^sub>\<Omega> obsI\<^sub>\<Omega> iter isReduction
  assume precond : "(0 < iter \<and>
                    tsN = TS M2 M1 \<Omega> V m (iter - 1) \<and>
                    cN = C M2 M1 \<Omega> V m iter \<and>
                    rmN = RM M2 M1 \<Omega> V m (iter - 1) \<and>
                    obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN) \<and>
                    obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN) \<and>
                    obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>) \<and>
                    obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>) \<and>
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
            "obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN)"
            "obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN)"
            "obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)"
            "obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>)"
    by linarith+

  

  show "(obsI \<subseteq> obs \<and> obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>) = M1 \<preceq> M2"
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
    ultimately have "M1 \<preceq> M2 = is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
      by presburger

    have "obsI \<subseteq> obs \<equiv> L\<^sub>i\<^sub>n M1 (tsN \<union> cN) \<subseteq> L\<^sub>i\<^sub>n M2 (tsN \<union> cN)"
      by (simp add: \<open>obs = L\<^sub>i\<^sub>n M2 (tsN \<union> cN)\<close> \<open>obsI = L\<^sub>i\<^sub>n M1 (tsN \<union> cN)\<close>)

    have "obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega> \<equiv> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)"
      by (simp add: \<open>obsI\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>)\<close> \<open>obs\<^sub>\<Omega> = (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)\<close>)
    

    have "(obsI \<subseteq> obs \<and> obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>) = is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
    proof
      assume "obsI \<subseteq> obs \<and> obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>"
      show "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
        using is_reduction_on_sets_from_obs[of M1 "tsN \<union> cN" M2 \<Omega>]
        using \<open>obsI \<subseteq> obs \<and> obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>\<close> \<open>obsI \<subseteq> obs \<equiv> L\<^sub>i\<^sub>n M1 (tsN \<union> cN) \<subseteq> L\<^sub>i\<^sub>n M2 (tsN \<union> cN)\<close> \<open>obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega> \<equiv> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)\<close> by linarith
    next
      assume "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
      show "obsI \<subseteq> obs \<and> obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega>" 
        using is_reduction_on_sets_to_obs[of M1 M2 \<open>tsN \<union> cN\<close> \<Omega>]
        using \<open>is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>\<close> \<open>obsI \<subseteq> obs \<equiv> L\<^sub>i\<^sub>n M1 (tsN \<union> cN) \<subseteq> L\<^sub>i\<^sub>n M2 (tsN \<union> cN)\<close> \<open>obsI\<^sub>\<Omega> \<subseteq> obs\<^sub>\<Omega> \<equiv> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 (tsN \<union> cN). {io} \<times> append_io_B M1 io \<Omega>) \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 (tsN \<union> cN). {io} \<times> append_io_B M2 io \<Omega>)\<close> by blast 
    qed
    then show ?thesis 
      using \<open>M1 \<preceq> M2 = is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>\<close> by linarith
next
    case False

    then have "\<not> obsI \<subseteq> obs"
      using \<open>cN = {} \<or> \<not> obsI \<subseteq> obs\<close> by auto

    have "\<not> is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
      by (metis (no_types, lifting) False is_reduction_on_sets_to_obs(1) precond) 
  
    have "\<not> M1 \<preceq> M2"
    proof 
      assume "M1 \<preceq> M2"
      have "is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>"
        using asc_soundness[OF \<open>M1 \<preceq> M2\<close> \<open>OFSM M1\<close> \<open>OFSM M2\<close>] by blast
      then show "False"
        using \<open>\<not> is_reduction_on_sets M1 M2 (tsN \<union> cN) \<Omega>\<close> by blast
    qed
    
    then show ?thesis 
      by (simp add: \<open>\<not> obsI \<subseteq> obs\<close>)

  qed
qed






lemma OFSM_not_vacuous :
  shows "\<exists> (M::(nat,nat,nat)FSM) . OFSM M"
proof

  let ?succ'_none = "\<lambda> xys . {}"
  let ?succ' = "?succ'_none( ((0,0),0) := {1},
                           ((0,1),0) := {1}, 
                           ((0,2),1) := {1})"
  let ?succ = "\<lambda> xy s . ?succ' (xy,s)"
  let ?inputs = "{0}"
  let ?outputs = "{0,1,2}"
  
  let ?M = "\<lparr>succ = ?succ, inputs=?inputs, outputs=?outputs, initial=0\<rparr> :: (nat,nat,nat) FSM"

  have "\<And> xy s . (succ ?M xy s \<subseteq> {0,1})"
    by auto 
  have "0 \<in> nodes ?M" 
    by auto
  moreover have "snd ((0,0),1) \<in> succ ?M (fst ((0,0),1)) 0" 
    by auto
  ultimately have "1 \<in> nodes ?M" 
    using FSM.nodes.execute[of 0 ?M "((0,0),1)"] by simp

  have "\<And> p a . succ ?M (fst a) p \<subseteq> {0,1}" 
    by auto
  then have "\<And> p a . p \<in> nodes ?M \<Longrightarrow> snd a \<in> succ ?M (fst a) p \<Longrightarrow> snd a \<in> {0,1}"
    by blast
  then have "nodes ?M \<subseteq> {0,1}"
    by (metis FSM.nodes.simps insertCI select_convs(4) subsetI) 
  then have "nodes ?M = {0,1}"
    using \<open>0 \<in> nodes ?M\<close> \<open>1 \<in> nodes ?M\<close> by blast
  
  have "finite_FSM ?M"
    unfolding finite_FSM.simps
    using \<open>nodes ?M = {0,1}\<close> by auto
  
  moreover have "\<And> s1 x y . (x \<notin> inputs ?M \<or> y \<notin> outputs ?M) \<longrightarrow> succ ?M (x,y) s1 = {}"
  proof 
    fix s1 x y assume "x \<notin> inputs ?M \<or> y \<notin> outputs ?M"
    then have "((x,y),(s1::nat)) \<noteq> ((0,0),0)" "((x,y),s1) \<noteq> ((0,1),0)" "((x,y),s1) \<noteq> ((0,2),1)" 
      by auto
    then show "succ ?M (x,y) s1 = {}" 
      by auto
  qed

  ultimately have "well_formed ?M" 
    by auto
  

  moreover have "observable ?M" 
    by auto

  moreover have "completely_specified ?M" 
    unfolding completely_specified.simps 
  proof 
    fix s1 assume "s1 \<in> nodes ?M"
    then have "s1 = 0 \<or> s1 = 1"
      using \<open>nodes ?M = {0,1}\<close> by blast
    then show "\<forall> x \<in> inputs ?M . \<exists> y \<in> outputs ?M . \<exists> s2 . s2 \<in> (succ ?M) (x,y) s1"
    proof
      assume "s1 = 0"
      show "\<forall> x \<in> inputs ?M . \<exists> y \<in> outputs ?M . \<exists> s2 . s2 \<in> (succ ?M) (x,y) s1"
      proof 
        fix x assume "x \<in> inputs ?M"
        then have"x = 0" 
          by auto
        then have "1 \<in> outputs ?M" "1 \<in> succ ?M (x,0) s1" 
          using \<open>s1 = 0\<close> by auto
        then show "\<exists> y \<in> outputs ?M . \<exists> s2 . s2 \<in> (succ ?M) (x,y) s1"
          by (metis insertI1 select_convs(3))
      qed
    next
      assume "s1 = 1"
      show "\<forall> x \<in> inputs ?M . \<exists> y \<in> outputs ?M . \<exists> s2 . s2 \<in> (succ ?M) (x,y) s1"
      proof 
        fix x assume "x \<in> inputs ?M"
        then have"x = 0" 
          by auto
        then have "2 \<in> outputs ?M" "1 \<in> succ ?M (x,2) s1" 
          using \<open>s1 = 1\<close> by auto
        then show "\<exists> y \<in> outputs ?M . \<exists> s2 . s2 \<in> (succ ?M) (x,y) s1"
          by (metis select_convs(3))
      qed
    qed
  qed

    
  ultimately show "OFSM ?M" 
    by auto
qed
  
lemma fault_model_not_vacuous :
  shows "\<exists> M2 M1 m . fault_model M2 M1 m"
(* TODO: define M2 M1 as used in the counterexample for the original algorithm and use those *)



lemma precondition_not_vacuous :
  shows "\<exists> M1 M2 m FAIL PM V \<Omega> . OFSM M1 \<and> OFSM M2 \<and> fault_model M2 M1 m \<and> test_tools_R M2 M1 FAIL PM V \<Omega>"
proof 


end