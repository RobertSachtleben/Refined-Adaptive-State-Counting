theory Test_Suite_IO
imports Test_Suite
begin





lemma preamble_maximal_io_paths :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "path P (initial P) p"
  and     "target (initial P) p = q"
shows "\<nexists>io' . io' \<noteq> [] \<and> p_io p @ io' \<in> L P" 
proof -
  have "deadlock_state P q"  
  and  "is_submachine P M"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using \<open>observable M\<close> \<open>is_submachine P M\<close>
    using submachine_observable by blast 

  show "\<nexists>io' . io' \<noteq> [] \<and> p_io p @ io' \<in> L P"
  proof
    assume "\<exists>io'. io' \<noteq> [] \<and> p_io p @ io' \<in> L P"
    then obtain io' where "io' \<noteq> []" and "p_io p @ io' \<in> L P"
      by blast

    obtain p1 p2 where "path P (FSM.initial P) p1" and "path P (target (FSM.initial P) p1) p2" and "p_io p1 = p_io p" and "p_io p2 = io'"
      using language_state_split[OF \<open>p_io p @ io' \<in> L P\<close>] by blast

    have "p1 = p"
      using observable_path_unique[OF \<open>observable P\<close> \<open>path P (FSM.initial P) p1\<close> \<open>path P (FSM.initial P) p\<close> \<open>p_io p1 = p_io p\<close>] by assumption

    have "io' \<in> LS P q"
      using \<open>path P (target (FSM.initial P) p1) p2\<close> \<open>p_io p2 = io'\<close>
      unfolding \<open>p1 = p\<close> assms(4) by auto
    then show "False"
      using \<open>io' \<noteq> []\<close> \<open>deadlock_state P q\<close> unfolding deadlock_state_alt_def by blast
  qed
qed



lemma preamble_maximal_io_paths_rev :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "io \<in> L P"
  and     "\<nexists>io' . io' \<noteq> [] \<and> io @ io' \<in> L P"
obtains p where "path P (initial P) p"
          and   "p_io p = io"
          and   "target (initial P) p = q"
proof -
  
  have "acyclic P"
  and  "deadlock_state P q"  
  and  "is_submachine P M"
  and  "\<And> q' . q'\<in>reachable_nodes P \<Longrightarrow> (q = q' \<or> \<not> deadlock_state P q')"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using \<open>observable M\<close> \<open>is_submachine P M\<close>
    using submachine_observable by blast 

  obtain p where "path P (initial P) p" and "p_io p = io"
    using \<open>io \<in> L P\<close> by auto

  moreover have "target (initial P) p = q"
  proof (rule ccontr)
    assume "target (FSM.initial P) p \<noteq> q"
    then have "\<not> deadlock_state P (target (FSM.initial P) p)"
      using \<open>\<And> q' . q'\<in>reachable_nodes P \<Longrightarrow> (q = q' \<or> \<not> deadlock_state P q')\<close>[OF reachable_nodes_intro[OF \<open>path P (initial P) p\<close>]] by simp
    then obtain t where "t \<in> transitions P" and "t_source t = target (initial P) p"
      by auto
    then have "path P (initial P) (p @ [t])"
      using path_append_transition[OF \<open>path P (initial P) p\<close>] by auto
    then have "p_io (p@[t]) \<in> L P"
      unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq)
    then have "io @ [(t_input t, t_output t)] \<in> L P"
      using \<open>p_io p = io\<close> by auto
    then show "False"
      using assms(4) by auto
  qed

  ultimately show ?thesis using that by blast
qed



(*
datatype ('a,'b,'c,'d) test_suite = 
  Test_Suite "('a \<times> ('a,'b,'c) preamble) set" 
             "'a \<Rightarrow> ('a,'b,'c) traversal_Path set" 
             "('a \<times> ('a,'b,'c) traversal_Path) \<Rightarrow> 'a set" 
             "('a \<times> 'a) \<Rightarrow> (('d,'b,'c) atc \<times> 'd \<times> 'd) set"
*)


fun test_suite_to_io :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) =
    (\<Union> (q,P) \<in> prs . L P)
    \<union> {p_io p @ p_io pt | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q}
    \<union> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (maximal_contained_lists (atc_to_io_set (from_FSM M (target q pt)) A)) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (q,q') })"


lemma test_suite_to_io_pass :
  "pass_io_set M' (test_suite_to_io M T) = passes_test_suite M T M'"
proof -
  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)
    

  have "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs)) \<Longrightarrow> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
  proof -
    assume "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"

    then have pass_io_prop: "\<And> io x y y' . io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<Longrightarrow> io @ [(x, y')] \<in> L M' \<Longrightarrow> io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
      unfolding pass_io_set_def by blast


    show "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
    proof (rule ccontr)
      assume "\<not> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"

      then consider (a) "\<not> (\<forall>q P io x y y'. (q, P) \<in> prs \<longrightarrow> io @ [(x, y)] \<in> L P \<longrightarrow> io @ [(x, y')] \<in> L M' \<longrightarrow> io @ [(x, y')] \<in> L P)" |
                    (b) "\<not> ((\<forall>q P pP ioT pT x y y'.
                              (q, P) \<in> prs \<longrightarrow>
                              path P (FSM.initial P) pP \<longrightarrow>
                              target (FSM.initial P) pP = q \<longrightarrow>
                              pT \<in> tps q \<longrightarrow>
                              ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<longrightarrow>
                              p_io pP @ ioT @ [(x, y')] \<in> L M' \<longrightarrow> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))))" |
                    (c) "\<not> ((\<forall>q P pP pT.
                              (q, P) \<in> prs \<longrightarrow>
                              path P (FSM.initial P) pP \<longrightarrow>
                              target (FSM.initial P) pP = q \<longrightarrow>
                              pT \<in> tps q \<longrightarrow>
                              p_io pP @ p_io pT \<in> L M' \<longrightarrow>
                              (\<forall>q' A d1 d2 qT.
                                  q' \<in> rd_targets (q, pT) \<longrightarrow>
                                  (A, d1, d2) \<in> atcs (target q pT, q') \<longrightarrow> qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M') \<longrightarrow> pass_separator_ATC M' A qT d2)))"  
        unfolding passes_test_suite.simps by blast
      then show False proof cases
        case a
        then obtain q P io x y y' where "(q, P) \<in> prs" and "io @ [(x, y)] \<in> L P" and "io @ [(x, y')] \<in> L M'" and "io @ [(x, y')] \<notin> L P"
          by blast

        have "io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps using \<open>(q, P) \<in> prs\<close> \<open>io @ [(x, y)] \<in> L P\<close> by force

        (* TODO: requires some uniqueness between Ps ... *)

        show "False"
          using pass_io_prop[OF \<open>io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> \<open>io @ [(x, y')] \<in> L M'\<close>] 
        
end (*

then show ?thesis sorry
next
  case b
  then show ?thesis sorry
next
  case c
  then show ?thesis sorry
qed
    


end (*
fun test_suite_to_io_code :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io (Test_Suite prs tps rd_targets atcs) = 
  (let
    preamble_ios = (\<lambda> (q,P) . maximal_contained_lists (LS_acyclic P (initial P))) ` prs;
    
  in
    {})"
  



end (*
fun test_suite_to_io :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('b \<times> 'c) list set" where
  "test_suite_to_io (Test_Suite prs tps rd_targets atcs) = 
   (\<Union> (q,P) \<in> prs . maximal_contained_lists (LS_acyclic P (initial P)))  
"
  

end