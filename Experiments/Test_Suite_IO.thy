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
    \<union> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})
    \<union> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"





lemma test_suite_to_io_language :
  assumes "is_sufficient_for_reduction_testing T M m"
shows "(test_suite_to_io M T) \<subseteq> L M"
proof 
  fix io assume "io \<in> test_suite_to_io M T"

  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)



  then obtain RepSets where RepSets_def: "is_sufficient_for_reduction_testing_for_RepSets (Test_Suite prs tps rd_targets atcs) M m RepSets"
    using assms(1) unfolding is_sufficient_for_reduction_testing_def by blast
  then have "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m"
    unfolding is_sufficient_for_reduction_testing_def by blast


  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(2)[OF RepSets_def] by blast
  
  have t5: "\<And>q. q \<in> FSM.nodes M \<Longrightarrow> (\<exists>d\<in>set RepSets. q \<in> fst d)"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(4)[OF RepSets_def] by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(7)[OF RepSets_def] by assumption

  have t8: "\<And> d. d \<in> set RepSets \<Longrightarrow> snd d \<subseteq> fst d"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(5,6)[OF RepSets_def] 
    by blast

  


  from \<open>io \<in> test_suite_to_io M T\<close> consider
    (a) "io \<in> (\<Union> (q,P) \<in> prs . L P)" |
    (b) "io \<in> (\<Union>{(\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt))) | p pt . \<exists> q P . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q})" |
    (c) "io \<in> (\<Union>{(\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A) | p pt q A . \<exists> P q' t1 t2 . (q,P) \<in> prs \<and> path P (initial P) p \<and> target (initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q,pt) \<and> (A,t1,t2) \<in> atcs (target q pt,q') })"
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> test_suite_to_io.simps
    by blast

  then show "io \<in> L M" proof cases
    case a
    then obtain q P  where "(q, P) \<in> prs" and "io \<in> L P"
      by blast

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast

    show "io \<in> L M"
      using submachine_language[OF \<open>is_submachine P M\<close>] \<open>io \<in> L P\<close> by blast
  next
    case b
    then obtain p pt q P where "io \<in> (\<lambda> io' . p_io p @ io') ` (set (prefixes (p_io pt)))" and "(q,P) \<in> prs" and "path P (initial P) p" and "target (initial P) p = q" and "pt \<in> tps q"
      by blast

    then obtain io' where "io = p_io p @ io'" and "io' \<in> (set (prefixes (p_io pt)))"
      by blast

    then obtain io'' where "p_io pt = io' @ io''" and "io = p_io p @ io'"
      unfolding prefixes_set
    proof -
      assume a1: "io' \<in> {xs'. \<exists>xs''. xs' @ xs'' = p_io pt}"
      assume "\<And>io''. \<lbrakk>p_io pt = io' @ io''; io = p_io p @ io'\<rbrakk> \<Longrightarrow> thesis"
      then show ?thesis
        using a1 \<open>io = p_io p @ io'\<close> by moura
    qed 



    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> by force

    

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
    then have "initial P = initial M" by auto

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) p\<close>] unfolding \<open>initial P = initial M\<close> by assumption
    have "target (initial M) p = q"
      using \<open>target (initial P) p = q\<close> unfolding \<open>initial P = initial M\<close> by assumption

    obtain p2 d where "(pt @ p2, d) \<in> m_traversal_paths_with_witness M q RepSets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pt \<in> tps q\<close> by blast

    then have "path M q (pt @ p2)"
      using m_traversal_paths_with_witness_set[OF t5 t8 path_target_is_node[OF \<open>path M (initial M) p\<close>], of m]
      unfolding \<open>target (initial M) p = q\<close> by blast
    then have "path M (initial M) (p@pt)"
      using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> by auto
    then have "p_io p @ p_io pt \<in> L M"
      by (metis (mono_tags, lifting) language_intro map_append)
    
    then show "io \<in> L M"
      unfolding \<open>io = p_io p @ io'\<close> \<open>p_io pt = io' @ io''\<close> append.assoc[symmetric] using language_prefix[of "p_io p @ io'" io'' M "initial M"] by blast
  next
    case c
                                                                                                                      
    then obtain p pt q A P q' t1 t2 where "io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)"
                                    and   "(q,P) \<in> prs" 
                                    and   "path P (initial P) p"
                                    and   "target (initial P) p = q"
                                    and   "pt \<in> tps q"
                                    and   "q' \<in> rd_targets (q,pt)" 
                                    and   "(A,t1,t2) \<in> atcs (target q pt,q')"
      by blast

    obtain ioA where "io = p_io p @ p_io pt @ ioA"
               and   "ioA \<in> (atc_to_io_set (from_FSM M (target q pt)) A)"
      using \<open>io \<in> (\<lambda> io_atc . p_io p @ p_io pt @ io_atc) ` (atc_to_io_set (from_FSM M (target q pt)) A)\<close>
      by blast
    then have "ioA \<in> L (from_FSM M (target q pt))"
      unfolding atc_to_io_set.simps by blast


    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> by force
    

    have "is_submachine P M"
      using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
    then have "initial P = initial M" by auto

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) p\<close>] unfolding \<open>initial P = initial M\<close> by assumption
    have "target (initial M) p = q"
      using \<open>target (initial P) p = q\<close> unfolding \<open>initial P = initial M\<close> by assumption

    obtain p2 d where "(pt @ p2, d) \<in> m_traversal_paths_with_witness M q RepSets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pt \<in> tps q\<close> by blast

    then have "path M q (pt @ p2)"
      using m_traversal_paths_with_witness_set[OF t5 t8 path_target_is_node[OF \<open>path M (initial M) p\<close>], of m]
      unfolding \<open>target (initial M) p = q\<close> by blast
    then have "path M (initial M) (p@pt)"
      using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> by auto

    moreover have "(target q pt) = target (initial M) (p@pt)"
      using \<open>target (initial M) p = q\<close> by auto

    ultimately have "(target q pt) \<in> nodes M"
      using path_target_is_node by metis

    have "ioA \<in> LS M (target q pt)"
      using from_FSM_language[OF \<open>(target q pt) \<in> nodes M\<close>] \<open>ioA \<in> L (from_FSM M (target q pt))\<close> by blast
    then obtain pA where "path M (target q pt) pA" and "p_io pA = ioA"
      by auto

    then have "path M (initial M) (p @ pt @ pA)"
      using \<open>path M (initial M) (p@pt)\<close>  unfolding \<open>(target q pt) = target (initial M) (p@pt)\<close> by auto
    then have "p_io p @ p_io pt @ ioA \<in> L M"
      unfolding \<open>p_io pA = ioA\<close>[symmetric]
      using language_intro by fastforce
    then show "io \<in> L M"
      unfolding \<open>io = p_io p @ p_io pt @ ioA\<close> by assumption
  qed
qed

  
  





lemma minimal_io_seq_to_failure :
  assumes "\<not> (L M' \<subseteq> L M)"
  and     "inputs M' = inputs M"  
  and     "completely_specified M"
obtains io x y y' where "io@[(x,y)] \<in> L M" and "io@[(x,y')] \<notin>  L M" and "io@[(x,y')] \<in> L M'" 
proof -
  obtain ioF where "ioF \<in> L M'" and "ioF \<notin> L M"
    using assms(1) by blast
  

  let ?prefs = "{ioF' \<in> set (prefixes ioF) . ioF' \<in> L M' \<and> ioF' \<notin> L M}"
  have "finite ?prefs"
    by auto
  moreover have "?prefs \<noteq> {}"
    unfolding prefixes_set using \<open>ioF \<in> L M'\<close> \<open>ioF \<notin> L M\<close> by auto
  ultimately obtain ioF' where "ioF' \<in> ?prefs" and "\<And> ioF'' . ioF'' \<in> ?prefs \<Longrightarrow> length ioF' \<le> length ioF''"
    by (meson leI min_length_elem) 
  
  then have "ioF' \<in> L M'" and "ioF' \<notin> L M"
    by auto
  then have "ioF' \<noteq> []" 
    by auto
  then have "ioF' = (butlast ioF')@[last ioF']" and "length (butlast ioF') < length ioF'"
    by auto
  then have "butlast ioF' \<notin> ?prefs"
    using \<open>\<And> ioF'' . ioF'' \<in> ?prefs \<Longrightarrow> length ioF' \<le> length ioF''\<close> leD by blast 
  moreover have "butlast ioF' \<in> L M'"
    using \<open>ioF' \<in> L M'\<close> language_prefix[of "butlast ioF'" "[last ioF']" M' "initial M'"] unfolding \<open>ioF' = (butlast ioF')@[last ioF']\<close>[symmetric] by blast
  moreover have "butlast ioF' \<in> set (prefixes ioF)"
    using \<open>ioF' = (butlast ioF')@[last ioF']\<close> \<open>ioF' \<in> ?prefs\<close> prefixes_set
  proof -
    have "\<exists>ps. (butlast ioF' @ [last ioF']) @ ps = ioF"
      using \<open>ioF' = butlast ioF' @ [last ioF']\<close> \<open>ioF' \<in> {ioF' \<in> set (prefixes ioF). ioF' \<in> L M' \<and> ioF' \<notin> L M}\<close> prefixes_set by auto
    then show ?thesis
      using prefixes_set by fastforce
  qed
  ultimately have "butlast ioF' \<in> L M" 
    by blast
  
  have *: "(butlast ioF')@[(fst (last ioF'), snd (last ioF'))] \<in> L M'"
    using \<open>ioF' \<in> L M'\<close> \<open>ioF' = (butlast ioF')@[last ioF']\<close> by auto
  have **: "(butlast ioF')@[(fst (last ioF'), snd (last ioF'))] \<notin> L M"
    using \<open>ioF' \<notin> L M\<close> \<open>ioF' = (butlast ioF')@[last ioF']\<close> by auto
  
  obtain p where "path M (initial M) p" and "p_io p = butlast ioF'"
    using \<open>butlast ioF' \<in> L M\<close> by auto
  moreover obtain t where "t \<in> transitions M" and "t_source t = target (initial M) p" and "t_input t = fst (last ioF')"
  proof -
    have "fst (last ioF') \<in> inputs M'"
      using language_io(1)[OF *, of "fst (last ioF')" "snd (last ioF')"] by simp 
    then have "fst (last ioF') \<in> inputs M"
      using assms(2) by auto
    then show ?thesis
      using that \<open>completely_specified M\<close> path_target_is_node[OF \<open>path M (initial M) p\<close>] unfolding completely_specified.simps by blast
  qed
  ultimately have ***: "(butlast ioF')@[(fst (last ioF'), t_output t)] \<in> L M"
  proof -
    have "p_io (p @ [t]) \<in> L M"
      by (metis (no_types) \<open>path M (FSM.initial M) p\<close> \<open>t \<in> FSM.transitions M\<close> \<open>t_source t = target (FSM.initial M) p\<close> language_intro path_append single_transition_path)
    then show ?thesis
      by (simp add: \<open>p_io p = butlast ioF'\<close> \<open>t_input t = fst (last ioF')\<close>)
  qed

  show ?thesis using that[OF *** ** *] by assumption
qed




lemma language_append_path_ob :
  assumes "io@[(x,y)] \<in> L M"
  obtains p t where "path M (initial M) (p@[t])" and "p_io p = io" and "t_input t = x" and "t_output t = y"
proof -
  obtain p p2 where "path M (initial M) p" and "path M (target (initial M) p) p2"  and "p_io p = io" and "p_io p2 = [(x,y)]"
    using language_state_split[OF assms] by blast

  obtain t where "p2 = [t]" and "t_input t = x" and "t_output t = y"
    using \<open>p_io p2 = [(x,y)]\<close> by auto

  have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close> \<open>path M (target (initial M) p) p2\<close> unfolding \<open>p2 = [t]\<close> by auto
  then show ?thesis using that[OF _ \<open>p_io p = io\<close> \<open>t_input t = x\<close> \<open>t_output t = y\<close>]
    by simp 
qed



lemma observable_minimal_path_to_failure :
  assumes "\<not> (L M' \<subseteq> L M)"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"  
  and     "completely_specified M"
  and     "completely_specified M'"
obtains p p' t t' where "path M (initial M) (p@[t])" 
                  and   "path M' (initial M') (p'@[t'])"
                  and   "p_io p' = p_io p"
                  and   "t_input t' = t_input t"
                  and   "\<not>(\<exists> t'' . t'' \<in> transitions M \<and> t_source t'' = target (initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t')"
proof -
               
  obtain io x y y' where "io@[(x,y)] \<in> L M" and "io@[(x,y')] \<notin>  L M" and "io@[(x,y')] \<in> L M'" 
    using minimal_io_seq_to_failure[OF assms(1,4,5)] by blast

  obtain p t where "path M (initial M) (p@[t])" and "p_io p = io" and "t_input t = x" and "t_output t = y"
    using language_append_path_ob[OF \<open>io@[(x,y)] \<in> L M\<close>] by blast

  moreover obtain p' t' where "path M' (initial M') (p'@[t'])" and "p_io p' = io" and "t_input t' = x" and "t_output t' = y'"
    using language_append_path_ob[OF \<open>io@[(x,y')] \<in> L M'\<close>] by blast

  moreover have "\<not>(\<exists> t'' . t'' \<in> transitions M \<and> t_source t'' = target (initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t')"
  proof 
    assume "\<exists>t''. t'' \<in> FSM.transitions M \<and> t_source t'' = target (FSM.initial M) p \<and> t_input t'' = t_input t \<and> t_output t'' = t_output t'"
    then obtain t'' where "t'' \<in> FSM.transitions M" and "t_source t'' = target (FSM.initial M) p" and "t_input t'' = x" and "t_output t'' = y'"
      unfolding \<open>t_input t = x\<close> \<open>t_output t' = y'\<close> by blast

    then have "path M (initial M) (p@[t''])"
      using \<open>path M (initial M) (p@[t])\<close>
      by (meson path_append_elim path_append_transition)
    moreover have "p_io (p@[t'']) = io@[(x,y')]"
      using \<open>p_io p = io\<close> \<open>t_input t'' = x\<close> \<open>t_output t'' = y'\<close> by auto
    ultimately have "io@[(x,y')] \<in> L M"
      using language_state_containment
      by (metis (mono_tags, lifting)) 
    then show "False"
      using \<open>io@[(x,y')] \<notin> L M\<close> by blast
  qed

  ultimately show ?thesis using that[of p t p' t']
    by force
qed


(* TODO: move *)
lemma is_preamble_is_node : 
  assumes "is_preamble P M q"
  shows "q \<in> nodes M"
  using assms unfolding is_preamble_def
  by (meson nil path_nil_elim reachable_node_is_node submachine_path) 

lemma prefixes_set_ob :
  assumes "xs \<in> set (prefixes xss)"
  obtains xs' where "xss = xs@xs'"
  using assms unfolding prefixes_set
  by auto 


(* TODO: remove assumptions *)
lemma test_suite_to_io_pass :
  assumes "is_sufficient_for_reduction_testing T M m"
  and     "observable M" 
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
  and     "completely_specified M"
  and     "completely_specified M'"
  and     "size M' \<le> m"
shows "pass_io_set M' (test_suite_to_io M T) = passes_test_suite M T M'"
proof -
  obtain prs tps rd_targets atcs where "T = Test_Suite prs tps rd_targets atcs"
    by (meson test_suite.exhaust)



  then obtain RepSets where RepSets_def: "is_sufficient_for_reduction_testing_for_RepSets (Test_Suite prs tps rd_targets atcs) M m RepSets"
    using assms(1) unfolding is_sufficient_for_reduction_testing_def by blast
  then have "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m"
    unfolding is_sufficient_for_reduction_testing_def by blast
  then have test_suite_language_prop: "test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<subseteq> L M"
    using test_suite_to_io_language by blast


  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using is_sufficient_for_reduction_testing_for_RepSets_simps(1)[OF RepSets_def] by assumption
  (*have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}"*)
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(2)[OF RepSets_def] by blast
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(3)[OF RepSets_def] by assumption
  
  have t5: "\<And>q. q \<in> FSM.nodes M \<Longrightarrow> (\<exists>d\<in>set RepSets. q \<in> fst d)"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(4)[OF RepSets_def] by assumption

  have t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(7)[OF RepSets_def] by assumption

  have t7: "\<And> d. d \<in> set RepSets \<Longrightarrow> fst d \<subseteq> FSM.nodes M"
  and  t8: "\<And> d. d \<in> set RepSets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t8':  "\<And> d. d \<in> set RepSets \<Longrightarrow> snd d = fst d \<inter> fst ` prs"
  and  t9: "\<And> d q1 q2. d \<in> set RepSets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(5,6)[OF RepSets_def] 
    by blast+

  have t10: "\<And> q p d p1 p2 p3.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow>
              p = p1 @ p2 @ p3 \<Longrightarrow>
              p2 \<noteq> [] \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              target q (p1 @ p2) \<in> fst d \<Longrightarrow>
              target q p1 \<noteq> target q (p1 @ p2) \<Longrightarrow>
              p1 \<in> tps q \<and> p1 @ p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q, p1 @ p2) \<and> target q (p1 @ p2) \<in> rd_targets (q, p1)"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(8)[OF RepSets_def] by assumption

  have t11: "\<And> q p d p1 p2 q'.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow>
              p = p1 @ p2 \<Longrightarrow>
              q' \<in> fst ` prs \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              q' \<in> fst d \<Longrightarrow> 
              target q p1 \<noteq> q' \<Longrightarrow> 
              p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1)"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(9)[OF RepSets_def] by assumption
  
  have t12: "\<And> q p d q1 q2.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow>
              q1 \<noteq> q2 \<Longrightarrow>
              q1 \<in> snd d \<Longrightarrow> 
              q2 \<in> snd d \<Longrightarrow> 
              [] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2, []) \<and> q2 \<in> rd_targets (q1, [])"
    using is_sufficient_for_reduction_testing_for_RepSets_simps(10)[OF RepSets_def] by assumption


    

  have "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs)) \<Longrightarrow> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
  proof -
    assume "pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"

    then have pass_io_prop: "\<And> io x y y' . io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs) \<Longrightarrow> io @ [(x, y')] \<in> L M' \<Longrightarrow> io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
      unfolding pass_io_set_def by blast


    show "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
    proof (rule ccontr)
      assume "\<not> passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"


      (*
      then have "\<not> (L M' \<subseteq> L M)"
        using passes_test_suite_soundness[OF \<open>is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m\<close> assms(2,3,4,6)] by blast

      *)



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

        have "is_preamble P M q"
          using t2[OF \<open>(q, P) \<in> prs\<close>] by assumption
        

        have "io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps using \<open>(q, P) \<in> prs\<close> \<open>io @ [(x, y)] \<in> L P\<close> by force

        have "io @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          using pass_io_prop[OF \<open>io @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)\<close> \<open>io @ [(x, y')] \<in> L M'\<close>] by assumption

        then have "io @ [(x, y')] \<in> L M"
          using test_suite_language_prop by blast

        have "io @ [(x, y')] \<in> L P"
          using passes_test_suite_soundness_helper_1[OF \<open>is_preamble P M q\<close> \<open>observable M\<close> \<open>io @ [(x, y)] \<in> L P\<close> \<open>io @ [(x, y')] \<in> L M\<close>] by assumption
        then show "False"
          using \<open>io @ [(x, y')] \<notin> L P\<close> by blast

      next
        case b
        then obtain q P pP ioT pT x y y' where "(q, P) \<in> prs"
                                           and "path P (FSM.initial P) pP"
                                           and "target (FSM.initial P) pP = q"
                                           and "pT \<in> tps q"
                                           and "ioT @ [(x, y)] \<in> set (prefixes (p_io pT))"
                                           and "p_io pP @ ioT @ [(x, y')] \<in> L M'"
                                           and "\<not> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))"
          by blast

        have "\<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) pP \<and> target (FSM.initial P) pP = q \<and> pT \<in> tps q"
          using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pT \<in> tps q\<close> by blast
        moreover have "p_io pP @ ioT @ [(x, y)] \<in> (@) (p_io pP) ` set (prefixes (p_io pT))"
          using \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close> by auto
        ultimately have "p_io pP @ ioT @ [(x, y)] \<in> (\<Union>{(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q})"
          by blast
        then have "p_io pP @ ioT @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          unfolding test_suite_to_io.simps  
          by blast
        then have *: "(p_io pP @ ioT) @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          by auto

        have **: "(p_io pP @ ioT) @ [(x, y')] \<in> L M'"
          using \<open>p_io pP @ ioT @ [(x, y')] \<in> L M'\<close> by auto

        have "(p_io pP @ ioT) @ [(x, y')] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
          using pass_io_prop[OF * ** ] by assumption
        then have "(p_io pP @ ioT) @ [(x, y')] \<in> L M"
          using test_suite_language_prop by blast

        have "q \<in> nodes M"
          using is_preamble_is_node[OF t2[OF \<open>(q, P) \<in> prs\<close>]] by assumption

        have "q \<in> fst ` prs" 
          using \<open>(q, P) \<in> prs\<close> by force

        obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m"
          using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> by blast

        then have "path M q (pT @ pT')"
             and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pT @ pT'))) RepSets = Some d'"
             and  "\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m]
          by blast+

        obtain ioT' where "p_io pT = ioT @ [(x,y)] @ ioT'"
          using prefixes_set_ob[OF \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close>] unfolding prefixes_set append.assoc[symmetric] by blast

        let ?pt = "take (length (ioT @ [(x,y)])) pT"
        let ?p  = "butlast ?pt"
        let ?t  = "last ?pt"
         

        have "length ?pt > 0"
          using \<open>p_io pT = ioT @ [(x,y)] @ ioT'\<close> unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by auto
        then have "?pt = ?p @ [?t]"
          by auto
        moreover have "path M q ?pt"
          using \<open>path M q (pT @ pT')\<close>
          by (meson path_prefix path_prefix_take)
        ultimately have "path M q (?p@[?t])"
          by simp

        have "p_io ?p = ioT"
        proof -
          have "p_io ?pt = take (length (ioT @ [(x,y)])) (p_io pT)"
            by (simp add: take_map) 
          then have "p_io ?pt = ioT @ [(x,y)]"
            using \<open>p_io pT = ioT @ [(x,y)] @ ioT'\<close> by auto
          then show ?thesis
            by (simp add: map_butlast) 
        qed

        have "path M q ?p"
          using path_append_transition_elim[OF \<open>path M q (?p@[?t])\<close>] by blast
        
        have "is_submachine P M"
          using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
        then have "initial P = initial M" by auto
    
        have "path M (initial M) pP"
          using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] unfolding \<open>initial P = initial M\<close> by assumption
        moreover have "target (initial M) pP = q"
          using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption
        ultimately have "path M (initial M) (pP@?p)" using \<open>path M q ?p\<close> by auto
      

        have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) RepSets = None"
        proof -
          have *: "(pT @ pT') = ?p @ ([?t] @ (drop (length (ioT @ [(x,y)])) pT) @ pT')" 
            using \<open>?pt = ?p @ [?t]\<close>
            by (metis append_assoc append_take_drop_id) 
          have **: "([?t] @ (drop (length (ioT @ [(x,y)])) pT) @ pT') \<noteq> []"
            by simp
          show ?thesis using \<open>\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None\<close>[OF * **] by assumption
        qed


        (* obtain paths from the transition ending in y' to get a transition from ?p *)
        obtain p' t' where "path M (FSM.initial M) (p' @ [t'])" and "p_io p' = p_io pP @ ioT" and "t_input t' = x" and "t_output t' = y'"
          using language_append_path_ob[OF \<open>(p_io pP @ ioT) @ [(x, y')] \<in> L M\<close>] by blast
        then have "path M (FSM.initial M) p'" and "t_source t' = target (initial M) p'" and "t' \<in> transitions M"
          by auto

        
        have "p' = pP @ ?p"
          using observable_path_unique[OF \<open>observable M\<close> \<open>path M (FSM.initial M) p'\<close> \<open>path M (initial M) (pP@?p)\<close>] 
                \<open>p_io ?p = ioT\<close> 
          unfolding \<open>p_io p' = p_io pP @ ioT\<close>
          by simp 
        then have "t_source t' = target q ?p"
          unfolding \<open>t_source t' = target (initial M) p'\<close> using \<open>target (initial M) pP = q\<close>
          by auto  
        
        
        obtain pTt' dt' where "(?p @ [t'] @ pTt', dt') \<in> m_traversal_paths_with_witness M q RepSets m"
          using m_traversal_path_extension_exist_for_transition[OF \<open>completely_specified M\<close> \<open>q \<in> nodes M\<close> \<open>FSM.inputs M \<noteq> {}\<close> t5 t8 \<open>path M q ?p\<close> \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) RepSets = None\<close> \<open>t' \<in> transitions M\<close> \<open>t_source t' = target q ?p\<close>]
          by blast

        have "?p @ [t'] @ pTt' \<in> tps q"
          using t6[OF \<open>q \<in> fst ` prs\<close> ] \<open>(?p @ [t'] @ pTt', dt') \<in> m_traversal_paths_with_witness M q RepSets m\<close> by force
        moreover have "ioT @ [(x, y')] \<in> set (prefixes (p_io (?p @ [t'] @ pTt')))"
        proof -
          have "p_io (?p @ [t'] @ pTt') = ioT @ [(x,y')] @ p_io pTt'"
            using \<open>p_io ?p = ioT\<close> using \<open>t_input t' = x\<close> \<open>t_output t' = y'\<close> by auto  
          then show ?thesis unfolding prefixes_set by force
        qed

        ultimately show "False"
          using \<open>\<not> (\<exists>pT'. pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT')))\<close> by blast
      next
        case c

        then obtain q P pP pT q' A d1 d2 qT  where "(q, P) \<in> prs"
                                             and   "path P (FSM.initial P) pP"
                                             and   "target (FSM.initial P) pP = q"
                                             and   "pT \<in> tps q"
                                             and   "p_io pP @ p_io pT \<in> L M'"
                                             and   "q' \<in> rd_targets (q, pT)"
                                             and   "(A, d1, d2) \<in> atcs (target q pT, q')"
                                             and   "qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')"
                                             and   "\<not>pass_separator_ATC M' A qT d2"
          by blast

        
        
        


        have "is_submachine P M"
          using t2[OF \<open>(q, P) \<in> prs\<close>] unfolding is_preamble_def by blast
        then have "initial P = initial M" by auto
    
        have "path M (initial M) pP"
          using submachine_path[OF \<open>is_submachine P M\<close> \<open>path P (initial P) pP\<close>] unfolding \<open>initial P = initial M\<close> by assumption
        have "target (initial M) pP = q"
          using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption

        have "q \<in> nodes M"
          using is_preamble_is_node[OF t2[OF \<open>(q, P) \<in> prs\<close>]] by assumption

        have "q \<in> fst ` prs" 
          using \<open>(q, P) \<in> prs\<close> by force

        obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m"
          using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> by blast

        then have "path M q (pT @ pT')"
             and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pT @ pT'))) RepSets = Some d'"
             and  "\<And> p' p''. (pT @ pT') = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m]
          by blast+
        then have "path M q pT"
          by auto

        have "qT \<in> nodes M'"
          using \<open>qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')\<close> io_targets_nodes
          using subset_iff by fastforce 



        have "is_separator M (target q pT) q' A d1 d2"
          using  t3[OF \<open>(A, d1, d2) \<in> atcs (target q pT, q')\<close>] by blast

        have "\<not> pass_io_set (FSM.from_FSM M' qT) (atc_to_io_set (FSM.from_FSM M (target q pT)) A)"
          using \<open>\<not>pass_separator_ATC M' A qT d2\<close>
                pass_separator_pass_io_set_iff[OF \<open>is_separator M (target q pT) q' A d1 d2\<close> \<open>observable M\<close> \<open>observable M'\<close> path_target_is_node[OF \<open>path M q pT\<close>] \<open>qT \<in> nodes M'\<close> \<open>inputs M' = inputs M\<close> \<open>completely_specified M\<close>]
          by simp


        have "pass_io_set (FSM.from_FSM M' qT) (atc_to_io_set (FSM.from_FSM M (target q pT)) A)"
        proof -
          have "\<And> io x y y' . io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A \<Longrightarrow>
                               io @ [(x, y')] \<in> L (FSM.from_FSM M' qT) \<Longrightarrow> 
                                io @ [(x, y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
          proof -
            fix io x y y' assume "io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
                          and    "io @ [(x, y')] \<in> L (FSM.from_FSM M' qT)"


            (* subsets of test_suite_to_io *)
            define tmp where tmp_def : "tmp = (\<Union> {(\<lambda>io_atc. p_io p @ p_io pt @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pt)) A |p pt q A. \<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q \<and> q' \<in> rd_targets (q, pt) \<and> (A, t1, t2) \<in> atcs (target q pt, q')})"
            define tmp2 where tmp2_def : "tmp2 = \<Union> {(@) (p_io p) ` set (prefixes (p_io pt)) |p pt. \<exists>q P. (q, P) \<in> prs \<and> path P (FSM.initial P) p \<and> target (FSM.initial P) p = q \<and> pt \<in> tps q}"
            have "\<exists>P q' t1 t2. (q, P) \<in> prs \<and> path P (FSM.initial P) pP \<and> target (FSM.initial P) pP = q \<and> pT \<in> tps q \<and> q' \<in> rd_targets (q, pT) \<and> (A, t1, t2) \<in> atcs (target q pT, q')"
              using \<open>(q, P) \<in> prs\<close> \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> \<open>pT \<in> tps q\<close> \<open>q' \<in> rd_targets (q, pT)\<close> \<open>(A, d1, d2) \<in> atcs (target q pT, q')\<close> by blast
            then have "(\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A \<subseteq> tmp"
              unfolding tmp_def by blast
            then have "(\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A \<subseteq> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              unfolding test_suite_to_io.simps tmp_def[symmetric] tmp2_def[symmetric] by blast
            moreover have "(p_io pP @ p_io pT @ (io @ [(x, y)])) \<in> (\<lambda>io_atc. p_io pP @ p_io pT @ io_atc) ` atc_to_io_set (FSM.from_FSM M (target q pT)) A"
              using \<open>io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A\<close> by auto
            ultimately have "(p_io pP @ p_io pT @ (io @ [(x, y)])) \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              by blast
            then have *: "(p_io pP @ p_io pT @ io) @ [(x, y)] \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              by simp


            have "io @ [(x, y')] \<in> LS M' qT"
              using \<open>io @ [(x, y')] \<in> L (FSM.from_FSM M' qT)\<close> \<open>qT \<in> nodes M'\<close>
              by (metis from_FSM_language) 
            have **: "(p_io pP @ p_io pT @ io) @ [(x, y')] \<in> L M'" 
              using io_targets_language_append[OF \<open>qT \<in> io_targets M' (p_io pP @ p_io pT) (FSM.initial M')\<close> \<open>io @ [(x, y')] \<in> LS M' qT\<close>] by simp
            
            
            have "(p_io pP @ p_io pT) @ (io @ [(x, y')]) \<in> test_suite_to_io M (Test_Suite prs tps rd_targets atcs)"
              using pass_io_prop[OF * ** ] by simp
            then have "(p_io pP @ p_io pT) @ (io @ [(x, y')]) \<in> L M"
              using test_suite_language_prop by blast

            moreover have "target q pT \<in> io_targets M (p_io pP @ p_io pT) (initial M)"
            proof -
              have "target (initial M) (pP@pT) = target q pT"
                unfolding \<open>target (initial M) pP = q\<close>[symmetric] by auto
              moreover have "path M (initial M) (pP@pT)"
                using \<open>path M (initial M) pP\<close> \<open>path M q pT\<close> unfolding \<open>target (initial M) pP = q\<close>[symmetric] by auto
              moreover have "p_io (pP@pT) = (p_io pP @ p_io pT)" 
                by auto
              ultimately show ?thesis
                unfolding io_targets.simps
                by (metis (mono_tags, lifting) mem_Collect_eq) 
            qed

            ultimately have "io @ [(x, y')] \<in> LS M (target q pT)"
              using observable_io_targets_language[OF _ \<open>observable M\<close>, of "(p_io pP @ p_io pT)" "(io @ [(x, y')])" "initial M" "target q pT"] by blast


            
            then have "io @ [(x, y')] \<in> L (FSM.from_FSM M (target q pT))"
              unfolding from_FSM_language[OF path_target_is_node[OF \<open>path M q pT\<close>]] by assumption

            moreover have "io @ [(x, y')] \<in> L A"
              by (metis Int_iff \<open>io @ [(x, y')] \<in> LS M (target q pT)\<close> \<open>io @ [(x, y)] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A\<close> \<open>is_separator M (target q pT) q' A d1 d2\<close> atc_to_io_set.simps is_separator_simps(9))
              
            ultimately show "io @ [(x, y')] \<in> atc_to_io_set (FSM.from_FSM M (target q pT)) A"
              unfolding atc_to_io_set.simps by blast
          qed
              
          then show ?thesis unfolding pass_io_set_def by blast
        qed

        then show "False"
          using pass_separator_from_pass_io_set[OF \<open>is_separator M (target q pT) q' A d1 d2\<close> _ \<open>observable M\<close> \<open>observable M'\<close> path_target_is_node[OF \<open>path M q pT\<close>] \<open>qT \<in> nodes M'\<close> \<open>inputs M' = inputs M\<close> \<open>completely_specified M\<close>]
                \<open>\<not>pass_separator_ATC M' A qT d2\<close>
          by simp
      qed
    qed
  qed

  moreover have "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M' \<Longrightarrow> pass_io_set M' (test_suite_to_io M (Test_Suite prs tps rd_targets atcs))"
    sorry

  ultimately show ?thesis 
    unfolding \<open>T = Test_Suite prs tps rd_targets atcs\<close> by blast
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