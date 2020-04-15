theory Test_Suite
imports Helper_Algorithms Adaptive_Test_Case Traversal_Set
begin

section \<open>Test Suites\<close>

subsection \<open>Preliminary Definitions\<close>


type_synonym ('a,'b,'c) preamble = "('a,'b,'c) fsm"
type_synonym ('a,'b,'c) traversal_Path = "('a \<times> 'b \<times> 'c \<times> 'a) list"
type_synonym ('a,'b,'c) atc = "('a,'b,'c) fsm"
type_synonym ('a,'b,'c) test_path = "('a \<times> ('a,'b,'c) traversal_Path \<times> 'a)"




(* A test suite contains of
    - a set of d-reachable states with their associated preambles
    - a map from d_reachable states to their associated m-traversal paths 
    - a map from d-reachable states and associated m-traversal paths to the set of states to r-distinguish the targets of those paths from
    - a map from pairs of r-distinguishable states to a separator
*)
datatype ('a,'b,'c,'d) test_suite = Test_Suite "('a \<times> ('a,'b,'c) preamble) set" "'a \<Rightarrow> ('a,'b,'c) traversal_Path set" "('a \<times> ('a,'b,'c) traversal_Path) \<Rightarrow> 'a set" "('a \<times> 'a) \<Rightarrow> (('d,'b,'c) atc \<times> 'd \<times> 'd) set"




(* assumes the usage of m_traversal_paths_with_witness and thus of a universal (i.e. applied in all cases) ordering of the rep-sets *)
(* to simplify the soundness proof, this formalisation also requires tps to contain nothing but the m-traversal paths;
   this could be lifted by requiring that for every additional path the suite retains additional paths such that all "non-deadlock"
   (w.r.t. the set of all (tps q) paths) nodes are output complete for the inputs applied *)  
(* TODO: generalise if necessary (and possible with acceptable effort) *)
fun is_sufficient_for_reduction_testing :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> bool" where
  "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m = 
    ( (initial M,initial_preamble M) \<in> prs 
    \<and> (\<forall> q P . (q,P) \<in> prs \<longrightarrow> (is_preamble P M q) \<and> (tps q) \<noteq> {})
    \<and> (\<forall> q1 q2 A d1 d2 . (A,d1,d2) \<in> atcs (q1,q2) \<longrightarrow> (A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2)
    \<and> (\<exists> RepSets .  
        ((\<forall> q . q \<in> nodes M \<longrightarrow> (\<exists>d \<in> set RepSets. q \<in> fst d))
        \<and> (\<forall> d . d \<in> set RepSets \<longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})))
        \<and> (\<forall> q . q \<in> image fst prs \<longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q) 
        \<and> (\<forall> q p d . q \<in> image fst prs \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q RepSets m \<longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst prs \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))))))
    \<and> (\<forall> q1 q2 . q1 \<in> image fst prs \<longrightarrow> q2 \<in> image fst prs \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {} \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[])))
    
  )"

(*\<and> (\<forall> q p . q \<in> image fst prs \<longrightarrow> p \<in> tps q \<longrightarrow> path M q p) *) \<comment> \<open>obsolete due to stronger (tps q = {...}) requirement\<close>


(*
lemma test_suite_path :
  assumes "(q,P) \<in> prs"
  and     "path P q pp"
  and     "target (initial P) pp = q"
  and     "tp \<in> tps q"
  and     "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m"
shows "path M (initial M) (pp@tp)"
proof -
  have "(is_preamble P M q)"
    using assms(1,5) by auto
  then have "path M (initial M) pp"
    using assms(2) 
    unfolding is_preamble_def
    by (metis deadlock_state.elims(2) fsm_initial path.simps) 
  moreover have "target (initial M) pp = q"
    using \<open>(is_preamble P M q)\<close> assms(3) unfolding is_preamble_def by auto
  moreover have "path M q tp"
  proof -
    have "q \<in> image fst prs" using assms(1)
      using image_iff by fastforce 
    then show ?thesis
      using assms(4,5) unfolding is_sufficient_for_reduction_testing.simps by blas
  qed
  ultimately show ?thesis by auto
qed
*)
    

  


subsection \<open>Pass Relation for Test Suites and Reduction Testing\<close>

fun passes_test_suite :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M' = (
    \<comment> \<open>Reduction on preambles: as the preambles contain all responses of M to their chosen inputs, M' must not exhibit any other response\<close>
    (\<forall> q P io x y y' . (q,P) \<in> prs \<longrightarrow> io@[(x,y)] \<in> L P \<longrightarrow> io@[(x,y')] \<in> L M' \<longrightarrow> io@[(x,y')] \<in> L P) 
    \<comment> \<open>Reduction on traversal-paths applied after preambles (i.e., completed paths in preambles) - note that tps q is not necessarily prefix-complete\<close>
    \<and> (\<forall> q P pP ioT pT x y y' . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT'))))
    \<comment> \<open>Passing ATCs: if M' contains an IO-sequence that in the test suite leads through a preamble and an m-traversal path and the target of the latter is to be r-distinguished from some other state, then M' passes the corresponding ATC\<close>
    \<and> (\<forall> q P pP pT . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<longrightarrow> (\<forall> q' A d1 d2 qT . q' \<in> rd_targets (q,pT) \<longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<longrightarrow> pass_separator_ATC M' A qT d2))
    )"                                                                                                                                                                                                                                                                                                   





lemma observable_preamble_paths :
  assumes "is_preamble P M q'"
  and     "observable M"
  and     "path M q p"  
  and     "p_io p \<in> LS P q"
  and     "q \<in> reachable_nodes P"
shows "path P q p"
using assms(3,4,5) proof (induction p arbitrary: q rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons t p)

  have   "is_submachine P M"
  and *: "\<And> q' x t t' . q'\<in>reachable_nodes P \<Longrightarrow> x\<in>FSM.inputs M \<Longrightarrow>
            t\<in>FSM.transitions P \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in>FSM.transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> FSM.transitions P"
    using assms(1) unfolding is_preamble_def by blast+

  have "observable P"
    using submachine_observable[OF \<open>is_submachine P M\<close> \<open>observable M\<close>] by blast

  obtain t' where "t'\<in>FSM.transitions P" and "t_source t' = q" and "t_input t' = t_input t"
    using \<open>p_io (t # p) \<in> LS P q\<close> by auto

  have "t_source t = q" and "t \<in> transitions M" and "t_input t \<in> inputs M"
    using \<open>path M q (t # p)\<close> by auto

  have "t \<in> transitions P"
    using *[OF \<open>q \<in> reachable_nodes P\<close> \<open>t_input t \<in> inputs M\<close> \<open>t'\<in>FSM.transitions P\<close> \<open>t_source t' = q\<close> \<open>t_input t' = t_input t\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close>]
    by auto

  have "path M (t_target t) p"
    using \<open>path M q (t # p)\<close> by auto
  moreover have "p_io p \<in> LS P (t_target t)"
  proof -
    have f1: "t_input t = fst (t_input t, t_output t)"
      by (metis fst_conv)
    have f2: "t_output t = snd (t_input t, t_output t)"
      by auto
    have f3: "(t_input t, t_output t) # p_io p \<in> LS P (t_source t)"
      using Cons.prems(2) \<open>t_source t = q\<close> by fastforce
    have "L (FSM.from_FSM P (t_target t)) = LS P (t_target t)"
      by (meson \<open>t \<in> FSM.transitions P\<close> from_FSM_language fsm_transition_target)
    then show ?thesis
      using f3 f2 f1 \<open>observable P\<close> \<open>t \<in> FSM.transitions P\<close> observable_language_next by blast
  qed   
  moreover have "t_target t \<in> reachable_nodes P"
    using \<open>t \<in> transitions P\<close> \<open>t_source t = q\<close> \<open>q \<in> reachable_nodes P\<close>
    by (meson reachable_nodes_next) 
  ultimately have "path P (t_target t) p"
    using Cons.IH by blast
  then show ?case
    using \<open>t \<in> transitions P\<close> \<open>t_source t = q\<close> by auto
qed


  

lemma passes_test_suite_soundness_helper_1 :
  assumes "is_preamble P M q"
  and     "observable M"
  and     "io@[(x,y)] \<in> L P"
  and     "io@[(x,y')] \<in> L M"
shows     "io@[(x,y')] \<in> L P"
proof -
  have   "is_submachine P M"
  and *: "\<And> q' x t t' . q'\<in>reachable_nodes P \<Longrightarrow> x\<in>FSM.inputs M \<Longrightarrow>
            t\<in>FSM.transitions P \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in>FSM.transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> FSM.transitions P"
    using assms(1)  unfolding is_preamble_def by blast+

  have "initial P = initial M"
    unfolding submachine_simps[OF \<open>is_submachine P M\<close>]
    by simp
  
  obtain p where "path M (initial M) p" and "p_io p = io @ [(x,y')]"
    using assms(4) unfolding submachine_simps[OF \<open>is_submachine P M\<close>] by auto
  
  obtain p' t where "p = p'@[t]"
    using \<open>p_io p = io @ [(x,y')]\<close> by (induction p rule: rev_induct; auto)

  have "path M (initial M) p'" and "t \<in> transitions M" and "t_source t = target (initial M) p'"
    using \<open>path M (initial M) p\<close> path_append_transition_elim
    unfolding \<open>p = p'@[t]\<close> by force+

  have "p_io p' = io" and "t_input t = x" and "t_output t = y'"
    using \<open>p_io p = io @ [(x,y')]\<close> unfolding \<open>p = p'@[t]\<close> by force+
     

  
  have "p_io p' \<in> LS P (FSM.initial M)"
    using assms(3) unfolding \<open>p_io p' = io\<close> \<open>initial P = initial M\<close>
    by (meson language_prefix) 

  have "FSM.initial M \<in> reachable_nodes P"
    unfolding submachine_simps(1)[OF \<open>is_submachine P M\<close>, symmetric]
    using reachable_nodes_initial by blast
  

  obtain pp where "path P (initial P) pp" and "p_io pp = io @ [(x,y)]"
    using assms(3) by auto
  then obtain pp' t' where "pp = pp'@[t']"
  proof -
    assume a1: "\<And>pp' t'. pp = pp' @ [t'] \<Longrightarrow> thesis"
    have "pp \<noteq> []"
      using \<open>p_io pp = io @ [(x, y)]\<close> by auto
    then show ?thesis
      using a1 by (metis (no_types) rev_exhaust)
  qed 

  have "path P (initial P) pp'" and "t' \<in> transitions P" and "t_source t' = target (initial P) pp'"
    using \<open>path P (initial P) pp\<close> path_append_transition_elim
    unfolding \<open>pp = pp'@[t']\<close> by force+
  have "p_io pp' = io" and "t_input t' = x"
    using \<open>p_io pp = io @ [(x,y)]\<close> unfolding \<open>pp = pp'@[t']\<close> by force+

  have "path M (initial M) pp'"
    using \<open>path P (initial P) pp'\<close> submachine_path_initial[OF \<open>is_submachine P M\<close>] by blast
  
  have "pp' = p'"
    using observable_path_unique[OF assms(2) \<open>path M (initial M) pp'\<close> \<open>path M (initial M) p'\<close> ]
    unfolding \<open>p_io pp' = io\<close> \<open>p_io p' = io\<close>
    by blast
  then have "t_source t' = target (initial M) p'"
    using \<open>t_source t' = target (initial P) pp'\<close> unfolding \<open>initial P = initial M\<close> by blast


  have "path P (FSM.initial M) p'"
    using observable_preamble_paths[OF assms(1,2) \<open>path M (initial M) p'\<close> \<open>p_io p' \<in> LS P (FSM.initial M)\<close> \<open>FSM.initial M \<in> reachable_nodes P\<close>]
    by assumption
  then have "target (initial M) p' \<in> reachable_nodes P"
    using reachable_nodes_intro unfolding \<open>initial P = initial M\<close>[symmetric] by blast
  moreover have "x \<in> inputs M"
    using \<open>t \<in> transitions M\<close> \<open>t_input t = x\<close> fsm_transition_input by blast


  have "t \<in> transitions P"
    using *[OF \<open>target (initial M) p' \<in> reachable_nodes P\<close> \<open>x \<in> inputs M\<close> \<open>t' \<in> transitions P\<close> \<open>t_source t' = target (initial M) p'\<close> \<open>t_input t' = x\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = target (FSM.initial M) p'\<close> \<open>t_input t = x\<close>]
    by assumption

  then have "path P (initial P) (p'@[t])"
    using \<open>path P (initial P) pp'\<close> \<open>t_source t = target (initial M) p'\<close>
    unfolding \<open>pp' = p'\<close> \<open>initial P = initial M\<close> 
    using path_append_transition by simp
  then show ?thesis 
    unfolding \<open>p = p'@[t]\<close>[symmetric] LS.simps
    using \<open>p_io p = io@[(x,y')]\<close>
    by force
qed



















lemma path_prefix_take :
  assumes "path M q p"
  shows "path M q (take i p)"
proof -
  have "p = (take i p)@(drop i p)" by auto
  then have "path M q ((take i p)@(drop i p))" using assms by auto
  then show ?thesis
    by blast 
qed






lemma passes_test_suite_soundness :
  assumes "observable M"
  and     "completely_specified M"
  and     "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m"
  and     "L M' \<subseteq> L M"
shows     "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
proof -
  have t1: "(initial M, initial_preamble M) \<in> prs" 
    using assms(3) unfolding is_sufficient_for_reduction_testing.simps by blast
  have t2: "\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}"
    using assms(3) unfolding is_sufficient_for_reduction_testing.simps by force
  have t3: "\<And> q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<Longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2"
    using assms(3) unfolding is_sufficient_for_reduction_testing.simps by force 
  have t4: "\<And> q1 q2 . q1 \<in> fst ` prs \<Longrightarrow> q2 \<in> fst ` prs \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {} \<Longrightarrow> [] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2, []) \<and> q2 \<in> rd_targets (q1, [])"
    using assms(3) unfolding is_sufficient_for_reduction_testing.simps by auto 
  



  obtain RepSets where
       t5: "\<And>q. q \<in> FSM.nodes M \<Longrightarrow> (\<exists>d\<in>set RepSets. q \<in> fst d)"
   and "\<And> d. d \<in> set RepSets \<Longrightarrow> fst d \<subseteq> FSM.nodes M \<and> snd d \<subseteq> fst d \<and> (\<forall>q1 q2. q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1, q2) \<noteq> {})"
   and t6: "\<And> q. q \<in> fst ` prs \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q"
   and rs_paths': "\<And> q p d.
          q \<in> fst ` prs \<Longrightarrow>
          (p, d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow>
          (\<forall>p1 p2 p3.
              p = p1 @ p2 @ p3 \<longrightarrow>
              p2 \<noteq> [] \<longrightarrow>
              target q p1 \<in> fst d \<longrightarrow>
              target q (p1 @ p2) \<in> fst d \<longrightarrow>
              target q p1 \<noteq> target q (p1 @ p2) \<longrightarrow>
              p1 \<in> tps q \<and> p1 @ p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q, p1 @ p2) \<and> target q (p1 @ p2) \<in> rd_targets (q, p1)) \<and>
          (\<forall>p1 p2 q'.
              p = p1 @ p2 \<longrightarrow>
              q' \<in> fst ` prs \<longrightarrow>
              target q p1 \<in> fst d \<longrightarrow>
              q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1))"
    using assms(3) unfolding is_sufficient_for_reduction_testing.simps by force

  have t7: "\<And> d. d \<in> set RepSets \<Longrightarrow> fst d \<subseteq> FSM.nodes M"
  and  t8: "\<And> d. d \<in> set RepSets \<Longrightarrow> snd d \<subseteq> fst d"
  and  t9: "\<And> d q1 q2. d \<in> set RepSets \<Longrightarrow> q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1, q2) \<noteq> {}"
    using \<open>\<And> d. d \<in> set RepSets \<Longrightarrow> fst d \<subseteq> FSM.nodes M \<and> snd d \<subseteq> fst d \<and> (\<forall>q1 q2. q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1, q2) \<noteq> {})\<close>
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
    using rs_paths' by blast

  have t11: "\<And> q p d p1 p2 q'.
              q \<in> fst ` prs \<Longrightarrow>
              (p, d) \<in> m_traversal_paths_with_witness M q RepSets m \<Longrightarrow>
              p = p1 @ p2 \<Longrightarrow>
              q' \<in> fst ` prs \<Longrightarrow>
              target q p1 \<in> fst d \<Longrightarrow>
              q' \<in> fst d \<Longrightarrow> 
              target q p1 \<noteq> q' \<Longrightarrow> 
              p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q', []) \<and> q' \<in> rd_targets (q, p1)"
    using rs_paths' by blast
  
    






  have "\<And> q P io x y y' . (q,P) \<in> prs \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  proof -
    fix q P io x y y' assume "(q,P) \<in> prs" and "io@[(x,y)] \<in> L P" and "io@[(x,y')] \<in> L M'"

    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast

    have "io@[(x,y')] \<in> L M"
      using \<open>io@[(x,y')] \<in> L M'\<close> assms(4) by blast

    show "io@[(x,y')] \<in> L P"
      using passes_test_suite_soundness_helper_1[OF \<open>is_preamble P M q\<close> assms(1) \<open>io@[(x,y)] \<in> L P\<close> \<open>io@[(x,y')] \<in> L M\<close>]
      by assumption
  qed
  then have p1: "(\<forall> q P io x y y' . (q,P) \<in> prs \<longrightarrow> io@[(x,y)] \<in> L P \<longrightarrow> io@[(x,y')] \<in> L M' \<longrightarrow> io@[(x,y')] \<in> L P)"
    by blast



  have "\<And> q P pP ioT pT x x' y y' . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> (p_io pP)@ioT@[(x',y')] \<in> L M' \<Longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x', y')] \<in> set (prefixes (p_io pT')))"
  proof -
    fix q P pP ioT pT x x' y y' 
    assume "(q,P) \<in> prs"  
       and "path P (initial P) pP" 
       and "target (initial P) pP = q" 
       and "pT \<in> tps q" 
       and "ioT @ [(x, y)] \<in> set (prefixes (p_io pT))" 
       and "(p_io pP)@ioT@[(x',y')] \<in> L M'"

    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast
    then have "q \<in> nodes M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_node submachine_path) 

    have "(p_io pP)@ioT@[(x',y')] \<in> L M"
      using \<open>(p_io pP)@ioT@[(x',y')] \<in> L M'\<close> assms(4) by blast
    have "inputs M \<noteq> {}"
      using language_io(1)[OF \<open>(p_io pP)@ioT@[(x',y')] \<in> L M\<close>, of x' y']
      by auto 


    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close>
      using image_iff by fastforce 


    obtain ioT' where "p_io pT = (ioT @ [(x, y)]) @ ioT'"
      using \<open>ioT @ [(x, y)] \<in> set (prefixes (p_io pT))\<close>
      unfolding prefixes_set 
      by moura
    then have "length pT > length ioT"
      using length_map[of "(\<lambda> t . (t_input t, t_output t))" pT] by auto

    
    obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close>
      by blast

    let ?p = "pT @ pT'"

    have "path M q ?p"
    and  "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)) RepSets = Some d'"
    and  "(\<forall>p' p''. ?p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None)"
      using \<open>(pT @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m\<close>
            m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m] 
      by blast+

    


    let ?pIO = "take (length ioT) pT"
    have "?pIO = take (length ioT) ?p" 
      using \<open>length pT > length ioT\<close> by auto
    then have "?p = ?pIO@(drop (length ioT) ?p)"
      by auto
    have "(drop (length ioT) ?p) \<noteq> []" 
      using \<open>length pT > length ioT\<close> by auto

    have "p_io ?pIO = ioT" 
    proof -
      have "p_io ?pIO = take (length ioT) (p_io pT)"
        by (simp add: take_map)
      moreover have "take (length ioT) (p_io pT) = ioT"
        using \<open>p_io pT = (ioT @ [(x, y)]) @ ioT'\<close> by auto
      ultimately show ?thesis by simp
    qed

    
    have "path M q ?pIO"
      using \<open>path M q ?p\<close> unfolding \<open>?pIO = take (length ioT) ?p\<close> 
      using path_prefix_take by metis
    

    have "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take (length ioT) pT))) RepSets = None"
      using \<open>(\<forall>p' p''. ?p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None)\<close>
            \<open>?p = ?pIO@(drop (length ioT) ?p)\<close>
            \<open>(drop (length ioT) ?p) \<noteq> []\<close> 
      by blast

    (* TODO: applied to wrong path \<rightarrow> needs to be applied to the path obtained from M' *)
    thm m_traversal_path_extension_exist[OF \<open>completely_specified M\<close> \<open>q \<in> nodes M\<close> \<open>inputs M \<noteq> {}\<close> t5 t8 \<open>path M q ?pIO\<close> \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take (length ioT) pT))) RepSets = None\<close>]

    let ?p = "pT @ pT'"
    


    show "(\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x', y')] \<in> set (prefixes (p_io pT')))"
      sorry
  qed



  then have p2: "(\<forall> q P pP ioT pT x y y' . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT'))))"
    by blast


  have p3: "(\<forall> q P pP pT . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<longrightarrow> (\<forall> q' A d1 d2 qT . q' \<in> rd_targets (q,pT) \<longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<longrightarrow> pass_separator_ATC M' A qT d2))"
    sorry


  show ?thesis 
    using p1 p2 p3 unfolding passes_test_suite.simps by blast
qed


end