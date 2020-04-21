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
  and     "observable M'"
  and     "inputs M' = inputs M"
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


    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast
    

    have "(p_io pP)@ioT@[(x',y')] \<in> L M"
      using \<open>(p_io pP)@ioT@[(x',y')] \<in> L M'\<close> assms(4) by blast
    then obtain pM' where "path M (initial M) pM'" and "p_io pM' = (p_io pP)@ioT@[(x',y')]" 
      by auto

    let ?pP = "take (length pP) pM'"
    let ?pT = "take (length ioT) (drop (length pP) pM')"
    let ?t  = "last pM'"


    have "pM' = ?pP @ ?pT @ [?t]"
    proof -
      have "length pM' = (length pP) + (length ioT) + 1"
        using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close> 
        unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", of pM', symmetric] 
        unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", of pP, symmetric] 
        by auto
      then show ?thesis
        by (metis (no_types, lifting) add_diff_cancel_right' antisym_conv antisym_conv2 append_butlast_last_id append_eq_append_conv2 butlast_conv_take drop_Nil drop_eq_Nil le_add1 less_add_one take_add) 
    qed

    

    have "p_io ?pP = p_io pP"  
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      by (metis (no_types, lifting) append_eq_conv_conj length_map take_map)

    have "p_io ?pT = ioT" 
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      using \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (metis (no_types, lifting) append_eq_conv_conj length_map map_append take_map) 
      
    have "p_io [?t] = [(x',y')]"
      using \<open>p_io pM' = (p_io pP)@ioT@[(x',y')]\<close>
      using \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (metis (no_types, lifting) append_is_Nil_conv last_appendR last_map last_snoc list.simps(8) list.simps(9))

    have "path M (initial M) ?pP"
      using \<open>path M (initial M) pM'\<close> \<open>pM' = ?pP @ ?pT @ [?t]\<close>
      by (meson path_prefix_take)
      

    have "?pP = pP"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) ?pP\<close> \<open>path M (initial M) pP\<close> \<open>p_io ?pP = p_io pP\<close>]
      by assumption
    then have "path M q (?pT@[?t])"
      by (metis \<open>FSM.initial P = FSM.initial M\<close> \<open>pM' = take (length pP) pM' @ take (length ioT) (drop (length pP) pM') @ [last pM']\<close> \<open>path M (FSM.initial M) pM'\<close> \<open>target (FSM.initial P) pP = q\<close> path_suffix)
    then have "path M q ?pT" 
         and  "?t \<in> transitions M" 
         and  "t_source ?t = target q ?pT"
      by auto



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
    and  "\<And> p' p''. ?p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
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
    then have "p_io ?pIO = p_io ?pT"
      using \<open>p_io ?pT = ioT\<close> by simp

    
    have "path M q ?pIO"
      using \<open>path M q ?p\<close> unfolding \<open>?pIO = take (length ioT) ?p\<close> 
      using path_prefix_take by metis


    have "?pT = ?pIO"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M q ?pIO\<close> \<open>path M q ?pT\<close> \<open>p_io ?pIO = p_io ?pT\<close>] 
      by simp




    show "(\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x', y')] \<in> set (prefixes (p_io pT')))"
    proof (cases "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?pT@[?t]))) RepSets = None")
      case True

      obtain pT' d' where "(?pT @ [?t] @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m"
        using m_traversal_path_extension_exist[OF \<open>completely_specified M\<close> \<open>q \<in> nodes M\<close> \<open>inputs M \<noteq> {}\<close> t5 t8 \<open>path M q (?pT@[?t])\<close> True]
        by auto
      then have "?pT @ [?t] @ pT' \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force

      moreover have "ioT @ [(x', y')] \<in> set (prefixes (p_io (?pT @ [?t] @ pT')))"
        using \<open>p_io ?pIO = ioT\<close> \<open>p_io [?t] = [(x',y')]\<close> 
        unfolding \<open>?pT = ?pIO\<close> prefixes_set by force

      ultimately show ?thesis 
        by blast
    next
      case False
      
      note \<open>path M q (?pT @ [?t])\<close> 
      moreover obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (?pT@[?t]))) RepSets = Some d'"
        using False by blast


      moreover have "\<forall> p' p''. (?pT @ [?t]) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
      proof -
        have "\<And> p' p''. (?pT @ [?t]) = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
        proof -
          fix p' p'' assume "(?pT @ [?t]) = p' @ p''" and "p'' \<noteq> []" 
          then obtain pIO' where "?pIO = p' @ pIO'"
            unfolding \<open>?pT = ?pIO\<close>
            by (metis butlast_append butlast_snoc)
          then have "?p = p'@pIO'@(drop (length ioT) ?p)"
            using \<open>?p = ?pIO@((drop (length ioT) ?p))\<close>
            by (metis append.assoc) 
  
          have "pIO' @ drop (length ioT) (pT @ pT') \<noteq> []"
            using \<open>(drop (length ioT) ?p) \<noteq> []\<close> by auto
  
          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
            using \<open>\<And> p' p''. ?p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None\<close>
                  [of p' "pIO'@(drop (length ioT) ?p)", OF \<open>?p = p'@pIO'@(drop (length ioT) ?p)\<close> \<open>pIO' @ drop (length ioT) (pT @ pT') \<noteq> []\<close>]
            by assumption
        qed
        then show ?thesis by blast
      qed

      ultimately have "((?pT @ [?t]),d') \<in> m_traversal_paths_with_witness M q RepSets m"
        using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m] 
        by auto
      then have "(?pT @ [?t]) \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force
      moreover have "ioT @ [(x', y')] \<in> set (prefixes (p_io (?pT @ [?t])))"
        using \<open>p_io ?pT = ioT\<close> \<open>p_io [?t] = [(x',y')]\<close>
        unfolding prefixes_set by force

      ultimately show ?thesis 
        by blast
    qed
  qed
  then have p2: "(\<forall> q P pP ioT pT x y y' . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> ioT @ [(x, y)] \<in> set (prefixes (p_io pT)) \<longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT @ [(x, y')] \<in> set (prefixes (p_io pT'))))"
    by blast


  have "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> q' \<in> rd_targets (q,pT) \<Longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<Longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> pass_separator_ATC M' A qT d2"
  proof -
    fix q P pP pT q' A d1 d2 qT
    assume "(q,P) \<in> prs" 
    and    "path P (initial P) pP" 
    and    "target (initial P) pP = q" 
    and    "pT \<in> tps q"  
    and    "q' \<in> rd_targets (q,pT)" 
    and    "(A,d1,d2) \<in> atcs (target q pT, q')" 
    and    "qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')"

    have "q \<in> fst ` prs"
      using \<open>(q,P) \<in> prs\<close> by force
    have "is_preamble P M q"
      using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast
    then have "q \<in> nodes M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_node submachine_path) 

    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast

    have "is_separator M (target q pT) q' A d1 d2"
      using t3[OF \<open>(A,d1,d2) \<in> atcs (target q pT, q')\<close>]
      by blast

    have "qT \<in> nodes M'"
      using \<open>qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')\<close>
            io_targets_nodes
      by (metis (no_types, lifting) subsetD) 

    obtain pT' d' where "(pT @ pT', d') \<in> m_traversal_paths_with_witness M q RepSets m"
      using t6[OF \<open>q \<in> fst ` prs\<close>] \<open>pT \<in> tps q\<close> 
      by blast
    then have "path M q pT"
      using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m] 
      by auto
    then have "target q pT \<in> FSM.nodes M"
      using path_target_is_node by metis

    have "q' \<in> FSM.nodes M"
      using is_separator_separated_node_is_node[OF \<open>is_separator M (target q pT) q' A d1 d2\<close>] by simp

    have "\<not> pass_separator_ATC M' A qT d2 \<Longrightarrow> \<not> LS M' qT \<subseteq> LS M (target q pT)"
      using pass_separator_ATC_fail_no_reduction[OF \<open>observable M'\<close> \<open>observable M\<close> \<open>qT \<in> nodes M'\<close> \<open>target q pT \<in> FSM.nodes M\<close> \<open>q' \<in> FSM.nodes M\<close> \<open>is_separator M (target q pT) q' A d1 d2\<close> \<open>inputs M' = inputs M\<close>]
      by assumption

    moreover have "LS M' qT \<subseteq> LS M (target q pT)"
    proof -
      have "(target q pT) = target (initial M) (pP@pT)"
        using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by auto

      have "path M (initial M) (pP@pT)"
        using \<open>path M (initial M) pP\<close> \<open>target (initial P) pP = q\<close> \<open>path M q pT\<close> unfolding \<open>initial P = initial M\<close> by auto
      
      then have "(target q pT) \<in> io_targets M (p_io pP @ p_io pT) (FSM.initial M)"
        unfolding io_targets.simps \<open>(target q pT) = target (initial M) (pP@pT)\<close>
        using map_append by blast 
      

      show ?thesis
        using observable_language_target[OF \<open>observable M\<close> \<open>(target q pT) \<in> io_targets M (p_io pP @ p_io pT) (FSM.initial M)\<close> \<open>qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M')\<close> \<open>L M' \<subseteq> L M\<close>]
        by assumption
    qed

    ultimately show "pass_separator_ATC M' A qT d2"
      by blast
  qed
  then have p3: "(\<forall> q P pP pT . (q,P) \<in> prs \<longrightarrow> path P (initial P) pP \<longrightarrow> target (initial P) pP = q \<longrightarrow> pT \<in> tps q \<longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<longrightarrow> (\<forall> q' A d1 d2 qT . q' \<in> rd_targets (q,pT) \<longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<longrightarrow> pass_separator_ATC M' A qT d2))"
    by blast


  show ?thesis 
    using p1 p2 p3 unfolding passes_test_suite.simps by blast
qed






lemma observable_path_suffix :
  assumes "(p_io p)@io \<in> LS M q"
  and     "path M q p"
  and     "observable M"
obtains p' where "path M (target q p) p'" and "p_io p' = io"
proof -
  obtain p1 p2 where "path M q p1" and "path M (target q p1) p2"  and "p_io p1 = p_io p" and "p_io p2 = io"
    using language_state_split[OF assms(1)] by blast

  have "p1 = p"
    using observable_path_unique[OF assms(3,2) \<open>path M q p1\<close> \<open>p_io p1 = p_io p\<close>[symmetric]]
    by simp

  show ?thesis using that[of p2] \<open>path M (target q p1) p2\<close> \<open>p_io p2 = io\<close> unfolding \<open>p1 = p\<close>
    by blast
qed


subsection \<open>Lower Bound\<close>
(* TODO: extract into new theory after completion *)

subsubsection \<open>R Functions\<close>


(* collect all proper suffixes of p that target q' if applied to q *)
definition R :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list set" where
  "R M q q' pP p = {pP @ p' | p' . p' \<noteq> [] \<and> target q p' = q' \<and> (\<exists> p'' . p = p'@p'')}" 

(* add one completed path of some Preamble of q' to R if a preamble exists *)
definition RP :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a \<times> ('a,'b,'c) preamble) set \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list set" where
  "RP M q q' pP p PS M' = (if \<exists> P' .  (q',P') \<in> PS then insert (SOME pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M') (R M q q' pP p) else (R M q q' pP p))" 





(* TODO: move *)
lemma language_intro :
  assumes "path M q p"
  shows "p_io p \<in> LS M q"
  using assms unfolding LS.simps by auto

(* TODO: move *)
lemma preamble_pass_path :
  assumes "is_preamble P M q"
  and     "\<And> io x y y' . io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
obtains p where "path P (initial P) p" and "target (initial P) p = q" and "p_io p \<in> L M'"
proof -
  (* get the longest paths p such that p_io p is still in L M' *)

  let ?ps = "{p . path P (initial P) p \<and> p_io p \<in> L M'}"
  have "?ps \<noteq> {}"
  proof -
    have "[] \<in> ?ps" by auto
    then show ?thesis by blast
  qed
  moreover have "finite ?ps"
  proof -
    have "acyclic P"
      using assms(1) unfolding is_preamble_def by blast
    have "finite {p. path P (FSM.initial P) p}"
      using acyclic_finite_paths_from_reachable_node[OF \<open>acyclic P\<close>, of "[]" "initial P"] by auto
    then show ?thesis
      by simp 
  qed
  ultimately obtain p where "p \<in> ?ps" and "\<And> p' . p' \<in> ?ps \<Longrightarrow> length p' \<le> length p" 
    by (meson leI max_length_elem) 
  then have "path P (initial P) p"
       and  "p_io p \<in> L M'"
    by blast+

  show ?thesis
  proof (cases "target (initial P) p = q")
    case True
    then show ?thesis using that[OF \<open>path P (initial P) p\<close> _ \<open>p_io p \<in> L M'\<close>] by blast
  next
    case False

    (* if p does not target the sole deadlock state q, then it can be extended *)

    then have "\<not> deadlock_state P (target (initial P) p)"
      using reachable_nodes_intro[OF \<open>path P (initial P) p\<close>] assms(1) unfolding is_preamble_def by fastforce
    then obtain t where "t \<in> transitions P" and "t_source t = target (initial P) p"
      by auto
    then have "path P (initial P) (p@[t])" 
      using \<open>path P (initial P) p\<close> path_append_transition by simp
    have "(p_io p) @ [(t_input t, t_output t)] \<in> L P"
      using language_intro[OF \<open>path P (initial P) (p@[t])\<close>] by simp

    have "t_input t \<in> inputs M'"
      using assms(1,4) fsm_transition_input[OF \<open>t \<in> transitions P\<close>] unfolding is_preamble_def is_submachine.simps by blast
    
    obtain p' where "path M' (initial M') p'" and "p_io p' = p_io p"
      using \<open>p_io p \<in> L M'\<close> by auto
    obtain t' where "t' \<in> transitions M'" and "t_source t' = target (initial M') p'" and "t_input t' = t_input t"
      using \<open>completely_specified M'\<close> \<open>t_input t \<in> inputs M'\<close> path_target_is_node[OF \<open>path M' (initial M') p'\<close>]
      unfolding completely_specified.simps by blast
    then have "path M' (initial M') (p'@[t'])" 
      using \<open>path M' (initial M') p'\<close> path_append_transition by simp
    have "(p_io p) @ [(t_input t, t_output t')] \<in> L M'"
      using language_intro[OF \<open>path M' (initial M') (p'@[t'])\<close>] 
      unfolding \<open>p_io p' = p_io p\<close>[symmetric] \<open>t_input t' = t_input t\<close>[symmetric] by simp

    have "(p_io p) @ [(t_input t, t_output t')] \<in> L P"
      using assms(2)[OF \<open>(p_io p) @ [(t_input t, t_output t)] \<in> L P\<close> \<open>(p_io p) @ [(t_input t, t_output t')] \<in> L M'\<close>]
      by assumption
    then obtain pt' where "path P (initial P) pt'" and "p_io pt' = (p_io p) @ [(t_input t, t_output t')]"
      by auto
    then have "pt' \<in> ?ps"
      using \<open>(p_io p) @ [(t_input t, t_output t')] \<in> L M'\<close> by auto
    then have "length pt' \<le> length p"
      using \<open>\<And> p' . p' \<in> ?ps \<Longrightarrow> length p' \<le> length p\<close> by blast
    moreover have "length pt' > length p"
      using \<open>p_io pt' = (p_io p) @ [(t_input t, t_output t')]\<close> 
      unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by simp
    ultimately have "False"
      by simp
    then show ?thesis by simp
  qed
qed
    




lemma RP_from_R :
  assumes "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "(RP M q q' pP p PS M' = R M q q' pP p) \<or> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
proof (rule ccontr)
  assume "\<not> (RP M q q' pP p PS M' = R M q q' pP p \<or> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p)))"
  then have "(RP M q q' pP p PS M' \<noteq> R M q q' pP p)"
       and  "\<not> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
    by blast+

  let ?p = "SOME pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'"

  have "\<exists> P' .  (q',P') \<in> PS"
    using \<open>(RP M q q' pP p PS M' \<noteq> R M q q' pP p)\<close> unfolding RP_def by auto
  then obtain P' where "(q',P') \<in> PS"
    by auto
  then have "is_preamble P' M q'"
    using assms by blast

  obtain pP' where "path P' (initial P') pP'" and "target (initial P') pP' = q'" and "p_io pP' \<in> L M'"
    using preamble_pass_path[OF \<open>is_preamble P' M q'\<close>  assms(2)[OF \<open>(q',P') \<in> PS\<close>] assms(3,4)] by force


  then have "\<exists> pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'"
    using \<open>(q',P') \<in> PS\<close> by blast
  have "\<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') ?p \<and> target (initial P') ?p = q' \<and> p_io ?p \<in> L M'"
    using someI_ex[OF \<open>\<exists> pP' . \<exists> P' .  (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> p_io pP' \<in> L M'\<close>] 
    by blast

  then obtain P'' where "(q',P'') \<in> PS" and "path P'' (initial P'') ?p" and "target (initial P'') ?p = q'" and "p_io ?p \<in> L M'"
    by auto
  then have "is_preamble P'' M q'"
    using assms by blast

  
  have "initial P'' = initial M"
    using \<open>is_preamble P'' M q'\<close> unfolding is_preamble_def by auto
  have "path M (initial M) ?p"
    using \<open>is_preamble P'' M q'\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P'' (FSM.initial P'') ?p\<close> by blast
  have "target (initial M) ?p = q'"
    using \<open>target (initial P'') ?p = q'\<close> unfolding \<open>initial P'' = initial M\<close> by assumption

  have "RP M q q' pP p PS M' = insert ?p (R M q q' pP p)"
    using \<open>\<exists> P' .  (q',P') \<in> PS\<close> unfolding RP_def by auto

  then have "(\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))"
    using \<open>(q',P'') \<in> PS\<close> \<open>path P'' (initial P'') ?p\<close> \<open>target (initial P'') ?p = q'\<close> \<open>path M (initial M) ?p\<close> \<open>target (initial M) ?p = q'\<close> \<open>p_io ?p \<in> L M'\<close> by blast
  then show "False"
    using \<open>\<not> (\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> RP M q q' pP p PS M' = insert pP' (R M q q' pP p))\<close>
    by blast
qed










lemma finite_R :
  assumes "path M q p"
  shows "finite (R M q q' pP p)"
proof -
  have "\<And> p' . p' \<in> (R M q q' pP p) \<Longrightarrow> p' \<in> set (prefixes (pP@p))"
  proof -
    fix p' assume "p' \<in> (R M q q' pP p)"
    then obtain p'' where "p' = pP @ p''"
      unfolding R_def by blast
    then obtain p''' where "p = p'' @ p'''"
      using \<open>p' \<in> (R M q q' pP p)\<close> unfolding R_def by blast
    
    show "p' \<in> set (prefixes (pP@p))"
      unfolding prefixes_set \<open>p' = pP @ p''\<close> \<open>p = p'' @ p'''\<close> by auto
  qed
  then have "(R M q q' pP p) \<subseteq> set (prefixes (pP@p))"
    by blast
  then show ?thesis
    using rev_finite_subset by auto 
qed

lemma finite_RP :
  assumes "path M q p"
  and     "\<And> q P . (q,P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "finite (RP M q q' pP p PS M')"
  using finite_R[OF assms(1), of q' pP ]
        RP_from_R[OF assms(2,3,4,5), of PS _ _ q q' pP p] by force
  




lemma card_union_of_singletons :
  assumes "\<And> S . S \<in> SS \<Longrightarrow> (\<exists> t . S = {t})"
shows "card (\<Union> SS) = card SS"
proof -
  let ?f = "\<lambda> x . {x}"
  have "bij_betw ?f (\<Union> SS) SS" 
    unfolding bij_betw_def inj_on_def using assms by fastforce
  then show ?thesis 
    using bij_betw_same_card by blast 
qed

lemma card_union_of_distinct :
  assumes "\<And> S1 S2 . S1 \<in> SS \<Longrightarrow> S2 \<in> SS \<Longrightarrow> S1 = S2 \<or> f S1 \<inter> f S2 = {}"
  and     "finite SS"
  and     "\<And> S . S \<in> SS \<Longrightarrow> f S \<noteq> {}"
shows "card (image f SS) = card SS" 
proof -
  from assms(2) have "\<forall> S1 \<in> SS . \<forall> S2 \<in> SS . S1 = S2 \<or> f S1 \<inter> f S2 = {} 
                      \<Longrightarrow> \<forall> S \<in> SS . f S \<noteq> {} \<Longrightarrow> ?thesis"
  proof (induction SS)
    case empty
    then show ?case by auto
  next
    case (insert x F)
    then have "\<not> (\<exists> y \<in> F . f y = f x)" 
      by auto
    then have "f x \<notin> image f F" 
      by auto
    then have "card (image f (insert x F)) = Suc (card (image f F))" 
      using insert by auto
    moreover have "card (f ` F) = card F" 
      using insert by auto
    moreover have "card (insert x F) = Suc (card F)" 
      using insert by auto
    ultimately show ?case 
      by simp
  qed
  then show ?thesis 
    using assms by simp
qed



(* TODO: move *)
lemma take_le :
  assumes "i \<le> length xs"
  shows "take i (xs@ys) = take i xs"
  by (simp add: assms less_imp_le_nat)

lemma butlast_take_le :
  assumes "i \<le> length (butlast xs)" 
  shows "take i (butlast xs) = take i xs" 
  using take_le[OF assms, of "[last xs]"]
  by (metis append_butlast_last_id butlast.simps(1)) 

lemma R_component_ob :
  assumes "pR' \<in> R M q q' pP p"
  obtains pR where "pR' = pP@pR"
  using assms unfolding R_def by blast

lemma R_component :
  assumes "(pP@pR) \<in> R M q q' pP p" 
shows "pR = take (length pR) p"
and   "length pR \<le> length p"
and   "t_target (p ! (length pR - 1)) = q'"
and   "pR \<noteq> []"
proof -
  let ?R = "R M q q' p"

  have "pR \<noteq> []" and "target q pR = q'" and "\<exists> p'' . p = pR@p''"
    using \<open>pP@pR \<in> R M q q' pP p\<close> unfolding R_def by blast+
  then obtain pR' where "p = pR@pR'"
    by blast

  then show "pR = take (length pR) p" and "length pR \<le> length p"
    by auto
  
  show "t_target (p ! (length pR - 1)) = q'"
    using \<open>pR \<noteq> []\<close> \<open>target q pR = q'\<close> unfolding target.simps visited_nodes.simps
    by (metis (no_types, lifting) Suc_diff_1 \<open>pR = take (length pR) p\<close> append_butlast_last_id last.simps last_map length_butlast lessI list.map_disc_iff not_gr_zero nth_append_length nth_take take_eq_Nil) 

  show "pR \<noteq> []" using \<open>pR \<noteq> []\<close> by assumption
qed


lemma R_component_observable :
  assumes "pP@pR \<in> R M (target (initial M) pP) q' pP p"
  and     "observable M"
  and     "path M (initial M) pP"
  and     "path M (target (initial M) pP) p"
shows "io_targets M (p_io pP @ p_io pR) (initial M) = {target (target (initial M) pP) (take (length pR) p)}"
proof -
  have "pR = take (length pR) p"
  and  "length pR \<le> length p"
  and  "t_target (p ! (length pR - 1)) = q'"
    using R_component[OF assms(1)] by blast+

  let ?q = "(target (initial M) pP)"
  have "path M ?q (take (length pR) p)"
    using assms(4) by (simp add: path_prefix_take) 
  have "p_io (take (length pR) p) = p_io pR"
    using \<open>pR = take (length pR) p\<close> by auto
    

  have *:"path M (initial M) (pP @ (take (length pR) p))"
    using \<open>path M (initial M) pP\<close> \<open>path M ?q (take (length pR) p)\<close> by auto
  have **:"p_io (pP @ (take (length pR) p)) = (p_io pP @ p_io pR)"
    using \<open>p_io (take (length pR) p) = p_io pR\<close> by auto
  
  have "target (initial M) (pP @ (take (length pR) p)) = target ?q (take (length pR) p)"
    by auto 
  then have "target ?q (take (length pR) p) \<in> io_targets M (p_io pP @ p_io pR) (initial M)"
    unfolding io_targets.simps using * **
    by (metis (mono_tags, lifting) mem_Collect_eq) 

  show "io_targets M (p_io pP @ p_io pR) (initial M) = {target ?q (take (length pR) p)}"
    using observable_io_targets[OF \<open>observable M\<close> language_state_containment[OF * **]]
    by (metis (no_types) \<open>target (target (FSM.initial M) pP) (take (length pR) p) \<in> io_targets M (p_io pP @ p_io pR) (FSM.initial M)\<close> singleton_iff)
qed


(* TODO: move *)
lemma io_targets_finite :
  "finite (io_targets M io q)"
proof -
  have "(io_targets M io q) \<subseteq> {target q p | p . path M q p \<and> length p \<le> length io}"
    unfolding io_targets.simps length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] by force
  moreover have "finite {target q p | p . path M q p \<and> length p \<le> length io}"
    using paths_finite[of M q "length io"]
    by simp 
  ultimately show ?thesis
    using rev_finite_subset by blast 
qed



lemma R_count :                        
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "observable M'"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "path M (target (initial M) pP) p"
  and     "p_io p = butlast io"
shows "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (R M (target (initial M) pP) q' pP p))) = card (R M (target (initial M) pP) q' pP p)"
  (is "card ?Tgts = card ?R")
and   "\<And> pR . pR \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
and   "\<And> pR1 pR2 . pR1 \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> pR2 \<in> (R M (target (initial M) pP) q' pP p) \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
proof -

  have "sequence_to_failure_extending_preamble_path M M' PS pP io"
  and  "\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'"
    using \<open>minimal_sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
    unfolding minimal_sequence_to_failure_extending_preamble_path_def   
    by blast+

  obtain q P where "(q,P) \<in> PS"
              and  "path P (initial P) pP"
              and  "target (initial P) pP = q"
              and  "((p_io pP) @ butlast io) \<in> L M" 
              and  "((p_io pP) @ io) \<notin> L M"
              and  "((p_io pP) @ io) \<in> L M'"

    using \<open>sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
    unfolding sequence_to_failure_extending_preamble_path_def  
    by blast

  have "is_preamble P M q"
    using \<open>(q,P) \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> by blast
  then have "q \<in> nodes M"
    unfolding is_preamble_def
    by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_node submachine_path) 

  have "initial P = initial M"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
  have "path M (initial M) pP"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P (FSM.initial P) pP\<close> by blast
  have "target (initial M) pP = q"
    using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption

  then have "path M q p"
    using \<open>path M (target (initial M) pP) p\<close> by auto

  have "io \<noteq> []"
    using \<open>((p_io pP) @ butlast io) \<in> L M\<close> \<open>((p_io pP) @ io) \<notin> L M\<close> by auto


  (* finiteness properties *)

  have "finite ?R"
    using finite_R[OF \<open>path M (target (initial M) pP) p\<close>]
    by assumption
  moreover have "\<And> pR . pR \<in> ?R \<Longrightarrow> finite (io_targets M' (p_io pR) (initial M'))"
    using io_targets_finite by metis
  ultimately have "finite ?Tgts"
    by blast


  (* path properties *)
  
  obtain pP' p' where "path M' (FSM.initial M') pP'" 
                and   "path M' (target (FSM.initial M') pP') p'" 
                and   "p_io pP' = p_io pP" 
                and   "p_io p' = io"
    using language_state_split[OF \<open>((p_io pP) @ io) \<in> L M'\<close>]
    by blast

  have "length p < length p'"
    using \<open>io \<noteq> []\<close> 
    unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] \<open>p_io p = butlast io\<close> \<open>p_io p' = io\<close> by auto

  let ?q = "(target (FSM.initial M') pP')"

  have "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
  proof -
    fix pR assume "pP@pR \<in> ?R"
    then have  "pR = take (length pR) p \<and> length pR \<le> length p"
      using R_component(1,2) by metis
    then have "p_io pR = take (length pR) (butlast io)"
      using \<open>p_io p = butlast io\<close>
      by (metis (no_types, lifting) take_map) 
    moreover have "p_io (take (length pR) p') = take (length pR) io"
      by (metis (full_types) \<open>p_io p' = io\<close> take_map)
    moreover have "take (length pR) (butlast io) = take (length pR) io"
      using \<open>pR = take (length pR) p \<and> length pR \<le> length p\<close>   
      unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] \<open>p_io p = butlast io\<close>
      using butlast_take_le[of "length (p_io pR)" io] by blast
    ultimately have "p_io (take (length pR) p') = p_io pR"
      by simp 
    moreover have "path M' ?q (take (length pR) p')"
      using \<open>path M' (target (FSM.initial M') pP') p'\<close>
      by (simp add: path_prefix_take) 
    ultimately show "path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
      by blast
  qed


  (* every element in R reaches exactly one state in M' *)

  have singleton_prop': "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
  proof -
    fix pR assume "pP@pR \<in> ?R"
    then have "path M' ?q (take (length pR) p')" and "p_io (take (length pR) p') = p_io pR"
      using \<open>\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR\<close> by blast+

    have *:"path M' (initial M') (pP' @ (take (length pR) p'))"
      using \<open>path M' (initial M') pP'\<close> \<open>path M' ?q (take (length pR) p')\<close> by auto
    have **:"p_io (pP' @ (take (length pR) p')) = (p_io (pP@pR))"
      using \<open>p_io pP' = p_io pP\<close> \<open>p_io (take (length pR) p') = p_io pR\<close> by auto
    
    have "target (initial M') (pP' @ (take (length pR) p')) = target ?q (take (length pR) p')"
      by auto 
    then have "target ?q (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (initial M')"
      unfolding io_targets.simps using * **
      by (metis (mono_tags, lifting) mem_Collect_eq) 

    show "io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
      using observable_io_targets[OF \<open>observable M'\<close> language_state_containment[OF * **]]
      by (metis (no_types) \<open>target (target (FSM.initial M') pP') (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (FSM.initial M')\<close> singleton_iff)
  qed

  have singleton_prop: "\<And> pR . pR \<in> ?R \<Longrightarrow> io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
  proof -
    fix pR assume "pR \<in> ?R"
    then obtain pR' where "pR = pP@pR'"
      using R_component_ob[of _ M "(target (FSM.initial M) pP)" q' pP p] by blast
    have **: "(length (pP @ pR') - length pP) = length pR'"
      by auto

    show "io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
      using singleton_prop'[of pR'] \<open>pR \<in> ?R\<close> unfolding \<open>pR = pP@pR'\<close> ** by blast
  qed
  then show "\<And> pR . pR \<in> ?R \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
    by blast

  (* distinct elements in R reach distinct states in M' *)
  have pairwise_dist_prop': "\<And> pR1 pR2 . pP@pR1 \<in> ?R \<Longrightarrow> pP@pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
  proof -
    
    have diff_prop: "\<And> pR1 pR2 . pP@pR1 \<in> ?R \<Longrightarrow> pP@pR2 \<in> ?R \<Longrightarrow> length pR1 < length pR2 \<Longrightarrow> io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
    proof -
      fix pR1 pR2 assume "pP@pR1 \<in> ?R" and "pP@pR2 \<in> ?R" and "length pR1 < length pR2"

      let ?i = "length pR1 - 1"
      let ?j = "length pR2 - 1"

      have "pR1 = take (length pR1) p" and \<open>length pR1 \<le> length p\<close> and "t_target (p ! ?i) = q'"
        using R_component[OF \<open>pP@pR1 \<in> ?R\<close>]
        by simp+
      have "length pR1 \<noteq> 0"
        using \<open>pP@pR1 \<in> ?R\<close> unfolding R_def
        by simp 
      then have "?i < ?j" 
        using \<open>length pR1 < length pR2\<close>
        by (simp add: less_diff_conv) 


      have "pR2 = take (length pR2) p" and \<open>length pR2 \<le> length p\<close> and "t_target (p ! ?j) = q'"
        using R_component[OF \<open>pP@pR2 \<in> ?R\<close>]
        by simp+
      then have "?j < length (butlast io)"
        unfolding \<open>p_io p = butlast io\<close>[symmetric] 
        unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric]
        using \<open>length pR1 < length pR2\<close> by auto 


      have "?q \<in> io_targets M' (p_io pP) (FSM.initial M')"
        unfolding \<open>p_io pP' = p_io pP\<close>[symmetric] io_targets.simps
        using \<open>path M' (initial M') pP'\<close> by auto

      have "t_target (p ! ?i) = t_target (p ! ?j)"
        using \<open>t_target (p ! ?i) = q'\<close> \<open>t_target (p ! ?j) = q'\<close> by simp
      then have "t_target (p' ! ?i) \<noteq> t_target (p' ! ?j)"
        using minimal_sequence_to_failure_extending_preamble_no_repetitions_along_path[OF assms(1,2,5,6) \<open>?q \<in> io_targets M' (p_io pP) (FSM.initial M')\<close> \<open>path M' (target (FSM.initial M') pP') p'\<close> \<open>p_io p' = io\<close> \<open>?i < ?j\<close> \<open>?j < length (butlast io)\<close> assms(4)]
        by blast

      have t1: "io_targets M' (p_io (pP@pR1)) (initial M') = {t_target (p' ! ?i)}"
      proof -
        have "(p' ! ?i) = last (take (length pR1) p')"
          using \<open>length pR1 \<le> length p\<close> \<open>length p < length p'\<close>
          by (metis Suc_diff_1 \<open>length pR1 \<noteq> 0\<close> dual_order.strict_trans2 length_0_conv length_greater_0_conv less_imp_diff_less take_last_index)
        then have *: "target (target (FSM.initial M') pP') (take (length pR1) p') = t_target (p' ! ?i)"
          unfolding target.simps visited_nodes.simps
          by (metis (no_types, lifting) \<open>length p < length p'\<close> \<open>length pR1 \<noteq> 0\<close> gr_implies_not_zero last.simps last_map length_0_conv map_is_Nil_conv take_eq_Nil) 
        have **: "(length (pP @ pR1) - length pP) = length pR1"
          by auto
        show ?thesis
          using singleton_prop[OF \<open>pP@pR1 \<in> ?R\<close>]
          unfolding * ** by assumption
      qed

      have t2: "io_targets M' (p_io (pP@pR2)) (initial M') = {t_target (p' ! ?j)}"
      proof -
        have "(p' ! ?j) = last (take (length pR2) p')"
          using \<open>length pR2 \<le> length p\<close> \<open>length p < length p'\<close>
          by (metis Suc_diff_1 \<open>length pR1 - 1 < length pR2 - 1\<close> le_less_trans less_imp_diff_less linorder_neqE_nat not_less_zero take_last_index zero_less_diff)
        then have *: "target (target (FSM.initial M') pP') (take (length pR2) p') = t_target (p' ! ?j)"
          unfolding target.simps visited_nodes.simps
          by (metis (no_types, lifting) Nil_is_map_conv \<open>length p < length p'\<close> \<open>length pR1 < length pR2\<close> last.simps last_map list.size(3) not_less_zero take_eq_Nil)
        have **: "(length (pP @ pR2) - length pP) = length pR2"
          by auto  
        show ?thesis
          using singleton_prop'[OF \<open>pP@pR2 \<in> ?R\<close>]
          unfolding * ** by assumption
      qed

      show "io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
        using \<open>t_target (p' ! ?i) \<noteq> t_target (p' ! ?j)\<close>
        unfolding t1 t2 by simp
    qed


    fix pR1 pR2 assume "pP@pR1 \<in> ?R" and "pP@pR2 \<in> ?R" and "pR1 \<noteq> pR2"
    then have "length pR1 \<noteq> length pR2"
      unfolding R_def
      by auto 

    then consider (a) "length pR1 < length pR2" | (b) "length pR2 < length pR1"
      using nat_neq_iff by blast 
    then show "io_targets M' (p_io (pP@pR1)) (initial M') \<inter> io_targets M' (p_io (pP@pR2)) (initial M') = {}"
    proof cases
      case a
      show ?thesis using diff_prop[OF \<open>pP@pR1 \<in> ?R\<close> \<open>pP@pR2 \<in> ?R\<close> a] by blast
    next
      case b
      show ?thesis using diff_prop[OF \<open>pP@pR2 \<in> ?R\<close> \<open>pP@pR1 \<in> ?R\<close> b] by blast
    qed
  qed

  then show pairwise_dist_prop: "\<And> pR1 pR2 . pR1 \<in> ?R \<Longrightarrow> pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}" 
    using R_component_ob
    by (metis (no_types, lifting)) 


  (* combining results *)

  let ?f = "(\<lambda> pR . io_targets M' (p_io pR) (initial M'))"
  
  have p1: "(\<And>S1 S2. S1 \<in> ?R \<Longrightarrow> S2 \<in> ?R \<Longrightarrow> S1 = S2 \<or> ?f S1 \<inter> ?f S2 = {})"
    using pairwise_dist_prop by blast
  have p2: "(\<And>S. S \<in> R M (target (FSM.initial M) pP) q' pP p \<Longrightarrow> io_targets M' (p_io S) (FSM.initial M') \<noteq> {})"
    using singleton_prop by blast
  have c1: "card (R M (target (FSM.initial M) pP) q' pP p) = card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p)"
    using card_union_of_distinct[of ?R, OF p1 \<open>finite ?R\<close> p2] by force

  have p3: "(\<And>S. S \<in> (\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p \<Longrightarrow> \<exists>t. S = {t})"
    using singleton_prop by blast
  have c2:"card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p) = card (\<Union>S\<in>R M (target (FSM.initial M) pP) q' pP p. io_targets M' (p_io S) (FSM.initial M'))"
    using card_union_of_singletons[of "((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` R M (target (FSM.initial M) pP) q' pP p)", OF p3] by force

    
  show "card ?Tgts = card ?R"
    unfolding c1 c2 by blast
qed






lemma R_update :
  "R M q q' pP (p@[t]) = (if (target q (p@[t]) = q')
                          then insert (pP@p@[t]) (R M q q' pP p)
                          else (R M q q' pP p))"
  (is "?R1 = ?R2")
proof (cases "(target q (p@[t]) = q')")
  case True
  then have *: "?R2 = insert (pP@p@[t]) (R M q q' pP p)"
    by auto
  
  have "\<And> p' . p' \<in> R M q q' pP (p@[t]) \<Longrightarrow> p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
  proof -
    fix p' assume "p' \<in> R M q q' pP (p@[t])"

    obtain p'' where "p' = pP @ p''"
      using R_component_ob[OF \<open>p' \<in> R M q q' pP (p@[t])\<close>] by blast

    obtain p''' where "p'' \<noteq> []" and "target q p'' = q'" and "p @ [t] = p'' @ p'''"
      using \<open>p' \<in> R M q q' pP (p@[t])\<close> unfolding R_def \<open>p' = pP @ p''\<close>
      by auto 

    show "p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
    proof (cases p''' rule: rev_cases)
      case Nil
      then have "p' = pP@(p@[t])" using \<open>p' = pP @ p''\<close> \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis by blast
    next
      case (snoc p'''' t')
      then have "p = p'' @ p''''" using \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis 
        unfolding R_def using \<open>p'' \<noteq> []\<close> \<open>target q p'' = q'\<close>
        by (simp add: \<open>p' = pP @ p''\<close>) 
    qed
  qed
  moreover have "\<And> p' . p' \<in> insert (pP@p@[t]) (R M q q' pP p) \<Longrightarrow> p' \<in> R M q q' pP (p@[t])"
  proof -
    fix p' assume "p' \<in> insert (pP@p@[t]) (R M q q' pP p)"
    then consider (a) "p' = (pP@p@[t])" | (b) "p' \<in> (R M q q' pP p)" by blast
    then show "p' \<in> R M q q' pP (p@[t])" proof cases
      case a
      then show ?thesis using True unfolding R_def
        by simp 
    next
      case b
      then show ?thesis unfolding R_def
        using append.assoc by blast 
    qed 
  qed
  ultimately show ?thesis 
    unfolding * by blast
next
  case False
  then have *: "?R2 = (R M q q' pP p)"
    by auto

  have "\<And> p' . p' \<in> R M q q' pP (p@[t]) \<Longrightarrow> p' \<in> (R M q q' pP p)"
  proof -
    fix p' assume "p' \<in> R M q q' pP (p@[t])"

    obtain p'' where "p' = pP @ p''"
      using R_component_ob[OF \<open>p' \<in> R M q q' pP (p@[t])\<close>] by blast

    obtain p''' where "p'' \<noteq> []" and "target q p'' = q'" and "p @ [t] = p'' @ p'''"
      using \<open>p' \<in> R M q q' pP (p@[t])\<close> unfolding R_def \<open>p' = pP @ p''\<close> by blast

    show "p' \<in> (R M q q' pP p)"
    proof (cases p''' rule: rev_cases)
      case Nil
      then have "p' = pP@(p@[t])" using \<open>p' = pP @ p''\<close> \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis
        using False \<open>p @ [t] = p'' @ p'''\<close> \<open>target q p'' = q'\<close> local.Nil by auto
    next
      case (snoc p'''' t')
      then have "p = p'' @ p''''" using \<open>p @ [t] = p'' @ p'''\<close> by auto
      then show ?thesis 
        unfolding R_def using \<open>p'' \<noteq> []\<close> \<open>target q p'' = q'\<close>
        by (simp add: \<open>p' = pP @ p''\<close>) 
    qed
  qed
  moreover have "\<And> p' . p' \<in> (R M q q' pP p) \<Longrightarrow> p' \<in> R M q q' pP (p@[t])"
  proof -
    fix p' assume "p' \<in> (R M q q' pP p)"
    then show "p' \<in> R M q q' pP (p@[t])" unfolding R_def
      using append.assoc by blast 
  qed
  ultimately show ?thesis 
    unfolding * by blast
qed



lemma R_union_card_is_suffix_length :
  assumes "path M (initial M) pP"
  and     "path M (target (initial M) pP) p"
shows "(\<Sum> q \<in> nodes M . card (R M (target (initial M) pP) q pP p)) = length p"
using assms(2) proof (induction p rule: rev_induct)
  case Nil
  have "\<And> q' . R M (target (initial M) pP) q' pP [] = {}"
    unfolding R_def by auto 
  then show ?case
    by simp 
next
  case (snoc t p)
  then have "path M (target (initial M) pP) p"
    by auto

  let ?q = "(target (initial M) pP)"
  let ?q' = "target ?q (p @ [t])"

  have "\<And> q . q \<noteq> ?q' \<Longrightarrow> R M ?q q pP (p@[t]) = R M ?q q pP p"
    using R_update[of M ?q _ pP p t] by force
  then have *: "(\<Sum> q \<in> nodes M - {?q'} . card (R M (target (initial M) pP) q pP (p@[t]))) = (\<Sum> q \<in> nodes M - {?q'} . card (R M (target (initial M) pP) q pP p))"
    by force



  have "R M ?q ?q' pP (p@[t]) = insert (pP@p@[t]) (R M ?q ?q' pP p)"
    using R_update[of M ?q ?q' pP p t] by force 
  moreover have "(pP@p@[t]) \<notin> (R M ?q ?q' pP p)"
    unfolding R_def by simp 
  ultimately have **: "card (R M (target (initial M) pP) ?q' pP (p@[t])) = Suc (card (R M (target (initial M) pP) ?q' pP p))"
    using finite_R[OF \<open>path M (target (initial M) pP) (p@[t])\<close>] finite_R[OF \<open>path M (target (initial M) pP) p\<close>]
    by simp


  have "?q' \<in> nodes M"
    using path_target_is_node[OF \<open>path M (target (FSM.initial M) pP) (p @ [t])\<close>] by assumption
  then have ***: "(\<Sum> q \<in> nodes M . card (R M (target (initial M) pP) q pP (p@[t]))) = (\<Sum> q \<in> nodes M - {?q'} . card (R M (target (initial M) pP) q pP (p@[t]))) + (card (R M (target (initial M) pP) ?q' pP (p@[t])))"
       and ****: "(\<Sum> q \<in> nodes M . card (R M (target (initial M) pP) q pP p)) = (\<Sum> q \<in> nodes M - {?q'} . card (R M (target (initial M) pP) q pP p)) + (card (R M (target (initial M) pP) ?q' pP p))"
    by (metis (no_types, lifting) Diff_insert_absorb add.commute finite_Diff fsm_nodes_finite mk_disjoint_insert sum.insert)+

  have "(\<Sum> q \<in> nodes M . card (R M (target (initial M) pP) q pP (p@[t]))) = Suc (\<Sum> q \<in> nodes M . card (R M (target (initial M) pP) q pP p))"
    unfolding **** *** ** * by simp

  then show ?case
    unfolding snoc.IH[OF \<open>path M (target (initial M) pP) p\<close>] by auto
qed






(* note: already incorporates a pass criterion *)
lemma RP_count :                        
  assumes "minimal_sequence_to_failure_extending_preamble_path M M' PS pP io"
  and     "observable M"
  and     "observable M'"
  and     "\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q"
  and     "path M (target (initial M) pP) p"
  and     "p_io p = butlast io"
  and     "\<And> q P io x y y' . (q,P) \<in> PS \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P"
  and     "completely_specified M'"
  and     "inputs M' = inputs M"
shows "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) = card (RP M (target (initial M) pP) q' pP p PS M')"
  (is "card ?Tgts = card ?RP")
and "\<And> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
and "\<And> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
proof -
  let ?P1 = "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) = card (RP M (target (initial M) pP) q' pP p PS M')"
  let ?P2 = "\<forall> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> (\<exists> q . io_targets M' (p_io pR) (initial M') = {q})"
  let ?P3 = "\<forall> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<longrightarrow> pR1 \<noteq> pR2 \<longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
  let ?combined_goals = "?P1 \<and> ?P2 \<and> ?P3"
    
  
  
  let ?q = "(target (initial M) pP)"
  let ?R = "R M ?q q' pP p"



  consider (a) "(?RP = ?R)" |
           (b) "(\<exists> P' pP' . (q',P') \<in> PS \<and> path P' (initial P') pP' \<and> target (initial P') pP' = q' \<and> path M (initial M) pP' \<and> target (initial M) pP' = q' \<and> p_io pP' \<in> L M' \<and> ?RP = insert pP' ?R)"
    using RP_from_R[OF assms(4,7,8,9), of PS _ _ ?q q' pP p] by force

  then have ?combined_goals proof cases
    case a
    show ?thesis unfolding a using R_count[OF assms(1-6)] by blast
  next
    case b
    

    (* properties from R_count *)

    have "sequence_to_failure_extending_preamble_path M M' PS pP io"
    and  "\<And> p' io' . sequence_to_failure_extending_preamble_path M M' PS p' io' \<Longrightarrow> length io \<le> length io'"
      using \<open>minimal_sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
      unfolding minimal_sequence_to_failure_extending_preamble_path_def   
      by blast+
  
    obtain q P where "(q,P) \<in> PS"
                and  "path P (initial P) pP"
                and  "target (initial P) pP = q"
                and  "((p_io pP) @ butlast io) \<in> L M" 
                and  "((p_io pP) @ io) \<notin> L M"
                and  "((p_io pP) @ io) \<in> L M'"
  
      using \<open>sequence_to_failure_extending_preamble_path M M' PS pP io\<close>
      unfolding sequence_to_failure_extending_preamble_path_def  
      by blast
  
    have "is_preamble P M q"
      using \<open>(q,P) \<in> PS\<close> \<open>\<And> q P. (q, P) \<in> PS \<Longrightarrow> is_preamble P M q\<close> by blast
    then have "q \<in> nodes M"
      unfolding is_preamble_def
      by (metis \<open>path P (FSM.initial P) pP\<close> \<open>target (FSM.initial P) pP = q\<close> path_target_is_node submachine_path) 
  
    have "initial P = initial M"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
    have "path M (initial M) pP"
      using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
      using \<open>path P (FSM.initial P) pP\<close> by blast
    have "target (initial M) pP = q"
      using \<open>target (initial P) pP = q\<close> unfolding \<open>initial P = initial M\<close> by assumption
  
    then have "path M q p"
      using \<open>path M (target (initial M) pP) p\<close> by auto
  
    have "io \<noteq> []"
      using \<open>((p_io pP) @ butlast io) \<in> L M\<close> \<open>((p_io pP) @ io) \<notin> L M\<close> by auto
  
  
    (* finiteness properties *)
  
    have "finite ?RP"                                          
      using finite_RP[OF \<open>path M (target (initial M) pP) p\<close> assms(4,7,8,9)] by force
    moreover have "\<And> pR . pR \<in> ?RP \<Longrightarrow> finite (io_targets M' (p_io pR) (initial M'))"
      using io_targets_finite by metis
    ultimately have "finite ?Tgts"
      by blast
  
  
    (* path properties *)
    
    obtain pP' p' where "path M' (FSM.initial M') pP'" 
                  and   "path M' (target (FSM.initial M') pP') p'" 
                  and   "p_io pP' = p_io pP" 
                  and   "p_io p' = io"
      using language_state_split[OF \<open>((p_io pP) @ io) \<in> L M'\<close>]
      by blast
  
    have "length p < length p'"
      using \<open>io \<noteq> []\<close> 
      unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] \<open>p_io p = butlast io\<close> \<open>p_io p' = io\<close> by auto
  
    let ?q = "(target (FSM.initial M') pP')"
  
    have "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
    proof -
      fix pR assume "pP@pR \<in> ?R"
      then have  "pR = take (length pR) p \<and> length pR \<le> length p"
        using R_component(1,2) by metis
      then have "p_io pR = take (length pR) (butlast io)"
        using \<open>p_io p = butlast io\<close>
        by (metis (no_types, lifting) take_map) 
      moreover have "p_io (take (length pR) p') = take (length pR) io"
        by (metis (full_types) \<open>p_io p' = io\<close> take_map)
      moreover have "take (length pR) (butlast io) = take (length pR) io"
        using \<open>pR = take (length pR) p \<and> length pR \<le> length p\<close>   
        unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] \<open>p_io p = butlast io\<close>
        using butlast_take_le[of "length (p_io pR)" io] by blast
      ultimately have "p_io (take (length pR) p') = p_io pR"
        by simp 
      moreover have "path M' ?q (take (length pR) p')"
        using \<open>path M' (target (FSM.initial M') pP') p'\<close>
        by (simp add: path_prefix_take) 
      ultimately show "path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR"
        by blast
    qed
  
  
    (* every element in R reaches exactly one state in M' *)
  
    have singleton_prop'_R: "\<And> pR . pP@pR \<in> ?R \<Longrightarrow> io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
    proof -
      fix pR assume "pP@pR \<in> ?R"
      then have "path M' ?q (take (length pR) p')" and "p_io (take (length pR) p') = p_io pR"
        using \<open>\<And> pR . pP@pR \<in> ?R \<Longrightarrow> path M' ?q (take (length pR) p') \<and> p_io (take (length pR) p') = p_io pR\<close> by blast+
  
      have *:"path M' (initial M') (pP' @ (take (length pR) p'))"
        using \<open>path M' (initial M') pP'\<close> \<open>path M' ?q (take (length pR) p')\<close> by auto
      have **:"p_io (pP' @ (take (length pR) p')) = (p_io (pP@pR))"
        using \<open>p_io pP' = p_io pP\<close> \<open>p_io (take (length pR) p') = p_io pR\<close> by auto
      
      have "target (initial M') (pP' @ (take (length pR) p')) = target ?q (take (length pR) p')"
        by auto 
      then have "target ?q (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (initial M')"
        unfolding io_targets.simps using * **
        by (metis (mono_tags, lifting) mem_Collect_eq) 
  
      show "io_targets M' (p_io (pP@pR)) (initial M') = {target ?q (take (length pR) p')}"
        using observable_io_targets[OF \<open>observable M'\<close> language_state_containment[OF * **]]
        by (metis (no_types) \<open>target (target (FSM.initial M') pP') (take (length pR) p') \<in> io_targets M' (p_io (pP@pR)) (FSM.initial M')\<close> singleton_iff)
    qed
  
    have singleton_prop_R: "\<And> pR . pR \<in> ?R \<Longrightarrow> io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
    proof -
      fix pR assume "pR \<in> ?R"
      then obtain pR' where "pR = pP@pR'"
        using R_component_ob[of _ M "(target (FSM.initial M) pP)" q' pP p] by blast
      have **: "(length (pP @ pR') - length pP) = length pR'"
        by auto
  
      show "io_targets M' (p_io pR) (initial M') = {target ?q (take (length pR - length pP) p')}"
        using singleton_prop'_R[of pR'] \<open>pR \<in> ?R\<close> unfolding \<open>pR = pP@pR'\<close> ** by blast
    qed




    (* RP props *)

    from b obtain P' pP'' where "(q',P') \<in> PS"
                          and   "path P' (initial P') pP''"
                          and   "target (initial P') pP'' = q'"
                          and   "path M (initial M) pP''"
                          and   "target (initial M) pP'' = q'"
                          and   "p_io pP'' \<in> L M'"
                          and   "?RP = insert pP'' ?R"
      by blast
    have "initial P' = initial M"
      using assms(4)[OF \<open>(q',P') \<in> PS\<close>] unfolding is_preamble_def by auto

    

    (* revisiting singleton_prop *)

    have "\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''"
      using \<open>?RP = insert pP'' ?R\<close> by blast
    then have rp_cases[consumes 1, case_names in_R inserted]: "\<And> pR P . (pR \<in> ?RP) \<Longrightarrow> (pR \<in> ?R \<Longrightarrow> P) \<Longrightarrow> (pR = pP'' \<Longrightarrow> P) \<Longrightarrow> P" 
      by force 

    have singleton_prop_RP: "\<And> pR . pR \<in> ?RP \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
    proof - 
      fix pR assume "pR \<in> ?RP"
      then show "\<exists> q . io_targets M' (p_io pR) (initial M') = {q}" 
      proof (cases rule: rp_cases)
        case in_R
        then show ?thesis using singleton_prop_R by blast
      next
        case inserted
        show ?thesis 
          using observable_io_targets[OF \<open>observable M'\<close> \<open>p_io pP'' \<in> L M'\<close>] unfolding inserted
          by meson 
      qed
    qed
    then have ?P2 by blast






    (* distinctness in RP *)

    have pairwise_dist_prop_RP: "\<And> pR1 pR2 . pR1 \<in> ?RP \<Longrightarrow> pR2 \<in> ?RP \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
    proof -
      
      have pairwise_dist_prop_R: "\<And> pR1 pR2 . pR1 \<in> ?R \<Longrightarrow> pR2 \<in> ?R \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}" 
        using R_count(3)[OF assms(1-6)] by force

      have pairwise_dist_prop_PS: "\<And> pR1 . pR1 \<in> ?RP \<Longrightarrow> pR1 \<noteq> pP'' \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pP'') (initial M') = {}"
      proof -
        fix pR1 assume "pR1 \<in> ?RP" and "pR1 \<noteq> pP''"
        then have "pR1 \<in> ?R"
          using \<open>\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''\<close> by blast

        

        
        obtain pR' where "pR1 = pP@pR'"
          using R_component_ob[OF \<open>pR1 \<in> ?R\<close>] by blast
        then have "pP@pR' \<in> ?R"
          using \<open>pR1 \<in> ?R\<close> by blast

        have "pR' = take (length pR') p" and "length pR' \<le> length p" and "t_target (p ! (length pR' - 1)) = q'" and "pR' \<noteq> []"
          using R_component[OF \<open>pP@pR' \<in> ?R\<close>] by blast+

        let ?i = "(length pR') - 1"
        have "?i < length p"
          using \<open>length pR' \<le> length p\<close> \<open>pR' \<noteq> []\<close>
          using diff_less dual_order.strict_trans1 less_numeral_extra(1) by blast 
        then have "?i < length (butlast io)"
          unfolding length_map[of "(\<lambda> t . (t_input t, t_output t))", symmetric] \<open>p_io p = butlast io\<close> by assumption


        have "io_targets M' (p_io pR1) (initial M') = {t_target (p' ! ?i)}"
        proof -
          have "(p' ! ?i) = last (take (length pR') p')"
            using \<open>length pR' \<le> length p\<close> \<open>length p < length p'\<close>
            by (metis Suc_diff_1 \<open>pR' \<noteq> []\<close> dual_order.strict_trans2 length_greater_0_conv less_imp_diff_less take_last_index)
          then have *: "target ?q (take (length pR') p') = t_target (p' ! ?i)"
            unfolding target.simps visited_nodes.simps
            by (metis (no_types, lifting) \<open>length p < length p'\<close> \<open>pR' \<noteq> []\<close> gr_implies_not_zero last.simps last_map length_0_conv map_is_Nil_conv take_eq_Nil) 
          moreover have "io_targets M' (p_io pR1) (initial M') = {target ?q (take (length pR') p')}"
            using singleton_prop'_R \<open>pR1 \<in> ?R\<close> unfolding \<open>pR1 = pP@pR'\<close> by auto
          ultimately show ?thesis by auto
        qed

        have "t_target (p' ! (length pR' - 1)) \<notin> io_targets M' (p_io pP'') (FSM.initial M')"
        proof -
          have "target (FSM.initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')"
            using \<open>p_io pP' = p_io pP\<close> \<open>path M' (FSM.initial M') pP'\<close> observable_path_io_target by auto 
  
          have "(t_target (p ! (length pR' - 1)), P') \<in> PS"
            using \<open>(q',P') \<in> PS\<close> unfolding \<open>t_target (p ! (length pR' - 1)) = q'\<close> by assumption
  
          have "target (FSM.initial P') pP'' = t_target (p ! (length pR' - 1))"
            unfolding \<open>target (initial M) pP'' = q'\<close> \<open>t_target (p ! (length pR' - 1)) = q'\<close> \<open>initial P' = initial M\<close> by simp

          show ?thesis
            using minimal_sequence_to_failure_extending_preamble_no_repetitions_with_other_preambles[OF assms(1,2,5,6) \<open>target (FSM.initial M') pP' \<in> io_targets M' (p_io pP) (FSM.initial M')\<close> \<open>path M' (target (FSM.initial M') pP') p'\<close> \<open>p_io p' = io\<close> assms(4) \<open>?i < length (butlast io)\<close> \<open>(t_target (p ! (length pR' - 1)), P') \<in> PS\<close> \<open>path P' (initial P') pP''\<close> \<open>target (FSM.initial P') pP'' = t_target (p ! (length pR' - 1))\<close>]
            by blast
        qed
        then show "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pP'') (initial M') = {}"
          unfolding \<open>io_targets M' (p_io pR1) (initial M') = {t_target (p' ! ?i)}\<close> by blast
      qed


      fix pR1 pR2 assume "pR1 \<in> ?RP" and "pR2 \<in> ?RP" and "pR1 \<noteq> pR2"

      then consider (a) "pR1 \<in> ?R \<and> pR2 \<in> ?R" |
                    (b) "pR1 = pP''" |
                    (c) "pR2 = pP''" 
        using \<open>\<And> pR . pR \<in> ?RP \<Longrightarrow> pR \<in> ?R \<or> pR = pP''\<close> \<open>pR1 \<noteq> pR2\<close> by blast
      then show "io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
      proof cases
        case a
        then show ?thesis using pairwise_dist_prop_R[of pR1 pR2, OF _ _ \<open>pR1 \<noteq> pR2\<close>] by blast
      next
        case b
        then show ?thesis using pairwise_dist_prop_PS[OF \<open>pR2 \<in> ?RP\<close>] \<open>pR1 \<noteq> pR2\<close> by blast
      next
        case c
        then show ?thesis using pairwise_dist_prop_PS[OF \<open>pR1 \<in> ?RP\<close>] \<open>pR1 \<noteq> pR2\<close> by blast
      qed
    qed
    then have ?P3 by blast

    
    

    let ?f = "(\<lambda> pR . io_targets M' (p_io pR) (initial M'))"
  
    have p1: "(\<And>S1 S2. S1 \<in> ?RP \<Longrightarrow> S2 \<in> ?RP \<Longrightarrow> S1 = S2 \<or> ?f S1 \<inter> ?f S2 = {})"
      using pairwise_dist_prop_RP by blast
    have p2: "(\<And>S. S \<in> ?RP \<Longrightarrow> io_targets M' (p_io S) (FSM.initial M') \<noteq> {})"
      using singleton_prop_RP by blast
    have c1: "card ?RP = card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP)"
      using card_union_of_distinct[of ?RP, OF p1 \<open>finite ?RP\<close> p2] by force
  
    have p3: "(\<And>S. S \<in> (\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP \<Longrightarrow> \<exists>t. S = {t})"
      using singleton_prop_RP by blast
    have c2:"card ((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP) = card (\<Union>S\<in>?RP. io_targets M' (p_io S) (FSM.initial M'))"
      using card_union_of_singletons[of "((\<lambda>S. io_targets M' (p_io S) (FSM.initial M')) ` ?RP)", OF p3] by force
  
      
    have ?P1
      unfolding c1 c2 by blast

    show ?combined_goals using \<open>?P1\<close> \<open>?P2\<close> \<open>?P3\<close> by blast
  qed

  

  then show "card (\<Union> (image (\<lambda> pR . io_targets M' (p_io pR) (initial M')) (RP M (target (initial M) pP) q' pP p PS M'))) = card (RP M (target (initial M) pP) q' pP p PS M')"
       and  "\<And> pR . pR \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> \<exists> q . io_targets M' (p_io pR) (initial M') = {q}"
       and  "\<And> pR1 pR2 . pR1 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR2 \<in> (RP M (target (initial M) pP) q' pP p PS M') \<Longrightarrow> pR1 \<noteq> pR2 \<Longrightarrow> io_targets M' (p_io pR1) (initial M') \<inter> io_targets M' (p_io pR2) (initial M') = {}"
    by blast+
qed



end (*




lemma passes_test_suite_exhaustiveness :
  assumes "observable M"
  and     "completely_specified M"
  and     "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m"
  and     "passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'"
  and     "observable M'"
  and     "inputs M' = inputs M"
  and     "inputs M \<noteq> {}"
shows     "L M' \<subseteq> L M"
proof (rule ccontr)
  assume "\<not> L M' \<subseteq> L M"


  (* sufficiency properties *)


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
  


  (* pass properties *)

  have pass1: "\<And> q P io x y y' . (q,P) \<in> prs \<Longrightarrow> io@[(x,y)] \<in> L P \<Longrightarrow> io@[(x,y')] \<in> L M' \<Longrightarrow> io@[(x,y')] \<in> L P" 
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
    unfolding passes_test_suite.simps
    by meson 

  have pass2: "\<And> q P pP ioT pT x y y' . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> ioT@[(x,y)] \<in> set (prefixes (p_io pT)) \<Longrightarrow> (p_io pP)@ioT@[(x,y')] \<in> L M' \<Longrightarrow> (\<exists> pT' . pT' \<in> tps q \<and> ioT@[(x,y')] \<in> set (prefixes (p_io pT')))"
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
    unfolding passes_test_suite.simps by blast

  have pass3: "\<And> q P pP pT q' A d1 d2 qT . (q,P) \<in> prs \<Longrightarrow> path P (initial P) pP \<Longrightarrow> target (initial P) pP = q \<Longrightarrow> pT \<in> tps q \<Longrightarrow> (p_io pP)@(p_io pT) \<in> L M' \<Longrightarrow> q' \<in> rd_targets (q,pT) \<Longrightarrow> (A,d1,d2) \<in> atcs (target q pT, q') \<Longrightarrow> qT \<in> io_targets M' ((p_io pP)@(p_io pT)) (initial M') \<Longrightarrow> pass_separator_ATC M' A qT d2"  
    using \<open>passes_test_suite M (Test_Suite prs tps rd_targets atcs) M'\<close>
    unfolding passes_test_suite.simps by blast


  (* seq to failure *)


  obtain io where "minimal_sequence_to_failure_extending_preamble M M' prs io"
    using minimal_sequence_to_failure_extending_preamble_ex[OF t1 \<open>\<not> L M' \<subseteq> L M\<close>] by blast

  then have "sequence_to_failure_extending_preamble M M' prs io" 
            "\<And> io'. sequence_to_failure_extending_preamble M M' prs io' \<Longrightarrow> length io \<le> length io'"
    unfolding minimal_sequence_to_failure_extending_preamble_def
    by blast+

  obtain q P p where "q \<in> nodes M"
                 and "(q,P) \<in> prs"
                 and "path P (initial P) p"
                 and "target (initial P) p = q"
                 and "((p_io p) @ butlast io) \<in> L M" 
                 and "((p_io p) @ io) \<notin> L M"
                 and "((p_io p) @ io) \<in> L M'"
    using \<open>sequence_to_failure_extending_preamble M M' prs io\<close>
    unfolding sequence_to_failure_extending_preamble_def 
    by blast

  let ?xF = "fst (last io)"
  let ?yF = "snd (last io)"
  let ?xyF = "(?xF,?yF)"
  let ?ioF = "butlast io"
  have "io \<noteq> []"
    using \<open>((p_io p) @ io) \<notin> L M\<close> \<open>((p_io p) @ butlast io) \<in> L M\<close> by auto
  then have "io = ?ioF@[?xyF]"
    by auto

  have "?xF \<in> inputs M'"
    using language_io(1)[OF \<open>((p_io p) @ io) \<in> L M'\<close>, of ?xF ?yF] \<open>io \<noteq> []\<close> by auto 
  then have "?xF \<in> inputs M"
    using assms(6) by simp

  have "q \<in> fst ` prs"
    using \<open>(q,P) \<in> prs\<close> by force
  have "is_preamble P M q"
    using \<open>(q,P) \<in> prs\<close> \<open>\<And> q P. (q, P) \<in> prs \<Longrightarrow> is_preamble P M q \<and> tps q \<noteq> {}\<close> by blast
  then have "q \<in> nodes M"
    unfolding is_preamble_def
    by (metis \<open>path P (FSM.initial P) p\<close> \<open>target (FSM.initial P) p = q\<close> path_target_is_node submachine_path) 

  have "initial P = initial M"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def by auto
  have "path M (initial M) p"
    using \<open>is_preamble P M q\<close> unfolding is_preamble_def using submachine_path_initial
    using \<open>path P (FSM.initial P) p\<close> by blast
  have "target (initial M) p = q"
    using \<open>target (initial P) p = q\<close> unfolding \<open>initial P = initial M\<close> by assumption


  (* io must be a proper extension of some m-traversal path, as all m-traversal paths pass *)
  obtain pM dM ioEx where "(pM,dM) \<in> m_traversal_paths_with_witness M q RepSets m"
                    and   "io = (p_io pM)@ioEx"
                    and   "ioEx \<noteq> []"
  proof -
    
    obtain pF where "path M q pF" and "p_io pF = ?ioF"
      using observable_path_suffix[OF \<open>((p_io p) @ ?ioF) \<in> L M\<close> \<open>path M (initial M) p\<close> \<open>observable M\<close> ]
      unfolding \<open>target (initial M) p = q\<close>
      by blast

    obtain tM where "tM \<in> transitions M" and "t_source tM = target q pF" and "t_input tM = ?xF"
      using \<open>?xF \<in> inputs M\<close> path_target_is_node[OF \<open>path M q pF\<close>]
            \<open>completely_specified M\<close>
      unfolding completely_specified.simps
      by blast

    then have "path M q (pF@[tM])"
      using \<open>path M q pF\<close> path_append_transition by simp




    show ?thesis proof (cases "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pF@[tM]))) RepSets")
      case None

      (* if no RepSets witness exists for (pF@[tM]), then it is a proper prefix of some m-traversal path and hence also in L M, providing a contradiction*)

      obtain pF' d' where "((pF@[tM]) @ pF', d') \<in> m_traversal_paths_with_witness M q RepSets m"
        using m_traversal_path_extension_exist[OF \<open>completely_specified M\<close> \<open>q \<in> nodes M\<close> \<open>inputs M \<noteq> {}\<close> t5 t8 \<open>path M q (pF@[tM])\<close> None]
        by blast

      then have "(pF@[tM]) @ pF' \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>] by force


      
      have "(p_io pF) @ [(?xF,t_output tM)] \<in> set (prefixes (p_io ((pF@[tM])@pF')))"
        using \<open>t_input tM = ?xF\<close>
        unfolding prefixes_set by auto

      have "p_io p @ p_io pF @ [?xyF] \<in> L M'"
        using \<open>((p_io p) @ io) \<in> L M'\<close> unfolding \<open>p_io pF = ?ioF\<close> \<open>io = ?ioF@[?xyF]\<close>[symmetric] by assumption

      obtain pT' where "pT' \<in> tps q" 
                 and   "p_io pF @ [(fst (last io), snd (last io))] \<in> set (prefixes (p_io pT'))"
        using pass2[OF \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>(pF@[tM]) @ pF' \<in> tps q\<close> \<open>(p_io pF) @ [(?xF,t_output tM)] \<in> set (prefixes (p_io ((pF@[tM])@pF')))\<close> \<open>p_io p @ p_io pF @ [?xyF] \<in> L M'\<close>]
        by blast

      have "path M q pT'"
      proof -
        obtain pT'' d'' where "(pT'@pT'', d'') \<in> m_traversal_paths_with_witness M q RepSets m"
          using \<open>pT' \<in> tps q\<close> t6[OF \<open>q \<in> fst ` prs\<close>] by blast
        then have "path M q (pT'@pT'')"
          using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>] 
          by force
        then show ?thesis by auto
      qed
      then have "path M (initial M) (p@pT')"
        using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> by auto
      then have "(p_io (p@pT')) \<in> L M"
        unfolding LS.simps by blast
      then have "(p_io p)@(p_io pT') \<in> L M"
        by auto
      


      have "io \<in> set (prefixes (p_io pT'))"
        using \<open>p_io pF @ [(fst (last io), snd (last io))] \<in> set (prefixes (p_io pT'))\<close>
        unfolding \<open>p_io pF = ?ioF\<close> \<open>io = ?ioF@[?xyF]\<close>[symmetric] by assumption
      then obtain io' where "p_io pT' = io @ io'"
        unfolding prefixes_set by moura
      
      have " p_io p @ io \<in> L M"
        using \<open>(p_io p)@(p_io pT') \<in> L M\<close> 
        unfolding \<open>p_io pT' = io @ io'\<close>
        unfolding append.assoc[symmetric]
        using language_prefix[of "p_io p @ io" io', of M "initial M"] 
        by blast
      
      then show ?thesis
        using \<open>(p_io p) @ io \<notin> L M\<close> by simp
    next
      case (Some d)

      (* get the shortest prefix of pF that still has a RepSet witness *)

      let ?ps = "{ p1 . \<exists> p2 . (pF@[tM]) = p1 @ p2 \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p1)) RepSets \<noteq> None}"

      have "finite ?ps"
      proof -
        have "?ps \<subseteq> set (prefixes (pF@[tM]))"
          unfolding prefixes_set by force
        moreover have "finite (set (prefixes (pF@[tM])))"
          by simp
        ultimately show ?thesis
          by (simp add: finite_subset) 
      qed
      moreover have "?ps \<noteq> {}"
      proof -
        have "pF @ [tM] = (pF @ [tM]) @ [] \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (pF @ [tM]))) RepSets \<noteq> None"
          using Some by auto
        then have "(pF@[tM]) \<in> ?ps"
          by blast
        then show ?thesis by blast
      qed
      ultimately obtain pMin where "pMin \<in> ?ps" and "\<And> p' . p' \<in> ?ps \<Longrightarrow> length pMin \<le> length p'"
        by (meson leI min_length_elem) 




      obtain pMin' dMin where "(pF@[tM]) = pMin @ pMin'" and "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pMin)) RepSets = Some dMin"
        using \<open>pMin \<in> ?ps\<close> by blast
      then have "path M q pMin"
        using \<open>path M q (pF@[tM])\<close> by auto

      moreover have "(\<forall>p' p''. pMin = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None)"
      proof -
        have "\<And> p' p''. pMin = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
        proof -
          fix p' p'' assume "pMin = p' @ p''" and "p'' \<noteq> []"
          show "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets = None"
          proof (rule ccontr) 
            assume "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) RepSets \<noteq> None"
            then have "p' \<in> ?ps"
              using \<open>(pF@[tM]) = pMin @ pMin'\<close> unfolding \<open>pMin = p' @ p''\<close> append.assoc by blast
            
            have "length p' < length pMin"
              using \<open>pMin = p' @ p''\<close> \<open>p'' \<noteq> []\<close> by auto
            then show "False"
              using \<open>\<And> p' . p' \<in> ?ps \<Longrightarrow> length pMin \<le> length p'\<close>[OF \<open>p' \<in> ?ps\<close>] by simp
          qed
        qed
        then show ?thesis by blast
      qed
      
      ultimately have "(pMin,dMin) \<in> m_traversal_paths_with_witness M q RepSets m"
        using \<open>find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) pMin)) RepSets = Some dMin\<close>
              m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>, of m]
        by blast

      then have "pMin \<in> tps q"
        using t6[OF \<open>q \<in> fst ` prs\<close>]
        by force
  

      show ?thesis proof (cases "pMin = (pF@[tM])")
        (* if the m-traversal path is not shorter than io, then again the failure is observed *)
        case True 
        then have "?ioF @ [(?xF, t_output tM)] \<in> set (prefixes (p_io pMin))"
          using \<open>p_io pF = ?ioF\<close> \<open>t_input tM = ?xF\<close> unfolding prefixes_set by force


        obtain pMinF where "pMinF \<in> tps q" and "io \<in> set (prefixes (p_io pMinF))"
          using pass2[OF \<open>(q,P) \<in> prs\<close> \<open>path P (initial P) p\<close> \<open>target (initial P) p = q\<close> \<open>pMin \<in> tps q\<close> \<open>?ioF @ [(?xF, t_output tM)] \<in> set (prefixes (p_io pMin))\<close>, of ?yF]
          using \<open>p_io p @ io \<in> L M'\<close>
          unfolding \<open>io = ?ioF@[?xyF]\<close>[symmetric]
          by blast

        have "path M q pMinF"
        proof -
          obtain pT'' d'' where "(pMinF@pT'', d'') \<in> m_traversal_paths_with_witness M q RepSets m"
            using \<open>pMinF \<in> tps q\<close> t6[OF \<open>q \<in> fst ` prs\<close>] by blast
          then have "path M q (pMinF@pT'')"
            using m_traversal_paths_with_witness_set[OF t5 t8 \<open>q \<in> nodes M\<close>] 
            by force
          then show ?thesis by auto
        qed
        then have "path M (initial M) (p@pMinF)"
          using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q\<close> by auto
        then have "(p_io (p@pMinF)) \<in> L M"
          unfolding LS.simps by blast
        then have "(p_io p)@(p_io pMinF) \<in> L M"
          by auto
        
  
  
        obtain io' where "p_io pMinF = io @ io'"
          using \<open>io \<in> set (prefixes (p_io pMinF))\<close> unfolding prefixes_set by moura
        
        have " p_io p @ io \<in> L M"
          using \<open>(p_io p)@(p_io pMinF) \<in> L M\<close> 
          unfolding \<open>p_io pMinF = io @ io'\<close>
          unfolding append.assoc[symmetric]
          using language_prefix[of "p_io p @ io" io', of M "initial M"] 
          by blast
        
        then show ?thesis
          using \<open>(p_io p) @ io \<notin> L M\<close> by simp
      next
        case False
        then obtain pMin'' where "pF = pMin @ pMin''"
          using \<open>(pF@[tM]) = pMin @ pMin'\<close>
          by (metis butlast_append butlast_snoc) 
        then have "io = (p_io pMin) @ (p_io pMin'') @ [?xyF]"
          using \<open>io = ?ioF @ [?xyF]\<close> \<open>p_io pF = ?ioF\<close>
          by (metis (no_types, lifting) append_assoc map_append)


        then show ?thesis using that[OF \<open>(pMin,dMin) \<in> m_traversal_paths_with_witness M q RepSets m\<close>, of "(p_io pMin'') @ [?xyF]"] by auto
      qed
    qed
  qed


  


end