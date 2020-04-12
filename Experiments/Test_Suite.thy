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
(* TODO: generalise if necessary (and possible with acceptable effort) *)
fun is_sufficient_for_reduction_testing :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> bool" where
  "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m = 
    ( (initial M,initial_preamble M) \<in> prs 
    \<and> (\<forall> q P . (q,P) \<in> prs \<longrightarrow> (is_preamble P M q) \<and> (tps q) \<noteq> {})
    \<and> (\<forall> q1 q2 A d1 d2 . (A,d1,d2) \<in> atcs (q1,q2) \<longrightarrow> (A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2)
    \<and> (\<exists> RepSets .  
        ((\<forall> q . q \<in> nodes M \<longrightarrow> (\<exists>d \<in> set RepSets. q \<in> fst d))
        \<and> (\<forall> d . d \<in> set RepSets \<longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})))
        \<and> (\<forall> q p d . q \<in> image fst prs \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q RepSets m \<longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst prs \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))))))
    \<and> (\<forall> q1 q2 . q1 \<in> image fst prs \<longrightarrow> q2 \<in> image fst prs \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {} \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[])))
    \<and> (\<forall> q p . q \<in> image fst prs \<longrightarrow> p \<in> tps q \<longrightarrow> path M q p)
  )"



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
      using assms(4,5) unfolding is_sufficient_for_reduction_testing.simps by blast
  qed
  ultimately show ?thesis by auto
qed

    

  


subsection \<open>Pass Relation for Test Suites and Reduction Testing\<close>

definition passes_test_suite :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "passes_test_suite M T M' = False"



end