theory Traversal_Set
imports R_Distinguishability Helper_Algorithms 
begin

section \<open>Traversal Sets for State Counting\<close>

subsection \<open>Calculating Traversal Paths\<close>

definition m_traversal_paths_with_witness_up_to_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (('a\<times>'b\<times>'c\<times>'a) list \<times> ('a set \<times> 'a set)) set" where
  "m_traversal_paths_with_witness_up_to_length M q D m k = paths_up_to_length_or_condition_with_witness M (\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D) k q"

definition m_traversal_paths_with_witness :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) list \<Rightarrow> nat \<Rightarrow> (('a\<times>'b\<times>'c\<times>'a) list \<times> ('a set \<times> 'a set)) set" where
  "m_traversal_paths_with_witness M q D m = m_traversal_paths_with_witness_up_to_length M q D m (Suc (size M * m))"

value "m_traversal_paths_with_witness m_ex_H 1 [({1,3,4},{1,3,4}),({2,3,4},{3,4})] 4 "
value "m_traversal_paths_with_witness m_ex_H 3 [({1,3,4},{1,3,4}),({2,3,4},{3,4})] 4 "
value "m_traversal_paths_with_witness m_ex_H 4 [({1,3,4},{1,3,4}),({2,3,4},{3,4})] 4 "

value "m_traversal_paths_with_witness m_ex_H 4 (maximal_repetition_sets_from_separators_list m_ex_H) 4"







lemma m_traversal_paths_with_witness_up_to_length_max_length :
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> set D . q \<in> fst d"
  and     "\<forall> d \<in> set D . snd d \<subseteq> fst d"
  and     "q \<in> nodes M"
  and     "(p,d) \<in> (m_traversal_paths_with_witness_up_to_length M q D m k)"
shows "length p \<le> Suc ((size M) * m)"
proof (rule ccontr)
  assume "\<not> length p \<le> Suc (FSM.size M * m)"

  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"

  have "path M q []" using assms(3) by auto
  
  have "path M q p"
        and "length p \<le> k"
        and "?f p = Some d"
        and "\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> ?f p' = None"
    using assms(4) unfolding m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def by auto

  let ?p = "take (Suc (m * size M)) p"
  let ?p' = "drop (Suc (m * size M)) p"
  have "path M q ?p"
    using \<open>path M q p\<close> using path_prefix[of M q ?p "drop (Suc (m * size M)) p"]
    by simp
  have "?p' \<noteq> []"
    using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
    by (simp add: mult.commute) 

  have "\<exists> q \<in> nodes M . length (filter (\<lambda>t . t_target t = q) ?p) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>nodes M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) ?p))"
    then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) < Suc m"
      by auto
    then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) ?p)) \<le> (\<Sum>q\<in>nodes M . m)"
      using \<open>\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m\<close> by (meson sum_mono) 
    then have "length ?p \<le> m * (size M)"
      using path_length_sum[OF \<open>path M q ?p\<close>] 
      using fsm_nodes_finite[of M] 
      by (simp add: mult.commute)

    then show "False"
      using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
      by (simp add: mult.commute) 
  qed

  then obtain q where "q \<in> nodes M"
                  and "length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> set D"
                  and "q \<in> fst d"
    using assms(1) by blast
  then have "\<And> t . t_target t = q \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q) ?p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) ?p)"
    using filter_length_weakening[of "\<lambda> t . t_target t = q" "\<lambda> t . t_target t \<in> fst d"] by auto
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
    using \<open>length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m\<close> by auto
  then have "?f ?p \<noteq> None"
    using assms(2)
  proof -
    have "\<forall>p. find p D \<noteq> None \<or> \<not> p d"
      by (metis \<open>d \<in> set D\<close> find_from)
    then show ?thesis
      using \<open>Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take (Suc (m * FSM.size M)) p))\<close> diff_le_self le_trans not_less_eq_eq by blast
  qed 
  then obtain d' where "?f ?p = Some d'"
    by blast

  then have "p = ?p@?p' \<and> ?p' \<noteq> [] \<and> ?f ?p = Some d'"
    using \<open>?p' \<noteq> []\<close> by auto

  then show "False"
    using \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> (?f p') = None\<close>
    by (metis (no_types) \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None\<close> \<open>p = take (Suc (m * FSM.size M)) p @ drop (Suc (m * FSM.size M)) p \<and> drop (Suc (m * FSM.size M)) p \<noteq> [] \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) (take (Suc (m * FSM.size M)) p))) D = Some d'\<close> option.distinct(1))
qed


lemma m_traversal_paths_with_witness_set :
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> set D . q \<in> fst d"
  and     "\<forall> d \<in> set D . snd d \<subseteq> fst d"
  and     "q \<in> nodes M"
  shows "(m_traversal_paths_with_witness M q D m) = {(p,d) | p d . path M q p \<and> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) D = Some d
                                                                  \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)}"
        (is "?MTP = ?P")
proof -
  let ?f = "(\<lambda> p . find (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))) D)"

  have "path M q []"
    using assms(3) by auto

  have "\<And> p . p \<in> ?MTP \<Longrightarrow> p \<in> ?P"
    unfolding m_traversal_paths_with_witness_def m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def
    by force
  moreover have "\<And> p . p \<in> ?P \<Longrightarrow> p \<in> ?MTP"
  proof -
    fix px assume "px \<in> ?P"
    then obtain p x where "px = (p,x)"
          and p1: "path M q p"
          and **: "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) D = Some x"
          and ***:"(\<forall>p' p''.
                     p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow>
                     find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) D = None)"
      using prod.collapse by force

    
    then have "(p,x) \<in> (m_traversal_paths_with_witness_up_to_length M q D m (length p))"
      unfolding m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def
      by force
    then have "length p \<le> Suc (size M * m)"
      using m_traversal_paths_with_witness_up_to_length_max_length[OF assms] by blast
    
    have "(p,x) \<in> ?MTP"
      using \<open>path M q p\<close> \<open>length p \<le> Suc (size M * m)\<close> \<open>?f p = Some x\<close> \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> (?f p') = None\<close>
      unfolding m_traversal_paths_with_witness_def m_traversal_paths_with_witness_up_to_length_def paths_up_to_length_or_condition_with_witness_def
      by force 
    then show "px \<in> ?MTP"
      using \<open>px = (p,x)\<close> by simp
  qed
  ultimately show ?thesis
    by (meson subsetI subset_antisym) 
qed







lemma maximal_repetition_sets_from_separators_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> d \<in> (maximal_repetition_sets_from_separators M) . q \<in> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  using maximal_pairwise_r_distinguishable_state_sets_from_separators_cover[OF assms] by auto

lemma maximal_repetition_sets_from_separators_d_reachable_subset :
  shows "\<And> d . d \<in> (maximal_repetition_sets_from_separators M) \<Longrightarrow> snd d \<subseteq> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  by auto



(* Sufficient conditions for a path to be contained in the m-traversal paths *)
lemma m_traversal_paths_with_witness_set_containment :
  assumes "q \<in> nodes M"
  and     "path M q p"
  and     "d \<in> set repSets"
  and     "Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)"
  and     "\<And> p' p''.
                  p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow>
                  \<not> (\<exists>d\<in>set repSets.
                         Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p'))"
  and     "\<And> q . q\<in>nodes M \<Longrightarrow> \<exists>d\<in>set repSets. q \<in> fst d"
  and     "\<And> d . d\<in>set repSets \<Longrightarrow> snd d \<subseteq> fst d"
shows "\<exists> d' . (p,d') \<in> (m_traversal_paths_with_witness M q repSets m)"
proof -
  have *:"\<forall> q \<in> nodes M . \<exists>d\<in>set repSets. q \<in> fst d"
    using assms(6) by blast
  have **:"\<forall> d \<in> set repSets . snd d \<subseteq> fst d"
    using assms(7) by blast

  obtain d' where "find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) repSets = Some d'"
    using assms(3,4) find_None_iff[of "(\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))" repSets] by auto
  moreover have "(\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> find (\<lambda>d. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')) repSets = None)"
    using assms(5) find_None_iff[of _ repSets] by force
  

  ultimately show ?thesis
    unfolding m_traversal_paths_with_witness_set[of M repSets q m, OF * ** assms(1)]
    using assms(2) by blast
qed



end

