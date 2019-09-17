theory Helper_Algorithms
imports R_Distinguishability State_Preamble
begin

value "Pow {1::nat,2}"

(* calculate all pairs of r_distinguishable states *)
fun r_distinguishable_state_pairs :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> 'a) list" where
  "r_distinguishable_state_pairs M = filter (\<lambda> qq . is_r_distinguishable M (fst qq) (snd qq)) (concat (map (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (nodes_from_distinct_paths M)) (nodes_from_distinct_paths M)))"

value "r_distinguishable_state_pairs M_ex_H"
value "r_distinguishable_state_pairs M_ex_9"

lemma r_distinguishable_state_pairs_set : "set (r_distinguishable_state_pairs M) = {(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> is_r_distinguishable M q1 q2}"
  (is "set ?CalcPairs = ?DistPairs")
proof -
  let ?Concs = "(concat (map (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (nodes_from_distinct_paths M)) (nodes_from_distinct_paths M)))"
  let ?Pairs = "{(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M}"
  
  have "set ?Concs = ?Pairs"
    by (metis (no_types) cartesian_product_list.simps cartesian_product_list_set nodes_code)
  moreover have "set ?CalcPairs = {qq . qq \<in> set ?Concs \<and> is_r_distinguishable M (fst qq) (snd qq)}"
    by (metis r_distinguishable_state_pairs.simps set_filter)
  moreover have "?DistPairs = {qq . qq \<in> ?Pairs \<and> is_r_distinguishable M (fst qq) (snd qq)}"
    using prod.collapse by auto 
  ultimately show ?thesis by blast
qed
    
    

(* calculate sets of pairwise r_distinguishable states *)

definition pairwise_r_distinguishable_state_sets :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets M = {S . S \<subseteq> nodes M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> is_r_distinguishable M q1 q2)}"

fun pairwise_r_distinguishable_state_sets_naive :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets_naive M = {S \<in> Pow (set (nodes_from_distinct_paths M)) . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> set (r_distinguishable_state_pairs M)}"
  


lemma pairwise_r_distinguishable_state_sets_code[code] :
  "pairwise_r_distinguishable_state_sets M = pairwise_r_distinguishable_state_sets_naive M"
proof
  show "pairwise_r_distinguishable_state_sets M \<subseteq> pairwise_r_distinguishable_state_sets_naive M"
  proof 
    fix S assume "S \<in> pairwise_r_distinguishable_state_sets M"
    then have *:  "S \<subseteq> nodes M"
          and **: "\<forall>q1\<in>S. \<forall>q2\<in>S. q1 \<noteq> q2 \<longrightarrow> is_r_distinguishable M q1 q2" 
      unfolding pairwise_r_distinguishable_state_sets_def by blast+

    have "S \<in> Pow (set (nodes_from_distinct_paths M))"
      using * by (simp add: nodes_code) 
    moreover have "\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> set (r_distinguishable_state_pairs M)"
      using * ** r_distinguishable_state_pairs_set[of M] by blast 
    ultimately show "S \<in> pairwise_r_distinguishable_state_sets_naive M"
      unfolding pairwise_r_distinguishable_state_sets_naive.simps by blast
  qed
  show "pairwise_r_distinguishable_state_sets_naive M \<subseteq> pairwise_r_distinguishable_state_sets M"
  proof 
    fix S assume "S \<in> pairwise_r_distinguishable_state_sets_naive M"
    then have *:  "S \<in> Pow (set (nodes_from_distinct_paths M))"
          and **: "\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> set (r_distinguishable_state_pairs M)"
      unfolding pairwise_r_distinguishable_state_sets_naive.simps by blast+
    
    have "S \<subseteq> nodes M"
      using * by (simp add: nodes_code) 
    moreover have "\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> is_r_distinguishable M q1 q2"
      using ** r_distinguishable_state_pairs_set[of M] calculation by blast 
    ultimately show "S \<in> pairwise_r_distinguishable_state_sets M"
      unfolding pairwise_r_distinguishable_state_sets_def by blast
  qed  
qed

value "pairwise_r_distinguishable_state_sets M_ex_H"

lemma pairwise_r_distinguishable_state_sets_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> S \<in> pairwise_r_distinguishable_state_sets M . q \<in> S"
proof -
  have "{q} \<in> pairwise_r_distinguishable_state_sets M"
    unfolding pairwise_r_distinguishable_state_sets_def using assms by blast
  then show ?thesis by blast
qed




definition maximal_pairwise_r_distinguishable_state_sets :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "maximal_pairwise_r_distinguishable_state_sets M = {S \<in> pairwise_r_distinguishable_state_sets M . \<not>(\<exists> S' \<in> pairwise_r_distinguishable_state_sets M . S \<subset> S')}"

fun maximal_pairwise_r_distinguishable_state_sets' :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "maximal_pairwise_r_distinguishable_state_sets' M = (let PR = pairwise_r_distinguishable_state_sets M in {S \<in> PR . \<not>(\<exists> S' \<in> PR . S \<subset> S')})"

lemma maximal_pairwise_r_distinguishable_state_sets_code[code] :
  "maximal_pairwise_r_distinguishable_state_sets M = maximal_pairwise_r_distinguishable_state_sets' M"
  unfolding maximal_pairwise_r_distinguishable_state_sets_def maximal_pairwise_r_distinguishable_state_sets'.simps
  by metis

value "maximal_pairwise_r_distinguishable_state_sets M_ex_H"

(* TODO: move *)
lemma maximal_set_cover : 
  fixes X :: "'a set set"
  assumes "finite X" 
  and     "S \<in> X"  
shows "\<exists> S' \<in> X . S \<subseteq> S' \<and> (\<forall> S'' \<in> X . \<not>(S' \<subset> S''))"
proof (rule ccontr)
  assume "\<not> (\<exists>S'\<in>X. S \<subseteq> S' \<and> (\<forall>S''\<in>X. \<not> S' \<subset> S''))"
  then have *: "\<And> T . T \<in> X \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<exists> T' \<in> X . T \<subset> T'"
    by auto

  have "\<And> k . \<exists> ss . (length ss = Suc k) \<and> (hd ss = S) \<and> (\<forall> i < k . ss ! i \<subset> ss ! (Suc i)) \<and> (set ss \<subseteq> X)"
  proof -
    fix k show "\<exists> ss . (length ss = Suc k) \<and> (hd ss = S) \<and> (\<forall> i < k . ss ! i \<subset> ss ! (Suc i)) \<and> (set ss \<subseteq> X)"
    proof (induction k)
      case 0
      have "length [S] = Suc 0 \<and> hd [S] = S \<and> (\<forall> i < 0 . [S] ! i \<subset> [S] ! (Suc i)) \<and> (set [S] \<subseteq> X)" using assms(2) by auto
      then show ?case by blast
    next
      case (Suc k)
      then obtain ss where "length ss = Suc k" 
                       and "hd ss = S" 
                       and "(\<forall>i<k. ss ! i \<subset> ss ! Suc i)" 
                       and "set ss \<subseteq> X"
        by blast
      then have "ss ! k \<in> X"
        by auto
      moreover have "S \<subseteq> (ss ! k)"
      proof -
        have "\<And> i . i < Suc k \<Longrightarrow> S \<subseteq> (ss ! i)"
        proof -
          fix i assume "i < Suc k"
          then show "S \<subseteq> (ss ! i)"
          proof (induction i)
            case 0
            then show ?case using \<open>hd ss = S\<close> \<open>length ss = Suc k\<close>
              by (metis hd_conv_nth list.size(3) nat.distinct(1) order_refl) 
          next
            case (Suc i)
            then have "S \<subseteq> ss ! i" and "i < k" by auto
            then have "ss ! i \<subset> ss ! Suc i" using \<open>(\<forall>i<k. ss ! i \<subset> ss ! Suc i)\<close> by blast
            then show ?case using \<open>S \<subseteq> ss ! i\<close> by auto
          qed
        qed
        then show ?thesis using \<open>length ss = Suc k\<close> by auto 
      qed
      ultimately obtain T' where "T' \<in> X" and "ss ! k \<subset> T'"
        using * by meson 

      let ?ss = "ss@[T']"

      have "length ?ss = Suc (Suc k)" 
        using \<open>length ss = Suc k\<close> by auto
      moreover have "hd ?ss = S" 
        using \<open>hd ss = S\<close> by (metis \<open>length ss = Suc k\<close> hd_append list.size(3) nat.distinct(1)) 
      moreover have "(\<forall>i < Suc k. ?ss ! i \<subset> ?ss ! Suc i)" 
        using \<open>(\<forall>i<k. ss ! i \<subset> ss ! Suc i)\<close> \<open>ss ! k \<subset> T'\<close> 
        by (metis Suc_lessI \<open>length ss = Suc k\<close> diff_Suc_1 less_SucE nth_append nth_append_length) 
      moreover have "set ?ss \<subseteq> X" 
        using \<open>set ss \<subseteq> X\<close> \<open>T' \<in> X\<close> by auto
      ultimately show ?case by blast
    qed
  qed

  then obtain ss where "(length ss = Suc (card X))"
                   and "(hd ss = S)" 
                   and "(\<forall> i < card X . ss ! i \<subset> ss ! (Suc i))" 
                   and "(set ss \<subseteq> X)" 
    by blast
  then have "(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))"
    by auto

  have **: "\<And> i (ss :: 'a set list) . (\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i)) \<Longrightarrow> i < length ss  \<Longrightarrow> \<forall> s \<in> set (take i ss) . s \<subset> ss ! i"
  proof -
    fix i 
    fix ss :: "'a set list"
    assume "i < length ss " and "(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))"
    then show "\<forall> s \<in> set (take i ss) . s \<subset> ss ! i"
    proof (induction i)
      case 0
      then show ?case by auto
    next
      case (Suc i)
      then have "\<forall>s\<in>set (take i ss). s \<subset> ss ! i" by auto
      then have "\<forall>s\<in>set (take i ss). s \<subset> ss ! (Suc i)" using Suc.prems
        by (metis One_nat_def Suc_diff_Suc Suc_lessE diff_zero dual_order.strict_trans nat.inject zero_less_Suc) 
      moreover have "ss ! i \<subset> ss ! (Suc i)" using Suc.prems by auto
      moreover have "(take (Suc i) ss) = (take i ss)@[ss ! i]" using Suc.prems(1)
        by (simp add: take_Suc_conv_app_nth)
      ultimately show ?case by auto 
    qed
  qed

  have "distinct ss"
    using \<open>(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))\<close>
  proof (induction ss rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc a ss)
    from snoc.prems have "\<forall>i<length ss - 1. ss ! i \<subset> ss ! Suc i"
      by (metis Suc_lessD diff_Suc_1 diff_Suc_eq_diff_pred length_append_singleton nth_append zero_less_diff) 
    then have "distinct ss"
      using snoc.IH by auto
    moreover have "a \<notin> set ss"
      using **[OF snoc.prems, of "length (ss @ [a]) - 1"] by auto
    ultimately show ?case by auto
  qed

  then have "card (set ss) = Suc (card X)"
    using \<open>(length ss = Suc (card X))\<close> by (simp add: distinct_card) 
  then show "False"
    using \<open>set ss \<subseteq> X\<close> \<open>finite X\<close> by (metis Suc_n_not_le_n card_mono) 
qed
  
    
  
  


lemma maximal_pairwise_r_distinguishable_state_sets_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> S \<in> maximal_pairwise_r_distinguishable_state_sets M . q \<in> S"
proof -

  have *: "{q} \<in> pairwise_r_distinguishable_state_sets M"
    unfolding pairwise_r_distinguishable_state_sets_def using assms by blast
  have **: "finite (pairwise_r_distinguishable_state_sets M)"
    unfolding pairwise_r_distinguishable_state_sets_def by (simp add: nodes_finite) 

  show ?thesis
    unfolding maximal_pairwise_r_distinguishable_state_sets_def  
    using maximal_set_cover[OF ** *] by auto
qed

  

(* calculate d-reachable states and a fixed assignment of preambles *)
fun d_reachable_states_with_preambles :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> ((Input \<times> Output) list set)) list" where
  "d_reachable_states_with_preambles M = map (\<lambda> qp . (fst qp, the (snd qp))) (filter (\<lambda> qp . snd qp \<noteq> None) (map (\<lambda> q . (q,calculate_preamble_set_naive M q)) (nodes_from_distinct_paths M)))"

lemma d_reachable_states_with_preambles_exhaustiveness :
  assumes "\<exists> P . is_preamble_set M q P"
  and     "observable M"
  and     "q \<in> nodes M"
shows "\<exists> P . is_preamble_set M q P \<and> (q,P) \<in> set (d_reachable_states_with_preambles M)"
proof -
  have "calculate_preamble_set_naive M q \<noteq> None"
    using calculate_preamble_set_naive_exhaustiveness[OF assms(2,1)] by assumption
  then obtain P where "calculate_preamble_set_naive M q = Some P"
    by blast
  then have "(q,Some P) \<in> set ((filter (\<lambda>qp. snd qp \<noteq> None)
               (map (\<lambda>q. (q, calculate_preamble_set_naive M q)) (nodes_from_distinct_paths M))))"
    by (metis (mono_tags, lifting) \<open>calculate_preamble_set_naive M q \<noteq> None\<close> assms(3) filter_list_set image_eqI nodes_code set_map snd_conv)
    
  then have "(q,P) \<in> set (d_reachable_states_with_preambles M)" 
    unfolding d_reachable_states_with_preambles.simps
  proof -
    have "(q, P) = (fst (q, Some P), the (snd (q, Some P)))"
      by auto
    then have "(q, P) \<in> (\<lambda>p. (fst p, the (snd p))) ` set (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_preamble_set_naive M a)) (nodes_from_distinct_paths M)))"
      using \<open>(q, Some P) \<in> set (filter (\<lambda>qp. snd qp \<noteq> None) (map (\<lambda>q. (q, calculate_preamble_set_naive M q)) (nodes_from_distinct_paths M)))\<close> by blast
    then show "(q, P) \<in> set (map (\<lambda>p. (fst p, the (snd p))) (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_preamble_set_naive M a)) (nodes_from_distinct_paths M))))"
      by (metis (no_types) list.set_map)
  qed 
  then show ?thesis
    by (meson \<open>calculate_preamble_set_naive M q = Some P\<close> calculate_preamble_set_naive_soundness) 
qed

lemma d_reachable_states_with_preambles_containment :
  assumes "(q,P) \<in> set (d_reachable_states_with_preambles M)"
  shows "is_preamble_set M q P"
    and "q \<in> nodes M"
proof -

  have "calculate_preamble_set_naive M q = Some P"
    using assms unfolding d_reachable_states_with_preambles.simps
    using image_iff by auto 
  then show "is_preamble_set M q P"
    using calculate_preamble_set_naive_soundness by metis

  show "q \<in> nodes M"
    using assms unfolding d_reachable_states_with_preambles.simps
  proof -
    assume "(q, P) \<in> set (map (\<lambda>qp. (fst qp, the (snd qp))) (filter (\<lambda>qp. snd qp \<noteq> None) (map (\<lambda>q. (q, calculate_preamble_set_naive M q)) (nodes_from_distinct_paths M))))"
    then have "q \<in> set (nodes_from_distinct_paths M)"
      by fastforce
    then show ?thesis
      by (metis nodes_code)
  qed
qed



value "d_reachable_states_with_preambles M_ex_H"



fun d_reachable_states :: "('a,'b) FSM_scheme \<Rightarrow> 'a list" where
  "d_reachable_states M = (map fst (d_reachable_states_with_preambles M))"

lemma d_reachable_states_set : 
  assumes "observable M"
  shows "set (d_reachable_states M) = {q . q \<in> nodes M \<and> (\<exists> P . is_preamble_set M q P)}"
proof -
  have "\<And> q . q \<in> set (d_reachable_states M) \<Longrightarrow> q \<in> {q \<in> nodes M. \<exists>P. is_preamble_set M q P}"
    unfolding d_reachable_states.simps using d_reachable_states_with_preambles_containment[of _ _ M]
    by (metis (no_types, lifting) list_map_source_elem mem_Collect_eq prod.collapse)
  moreover have "\<And> q . q \<in> {q \<in> nodes M. \<exists>P. is_preamble_set M q P} \<Longrightarrow> q \<in> set (d_reachable_states M)"
    unfolding d_reachable_states.simps using d_reachable_states_with_preambles_exhaustiveness[OF _ assms]
  proof -
    fix q :: 'a
    assume "q \<in> {q \<in> nodes M. \<exists>P. is_preamble_set M q P}"
    then have "q \<in> nodes M \<and> Ex (is_preamble_set M q)"
      by blast
    then show "q \<in> set (map fst (d_reachable_states_with_preambles M))"
      by (metis (no_types) \<open>\<And>q. \<lbrakk>\<exists>P. is_preamble_set M q P; q \<in> nodes M\<rbrakk> \<Longrightarrow> \<exists>P. is_preamble_set M q P \<and> (q, P) \<in> set (d_reachable_states_with_preambles M)\<close> fst_conv image_eqI set_map)
  qed
  ultimately show ?thesis by blast
qed

value "d_reachable_states M_ex_H"

(* calculate maximal sets of pairwise r_distinguishable states and their respective subsets of d-reachable states *)
fun maximal_repetition_sets :: "('a,'b) FSM_scheme \<Rightarrow> ('a set \<times> 'a set) set" where
  "maximal_repetition_sets M = image (\<lambda> S . (S, {q \<in> S . q \<in> set (d_reachable_states M)})) (maximal_pairwise_r_distinguishable_state_sets M)"

value "maximal_repetition_sets M_ex_H"
end