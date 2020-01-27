theory Helper_Algorithms
imports R_Distinguishability State_Separator State_Preamble
begin

(* wrong, uses ''directed'' separators *)
definition r_distinguishable_state_pairs_with_separators :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) \<times> (('a \<times> 'a) + 'a,'b) FSM_scheme) set" where
  "r_distinguishable_state_pairs_with_separators M = {((q1,q2),Sep) | q1 q2 Sep . q1 \<in> nodes M 
                                                                                \<and> q2 \<in> nodes M 
                                                                                \<and> q1 \<noteq> q2 
                                                                                \<and> (((q1,q2) \<in> node_order M \<and> calculate_state_separator_from_s_states M q1 q2 = Some Sep)
                                                                                  \<or> ((q2,q1) \<in> node_order M \<and> calculate_state_separator_from_s_states M q2 q1 = Some Sep)) }"

lemma r_distinguishable_state_pairs_with_separators_same_pair_same_separator :
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "((q1,q2),A') \<in> r_distinguishable_state_pairs_with_separators M"
shows "A = A'"
  using assms unfolding r_distinguishable_state_pairs_with_separators_def
  using node_order_antisym by force 


lemma r_distinguishable_state_pairs_with_separators_sym_pair_same_separator :
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "((q2,q1),A') \<in> r_distinguishable_state_pairs_with_separators M"
shows "A = A'"
  using assms unfolding r_distinguishable_state_pairs_with_separators_def
  using node_order_antisym by force 



definition r_distinguishable_state_pairs_with_separators_naive :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) \<times> (('a \<times> 'a) + 'a,'b) FSM_scheme) list" where
  "r_distinguishable_state_pairs_with_separators_naive M =
    (let nonSymNodes = non_sym_dist_pairs (nodes_from_distinct_paths M);
         nonSymSeps = map (\<lambda> (q1,q2) . ((q1,q2),calculate_state_separator_from_s_states M q1 q2)) nonSymNodes;
         filtered = map (\<lambda> ((q1,q2),A) . ((q1,q2), the A)) (filter (\<lambda> ((q1,q2),A) . A \<noteq> None) nonSymSeps)
      in
         concat (map (\<lambda> ((q1,q2),A) . [((q1,q2),A),((q2,q1),A)]) filtered))"
        

value "r_distinguishable_state_pairs_with_separators_naive M_ex_H"

lemma r_distinguishable_state_pairs_with_separators_code[code] :
  "r_distinguishable_state_pairs_with_separators M = set (r_distinguishable_state_pairs_with_separators_naive M)"
proof -
  have "\<And> q1 q2 A . ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<Longrightarrow> ((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M)"
  proof -
    fix q1 q2 A assume "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
    then have "q1 \<in> nodes M" and "q2 \<in> nodes M" and "q1 \<noteq> q2" and *: "((q1,q2) \<in> node_order M \<and> calculate_state_separator_from_s_states M q1 q2 = Some A) \<or> ((q2,q1) \<in> node_order M \<and> calculate_state_separator_from_s_states M q2 q1 = Some A)"
      unfolding r_distinguishable_state_pairs_with_separators_def by blast+

    let ?nonSymNodes = "non_sym_dist_pairs (nodes_from_distinct_paths M)"
    let ?nonSymSeps = "map (\<lambda> (q1,q2) . ((q1,q2),calculate_state_separator_from_s_states M q1 q2)) ?nonSymNodes"
    let ?filtered = "map (\<lambda> ((q1,q2),A) . ((q1,q2), the A)) (filter (\<lambda> ((q1,q2),A) . A \<noteq> None) ?nonSymSeps)"

    have "q1 \<in> set (nodes_from_distinct_paths M)"
      using \<open>q1 \<in> nodes M\<close> nodes_code by metis
    moreover have "q2 \<in> set (nodes_from_distinct_paths M)"
      using \<open>q2 \<in> nodes M\<close> nodes_code by metis
    ultimately have "(q1,q2) \<in> set ?nonSymNodes \<or> (q2,q1) \<in> set ?nonSymNodes"
      using non_sym_dist_pairs_elems[OF _ _ \<open>q1 \<noteq> q2\<close>] by blast
    then have "(q1,q2) \<in> node_order M \<or> (q2,q1) \<in> node_order M"
      unfolding node_order_def 
      unfolding linear_order_from_list_position_set by blast
    
    have "\<not> ((q1,q2) \<in> node_order M \<and> (q2,q1) \<in> node_order M)"
      using node_order_antisym[of q1 q2 M] \<open>q1 \<noteq> q2\<close> by auto
    then have "(q1,q2) \<in> node_order M \<Longrightarrow> (q2,q1) \<notin> node_order M"
         and  "(q2,q1) \<in> node_order M \<Longrightarrow> (q1,q2) \<notin> node_order M"
      by auto

    have scheme: "\<And> s1 s2 S . (s1,s2) \<in> node_order M \<Longrightarrow> s1 \<noteq> s2 \<Longrightarrow> calculate_state_separator_from_s_states M s1 s2 = Some S \<Longrightarrow> ((s1,s2),S) \<in> set ?filtered"
    proof -
      fix s1 s2 S assume "(s1,s2) \<in> node_order M" and "s1 \<noteq> s2" and "calculate_state_separator_from_s_states M s1 s2 = Some S"
      then have "((s1,s2), Some S) \<in> set ?nonSymSeps"
        unfolding node_order_def 
      unfolding linear_order_from_list_position_set by force
      then have *: "((s1,s2), Some S) \<in> set (filter (\<lambda> ((q1,q2),A) . A \<noteq> None) ?nonSymSeps)"
        by force
      
      have **: "(\<lambda>((q1, q2), A). ((q1, q2), the A)) ((s1,s2),Some S) = ((s1,s2),S)"
        by simp

      have scheme: "\<And> x xs f y . x \<in> set xs \<Longrightarrow> (f x) = y \<Longrightarrow> y \<in> set (map f xs)" by auto

      show "((s1,s2),S) \<in> set ?filtered"
        using scheme[OF *, of "(\<lambda>((q1, q2), A). ((q1, q2), the A))", OF **] by assumption
    qed

    

    have "(q1,q2) \<in> node_order M \<Longrightarrow> ((q1,q2),A) \<in> set ?filtered"
      using * \<open>(q1,q2) \<in> node_order M \<Longrightarrow> (q2,q1) \<notin> node_order M\<close> 
      using scheme by blast

    moreover have "(q2,q1) \<in> node_order M \<Longrightarrow> ((q2,q1),A) \<in> set ?filtered"
      using * \<open>(q2,q1) \<in> node_order M \<Longrightarrow> (q1,q2) \<notin> node_order M\<close> 
      using scheme by blast


    ultimately consider (a) "((q1,q2),A) \<in> set ?filtered" |
                        (b) "((q2,q1),A) \<in> set ?filtered"
      using \<open>(q1,q2) \<in> node_order M \<or> (q2,q1) \<in> node_order M\<close> by blast
    
    
        
    then show "((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M)"
    proof (cases)
      case a

      have scheme1: "\<And> x xs f y . x \<in> set xs \<Longrightarrow> (f x) = y \<Longrightarrow> y \<in> set (map f xs)" by auto
      have scheme2: "\<And> xs xss . xs \<in> set xss \<Longrightarrow> set xs \<subseteq> set (concat xss)" by auto

      have *: "[((q1,q2),A),((q2,q1),A)] \<in> set (map (\<lambda> ((q1,q2),A) . [((q1,q2),A),((q2,q1),A)]) ?filtered)"
        using scheme1[OF a, of "(\<lambda>((q1, q2), A). [((q1, q2), A), ((q2, q1), A)])" "[((q1, q2), A), ((q2, q1), A)]"] by force
      have "set ([((q1,q2),A),((q2,q1),A)]) \<subseteq> set (r_distinguishable_state_pairs_with_separators_naive M)"
        using scheme2[OF *]
        unfolding r_distinguishable_state_pairs_with_separators_naive_def Let_def  by assumption
      then show ?thesis by auto
    next
      case b

      have scheme1: "\<And> x xs f y . x \<in> set xs \<Longrightarrow> (f x) = y \<Longrightarrow> y \<in> set (map f xs)" by auto
      have scheme2: "\<And> xs xss . xs \<in> set xss \<Longrightarrow> set xs \<subseteq> set (concat xss)" by auto

      have *: "[((q2,q1),A),((q1,q2),A)] \<in> set (map (\<lambda> ((q1,q2),A) . [((q1,q2),A),((q2,q1),A)]) ?filtered)"
        using scheme1[OF b, of "(\<lambda>((q1, q2), A). [((q1, q2), A), ((q2, q1), A)])" "[((q2, q1), A), ((q1, q2), A)]"] by force
      have "set ([((q2,q1),A),((q1,q2),A)]) \<subseteq> set (r_distinguishable_state_pairs_with_separators_naive M)"
        using scheme2[OF *]
        unfolding r_distinguishable_state_pairs_with_separators_naive_def Let_def  by assumption
      then show ?thesis by auto
    qed
  qed

  moreover have "\<And> q1 q2 A . ((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M) \<Longrightarrow> ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  proof -
    fix q1 q2 A assume "((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M)"

    let ?f1 = "(\<lambda> ((q1,q2),A) . [((q1,q2),A),((q2,q1),A)])"
    let ?f2 = "(\<lambda> ((q1,q2),A) . ((q1,q2), the A))"
    let ?f3 = "(\<lambda> ((q1,q2),A) . A \<noteq> None)"
    let ?f4 = "(\<lambda> (q1,q2) . ((q1,q2),calculate_state_separator_from_s_states M q1 q2))"

    have "((q1,q2),A) \<in> set (concat (map ?f1 (map ?f2 (filter ?f3 (map ?f4 (non_sym_dist_pairs (nodes_from_distinct_paths M)))))))"
      using \<open>((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M)\<close>
      unfolding r_distinguishable_state_pairs_with_separators_naive_def Let_def by assumption

    have scheme1: "\<And> x xs f1 f2 f3 f4 . x \<in> set (concat (map f1 (map f2 (filter f3 (map f4 xs))))) \<Longrightarrow> \<exists> y \<in> set xs . x \<in> set (f1 (f2 (f4 y))) \<and> f3 (f4 y)" by auto

    obtain qq where "qq \<in> set (non_sym_dist_pairs (nodes_from_distinct_paths M))"
              and   "((q1,q2),A) \<in> set (?f1 (?f2 (?f4 qq)))"
              and   "?f3 (?f4 qq)"
      using scheme1[OF \<open>((q1,q2),A) \<in> set (concat (map ?f1 (map ?f2 (filter ?f3 (map ?f4 (non_sym_dist_pairs (nodes_from_distinct_paths M)))))))\<close>] by force

    obtain q1' q2' where "qq = (q1',q2')"
      using prod.collapse by metis

    then have "(q1',q2') \<in> set (non_sym_dist_pairs (nodes_from_distinct_paths M))"
      using \<open>qq \<in> set (non_sym_dist_pairs (nodes_from_distinct_paths M))\<close> by auto
    then have "q1' \<in> nodes M" and "q2' \<in> nodes M" and "q1' \<noteq> q2'"
      using Util.non_sym_dist_pairs_elems_distinct[of q1' q2' "nodes_from_distinct_paths M"] unfolding nodes_code by blast+

    have "(q1',q2') \<in> node_order M"
      using \<open>(q1',q2') \<in> set (non_sym_dist_pairs (nodes_from_distinct_paths M))\<close> 
      unfolding node_order_def linear_order_from_list_position_set by blast
    

    have "\<And> qq . fst (?f2 (?f4 qq)) = qq" by auto
    then have "fst (?f2 (?f4 qq)) = (q1',q2')" 
      using \<open>qq = (q1',q2')\<close> by auto

    have *: "\<And> s1 s2 A s1' s2' A' . ((s1',s2'),A') \<in> set (?f1 ((s1,s2),A)) \<Longrightarrow> A = A' \<and> ((s1',s2') = (s1,s2) \<or> (s1',s2') = (s2,s1))" by auto
    have "A = snd (?f2 (?f4 (q1',q2')))" and "(q1, q2) = (q1', q2') \<or> (q1, q2) = (q2', q1')"
      using *[of q1 q2 A q1' q2' "snd (?f2 (?f4 (q1',q2')))"]
      using \<open>((q1,q2),A) \<in> set (?f1 (?f2 (?f4 qq)))\<close> 
      unfolding \<open>qq = (q1',q2')\<close> by simp+

    have "Some A = snd (?f4 (q1',q2'))"
      using \<open>A = snd (?f2 (?f4 (q1',q2')))\<close> 
      using \<open>?f3 (?f4 qq)\<close> \<open>qq = (q1', q2')\<close> by auto    
      
    
    consider (a) "qq = (q1, q2)" |
                  (b) "qq = (q2, q1)"
      using \<open>(q1, q2) = (q1', q2') \<or> (q1, q2) = (q2', q1')\<close> \<open>qq = (q1',q2')\<close> by auto
    then show "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M" 
    proof cases
      case a
      then have "q1' = q1" and "q2' = q2" using \<open>qq = (q1', q2')\<close> by auto

      have "calculate_state_separator_from_s_states M q1' q2' = Some A"
        using \<open>Some A = snd (?f4 (q1',q2'))\<close> a by auto 
      
      show ?thesis unfolding r_distinguishable_state_pairs_with_separators_def
        using \<open>q1' \<in> nodes M\<close> \<open>q2' \<in> nodes M\<close> \<open>q1' \<noteq> q2'\<close> \<open>(q1',q2') \<in> node_order M\<close> \<open>calculate_state_separator_from_s_states M q1' q2' = Some A\<close> 
        unfolding \<open>q1' = q1\<close> \<open>q2' = q2\<close> by blast
    next
      case b
      then have "q1' = q2" and "q2' = q1" using \<open>qq = (q1', q2')\<close> by auto

      have "calculate_state_separator_from_s_states M q1' q2' = Some A"
        using \<open>Some A = snd (?f4 (q1',q2'))\<close> b by auto 
      
      show ?thesis unfolding r_distinguishable_state_pairs_with_separators_def
        using \<open>q1' \<in> nodes M\<close> \<open>q2' \<in> nodes M\<close> \<open>q1' \<noteq> q2'\<close> \<open>(q1',q2') \<in> node_order M\<close> \<open>calculate_state_separator_from_s_states M q1' q2' = Some A\<close> 
        unfolding \<open>q1' = q2\<close> \<open>q2' = q1\<close> by blast
    qed
  qed
    
  ultimately show ?thesis by auto
qed

    




(* TODO: inefficient*)
(* TODO: maybe constrain to ('a::ord,'b) FSM_scheme and filter for q1 < q2 *)
definition r_distinguishable_state_pairs_with_separators_naive_old :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) \<times> (('a \<times> 'a) + 'a,'b) FSM_scheme) list" where
  "r_distinguishable_state_pairs_with_separators_naive_old M = 
    map 
      (\<lambda> qqp . (fst qqp, the (snd qqp))) 
      (filter 
        (\<lambda> qqp . snd qqp \<noteq> None) 
        (map 
          (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
          (concat 
            (map 
              (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
              (nodes_from_distinct_paths M)))))"




end (*

lemma concat_pair_set_f :
  "set (concat (map (\<lambda>x. map (Pair x) (f x)) xs)) = {xy . fst xy \<in> set xs \<and> snd xy \<in> set (f (fst xy))}"
  by auto

lemma r_distinguishable_state_pairs_with_separators_code[code] :
  fixes M :: "('a::ord,'b) FSM_scheme"
  shows
  "r_distinguishable_state_pairs_with_separators M = set (r_distinguishable_state_pairs_with_separators_naive M)"
proof -

  have "{(q1,q2) | q1 q2 . q1 \<in> set (nodes_from_distinct_paths M) \<and> q2 \<in> set (nodes_from_distinct_paths M) \<and> q1 \<noteq> q2} = 
        {xy. fst xy \<in> set (nodes_from_distinct_paths M) \<and> snd xy \<in> set (filter ((\<noteq>) (fst xy)) (nodes_from_distinct_paths M))} "
    by force
  then have *: "set (concat 
            (map 
              (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
              (nodes_from_distinct_paths M)))
         = {(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2}"
    using concat_pair_set_f[of "\<lambda>q1 . filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)" "nodes_from_distinct_paths M"]
    using nodes_code[of M] by metis
  moreover have "set (map 
                  (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                  (concat 
                    (map 
                      (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                      (nodes_from_distinct_paths M)))) =
                 image (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) (set (concat 
                    (map 
                      (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                      (nodes_from_distinct_paths M))))"
    by auto
  moreover have "image (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) {(q1,q2) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2}
                   = {((q1,q2),calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2}"
    by auto
  ultimately have "set (map 
                  (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                  (concat 
                    (map 
                      (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                      (nodes_from_distinct_paths M)))) =
            {((q1,q2),calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2}" 
    
    by presburger
  then have "{qqp \<in> set (map 
                  (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                  (concat 
                    (map 
                      (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                      (nodes_from_distinct_paths M)))) . snd qqp \<noteq> None}
                 = {((q1,q2),calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)) \<noteq> None}"
    by auto
  moreover have "set (filter 
                    (\<lambda> qqp . snd qqp \<noteq> None) 
                    (map 
                      (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                      (concat 
                        (map 
                          (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                          (nodes_from_distinct_paths M))))) =
                 {qqp \<in> set (map 
                  (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                  (concat 
                    (map 
                      (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                      (nodes_from_distinct_paths M)))) . snd qqp \<noteq> None}"
    by (metis (full_types) set_filter)
  ultimately have "set (filter 
                    (\<lambda> qqp . snd qqp \<noteq> None) 
                    (map 
                      (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                      (concat 
                        (map 
                          (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                          (nodes_from_distinct_paths M))))) = 
            {((q1,q2),calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)) \<noteq> None}"
    by presburger
  moreover have "image (\<lambda> qqp . (fst qqp, the (snd qqp))) {((q1,q2),calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)) \<noteq> None}
                  = {((q1,q2),the (calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)) \<noteq> None}"
    by force
  moreover have "set (r_distinguishable_state_pairs_with_separators_naive M) =
                 image (\<lambda> qqp . (fst qqp, the (snd qqp))) (set (filter 
                    (\<lambda> qqp . snd qqp \<noteq> None) 
                    (map 
                      (\<lambda> qq . (qq, calculate_state_separator_from_s_states M (fst qq) (snd qq))) 
                      (concat 
                        (map 
                          (\<lambda> q1 . map (\<lambda> q2 . (q1,q2)) (filter (\<lambda> q2 . q1 \<noteq> q2) (nodes_from_distinct_paths M)))  
                          (nodes_from_distinct_paths M))))))"
    unfolding r_distinguishable_state_pairs_with_separators_naive_def
    by (meson list.set_map) 
    
  ultimately have "set (r_distinguishable_state_pairs_with_separators_naive M) =
              {((q1,q2),the (calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)))) | q1 q2 . q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M (fst (q1,q2)) (snd (q1,q2)) \<noteq> None}"
    unfolding r_distinguishable_state_pairs_with_separators_naive_def 
    by presburger

  then show ?thesis
    unfolding r_distinguishable_state_pairs_with_separators_def by auto
qed

  
lemma r_distinguishable_state_pairs_with_separators_naive_set :
  fixes M :: "('a::ord,'b) FSM_scheme"
shows "set (r_distinguishable_state_pairs_with_separators_naive M) = {((q1, q2), Sep) |q1 q2 Sep.  q1 \<in> nodes M \<and> q2 \<in> nodes M \<and> q1 \<noteq> q2 \<and> calculate_state_separator_from_s_states M q1 q2 = Some Sep}"
  using r_distinguishable_state_pairs_with_separators_code[of M]
  unfolding r_distinguishable_state_pairs_with_separators_def by simp



(* calculate all pairs of r_distinguishable states *)
(*
definition r_distinguishable_state_pairs :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> 'a) list" where
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
    by (metis r_distinguishable_state_pairs_def set_filter)
  moreover have "?DistPairs = {qq . qq \<in> ?Pairs \<and> is_r_distinguishable M (fst qq) (snd qq)}"
    using prod.collapse by auto 
  ultimately show ?thesis by blast
qed
*)   
    



definition pairwise_r_distinguishable_state_sets_from_separators :: "('a,'b) FSM_scheme \<Rightarrow> 'a set list" where
  "pairwise_r_distinguishable_state_sets_from_separators M = (let RDS = r_distinguishable_state_pairs_with_separators M 
                                                              in filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst RDS) 
                                                                     (map set (pow_list (nodes_from_distinct_paths M))))"

lemma pairwise_r_distinguishable_state_sets_from_separators_set :
  "set (pairwise_r_distinguishable_state_sets_from_separators M) = {S . S \<subseteq> nodes M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M))}"
proof -
  have "\<And> S . S \<in> set (pairwise_r_distinguishable_state_sets_from_separators M) \<Longrightarrow> S \<in> {S . S \<subseteq> nodes M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M))}"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def
    using pow_list_set[of "nodes_from_distinct_paths M"]
    by (metis (no_types, lifting) PowD filter_is_subset filter_list_set_not_contained mem_Collect_eq nodes_code subsetCE)
  moreover have "\<And> S . S \<in> {S . S \<subseteq> nodes M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M))} \<Longrightarrow> S \<in> set (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def
    using pow_list_set[of "nodes_from_distinct_paths M"]
    by (simp add: nodes_code)
  ultimately show ?thesis by blast
qed
   
(* old definitions
definition pairwise_r_distinguishable_state_sets_from_separators :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets_from_separators M = {S . S \<subseteq> nodes M \<and> (\<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> image fst (r_distinguishable_state_pairs_with_separators M))}"

definition pairwise_r_distinguishable_state_sets_from_separators_naive :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "pairwise_r_distinguishable_state_sets_from_separators_naive M = (let PR = image fst (r_distinguishable_state_pairs_with_separators M) in {S \<in> Pow (set (nodes_from_distinct_paths M)) . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> PR})"

lemma pairwise_r_distinguishable_state_sets_from_separators_code[code] :
  "pairwise_r_distinguishable_state_sets_from_separators M = pairwise_r_distinguishable_state_sets_from_separators_naive M"
  unfolding pairwise_r_distinguishable_state_sets_from_separators_def pairwise_r_distinguishable_state_sets_from_separators_naive_def
  by (metis (mono_tags, lifting) Collect_cong Pow_iff nodes_code)
*)

lemma pairwise_r_distinguishable_state_sets_from_separators_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> S \<in> set (pairwise_r_distinguishable_state_sets_from_separators M) . q \<in> S"
proof -
  have "{q} \<in> set (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_set using assms by blast
  then show ?thesis by blast
qed


definition maximal_pairwise_r_distinguishable_state_sets_from_separators :: "('a,'b) FSM_scheme \<Rightarrow> 'a set list" where
  "maximal_pairwise_r_distinguishable_state_sets_from_separators M = (let PR = (pairwise_r_distinguishable_state_sets_from_separators M) in filter (\<lambda> S . \<not>(\<exists> S' \<in> set PR . S \<subset> S')) PR)"

lemma maximal_pairwise_r_distinguishable_state_sets_from_separators_set : 
  "set (maximal_pairwise_r_distinguishable_state_sets_from_separators M) = 
    {S \<in> {S. S \<subseteq> nodes M \<and> (\<forall>q1\<in>S. \<forall>q2\<in>S. q1 \<noteq> q2 \<longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M)} .
     \<not> Bex {S. S \<subseteq> nodes M \<and>
                (\<forall>q1\<in>S. \<forall>q2\<in>S. q1 \<noteq> q2 \<longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M)}
         ((\<subset>) S)}"
  unfolding maximal_pairwise_r_distinguishable_state_sets_from_separators_def
  unfolding Let_def 
  unfolding pairwise_r_distinguishable_state_sets_from_separators_set
  using pairwise_r_distinguishable_state_sets_from_separators_set by force
  

end (*




definition maximal_pairwise_r_distinguishable_state_sets_from_separators :: "('a,'b) FSM_scheme \<Rightarrow> 'a set set" where
  "maximal_pairwise_r_distinguishable_state_sets_from_separators M = (let PR = (pairwise_r_distinguishable_state_sets_from_separators M) in {S \<in> PR . \<not>(\<exists> S' \<in> PR . S \<subset> S')})"

value "r_distinguishable_state_pairs_with_separators M_ex_H"
value "pairwise_r_distinguishable_state_sets_from_separators M_ex_H"
value "maximal_pairwise_r_distinguishable_state_sets_from_separators M_ex_H"

value "r_distinguishable_state_pairs_with_separators M_ex_9"
value "pairwise_r_distinguishable_state_sets_from_separators M_ex_9"
value "maximal_pairwise_r_distinguishable_state_sets_from_separators M_ex_9"


lemma maximal_pairwise_r_distinguishable_state_sets_from_separators_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> S \<in> maximal_pairwise_r_distinguishable_state_sets_from_separators M . q \<in> S"
proof -

  have *: "{q} \<in> pairwise_r_distinguishable_state_sets_from_separators M"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def using assms by blast
  have **: "finite (pairwise_r_distinguishable_state_sets_from_separators M)"
    unfolding pairwise_r_distinguishable_state_sets_from_separators_def by (simp add: nodes_finite) 

  have "maximal_pairwise_r_distinguishable_state_sets_from_separators M = 
        {S \<in> pairwise_r_distinguishable_state_sets_from_separators M . \<not>(\<exists> S' \<in> pairwise_r_distinguishable_state_sets_from_separators M . S \<subset> S')}"
    unfolding maximal_pairwise_r_distinguishable_state_sets_from_separators_def by metis 
  then have "maximal_pairwise_r_distinguishable_state_sets_from_separators M = 
        {S \<in> pairwise_r_distinguishable_state_sets_from_separators M . (\<forall> S' \<in> pairwise_r_distinguishable_state_sets_from_separators M . \<not> S \<subset> S')}"
    by blast 
  moreover have "\<exists> S \<in> {S \<in> pairwise_r_distinguishable_state_sets_from_separators M . (\<forall> S' \<in> pairwise_r_distinguishable_state_sets_from_separators M . \<not> S \<subset> S')} . q \<in> S"
    using maximal_set_cover[OF ** *] by blast
  ultimately show ?thesis by blast 
qed





(* calculate d-reachable states and a fixed assignment of preambles *)
definition d_reachable_states_with_preambles :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> ('a,'b) FSM_scheme) list" where
  "d_reachable_states_with_preambles M = map (\<lambda> qp . (fst qp, the (snd qp))) (filter (\<lambda> qp . snd qp \<noteq> None) (map (\<lambda> q . (q, calculate_state_preamble_from_d_states M q)) (nodes_from_distinct_paths M)))"

lemma d_reachable_states_with_preambles_exhaustiveness :
  assumes "\<exists> P . is_preamble P M q"
  and     "observable M"
  and     "q \<in> nodes M"
shows "\<exists> P . is_preamble P M q \<and> (q,P) \<in> set (d_reachable_states_with_preambles M)"
proof -
  have "calculate_state_preamble_from_d_states M q \<noteq> None"
    using calculate_state_preamble_from_d_states_exhaustiveness[OF assms(1)] by assumption
  then obtain P where "calculate_state_preamble_from_d_states M q = Some P"
    by blast
  then have "(q,Some P) \<in> set ((filter (\<lambda>qp. snd qp \<noteq> None)
               (map (\<lambda>q. (q, calculate_state_preamble_from_d_states M q)) (nodes_from_distinct_paths M))))"
    by (metis (mono_tags, lifting) \<open>calculate_state_preamble_from_d_states M q \<noteq> None\<close> assms(3) filter_list_set image_eqI nodes_code set_map snd_conv)
    
  then have "(q,P) \<in> set (d_reachable_states_with_preambles M)" 
    unfolding d_reachable_states_with_preambles_def 
  proof -
    have "(q, P) = (fst (q, Some P), the (snd (q, Some P)))"
      by auto
    then have "(q, P) \<in> (\<lambda>p. (fst p, the (snd p))) ` set (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_state_preamble_from_d_states M a)) (nodes_from_distinct_paths M)))"
      using \<open>(q, Some P) \<in> set (filter (\<lambda>qp. snd qp \<noteq> None) (map (\<lambda>q. (q, calculate_state_preamble_from_d_states M q)) (nodes_from_distinct_paths M)))\<close> by blast      
    then show "(q, P) \<in> set (map (\<lambda>p. (fst p, the (snd p))) (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_state_preamble_from_d_states M a)) (nodes_from_distinct_paths M))))"
      by (metis (no_types) list.set_map)
  qed 
  then show ?thesis
    by (meson \<open>calculate_state_preamble_from_d_states M q = Some P\<close> assms(2) calculate_state_preamble_from_d_states_soundness)     
qed



lemma d_reachable_states_with_preambles_containment :
  assumes "(q,P) \<in> set (d_reachable_states_with_preambles M)"
  and     "observable M"
  shows "is_preamble P M q"
    and "q \<in> nodes M"
proof -

  have "calculate_state_preamble_from_d_states M q = Some P"
    using assms unfolding d_reachable_states_with_preambles_def
    using image_iff by auto 
  then show "is_preamble P M q"
    using calculate_state_preamble_from_d_states_soundness assms(2) by metis

  show "q \<in> nodes M"
    using assms unfolding d_reachable_states_with_preambles_def nodes_code
    using filter_map_elem fst_conv list_map_source_elem by force
qed



value "d_reachable_states_with_preambles M_ex_H"



















(* calculate d-reachable states and a fixed assignment of preambles *)
definition d_reachable_states_with_preamble_sets :: "('a,'b) FSM_scheme \<Rightarrow> ('a \<times> ((Input \<times> Output) list set)) list" where
  "d_reachable_states_with_preamble_sets M = map (\<lambda> qp . (fst qp, the (snd qp))) (filter (\<lambda> qp . snd qp \<noteq> None) (map (\<lambda> q . (q, calculate_preamble_set_from_d_states M q)) (nodes_from_distinct_paths M)))"

lemma d_reachable_states_with_preamble_sets_exhaustiveness :
  assumes "\<exists> P . is_preamble_set M q P"
  and     "observable M"
  and     "q \<in> nodes M"
shows "\<exists> P . is_preamble_set M q P \<and> (q,P) \<in> set (d_reachable_states_with_preamble_sets M)"
proof -
  have "calculate_preamble_set_from_d_states M q \<noteq> None"
    using calculate_preamble_set_from_d_states_exhaustiveness[OF assms(1,2)] by assumption
  then obtain P where "calculate_preamble_set_from_d_states M q = Some P"
    by blast
  then have "(q,Some P) \<in> set ((filter (\<lambda>qp. snd qp \<noteq> None)
               (map (\<lambda>q. (q, calculate_preamble_set_from_d_states M q)) (nodes_from_distinct_paths M))))"
    by (metis (mono_tags, lifting) \<open>calculate_preamble_set_from_d_states M q \<noteq> None\<close> assms(3) filter_list_set image_eqI nodes_code set_map snd_conv)
    
  then have "(q,P) \<in> set (d_reachable_states_with_preamble_sets M)" 
    unfolding d_reachable_states_with_preamble_sets_def
  proof -
    have "(q, P) = (fst (q, Some P), the (snd (q, Some P)))"
      by auto
    then have "(q, P) \<in> (\<lambda>p. (fst p, the (snd p))) ` set (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_preamble_set_from_d_states M a)) (nodes_from_distinct_paths M)))"
      using \<open>(q, Some P) \<in> set (filter (\<lambda>qp. snd qp \<noteq> None) (map (\<lambda>q. (q, calculate_preamble_set_from_d_states M q)) (nodes_from_distinct_paths M)))\<close> by blast
    then show "(q, P) \<in> set (map (\<lambda>p. (fst p, the (snd p))) (filter (\<lambda>p. snd p \<noteq> None) (map (\<lambda>a. (a, calculate_preamble_set_from_d_states M a)) (nodes_from_distinct_paths M))))"
      by (metis (no_types) list.set_map)
  qed 
  then show ?thesis
    by (meson \<open>calculate_preamble_set_from_d_states M q = Some P\<close> assms(2) calculate_preamble_set_from_d_states_soundness)     
qed

lemma d_reachable_states_with_preamble_sets_containment :
  assumes "(q,P) \<in> set (d_reachable_states_with_preamble_sets M)"
  and     "observable M"
  shows "is_preamble_set M q P"
    and "q \<in> nodes M"
proof -

  have "calculate_preamble_set_from_d_states M q = Some P"
    using assms unfolding d_reachable_states_with_preamble_sets_def
    using image_iff by auto 
  then show "is_preamble_set M q P"
    using calculate_preamble_set_from_d_states_soundness assms(2) by metis

  show "q \<in> nodes M"
    using assms unfolding d_reachable_states_with_preamble_sets_def
  proof -
    assume "(q, P) \<in> set (map (\<lambda>qp. (fst qp, the (snd qp))) (filter (\<lambda>qp. snd qp \<noteq> None) (map (\<lambda>q. (q, calculate_preamble_set_from_d_states M q)) (nodes_from_distinct_paths M))))"
    then have "q \<in> set (nodes_from_distinct_paths M)"
      by fastforce
    then show ?thesis
      by (metis nodes_code)
  qed
qed



value "d_reachable_states_with_preamble_sets M_ex_H"






fun d_reachable_states :: "('a,'b) FSM_scheme \<Rightarrow> 'a list" where
  "d_reachable_states M = (map fst (d_reachable_states_with_preambles M))"

lemma d_reachable_states_set : 
  assumes "observable M"
  shows "set (d_reachable_states M) = {q . q \<in> nodes M \<and> (\<exists> P . is_preamble P M q)}"
proof -
  have "\<And> q . q \<in> set (d_reachable_states M) \<Longrightarrow> q \<in> {q \<in> nodes M. \<exists>P. is_preamble P M q}"
    unfolding d_reachable_states.simps using d_reachable_states_with_preambles_containment[of _ _ M]
    by (metis (no_types, lifting) assms list_map_source_elem mem_Collect_eq prod.collapse)
    
  moreover have "\<And> q . q \<in> {q \<in> nodes M. \<exists>P. is_preamble P M q} \<Longrightarrow> q \<in> set (d_reachable_states M)"
    unfolding d_reachable_states.simps using d_reachable_states_with_preambles_exhaustiveness[OF _ assms]
  proof -
    fix q :: 'a
    assume "q \<in> {q \<in> nodes M. \<exists>P. is_preamble P M q}"
    then have "q \<in> nodes M \<and> (\<exists>P. (is_preamble P M q))"
      by blast
    then show "q \<in> set (map fst (d_reachable_states_with_preambles M))"
      by (metis (no_types) \<open>\<And>q. \<lbrakk>\<exists>P. is_preamble P M q; q \<in> nodes M\<rbrakk> \<Longrightarrow> \<exists>P. is_preamble P M q \<and> (q, P) \<in> set (d_reachable_states_with_preambles M)\<close> fst_conv image_eqI set_map)
  qed
  ultimately show ?thesis by blast
qed


value "d_reachable_states M_ex_H"
value "d_reachable_states M_ex_9"



definition maximal_repetition_sets_from_separators :: "('a,'b) FSM_scheme \<Rightarrow> ('a set \<times> 'a set) set" where
  "maximal_repetition_sets_from_separators M = {(S, S \<inter> set (d_reachable_states M)) | S . S \<in> (maximal_pairwise_r_distinguishable_state_sets_from_separators M)}" 

lemma maximal_repetition_sets_from_separators_code[code] :
  "maximal_repetition_sets_from_separators M = (let DR = set (d_reachable_states M) in image (\<lambda> S . (S, S \<inter> DR)) (maximal_pairwise_r_distinguishable_state_sets_from_separators M))"
  unfolding maximal_repetition_sets_from_separators_def Let_def
  by (simp add: Setcompr_eq_image) 
  


value "maximal_repetition_sets_from_separators M_ex_H"
value "maximal_repetition_sets_from_separators M_ex_9"



end