theory ASC_Sufficiency
  imports ASC_Suite
begin

(* variations on preconditions *)
(* TODO: rework by extracting V'' *)
abbreviation
  "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs xs \<equiv> (
      productF M2 M1 FAIL PM
    \<and> is_det_state_cover M2 V
    \<and> V'' \<in> N (vs@xs) M1 V
    \<and> applicable_set M2 \<Omega>
    \<and> \<Omega> \<noteq> {}
   )"

lemma test_tools_props_N[elim] :
  assumes "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs xs"
  and     "fault_model M2 M1 m"
  shows "productF M2 M1 FAIL PM"
        "is_det_state_cover M2 V"
        "V'' \<in> N (vs@xs) M1 V"
        "applicable_set M2 \<Omega>"
        "applicable_set M1 \<Omega>"
        "\<Omega> \<noteq> {}"
proof -
  show "productF M2 M1 FAIL PM" using assms(1) by blast
  show "is_det_state_cover M2 V" using assms(1) by blast
  show "V'' \<in> N (vs@xs) M1 V" using assms(1) by blast
  show "applicable_set M2 \<Omega>" using assms(1) by blast
  then show "applicable_set M1 \<Omega>" unfolding applicable_set.simps applicable.simps using fault_model_props(1)[OF assms(2)] by simp
  show "\<Omega> \<noteq> {}" using assms(1) by blast
qed

abbreviation
  "test_tools_R M2 M1 FAIL PM V \<Omega> \<equiv> (
      productF M2 M1 FAIL PM
    \<and> is_det_state_cover M2 V
    \<and> applicable_set M2 \<Omega>
    \<and> \<Omega> \<noteq> {}
   )"

lemma test_tools_props_R[elim] :
  assumes "test_tools_R M2 M1 FAIL PM V \<Omega>"
  and     "fault_model M2 M1 m"
  shows "productF M2 M1 FAIL PM"
        "is_det_state_cover M2 V"
        "applicable_set M2 \<Omega>"
        "applicable_set M1 \<Omega>"
        "\<Omega> \<noteq> {}"
proof -
  show "productF M2 M1 FAIL PM" using assms(1) by blast
  show "is_det_state_cover M2 V" using assms(1) by blast
  show "applicable_set M2 \<Omega>" using assms(1) by blast
  then show "applicable_set M1 \<Omega>" unfolding applicable_set.simps applicable.simps using fault_model_props(1)[OF assms(2)] by simp
  show "\<Omega> \<noteq> {}" using assms(1) by blast
qed

(* helper properties concerning minimal sequences to failures *)
lemma language_state_in_map_fst_contained :
  assumes "vs \<in> language_state_in M q V"
shows "map fst vs \<in> V" 
proof -
  have "(map fst vs) || (map snd vs) = vs" 
    by auto
  then have "(map fst vs) || (map snd vs) \<in> language_state_in M q V" 
    using assms by auto
  then show ?thesis by auto
qed
  

lemma mstfe_prefix_input_in_V :
  assumes "minimal_sequence_to_failure_extending V M1 M2 vs xs"
  shows "(map fst vs) \<in> V"
proof -
  have "vs \<in> language_state_in M1 (initial M1) V" 
    using assms by auto
  then show ?thesis 
    using language_state_in_map_fst_contained by auto
qed
    
    


lemma mstfe_mcp :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "is_det_state_cover M2 V"
  and     "minimal_sequence_to_failure_extending V M1 M2 vs xs"
shows "mcp (map fst (vs@xs)) V (map fst vs)"
proof (rule ccontr)
  assume "\<not> mcp (map fst (vs @ xs)) V (map fst vs)"
  moreover have "prefix (map fst vs) (map fst (vs @ xs))"  
    by auto
  moreover have "(map fst vs) \<in> V"
    using mstfe_prefix_input_in_V assms(4) by auto
  ultimately obtain v' where "prefix v' (map fst (vs @ xs))" 
                             "v' \<in> V" 
                             "length v' > length (map fst vs)"
    using leI by auto 

  (*sketch 
      length v' > length (map fst vs) implies the existence of a seq. to failure shorter than vs
   *)

  then obtain x' where "(map fst (vs@xs)) = v'@x'"
    using prefixE by blast 

  have "vs@xs \<in> L M1 - L M2" 
    using assms(4) unfolding minimal_sequence_to_failure_extending.simps sequence_to_failure.simps by blast
  then have "vs@xs \<in> language_state_in M1 (initial M1) {map fst (vs@xs)}"
    by (meson DiffE insertI1 language_state_in_map_fst) 
  have "vs@xs \<in> language_state_in M1 (initial M1) {v'@x'}"
    using \<open>map fst (vs @ xs) = v' @ x'\<close> \<open>vs @ xs \<in> language_state_in M1 (initial M1) {map fst (vs @ xs)}\<close> by presburger
   
  let ?vs' = "take (length v') (vs@xs)"
  let ?xs' = "drop (length v') (vs@xs)"
  
  have "vs@xs = ?vs'@?xs'"
    by (metis append_take_drop_id) 

  have "?vs' \<in> language_state_in M1 (initial M1) V"
    by (metis (no_types) DiffE \<open>map fst (vs @ xs) = v' @ x'\<close> \<open>v' \<in> V\<close> \<open>vs @ xs \<in> L M1 - L M2\<close> append_eq_conv_conj append_take_drop_id language_state_in_map_fst language_state_prefix take_map) 
    
  have "sequence_to_failure M1 M2 (?vs' @ ?xs')"
    by (metis (full_types) \<open>vs @ xs = take (length v') (vs @ xs) @ drop (length v') (vs @ xs)\<close> assms(4) minimal_sequence_to_failure_extending.simps) 

  have "length ?xs' < length xs"
    using \<open>length (map fst vs) < length v'\<close> \<open>prefix v' (map fst (vs @ xs))\<close> \<open>vs @ xs = take (length v') (vs @ xs) @ drop (length v') (vs @ xs)\<close> prefix_length_le by fastforce 
  
  show "False"
    by (meson \<open>length (drop (length v') (vs @ xs)) < length xs\<close> \<open>sequence_to_failure M1 M2 (take (length v') (vs @ xs) @ drop (length v') (vs @ xs))\<close> \<open>take (length v') (vs @ xs) \<in> language_state_in M1 (initial M1) V\<close> assms(4) minimal_sequence_to_failure_extending.elims(2)) 

qed

lemma io_target_implies_L :
  assumes "q \<in> io_targets M (initial M) io"
  shows "io \<in> L M" 
proof -
  obtain tr where "path M (io || tr) (initial M)" "length tr = length io" "target (io || tr) (initial M) = q" 
    using assms by auto
  then show ?thesis by auto
qed

lemma stf_non_nil : 
  assumes "sequence_to_failure M1 M2 xs"
  shows "xs \<noteq> []" 
proof 
  assume "xs = []"
  then have "xs \<in> L M1 \<inter> L M2" 
    by auto
  then show "False" using assms by auto
qed

lemma stf_reaches_FAIL :
  assumes "sequence_to_failure M1 M2 io"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "productF M2 M1 FAIL PM"
shows "FAIL \<in> io_targets PM (initial PM) io" 
proof -
  obtain p where "path PM (io || p) (initial PM) \<and> length p = length io \<and> target (io || p) (initial PM) = FAIL" 
    using fail_reachable_by_sequence_to_failure[OF assms(1)]
    using assms(2) assms(3) assms(4) by blast 
  then show ?thesis by auto
qed

lemma stf_reaches_FAIL_ob :
  assumes "sequence_to_failure M1 M2 io"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "productF M2 M1 FAIL PM"
shows "io_targets PM (initial PM) io = {FAIL}"
proof -
  have "FAIL \<in> io_targets PM (initial PM) io" 
    using stf_reaches_FAIL[OF assms(1-4)] by assumption
  have "observable PM"
    by (meson assms(2) assms(3) assms(4) observable_productF)
  show ?thesis
    by (meson \<open>FAIL \<in> io_targets PM (initial PM) io\<close> \<open>observable PM\<close> observable_io_target_is_singleton)
qed

lemma stf_alt_def :
  assumes "io_targets PM (initial PM) io = {FAIL}"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "productF M2 M1 FAIL PM"
shows "sequence_to_failure M1 M2 io"
proof -
  obtain p where "path PM (io || p) (initial PM)" "length p = length io" "target (io || p) (initial PM) = FAIL"
    using assms(1) by (metis io_targets_elim singletonI) 
  have "io \<noteq> []" 
  proof 
    assume "io = []"
    then have "io_targets PM (initial PM) io = {initial PM}" 
      by auto 
    moreover have "initial PM \<noteq> FAIL" 
    proof -
      have "initial PM = (initial M2, initial M1)" 
        using assms(4) by auto
      then have "initial PM \<in> (nodes M2 \<times> nodes M1)"
        by (simp add: FSM.nodes.initial) 
      moreover have "FAIL \<notin> (nodes M2 \<times> nodes M1)"
        using assms(4) by auto
      ultimately show ?thesis 
        by auto
    qed
    ultimately show "False"
      using assms(1) by blast 
  qed
  then have "0 < length io" 
    by blast
  
  have "target (butlast (io||p)) (initial PM) \<noteq> FAIL" using no_prefix_targets_FAIL[OF assms(4) \<open>path PM (io || p) (initial PM)\<close>, of "(length io) - 1" ]
    by (metis (no_types, lifting) \<open>0 < length io\<close> \<open>length p = length io\<close> butlast_conv_take diff_less length_map less_numeral_extra(1) map_fst_zip)  
  have "target (butlast (io||p)) (initial PM) \<in> nodes PM"
    by (metis FSM.nodes.initial FSM.nodes_target FSM.path_append_elim \<open>path PM (io || p) (initial PM)\<close> append_butlast_last_id butlast.simps(1)) 
  moreover have "nodes PM \<subseteq> insert FAIL (nodes M2 \<times> nodes M1)" 
    using nodes_productF[OF _ _ assms(4)] assms(2) assms(3) by linarith 
  ultimately have "target (butlast (io||p)) (initial PM) \<in> insert FAIL (nodes M2 \<times> nodes M1)"
    by blast
  
  have "target (butlast (io||p)) (initial PM) \<in> (nodes M2 \<times> nodes M1)"
    using \<open>target (butlast (io || p)) (initial PM) \<in> insert FAIL (nodes M2 \<times> nodes M1)\<close> \<open>target (butlast (io || p)) (initial PM) \<noteq> FAIL\<close> by blast
  then obtain s2 s1 where "target (butlast (io||p)) (initial PM) = (s2,s1)" "s2 \<in> nodes M2" "s1 \<in> nodes M1" 
    by blast

  have "length (butlast io) = length (map fst (butlast p))" "length (map fst (butlast p)) = length (map snd (butlast p))"
    by (simp add: \<open>length p = length io\<close>)+

  have "path PM (butlast (io||p)) (initial PM)"
    by (metis FSM.path_append_elim \<open>path PM (io || p) (initial PM)\<close> append_butlast_last_id butlast.simps(1)) 
  then have "path PM ((butlast io) || (map fst (butlast p)) || (map snd (butlast p))) (initial M2, initial M1)"
    using \<open>length p = length io\<close> assms(4) by auto 
  have "target (butlast io || map fst (butlast p) || map snd (butlast p)) (initial M2, initial M1) \<noteq> FAIL"
    using \<open>length p = length io\<close> \<open>target (butlast (io || p)) (initial PM) \<noteq> FAIL\<close> assms(4) by auto  
  
  have "path M2 (butlast io || map fst (butlast p)) (initial M2) \<and>
          path M1 (butlast io || map snd (butlast p)) (initial M1) \<or>
        target (butlast io || map fst (butlast p) || map snd (butlast p)) (initial M2, initial M1) = FAIL" 
    using productF_path_reverse[OF \<open>length (butlast io) = length (map fst (butlast p))\<close> 
                                   \<open>length (map fst (butlast p)) = length (map snd (butlast p))\<close> 
                                   assms(4) _ _ 
                                   \<open>path PM ((butlast io) || (map fst (butlast p)) || (map snd (butlast p))) (initial M2, initial M1)\<close> _ _]
    using assms(2) assms(3) by auto
  then have "path M2 (butlast io || map fst (butlast p)) (initial M2)"
            "path M1 (butlast io || map snd (butlast p)) (initial M1)"
    using \<open>target (butlast io || map fst (butlast p) || map snd (butlast p)) (initial M2, initial M1) \<noteq> FAIL\<close> by auto
  
  then have "butlast io \<in> L M2 \<inter> L M1"
    using \<open>length (butlast io) = length (map fst (butlast p))\<close> by auto 

  have "path PM (io || map fst p || map snd p) (initial M2, initial M1)"
    using \<open>path PM (io || p) (initial PM)\<close> assms(4) by auto 
  have "length io = length (map fst p)"
       "length (map fst p) = length (map snd p)"
    by (simp add: \<open>length p = length io\<close>)+
    
  obtain p1' where "path M1 (io || p1') (initial M1) \<and> length io = length p1'"
    using productF_path_reverse_ob[OF \<open>length io = length (map fst p)\<close> \<open>length (map fst p) = length (map snd p)\<close> assms(4) _ _ \<open>path PM (io || map fst p || map snd p) (initial M2, initial M1)\<close>]
    using assms(2) assms(3) by blast 
  then have "io \<in> L M1" 
    by auto
    


  moreover have "io \<notin> L M2"
  proof  
    assume "io \<in> L M2" (* only possible if io does not target FAIL *)
    then obtain p2' where "path M2 (io || p2') (initial M2)" "length io = length p2'" 
      by auto
    then have "length p2' = length p1'"
      using \<open>path M1 (io || p1') (initial M1) \<and> length io = length p1'\<close> by auto 
      
    have "path PM (io || p2' || p1') (initial M2, initial M1)" 
      using productF_path_inclusion[OF \<open>length io = length p2'\<close> \<open>length p2' = length p1'\<close> assms(4), of "initial M2" "initial M1"]
      by (meson FSM.nodes.initial \<open>\<lbrakk>well_formed M2; well_formed M1; path M2 (io || p2') (initial M2) \<and> path M1 (io || p1') (initial M1); initial M2 \<in> nodes M2; initial M1 \<in> nodes M1\<rbrakk> \<Longrightarrow> path PM (io || p2' || p1') (initial M2, initial M1)\<close> \<open>path M1 (io || p1') (initial M1) \<and> length io = length p1'\<close> \<open>path M2 (io || p2') (initial M2)\<close> assms(2) assms(3))
    
    have "target (io || p2' || p1') (initial M2, initial M1) \<in> (nodes M2 \<times> nodes M1)"
      using \<open>length io = length p2'\<close> \<open>path M1 (io || p1') (initial M1) \<and> length io = length p1'\<close> \<open>path M2 (io || p2') (initial M2)\<close> by auto 
    moreover have "FAIL \<notin> (nodes M2 \<times> nodes M1)"
      using assms(4) by auto
    ultimately have "target (io || p2' || p1') (initial M2, initial M1) \<noteq> FAIL" 
      by blast
    
    have "length io = length (p2' || p1')"
      by (simp add: \<open>length io = length p2'\<close> \<open>length p2' = length p1'\<close>) 
    have "target (io || p2' || p1') (initial M2, initial M1) \<in> io_targets PM (initial M2, initial M1) io"  
      using \<open>path PM (io || p2' || p1') (initial M2, initial M1)\<close> \<open>length io = length (p2' || p1')\<close>
      unfolding io_targets.simps by blast
    
    have "io_targets PM (initial PM) io \<noteq> {FAIL}"
      using \<open>target (io || p2' || p1') (initial M2, initial M1) \<in> io_targets PM (initial M2, initial M1) io\<close> \<open>target (io || p2' || p1') (initial M2, initial M1) \<noteq> FAIL\<close> assms(4) by auto
    then show "False"
      using assms(1) by blast  
  qed

  ultimately have "io \<in> L M1 - L M2" 
    by blast

  show "sequence_to_failure M1 M2 io" 
    using \<open>butlast io \<in> L M2 \<inter> L M1\<close> \<open>io \<in> L M1 - L M2\<close> by auto
qed


lemma mstfe_distinct_Rep_Pre :
  assumes "minimal_sequence_to_failure_extending V M1 M2 vs xs"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs xs'"
  and     "prefix xs' xs"
  shows "\<not> Rep_Pre M2 M1 vs xs'"
proof 
  assume "Rep_Pre M2 M1 vs xs'" 
  then obtain xs1 xs2 s1 s2 where  "prefix xs1 xs2"   
                                   "prefix xs2 xs'"
                                   "xs1 \<noteq> xs2"
                                   "io_targets M2 (initial M2) (vs @ xs1) = {s2}" 
                                   "io_targets M2 (initial M2) (vs @ xs2) = {s2}"
                                   "io_targets M1 (initial M1) (vs @ xs1) = {s1}"
                                   "io_targets M1 (initial M1) (vs @ xs2) = {s1}"
    by auto
  then have "s2 \<in> io_targets M2 (initial M2) (vs @ xs1)"
            "s2 \<in> io_targets M2 (initial M2) (vs @ xs2)"
            "s1 \<in> io_targets M1 (initial M1) (vs @ xs1)"
            "s1 \<in> io_targets M1 (initial M1) (vs @ xs2)"            
    by auto

  have "vs@xs1 \<in> L M1" 
    using io_target_implies_L[OF \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs1)\<close>] by assumption
  have "vs@xs2 \<in> L M1" 
    using io_target_implies_L[OF \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs2)\<close>] by assumption
  have "vs@xs1 \<in> L M2" 
    using io_target_implies_L[OF \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs1)\<close>] by assumption
  have "vs@xs2 \<in> L M2" 
    using io_target_implies_L[OF \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs2)\<close>] by assumption

  obtain tr1_1 where "path M1 (vs@xs1 || tr1_1) (initial M1)" "length tr1_1 = length (vs@xs1)" "target (vs@xs1 || tr1_1) (initial M1) = s1"
    using \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs1)\<close> by auto
  obtain tr1_2 where "path M1 (vs@xs2 || tr1_2) (initial M1)" "length tr1_2 = length (vs@xs2)" "target (vs@xs2 || tr1_2) (initial M1) = s1"
    using \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs2)\<close> by auto 
  obtain tr2_1 where "path M2 (vs@xs1 || tr2_1) (initial M2)" "length tr2_1 = length (vs@xs1)" "target (vs@xs1 || tr2_1) (initial M2) = s2"
    using \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs1)\<close> by auto
  obtain tr2_2 where "path M2 (vs@xs2 || tr2_2) (initial M2)" "length tr2_2 = length (vs@xs2)" "target (vs@xs2 || tr2_2) (initial M2) = s2"
    using \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs2)\<close> by auto 


  have "productF M2 M1 FAIL PM" 
    using assms(5) by auto
  have "well_formed M1" 
    using assms(2) by auto
  have "well_formed M2" 
    using assms(3) by auto
  have "observable PM"
    by (meson assms(2) assms(3) assms(5) observable_productF)

  have "length (vs@xs1) = length tr2_1"
    using \<open>length tr2_1 = length (vs @ xs1)\<close> by presburger
  then have "length tr2_1 = length tr1_1" 
    using \<open>length tr1_1 = length (vs@xs1)\<close> by presburger

  have "vs@xs1 \<in> L PM" 
    using productF_path_inclusion[OF \<open>length (vs@xs1) = length tr2_1\<close> \<open>length tr2_1 = length tr1_1\<close> \<open>productF M2 M1 FAIL PM\<close> \<open>well_formed M2\<close> \<open>well_formed M1\<close>]
    by (meson Int_iff \<open>productF M2 M1 FAIL PM\<close> \<open>vs @ xs1 \<in> L M1\<close> \<open>vs @ xs1 \<in> L M2\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> productF_language)
    

  have "length (vs@xs2) = length tr2_2"
    using \<open>length tr2_2 = length (vs @ xs2)\<close> by presburger
  then have "length tr2_2 = length tr1_2" 
    using \<open>length tr1_2 = length (vs@xs2)\<close> by presburger

  have "vs@xs2 \<in> L PM" 
    using productF_path_inclusion[OF \<open>length (vs@xs2) = length tr2_2\<close> \<open>length tr2_2 = length tr1_2\<close> \<open>productF M2 M1 FAIL PM\<close> \<open>well_formed M2\<close> \<open>well_formed M1\<close>]
    by (meson Int_iff \<open>productF M2 M1 FAIL PM\<close> \<open>vs @ xs2 \<in> L M1\<close> \<open>vs @ xs2 \<in> L M2\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> productF_language)


  

  have "io_targets PM (initial M2, initial M1) (vs @ xs1) = {(s2, s1)}" 
    using productF_path_io_targets_reverse[OF \<open>productF M2 M1 FAIL PM\<close> \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs1)\<close> \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs1)\<close> \<open>vs @ xs1 \<in> L M2\<close> \<open>vs @ xs1 \<in> L M1\<close> ]
  proof -
    have "\<forall>c f. c \<noteq> initial (f::('a, 'b, 'c) FSM) \<or> c \<in> nodes f"
      by blast
    then show ?thesis
      by (metis (no_types) \<open>\<lbrakk>observable M2; observable M1; well_formed M2; well_formed M1; initial M2 \<in> nodes M2; initial M1 \<in> nodes M1\<rbrakk> \<Longrightarrow> io_targets PM (initial M2, initial M1) (vs @ xs1) = {(s2, s1)}\<close> assms(2) assms(3))
  qed 

  have "io_targets PM (initial M2, initial M1) (vs @ xs2) = {(s2, s1)}" 
    using productF_path_io_targets_reverse[OF \<open>productF M2 M1 FAIL PM\<close> \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs2)\<close> \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs2)\<close> \<open>vs @ xs2 \<in> L M2\<close> \<open>vs @ xs2 \<in> L M1\<close> ]
  proof -
    have "\<forall>c f. c \<noteq> initial (f::('a, 'b, 'c) FSM) \<or> c \<in> nodes f"
      by blast
    then show ?thesis
      by (metis (no_types) \<open>\<lbrakk>observable M2; observable M1; well_formed M2; well_formed M1; initial M2 \<in> nodes M2; initial M1 \<in> nodes M1\<rbrakk> \<Longrightarrow> io_targets PM (initial M2, initial M1) (vs @ xs2) = {(s2, s1)}\<close> assms(2) assms(3))
  qed

  have "prefix (vs @ xs1) (vs @ xs2)"
    using \<open>prefix xs1 xs2\<close> by auto



  have "sequence_to_failure M1 M2 (vs@xs)" 
    using assms(1) by auto
  

  have "prefix (vs@xs1) (vs@xs')"
    using \<open>prefix xs1 xs2\<close> \<open>prefix xs2 xs'\<close> prefix_order.dual_order.trans same_prefix_prefix by blast 
  have "prefix (vs@xs2) (vs@xs')"
    using \<open>prefix xs2 xs'\<close> prefix_order.dual_order.trans same_prefix_prefix by blast 

   

  have "io_targets PM (initial PM) (vs @ xs1) = {(s2,s1)}"
    using \<open>io_targets PM (initial M2, initial M1) (vs @ xs1) = {(s2, s1)}\<close> assms(5) by auto
  have "io_targets PM (initial PM) (vs @ xs2) = {(s2,s1)}"
    using \<open>io_targets PM (initial M2, initial M1) (vs @ xs2) = {(s2, s1)}\<close> assms(5) by auto


  have "(vs @ xs2) @ (drop (length xs2) xs) = vs@xs"
    by (metis \<open>prefix xs2 xs'\<close>  append_eq_appendI append_eq_conv_conj assms(6) prefixE) 
  moreover have "io_targets PM (initial PM) (vs@xs) = {FAIL}" 
    using stf_reaches_FAIL_ob[OF \<open>sequence_to_failure M1 M2 (vs@xs)\<close> assms(2,3) \<open>productF M2 M1 FAIL PM\<close>] by assumption
  ultimately have "io_targets PM (initial PM) ((vs @ xs2) @ (drop (length xs2) xs)) = {FAIL}" 
    by auto
  
  have "io_targets PM (s2,s1) (drop (length xs2) xs) = {FAIL}" 
    using observable_io_targets_split[OF \<open>observable PM\<close> \<open>io_targets PM (initial PM) ((vs @ xs2) @ (drop (length xs2) xs)) = {FAIL}\<close> \<open>io_targets PM (initial PM) (vs @ xs2) = {(s2, s1)}\<close>] by assumption

  have "io_targets PM (initial PM) (vs@xs1@(drop (length xs2) xs)) = {FAIL}"
    using observable_io_targets_append[OF \<open>observable PM\<close> \<open>io_targets PM (initial PM) (vs @ xs1) = {(s2,s1)}\<close> \<open>io_targets PM (s2,s1) (drop (length xs2) xs) = {FAIL}\<close>] by simp
  have "sequence_to_failure M1 M2 (vs@xs1@(drop (length xs2) xs))"
    using stf_alt_def[OF \<open>io_targets PM (initial PM) (vs@xs1@(drop (length xs2) xs)) = {FAIL}\<close> assms(2,3)]
    using assms(5) by blast 

  have "length xs1 < length xs2"
    using \<open>prefix xs1 xs2\<close> \<open>xs1 \<noteq> xs2\<close> prefix_length_prefix by fastforce     
  have "xs = (xs1 @ (drop (length xs1) xs))"
    by (metis (no_types) \<open>(vs @ xs2) @ drop (length xs2) xs = vs @ xs\<close> \<open>prefix xs1 xs2\<close> append_assoc append_eq_conv_conj prefixE)
  have "length xs1 < length xs"
    using \<open>prefix xs1 xs2\<close> \<open>prefix xs2 xs'\<close> \<open>xs = xs1 @ drop (length xs1) xs\<close> \<open>xs1 \<noteq> xs2\<close> assms(6) leI by fastforce 
  have "length (xs1@(drop (length xs2) xs)) < length xs"
    using \<open>length xs1 < length xs2\<close> \<open>length xs1 < length xs\<close> by auto


  have "vs \<in> language_state_in M1 (initial M1) V \<and> sequence_to_failure M1 M2 (vs @ xs1@(drop (length xs2) xs)) \<and> length (xs1@(drop (length xs2) xs)) < length xs"
    using \<open>length (xs1 @ drop (length xs2) xs) < length xs\<close> \<open>sequence_to_failure M1 M2 (vs @ xs1 @ drop (length xs2) xs)\<close> assms(1) minimal_sequence_to_failure_extending.simps by blast
  
  then have "\<not> minimal_sequence_to_failure_extending V M1 M2 vs xs"
    by (meson minimal_sequence_to_failure_extending.elims(2))
   

  then show "False" 
    using assms(1) by linarith
qed
  



lemma mstfe_distinct_Rep_Cov :
  assumes "minimal_sequence_to_failure_extending V M1 M2 vs xs"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs xsR"
  and     "prefix xsR xs"
shows "\<not> Rep_Cov M2 M1 V'' vs xsR"
proof 
  assume "Rep_Cov M2 M1 V'' vs xsR"
  then obtain xs' vs' s2 s1 where "xs' \<noteq> []" 
                                  "prefix xs' xsR" 
                                  "vs' \<in> V''"
                                  "io_targets M2 (initial M2) (vs @ xs') = {s2}" 
                                  "io_targets M2 (initial M2) (vs') = {s2}"
                                  "io_targets M1 (initial M1) (vs @ xs') = {s1}" 
                                  "io_targets M1 (initial M1) (vs') = {s1}"
    by auto

  then have "s2 \<in> io_targets M2 (initial M2) (vs @ xs')"
            "s2 \<in> io_targets M2 (initial M2) (vs')"
            "s1 \<in> io_targets M1 (initial M1) (vs @ xs')"
            "s1 \<in> io_targets M1 (initial M1) (vs')"            
    by auto

  have "vs@xs' \<in> L M1" 
    using io_target_implies_L[OF \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs')\<close>] by assumption
  have "vs' \<in> L M1" 
    using io_target_implies_L[OF \<open>s1 \<in> io_targets M1 (initial M1) (vs')\<close>] by assumption
  have "vs@xs' \<in> L M2" 
    using io_target_implies_L[OF \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs')\<close>] by assumption
  have "vs' \<in> L M2" 
    using io_target_implies_L[OF \<open>s2 \<in> io_targets M2 (initial M2) (vs')\<close>] by assumption

  obtain tr1_1 where "path M1 (vs@xs' || tr1_1) (initial M1)" "length tr1_1 = length (vs@xs')" "target (vs@xs' || tr1_1) (initial M1) = s1"
    using \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs')\<close> by auto
  obtain tr1_2 where "path M1 (vs' || tr1_2) (initial M1)" "length tr1_2 = length (vs')" "target (vs' || tr1_2) (initial M1) = s1"
    using \<open>s1 \<in> io_targets M1 (initial M1) (vs')\<close> by auto 
  obtain tr2_1 where "path M2 (vs@xs' || tr2_1) (initial M2)" "length tr2_1 = length (vs@xs')" "target (vs@xs' || tr2_1) (initial M2) = s2"
    using \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs')\<close> by auto
  obtain tr2_2 where "path M2 (vs' || tr2_2) (initial M2)" "length tr2_2 = length (vs')" "target (vs' || tr2_2) (initial M2) = s2"
    using \<open>s2 \<in> io_targets M2 (initial M2) (vs')\<close> by auto 


  have "productF M2 M1 FAIL PM" 
    using assms(5) by auto
  have "well_formed M1" 
    using assms(2) by auto
  have "well_formed M2" 
    using assms(3) by auto
  have "observable PM"
    by (meson assms(2) assms(3) assms(5) observable_productF)

  have "length (vs@xs') = length tr2_1"
    using \<open>length tr2_1 = length (vs @ xs')\<close> by presburger
  then have "length tr2_1 = length tr1_1" 
    using \<open>length tr1_1 = length (vs@xs')\<close> by presburger

  have "vs@xs' \<in> L PM" 
    using productF_path_inclusion[OF \<open>length (vs@xs') = length tr2_1\<close> \<open>length tr2_1 = length tr1_1\<close> \<open>productF M2 M1 FAIL PM\<close> \<open>well_formed M2\<close> \<open>well_formed M1\<close>]
    by (meson Int_iff \<open>productF M2 M1 FAIL PM\<close> \<open>vs @ xs' \<in> L M1\<close> \<open>vs @ xs' \<in> L M2\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> productF_language)
    

  have "length (vs') = length tr2_2"
    using \<open>length tr2_2 = length (vs')\<close> by presburger
  then have "length tr2_2 = length tr1_2" 
    using \<open>length tr1_2 = length (vs')\<close> by presburger

  have "vs' \<in> L PM" 
    using productF_path_inclusion[OF \<open>length (vs') = length tr2_2\<close> \<open>length tr2_2 = length tr1_2\<close> \<open>productF M2 M1 FAIL PM\<close> \<open>well_formed M2\<close> \<open>well_formed M1\<close>]
    by (meson Int_iff \<open>productF M2 M1 FAIL PM\<close> \<open>vs' \<in> L M1\<close> \<open>vs' \<in> L M2\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> productF_language)


  

  have "io_targets PM (initial M2, initial M1) (vs @ xs') = {(s2, s1)}" 
    using productF_path_io_targets_reverse[OF \<open>productF M2 M1 FAIL PM\<close> \<open>s2 \<in> io_targets M2 (initial M2) (vs @ xs')\<close> \<open>s1 \<in> io_targets M1 (initial M1) (vs @ xs')\<close> \<open>vs @ xs' \<in> L M2\<close> \<open>vs @ xs' \<in> L M1\<close> ]
  proof -
    have "\<forall>c f. c \<noteq> initial (f::('a, 'b, 'c) FSM) \<or> c \<in> nodes f"
      by blast
    then show ?thesis
      by (metis (no_types) \<open>\<lbrakk>observable M2; observable M1; well_formed M2; well_formed M1; initial M2 \<in> nodes M2; initial M1 \<in> nodes M1\<rbrakk> \<Longrightarrow> io_targets PM (initial M2, initial M1) (vs @ xs') = {(s2, s1)}\<close> assms(2) assms(3))
  qed 

  have "io_targets PM (initial M2, initial M1) (vs') = {(s2, s1)}" 
    using productF_path_io_targets_reverse[OF \<open>productF M2 M1 FAIL PM\<close> \<open>s2 \<in> io_targets M2 (initial M2) (vs')\<close> \<open>s1 \<in> io_targets M1 (initial M1) (vs')\<close> \<open>vs' \<in> L M2\<close> \<open>vs' \<in> L M1\<close> ]
  proof -
    have "\<forall>c f. c \<noteq> initial (f::('a, 'b, 'c) FSM) \<or> c \<in> nodes f"
      by blast
    then show ?thesis
      by (metis (no_types) \<open>\<lbrakk>observable M2; observable M1; well_formed M2; well_formed M1; initial M2 \<in> nodes M2; initial M1 \<in> nodes M1\<rbrakk> \<Longrightarrow> io_targets PM (initial M2, initial M1) (vs') = {(s2, s1)}\<close> assms(2) assms(3))
  qed
  have "io_targets PM (initial PM) (vs') = {(s2, s1)}"
    by (metis (no_types) \<open>io_targets PM (initial M2, initial M1) vs' = {(s2, s1)}\<close> \<open>productF M2 M1 FAIL PM\<close> productF_simps(4))
   

  have "sequence_to_failure M1 M2 (vs@xs)" 
    using assms(1) by auto

  have "xs = xs' @ (drop (length xs') xs)"
    by (metis \<open>prefix xs' xsR\<close> append_assoc append_eq_conv_conj assms(6) prefixE)
  then have "io_targets PM (initial M2, initial M1) (vs @ xs' @ (drop (length xs') xs)) = {FAIL}"
    by (metis \<open>productF M2 M1 FAIL PM\<close> \<open>sequence_to_failure M1 M2 (vs @ xs)\<close> assms(2) assms(3) productF_simps(4) stf_reaches_FAIL_ob)
  then have "io_targets PM (initial M2, initial M1) ((vs @ xs') @ (drop (length xs') xs)) = {FAIL}"    
    by auto
  have "io_targets PM (s2, s1) (drop (length xs') xs) = {FAIL}" 
    using observable_io_targets_split[OF \<open>observable PM\<close> \<open>io_targets PM (initial M2, initial M1) ((vs @ xs') @ (drop (length xs') xs)) = {FAIL}\<close> \<open>io_targets PM (initial M2, initial M1) (vs @ xs') = {(s2, s1)}\<close>] by assumption

  have "io_targets PM (initial PM) (vs' @ (drop (length xs') xs)) = {FAIL}" 
    using observable_io_targets_append[OF \<open>observable PM\<close> \<open>io_targets PM (initial PM) (vs') = {(s2, s1)}\<close> \<open>io_targets PM (s2, s1) (drop (length xs') xs) = {FAIL}\<close>] by assumption

  have "sequence_to_failure M1 M2 (vs' @ (drop (length xs') xs))"   
    using stf_alt_def[OF \<open>io_targets PM (initial PM) (vs' @ (drop (length xs') xs)) = {FAIL}\<close> assms(2,3)] assms(5) by blast

  have "length (drop (length xs') xs) < length xs"
    by (metis (no_types) \<open>xs = xs' @ drop (length xs') xs\<close> \<open>xs' \<noteq> []\<close> length_append length_greater_0_conv less_add_same_cancel2)   

  have "vs' \<in> language_state_in M1 (initial M1) V" 
  proof -
    have "V'' \<in> N (vs@xsR) M1 V" 
      using assms(5) by auto
    then have "V'' \<in> Perm V M1" 
      unfolding N.simps by blast

    then obtain f where f_def : "V'' = image f V \<and> (\<forall> v \<in> V . f v \<in> language_state_for_input M1 (initial M1) v)"
      unfolding Perm.simps by blast
    then obtain v where "v \<in> V" "vs' = f v" 
      using \<open>vs' \<in> V''\<close> by auto
    then have "vs' \<in> language_state_for_input M1 (initial M1) v" 
      using f_def by auto
    
    have "language_state_for_input M1 (initial M1) v = language_state_in M1 (initial M1) {v}"
      by auto
    moreover have "{v} \<subseteq> V" 
      using \<open>v \<in> V\<close> by blast   
    ultimately have "language_state_for_input M1 (initial M1) v \<subseteq> language_state_in M1 (initial M1) V"
      unfolding language_state_in.simps language_state_for_input.simps by blast
    then show ?thesis
      using\<open>vs' \<in> language_state_for_input M1 (initial M1) v\<close> by blast
  qed
  
  have "\<not> minimal_sequence_to_failure_extending V M1 M2 vs xs" 
    using \<open>vs' \<in> language_state_in M1 (initial M1) V\<close>
          \<open>sequence_to_failure M1 M2 (vs' @ (drop (length xs') xs))\<close>
          \<open>length (drop (length xs') xs) < length xs\<close>
    using minimal_sequence_to_failure_extending.elims(2) by blast 
  then show "False" 
    using assms(1) by linarith
qed




lemma language_state_inputs :
  assumes "well_formed M"
  and     "io \<in> language_state M q"
shows "set (map fst io) \<subseteq> inputs M"
proof -
  obtain tr where "path M (io || tr) q" "length tr = length io" 
    using assms(2) by auto
  show ?thesis 
    by (metis (no_types) \<open>\<And>thesis. (\<And>tr. \<lbrakk>path M (io || tr) q; length tr = length io\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) map_fst_zip path_input_containment)
qed 


lemma io_reduction_on_subset :
  assumes "io_reduction_on M1 T M2"
  and     "T' \<subseteq> T"
shows "io_reduction_on M1 T' M2"
proof (rule ccontr)
  assume "\<not> io_reduction_on M1 T' M2"
  then obtain xs' where "xs' \<in> T'" "\<not> language_state_in M1 (initial M1) {xs'} \<subseteq> language_state_in M2 (initial M2) {xs'}"
  proof -
    have f1: "\<forall>ps P Pa. (ps::('a \<times> 'b) list) \<notin> P \<or> \<not> P \<subseteq> Pa \<or> ps \<in> Pa"
      by blast
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have f2: "\<forall>P Pa. pps Pa P \<in> P \<and> pps Pa P \<notin> Pa \<or> P \<subseteq> Pa"
      by (meson subsetI)
    have f3: "\<forall>ps f c A. (ps::('a \<times> 'b) list) \<notin> language_state_in f (c::'c) A \<or> map fst ps \<in> A"
      by (meson language_state_in_map_fst_contained)
    then have "language_state_in M1 (initial M1) T' \<subseteq> language_state_in M1 (initial M1) T"
      using f2 by (meson assms(2) language_state_in_in_language_state language_state_in_map_fst set_rev_mp)
    then show ?thesis
      using f3 f2 f1 by (meson \<open>\<not> io_reduction_on M1 T' M2\<close> assms(1) language_state_in_in_language_state language_state_in_map_fst)
  qed 
  then have "xs' \<in> T" 
    using assms(2) by blast

  have "\<not> io_reduction_on M1 T M2"
  proof -
    have f1: "\<forall>as. as \<notin> T' \<or> as \<in> T"
      using assms(2) by auto
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have "\<forall>P Pa. (\<not> P \<subseteq> Pa \<or> (\<forall>ps. ps \<notin> P \<or> ps \<in> Pa)) \<and> (P \<subseteq> Pa \<or> pps Pa P \<in> P \<and> pps Pa P \<notin> Pa)"
      by blast
    then show ?thesis
      using f1 by (meson \<open>\<not> io_reduction_on M1 T' M2\<close> language_state_in_in_language_state language_state_in_map_fst language_state_in_map_fst_contained)
  qed 

  then show "False" 
    using assms(1) by auto
qed
    
lemma io_reduction_from_atc_reduction :
  assumes "is_reduction_on_sets M1 M2 T \<Omega>"
  and     "finite T"
  shows "io_reduction_on M1 T M2" 
using assms(2,1) proof (induction T)
  case empty
  then show ?case by auto
next
  case (insert t T)
  then have "is_reduction_on M1 M2 t \<Omega>"
    by auto
  then have "language_state_in M1 (initial M1) {t} \<subseteq> language_state_in M2 (initial M2) {t}"
    using is_reduction_on.simps by blast

  have "language_state_in M1 (initial M1) T \<subseteq> language_state_in M2 (initial M2) T" 
    using insert.IH
  proof -
    have "is_reduction_on_sets M1 M2 T \<Omega>"
      by (meson contra_subsetD insert.prems is_reduction_on_sets.simps subset_insertI)
    then show ?thesis
      using insert.IH by blast
  qed
  then have "language_state_in M1 (initial M1) T \<subseteq> language_state_in M2 (initial M2) (insert t T)"
    by (meson insert_iff language_state_in_in_language_state language_state_in_map_fst language_state_in_map_fst_contained subsetCE subsetI) 
  moreover have "language_state_in M1 (initial M1) {t} \<subseteq> language_state_in M2 (initial M2) (insert t T)"
  proof -
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have "\<forall>P Pa. pps Pa P \<in> P \<and> pps Pa P \<notin> Pa \<or> P \<subseteq> Pa"
      by blast
    moreover
    { assume "map fst (pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t})) \<notin> insert t T"
      then have "pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t}) \<notin> L\<^sub>i\<^sub>n M1 {t} \<or> pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t}) \<in> L\<^sub>i\<^sub>n M2 (insert t T)"
        by (metis (no_types) insertI1 language_state_in_map_fst_contained singletonD) }
    ultimately show ?thesis
      by (meson \<open>L\<^sub>i\<^sub>n M1 {t} \<subseteq> L\<^sub>i\<^sub>n M2 {t}\<close> language_state_in_in_language_state language_state_in_map_fst set_rev_mp)
  qed
    
    
     
  ultimately show ?case
  proof -
    have f1: "\<forall>ps P Pa. (ps::('a \<times> 'b) list) \<notin> P \<or> \<not> P \<subseteq> Pa \<or> ps \<in> Pa"
      by blast
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    moreover
    { assume "pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T)) \<notin> language_state_in M1 (initial M1) {t}"
      moreover
      { assume "map fst (pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T))) \<notin> {t}"
        then have "map fst (pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T))) \<noteq> t"
          by blast
        then have "pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T)) \<notin> language_state_in M1 (initial M1) (insert t T) \<or> pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T)) \<in> language_state_in M2 (initial M2) (insert t T)"
          using f1 by (meson \<open>language_state_in M1 (initial M1) T \<subseteq> language_state_in M2 (initial M2) (insert t T)\<close> insertE language_state_in_in_language_state language_state_in_map_fst language_state_in_map_fst_contained) }
      ultimately have "io_reduction_on M1 (insert t T) M2 \<or> pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T)) \<notin> language_state_in M1 (initial M1) (insert t T) \<or> pps (language_state_in M2 (initial M2) (insert t T)) (language_state_in M1 (initial M1) (insert t T)) \<in> language_state_in M2 (initial M2) (insert t T)"
        using f1 by (meson language_state_in_in_language_state language_state_in_map_fst) }
      ultimately show ?thesis
        using f1 by (meson \<open>language_state_in M1 (initial M1) {t} \<subseteq> language_state_in M2 (initial M2) (insert t T)\<close> subsetI)
  qed 
qed
    
lemma is_reduction_on_subset :
  assumes "is_reduction_on_sets M1 M2 T \<Omega>"
  and     "T' \<subseteq> T"
shows "is_reduction_on_sets M1 M2 T' \<Omega>"
  using assms unfolding is_reduction_on_sets.simps by blast



(* lemma 7.3.1 *)
lemma asc_sufficiency :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_R M2 M1 FAIL PM V \<Omega>"
  and     "final_iteration M2 M1 \<Omega> V m i"
  and     "is_reduction_on_sets M1 M2 (TS M2 M1 \<Omega> V m i) \<Omega>"
shows "M1 \<preceq> M2"
proof (rule ccontr)

  let ?TS = "\<lambda> n . TS M2 M1 \<Omega> V m n"
  let ?C = "\<lambda> n . C M2 M1 \<Omega> V m n"
  let ?RM = "\<lambda> n . RM M2 M1 \<Omega> V m n"


  assume "\<not> M1 \<preceq> M2"
  obtain vs xs where "minimal_sequence_to_failure_extending V M1 M2 vs xs" 
    using \<open>\<not> M1 \<preceq> M2\<close> assms(1) assms(2) assms(4) minimal_sequence_to_failure_extending_det_state_cover_ob[of M2 M1 FAIL PM V] by blast 

  then have "vs \<in> language_state_in M1 (initial M1) V" 
            "sequence_to_failure M1 M2 (vs @ xs)" 
            "\<not> (\<exists> io' . \<exists> w' \<in> language_state_in M1 (initial M1) V . sequence_to_failure M1 M2 (w' @ io') \<and> length io' < length xs)"
    by auto

  then have "vs@xs \<in> L M1 - L M2" 
    by auto

  have "vs@xs \<in> language_state_in M1 (initial M1) {map fst (vs@xs)}"
    by (metis (full_types) Diff_iff \<open>vs @ xs \<in> L M1 - L M2\<close> insertI1 language_state_in_map_fst)

  have "vs@xs \<notin> language_state_in M2 (initial M2) {map fst (vs@xs)}"
    by (meson Diff_iff \<open>vs @ xs \<in> L M1 - L M2\<close> language_state_in_in_language_state subsetCE) 

  have "finite V" 
    using det_state_cover_finite assms(4,2) by auto
  then have "finite (?TS i)"
    using TS_finite[of V M2] assms(2) by auto
  then have "io_reduction_on M1 (?TS i) M2" 
    using io_reduction_from_atc_reduction[OF assms(6)] by auto

  have "map fst (vs@xs) \<notin> ?TS i"
  proof -
    have f1: "\<forall>ps P Pa. (ps::('a \<times> 'b) list) \<notin> P - Pa \<or> ps \<in> P \<and> ps \<notin> Pa"
      by blast
    have "\<forall>P Pa ps. \<not> P \<subseteq> Pa \<or> (ps::('a \<times> 'b) list) \<in> Pa \<or> ps \<notin> P"
      by blast
    then show ?thesis
      using f1 by (metis (no_types) \<open>vs @ xs \<in> L M1 - L M2\<close> \<open>io_reduction_on M1 (?TS i) M2\<close> language_state_in_in_language_state language_state_in_map_fst)
  qed 

  have "map fst vs \<in> V"
    using \<open>vs \<in> language_state_in M1 (initial M1) V\<close> by auto 
  
  let ?stf = "map fst (vs@xs)"
  let ?stfV = "map fst vs"
  let ?stfX = "map fst xs"
  have "?stf = ?stfV @ ?stfX"
    by simp 

  then have "?stfV @ ?stfX \<notin> ?TS i"
    using \<open>?stf \<notin> ?TS i\<close> by auto 

  have "mcp (?stfV @ ?stfX) V ?stfV"
    by (metis \<open>map fst (vs @ xs) = map fst vs @ map fst xs\<close> \<open>minimal_sequence_to_failure_extending V M1 M2 vs xs\<close> assms(1) assms(2) assms(4) mstfe_mcp)

  have "set ?stf \<subseteq> inputs M1"
    by (meson DiffD1 \<open>vs @ xs \<in> L M1 - L M2\<close> assms(1) language_state_inputs) 
  then have "set ?stf \<subseteq> inputs M2"
    using assms(3) by blast 
  moreover have "set ?stf = set ?stfV \<union> set ?stfX"
    by simp 
  ultimately have "set ?stfX \<subseteq> inputs M2"
    by blast 


  obtain xr j where "xr \<noteq> ?stfX" "prefix xr ?stfX" "Suc j \<le> i" "?stfV@xr \<in> RM M2 M1 \<Omega> V m (Suc j)"
    using TS_non_containment_causes_final_suc[OF \<open>?stfV @ ?stfX \<notin> ?TS i\<close> \<open>mcp (?stfV @ ?stfX) V ?stfV\<close> \<open>set ?stfX \<subseteq> inputs M2\<close> assms(5,2)] by blast

  
  let ?yr = "take (length xr) (map snd xs)"
  have "length ?yr = length xr"
    using \<open>prefix xr (map fst xs)\<close> prefix_length_le by fastforce 
  have "(xr || ?yr) = take (length xr) xs"
    by (metis (no_types, hide_lams) \<open>prefix xr (map fst xs)\<close> append_eq_conv_conj prefixE take_zip zip_map_fst_snd) 

  have "prefix (vs@(xr || ?yr)) (vs@xs)"
    by (simp add: \<open>xr || take (length xr) (map snd xs) = take (length xr) xs\<close> take_is_prefix)

  have "xr = take (length xr) (map fst xs)"
    by (metis \<open>length (take (length xr) (map snd xs)) = length xr\<close> \<open>xr || take (length xr) (map snd xs) = take (length xr) xs\<close> map_fst_zip take_map) 

  have "vs@(xr || ?yr) \<in> L M1"
    by (metis DiffD1 \<open>prefix (vs @ (xr || take (length xr) (map snd xs))) (vs @ xs)\<close> \<open>vs @ xs \<in> L M1 - L M2\<close> language_state_prefix prefixE) 

  then have "vs@(xr || ?yr) \<in> language_state_in M1 (initial M1) {?stfV @ xr}"
    by (metis \<open>length (take (length xr) (map snd xs)) = length xr\<close> insertI1 language_state_in_map_fst map_append map_fst_zip) 

  have "length xr < length xs"
    by (metis \<open>xr = take (length xr) (map fst xs)\<close> \<open>xr \<noteq> map fst xs\<close> not_le_imp_less take_all take_map)



  from \<open>?stfV@xr \<in> RM M2 M1 \<Omega> V m (Suc j)\<close> have "?stfV@xr \<in> {xs' \<in> C M2 M1 \<Omega> V m (Suc j) .
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
                \<and> m < LB M2 M1 vs xs (TS M2 M1 \<Omega> V m j \<union> V) S1 \<Omega> V'' ))))}" 
    unfolding RM.simps by blast

  moreover have "\<forall> xs' \<in> ?C (Suc j) . language_state_in M1 (initial M1) {xs'} \<subseteq> language_state_in M2 (initial M2) {xs'}"
  proof 
    fix xs' assume "xs' \<in> ?C (Suc j)"
    from \<open>Suc j \<le> i\<close> have "?C (Suc j) \<subseteq> ?TS i"
      using C_subset TS_subset by blast 
    then have "{xs'} \<subseteq> ?TS i" 
      using \<open>xs' \<in> ?C (Suc j)\<close> by blast
    show "language_state_in M1 (initial M1) {xs'} \<subseteq> language_state_in M2 (initial M2) {xs'}" 
      using io_reduction_on_subset[OF \<open>io_reduction_on M1 (?TS i) M2\<close> \<open>{xs'} \<subseteq> ?TS i\<close>] by assumption
  qed

  ultimately have "(\<forall> io \<in> language_state_in M1 (initial M1) {?stfV@xr} .
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
                \<and> m < LB M2 M1 vs xs (TS M2 M1 \<Omega> V m j \<union> V) S1 \<Omega> V'' ))))"
    by blast 

  then have "
          (\<exists> V'' \<in> N (vs@(xr || ?yr)) M1 V .  
            (\<exists> S1 . 
              (\<exists> vs' xs' .
                vs@(xr || ?yr) = (vs'@xs')
                \<and> mcp (vs'@xs') V'' vs'
                \<and> S1 \<subseteq> nodes M2
                \<and> (\<forall> s1 \<in> S1 . \<forall> s2 \<in> S1 .
                  s1 \<noteq> s2 \<longrightarrow> 
                    (\<forall> io1 \<in> RP M2 s1 vs' xs' V'' .
                       \<forall> io2 \<in> RP M2 s2 vs' xs' V'' .
                         B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega> ))
                \<and> m < LB M2 M1 vs' xs' (TS M2 M1 \<Omega> V m j \<union> V) S1 \<Omega> V'' )))"
    using \<open>vs@(xr || ?yr) \<in> language_state_in M1 (initial M1) {?stfV @ xr}\<close>
    by blast 

  then obtain V'' S1 vs' xs' where RM_impl :  
                                   "V'' \<in> N (vs@(xr || ?yr)) M1 V"
                                   "vs@(xr || ?yr) = (vs'@xs')"
                                   "mcp (vs'@xs') V'' vs'"
                                   "S1 \<subseteq> nodes M2"
                                   "(\<forall> s1 \<in> S1 . \<forall> s2 \<in> S1 .
                                     s1 \<noteq> s2 \<longrightarrow> 
                                        (\<forall> io1 \<in> RP M2 s1 vs' xs' V'' .
                                           \<forall> io2 \<in> RP M2 s2 vs' xs' V'' .
                                             B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega> ))"
                                   " m < LB M2 M1 vs' xs' (TS M2 M1 \<Omega> V m j \<union> V) S1 \<Omega> V''"
    by blast

 
  have "?stfV = mcp' (map fst (vs @ (xr || take (length xr) (map snd xs)))) V"
    by (metis (full_types) \<open>length (take (length xr) (map snd xs)) = length xr\<close> \<open>mcp (map fst vs @ map fst xs) V (map fst vs)\<close> \<open>prefix xr (map fst xs)\<close> map_append map_fst_zip mcp'_intro mcp_prefix_of_suffix) 

  have "is_det_state_cover M2 V"
    using assms(4) by blast 
  moreover have "well_formed M2" 
    using assms(2) by auto
  moreover have "finite V" 
    using det_state_cover_finite assms(4,2) by auto
  ultimately have "vs \<in> V''"  
       "vs = mcp' (vs @ (xr || take (length xr) (map snd xs))) V''"
    using N_mcp_prefix[OF \<open>?stfV = mcp' (map fst (vs @ (xr || take (length xr) (map snd xs)))) V\<close> \<open>V'' \<in> N (vs@(xr || ?yr)) M1 V\<close>, of M2] by simp+
  
  have "vs' = vs"
    by (metis (no_types) \<open>mcp (vs' @ xs') V'' vs'\<close> \<open>vs = mcp' (vs @ (xr || take (length xr) (map snd xs))) V''\<close> \<open>vs @ (xr || take (length xr) (map snd xs)) = vs' @ xs'\<close> mcp'_intro)
   
  then have "xs' = (xr || ?yr)"
    using \<open>vs @ (xr || take (length xr) (map snd xs)) = vs' @ xs'\<close> by blast  




  have "V \<subseteq> ?TS i"
  proof -
    have "1 \<le> i"
      using \<open>Suc j \<le> i\<close> by linarith
    then have "?TS 1 \<subseteq> ?TS i"
      using TS_subset by blast   
    then show ?thesis 
      by auto
  qed
    
  have "?stfV@xr \<in> ?C (Suc j)" 
        using \<open>?stfV@xr \<in> RM M2 M1 \<Omega> V m (Suc j)\<close> unfolding RM.simps by blast



  (* show the the prerequisites (Prereq) for LB are met by construction *)

  have "(\<forall>vs'a\<in>V''. prefix vs'a (vs' @ xs') \<longrightarrow> length vs'a \<le> length vs')"
    using \<open>mcp (vs' @ xs') V'' vs'\<close> by auto

  moreover have "is_reduction_on_sets M1 M2 (?TS j \<union> V) \<Omega>"   
  proof -
    have "j < i" 
      using \<open>Suc j \<le> i\<close> by auto
    then have "?TS j \<subseteq> ?TS i" 
      by (simp add: TS_subset) 
    then show ?thesis 
      using is_reduction_on_subset[OF assms(6), of "?TS j"]
      by (meson Un_subset_iff \<open>V \<subseteq> ?TS i\<close> assms(6) is_reduction_on_subset) 
  qed

  moreover have "finite (?TS j \<union> V)"
  proof -
    have "finite (?TS j)"
      using TS_finite[OF \<open>finite V\<close>, of M2 M1 \<Omega> m j] assms(2) by auto 
    then show ?thesis 
      using \<open>finite V\<close> by blast
  qed

  moreover have "V \<subseteq> ?TS j \<union> V" 
    by blast

  moreover have "(\<forall> p . (prefix p xs' \<and> p \<noteq> xs') \<longrightarrow> map fst (vs' @ p) \<in> ?TS j \<union> V)"
  proof 
    fix p 
    show "prefix p xs' \<and> p \<noteq> xs' \<longrightarrow> map fst (vs' @ p) \<in> TS M2 M1 \<Omega> V m j \<union> V"
    proof
      assume "prefix p xs' \<and> p \<noteq> xs'"

      have "prefix (map fst (vs' @ p)) (map fst (vs' @ xs'))"
        by (simp add: \<open>prefix p xs' \<and> p \<noteq> xs'\<close> map_mono_prefix)
      have "prefix (map fst (vs' @ p)) (?stfV @ xr)"
        using \<open>length (take (length xr) (map snd xs)) = length xr\<close> \<open>prefix (map fst (vs' @ p)) (map fst (vs' @ xs'))\<close> \<open>vs' = vs\<close> \<open>xs' = xr || take (length xr) (map snd xs)\<close> by auto
      then have "prefix (map fst vs' @ map fst p) (?stfV @ xr)"
        by simp 
      then have "prefix (map fst p) xr"
        by (simp add: \<open>vs' = vs\<close>)

      have "?stfV @ xr \<in> ?TS (Suc j)" 
      proof (cases j)
        case 0
        then show ?thesis
          using \<open>map fst vs @ xr \<in> C M2 M1 \<Omega> V m (Suc j)\<close> by auto  
      next
        case (Suc nat)
        then show ?thesis
          using TS.simps(3) \<open>map fst vs @ xr \<in> C M2 M1 \<Omega> V m (Suc j)\<close> by blast 
      qed

      have "mcp (map fst vs @ xr) V (map fst vs)"
        using \<open>mcp (map fst vs @ map fst xs) V (map fst vs)\<close> \<open>prefix xr (map fst xs)\<close> mcp_prefix_of_suffix by blast 

      have "map fst vs @ map fst p \<in> TS M2 M1 \<Omega> V m (Suc j)"
        using TS_prefix_containment[OF \<open>?stfV @ xr \<in> ?TS (Suc j)\<close> \<open>mcp (map fst vs @ xr) V (map fst vs)\<close> \<open>prefix (map fst p) xr\<close>] by assumption
 

      have "Suc (length xr) = (Suc j)" 
        using C_index[OF \<open>?stfV@xr \<in> ?C (Suc j)\<close> \<open>mcp (map fst vs @ xr) V (map fst vs)\<close>] by assumption
      
      have"Suc (length p) < (Suc j)"
      proof -
        have "map fst xs' = xr"
          by (metis \<open>xr = take (length xr) (map fst xs)\<close> \<open>xr || take (length xr) (map snd xs) = take (length xr) xs\<close> \<open>xs' = xr || take (length xr) (map snd xs)\<close> take_map)
        then show ?thesis
          by (metis (no_types) Suc_less_eq \<open>Suc (length xr) = Suc j\<close> \<open>prefix p xs' \<and> p \<noteq> xs'\<close> append_eq_conv_conj length_map nat_less_le prefixE prefix_length_le take_all)
      qed

      have "mcp (map fst vs @ map fst p) V (map fst vs)"
        using \<open>mcp (map fst vs @ xr) V (map fst vs)\<close> \<open>prefix (map fst p) xr\<close> mcp_prefix_of_suffix by blast 

      then have "map fst vs @ map fst p \<in> ?C (Suc (length (map fst p)))" 
        using TS_index(2)[OF \<open>map fst vs @ map fst p \<in> TS M2 M1 \<Omega> V m (Suc j)\<close>] by auto

      have "map fst vs @ map fst p \<in> ?TS j"
        using TS_union[of M2 M1 \<Omega> V m j]
      proof -
        have "Suc (length p) \<in> {0..<Suc j}"
          using \<open>Suc (length p) < Suc j\<close> by force
        then show ?thesis
          by (metis UN_I \<open>TS M2 M1 \<Omega> V m j = (\<Union>j\<in>set [0..<Suc j]. C M2 M1 \<Omega> V m j)\<close> \<open>map fst vs @ map fst p \<in> C M2 M1 \<Omega> V m (Suc (length (map fst p)))\<close> length_map set_upt)
      qed 

      then show "map fst (vs' @ p) \<in> TS M2 M1 \<Omega> V m j \<union> V"
        by (simp add: \<open>vs' = vs\<close>) 
    qed
  qed

  
  moreover have "vs' @ xs' \<in> L M2 \<inter> L M1"
    by (metis (no_types, lifting) IntI RM_impl(2) \<open>\<forall>xs'\<in>C M2 M1 \<Omega> V m (Suc j). L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'}\<close> \<open>map fst vs @ xr \<in> C M2 M1 \<Omega> V m (Suc j)\<close> \<open>vs @ (xr || take (length xr) (map snd xs)) \<in> L\<^sub>i\<^sub>n M1 {map fst vs @ xr}\<close> language_state_in_in_language_state subsetCE)
    
        
  
  ultimately have "Prereq M2 M1 vs' xs' (?TS j \<union> V) S1 \<Omega> V V''"
    using RM_impl(4,5) unfolding Prereq.simps by blast

  have "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs (xr || ?yr)"
    using assms(4) \<open>V'' \<in> N (vs@(xr || ?yr)) M1 V\<close>
    by blast 
  
  have "V'' \<in> Perm V M1"
    using \<open>V'' \<in> N (vs@(xr || ?yr)) M1 V\<close> unfolding N.simps by blast
  then have "test_tools M2 M1 FAIL PM V V'' \<Omega>" 
    using assms(4) by blast

  have \<open>prefix (xr || ?yr) xs\<close>
    by (simp add: \<open>xr || take (length xr) (map snd xs) = take (length xr) xs\<close> take_is_prefix)


  (* no repetition can occur as the sequence to failure is already minimal *)
  have "\<not> Rep_Pre M2 M1 vs (xr || ?yr)"
    using mstfe_distinct_Rep_Pre[OF \<open>minimal_sequence_to_failure_extending V M1 M2 vs xs\<close> assms(1,2,3) \<open>test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs (xr || ?yr)\<close> \<open>prefix (xr || take (length xr) (map snd xs)) xs\<close>]
    by assumption
  then have "\<not> Rep_Pre M2 M1 vs' xs'"
    using \<open>vs' = vs\<close> \<open>xs' = xr || ?yr\<close> by blast 

  have "\<not> Rep_Cov M2 M1 V'' vs (xr || ?yr)" 
    using mstfe_distinct_Rep_Cov[OF \<open>minimal_sequence_to_failure_extending V M1 M2 vs xs\<close> assms(1,2,3) \<open>test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs (xr || ?yr)\<close> \<open>prefix (xr || take (length xr) (map snd xs)) xs\<close>]
    by assumption
  then have "\<not> Rep_Cov M2 M1 V'' vs' xs'"
    using \<open>vs' = vs\<close> \<open>xs' = xr || ?yr\<close> by blast 

  have "vs'@xs' \<in> L M1"
    using \<open>vs @ (xr || take (length xr) (map snd xs)) \<in> L M1\<close> \<open>vs' = vs\<close> \<open>xs' = xr || take (length xr) (map snd xs)\<close> by blast 
  

  (* prove the impossiblility to remove the prefix of the minimal sequence to a failure
     by demonstrating that this would require M1 to have more than m states *)
  
  have "LB M2 M1 vs' xs' (?TS j \<union> V) S1 \<Omega> V'' \<le> card (nodes M1)"
    using LB_count[OF \<open>vs'@xs' \<in> L M1\<close> assms(1,2,3) \<open>test_tools M2 M1 FAIL PM V V'' \<Omega>\<close> \<open>Prereq M2 M1 vs' xs' (?TS j \<union> V) S1 \<Omega> V V''\<close> \<open>\<not> Rep_Pre M2 M1 vs' xs'\<close> \<open> \<not> Rep_Cov M2 M1 V'' vs' xs'\<close>]
    by assumption
  then have "LB M2 M1 vs' xs' (?TS j \<union> V) S1 \<Omega> V'' \<le> m" 
    using assms(3) by linarith

  then show "False" 
    using \<open>m < LB M2 M1 vs' xs' (?TS j \<union> V) S1 \<Omega> V''\<close> by linarith
qed




(* lemma 7.3.1 - reverse *)
lemma asc_soundness :
  assumes     "M1 \<preceq> M2"
  and         "OFSM M1"
  and         "OFSM M2"
shows "is_reduction_on_sets M1 M2 T \<Omega>"
  using is_reduction_on_sets_reduction[OF assms(1)] assms(2,3) by blast



(* Theorem 7.3.2 *)
lemma asc_main_theorem :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_R M2 M1 FAIL PM V \<Omega>"
  and     "final_iteration M2 M1 \<Omega> V m i"
shows     "M1 \<preceq> M2 \<longleftrightarrow> is_reduction_on_sets M1 M2 (TS M2 M1 \<Omega> V m i) \<Omega>"
by (metis asc_sufficiency assms(1-5) is_reduction_on_sets_reduction)





end