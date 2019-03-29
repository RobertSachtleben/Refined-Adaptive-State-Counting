theory ASC_Sufficiency
  imports ASC_Suite
begin

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


lemma mstfe_distinct :
  assumes "minimal_sequence_to_failure_extending V M1 M2 vs xs"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools_N M2 M1 FAIL PM V V'' \<Omega> vs xs"
  shows "\<not> Rep_Pre M2 M1 vs xs"
        (*"\<not> Rep_Cov M2 M1 V'' vs xs"*)
proof 
  assume "Rep_Pre M2 M1 vs xs" 
  then obtain xs1 xs2 s1 s2 where  "prefix xs1 xs2"   
                                   "prefix xs2 xs"
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



  obtain trP1 where "path PM ((vs@xs1) || trP1) (initial PM)" "length trP1 = length (vs@xs1)" "target ((vs@xs1) || trP1) (initial PM) = (s2,s1)"
    by (smt \<open>io_targets PM (initial M2, initial M1) (vs @ xs1) = {(s2, s1)}\<close> \<open>productF M2 M1 FAIL PM\<close> insertI1 io_targets_elim productF_simps(4))

  obtain trP2 where "path PM ((vs@xs2) || trP2) (initial PM)" "length trP2 = length (vs@xs2)" "target ((vs@xs2) || trP2) (initial PM) = (s2,s1)"
    by (smt \<open>io_targets PM (initial M2, initial M1) (vs @ xs2) = {(s2, s1)}\<close> \<open>productF M2 M1 FAIL PM\<close> insertI1 io_targets_elim productF_simps(4))

  have "sequence_to_failure M1 M2 (vs@xs)" 
    using assms(1) by auto
  obtain trP where "path PM (vs@xs || trP) (initial PM)" "length trP = length (vs@xs)" "target (vs@xs || trP) (initial PM) = FAIL"
    using fail_reachable_by_sequence_to_failure[OF \<open>sequence_to_failure M1 M2 (vs@xs)\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> \<open>productF M2 M1 FAIL PM\<close>] by blast


  have "prefix (vs@xs1) (vs@xs)"
    using \<open>prefix xs1 xs2\<close> \<open>prefix xs2 xs\<close> prefix_order.dual_order.trans same_prefix_prefix by blast 
  have "prefix (vs@xs2) (vs@xs)"
    using \<open>prefix xs2 xs\<close> prefix_order.dual_order.trans same_prefix_prefix by blast 

   

  have "io_targets PM (initial PM) (vs @ xs1) = {(s2,s1)}"
    using \<open>io_targets PM (initial M2, initial M1) (vs @ xs1) = {(s2, s1)}\<close> assms(5) by auto
  have "io_targets PM (initial PM) (vs @ xs2) = {(s2,s1)}"
    using \<open>io_targets PM (initial M2, initial M1) (vs @ xs2) = {(s2, s1)}\<close> assms(5) by auto


  have "(vs @ xs2) @ (drop (length xs2) xs) = vs@xs"
    using \<open>prefix (vs @ xs2) (vs @ xs)\<close> prefixE by fastforce 
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
    by (metis \<open>(vs @ xs2) @ drop (length xs2) xs = vs @ xs\<close> \<open>prefix (vs @ xs1) (vs @ xs)\<close> \<open>prefix xs1 xs2\<close> \<open>xs1 \<noteq> xs2\<close> append_eq_append_conv le_neq_trans length_append prefixE prefix_length_le) 
  have "xs = (xs1 @ (drop (length xs1) xs))"
    by (metis (no_types) \<open>prefix (vs @ xs1) (vs @ xs)\<close> append_eq_conv_conj prefixE same_prefix_prefix) 
  have "length xs1 < length xs"
    using \<open>prefix xs1 xs2\<close> \<open>prefix xs2 xs\<close> \<open>xs = xs1 @ drop (length xs1) xs\<close> \<open>xs1 \<noteq> xs2\<close> not_le_imp_less by fastforce  
  have "length (xs1@(drop (length xs2) xs)) < length xs"
    using \<open>length xs1 < length xs2\<close> \<open>length xs1 < length xs\<close> by auto


  have "vs \<in> language_state_in M1 (initial M1) V \<and> sequence_to_failure M1 M2 (vs @ xs1@(drop (length xs2) xs)) \<and> length (xs1@(drop (length xs2) xs)) < length xs"
    using \<open>length (xs1 @ drop (length xs2) xs) < length xs\<close> \<open>sequence_to_failure M1 M2 (vs @ xs1 @ drop (length xs2) xs)\<close> assms(1) minimal_sequence_to_failure_extending.simps by blast
  
  then have "\<not> minimal_sequence_to_failure_extending V M1 M2 vs xs"
    by (meson minimal_sequence_to_failure_extending.elims(2))
   

  then show "False" 
    using assms(1) by linarith
qed
  


  
    

(* lemma 7.3.1 *)
lemma asc_sufficiency :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  (*and     "test_tools M2 M1 FAIL PM V V'' \<Omega>"*)
  and     "final_iteration M2 M1 T \<Omega> V m i"
  and     "is_reduction_on_sets M1 M2 (TS M2 M1 T \<Omega> V m i) \<Omega>"
shows "M1 \<preceq> M2"
proof (rule ccontr)
  assume "\<not> M1 \<preceq> M2"
  obtain xs where "minimal_sequence_to_failure_extending V M1 M2 xs" 
    using \<open>\<not> M1 \<preceq> M2\<close> assms(1) assms(2) assms(4) minimal_sequence_to_failure_extending_det_state_cover_ob[of M2 M1 FAIL PM V] by blast 

  then obtain vs where   "vs \<in> language_state_in M1 (initial M1) V" 
                         "sequence_to_failure M1 M2 (vs @ xs)" 
                         "\<not> (\<exists> io' . \<exists> w' \<in> language_state_in M1 (initial M1) V . 
                                          sequence_to_failure M1 M2 (w' @ io') 
                                          \<and> length io' < length xs)"
    by auto

  have "mcp xs vs"
  
  



end