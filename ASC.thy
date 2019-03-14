theory ASC
imports ATC4 FSM2 FSM_Product
begin 

(* Proposition 5.4.2 *)
(* see B_dist, B_dist' in ATC *)


(* R *)
fun R :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list set" where
  "R M s vs xs = { vs @ xs' | xs' . xs' \<noteq> [] \<and> prefix xs' xs \<and> s \<in> io_targets M (initial M) (vs @ xs') }"

lemma finite_R : "finite (R M s vs xs)" 
proof -
  have "R M s vs xs \<subseteq> { vs @ xs' | xs' .prefix xs' xs }" by auto 
  then have "R M s vs xs \<subseteq> image (\<lambda> xs' . vs @ xs') {xs' . prefix xs' xs}" by auto
  moreover have "{xs' . prefix xs' xs} = {take n xs | n . n \<le> length xs}" 
    proof 
      show "{xs'. prefix xs' xs} \<subseteq> {take n xs |n. n \<le> length xs}" 
      proof 
        fix xs' assume "xs' \<in> {xs'. prefix xs' xs}"
        then obtain zs' where "xs' @ zs' = xs" by (metis (full_types) mem_Collect_eq prefixE) 
        then obtain i where "xs' = take i xs \<and> i \<le> length xs" by (metis (full_types) append_eq_conv_conj le_cases take_all) 
        then show "xs' \<in> {take n xs |n. n \<le> length xs}" by auto
      qed
      show "{take n xs |n. n \<le> length xs} \<subseteq> {xs'. prefix xs' xs}" using take_is_prefix by force 
    qed
  moreover have "finite {take n xs | n . n \<le> length xs}" by auto
  ultimately show ?thesis by auto
qed



lemma card_union_of_singletons :
  assumes "\<forall> S \<in> SS . (\<exists> t . S = {t})"
shows "card (\<Union> SS) = card SS"
proof -
  let ?f = "\<lambda> x . {x}"
  have "bij_betw ?f (\<Union> SS) SS" unfolding bij_betw_def inj_on_def using assms by fastforce
  then show ?thesis using bij_betw_same_card by blast 
qed

lemma card_union_of_distinct :
  assumes "\<forall> S1 \<in> SS . \<forall> S2 \<in> SS . S1 = S2 \<or> f S1 \<inter> f S2 = {}"
  and     "finite SS"
  and     "\<forall> S \<in> SS . f S \<noteq> {}"
shows "card (image f SS) = card SS" 
proof -
  from assms(2) have "\<forall> S1 \<in> SS . \<forall> S2 \<in> SS . S1 = S2 \<or> f S1 \<inter> f S2 = {} \<Longrightarrow> \<forall> S \<in> SS . f S \<noteq> {} \<Longrightarrow> ?thesis"
  proof (induction SS)
    case empty
    then show ?case by auto
  next
    case (insert x F)
    then have "\<not> (\<exists> y \<in> F . f y = f x)" by auto
    then have "f x \<notin> image f F" by auto
    then have "card (image f (insert x F)) = Suc (card (image f F))" using insert by auto
    moreover have "card (f ` F) = card F" using insert by auto
    moreover have "card (insert x F) = Suc (card F)" using insert by auto
    ultimately show ?case by simp
  qed
  then show ?thesis using assms by simp
qed



(* Lemma 5.4.5 *)
lemma R_count :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "distinct (states (xs || tr) (q2,q1))" 
shows "card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))) = card (R M2 s vs xs)"
proof -

  have obs_PM : "observable PM" using observable_productF assms(2) assms(3) assms(7) by blast

  have state_component_2 : "\<forall> io \<in> (R M2 s vs xs) . io_targets M2 (initial M2) io = {s}" 
    proof 
      fix io assume "io \<in> R M2 s vs xs"
      then have "s \<in> io_targets M2 (initial M2) io" by auto
      moreover have "io \<in> language_state M2 (initial M2)" using calculation by auto
      ultimately show "io_targets M2 (initial M2) io = {s}" using assms(3) io_targets_observable_singleton_ex by (metis singletonD) 
    qed

  moreover have "\<forall> io \<in> R M2 s vs xs . io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io"
    proof 
      fix io assume io_assm : "io \<in> R M2 s vs xs" 
      then have io_prefix : "prefix io (vs @ xs)" by auto
      then have io_lang_subs : "io \<in> L M1 \<and> io \<in> L M2" using assms(1) unfolding prefix_def by (metis IntE language_state language_state_split) 
      then have io_lang_inter : "io \<in> L M1 \<inter> L M2" by simp
      then have io_lang_pm : "io \<in> L PM" using productF_language assms by blast 
      moreover obtain p2 p1 where "(p2,p1) \<in> io_targets PM (initial PM) io" by (metis assms(2) assms(3) assms(7) calculation insert_absorb insert_ident insert_not_empty io_targets_observable_singleton_ob observable_productF singleton_insert_inj_eq subrelI) 
      ultimately have targets_pm : "io_targets PM (initial PM) io = {(p2,p1)}" using assms io_targets_observable_singleton_ex singletonD by (metis observable_productF) 
      then obtain trP where trP_def : "target (io || trP) (initial PM) = (p2,p1) \<and> path PM (io || trP) (initial PM) \<and> length io = length trP"
        proof -
          assume a1: "\<And>trP. target (io || trP) (initial PM) = (p2, p1) \<and> path PM (io || trP) (initial PM) \<and> length io = length trP \<Longrightarrow> thesis"
          have "\<exists>ps. target (io || ps) (initial PM) = (p2, p1) \<and> path PM (io || ps) (initial PM) \<and> length io = length ps"
            using \<open>(p2, p1) \<in> io_targets PM (initial PM) io\<close> by auto
          then show ?thesis
            using a1 by blast
        qed 
      then have trP_unique : "{ tr . path PM (io || tr) (initial PM) \<and> length io = length tr } = { trP }" 
        using observable_productF observable_path_unique_ex[of PM io "initial PM"] io_lang_pm assms(2) assms(3) assms(7)
        proof -
          obtain pps :: "('d \<times> 'c) list" where
            f1: "{ps. path PM (io || ps) (initial PM) \<and> length io = length ps} = {pps} \<or> \<not> observable PM"
            by (metis (no_types) \<open>\<And>thesis. \<lbrakk>observable PM; io \<in> L PM; \<And>tr. {t. path PM (io || t) (initial PM) \<and> length io = length t} = {tr} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> io_lang_pm)
          have f2: "observable PM"
            by (meson \<open>observable M1\<close> \<open>observable M2\<close> \<open>productF M2 M1 FAIL PM\<close> observable_productF)
          then have "trP \<in> {pps}"
            using f1 trP_def by blast
          then show ?thesis
            using f2 f1 by force
        qed
       
      
      obtain trIO2 where trIO2_def : "{ tr . path M2 (io || tr) (initial M2) \<and> length io = length tr } = { trIO2 }" using observable_path_unique_ex[of M2 io "initial M2"] io_lang_subs assms(3) by blast
      obtain trIO1 where trIO1_def : "{ tr . path M1 (io || tr) (initial M1) \<and> length io = length tr } = { trIO1 }" using observable_path_unique_ex[of M1 io "initial M1"] io_lang_subs assms(2) by blast
  
      have "path PM (io || trIO2 || trIO1) (initial M2, initial M1) \<and> length io = length trIO2 \<and> length trIO2 = length trIO1" using trIO2_def trIO1_def
      proof -
        have f1: "path M2 (io || trIO2) (initial M2) \<and> length io = length trIO2" using trIO2_def by auto
        have f2: "path M1 (io || trIO1) (initial M1) \<and> length io = length trIO1" using trIO1_def by auto
        then have "length trIO2 = length trIO1" using f1 by presburger
        then show ?thesis using f2 f1 assms(4) assms(5) assms(7) by blast
      qed 
      then have trP_split : "path PM (io || trIO2 || trIO1) (initial PM) \<and> length io = length trIO2 \<and> length trIO2 = length trIO1" using assms(7) by auto 
      then have trP_zip : "trIO2 || trIO1 = trP" using trP_def trP_unique using length_zip by fastforce 
  
      have "target (io || trIO2) (initial M2) = p2 \<and> path M2 (io || trIO2) (initial M2) \<and> length io = length trIO2" using trP_zip trP_split assms(7) trP_def trIO2_def by auto 
      then have "p2 \<in> io_targets M2 (initial M2) io" by auto
      then have targets_2 : "io_targets M2 (initial M2) io = {p2}" by (metis state_component_2 io_assm singletonD)   
  
      have "target (io || trIO1) (initial M1) = p1 \<and> path M1 (io || trIO1) (initial M1) \<and> length io = length trIO1" using trP_zip trP_split assms(7) trP_def trIO1_def by auto 
      then have "p1 \<in> io_targets M1 (initial M1) io" by auto
      then have targets_1 : "io_targets M1 (initial M1) io = {p1}" by (metis io_lang_subs assms(2) io_targets_observable_singleton_ex singletonD) 
  
      have "io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io = {(p2,p1)}" using targets_2 targets_1 by simp
      then show "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" using targets_pm by simp
    qed

  ultimately have state_components : "\<forall> io \<in> R M2 s vs xs . io_targets PM (initial PM) io = {s} \<times> io_targets M1 (initial M1) io" by auto

  then have "\<Union> (image (io_targets PM (initial PM)) (R M2 s vs xs)) = \<Union> (image (\<lambda> io . {s} \<times> io_targets M1 (initial M1) io) (R M2 s vs xs))" by auto
  then have "\<Union> (image (io_targets PM (initial PM)) (R M2 s vs xs)) = {s} \<times> \<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))" by auto
  then have "card (\<Union> (image (io_targets PM (initial PM)) (R M2 s vs xs))) = card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs)))" by (metis (no_types) card_cartesian_product_singleton)

  moreover have "card (\<Union> (image (io_targets PM (initial PM)) (R M2 s vs xs))) = card (R M2 s vs xs)"
  proof (rule ccontr)
    assume assm : "card (UNION (R M2 s vs xs) (io_targets PM (initial PM))) \<noteq> card (R M2 s vs xs)"

    have "\<forall> io \<in> R M2 s vs xs . io \<in> L PM" 
    proof 
      fix io assume io_assm : "io \<in> R M2 s vs xs" 
      then have "prefix io (vs @ xs)" by auto
      then have "io \<in> L M1 \<and> io \<in> L M2" using assms(1) unfolding prefix_def by (metis IntE language_state language_state_split) 
      then show "io \<in> L PM" using productF_language assms by blast 
    qed
    then have singletons : "\<forall> io \<in> R M2 s vs xs . (\<exists> t . io_targets PM (initial PM) io = {t})" using io_targets_observable_singleton_ex observable_productF assms by metis 
    then have card_targets : "card (UNION (R M2 s vs xs) (io_targets PM (initial PM))) = card (image (io_targets PM (initial PM)) (R M2 s vs xs))" using finite_R card_union_of_singletons[of "image (io_targets PM (initial PM)) (R M2 s vs xs)"] by simp
    
    moreover have "card (image (io_targets PM (initial PM)) (R M2 s vs xs)) \<le> card (R M2 s vs xs)" using finite_R by (metis card_image_le)
    ultimately have card_le : "card (UNION (R M2 s vs xs) (io_targets PM (initial PM))) < card (R M2 s vs xs)" using assm by linarith 

    have "\<exists> io1 \<in> (R M2 s vs xs) . \<exists> io2 \<in> (R M2 s vs xs) . io1 \<noteq> io2 \<and> io_targets PM (initial PM) io1 \<inter> io_targets PM (initial PM) io2 \<noteq> {}"  
    proof (rule ccontr)
      assume "\<not> (\<exists>io1\<in>R M2 s vs xs. \<exists>io2\<in>R M2 s vs xs. io1 \<noteq> io2 \<and> io_targets PM (initial PM) io1 \<inter> io_targets PM (initial PM) io2 \<noteq> {})"
      then have "\<forall>io1\<in>R M2 s vs xs. \<forall>io2\<in>R M2 s vs xs. io1 = io2 \<or> io_targets PM (initial PM) io1 \<inter> io_targets PM (initial PM) io2 = {}" by blast
      moreover have "\<forall>io\<in>R M2 s vs xs. io_targets PM (initial PM) io \<noteq> {}" by (metis insert_not_empty singletons)
      ultimately have "card (image (io_targets PM (initial PM)) (R M2 s vs xs)) = card (R M2 s vs xs)" using finite_R[of M2 s vs xs] card_union_of_distinct[of "R M2 s vs xs" "(io_targets PM (initial PM))"] by blast 
      then show "False" using card_le card_targets by linarith 
    qed

    then have "\<exists> io1 io2 . io1 \<in> (R M2 s vs xs) \<and> io2 \<in> (R M2 s vs xs) \<and> io1 \<noteq> io2 \<and> io_targets PM (initial PM) io1 \<inter> io_targets PM (initial PM) io2 \<noteq> {}" by blast
    moreover have "\<forall> io1 io2 . (io1 \<in> (R M2 s vs xs) \<and> io2 \<in> (R M2 s vs xs) \<and> io1 \<noteq> io2) \<longrightarrow> length io1 \<noteq> length io2" 
     proof (rule ccontr)
       assume " \<not> (\<forall>io1 io2. io1 \<in> R M2 s vs xs \<and> io2 \<in> R M2 s vs xs \<and> io1 \<noteq> io2 \<longrightarrow> length io1 \<noteq> length io2)"
       then obtain io1 io2 where io_def : "io1 \<in> R M2 s vs xs \<and> io2 \<in> R M2 s vs xs \<and> io1 \<noteq> io2 \<and> length io1 = length io2" by auto
       then have "prefix io1 (vs @ xs) \<and> prefix io2 (vs @ xs)" by auto
       then have "io1 = take (length io1) (vs @ xs) \<and> io2 = take (length io2) (vs @ xs)" by (metis append_eq_conv_conj prefixE) 
       then show "False" using io_def by auto
     qed
  
    ultimately obtain io1 io2 where rep_ios_def : "io1 \<in> (R M2 s vs xs) \<and> io2 \<in> (R M2 s vs xs) \<and> length io1 < length io2 \<and> io_targets PM (initial PM) io1 \<inter> io_targets PM (initial PM) io2 \<noteq> {}" by (metis inf_sup_aci(1) linorder_neqE_nat)
    then obtain rep where rep_state : "io_targets PM (initial PM) io1 = {(s,rep)} \<and> io_targets PM (initial PM) io2 = {(s,rep)}" using singletons by (smt SigmaE disjoint_iff_not_equal singletonD state_components)   

    obtain io1X io2X where rep_ios_split : "io1 = vs @ io1X \<and> prefix io1X xs \<and> io2 = vs @ io2X \<and> prefix io2X xs" using rep_ios_def by auto
    then have "length io1 > length vs" using rep_ios_def by auto

    (* path from init to (q2,q1) *)

    have "vs \<in> L PM" using assms by auto
    then obtain trV where trV_def : "{ tr . path PM (vs || tr) (initial PM) \<and> length vs = length tr } = { trV }" using observable_path_unique_ex[of PM vs "initial PM"] assms(2) assms(3) assms(7) observable_productF by blast
    let ?qv = "target (vs || trV) (initial PM)"
    
    have "?qv \<in> io_targets PM (initial PM) vs" using trV_def by auto
    then have qv_simp[simp] : "?qv = (q2,q1)" using singletons assms by blast
    then have "?qv \<in> nodes PM" using trV_def assms by blast  
   
    (* path from ?qv by io1X *)

    obtain tr1X_all where tr1X_all_def : "path PM (vs @ io1X || tr1X_all) (initial PM) \<and> length (vs @ io1X) = length tr1X_all" using rep_ios_def rep_ios_split by auto 
    let ?tr1X = "drop (length vs) tr1X_all"
    have "take (length vs) tr1X_all = trV" 
    proof -
      have "path PM (vs || take (length vs) tr1X_all) (initial PM) \<and> length vs = length (take (length vs) tr1X_all)" using tr1X_all_def trV_def
        by (metis (no_types, lifting) FSM.path_append_elim append_eq_conv_conj length_take zip_append1)
      then show "take (length vs) tr1X_all = trV" using trV_def by blast
    qed
    then have tr1X_def : "path PM (io1X || ?tr1X) ?qv \<and> length io1X = length ?tr1X" using tr1X_all_def
    proof -
      have "length tr1X_all = length vs + length io1X" using tr1X_all_def by auto
      then have "length io1X = length tr1X_all - length vs" by presburger
      then show ?thesis by (metis (no_types) FSM.path_append_elim \<open>take (length vs) tr1X_all = trV\<close> length_drop tr1X_all_def zip_append1)
    qed  
    then have io1X_lang : "io1X \<in> language_state PM ?qv" by auto
    then obtain tr1X' where tr1X'_def : "{ tr . path PM (io1X || tr) ?qv \<and> length io1X = length tr } = { tr1X' }" using observable_path_unique_ex[of PM io1X ?qv] assms(2) assms(3) assms(7) observable_productF by blast
    moreover have "?tr1X \<in> { tr . path PM (io1X || tr) ?qv \<and> length io1X = length tr }" using tr1X_def by auto
    ultimately have tr1x_unique : "tr1X' = ?tr1X" by simp
 
    (* path from ?qv by io2X *) 

    obtain tr2X_all where tr2X_all_def : "path PM (vs @ io2X || tr2X_all) (initial PM) \<and> length (vs @ io2X) = length tr2X_all" using rep_ios_def rep_ios_split by auto 
    let ?tr2X = "drop (length vs) tr2X_all"
    have "take (length vs) tr2X_all = trV" 
    proof -
      have "path PM (vs || take (length vs) tr2X_all) (initial PM) \<and> length vs = length (take (length vs) tr2X_all)" using tr2X_all_def trV_def
        by (metis (no_types, lifting) FSM.path_append_elim append_eq_conv_conj length_take zip_append1)
      then show "take (length vs) tr2X_all = trV" using trV_def by blast
    qed
    then have tr2X_def : "path PM (io2X || ?tr2X) ?qv \<and> length io2X = length ?tr2X" using tr1X_all_def
    proof -
      have "length tr2X_all = length vs + length io2X" using tr2X_all_def by auto
      then have "length io2X = length tr2X_all - length vs" by presburger
      then show ?thesis by (metis (no_types) FSM.path_append_elim \<open>take (length vs) tr2X_all = trV\<close> length_drop tr2X_all_def zip_append1)
    qed  
    then have io2X_lang : "io2X \<in> language_state PM ?qv" by auto
    then obtain tr2X' where tr2X'_def : "{ tr . path PM (io2X || tr) ?qv \<and> length io2X = length tr } = { tr2X' }" using observable_path_unique_ex[of PM io2X ?qv] assms(2) assms(3) assms(7) observable_productF by blast
    moreover have "?tr2X \<in> { tr . path PM (io2X || tr) ?qv \<and> length io2X = length tr }" using tr2X_def by auto
    ultimately have tr2x_unique : "tr2X' = ?tr2X" by simp

    (* both reach same state in PM *)

    have "io_targets PM (initial PM) (vs @ io1X) = {(s,rep)}" using rep_state rep_ios_split by auto
    moreover have "io_targets PM (initial PM) vs = {?qv}" using assms(8) by auto 
    ultimately have rep_via_1 : "io_targets PM ?qv io1X = {(s,rep)}" by (meson obs_PM observable_io_targets_split) 
    then have rep_tgt_1 : "target (io1X || tr1X') ?qv = (s,rep)" using obs_PM observable_io_target_unique_target[of PM ?qv io1X "(s,rep)"] tr1X'_def by blast 
    have length_1 : "length (io1X || tr1X') > 0" using \<open>length vs < length io1\<close> rep_ios_split tr1X_def tr1x_unique by auto
    
    have tr1X_alt_def : "tr1X' = take (length io1X) tr" by (metis (no_types) assms(10) assms(9) obs_PM observable_path_prefix qv_simp rep_ios_split tr1X_def tr1x_unique)
    moreover have "io1X = take (length io1X) xs" using rep_ios_split by (metis append_eq_conv_conj prefixE)
    ultimately have "(io1X || tr1X') = take (length io1X) (xs || tr)" by (metis take_zip) 
    moreover have "length (xs || tr) \<ge> length (io1X || tr1X')"
      by (metis (no_types) \<open>io1X = take (length io1X) xs\<close> assms(10) length_take length_zip nat_le_linear take_all tr1X_def tr1x_unique) 
    ultimately have rep_idx_1 : "(states (xs || tr) ?qv) ! ((length io1X) - 1) = (s,rep)"
      by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred rep_tgt_1 length_1 less_Suc_eq_le map_snd_zip scan_length scan_nth states_alt_def tr1X_def tr1x_unique) 


    have "io_targets PM (initial PM) (vs @ io2X) = {(s,rep)}" using rep_state rep_ios_split by auto
    moreover have "io_targets PM (initial PM) vs = {?qv}" using assms(8) by auto 
    ultimately have rep_via_2 : "io_targets PM ?qv io2X = {(s,rep)}" by (meson obs_PM observable_io_targets_split) 
    then have rep_tgt_2 : "target (io2X || tr2X') ?qv = (s,rep)" using obs_PM observable_io_target_unique_target[of PM ?qv io2X "(s,rep)"] tr2X'_def by blast 
    moreover have length_2 : "length (io2X || tr2X') > 0" by (metis \<open>length vs < length io1\<close> append.right_neutral length_0_conv length_zip less_asym min.idem neq0_conv rep_ios_def rep_ios_split tr2X_def tr2x_unique)
    
    have tr2X_alt_def : "tr2X' = take (length io2X) tr" by (metis (no_types) assms(10) assms(9) obs_PM observable_path_prefix qv_simp rep_ios_split tr2X_def tr2x_unique)
    moreover have "io2X = take (length io2X) xs" using rep_ios_split by (metis append_eq_conv_conj prefixE)
    ultimately have "(io2X || tr2X') = take (length io2X) (xs || tr)" by (metis take_zip) 
    moreover have "length (xs || tr) \<ge> length (io2X || tr2X')" using calculation by auto 
    ultimately have rep_idx_2 : "(states (xs || tr) ?qv) ! ((length io2X) - 1) = (s,rep)"
      by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred rep_tgt_2 length_2 less_Suc_eq_le map_snd_zip scan_length scan_nth states_alt_def tr2X_def tr2x_unique) 

    (* then (xs||tr) repeats a state *)

    have "length io1X \<noteq> length io2X" by (metis \<open>io1X = take (length io1X) xs\<close> \<open>io2X = take (length io2X) xs\<close> less_irrefl rep_ios_def rep_ios_split) 
    moreover have "(states (xs || tr) ?qv) ! ((length io1X) - 1) = (states (xs || tr) ?qv) ! ((length io2X) - 1)" using rep_idx_1 rep_idx_2 by simp
    ultimately have "\<not> (distinct (states (xs || tr) ?qv))" by (metis Suc_less_eq \<open>io1X = take (length io1X) xs\<close> \<open>io1X || tr1X' = take (length io1X) (xs || tr)\<close> \<open>io2X = take (length io2X) xs\<close> \<open>io2X || tr2X' = take (length io2X) (xs || tr)\<close> \<open>length (io1X || tr1X') \<le> length (xs || tr)\<close> \<open>length (io2X || tr2X') \<le> length (xs || tr)\<close> assms(10) diff_Suc_1 distinct_conv_nth gr0_conv_Suc le_imp_less_Suc length_1 length_2 length_take map_snd_zip scan_length states_alt_def) 
    then show "False" by (metis assms(11) states_alt_def) 
  qed

  ultimately show ?thesis by linarith 
qed 


(* V' *)
fun Perm :: "'in list set \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> ('in \<times> 'out) list set set" where
  "Perm V M = {image f V | f . \<forall> v \<in> V . f v \<in> language_state_for_input M (initial M) v }"

lemma perm_empty :
  assumes "is_det_state_cover M V"
  and "V'' \<in> Perm V M"
shows "[] \<in> V''"
proof -
  have init_seq : "[] \<in> V" using det_state_cover_empty assms by simp
  obtain f where f_def : "V'' = image f V \<and> (\<forall> v \<in> V . f v \<in> language_state_for_input M (initial M) v)" using assms by auto
  then have "f [] = []" using init_seq by (metis language_state_for_input_empty singleton_iff) 
  then show ?thesis using init_seq f_def by (metis image_eqI) 
qed

lemma perm_elem_finite :
  assumes "is_det_state_cover M2 V"
  and     "well_formed M2"
  and     "V'' \<in> Perm V M1"
  shows "finite V''"
proof -
  obtain f where "is_det_state_cover_ass M2 f \<and> V = f ` d_reachable M2 (initial M2)" using assms by auto
  moreover have "finite (d_reachable M2 (initial M2))" 
  proof -
    have "finite (nodes M2)" using assms by auto
    moreover have "nodes M2 = reachable M2 (initial M2)" by auto
    ultimately have "finite (reachable M2 (initial M2))" by simp
    moreover have "d_reachable M2 (initial M2) \<subseteq> reachable M2 (initial M2)" by auto
    ultimately show ?thesis using infinite_super by blast 
  qed
  ultimately have "finite V" by auto
  moreover obtain f'' where "V'' = image f'' V \<and> (\<forall> v \<in> V . f'' v \<in> language_state_for_input M1 (initial M1) v)" using assms(3) by auto 
  ultimately show ?thesis by simp
qed

lemma perm_inputs :
  assumes "V'' \<in> Perm V M"
  and     "vs \<in> V''"
shows "map fst vs \<in> V"
proof -
  obtain f where f_def : "V'' = image f V \<and> (\<forall> v \<in> V . f v \<in> language_state_for_input M (initial M) v)" using assms by auto
  then obtain v where v_def : "v \<in> V \<and> f v = vs" using assms by auto
  then have "vs \<in> language_state_for_input M (initial M) v" using f_def by auto
  then show ?thesis using v_def unfolding language_state_for_input.simps by auto
qed

lemma perm_inputs_diff :
  assumes "V'' \<in> Perm V M"
  and     "vs1 \<in> V''"
  and     "vs2 \<in> V''"
  and     "vs1 \<noteq> vs2"
shows "map fst vs1 \<noteq> map fst vs2"
proof -
  obtain f where f_def : "V'' = image f V \<and> (\<forall> v \<in> V . f v \<in> language_state_for_input M (initial M) v)" using assms by auto
  then obtain v1 v2 where v_def : "v1 \<in> V \<and> f v1 = vs1 \<and> v2 \<in> V \<and> f v2 = vs2" using assms by auto
  then have "vs1 \<in> language_state_for_input M (initial M) v1"
            "vs2 \<in> language_state_for_input M (initial M) v2" using f_def by auto
  moreover have "v1 \<noteq> v2" using v_def using assms(4) by blast 
  ultimately show ?thesis by auto
qed

lemma perm_language :
  assumes "V'' \<in> Perm V M"
  and     "vs \<in> V''"
shows "vs \<in> L M"
proof -
  obtain f where f_def : "image f V = V'' \<and> (\<forall> v \<in> V . f v \<in> language_state_for_input M (initial M) v)" using assms(1) by auto
  then have "\<exists> v . f v = vs \<and> f v \<in> language_state_for_input M (initial M) v" using assms(2) by blast 
  then show ?thesis by auto
qed

(* TODO: show that Perm sets used during testing actually exist *)
(*
lemma perm_nonempty : 
  assumes "is_det_state_cover M2 V"
  and "completely_specified M1"
  and "inputs M1 = inputs M2"
shows "Perm V M1 \<noteq> {}"
*)


(* R\<^sup>+ *)
fun RP :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> ('in \<times> 'out) list set" where
  "RP M s vs xs V'' = R M s vs xs \<union> {vs' \<in> V'' . io_targets M (initial M) vs' = {s}}"

lemma RP_from_R:
  assumes "is_det_state_cover M2 V"
  and     "V'' \<in> Perm V M1"
shows "RP M2 s vs xs V'' = R M2 s vs xs \<or> (\<exists> vs' \<in> V'' . vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs))" 
proof (rule ccontr)
  assume assm : "\<not> (RP M2 s vs xs V'' = R M2 s vs xs \<or>
        (\<exists>vs'\<in>V''. vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs)))"
 
  moreover have "R M2 s vs xs \<subseteq> RP M2 s vs xs V''" by simp
  moreover have "RP M2 s vs xs V'' \<subseteq> R M2 s vs xs \<union> V''" by auto
  ultimately obtain vs1 vs2 where vs_def : 
       "vs1 \<noteq> vs2 \<and> vs1 \<in> V'' \<and> vs2 \<in> V'' \<and> vs1 \<notin> R M2 s vs xs \<and> vs2 \<notin> R M2 s vs xs \<and> vs1 \<in> RP M2 s vs xs V'' \<and> vs2 \<in> RP M2 s vs xs V''" by blast 

  then have "io_targets M2 (initial M2) vs1 = {s} \<and> io_targets M2 (initial M2) vs2 = {s}" by (metis (mono_tags, lifting) RP.simps Un_iff mem_Collect_eq) 
  then have "io_targets M2 (initial M2) vs1 = io_targets M2 (initial M2) vs2" by simp
 
  obtain f where f_def : "is_det_state_cover_ass M2 f \<and> V = f ` d_reachable M2 (initial M2)" using assms by auto
  moreover have "V = image f (d_reachable M2 (initial M2))" using f_def by blast 
  moreover have "map fst vs1 \<in> V \<and> map fst vs2 \<in> V" using assms(2) perm_inputs vs_def by blast
  ultimately obtain r1 r2 where r_def : 
    "f r1 = map fst vs1 \<and> r1 \<in> d_reachable M2 (initial M2)"
    "f r2 = map fst vs2 \<and> r2 \<in> d_reachable M2 (initial M2)" by force 
  then have "d_reaches M2 (initial M2) (map fst vs1) r1"
            "d_reaches M2 (initial M2) (map fst vs2) r2" by (metis f_def is_det_state_cover_ass.elims(2))+ 

  then have "io_targets M2 (initial M2) vs1 \<subseteq> {r1}" using d_reaches_io_target[of M2 "initial M2" "map fst vs1" r1 "map snd vs1"] by simp
  moreover have "io_targets M2 (initial M2) vs2 \<subseteq> {r2}" using d_reaches_io_target[of M2 "initial M2" "map fst vs2" r2 "map snd vs2"] \<open>d_reaches M2 (initial M2) (map fst vs2) r2\<close> by auto 
  ultimately have "r1 = r2" using \<open>io_targets M2 (initial M2) vs1 = {s} \<and> io_targets M2 (initial M2) vs2 = {s}\<close> by auto 

  have "map fst vs1 \<noteq> map fst vs2" using assms(2) perm_inputs_diff vs_def by blast 
  then have "r1 \<noteq> r2" using r_def(1) r_def(2) by force  

  then show "False" using \<open>r1 = r2\<close> by auto
qed 

lemma finite_RP : 
  assumes "is_det_state_cover M2 V"
  and     "V'' \<in> Perm V M1"
shows "finite (RP M2 s vs xs V'')"
  using assms RP_from_R finite_R by (metis finite_insert) 
  



(* Lemma 5.4.8 *)
lemma RP_count :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "distinct (states (xs || tr) (q2,q1))" 
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "\<forall> s' \<in> set (states (xs || map fst tr) q2) . \<not> (\<exists> v \<in> V . d_reaches M2 (initial M2) v s')" 
shows "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (RP M2 s vs xs V'')"
proof -
  have RP_cases : "RP M2 s vs xs V'' = R M2 s vs xs \<or> (\<exists> vs' \<in> V'' . vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs))" using RP_from_R assms by metis
  show ?thesis 
  proof (cases "RP M2 s vs xs V'' = R M2 s vs xs")
    case True
    then show ?thesis using R_count assms by metis
  next
    case False
    then obtain vs' where vs'_def : "vs' \<in> V'' \<and> vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs)" using RP_cases by auto
    

    have obs_PM : "observable PM" using observable_productF assms(2) assms(3) assms(7) by blast

    have state_component_2 : "\<forall> io \<in> (R M2 s vs xs) . io_targets M2 (initial M2) io = {s}" 
      proof 
        fix io assume "io \<in> R M2 s vs xs"
        then have "s \<in> io_targets M2 (initial M2) io" by auto
        moreover have "io \<in> language_state M2 (initial M2)" using calculation by auto
        ultimately show "io_targets M2 (initial M2) io = {s}" using assms(3) io_targets_observable_singleton_ex by (metis singletonD) 
      qed

    have "vs' \<in> L M1" using assms(13) perm_language vs'_def by blast
    then obtain s' where s'_def : "io_targets M1 (initial M1) vs' = {s'}" by (meson assms(2) io_targets_observable_singleton_ob) 

    moreover have "s' \<notin> \<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))" 
    proof (rule ccontr)
      assume "\<not> s' \<notin> UNION (R M2 s vs xs) (io_targets M1 (initial M1))"
      then obtain xs' where xs'_def : "vs @ xs' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (vs @ xs')"
      proof -
        assume a1: "\<And>xs'. vs @ xs' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (vs @ xs') \<Longrightarrow> thesis"
        obtain pps :: "('a \<times> 'b) list set \<Rightarrow> (('a \<times> 'b) list \<Rightarrow> 'c set) \<Rightarrow> 'c \<Rightarrow> ('a \<times> 'b) list" where
          "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 \<in> x1 v3) = (pps x0 x1 x2 \<in> x0 \<and> x2 \<in> x1 (pps x0 x1 x2))"
          by moura
        then have f2: "pps (R M2 s vs xs) (io_targets M1 (initial M1)) s' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (pps (R M2 s vs xs) (io_targets M1 (initial M1)) s')"
          using \<open>\<not> s' \<notin> UNION (R M2 s vs xs) (io_targets M1 (initial M1))\<close> by blast
        then have "\<exists>ps. pps (R M2 s vs xs) (io_targets M1 (initial M1)) s' = vs @ ps \<and> ps \<noteq> [] \<and> prefix ps xs \<and> s \<in> io_targets M2 (initial M2) (vs @ ps)"
          by simp
        then show ?thesis
          using f2 a1 by (metis (no_types))
      qed  
      then obtain tr' where tr'_def : "path M2 (vs @ xs' || tr') (initial M2) \<and> length tr' = length (vs @ xs')" by auto

      then obtain trV' trX' where tr'_split : "trV' = take (length vs) tr'" "trX' = drop (length vs) tr'" "tr' = trV' @ trX'" by fastforce 
      then have "path M2 (vs || trV') (initial M2) \<and> length trV' = length vs" by (metis (no_types) FSM.path_append_elim \<open>trV' = take (length vs) tr'\<close> append_eq_conv_conj length_take tr'_def zip_append1)
            

      

      have "initial PM = (initial M2, initial M1)" using assms(7) by simp
      moreover have "vs \<in> L M2" "vs \<in> L M1" using assms(1) language_state_prefix by auto
      ultimately have "io_targets M1 (initial M1) vs = {q1}" "io_targets M2 (initial M2) vs = {q2}" using productF_path_io_targets[of M2 M1 FAIL PM "initial M2" "initial M1" vs q2 q1] by (metis FSM.nodes.initial assms(7) assms(8) assms(2) assms(3) assms(4) assms(5) io_targets_observable_singleton_ex singletonD)+ 

      then have "target (vs || trV') (initial M2) = q2" using \<open>path M2 (vs || trV') (initial M2) \<and> length trV' = length vs\<close> io_target_target by metis
      then have path_xs' : "path M2 (xs' || trX') q2 \<and> length trX' = length xs'" by (metis (no_types) FSM.path_append_elim \<open>path M2 (vs || trV') (initial M2) \<and> length trV' = length vs\<close> \<open>target (vs || trV') (initial M2) = q2\<close> append_eq_conv_conj length_drop tr'_def tr'_split(1) tr'_split(2) zip_append2)
      
      
      have "io_targets M2 (initial M2) (vs @ xs') = {s}" using state_component_2 xs'_def by blast
      then have "io_targets M2 q2 xs' = {s}" by (meson assms(3) observable_io_targets_split \<open>io_targets M2 (initial M2) vs = {q2}\<close>) 
      then have target_xs' : "target (xs' || trX') q2 = s" using io_target_target path_xs' by metis
      moreover have "length xs' > 0" using xs'_def by auto
      ultimately have "last (states (xs' || trX') q2) = s" using path_xs' target_in_states by metis
      moreover have "length (states (xs' || trX') q2) > 0" using \<open>0 < length xs'\<close> path_xs' by auto 
      ultimately have states_xs' : "s \<in> set (states (xs' || trX') q2)" using last_in_set by blast

      have "vs @ xs \<in> L M2" using assms by simp
      then obtain q' where "io_targets M2 (initial M2) (vs@xs) = {q'}" using io_targets_observable_singleton_ob[of M2 "vs@xs" "initial M2"] assms(3) by auto
      then have "xs \<in> language_state M2 q2" using assms(3) \<open>io_targets M2 (initial M2) vs = {q2}\<close> observable_io_targets_split[of M2 "initial M2" vs xs q' q2] by auto

      moreover have "path PM (xs || map fst tr || map snd tr) (q2,q1) \<and> length xs = length (map fst tr)" using assms(7) assms(9) assms(10) productF_path_unzip by simp
      moreover have "xs \<in> language_state PM (q2,q1)" using assms(9) assms(10) by auto
      moreover have "q2 \<in> nodes M2" using \<open>io_targets M2 (initial M2) vs = {q2}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1) 
      moreover have "q1 \<in> nodes M1" using \<open>io_targets M1 (initial M1) vs = {q1}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1)
      ultimately have path_xs : "path M2 (xs || map fst tr) q2" using productF_path_reverse_ob_2(1)[of xs "map fst tr" "map snd tr" M2 M1 FAIL PM q2 q1] assms(2,3,4,5,7) by simp

      

      moreover have "prefix xs' xs" using xs'_def by auto
      ultimately have "trX' = take (length xs') (map fst tr)"
        using \<open>path PM (xs || map fst tr || map snd tr) (q2, q1) \<and> length xs = length (map fst tr)\<close> assms(3) path_xs'
        by (metis observable_path_prefix) 

      then have states_xs : "s \<in> set (states (xs || map fst tr) q2)" by (metis assms(10) in_set_takeD length_map map_snd_zip path_xs' states_alt_def states_xs') 

      
      
      have "d_reaches M2 (initial M2) (map fst vs') s"
      proof -
        obtain fV where fV_def : "is_det_state_cover_ass M2 fV \<and> V = fV ` d_reachable M2 (initial M2)" using assms(12) by auto
        moreover have "V = image fV (d_reachable M2 (initial M2))" using fV_def by blast 
        moreover have "map fst vs' \<in> V" using perm_inputs vs'_def assms(13) by metis
        ultimately obtain qv where qv_def : "fV qv = map fst vs' \<and> qv \<in> d_reachable M2 (initial M2)" by force
        then have "d_reaches M2 (initial M2) (map fst vs') qv" by (metis fV_def is_det_state_cover_ass.elims(2))
        then have "io_targets M2 (initial M2) vs' \<subseteq> {qv}" using d_reaches_io_target[of M2 "initial M2" "map fst vs'" qv "map snd vs'"] by simp
        moreover have "io_targets M2 (initial M2) vs' = {s}" using vs'_def by (metis (mono_tags, lifting) RP.simps Un_iff insertI1 mem_Collect_eq)
        ultimately have "qv = s" by simp
        then show ?thesis using \<open>d_reaches M2 (initial M2) (map fst vs') qv\<close> by blast 
      qed
      
      then show "False"  by (meson assms(14) assms(13) perm_inputs states_xs vs'_def)
    qed 

    moreover have "\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs)))
      = insert s' (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs)))" using s'_def by simp

    moreover have "finite (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs)))" 
    proof 
      show "finite (R M2 s vs xs)" using finite_R by simp
      show "\<And>a. a \<in> R M2 s vs xs \<Longrightarrow> finite (io_targets M1 (initial M1) a)" 
      proof -
        fix a assume "a \<in> R M2 s vs xs" 
        then have "prefix a (vs@xs)" by auto
        then have "a \<in> L M1" using language_state_prefix by (metis IntD1 assms(1) prefix_def) 
        then obtain p where "io_targets M1 (initial M1) a = {p}" using assms(2) io_targets_observable_singleton_ob by metis
        then show "finite (io_targets M1 (initial M1) a)" by simp
      qed
    qed

    ultimately have "card (\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs)))) = 
      Suc (card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))))" by (metis (no_types) card_insert_disjoint)

      
    moreover have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs))))" using vs'_def by simp
    
    ultimately have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = Suc (card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))))" by linarith

    then have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = Suc (card (R M2 s vs xs))" using R_count[of vs xs M1 M2 s FAIL PM q2 q1 tr] using assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) by linarith 

    moreover have "card (RP M2 s vs xs V'') = Suc (card (R M2 s vs xs))" using vs'_def by (metis card_insert_if finite_R)

    ultimately show ?thesis by linarith
  qed
qed






  


(* LB *)
fun LB :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> nat" where
  "LB M2 M1 vs xs T S \<Omega> V'' = (sum (\<lambda> s . card (RP M2 s vs xs V'')) S) 
                              + card ( (D M1 \<Omega> T) - {B M1 xs' \<Omega> | xs' s' . s' \<in> S \<and> xs' \<in> RP M2 s' vs xs V''})"


(* Prereq *)
fun Prereq :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> bool" where 
  "Prereq M2 M1 vs xs T S \<Omega> V V'' = (
    (\<forall> vs' \<in> V'' . (prefix vs' (vs @ xs) \<longrightarrow> length vs' \<le> length vs))      \<comment>\<open>(1.)\<close>
    \<and> (is_reduction_on_sets M1 M2 T \<Omega>)                                     \<comment>\<open>(2.) and (3.)\<close>
    \<and> V \<subseteq> T \<and> (\<forall> xs' . prefix xs' xs \<longrightarrow> map fst (vs @ xs') \<in> T)           \<comment>\<open>(4.)\<close>
    \<and> S \<subseteq> nodes M2                                                         \<comment>\<open>(addition, not strictly necessary as RP for any state not in (nodes M2) is empty)\<close>
    \<and> (\<forall> s1 \<in> S . \<forall> s2 \<in> S . s1 \<noteq> s2                                       \<comment>\<open>(5.)\<close>
        \<longrightarrow> (\<forall> seq1 \<in> RP M2 s1 vs xs V'' . \<forall> seq2 \<in> RP M2 s2 vs xs V'' . 
               \<forall> t1 \<in> io_targets M1 (initial M1) seq1 . \<forall> t2 \<in> io_targets M1 (initial M1) seq2 .  
                 r_dist_set M1 \<Omega> t1 t2)))"


(* Rep_pre *)
fun Rep_Pre :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "Rep_Pre M2 M1 vs xs = (\<exists> xs1 xs2 . xs1 \<noteq> [] \<and> prefix xs1 xs \<and> prefix xs2 xs \<and> xs1 \<noteq> xs2 
    \<and> (\<exists> s2 . io_targets M2 (initial M2) (vs @ xs1) = {s2} \<and> io_targets M2 (initial M2) (vs @ xs2) = {s2})
    \<and> (\<exists> s1 . io_targets M1 (initial M1) (vs @ xs1) = {s1} \<and> io_targets M1 (initial M1) (vs @ xs2) = {s1}))"




lemma distinctness_via_Rep_Pre :
  assumes "\<not> Rep_Pre M2 M1 vs xs"
  and "productF M2 M1 FAIL PM"
  and "observable M1"
  and "observable M2"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "well_formed M1"
  and "well_formed M2"
shows "distinct (states (xs || tr) (q2, q1))"
proof (rule ccontr)
  assume assm : "\<not> distinct (states (xs || tr) (q2, q1))"
  then obtain i1 i2 where index_def :
     "i1 \<noteq> 0 
      \<and> i1 \<noteq> i2 
      \<and> i1 < length (states (xs || tr) (q2, q1)) 
      \<and> i2 < length (states (xs || tr) (q2, q1)) 
      \<and> (states (xs || tr) (q2, q1)) ! i1 = (states (xs || tr) (q2, q1)) ! i2" by (metis distinct_conv_nth) 
  then have "length xs > 0" by auto
  
  let ?xs1 = "take (Suc i1) xs"
  let ?xs2 = "take (Suc i2) xs"
  let ?tr1 = "take (Suc i1) tr"
  let ?tr2 = "take (Suc i2) tr"
  let ?st  = "(states (xs || tr) (q2, q1)) ! i1"

  have obs_PM : "observable PM" using observable_productF assms(2) assms(3) assms(4) by blast

  have "initial PM = (initial M2, initial M1)" using assms(2) by simp
  moreover have "vs \<in> L M2" "vs \<in> L M1" using assms(8) language_state_prefix by auto
  ultimately have "io_targets M1 (initial M1) vs = {q1}" "io_targets M2 (initial M2) vs = {q2}" using productF_path_io_targets[of M2 M1 FAIL PM "initial M2" "initial M1" vs q2 q1] by (metis FSM.nodes.initial assms(2) assms(3) assms(4) assms(5) assms(9) assms(10) io_targets_observable_singleton_ex singletonD)+

  (* paths for ?xs1 *)
  
  have "(states (xs || tr) (q2, q1)) ! i1 \<in> io_targets PM (q2, q1) ?xs1" by (metis \<open>0 < length xs\<close> assms(6) assms(7) index_def map_snd_zip states_alt_def states_index_io_target)
  then have "io_targets PM (q2, q1) ?xs1 = {?st}" using obs_PM by (meson observable_io_target_is_singleton) 

  have "path PM (?xs1 || ?tr1) (q2,q1)" by (metis FSM.path_append_elim append_take_drop_id assms(6) assms(7) length_take zip_append) 
  then have "path PM (?xs1 || map fst ?tr1 || map snd ?tr1) (q2,q1)" by auto
  
  have "vs @ ?xs1 \<in> L M2" by (metis (no_types) IntD2 append_assoc append_take_drop_id assms(8) language_state_prefix) 
  then obtain q2' where "io_targets M2 (initial M2) (vs@?xs1) = {q2'}" using io_targets_observable_singleton_ob[of M2 "vs@?xs1" "initial M2"] assms(4) by auto
  then have "q2' \<in> io_targets M2 q2 ?xs1"
    using assms(4) \<open>io_targets M2 (initial M2) vs = {q2}\<close> observable_io_targets_split[of M2 "initial M2" vs ?xs1 q2' q2] by simp
  then have "?xs1 \<in> language_state M2 q2" by auto
  moreover have "length ?xs1 = length (map snd ?tr1)" using assms(7) by auto
  moreover have "length (map fst ?tr1) = length (map snd ?tr1)" by auto
  moreover have "q2 \<in> nodes M2" using \<open>io_targets M2 (initial M2) vs = {q2}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1) 
  moreover have "q1 \<in> nodes M1" using \<open>io_targets M1 (initial M1) vs = {q1}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1)
  ultimately have 
     "path M1 (?xs1 || map snd ?tr1) q1" 
     "path M2 (?xs1 || map fst ?tr1) q2" 
     "target (?xs1 || map snd ?tr1) q1 = snd (target (?xs1 || map fst ?tr1 || map snd ?tr1) (q2,q1))"
     "target (?xs1 || map fst ?tr1) q2 = fst (target (?xs1 || map fst ?tr1 || map snd ?tr1) (q2,q1))"
    using assms(2) assms(9) assms(10) \<open>path PM (?xs1 || map fst ?tr1 || map snd ?tr1) (q2,q1)\<close> assms(4) productF_path_reverse_ob_2[of ?xs1 "map fst ?tr1" "map snd ?tr1" M2 M1 FAIL PM q2 q1] by simp+
  moreover have "target (?xs1 || map fst ?tr1 || map snd ?tr1) (q2,q1) = ?st" by (metis (no_types) index_def scan_nth take_zip zip_map_fst_snd)
  ultimately have  
     "target (?xs1 || map snd ?tr1) q1 = snd ?st"
     "target (?xs1 || map fst ?tr1) q2 = fst ?st" by simp+  

  (* paths for ?xs2 *)
  
  have "(states (xs || tr) (q2, q1)) ! i2 \<in> io_targets PM (q2, q1) ?xs2" by (metis \<open>0 < length xs\<close> assms(6) assms(7) index_def map_snd_zip states_alt_def states_index_io_target)
  then have "io_targets PM (q2, q1) ?xs2 = {?st}" using obs_PM by (metis index_def observable_io_target_is_singleton)  

  have "path PM (?xs2 || ?tr2) (q2,q1)" by (metis FSM.path_append_elim append_take_drop_id assms(6) assms(7) length_take zip_append) 
  then have "path PM (?xs2 || map fst ?tr2 || map snd ?tr2) (q2,q1)" by auto

  have "vs @ ?xs2 \<in> L M2" by (metis (no_types) IntD2 append_assoc append_take_drop_id assms(8) language_state_prefix) 
  then obtain q2'' where "io_targets M2 (initial M2) (vs@?xs2) = {q2''}" using io_targets_observable_singleton_ob[of M2 "vs@?xs2" "initial M2"] assms(4) by auto
  then have "q2'' \<in> io_targets M2 q2 ?xs2"
    using assms(4) \<open>io_targets M2 (initial M2) vs = {q2}\<close> observable_io_targets_split[of M2 "initial M2" vs ?xs2 q2'' q2] by simp
  then have "?xs2 \<in> language_state M2 q2" by auto
  moreover have "length ?xs2 = length (map snd ?tr2)" using assms(7) by auto
  moreover have "length (map fst ?tr2) = length (map snd ?tr2)" by auto
  moreover have "q2 \<in> nodes M2" using \<open>io_targets M2 (initial M2) vs = {q2}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1) 
  moreover have "q1 \<in> nodes M1" using \<open>io_targets M1 (initial M1) vs = {q1}\<close> io_targets_nodes by (metis FSM.nodes.initial insertI1)
  ultimately have 
     "path M1 (?xs2 || map snd ?tr2) q1" 
     "path M2 (?xs2 || map fst ?tr2) q2" 
     "target (?xs2 || map snd ?tr2) q1 = snd (target (?xs2 || map fst ?tr2 || map snd ?tr2) (q2,q1))"
     "target (?xs2 || map fst ?tr2) q2 = fst (target (?xs2 || map fst ?tr2 || map snd ?tr2) (q2,q1))"
    using assms(2) assms(9) assms(10) \<open>path PM (?xs2 || map fst ?tr2 || map snd ?tr2) (q2,q1)\<close> assms(4) productF_path_reverse_ob_2[of ?xs2 "map fst ?tr2" "map snd ?tr2" M2 M1 FAIL PM q2 q1] by simp+
  moreover have "target (?xs2 || map fst ?tr2 || map snd ?tr2) (q2,q1) = ?st" by (metis (no_types) index_def scan_nth take_zip zip_map_fst_snd)
  ultimately have  
     "target (?xs2 || map snd ?tr2) q1 = snd ?st"
     "target (?xs2 || map fst ?tr2) q2 = fst ?st" by simp+

  

  have "io_targets M1 q1 ?xs1 = {snd ?st}" using \<open>path M1 (?xs1 || map snd ?tr1) q1\<close> \<open>target (?xs1 || map snd ?tr1) q1 = snd ?st\<close> \<open>length ?xs1 = length (map snd ?tr1)\<close> assms(3) obs_target_is_io_targets[of M1 ?xs1 "map snd ?tr1" q1] by simp
  then have tgt_1_1 : "io_targets M1 (initial M1) (vs @ ?xs1) = {snd ?st}" by (meson \<open>io_targets M1 (initial M1) vs = {q1}\<close> assms(3) observable_io_targets_append) 
  
  have "io_targets M2 q2 ?xs1 = {fst ?st}" using \<open>path M2 (?xs1 || map fst ?tr1) q2\<close> \<open>target (?xs1 || map fst ?tr1) q2 = fst ?st\<close> \<open>length ?xs1 = length (map snd ?tr1)\<close> assms(4) obs_target_is_io_targets[of M2 ?xs1 "map fst ?tr1" q2] by simp
  then have tgt_1_2 : "io_targets M2 (initial M2) (vs @ ?xs1) = {fst ?st}" by (meson \<open>io_targets M2 (initial M2) vs = {q2}\<close> assms(4) observable_io_targets_append)
  
  have "io_targets M1 q1 ?xs2 = {snd ?st}" using \<open>path M1 (?xs2 || map snd ?tr2) q1\<close> \<open>target (?xs2 || map snd ?tr2) q1 = snd ?st\<close> \<open>length ?xs2 = length (map snd ?tr2)\<close> assms(3) obs_target_is_io_targets[of M1 ?xs2 "map snd ?tr2" q1] by simp
  then have tgt_2_1 : "io_targets M1 (initial M1) (vs @ ?xs2) = {snd ?st}" by (meson \<open>io_targets M1 (initial M1) vs = {q1}\<close> assms(3) observable_io_targets_append)
  
  have "io_targets M2 q2 ?xs2 = {fst ?st}" using \<open>path M2 (?xs2 || map fst ?tr2) q2\<close> \<open>target (?xs2 || map fst ?tr2) q2 = fst ?st\<close> \<open>length ?xs2 = length (map snd ?tr2)\<close> assms(4) obs_target_is_io_targets[of M2 ?xs2 "map fst ?tr2" q2] by simp
  then have tgt_2_2 : "io_targets M2 (initial M2) (vs @ ?xs2) = {fst ?st}" by (meson \<open>io_targets M2 (initial M2) vs = {q2}\<close> assms(4) observable_io_targets_append)

  have "?xs1 \<noteq> []" using \<open>0 < length xs\<close> by auto  
  moreover have "prefix ?xs1 xs" using take_is_prefix by blast 
  moreover have "prefix ?xs2 xs" using take_is_prefix by blast
  moreover have "?xs1 \<noteq> ?xs2"
  proof -
    have f1: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na" by presburger
    have f2: "Suc i1 \<le> length xs" using index_def by force
    have "Suc i2 \<le> length xs" using f1 by (metis index_def length_take map_snd_zip_take min_less_iff_conj states_alt_def)
    then show ?thesis using f2 by (metis (no_types) index_def length_take min.absorb2 nat.simps(1))
  qed 
  ultimately have "Rep_Pre M2 M1 vs xs" using tgt_1_1 tgt_1_2 tgt_2_1 tgt_2_2 by (meson Rep_Pre.elims(3)) 
  then show "False" using assms(1) by simp
qed

  
  





(* Rep_Cov *)
fun Rep_Cov :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "Rep_Cov M2 M1 V'' vs xs = (\<exists> xs' vs' . xs' \<noteq> [] \<and> prefix xs' xs \<and> vs' \<in> V'' 
    \<and> (\<exists> s2 . io_targets M2 (initial M2) (vs @ xs') = {s2} \<and> io_targets M2 (initial M2) (vs') = {s2})
    \<and> (\<exists> s1 . io_targets M1 (initial M1) (vs @ xs') = {s1} \<and> io_targets M1 (initial M1) (vs') = {s1}))"



(* Lemma 5.4.8 (modifed to use Rep_Cov) *)
lemma RP_count_via_Rep_Cov :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "distinct (states (xs || tr) (q2,q1))" 
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "\<not> Rep_Cov M2 M1 V'' vs xs" (* weakened from 5.4.8 *) 
shows "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (RP M2 s vs xs V'')"
proof -
  have RP_cases : "RP M2 s vs xs V'' = R M2 s vs xs \<or> (\<exists> vs' \<in> V'' . vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs))" using RP_from_R assms by metis
  show ?thesis 
  proof (cases "RP M2 s vs xs V'' = R M2 s vs xs")
    case True
    then show ?thesis using R_count assms by metis
  next
    case False
    then obtain vs' where vs'_def : "vs' \<in> V'' \<and> vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs)" using RP_cases by auto
        
    have state_component_2 : "\<forall> io \<in> (R M2 s vs xs) . io_targets M2 (initial M2) io = {s}" 
      proof 
        fix io assume "io \<in> R M2 s vs xs"
        then have "s \<in> io_targets M2 (initial M2) io" by auto
        moreover have "io \<in> language_state M2 (initial M2)" using calculation by auto
        ultimately show "io_targets M2 (initial M2) io = {s}" using assms(3) io_targets_observable_singleton_ex by (metis singletonD) 
      qed

    have "vs' \<in> L M1" using assms(13) perm_language vs'_def by blast
    then obtain s' where s'_def : "io_targets M1 (initial M1) vs' = {s'}" by (meson assms(2) io_targets_observable_singleton_ob) 

    moreover have "s' \<notin> \<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))" 
    proof (rule ccontr)
      assume "\<not> s' \<notin> UNION (R M2 s vs xs) (io_targets M1 (initial M1))"
      then obtain xs' where xs'_def : "vs @ xs' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (vs @ xs')"
      proof -
        assume a1: "\<And>xs'. vs @ xs' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (vs @ xs') \<Longrightarrow> thesis"
        obtain pps :: "('a \<times> 'b) list set \<Rightarrow> (('a \<times> 'b) list \<Rightarrow> 'c set) \<Rightarrow> 'c \<Rightarrow> ('a \<times> 'b) list" where
          "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 \<in> x1 v3) = (pps x0 x1 x2 \<in> x0 \<and> x2 \<in> x1 (pps x0 x1 x2))"
          by moura
        then have f2: "pps (R M2 s vs xs) (io_targets M1 (initial M1)) s' \<in> R M2 s vs xs \<and> s' \<in> io_targets M1 (initial M1) (pps (R M2 s vs xs) (io_targets M1 (initial M1)) s')"
          using \<open>\<not> s' \<notin> UNION (R M2 s vs xs) (io_targets M1 (initial M1))\<close> by blast
        then have "\<exists>ps. pps (R M2 s vs xs) (io_targets M1 (initial M1)) s' = vs @ ps \<and> ps \<noteq> [] \<and> prefix ps xs \<and> s \<in> io_targets M2 (initial M2) (vs @ ps)"
          by simp
        then show ?thesis
          using f2 a1 by (metis (no_types))
      qed  
      
      have "vs @ xs' \<in> L M1" using xs'_def by blast 
      then have "io_targets M1 (initial M1) (vs@xs') = {s'}" by (metis assms(2) io_targets_observable_singleton_ob singletonD xs'_def)
      moreover have "io_targets M1 (initial M1) (vs') = {s'}" using s'_def by blast 
      moreover have "io_targets M2 (initial M2) (vs @ xs') = {s}" using state_component_2 xs'_def by blast
      moreover have "io_targets M2 (initial M2) (vs') = {s}" by (metis (mono_tags, lifting) RP.simps Un_iff insertI1 mem_Collect_eq vs'_def) 
      moreover have "xs' \<noteq> []" using xs'_def by simp
      moreover have "prefix xs' xs" using xs'_def by simp
      moreover have "vs' \<in> V''" using vs'_def by simp
      ultimately have "Rep_Cov M2 M1 V'' vs xs" by auto

      then show "False" using assms(14) by simp
    qed 

    moreover have "\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs)))
      = insert s' (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs)))" using s'_def by simp

    moreover have "finite (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs)))" 
    proof 
      show "finite (R M2 s vs xs)" using finite_R by simp
      show "\<And>a. a \<in> R M2 s vs xs \<Longrightarrow> finite (io_targets M1 (initial M1) a)" 
      proof -
        fix a assume "a \<in> R M2 s vs xs" 
        then have "prefix a (vs@xs)" by auto
        then have "a \<in> L M1" using language_state_prefix by (metis IntD1 assms(1) prefix_def) 
        then obtain p where "io_targets M1 (initial M1) a = {p}" using assms(2) io_targets_observable_singleton_ob by metis
        then show "finite (io_targets M1 (initial M1) a)" by simp
      qed
    qed

    ultimately have "card (\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs)))) = 
      Suc (card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))))" by (metis (no_types) card_insert_disjoint)

      
    moreover have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (\<Union> (image (io_targets M1 (initial M1)) (insert vs' (R M2 s vs xs))))" using vs'_def by simp
    
    ultimately have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = Suc (card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))))" by linarith

    then have "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = Suc (card (R M2 s vs xs))" using R_count[of vs xs M1 M2 s FAIL PM q2 q1 tr] using assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) by linarith 

    moreover have "card (RP M2 s vs xs V'') = Suc (card (R M2 s vs xs))" using vs'_def by (metis card_insert_if finite_R)

    ultimately show ?thesis by linarith
  qed
qed





(* Lemma 5.4.8 (modifed to use Rep_Cov and Rep_Pre) *)
lemma RP_count_alt_def :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "\<not> Rep_Pre M2 M1 vs xs" (* replaced the distinctness property of 5.4.8 *)
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "\<not> Rep_Cov M2 M1 V'' vs xs" (* weakened from 5.4.8 *) 
shows "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (RP M2 s vs xs V'')"
proof -
  have "distinct (states (xs || tr) (q2,q1))" using distinctness_via_Rep_Pre[of M2 M1 vs xs FAIL PM q2 q1 tr] assms by simp
  then show ?thesis using RP_count_via_Rep_Cov[of vs xs M1 M2 s FAIL PM q2 q1 tr V V'']
    using assms(1) assms(10) assms(12) assms(13) assms(14) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) by blast 
qed



(* helper functions to shorten assumptions *)
fun fault_model :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> nat \<Rightarrow> bool" where
  "fault_model M2 M1 m = (inputs M2 = inputs M1 \<and> card (nodes M1) \<le> m )"

lemma fault_model_props[elim!] :
  assumes "fault_model M2 M1 m"
  shows "inputs M2 = inputs M1"
        "card (nodes M1) \<le> m" using assms by auto

fun OFSM :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "OFSM M = (well_formed M \<and> observable M \<and> completely_specified M)"

lemma OFSM_props[elim!] :
  assumes "OFSM M"
shows "well_formed M" 
      "observable M" 
      "completely_specified M" using assms by auto

fun test_tools :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('state1 \<times> 'state2)  
  \<Rightarrow> ('in, 'out, 'state1 \<times>'state2) FSM \<Rightarrow>'in list set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
  "test_tools M2 M1 FAIL PM V V'' \<Omega> = (
      productF M2 M1 FAIL PM
    \<and> is_det_state_cover M2 V
    \<and> V'' \<in> Perm V M1
    \<and> applicable_set M2 \<Omega>
    \<and> \<Omega> \<noteq> {}
   )"

lemma test_tools_props[elim] :
  assumes "test_tools M2 M1 FAIL PM V V'' \<Omega>"
  and     "fault_model M2 M1 m"
  shows "productF M2 M1 FAIL PM"
        "is_det_state_cover M2 V"
        "V'' \<in> Perm V M1"
        "applicable_set M2 \<Omega>"
        "applicable_set M1 \<Omega>"
        "\<Omega> \<noteq> {}"
proof -
  show "productF M2 M1 FAIL PM" using assms(1) test_tools.elims by blast
  show "is_det_state_cover M2 V" using assms(1) test_tools.elims by blast
  show "V'' \<in> Perm V M1" using assms(1) test_tools.elims by blast
  show "applicable_set M2 \<Omega>" using assms(1) test_tools.elims by blast
  then show "applicable_set M1 \<Omega>" unfolding applicable_set.simps applicable.simps using fault_model_props(1)[OF assms(2)] by simp
  show "\<Omega> \<noteq> {}" using assms(1) test_tools.elims by blast
qed


(* LB helpers *)











lemma R_state_component_2 :  
  assumes "io \<in> (R M2 s vs xs)" 
  and     "observable M2"
shows "io_targets M2 (initial M2) io = {s}" 
proof -
  have "s \<in> io_targets M2 (initial M2) io" using assms(1) by auto
  moreover have "io \<in> language_state M2 (initial M2)" using calculation by auto
  ultimately show "io_targets M2 (initial M2) io = {s}" using assms(2) io_targets_observable_singleton_ex by (metis singletonD) 
qed

lemma RP_state_component_2 :
  assumes "io \<in> (RP M2 s vs xs V'')" 
  and     "observable M2"
shows "io_targets M2 (initial M2) io = {s}"
  by (metis (mono_tags, lifting) RP.simps R_state_component_2 Un_iff assms(1) assms(2) mem_Collect_eq)
  

lemma RP_io_targets_split :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "productF M2 M1 FAIL PM"
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "io \<in> RP M2 s vs xs V''"
shows "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io"
proof -
  have RP_cases : "RP M2 s vs xs V'' = R M2 s vs xs \<or> (\<exists> vs' \<in> V'' . vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs))" using RP_from_R assms by metis
  show "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" 
  proof (cases "io \<in> R M2 s vs xs")
    case True
    then have io_prefix : "prefix io (vs @ xs)" by auto
    then have io_lang_subs : "io \<in> L M1 \<and> io \<in> L M2" using assms(1) unfolding prefix_def by (metis IntE language_state language_state_split) 
    then have io_lang_inter : "io \<in> L M1 \<inter> L M2" by simp
    then have io_lang_pm : "io \<in> L PM" using productF_language assms by blast 
    moreover obtain p2 p1 where "(p2,p1) \<in> io_targets PM (initial PM) io" by (metis assms(2) assms(3) assms(6) calculation insert_absorb insert_ident insert_not_empty io_targets_observable_singleton_ob observable_productF singleton_insert_inj_eq subrelI) 
    ultimately have targets_pm : "io_targets PM (initial PM) io = {(p2,p1)}" using assms io_targets_observable_singleton_ex singletonD by (metis observable_productF) 
    then obtain trP where trP_def : "target (io || trP) (initial PM) = (p2,p1) \<and> path PM (io || trP) (initial PM) \<and> length io = length trP"
      proof -
        assume a1: "\<And>trP. target (io || trP) (initial PM) = (p2, p1) \<and> path PM (io || trP) (initial PM) \<and> length io = length trP \<Longrightarrow> thesis"
        have "\<exists>ps. target (io || ps) (initial PM) = (p2, p1) \<and> path PM (io || ps) (initial PM) \<and> length io = length ps"
          using \<open>(p2, p1) \<in> io_targets PM (initial PM) io\<close> by auto
        then show ?thesis
          using a1 by blast
      qed 
    then have trP_unique : "{ tr . path PM (io || tr) (initial PM) \<and> length io = length tr } = { trP }" 
      using observable_productF observable_path_unique_ex[of PM io "initial PM"] io_lang_pm assms(2) assms(3) assms(7)
      proof -
        obtain pps :: "('d \<times> 'c) list" where
          f1: "{ps. path PM (io || ps) (initial PM) \<and> length io = length ps} = {pps} \<or> \<not> observable PM"
          by (metis (no_types) \<open>\<And>thesis. \<lbrakk>observable PM; io \<in> L PM; \<And>tr. {t. path PM (io || t) (initial PM) \<and> length io = length t} = {tr} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> io_lang_pm)
        have f2: "observable PM"
          by (meson \<open>observable M1\<close> \<open>observable M2\<close> \<open>productF M2 M1 FAIL PM\<close> observable_productF)
        then have "trP \<in> {pps}"
          using f1 trP_def by blast
        then show ?thesis
          using f2 f1 by force
      qed
         
        
    obtain trIO2 where trIO2_def : "{ tr . path M2 (io || tr) (initial M2) \<and> length io = length tr } = { trIO2 }" using observable_path_unique_ex[of M2 io "initial M2"] io_lang_subs assms(3) by blast
    obtain trIO1 where trIO1_def : "{ tr . path M1 (io || tr) (initial M1) \<and> length io = length tr } = { trIO1 }" using observable_path_unique_ex[of M1 io "initial M1"] io_lang_subs assms(2) by blast

    have "path PM (io || trIO2 || trIO1) (initial M2, initial M1) \<and> length io = length trIO2 \<and> length trIO2 = length trIO1" using trIO2_def trIO1_def
    proof -
      have f1: "path M2 (io || trIO2) (initial M2) \<and> length io = length trIO2" using trIO2_def by auto
      have f2: "path M1 (io || trIO1) (initial M1) \<and> length io = length trIO1" using trIO1_def by auto
      then have "length trIO2 = length trIO1" using f1 by presburger
      then show ?thesis using f2 f1 assms(4) assms(5) assms(6) by blast
    qed 
    then have trP_split : "path PM (io || trIO2 || trIO1) (initial PM) \<and> length io = length trIO2 \<and> length trIO2 = length trIO1" using assms(6) by auto 
    then have trP_zip : "trIO2 || trIO1 = trP" using trP_def trP_unique using length_zip by fastforce 

    have "target (io || trIO2) (initial M2) = p2 \<and> path M2 (io || trIO2) (initial M2) \<and> length io = length trIO2" using trP_zip trP_split assms(6) trP_def trIO2_def by auto 
    then have "p2 \<in> io_targets M2 (initial M2) io" by auto
    then have targets_2 : "io_targets M2 (initial M2) io = {p2}" by (meson assms(3) observable_io_target_is_singleton)    

    have "target (io || trIO1) (initial M1) = p1 \<and> path M1 (io || trIO1) (initial M1) \<and> length io = length trIO1" using trP_zip trP_split assms(6) trP_def trIO1_def by auto 
    then have "p1 \<in> io_targets M1 (initial M1) io" by auto
    then have targets_1 : "io_targets M1 (initial M1) io = {p1}" by (metis io_lang_subs assms(2) io_targets_observable_singleton_ex singletonD) 

    have "io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io = {(p2,p1)}" using targets_2 targets_1 by simp
    then show "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" using targets_pm by simp
  
  next
    case False
    then have "io \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert io (R M2 s vs xs)" using RP_cases assms(9) by (metis insertE) 

    have "io \<in> L M1" using assms(8) perm_language assms(9) using False by auto 
    then obtain s' where s'_def : "io_targets M1 (initial M1) io = {s'}" by (meson assms(2) io_targets_observable_singleton_ob) 
    then obtain tr1 where tr1_def : "target (io || tr1) (initial M1) = s' \<and> path M1 (io || tr1) (initial M1) \<and> length tr1 = length io" by (metis io_targets_elim singletonI) 
    
    have "io_targets M2 (initial M2) io = {s}" using assms(9) assms(3) RP_state_component_2 by simp
    then obtain tr2 where tr2_def : "target (io || tr2) (initial M2) = s \<and> path M2 (io || tr2) (initial M2) \<and> length tr2 = length io" by (metis io_targets_elim singletonI)
    then have paths : "path M2 (io || tr2) (initial M2) \<and> path M1 (io || tr1) (initial M1)" using tr1_def by simp


    have "length io = length tr2" using tr2_def by simp
    moreover have "length tr2 = length tr1" using tr1_def tr2_def by simp
    ultimately have "path PM (io || tr2 || tr1) (initial M2, initial M1)" using assms(6) assms(5) assms(4) paths  productF_path_forward[of io tr2 tr1 M2 M1 FAIL PM "initial M2" "initial M1"] by blast

    moreover have "target (io || tr2 || tr1) (initial M2, initial M1) = (s,s')" by (simp add: tr1_def tr2_def) 
    moreover have "length (tr2 || tr2) = length io" using tr1_def tr2_def by simp
    moreover have "(initial M2, initial M1) = initial PM" using assms(6) by simp
    ultimately have "(s,s') \<in> io_targets PM (initial PM) io" by (metis io_target_from_path length_zip tr1_def tr2_def) 
    moreover have "observable PM" using assms(2) assms(3) assms(6) observable_productF by blast 
    then have "io_targets PM (initial PM) io = {(s,s')}" by (meson calculation observable_io_target_is_singleton) 

    then show ?thesis using \<open>io_targets M2 (initial M2) io = {s}\<close> \<open>io_targets M1 (initial M1) io = {s'}\<close> by simp
  qed
qed


  


lemma RP_io_targets_finite_M1 :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "is_det_state_cover M2 V" 
  and "V'' \<in> Perm V M1"
shows "finite (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V'')))" 
proof 
  show "finite (RP M2 s vs xs V'')" using finite_RP assms(3) assms(4) by simp
  show "\<And>a. a \<in> RP M2 s vs xs V'' \<Longrightarrow> finite (io_targets M1 (initial M1) a)" 
  proof -
    fix a assume "a \<in> RP M2 s vs xs V''" 

    have RP_cases : "RP M2 s vs xs V'' = R M2 s vs xs \<or> (\<exists> vs' \<in> V'' . vs' \<notin> R M2 s vs xs \<and> RP M2 s vs xs V'' = insert vs' (R M2 s vs xs))" using RP_from_R assms by metis
    have "a \<in> L M1"
    proof (cases "a \<in> R M2 s vs xs")
      case True
      then have "prefix a (vs@xs)" by auto
      then show "a \<in> L M1" using language_state_prefix by (metis IntD1 assms(1) prefix_def) 
    next
      case False
      then have "a \<in> V'' \<and> RP M2 s vs xs V'' = insert a (R M2 s vs xs)" using RP_cases \<open>a \<in> RP M2 s vs xs V''\<close> by (metis insertE) 
      then show "a \<in> L M1" by (meson assms(4) perm_language)
    qed
    then obtain p where "io_targets M1 (initial M1) a = {p}" using assms(2) io_targets_observable_singleton_ob by metis
      then show "finite (io_targets M1 (initial M1) a)" by simp   
  qed
qed

lemma RP_io_targets_finite_PM :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "productF M2 M1 FAIL PM"
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
shows "finite (\<Union> (image (io_targets PM (initial PM)) (RP M2 s vs xs V'')))" 
proof -
  have "\<forall> io \<in> RP M2 s vs xs V'' . io_targets PM (initial PM) io = {s} \<times> io_targets M1 (initial M1) io"
  proof 
    fix io assume "io \<in> RP M2 s vs xs V''"
    then have "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" using assms RP_io_targets_split[of vs xs M1 M2 FAIL PM V V'' io s] by simp
    moreover have "io_targets M2 (initial M2) io = {s}" using \<open>io \<in> RP M2 s vs xs V''\<close> assms(3) RP_state_component_2[of io M2 s vs xs V''] by blast
    ultimately show "io_targets PM (initial PM) io = {s} \<times> io_targets M1 (initial M1) io" by auto
  qed
  then have "\<Union> image (io_targets PM (initial PM)) (RP M2 s vs xs V'') = \<Union> image (\<lambda> io . {s} \<times> io_targets M1 (initial M1) io) (RP M2 s vs xs V'')" by simp
  moreover have "\<Union> image (\<lambda> io . {s} \<times> io_targets M1 (initial M1) io) (RP M2 s vs xs V'') = {s} \<times> \<Union> image (\<lambda> io . io_targets M1 (initial M1) io) (RP M2 s vs xs V'')" by blast
  ultimately have "\<Union> image (io_targets PM (initial PM)) (RP M2 s vs xs V'') = {s} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s vs xs V'')" by auto
  moreover have "finite ({s} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))" using assms(1,2,7,8) RP_io_targets_finite_M1[of vs xs M1 M2 V V'' s] by simp
  ultimately show ?thesis by simp
qed



lemma LB_count_helper_RP_disjoint_and_cards :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "productF M2 M1 FAIL PM"
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "s1 \<noteq> s2"
shows "\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') \<inter> \<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'') = {}" 
      "card (\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'')) = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V''))"
      "card (\<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'')) = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V''))"
proof -
  have "\<forall> io \<in> RP M2 s1 vs xs V'' . io_targets PM (initial PM) io = {s1} \<times> io_targets M1 (initial M1) io"
  proof 
    fix io assume "io \<in> RP M2 s1 vs xs V''"
    then have "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" using assms RP_io_targets_split[of vs xs M1 M2 FAIL PM V V'' io s1] by simp
    moreover have "io_targets M2 (initial M2) io = {s1}" using \<open>io \<in> RP M2 s1 vs xs V''\<close> assms(3) RP_state_component_2[of io M2 s1 vs xs V''] by blast
    ultimately show "io_targets PM (initial PM) io = {s1} \<times> io_targets M1 (initial M1) io" by auto
  qed
  then have "\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') = \<Union> image (\<lambda> io . {s1} \<times> io_targets M1 (initial M1) io) (RP M2 s1 vs xs V'')" by simp
  moreover have "\<Union> image (\<lambda> io . {s1} \<times> io_targets M1 (initial M1) io) (RP M2 s1 vs xs V'') = {s1} \<times> \<Union> image (\<lambda> io . io_targets M1 (initial M1) io) (RP M2 s1 vs xs V'')" by blast
  ultimately have image_split_1 :  "\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') = {s1} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'')" by simp
  then show "card (\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'')) = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V''))" by (metis (no_types)  card_cartesian_product_singleton)
  

  

  have "\<forall> io \<in> RP M2 s2 vs xs V'' . io_targets PM (initial PM) io = {s2} \<times> io_targets M1 (initial M1) io"
  proof
    fix io assume "io \<in> RP M2 s2 vs xs V''"
    then have "io_targets PM (initial PM) io = io_targets M2 (initial M2) io \<times> io_targets M1 (initial M1) io" using assms RP_io_targets_split[of vs xs M1 M2 FAIL PM V V'' io s2] by simp
    moreover have "io_targets M2 (initial M2) io = {s2}" using \<open>io \<in> RP M2 s2 vs xs V''\<close> assms(3) RP_state_component_2[of io M2 s2 vs xs V''] by blast
    ultimately show "io_targets PM (initial PM) io = {s2} \<times> io_targets M1 (initial M1) io" by auto
  qed
  then have "\<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'') = \<Union> image (\<lambda> io . {s2} \<times> io_targets M1 (initial M1) io) (RP M2 s2 vs xs V'')" by simp
  moreover have "\<Union> image (\<lambda> io . {s2} \<times> io_targets M1 (initial M1) io) (RP M2 s2 vs xs V'') = {s2} \<times> \<Union> image (\<lambda> io . io_targets M1 (initial M1) io) (RP M2 s2 vs xs V'')" by blast
  ultimately have image_split_2 :  "\<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'') = {s2} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V'')" by simp
  then show "card (\<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'')) = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V''))" by (metis (no_types)  card_cartesian_product_singleton)

  
  have "\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') \<inter> \<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'') 
        = {s1} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'') \<inter> {s2} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V'')" using image_split_1 image_split_2 by blast
  moreover have "{s1} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'') \<inter> {s2} \<times> \<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V'') = {}" using assms(9) by auto
  ultimately show "\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') \<inter> \<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'') = {}" by presburger  
qed


lemma LB_count_helper_RP_disjoint_card_M1 :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "productF M2 M1 FAIL PM"
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "s1 \<noteq> s2"
shows "card (\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V'') \<union> \<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V'')) 
       = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'')) + card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V''))"
proof -
  have "finite (\<Union> image (io_targets PM (initial PM)) (RP M2 s1 vs xs V''))" using RP_io_targets_finite_PM[OF assms(1-8)] by simp
  moreover have "finite (\<Union> image (io_targets PM (initial PM)) (RP M2 s2 vs xs V''))" using RP_io_targets_finite_PM[OF assms(1-8)] by simp
  ultimately show ?thesis using LB_count_helper_RP_disjoint_and_cards[OF assms] by (metis (no_types)  card_Un_disjoint)
qed 

lemma LB_count_helper_RP_disjoint_card :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {(q2,q1)}"
  and "path PM (xs || tr) (q2,q1)" 
  and "length xs = length tr"
  and "\<not> Rep_Pre M2 M1 vs xs" 
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "\<not> Rep_Cov M2 M1 V'' vs xs"  
  and "Prereq M2 M1 vs xs T S \<Omega> V V''"
  and "s1 \<noteq> s2"
  and "s1 \<in> S" 
  and "s2 \<in> S"
  and "applicable_set M1 \<Omega>"
  and "completely_specified M1"
shows "card (RP M2 s1 vs xs V'') + card (RP M2 s2 vs xs V'') 
       = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'')) + card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V''))"
proof -
  have "s1 \<in> nodes M2" using assms(14,16) unfolding Prereq.simps by blast
  have "s2 \<in> nodes M2" using assms(14,17) unfolding Prereq.simps by blast
  have "card (RP M2 s1 vs xs V'') = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V''))" using RP_count_alt_def[OF assms(1-5) \<open>s1 \<in> nodes M2\<close> assms(6-13)] by linarith
  moreover have "card (RP M2 s2 vs xs V'') = card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V''))" using RP_count_alt_def[OF assms(1-5) \<open>s2 \<in> nodes M2\<close> assms(6-13)] by linarith
 
  moreover have "\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'') \<inter> \<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V'') = {}"
  proof (rule ccontr)
    assume "\<Union> image (io_targets M1 (initial M1)) (RP M2 s1 vs xs V'') \<inter> \<Union> image (io_targets M1 (initial M1)) (RP M2 s2 vs xs V'') \<noteq> {}"
    then obtain io1 io2 t where shared_elem_def :
      "io1 \<in> (RP M2 s1 vs xs V'')"
      "io2 \<in> (RP M2 s2 vs xs V'')"
      "t \<in> io_targets M1 (initial M1) io1"
      "t \<in> io_targets M1 (initial M1) io2" by blast

    
    have "(\<forall> s1 \<in> S . \<forall> s2 \<in> S . s1 \<noteq> s2                                      
            \<longrightarrow> (\<forall> seq1 \<in> RP M2 s1 vs xs V'' . \<forall> seq2 \<in> RP M2 s2 vs xs V'' . 
               \<forall> t1 \<in> io_targets M1 (initial M1) seq1 . \<forall> t2 \<in> io_targets M1 (initial M1) seq2 .  
                 r_dist_set M1 \<Omega> t1 t2))" using assms(14) by simp
    then have dist_prop : "\<forall> t1 \<in> io_targets M1 (initial M1) io1 . \<forall> t2 \<in> io_targets M1 (initial M1) io2 .  
                 r_dist_set M1 \<Omega> t1 t2" using assms(16,17,15) shared_elem_def(1,2) by blast
    then have "io_targets M1 (initial M1) io1 \<inter> io_targets M1 (initial M1) io2 = {}" using assms(18-19) r_dist_set_dist_disjoint[of M1 \<Omega> "io_targets M1 (initial M1) io1" "io_targets M1 (initial M1) io2"] by simp

    then show "False" using shared_elem_def(3,4) by blast 
  qed

  ultimately show ?thesis by linarith 
qed 


(*
lemma LB_count_helper_vs_xs_in_languages :
  assumes "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools M2 M1 FAIL PM V V'' \<Omega>"
  and     "Prereq M2 M1 vs xs T S \<Omega> V V''"
shows "(vs @ xs) \<in> L M1 \<inter> L M2"
proof -
  have "map fst (vs @ xs) \<in> T" using assms(5) by simp

*)
  
lemma LB_count_helper_RP_card_union :
  assumes "observable M2"
  and     "s1 \<noteq> s2"
shows "RP M2 s1 vs xs V'' \<inter> RP M2 s2 vs xs V'' = {}"
proof (rule ccontr)
  assume "RP M2 s1 vs xs V'' \<inter> RP M2 s2 vs xs V'' \<noteq> {}"
  then obtain io where "io \<in> RP M2 s1 vs xs V'' \<and> io \<in> RP M2 s2 vs xs V''" by blast
  then have "s1 \<in> io_targets M2 (initial M2) io" 
            "s2 \<in> io_targets M2 (initial M2) io" by auto
  then have "s1 = s2" using assms(1) by (metis observable_io_target_is_singleton singletonD) 
  then show "False" using assms(2) by simp
qed

lemma LB_count_helper_RP_card_union_sum :
  assumes "(vs @ xs) \<in> L M2 \<inter> L M1"
  and     "OFSM M1"
  and     "OFSM M2"
  and     "fault_model M2 M1 m"
  and     "test_tools M2 M1 FAIL PM V V'' \<Omega>"
  and     "Prereq M2 M1 vs xs T S \<Omega> V V''"
  and     "\<not> Rep_Pre M2 M1 vs xs"
  and     "\<not> Rep_Cov M2 M1 V'' vs xs"
shows "sum (\<lambda> s . card (RP M2 s vs xs V'')) S = sum (\<lambda> s . card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) S"
using assms proof -
  have "finite (nodes M2)" using assms(3) by auto
  moreover have "S \<subseteq> nodes M2" using assms(6) by simp
  ultimately have "finite S" using infinite_super by blast 

  then have " vs @ xs \<in> L M2 \<inter> L M1 \<Longrightarrow>
    OFSM M1 \<Longrightarrow>
    OFSM M2 \<Longrightarrow>
    fault_model M2 M1 m \<Longrightarrow>
    test_tools M2 M1 FAIL PM V V'' \<Omega> \<Longrightarrow>
    Prereq M2 M1 vs xs T S \<Omega> V V'' \<Longrightarrow>
    \<not> Rep_Pre M2 M1 vs xs \<Longrightarrow>
    \<not> Rep_Cov M2 M1 V'' vs xs \<Longrightarrow> 
    sum (\<lambda> s . card (RP M2 s vs xs V'')) S = sum (\<lambda> s . card (\<Union> image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) S"
  proof (induction S)
    case empty
    show ?case by simp
  next
    case (insert s S)
    
    have "(insert s S) \<subseteq> nodes M2" using insert.prems(6) by simp
    then have "s \<in> nodes M2" by simp

    have "Prereq M2 M1 vs xs T S \<Omega> V V''" using \<open>Prereq M2 M1 vs xs T (insert s S) \<Omega> V V''\<close> by simp
    then have "(\<Sum>s\<in>S. card (RP M2 s vs xs V'')) = (\<Sum>s\<in>S. card (\<Union>a\<in>RP M2 s vs xs V''. io_targets M1 (initial M1) a))" using insert.IH[OF insert.prems(1-5) _ insert.prems(7-8)] by metis
    moreover have "(\<Sum>s'\<in>(insert s S). card (RP M2 s' vs xs V'')) = (\<Sum>s'\<in>S. card (RP M2 s' vs xs V'')) + card (RP M2 s vs xs V'')" by (simp add: add.commute insert.hyps(1) insert.hyps(2))
    ultimately have S_prop : "(\<Sum>s'\<in>(insert s S). card (RP M2 s' vs xs V'')) = (\<Sum>s\<in>S. card (\<Union>a\<in>RP M2 s vs xs V''. io_targets M1 (initial M1) a)) + card (RP M2 s vs xs V'')" by presburger

    have "vs@xs \<in> L M1 \<inter> L M2" using insert.prems(1) by simp

    obtain q2 q1 tr where suffix_path : "io_targets PM (initial PM) vs = {(q2,q1)}"
                          "path PM (xs || tr) (q2,q1)" 
                          "length xs = length tr" using productF_language_state_intermediate[OF insert.prems(1) test_tools_props(1)[OF insert.prems(5,4)] OFSM_props(2,1)[OF insert.prems(3)]  OFSM_props(2,1)[OF insert.prems(2)]] by blast
    
    
    
    have "card (RP M2 s vs xs V'') = card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V'')))"
      using OFSM_props(2,1)[OF insert.prems(3)] OFSM_props(2,1)[OF insert.prems(2)] RP_count_alt_def[OF \<open>vs@xs \<in> L M1 \<inter> L M2\<close> _ _ _ _ \<open>s\<in>nodes M2\<close> test_tools_props(1)[OF insert.prems(5,4)] suffix_path insert.prems(7) test_tools_props(2,3)[OF insert.prems(5,4)] insert.prems(8)]
      by linarith 
    
    show "(\<Sum>s\<in>insert s S. card (RP M2 s vs xs V'')) =
                  (\<Sum>s\<in>insert s S. card (UNION (RP M2 s vs xs V'') (io_targets M1 (initial M1))))"
    proof -
      have "(\<Sum>c\<in>insert s S. card (UNION (RP M2 c vs xs V'') (io_targets M1 (initial M1)))) = card (UNION (RP M2 s vs xs V'') (io_targets M1 (initial M1))) + (\<Sum>c\<in>S. card (UNION (RP M2 c vs xs V'') (io_targets M1 (initial M1))))"
        by (meson insert.hyps(1) insert.hyps(2) sum.insert)
      then show ?thesis
        using \<open>(\<Sum>s'\<in>insert s S. card (RP M2 s' vs xs V'')) = (\<Sum>s\<in>S. card (\<Union>a\<in>RP M2 s vs xs V''. io_targets M1 (initial M1) a)) + card (RP M2 s vs xs V'')\<close> \<open>card (RP M2 s vs xs V'') = card (UNION (RP M2 s vs xs V'') (io_targets M1 (initial M1)))\<close> by presburger
    qed 
  qed

  then show ?thesis using assms by blast 
qed




(* Lemma 5.4.11 *)
lemma LB_count :
  assumes "observable M1"
  and "observable M2"
  and "well_formed M1"
  and "well_formed M2"
  and "productF M2 M1 FAIL PM"
  and "is_det_state_cover M2 V"
  and "V'' \<in> Perm V M1"
  and "Prereq M2 M1 vs xs T S \<Omega> V V''"
  and "\<not> Rep_Pre M2 M1 vs xs"
  and "\<not> Rep_Cov M2 M1 V'' vs xs"
shows "LB M2 M1 vs xs T S \<Omega> V'' \<le> card (nodes M1)" 
  sorry


(* Lemma 5.4.13 *)
(* see minimal_sequence_to_failure_extending_det_state_cover_ob in FSM_Product *)








end