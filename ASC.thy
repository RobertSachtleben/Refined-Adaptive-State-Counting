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
  and "distinct (states (xs || tr) (q1,q2))" 
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
          obtain pps :: "('c \<times> 'c) list" where
            f1: "{ps. path PM (io || ps) (initial PM) \<and> length io = length ps} = {pps}"
            using \<open>\<And>thesis. \<lbrakk>observable PM; io \<in> L PM; \<And>tr. {t. path PM (io || t) (initial PM) \<and> length io = length t} = {tr} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> \<open>observable M1\<close> \<open>observable M2\<close> \<open>productF M2 M1 FAIL PM\<close> io_lang_pm observable_productF by blast
          then have "path PM (io || pps) (initial PM) \<and> length io = length pps"
            by blast
          then have "pps = trP"
            by (meson \<open>observable M1\<close> \<open>observable M2\<close> \<open>productF M2 M1 FAIL PM\<close> io_lang_pm observable_path_unique observable_productF trP_def)
          then show ?thesis
            using f1 by meson
        qed 
      
      obtain trIO2 where trIO2_def : "{ tr . path M2 (io || tr) (initial M2) \<and> length io = length tr } = { trIO2 }" using observable_path_unique_ex[of M2 io "initial M2"] io_lang_subs assms(3) by blast
      obtain trIO1 where trIO1_def : "{ tr . path M1 (io || tr) (initial M1) \<and> length io = length tr } = { trIO1 }" using observable_path_unique_ex[of M1 io "initial M1"] io_lang_subs assms(2) by blast
  
      have "path PM (io || trIO2 || trIO1) (initial M2, initial M1) \<and> length io = length trIO2 \<and> length trIO2 = length trIO1" using trIO2_def trIO1_def
      proof -
        have f1: "\<forall>cs. path M1 (io || cs) (initial M1) \<and> length io = length cs \<or> cs \<notin> {trIO1}" using trIO1_def by auto
        have f2: "\<forall>cs. path M2 (io || cs) (initial M2) \<and> length io = length cs \<or> cs \<notin> {trIO2}" using trIO2_def by auto
        have "\<forall>cs csa. (cs::'c list) \<in> {csa} \<or> csa \<noteq> cs" by fastforce
        then show ?thesis using f2 f1 by (metis (no_types) FSM.nodes.initial assms(4) assms(5) assms(7) productF_path_inclusion)
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
    moreover have "length (xs || tr) \<ge> length (io1X || tr1X')" using calculation by auto 
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
  "Perm V M = {image f V | f . \<forall> v . f v \<in> language_state_for_input M (initial M) v }"

lemma perm_empty :
  assumes "is_det_state_cover M V"
  and "V'' \<in> Perm V M"
shows "[] \<in> V''"
proof -
  have init_seq : "[] \<in> V" using det_state_cover_empty assms by simp
  obtain f where f_def : "V'' = image f V \<and> (\<forall> v . f v \<in> language_state_for_input M (initial M) v)" using assms by auto
  then have "f [] = []" using init_seq by (metis language_state_for_input_empty singleton_iff) 
  then show ?thesis using init_seq f_def by (metis image_eqI) 
qed


(* R\<^sup>+ *)
fun RP :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> ('in \<times> 'out) list set" where
  "RP M s vs xs V'' = R M s vs xs \<union> {vs' \<in> V'' . io_targets M (initial M) vs' = {s}}"

(* Lemma 5.4.8 *)
lemma RP_count :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {q}"
  and "path PM (xs || tr) q" 
  and "length tr = length xs"
  and "distinct (states (xs || tr) q)" 
  and "V'' \<in> Perm V M"
  shows "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (RP M2 s vs xs V'')"
  by sorry


(* LB *)
fun LB :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> nat" where
  "LB M2 M1 vs xs T S \<Omega> V'' = (sum (\<lambda> s . card (RP M2 s vs xs V'')) S) 
                              + card ( (D M1 \<Omega> T) - {B M1 xs' \<Omega> | xs' s' . s' \<in> S \<and> xs' \<in> RP M2 s' vs xs V''})"


(* Prereq *)
fun Prereq :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> bool" where 
  "Prereq M2 M1 vs xs T S \<Omega> V V'' = True"
(* 1 *)
(* 2 *)
(* 3 *)
(* 4 *)
(* 5 *)


(* Rep_pre *)

(* Rep_V *)

(* Lemma 5.4.11 *)


(* Lemma 5.4.13 *)
(* see minimal_sequence_to_failure_extending_det_state_cover_ob in FSM_Product *)








end