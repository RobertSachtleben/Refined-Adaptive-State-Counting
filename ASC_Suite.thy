theory ASC_Suite
imports ASC_LB
begin

(* maximum length contained prefix *)
fun mcp :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "mcp z W p = (prefix p z \<and> p \<in> W \<and> 
                 (\<forall> p' . (prefix p' z \<and> p' \<in> W) \<longrightarrow> length p' \<le> length p))"

(* def. for contained common prefix :
  "mcp z W p = (p \<in> {p . prefix p z \<and> (\<exists> w \<in> W . prefix p w)}
                \<and> (\<forall> p' \<in> {p . prefix p z \<and> (\<exists> w \<in> W . prefix p w)} .
                  length p' \<le> length p))"
*)

lemma mcp_ex :
  assumes "[] \<in> W"
  and     "finite W"
obtains p
where "mcp z W p"  
proof -
  let ?P = "{p . prefix p z \<and> p \<in> W}"
  let ?maxP = "arg_max length (\<lambda> p . p \<in> ?P)"

  have "finite {p . prefix p z}" 
  proof -
    have "{p . prefix p z} \<subseteq> image (\<lambda> i . take i z) (set [0 ..< Suc (length z)])"
    proof 
      fix p assume "p \<in> {p . prefix p z}"
      then obtain i where "i \<le> length z \<and> p = take i z"
        by (metis append_eq_conv_conj mem_Collect_eq prefix_def prefix_length_le) 
      then have "i < Suc (length z) \<and> p = take i z" by simp
      then show "p \<in> image (\<lambda> i . take i z) (set [0 ..< Suc (length z)])" 
        using atLeast_upt by blast  
    qed
    then show ?thesis using finite_surj by blast 
  qed
  then have "finite ?P" by simp 

  have "?P \<noteq> {}"
    using Nil_prefix assms(1) by blast 

  have "\<exists> maxP \<in> ?P . \<forall> p \<in> ?P . length p \<le> length maxP" 
  proof (rule ccontr)
    assume "\<not>(\<exists> maxP \<in> ?P . \<forall> p \<in> ?P . length p \<le> length maxP)" 
    then have "\<forall> p \<in> ?P . \<exists> p' \<in> ?P . length p < length p'" by (meson not_less) 
    then have "\<forall> l \<in> (image length ?P) . \<exists> l' \<in> (image length ?P) . l < l'" by auto 
    
    then have "infinite (image length ?P)" by (metis (no_types, lifting) \<open>?P \<noteq> {}\<close> image_is_empty infinite_growing) 
    then have "infinite ?P" by blast 
    then show "False" using \<open>finite ?P\<close> by simp
  qed 

  then obtain maxP where "maxP \<in> ?P" "\<forall> p \<in> ?P . length p \<le> length maxP" by blast

  then have "mcp z W maxP" unfolding mcp.simps by blast 
  then show ?thesis using that by auto
qed


lemma mcp_unique :
  assumes "mcp z W p" 
  and     "mcp z W p'"
shows "p = p'"
proof -
  have "length p' \<le> length p" using assms(1) assms(2) by auto 
  moreover have "length p \<le> length p'" using assms(1) assms(2) by auto
  ultimately have "length p' = length p" by simp

  moreover have "prefix p z" using assms(1) by auto
  moreover have "prefix p' z" using assms(2) by auto
  ultimately show ?thesis by (metis append_eq_conv_conj prefixE)
qed

fun mcp' :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list" where
  "mcp' z W = (THE p . mcp z W p)"

lemma mcp'_intro : 
  assumes "mcp z W p"
shows "mcp' z W = p"
using assms mcp_unique by (metis mcp'.elims theI_unique) 


fun N :: "('in \<times> 'out) list \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set set" where
  "N io M V = { V'' \<in> Perm V M . (map fst (mcp' io V'')) = (mcp' (map fst io) V) }"
(*
  "N io M V = { V'' \<in> Perm V M . \<exists> vs \<in> V'' . (mcp' (map fst io) V) = map fst vs 
                                              \<and> prefix vs io }"
*)
(*
  "N io M V = { V'' \<in> Perm V M . \<exists> v . prefix v (map fst io) \<and> 
                            (\<forall> w . prefix w (map fst io) \<longrightarrow> (length w > length v \<longrightarrow> w \<notin> V))
                            \<and> (\<exists> v' . length v' = length v \<and> (v || v') \<in> V'' \<and> prefix (v || v') io)}"
*)

(* TODO - show that construction is nonempty
lemma N_nonempty :
  assumes "[] \<in> V"
  shows "N io M V \<noteq> {}"
*)

(* Corollary 7.1.2 *)
lemma x :
  assumes "map fst vs = mcp' (map fst (vs@xs)) V"
  and     "V'' \<in> N (vs@xs) M1 V"
  and     "is_det_state_cover M2 V"
  and     "well_formed M2"
  and     "finite V"
shows "vs \<in> V'' \<and> vs = mcp' (vs@xs) V''" 
proof 
  have "map fst (mcp' (vs@xs) V'') = mcp' (map fst (vs@xs)) V" using assms(2) by auto
  then have "map fst (mcp' (vs@xs) V'') = map fst vs" using assms(1) by presburger
  then have "length (mcp' (vs@xs) V'') = length vs" by (metis length_map) 

  have "[] \<in> V''" using perm_empty[OF assms(3)] N.simps assms(2) by blast 
  moreover have "finite V''" using perm_elem_finite[OF assms(3,4)] N.simps assms(2) by blast
  ultimately obtain p where "mcp (vs@xs) V'' p" using mcp_ex by auto 
  then have "mcp' (vs@xs) V'' = p" using mcp'_intro by simp
  

  then have "prefix (mcp' (vs@xs) V'') (vs@xs)" unfolding mcp'.simps mcp.simps
    using \<open>mcp (vs @ xs) V'' p\<close> mcp.elims(2) by blast 
  then show "vs = mcp' (vs@xs) V''"
    by (metis \<open>length (mcp' (vs @ xs) V'') = length vs\<close> append_eq_append_conv prefix_def) 

  show "vs \<in> V''"
    using \<open>mcp (vs @ xs) V'' p\<close> \<open>mcp' (vs @ xs) V'' = p\<close> \<open>vs = mcp' (vs @ xs) V''\<close> by auto 
qed


abbreviation append_set :: "'a list set \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "append_set T X \<equiv> {xs @ [x] | xs x . xs \<in> T \<and> x \<in> X}"

abbreviation append_sets :: "'a list set \<Rightarrow> 'a list set \<Rightarrow> 'a list set" where
  "append_sets T X \<equiv> {xs @ xs' | xs xs' . xs \<in> T \<and> xs' \<in> X}"


fun TS :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> nat \<Rightarrow> 'in list set" 
and C  :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> nat \<Rightarrow> 'in list set"   
and R  :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> nat \<Rightarrow> 'in list set"   
where
  "R M2 M1 T S \<Omega> V 0 = {}" |
  "TS M2 M1 T S \<Omega> V 0 = V" |
  "TS M2 M1 T S \<Omega> V (Suc 0) = V" |
  "C M2 M1 T S \<Omega> V 0 = V" |
  "C M2 M1 T S \<Omega> V (Suc 0) = V" |
  "R M2 M1 T S \<Omega> V (Suc n) = 
    {xs' \<in> C M2 M1 T S \<Omega> V (Suc n) .
      (\<exists> vs xs . (vs@xs) \<in> language_state_in M1 (initial M1) {xs'}
        \<and> (\<exists> S1 . S1 \<subseteq> S
          \<and> (\<exists> V'' \<in> N (vs@xs) M1 V . 
            vs = mcp' (vs@xs) V''
            \<and> (\<forall> s1 \<in> S1 . \<forall> s2 \<in> S1 .
              s1 \<noteq> s2 \<longrightarrow> 
                (\<forall> io1 \<in> RP M2 s1 vs xs V'' .
                   \<forall> io2 \<in> RP M2 s2 vs xs V'' .
                     B M1 io1 \<Omega> \<noteq> B M1 io2 \<Omega> )))))}" |
  "C M2 M1 T S \<Omega> V (Suc n) = (append_set ((C M2 M1 T S \<Omega> V n) - (R M2 M1 T S \<Omega> V n)) (inputs M2)) - (TS M2 M1 T S \<Omega> V n)" |
  "TS M2 M1 T S \<Omega> V (Suc n) = (TS M2 M1 T S \<Omega> V n) \<union> (C M2 M1 T S \<Omega> V (Suc n))" 
    
    


(* Properties of the generated sets *)
abbreviation lists_of_length :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where 
  "lists_of_length X n \<equiv> {xs . length xs = n \<and> set xs \<subseteq> X}"

lemma append_lists_of_length_alt_def :
  "append_sets T (lists_of_length X (Suc n)) = append_set (append_sets T (lists_of_length X n)) X"
proof 
  show "append_sets T (lists_of_length X (Suc n)) \<subseteq> append_set (append_sets T (lists_of_length X n)) X"
  proof 
    fix tx assume "tx \<in> append_sets T (lists_of_length X (Suc n))"
    then obtain t x where "t@x = tx" "t \<in> T" "length x = Suc n" "set x \<subseteq> X" by blast
    then have "x \<noteq> []" "length (butlast x) = n" by auto
    moreover have "set (butlast x) \<subseteq> X" using \<open>set x \<subseteq> X\<close> by (meson dual_order.trans prefixeq_butlast set_mono_prefix) 
    ultimately have "butlast x \<in> lists_of_length X n" by auto
    then have "t@(butlast x) \<in> append_sets T (lists_of_length X n)" using \<open>t \<in> T\<close> by blast
    moreover have "last x \<in> X" using \<open>set x \<subseteq> X\<close> \<open>x \<noteq> []\<close> by auto
    ultimately have "t@(butlast x)@[last x] \<in> append_set (append_sets T (lists_of_length X n)) X" by auto
    then show "tx \<in> append_set (append_sets T (lists_of_length X n)) X" using \<open>t@x = tx\<close> by (simp add: \<open>x \<noteq> []\<close>) 
  qed
  show "append_set (append_sets T (lists_of_length X n)) X \<subseteq> append_sets T (lists_of_length X (Suc n))"
  proof 
    fix tx assume "tx \<in> append_set (append_sets T (lists_of_length X n)) X"
    then obtain tx' x where "tx = tx' @ [x]" "tx' \<in> append_sets T (lists_of_length X n)" "x \<in> X" by blast
    then obtain tx'' x' where "tx''@x' = tx'" "tx'' \<in> T" "length x' = n" "set x' \<subseteq> X" by blast
    then have "tx''@x'@[x] = tx" "tx'' \<in> T" "length (x'@[x]) = Suc n" "set (x'@[x]) \<subseteq> X" 
      apply (simp add: \<open>tx = tx' @ [x]\<close>)
      apply (meson \<open>tx'' \<in> T\<close>)
      apply (simp add: \<open>length x' = n\<close>)+
      by (simp add: \<open>set x' \<subseteq> X\<close> \<open>x \<in> X\<close>)
    then show "tx \<in> append_sets T (lists_of_length X (Suc n))" by blast
  qed
qed

lemma C_step : 
  assumes "n > 0"
  shows "C M2 M1 T S \<Omega> V (Suc n) \<subseteq> (append_set (C M2 M1 T S \<Omega> V n) (inputs M2)) - C M2 M1 T S \<Omega> V n"
proof -
  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  obtain k where n_def[simp] : "n = Suc k" using assms
    using not0_implies_Suc by blast 

  have "?C (Suc n) = (append_set (?C n - ?R n) (inputs M2)) - ?TS n" using n_def using C.simps(3) by blast
  moreover have "?C n \<subseteq> ?TS n" using n_def by (metis C.simps(2) TS.elims UnCI assms neq0_conv subsetI)  
  ultimately show "?C (Suc n) \<subseteq> append_set (?C n) (inputs M2) - ?C n" by blast
qed


lemma C_extension : 
  "C M2 M1 T S \<Omega> V (Suc n) \<subseteq> append_sets V (lists_of_length (inputs M2) n)"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc k)

  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  have "0 < Suc k" by simp
  have "?C (Suc (Suc k)) \<subseteq> (append_set (?C (Suc k)) (inputs M2)) - ?C (Suc k)" using C_step[OF \<open>0 < Suc k\<close>] by blast

  then have "?C (Suc (Suc k)) \<subseteq> append_set (?C (Suc k)) (inputs M2)" by blast
  moreover have "append_set (?C (Suc k)) (inputs M2) \<subseteq> append_set (append_sets V (lists_of_length (inputs M2) k)) (inputs M2)"
    using Suc.IH by auto 
  ultimately have I_Step : "?C (Suc (Suc k)) \<subseteq> append_set (append_sets V (lists_of_length (inputs M2) k)) (inputs M2)"
    by (meson order_trans) 

  show ?case using append_lists_of_length_alt_def[symmetric, of V k "inputs M2"] I_Step by presburger  
qed

lemma TS_union : 
shows "TS M2 M1 T S \<Omega> V i = (\<Union> j \<in> (set [0..<Suc i]) . C M2 M1 T S \<Omega> V j)" 
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc i)

  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  have "?TS (Suc i) = ?TS i \<union> ?C (Suc i)"
    by (metis (no_types) C.simps(2) TS.simps(1) TS.simps(2) TS.simps(3) list_decode.cases sup.idem sup_commute) 
  then have "?TS (Suc i) = (\<Union> j \<in> (set [0..<Suc i]) . ?C j) \<union> ?C (Suc i)" using Suc.IH by simp
  then show ?case by auto 
qed

lemma C_disj : 
  assumes "i \<le> j"
  and    "0 < i"
shows "C M2 M1 T S \<Omega> V i \<inter> C M2 M1 T S \<Omega> V (Suc j) = {}"
proof -
  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  have "Suc 0 < Suc j" using assms(1-2) by auto
  then obtain k where "Suc j = Suc (Suc k)" using not0_implies_Suc by blast 
  then have "?C (Suc j) = (append_set (?C j - ?R j) (inputs M2))  - ?TS j" using C.simps(3) by blast
  then have "?C (Suc j) \<inter> ?TS j = {}" by blast
  moreover have "?C i \<subseteq> ?TS j" using assms(1) TS_union[of M2 M1 T S \<Omega> V j] by fastforce  
  ultimately show ?thesis by blast
qed


lemma R_subset : "R M2 M1 T S \<Omega> V i \<subseteq> C M2 M1 T S \<Omega> V i" 
proof (cases i)
  case 0
  then show ?thesis by auto
next
  case (Suc n)
  then show ?thesis using ASC_Suite.R.simps(2) by blast
qed


lemma R_disj : 
  assumes "i \<le> j"
  and    "0 < i"
shows "R M2 M1 T S \<Omega> V i \<inter> R M2 M1 T S \<Omega> V (Suc j) = {}"
proof -
  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  have "?R i \<subseteq> ?C i" "?R (Suc j) \<subseteq> ?C (Suc j)" using R_subset by blast+
  moreover have "?C i \<inter> ?C (Suc j) = {}" using C_disj[OF assms] by assumption
  ultimately show ?thesis by blast
qed



lemma T_extension : 
  assumes "n > 0"
  shows "TS M2 M1 T S \<Omega> V (Suc n) - TS M2 M1 T S \<Omega> V n \<subseteq> (append_set (TS M2 M1 T S \<Omega> V n) (inputs M2)) - TS M2 M1 T S \<Omega> V n"
proof -
  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  obtain k where n_def[simp] : "n = Suc k" using assms
    using not0_implies_Suc by blast 

  have "?C (Suc n) = (append_set (?C n - ?R n) (inputs M2)) - ?TS n" using n_def using C.simps(3) by blast
  then have "?C (Suc n) \<subseteq> append_set (?C n) (inputs M2) - ?TS n" by blast
  moreover have "?C n \<subseteq> ?TS n" using TS_union[of M2 M1 T S \<Omega> V n] by fastforce
  ultimately have "?C (Suc n) \<subseteq> append_set (?TS n) (inputs M2) - ?TS n" by blast
  moreover have "?TS (Suc n) - ?TS n \<subseteq> ?C (Suc n) " using TS.simps(3)[of M2 M1 T S \<Omega> V k] using n_def by blast
  ultimately show ?thesis by blast
qed


lemma append_set_prefix :
  assumes "xs \<in> append_set T X"
  shows "butlast xs \<in> T"
  using assms by auto 


lemma C_subset : "C M2 M1 T S \<Omega> V i \<subseteq> TS M2 M1 T S \<Omega> V i"
  by (metis C.simps(1) C.simps(2) TS.elims Un_upper2 eq_iff) 
  

lemma TS_subset :
  assumes "i \<le> j"
  shows "TS M2 M1 T S \<Omega> V i \<subseteq> TS M2 M1 T S \<Omega> V j"
proof -
  have "TS M2 M1 T S \<Omega> V i = (\<Union> k \<in> (set [0..<Suc i]) . C M2 M1 T S \<Omega> V k)" 
       "TS M2 M1 T S \<Omega> V j = (\<Union> k \<in> (set [0..<Suc j]) . C M2 M1 T S \<Omega> V k)" using TS_union by assumption+
  moreover have "set [0..<Suc i] \<subseteq> set [0..<Suc j]" using assms by auto
  ultimately show ?thesis by blast
qed
  
  

(* Lemma 5.5.5 *)
lemma TS_immediate_prefix_containment :
  assumes "vs@xs \<in> TS M2 M1 T S \<Omega> V i"
  and     "mcp (vs@xs) V vs"
shows "vs@(butlast xs) \<in> TS M2 M1 T S \<Omega> V i"
proof -
  let ?TS = "\<lambda> n . TS M2 M1 T S \<Omega> V n"
  let ?C = "\<lambda> n . C M2 M1 T S \<Omega> V n"
  let ?R = "\<lambda> n . R M2 M1 T S \<Omega> V n"

  obtain j where j_def : "j \<le> i \<and> vs@xs \<in> ?C j" using assms(1)  TS_union[where i=i]
  proof -
    assume a1: "\<And>j. j \<le> i \<and> vs @ xs \<in> C M2 M1 T S \<Omega> V j \<Longrightarrow> thesis"
    obtain nn :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a list set) \<Rightarrow> 'a list \<Rightarrow> nat" where
      f2: "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 \<in> x1 v3) = (nn x0 x1 x2 \<in> x0 \<and> x2 \<in> x1 (nn x0 x1 x2))"
      by moura
    have "vs @ xs \<in> UNION (set [0..<Suc i]) (C M2 M1 T S \<Omega> V)"
      by (metis \<open>\<And>\<Omega> V T S M2 M1. TS M2 M1 T S \<Omega> V i = (\<Union>j\<in>set [0..<Suc i]. C M2 M1 T S \<Omega> V j)\<close> \<open>vs @ xs \<in> TS M2 M1 T S \<Omega> V i\<close>)
    then have "nn (set [0..<Suc i]) (C M2 M1 T S \<Omega> V) (vs @ xs) \<in> set [0..<Suc i] \<and> vs @ xs \<in> C M2 M1 T S \<Omega> V (nn (set [0..<Suc i]) (C M2 M1 T S \<Omega> V) (vs @ xs))"
      using f2 by blast
    then show ?thesis
      using a1 by (metis (no_types) atLeastLessThan_iff leD not_less_eq_eq set_upt)
  qed 

  show ?thesis
  proof (cases j)
    case 0
    then have "?C j = V" by auto
    then have "vs@xs \<in> V" using j_def by auto
    then have "mcp (vs@xs) V (vs@xs)" using assms(2) by auto
    then have "vs@xs = vs" using assms(2) mcp_unique by auto
    then have "butlast xs = []" by auto
    then show ?thesis using \<open>vs @ xs = vs\<close> assms(1) by auto  
  next
    case (Suc k)
    then show ?thesis 
    proof (cases k)
      case 0
      then have "?C j = V" using Suc by auto 
      then have "vs@xs \<in> V" using j_def by auto
      then have "mcp (vs@xs) V (vs@xs)" using assms(2) by auto
      then have "vs@xs = vs" using assms(2) mcp_unique by auto
      then have "butlast xs = []" by auto
      then show ?thesis using \<open>vs @ xs = vs\<close> assms(1) by auto
    next
      case (Suc m)
      assume j_assms : "j = Suc k" "k = Suc m"
      then have "?C (Suc (Suc m)) = append_set (?C (Suc m) - ?R (Suc m)) (inputs M2) - ?TS (Suc m)"
        using C.simps(3) by blast 
      then have "?C (Suc (Suc m)) \<subseteq> append_set (?C (Suc m)) (inputs M2)" by blast
      
      have "vs@xs \<in> ?C (Suc (Suc m))" using j_assms j_def by blast
      
      have "butlast (vs@xs) \<in> ?C (Suc m)"
      proof -
        show ?thesis
          by (meson \<open>?C (Suc (Suc m)) \<subseteq> append_set (?C (Suc m)) (inputs M2)\<close> \<open>vs @ xs \<in> ?C (Suc (Suc m))\<close> append_set_prefix subsetCE)
      qed

      moreover have "xs \<noteq> []"
      proof -
        have "1 \<le> k" using j_assms by auto
        then have "?C j \<inter> ?C 1 = {}" using C_disj[of 1 k] j_assms(1)
          using less_numeral_extra(1) by blast 
        then have "?C j \<inter> V = {}" by auto
        then have "vs@xs \<notin> V" using j_def by auto
        then show ?thesis using assms(2) by auto 
      qed

      ultimately have "vs@(butlast xs) \<in> ?C (Suc m)"
        by (simp add: butlast_append)

      have "Suc m < Suc j" using j_assms by auto
      have "?C (Suc m) \<subseteq> ?TS j" using TS_union[of M2 M1 T S \<Omega> V j] \<open>Suc m < Suc j\<close>
        by (metis UN_upper atLeast_upt lessThan_iff)
      

      have "vs @ butlast xs \<in> TS M2 M1 T S \<Omega> V j" using \<open>vs@(butlast xs) \<in> ?C (Suc m)\<close> \<open>?C (Suc m) \<subseteq> ?TS j\<close> j_def by auto
      then show ?thesis using j_def TS_subset[of j i] by blast 
    qed
  qed
qed


(* corollary 5.5.6 *)
lemma TS_prefix_containment :
  assumes "vs@xs \<in> TS M2 M1 T S \<Omega> V i"
  and     "mcp (vs@xs) V vs"
  and     "prefix xs' xs"
shows "vs@xs' \<in> TS M2 M1 T S \<Omega> V i"
(* Perform induction on length difference, as from each prefix we can deduce the 
   desired property for the prefix one element smaller than it via 5.5.5 *)
using assms proof (induction "length xs - length xs'" arbitrary: xs')
  case 0
  then have "xs = xs'"
    by (metis append_Nil2 append_eq_conv_conj gr_implies_not0 length_drop length_greater_0_conv prefixE)
  then show ?case using 0 by auto
next
  case (Suc k)
  then show ?case 
  proof (cases xs')
    case Nil
    then show ?thesis
      by (metis TS.simps(1) TS_subset append_Nil2 assms(2) mcp.elims(2) subset_iff zero_le) 
  next
    case (Cons a list)
    then show ?thesis
    proof (cases "xs = xs'")
      case True
      then show ?thesis using assms(1) by simp
    next
      case False 
      then obtain xs'' where "xs = xs'@xs''" using Suc.prems(3) using prefixE by blast 
      then have "xs'' \<noteq> []" using False by auto
      then have "k = length xs - length (xs' @ [hd xs''])" using \<open>xs = xs'@xs''\<close> Suc.hyps(2) by auto
      moreover have "prefix (xs' @ [hd xs'']) xs" using \<open>xs = xs'@xs''\<close> \<open>xs'' \<noteq> []\<close>
        by (metis Cons_prefix_Cons list.exhaust_sel prefix_code(1) same_prefix_prefix) 
      ultimately have "vs @ (xs' @ [hd xs'']) \<in> TS M2 M1 T S \<Omega> V i" using Suc.hyps(1)[OF _ Suc.prems(1,2)] by simp
      
      
      have "mcp (vs @ xs' @ [hd xs'']) V vs" using \<open>xs = xs'@xs''\<close> \<open>xs'' \<noteq> []\<close> assms(2)
      proof -
        obtain aas :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
          "\<forall>x0 x1 x2. (\<exists>v3. (prefix v3 x2 \<and> v3 \<in> x1) \<and> \<not> length v3 \<le> length x0) = ((prefix (aas x0 x1 x2) x2 \<and> aas x0 x1 x2 \<in> x1) \<and> \<not> length (aas x0 x1 x2) \<le> length x0)"
          by moura
        then have f1: "\<forall>as A asa. (\<not> mcp as A asa \<or> prefix asa as \<and> asa \<in> A \<and> (\<forall>asb. (\<not> prefix asb as \<or> asb \<notin> A) \<or> length asb \<le> length asa)) \<and> (mcp as A asa \<or> \<not> prefix asa as \<or> asa \<notin> A \<or> (prefix (aas asa A as) as \<and> aas asa A as \<in> A) \<and> \<not> length (aas asa A as) \<le> length asa)"
          by auto
        obtain aasa :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
          f2: "\<forall>x0 x1. (\<exists>v2. x0 = x1 @ v2) = (x0 = x1 @ aasa x0 x1)"
          by moura
        then have f3: "([] @ [hd xs'']) @ aasa (xs' @ xs'') (xs' @ [hd xs'']) = ([] @ [hd xs'']) @ aasa (([] @ [hd xs'']) @ aasa (xs' @ xs'') (xs' @ [hd xs''])) ([] @ [hd xs''])"
          by (meson prefixE prefixI)
        have "xs' @ xs'' = (xs' @ [hd xs'']) @ aasa (xs' @ xs'') (xs' @ [hd xs''])"
          using f2 by (metis (no_types) \<open>prefix (xs' @ [hd xs'']) xs\<close> \<open>xs = xs' @ xs''\<close> prefixE)
        then have "(vs @ (a # list) @ [hd xs'']) @ aasa (([] @ [hd xs'']) @ aasa (xs' @ xs'') (xs' @ [hd xs''])) ([] @ [hd xs'']) = vs @ xs"
          using f3 by (simp add: \<open>xs = xs' @ xs''\<close> local.Cons)
        then have "\<not> prefix (aas vs V (vs @ xs' @ [hd xs''])) (vs @ xs' @ [hd xs'']) \<or> aas vs V (vs @ xs' @ [hd xs'']) \<notin> V \<or> length (aas vs V (vs @ xs' @ [hd xs''])) \<le> length vs"
          using f1 by (metis (no_types) \<open>mcp (vs @ xs) V vs\<close> local.Cons prefix_append)
        then show ?thesis
          using f1 by (meson \<open>mcp (vs @ xs) V vs\<close> prefixI)
      qed 
      
      
      then have "vs @ butlast (xs' @ [hd xs'']) \<in> TS M2 M1 T S \<Omega> V i" using TS_immediate_prefix_containment[OF \<open>vs @ (xs' @ [hd xs'']) \<in> TS M2 M1 T S \<Omega> V i\<close>] by simp

      moreover have "xs' = butlast (xs' @ [hd xs''])" using \<open>xs'' \<noteq> []\<close> by simp

      ultimately show ?thesis by simp
    qed
  qed
qed



  


end