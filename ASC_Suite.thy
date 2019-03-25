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
  "C M2 M1 T S \<Omega> V (Suc n) = { xs@[x] | xs x . xs \<in> ((C M2 M1 T S \<Omega> V n) - (R M2 M1 T S \<Omega> V n)) \<and> x : inputs M2 } - (TS M2 M1 T S \<Omega> V n)" |
  "TS M2 M1 T S \<Omega> V (Suc n) = (TS M2 M1 T S \<Omega> V n) \<union> (C M2 M1 T S \<Omega> V (Suc n))" 
    
    



end