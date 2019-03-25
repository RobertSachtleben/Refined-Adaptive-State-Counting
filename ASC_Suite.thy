theory ASC_Suite
imports ASC_LB
begin

(* maximum length contained common prefix *)
fun mcp :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "mcp z W p = (p \<in> {p . prefix p z \<and> (\<exists> w \<in> W . prefix p w)}
                \<and> (\<forall> p' \<in> {p . prefix p z \<and> (\<exists> w \<in> W . prefix p w)} .
                  length p' \<le> length p))"

lemma mcp_ex :
  assumes "[] \<in> W"
  and     "finite W"
obtains p
where "mcp z W p"  
proof -
  let ?P = "{p . prefix p z \<and> (\<exists> w \<in> W . prefix p w)}"
  let ?maxP = "arg_max length (\<lambda> p . p \<in> ?P)"

  have "?P \<subseteq> {p . prefix p z} \<union> {p . \<exists> w \<in> W . prefix p w}" by blast
  moreover have "finite {p . prefix p z}" 
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
  moreover have "finite {p . \<exists> w \<in> W . prefix p w}"
    by (metis (no_types) List.finite_set assms(2) finite_Collect_bex set_prefixes_eq) 
  ultimately have "finite ?P" by simp 

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

    
    



end