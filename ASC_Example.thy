theory ASC_Example
  imports ASC_Sufficiency
begin

(* helper function to more easily create FSMs, only requiring a set of transition-tuples 
   and an initial state instead of, in particular, the explicit successor function *)
fun from_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) FSM" where
"from_rel rel q0 = \<lparr> succ = \<lambda> io p . { q . (p,io,q) \<in> rel }, 
                    inputs = image (fst \<circ> fst \<circ> snd) rel, 
                    outputs = image (snd \<circ> fst \<circ> snd) rel, 
                    initial = q0 \<rparr>"

(* functions for checking whether a set of transition-tuples constitutes an OFSM *)

fun well_formed_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> bool" where
  "well_formed_rel rel = (finite rel
                          \<and> (\<forall> s1 x y . (x \<notin> image (fst \<circ> fst \<circ> snd) rel \<or> y \<notin> image (snd \<circ> fst \<circ> snd) rel) \<longrightarrow> \<not>(\<exists> s2 . (s1,(x,y),s2) \<in> rel))
                          \<and> rel \<noteq> {})"

lemma well_formed_from_rel :
  assumes "well_formed_rel rel"
  shows "well_formed (from_rel rel q0)"  (is "well_formed ?M")
proof -
  have "\<And> q io p . q \<in> succ ?M io p \<Longrightarrow> q \<in> image (snd \<circ> snd) rel"
    by force
    
  have "\<And> q . q \<in> nodes ?M \<Longrightarrow> q = q0 \<or> q \<in> image (snd \<circ> snd) rel"
  proof -
    fix q assume "q \<in> nodes ?M"
    then show "q = q0 \<or> q \<in> image (snd \<circ> snd) rel"
    proof (cases rule: FSM.nodes.cases)
      case initial
      then show ?thesis by auto
    next
      case (execute p a)
      then show ?thesis
        using \<open>\<And> q io p . q \<in> succ ?M io p \<Longrightarrow> q \<in> image (snd \<circ> snd) rel\<close> by blast 
    qed
  qed
  then have "nodes ?M \<subseteq> insert q0 (image (snd \<circ> snd) rel)"
    by blast
  moreover have "finite (insert q0 (image (snd \<circ> snd) rel))"
    using assms by auto
  ultimately have "finite (nodes ?M)"
    by (simp add: Finite_Set.finite_subset) 
  moreover have "finite (inputs ?M)" "finite (outputs ?M)"
    using assms by auto  
  ultimately have "finite_FSM ?M"
    by auto

  moreover have "inputs ?M \<noteq> {}" 
    using assms by auto
  moreover have "outputs ?M \<noteq> {}" 
    using assms by auto
  moreover have "\<And> s1 x y . (x \<notin> inputs ?M \<or> y \<notin> outputs ?M) \<longrightarrow> succ ?M (x,y) s1 = {}"
    using assms by auto
  
  ultimately show ?thesis
    by auto
qed




fun completely_specified_rel_over :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> 'state set \<Rightarrow> bool" where
  "completely_specified_rel_over rel nods = (\<forall> s1 \<in> nods . \<forall> x \<in> image (fst \<circ> fst \<circ> snd) rel . \<exists> y \<in> image (snd \<circ> fst \<circ> snd) rel . \<exists> s2 . (s1,(x,y),s2) \<in> rel)"

lemma completely_specified_from_rel :
  assumes "completely_specified_rel_over rel (nodes ((from_rel rel q0)))"
  shows "completely_specified (from_rel rel q0)"  (is "completely_specified ?M")
  unfolding completely_specified.simps
proof
  fix s1 assume "s1 \<in> nodes (from_rel rel q0)"
  show  "\<forall>x\<in>inputs ?M. \<exists>y\<in>outputs ?M. \<exists>s2. s2 \<in> succ ?M (x, y) s1"
  proof 
    fix x assume "x \<in> inputs (from_rel rel q0)" 
    then have "x \<in>  image (fst \<circ> fst \<circ> snd) rel"
      using assms by auto
         
    obtain y s2 where "y \<in> image (snd \<circ> fst \<circ> snd) rel" "(s1,(x,y),s2) \<in> rel" 
      using assms \<open>s1 \<in> nodes (from_rel rel q0)\<close> \<open>x \<in>  image (fst \<circ> fst \<circ> snd) rel\<close>
      by (meson completely_specified_rel_over.elims(2)) 

    then have "y \<in> outputs (from_rel rel q0)" "s2 \<in> succ (from_rel rel q0) (x, y) s1"
      by auto

    then show "\<exists>y\<in>outputs (from_rel rel q0). \<exists>s2. s2 \<in> succ (from_rel rel q0) (x, y) s1" 
      by blast
  qed
qed





fun observable_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> bool" where
  "observable_rel rel = (\<forall> io s1 . { s2 . (s1,io,s2) \<in> rel } = {} \<or> (\<exists> s2 . { s2' . (s1,io,s2') \<in> rel } = {s2}))"

lemma observable_from_rel :
  assumes "observable_rel rel"
  shows "observable (from_rel rel q0)"  (is "observable ?M")  
proof -
  have "\<And> io s1 . { s2 . (s1,io,s2) \<in> rel } = succ ?M io s1"
    by auto
  then show ?thesis using assms by auto
qed





abbreviation "OFSM_rel rel q0 \<equiv> well_formed_rel rel \<and> completely_specified_rel_over rel (nodes (from_rel rel q0)) \<and> observable_rel rel"

lemma OFMS_from_rel :
  assumes "OFSM_rel rel q0"
  shows "OFSM (from_rel rel q0)"
  by (metis assms completely_specified_from_rel observable_from_rel well_formed_from_rel)
  








end
