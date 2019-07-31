theory R_Distinguishability
imports FSM ProductMachine
begin

fun r_compatible :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "r_compatible M q1 q2 = ((\<exists> S . completely_specified S \<and> is_submachine S (product (from_FSM M q1) (from_FSM M q2))))"

abbreviation "r_distinguishable M q1 q2 \<equiv> \<not> r_compatible M q1 q2"


fun r_distinguishable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"






lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M))"
  by auto

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  unfolding r_distinguishable_k.simps by fastforce

end