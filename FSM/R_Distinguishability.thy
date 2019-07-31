theory R_Distinguishability
imports FSM ProductMachine
begin

section \<open>R-Distinguishability\<close>

subsection \<open>Basic Definitions\<close>

fun r_compatible :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "r_compatible M q1 q2 = ((\<exists> S . completely_specified S \<and> is_submachine S (product (from_FSM M q1) (from_FSM M q2))))"

abbreviation(input) "r_distinguishable M q1 q2 \<equiv> \<not> r_compatible M q1 q2"


fun r_distinguishable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"



subsection \<open>R(k)-Distinguishability\<close>


lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M))"
  by auto

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  unfolding r_distinguishable_k.simps by fastforce


(* nodes that are reachable in at most k transitions *)
fun reachable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target p q | p . path M q p \<and> length p \<le> n}" 

(* TODO: reset to original ? otherwise change names to indicate _initial_ *)
(* lemma reachable_k_0 : "reachable_k M q 0 = {q}" 
  by auto*)
lemma reachable_k_0 : "reachable_k M (initial M) 0 = {initial M}" 
  by auto

lemma reachable_k_nodes : "nodes M = reachable_k M (initial M) ( size M - 1)"
proof -
  have "\<And>q. q \<in> nodes M \<Longrightarrow> q \<in> reachable_k M (initial M) ( size M - 1)"
  proof -
    fix q assume "q \<in> nodes M"
    then obtain p where "path M (initial M) p" and "target p (initial M) = q"
      by (metis path_to_node) 
    then obtain p' where "path M (initial M) p'"
                     and "target p' (initial M) = target p (initial M)" 
                     and "length p' < size M"
      using distinct_path_length_limit_nodes[of "M" "initial M" p]
      using distinct_path_length[of M "initial M" p] by auto
    then show "q \<in> reachable_k M (initial M) ( size M - 1)"
      using \<open>target p (initial M) = q\<close> list.size(3) mem_Collect_eq not_less_eq_eq reachable_k.simps by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( size M - 1) \<Longrightarrow> x \<in> nodes M"
    using nodes_path_initial by auto
  
  ultimately show ?thesis by blast
qed

lemma r_distinguishable_k_0_not_completely_specified :
  assumes "r_distinguishable_k M q1 q2 0"
      and "q1 \<in> nodes M"
      and "q2 \<in> nodes M"
  shows "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
proof -
  let ?F1 = "from_FSM M q1"
  let ?F2 = "from_FSM M q2"
  let ?P = "product ?F1 ?F2"

  obtain x where "x \<in> set (inputs M)" 
             and "\<not> (\<exists> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"  
    using assms by auto

  then have *: "\<not> (\<exists> t1 t2 . t1 \<in> h ?F1 \<and> t2 \<in> h ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    using from_FSM_h by (metis (no_types) \<open>\<nexists>t1 t2. t1 \<in> set (wf_transitions M) \<and> t2 \<in> set (wf_transitions M) \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2\<close> assms(2) assms(3) contra_subsetD from_FSM_h)
  
  have **: "\<not> (\<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x)"
  proof (rule ccontr)  
    assume "\<not> \<not> (\<exists>t\<in>h (product (from_FSM M q1) (from_FSM M q2)). t_source t = (q1, q2) \<and> t_input t = x)"
    then obtain t where "t \<in> h ?P" and "t_source t = (q1,q2)" and "t_input t = x"
      by blast 

    have "\<exists> t1 t2 . t1 \<in> h ?F1 \<and> t2 \<in> h ?F2 \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
      using product_transition_split[OF \<open>t \<in> h ?P\<close>]
      by (metis \<open>t_input t = x\<close> \<open>t_source t = (q1, q2)\<close> fst_conv snd_conv)
    then show "False" 
      using * by auto
  qed

  moreover have "x \<in> set (inputs ?P)"
    using \<open>x \<in> set (inputs M)\<close> by auto

  ultimately have "\<not> completely_specified_state ?P (q1,q2)"
    by (meson completely_specified_state.elims(2))
    

  have "(q1,q2) = initial (product (from_FSM M q1) (from_FSM M q2))"
    by auto

  show ?thesis
    using \<open>(q1, q2) = initial (product (from_FSM M q1) (from_FSM M q2))\<close> \<open>\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1, q2)\<close> by presburger
  
qed



end