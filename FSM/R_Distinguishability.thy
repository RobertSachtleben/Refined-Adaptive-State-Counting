theory R_Distinguishability
imports FSM ProductMachine
begin

section \<open>R-Distinguishability\<close>

subsection \<open>Basic Definitions\<close>

definition r_compatible :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
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
    using from_FSM_h by (metis (no_types) \<open>\<not> (\<exists> t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)\<close> assms(2) assms(3) contra_subsetD from_FSM_h)
  
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


(* TODO: move *)
lemma from_product_initial_paths_ex :
  "(\<exists>p1 p2.
         path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
         path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
         target p1 (initial (from_FSM M q1)) = q1 \<and>
         target p2 (initial (from_FSM M q2)) = q2 \<and> p_io p1 = p_io p2)"
proof -
  have "path (from_FSM M q1) (initial (from_FSM M q1)) []" by blast
  moreover have "path (from_FSM M q2) (initial (from_FSM M q2)) []" by blast
  moreover have "
         target [] (initial (from_FSM M q1)) = q1 \<and>
         target [] (initial (from_FSM M q2)) = q2 \<and> p_io [] = p_io []" by auto
  ultimately show ?thesis by blast
qed



lemma single_transition_path : "t \<in> h M \<Longrightarrow> path M (t_source t) [t]" by auto





lemma r_0_distinguishable_from_not_completely_specified :
  assumes "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1,q2)"
  shows "r_distinguishable_k M q1 q2 0"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  from assms obtain x where "x \<in> set (inputs ?P)"
                      and "\<not> (\<exists>t\<in>h ?P. t_source t = (q1, q2) \<and> t_input t = x)" 
        unfolding completely_specified_state.simps by blast

  then have "x \<in> set (inputs M)"
    by (metis from_FSM_product_inputs)

  have *: "\<nexists>t1 t2.
                t1 \<in> h (from_FSM M q1) \<and>
                t2 \<in> h (from_FSM M q2) \<and>
                t_source t1 = q1 \<and>
                t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
  proof

    assume "\<exists>t1 t2.
       t1 \<in> set (wf_transitions (from_FSM M q1)) \<and>
       t2 \<in> set (wf_transitions (from_FSM M q2)) \<and>
       t_source t1 = q1 \<and>
       t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2"
    then obtain t1 t2 where "t1 \<in> set (wf_transitions (from_FSM M q1))" 
                        and "t2 \<in> set (wf_transitions (from_FSM M q2))"
                        and "t_source t1 = q1"
                        and "t_source t2 = q2" 
                        and "t_input t1 = x" 
                        and "t_input t2 = x" 
                        and "t_output t1 = t_output t2"
      by blast

    let ?t = "((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
    let ?t1 = "(fst (t_source ?t), t_input ?t, t_output ?t, fst (t_target ?t))"
    let ?t2 = "(snd (t_source ?t), t_input ?t, t_output ?t, snd (t_target ?t))"

    have t1_alt : "t1 = ?t1"
      by auto
    have "t_source t2 = snd (t_source ?t)"
      by auto
    moreover have "t_input t2 = t_input ?t"
      using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> by auto
    moreover have "t_output t2 = t_output ?t"
      using \<open>t_output t1 = t_output t2\<close> by auto
    moreover have "t_target t2 = snd (t_target ?t)"
      by auto
    ultimately have "(t_source t2, t_input t2, t_output t2, t_target t2) = ?t2"
      by auto
    then have t2_alt : "t2 = ?t2"
      by auto
        
    have "?t1 \<in> set (wf_transitions (from_FSM M q1))"
      using \<open>t1 \<in> set (wf_transitions (from_FSM M q1))\<close> by auto
    have "?t2 \<in> set (wf_transitions (from_FSM M q2))"
      using \<open>t2 \<in> set (wf_transitions (from_FSM M q2))\<close> t2_alt by auto

    have "fst (t_source ?t) = q1" using \<open>t_source t1 = q1\<close> by auto
    moreover have "snd (t_source ?t) = q2" using \<open>t_source t2 = q2\<close> by auto
    ultimately have *: "(\<exists>p1 p2.
         path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
         path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
         target p1 (initial (from_FSM M q1)) = fst (t_source ?t) \<and>
         target p2 (initial (from_FSM M q2)) = snd (t_source ?t) \<and> p_io p1 = p_io p2)"
      using from_product_initial_paths_ex[of M q1 q2] by blast


    have "?t \<in> h ?P" 
      using product_transition_t[of ?t "from_FSM M q1" "from_FSM M q2"]
      using \<open>?t1 \<in> set (wf_transitions (from_FSM M q1))\<close> \<open>?t2 \<in> set (wf_transitions (from_FSM M q2))\<close> * by presburger
    moreover have "t_source ?t = (q1,q2)" using \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close> by auto
    moreover have "t_input ?t = x" using \<open>t_input t1 = x\<close> by auto
    ultimately show "False"
      using \<open>\<not> (\<exists>t\<in>h ?P. t_source t = (q1, q2) \<and> t_input t = x)\<close> by blast
  qed

  have **:  "\<And>t1 . t1 \<in> h M \<Longrightarrow> t_source t1 = q1 \<Longrightarrow> t1 \<in> h (from_FSM M q1)"
   and ***: "\<And>t2 . t2 \<in> h M \<Longrightarrow> t_source t2 = q2 \<Longrightarrow> t2 \<in> h (from_FSM M q2)"
    using from_FSM_transition_initial[of _ M] by auto

  show ?thesis unfolding r_distinguishable_k.simps
    using \<open>x \<in> set (inputs M)\<close> * ** *** by blast
qed          


lemma r_distinguishable_k_intersection_path : 
  assumes "\<not> r_distinguishable_k M q1 q2 k"
  and "length xs \<le> Suc k"
  and "set xs \<subseteq> set (inputs M)"
shows "\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs"
using assms proof (induction k arbitrary: q1 q2 xs)
  case 0
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  show ?case
  proof (cases "length xs < Suc 0")
    case True
    then have "xs = []" by auto
    moreover have "path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) []"
      by (metis from_FSM_simps(1) nodes.initial path.nil product_simps(1)) 
    moreover have "map fst (p_io []) = []" by auto
    ultimately show ?thesis by blast
  next
    case False
    
    have "completely_specified_state ?P (q1,q2)"
    proof (rule ccontr)
      assume "\<not> completely_specified_state ?P (q1,q2)"
      then have "r_distinguishable_k M q1 q2 0"
        using r_0_distinguishable_from_not_completely_specified by metis
      then show "False"
        using "0.prems" by simp
    qed
    then have *: "\<forall> x \<in> set (inputs ?P) . \<exists> t . t \<in> h ?P \<and> t_source t = (q1,q2) \<and> t_input t = x"
      unfolding completely_specified_state.simps by blast

    let ?x = "hd xs"
    have "xs = [?x]"
      using "0.prems"(2) False
      by (metis Suc_length_conv le_neq_implies_less length_0_conv list.sel(1))
    
    have "?x \<in> set (inputs M)"
      using "0.prems"(3) False by auto
    then obtain t where "t \<in> h ?P" and "t_source t = (q1,q2)" and "t_input t = ?x"
      using * by (metis from_FSM_product_inputs) 

    then have "path ?P (q1,q2) [t]" 
      using single_transition_path by metis
    moreover have "map fst (p_io [t]) = xs"
      using \<open>t_input t = ?x\<close> \<open>xs = [hd xs]\<close> by auto
    ultimately show ?thesis
      by (metis (no_types, lifting)) 
  qed
next
  case (Suc k)
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  
  

  show ?case 
  proof (cases "length xs \<le> Suc k")
    case True
    have "\<not> r_distinguishable_k M q1 q2 k" 
      using Suc.prems(1) by auto
    show ?thesis 
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M q1 q2 k\<close> True Suc.prems(3)] by assumption
  next
    case False
    then have "length xs = Suc (Suc k)"
      using Suc.prems(2) by auto
    
    then have "hd xs \<in> set (inputs M)"
      by (metis Suc.prems(3) contra_subsetD hd_in_set length_greater_0_conv zero_less_Suc) 
    have "set (tl xs) \<subseteq> set (inputs M)"
      by (metis \<open>length xs = Suc (Suc k)\<close> Suc.prems(3) dual_order.trans hd_Cons_tl length_0_conv nat.simps(3) set_subset_Cons)
    have "length (tl xs) \<le> Suc k"
      by (simp add: \<open>length xs = Suc (Suc k)\<close>) 

    let ?x = "hd xs"
    let ?xs = "tl xs"


    have "\<forall> x \<in> set (inputs M) . \<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
    proof 
      fix x assume "x \<in> set (inputs M)"
  
      have "\<not>(\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        using Suc.prems by auto
      then have "\<forall> x \<in> set (inputs M) . \<exists> t1 t2 . (t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> \<not> r_distinguishable_k M (t_target t1) (t_target t2) k)"
        by blast
      then obtain t1 t2 where "t1 \<in> h M"
                          and "t2 \<in> h M"  
                          and "t_source t1 = q1" 
                          and "t_source t2 = q2"  
                          and "t_input t1 = x" 
                          and "t_input t2 = x" 
                          and p4: "t_output t1 = t_output t2" 
                          and **: "\<not> r_distinguishable_k M (t_target t1) (t_target t2) k"
        using \<open>x \<in> set (inputs M)\<close> by auto

      have p1: "t1 \<in> h (from_FSM M q1)"
        using \<open>t1 \<in> h M\<close> \<open>t_source t1 = q1\<close> from_FSM_transition_initial by metis
      have p2: "t2 \<in> h (from_FSM M q2)"
        using \<open>t2 \<in> h M\<close> \<open>t_source t2 = q2\<close> from_FSM_transition_initial by metis
      have p3: "t_input t1 = t_input t2"
        using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> by auto
      

      
      
      have p5: "\<exists>p1 p2.
                   path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
                   path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
                   target p1 (initial (from_FSM M q1)) = t_source t1 \<and>
                   target p2 (initial (from_FSM M q2)) = t_source t2 \<and> p_io p1 = p_io p2"  
        using from_product_initial_paths_ex[of M q1 q2] \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close> by auto

      
      have ***: "((q1,q2), x, t_output t1, (t_target t1, t_target t2)) \<in> h ?P"
        using product_transition_from_transitions[OF p1 p2 p3 p4 p5]
              \<open>t_source t1 = q1\<close> \<open>t_source t2 = q2\<close> \<open>t_input t1 = x\<close> by metis
      
      show "\<exists> t \<in> h ?P . t_source t = (q1,q2) \<and> t_input t = x \<and> \<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
        by (metis "**" "***" fst_conv snd_conv)
    qed

    then obtain t where "t \<in> h ?P" and "t_source t = (q1,q2)" and "t_input t = ?x" 
                    and "\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
      using \<open>?x \<in> set (inputs M)\<close> by blast 

    obtain p where p_def: "path (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))) (t_target t) p" 
               and "map fst (p_io p) = ?xs"
      using Suc.IH[OF \<open>\<not> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k\<close> \<open>length (tl xs) \<le> Suc k\<close> \<open>set (tl xs) \<subseteq> set (inputs M)\<close>] by auto
    
    have "path ?P (t_target t) p" 
      using product_from_path_previous[OF p_def \<open>t \<in> h ?P\<close>] by assumption

    have "path ?P (q1,q2) (t#p)"
      using path_cons[OF\<open>t \<in> h ?P\<close> \<open>path ?P (t_target t) p\<close>] \<open>t_source t = (q1,q2)\<close> by metis
    moreover have "map fst (p_io (t#p)) = xs"
      using \<open>t_input t = ?x\<close> \<open>map fst (p_io p) = ?xs\<close>
      by (metis (no_types, lifting) \<open>length xs = Suc (Suc k)\<close> \<open>t_input t = hd xs\<close> fst_conv hd_Cons_tl length_greater_0_conv list.simps(9) zero_less_Suc)
    ultimately show ?thesis
      by (metis (no_types, lifting)) 
  qed
qed


    

end