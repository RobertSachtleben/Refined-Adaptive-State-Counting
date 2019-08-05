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



subsection \<open>R(k)-Distinguishability Properties\<close>


lemma r_distinguishable_k_0_alt_def : 
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not>(\<exists> y q1' q2' . (q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M))"
  by auto

lemma r_distinguishable_k_Suc_k_alt_def :
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k 
                                          \<or> (\<exists> x \<in> set (inputs M) . \<forall> y q1' q2' . ((q1,x,y,q1') \<in> h M \<and> (q2,x,y,q2') \<in> h M) \<longrightarrow> r_distinguishable_k M q1' q2' k))" 
  unfolding r_distinguishable_k.simps by fastforce




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











lemma r_0_distinguishable_from_not_completely_specified_initial :
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



  
lemma r_0_distinguishable_from_not_completely_specified :
  assumes "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1',q2')"
      and "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
    shows "r_distinguishable_k M q1' q2' 0"
  using r_0_distinguishable_from_not_completely_specified_initial[OF product_from_not_completely_specified[OF assms]] by assumption




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
        using r_0_distinguishable_from_not_completely_specified_initial by metis
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
      using path.cons[OF\<open>t \<in> h ?P\<close> \<open>path ?P (t_target t) p\<close>] \<open>t_source t = (q1,q2)\<close> by metis
    moreover have "map fst (p_io (t#p)) = xs"
      using \<open>t_input t = ?x\<close> \<open>map fst (p_io p) = ?xs\<close>
      by (metis (no_types, lifting) \<open>length xs = Suc (Suc k)\<close> \<open>t_input t = hd xs\<close> fst_conv hd_Cons_tl length_greater_0_conv list.simps(9) zero_less_Suc)
    ultimately show ?thesis
      by (metis (no_types, lifting)) 
  qed
qed



lemma r_distinguishable_k_intersection_paths : 
  assumes "\<not>(\<exists> k . r_distinguishable_k M q1 q2 k)"
  shows "\<forall> xs . set xs \<subseteq> set (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)"
proof (rule ccontr)
  assume "\<not> (\<forall> xs . set xs \<subseteq> set (inputs M) \<longrightarrow> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs))"
  then obtain xs where "set xs \<subseteq> set (inputs M)"
                   and "\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)" 
    by blast

  have "\<not> r_distinguishable_k M q1 q2 (length xs)"
    using assms by auto

  show "False" 
    using r_distinguishable_k_intersection_path[OF \<open>\<not> r_distinguishable_k M q1 q2 (length xs)\<close> _ \<open>set xs \<subseteq> set (inputs M)\<close>]
          \<open>\<not> (\<exists> p . path (product (from_FSM M q1) (from_FSM M q2)) (q1,q2) p \<and> map fst (p_io p) = xs)\<close> by fastforce
qed


subsubsection \<open>Equivalence of R-Distinguishability Definitions\<close>



lemma r_distinguishable_alt_def :
  assumes "q1 \<in> nodes M" and "q2 \<in> nodes M"
  shows "r_distinguishable M q1 q2 \<longleftrightarrow> (\<exists> k . r_distinguishable_k M q1 q2 k)"
proof 
  show "r_distinguishable M q1 q2 \<Longrightarrow> \<exists>k. r_distinguishable_k M q1 q2 k" 
  proof (rule ccontr)

    (* Proof sketch: if no k exists such that q1 and q2 are r(k)-distinguishable, then 
                     it is possible to construct a complete submachine of the product 
                     machine (product (from_FSM M q1) (from_FSM M q2)) by using only those
                     transitions in (product (from_FSM M q1) (from_FSM M q2)) that lead
                     from a pair of non r(0)-distinguishable states to a pair that is not
                     r(j)-distinguishable for any j. 
    *)


    assume "r_distinguishable M q1 q2"
    assume c_assm: "\<nexists>k. r_distinguishable_k M q1 q2 k"
  
    let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
    (* filter function to restrict transitions of ?P *)
    let ?f = "\<lambda> t . \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> \<not> (\<exists> k . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)"
    let ?ft = "filter ?f (transitions ?P)"
    (* resulting submachine of ?P *)
    let ?PC = "?P\<lparr> transitions := ?ft \<rparr>" 
  
  
    have h_ft : "h ?PC \<subseteq> { t \<in> h ?P . ?f t }" 
      using transition_filter_h[of _ ?f ?P] by blast
  
    
    have nodes_non_r_d_k : "\<And> q . q \<in> nodes ?PC \<Longrightarrow> \<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
    proof -   
      fix q assume "q \<in> nodes ?PC"
      have "q = initial ?PC \<or> (\<exists> t \<in> h ?PC . q = t_target t)"
        using nodes_initial_or_target[OF \<open>q \<in> nodes ?PC\<close>] by blast 
      then have "q = (q1,q2) \<or> (\<exists> t \<in> h ?PC . q = t_target t)"
        by (metis (no_types, lifting) product.simps from_FSM_product_initial select_convs(1) update_convs(4))
      show "\<not> (\<exists> k . r_distinguishable_k M (fst q) (snd q) k)"
      proof (cases "q = (q1,q2)")
        case True
        then show ?thesis using c_assm by auto
      next
        case False
        then obtain t where "t \<in> h ?PC" and "q = t_target t" using \<open>q = (q1,q2) \<or> (\<exists> t \<in> h ?PC . q = t_target t)\<close> by blast
        then show ?thesis
          using h_ft by blast 
      qed
    qed

    have "\<And> q . q \<in> nodes ?PC \<Longrightarrow> completely_specified_state ?PC q"  
    proof -
      fix q assume "q \<in> nodes ?PC"
      then have "q \<in> nodes ?P"
        using transition_filter_nodes[of ?f ?P] by blast

      show "completely_specified_state ?PC q"
      proof (rule ccontr)
        assume "\<not> completely_specified_state ?PC q"
        then obtain x where "x \<in> set (inputs ?PC)" 
                        and "\<not>(\<exists> t \<in> h ?PC . t_source t = q \<and> t_input t = x)"
          unfolding completely_specified_state.simps by blast
        then have "\<not>(\<exists> t \<in> h ?P . t_source t = q \<and> t_input t = x \<and> ?f t)"
          using transition_filter_state_transitions[of _ ?f ?P]
          using \<open>q \<in> nodes (product (from_FSM M q1) (from_FSM M q2) \<lparr>transitions := filter (\<lambda>t. \<not> r_distinguishable_k M (fst (t_source t)) (snd (t_source t)) 0 \<and> (\<nexists>k. r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k)) (transitions (product (from_FSM M q1) (from_FSM M q2)))\<rparr>)\<close> by blast
        then have not_f : "\<And> t . t \<in> h ?P \<Longrightarrow> t_source t = q \<Longrightarrow> t_input t = x \<Longrightarrow> \<not> ?f t"
          by blast


        have "\<exists> k . r_distinguishable_k M (fst q) (snd q) k"
        proof (cases "r_distinguishable_k M (fst q) (snd q) 0")
          case True
          then show ?thesis by blast
        next
          case False


          let ?tp = "{t . t \<in> h ?P \<and> t_source t = q \<and> t_input t = x}"
          have "finite ?tp" 
          proof -
            have "finite (h ?P)" by blast 
            moreover have "?tp \<subseteq> h ?P" by blast
            ultimately show ?thesis using finite_subset by blast 
          qed
  
          have k_ex : "\<forall> t \<in> ?tp . \<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"
          proof 
            fix t assume "t \<in> ?tp"
            then have "\<not> ?f t" using not_f by blast
            then obtain k where "r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
              using False \<open>t \<in> ?tp\<close> by blast
            then have "\<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"
              using nat_induct_at_least by fastforce
            then show "\<exists> k . \<forall> k' . k' \<ge> k \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'" by auto
          qed

          obtain k where k_def : "\<And> t . t \<in> ?tp \<Longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"          
            using finite_set_min_param_ex[OF \<open>finite ?tp\<close>, of "\<lambda> t k' . r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k'"]  k_ex by blast
          
          then have "\<forall> t \<in> h ?P . (t_source t = q \<and> t_input t = x) \<longrightarrow> r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
            by blast
          
          have "r_distinguishable_k M (fst q) (snd q) (Suc k)"
          proof - 
            have "\<And> t1 t2 . t1 \<in> h M \<Longrightarrow> t2 \<in> h M \<Longrightarrow> t_source t1 = fst q \<Longrightarrow> t_source t2 = snd q \<Longrightarrow> t_input t1 = x \<Longrightarrow> t_input t2 = x \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
            proof -
              fix t1 t2 assume "t1 \<in> h M" 
                           and "t2 \<in> h M" 
                           and "t_source t1 = fst q" 
                           and "t_source t2 = snd q" 
                           and "t_input t1 = x" 
                           and "t_input t2 = x" 
                           and "t_output t1 = t_output t2"
              then have "t_input t1 = t_input t2"
                    and "t_output t1 = t_output t2" by auto

              
              have "(fst q, snd q) \<in> nodes ?P" using  \<open>q \<in> nodes ?P\<close> by (metis prod.collapse)
              then have "fst q \<in> nodes (from_FSM M q1)" 
                    and "snd q \<in> nodes (from_FSM M q2)"
                using product_nodes[of "from_FSM M q1" "from_FSM M q2"] by blast+
  
              have "t1 \<in> h (from_FSM M q1)"
                using \<open>t1 \<in> h M\<close> \<open>fst q \<in> nodes (from_FSM M q1)\<close> \<open>t_source t1 = fst q\<close> by auto
              have "t2 \<in> h (from_FSM M q2)"
                using \<open>t2 \<in> h M\<close> \<open>snd q \<in> nodes (from_FSM M q2)\<close> \<open>t_source t2 = snd q\<close> by auto

              obtain p where "path ?P (q1,q2) p" and "target p (q1,q2) = (fst q, snd q)"
                using path_to_node[OF \<open>(fst q, snd q) \<in> nodes ?P\<close>] by (metis from_FSM_product_initial) 
              

              then have "path (from_FSM M q1) (initial (from_FSM M q1)) (left_path p)"
               and "path (from_FSM M q2) (initial (from_FSM M q2)) (right_path p)"
                using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p] by auto
              moreover have "target (left_path p) (initial (from_FSM M q1)) = t_source t1"
                by (metis (no_types) \<open>t_source t1 = fst q\<close> \<open>target p (q1, q2) = (fst q, snd q)\<close> from_FSM_simps(1) product_target_split(1))
              moreover have "target (right_path p) (initial (from_FSM M q2)) = t_source t2"
                by (metis (no_types) \<open>t_source t2 = snd q\<close> \<open>target p (q1, q2) = (fst q, snd q)\<close> from_FSM_simps(1) product_target_split(2))
              moreover have "p_io (left_path p) = p_io (right_path p)"
                by auto
              ultimately have px : "\<exists>p1 p2.
                                       path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
                                       path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
                                       target p1 (initial (from_FSM M q1)) = t_source t1 \<and>
                                       target p2 (initial (from_FSM M q2)) = t_source t2 \<and> p_io p1 = p_io p2" 
                by blast
              
              have "t_source ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) = q"
                using \<open>t_source t1 = fst q\<close> \<open>t_source t2 = snd q\<close> by auto
              moreover have "t_input ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) = x"
                using \<open>t_input t1 = x\<close> by auto
              ultimately have tt: "((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) \<in> ?tp"
                using product_transition_from_transitions[OF \<open>t1 \<in> h (from_FSM M q1)\<close> \<open>t2 \<in> h (from_FSM M q2)\<close> \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close> px] by blast
              
              show "r_distinguishable_k M (t_target t1) (t_target t2) k"
                using k_def[OF tt] by auto
            qed

            moreover have "x \<in> set (inputs M)" 
              using \<open>x \<in> set (inputs ?PC)\<close> unfolding product.simps from_FSM.simps by fastforce
            ultimately show ?thesis
              unfolding r_distinguishable_k.simps by blast
          qed
          then show ?thesis by blast
        qed

        then show "False" using nodes_non_r_d_k[OF \<open>q \<in> nodes ?PC\<close>] by blast
      qed
    qed
        
    then have "completely_specified ?PC"
      using completely_specified_states by blast 
  
    moreover have "is_submachine ?PC ?P"
       using transition_filter_submachine by metis
  
    ultimately have "r_compatible M q1 q2"
      unfolding r_compatible_def by blast
    then show "False" using \<open>r_distinguishable M q1 q2\<close>
      by blast 
  qed    

  

  show "\<exists>k. r_distinguishable_k M q1 q2 k \<Longrightarrow> r_distinguishable M q1 q2"
  proof (rule ccontr)
    assume *: "\<not> r_distinguishable M q1 q2"
    assume **: "\<exists>k. r_distinguishable_k M q1 q2 k"        
    then obtain k where "r_distinguishable_k M q1 q2 k" by auto
    then show "False"
    using * assms proof (induction k arbitrary: q1 q2)
      case 0
      then obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                      and "completely_specified S"
        by (meson r_compatible_def)      
      then have "completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2)))"
        using complete_submachine_initial by metis
      then show "False" using r_distinguishable_k_0_not_completely_specified[OF "0.prems"(1,3,4) ] by metis
    next
      case (Suc k)
      then show "False" 
      proof (cases "r_distinguishable_k M q1 q2 k")
        case True
        then show ?thesis 
          using Suc.IH Suc.prems by blast 
      next
        case False
        then obtain x where "x \<in> set (inputs M)"
                        and "\<forall>y q1' q2'. (q1, x, y, q1') \<in> h M \<and> (q2, x, y, q2') \<in> h M \<longrightarrow> r_distinguishable_k M q1' q2' k"
          using Suc.prems(1) by fastforce

        from Suc obtain S where "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
                            and "completely_specified S"
          by (meson r_compatible_def) 

        have "x \<in> set (inputs (product (from_FSM M q1) (from_FSM M q2)))"
          using \<open>x \<in> set (inputs M)\<close> by auto
        then have "x \<in> set (inputs S)" 
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis is_submachine.elims(2)) 

        moreover have "initial S = (q1,q2)"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          by (metis from_FSM_product_initial is_submachine.elims(2)) 
        ultimately obtain y q1' q2' where "((q1,q2),x,y,(q1',q2')) \<in> h S"
          using \<open>completely_specified S\<close> using nodes.initial by fastforce 
        then have "((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
          using \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close>
          using submachine_h by blast
        then have "(q1, x, y, q1') \<in> h (from_FSM M q1)" and "(q2, x, y, q2') \<in> h (from_FSM M q2)" 
          using product_transition[of q1 q2 x y q1' q2' "from_FSM M q1" "from_FSM M q2"] by presburger+
        
        then have "(q1, x, y, q1') \<in> h M" and "(q2, x, y, q2') \<in> h M" 
          using from_FSM_h[OF Suc.prems(3)] from_FSM_h[OF Suc.prems(4)] by blast+
        then have "r_distinguishable_k M q1' q2' k" 
          using \<open>\<forall>y q1' q2'. (q1, x, y, q1') \<in> h M \<and> (q2, x, y, q2') \<in> h M \<longrightarrow> r_distinguishable_k M q1' q2' k\<close> by blast
        have "r_distinguishable M q1' q2'"
          using Suc.IH[OF \<open>r_distinguishable_k M q1' q2' k\<close>] wf_transition_target[OF \<open>(q1, x, y, q1') \<in> h M\<close>] wf_transition_target[OF \<open>(q2, x, y, q2') \<in> h M\<close>] by auto
        moreover have "\<exists> S' . completely_specified S' \<and> is_submachine S' (product (from_FSM M q1') (from_FSM M q2'))"
          using \<open>((q1,q2),x,y,(q1',q2')) \<in> h S\<close>
          by (meson \<open>completely_specified S\<close> \<open>is_submachine S (product (from_FSM M q1) (from_FSM M q2))\<close> submachine_transition_complete_product_from submachine_transition_product_from) 

        ultimately show "False" unfolding r_compatible_def by blast
      qed
    qed
  qed
qed

end