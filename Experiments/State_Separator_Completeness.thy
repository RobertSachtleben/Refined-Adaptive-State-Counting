theory State_Separator_Completeness
imports State_Separator
begin


(* lemma s_states_exhaustiveness :
  assumes "r_distinguishable_k M q1 q2 k"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"
shows "\<exists> qqt \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) (size (product (from_FSM M q1) (from_FSM M q2)))) . fst qqt = (q1,q2)" 
using assms proof (induction k arbitrary: q1 q2)
  case 0

  let ?PM = "product (from_FSM M q1) (from_FSM M q2)"

  from 0 obtain x where "x \<in> (inputs M)"
                  and "\<not> (\<exists>t1\<in>(transitions M).
                            \<exists>t2\<in>(transitions M).
                               t_source t1 = q1 \<and>
                               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    unfolding r_distinguishable_k.simps by blast
  then have *: "\<not> (\<exists>t1 \<in> transitions (from_FSM M q1).
                            \<exists>t2 \<in> transitions (from_FSM M q2).
                               t_source t1 = q1 \<and>
                               t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)"
    using from_FSM_h[OF "0.prems"(2)] from_FSM_h[OF "0.prems"(3)] by blast

  then have "\<And> t . t \<in> transitions ?PM \<Longrightarrow> \<not>(t_source t = (q1,q2) \<and> t_input t = x)"
  proof -
    fix t assume "t \<in> transitions ?PM"
    show "\<not>(t_source t = (q1,q2) \<and> t_input t = x)"
    proof 
      assume "t_source t = (q1, q2) \<and> t_input t = x"
      then have "(q1, x, t_output t, fst (t_target t)) \<in> (transitions (from_FSM M q1))"
            and "(q2, x, t_output t, snd (t_target t)) \<in> (transitions (from_FSM M q2))"
        using product_transition_split[OF \<open>t \<in> transitions ?PM\<close>] by auto
      then show "False"
        using * by force
    qed
  qed

  have "(q1,q2) \<in> set (nodes_from_distinct_paths ?PM)"
    using nodes_code nodes.initial product_simps(1) from_FSM_simps(1) by metis
  
  have p_find_1: "\<And> k' . (\<forall> t \<in> transitions ?PM . (t_source t = fst ((q1,q2),x) \<and> t_input t = snd ((q1,q2),x) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM k') . fst qx' = (t_target t))))"
    by (simp add: \<open>\<And>t. t \<in> (transitions (product (from_FSM M q1) (from_FSM M q2))) \<Longrightarrow> \<not> (t_source t = (q1, q2) \<and> t_input t = x)\<close>)

  have p_find_2: "((q1,q2),x) \<in> set (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))"
    using concat_pair_set \<open>x \<in> (inputs M)\<close> \<open>(q1,q2) \<in> set (nodes_from_distinct_paths ?PM)\<close>
  proof -
    have f1: "\<forall>a ps aa f. set (concat (map (\<lambda>p. map (Pair (p::'a \<times> 'a)) (inputs (product (from_FSM (f::('a,'b,'c) fsm) a) (from_FSM f aa)))) ps)) = set (concat (map (\<lambda>p. map (Pair p) (inputs f)) ps))"
      by (simp add: from_FSM_product_inputs)
    have "\<forall>is p ps. p \<in> set (concat (map (\<lambda>p. map (Pair (p::'a \<times> 'a)) is) ps)) \<or> \<not> (fst p \<in> set ps \<and> (snd p::integer) \<in> set is)"
      using concat_pair_set by blast
    then show ?thesis
      using f1 by (metis \<open>(q1, q2) \<in> set (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))\<close> \<open>x \<in> (inputs M)\<close> fst_conv snd_conv)
  qed 


  have p_find: "\<And> k . (\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx') \<Longrightarrow>
               ((\<lambda> qx . (\<forall> qx' \<in> set (s_states ?PM k) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> transitions ?PM . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM k) . fst qx' = (t_target t)))) ((q1,q2),x))
                \<and> ((q1,q2),x) \<in> set (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))"
    using p_find_1 p_find_2
    by (metis fst_conv) 

  have p_find_alt : "\<And> k . (\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx') \<Longrightarrow>
                            find
                              (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k).
                                        fst qx \<noteq> fst qx') \<and>
                                    (\<forall>t\<in>(transitions ?PM).
                                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                                        (\<exists>qx'\<in>set (s_states ?PM k).
                                            fst qx' = t_target t)))
                              (concat
                                (map (\<lambda>q. map (Pair q) (inputs ?PM))
                                  (nodes_from_distinct_paths ?PM))) \<noteq> None" 
    
  proof -
    fix k assume assm: "(\<forall> qx' \<in> set (s_states ?PM k) . (q1,q2) \<noteq> fst qx')"
    show "find
            (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>(transitions ?PM). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states ?PM k). fst qx' = t_target t)))
            (concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM))) \<noteq> None"
      using find_None_iff[of "(\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM k). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>(transitions ?PM). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states ?PM k). fst qx' = t_target t)))"
                             "(concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))" ]
            p_find[OF assm] by blast
  qed
          






  have "\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM))"
  proof (rule ccontr)
    assume "\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM)))"
    
    let ?l = "length (s_states ?PM (size ?PM))"
    have "s_states ?PM (size ?PM) = s_states ?PM ?l"
      by (metis (no_types, hide_lams) s_states_self_length)

    then have l_assm: "\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM ?l))"
      using \<open>\<not> (\<exists> x . ((q1,q2),x) \<in> set (s_states ?PM (size ?PM)))\<close> by auto
    
    then have "(q1,q2) \<notin> set (map fst (s_states ?PM ?l))" by auto

    have "?l \<le> size ?PM"
      using s_states_length by blast
      

    then consider  
      (a) "?l = 0" |
      (b) "0 < ?l \<and> ?l < size ?PM" |
      (c) "?l = size ?PM"
      using nat_less_le by blast
    then show "False" proof cases
      case a 
      
      then have "(s_states ?PM (Suc 0)) = []"
        by (metis s_states_prefix s_states_self_length s_states_size take_eq_Nil)
      then have *: "find
              (\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t)))
              (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) = None"
        unfolding s_states.simps
        using find_None_iff by fastforce 
      then have "\<not>(\<exists> qqt \<in> set (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) . (\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t))) qqt)"
        unfolding s_states.simps
        using find_None_iff[of "(\<lambda>qx. (\<forall>qx'\<in>set []. fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set []. fst qx' = t_target t)))" "(concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))" ] by blast
      then have "\<not>(\<exists> qqt \<in> set (concat
                (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) . (\<lambda>qx. (\<forall>qx'\<in>set (s_states ?PM 0). fst qx \<noteq> fst qx') \<and>
                    (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        (\<exists>qx'\<in>set (s_states ?PM 0). fst qx' = t_target t))) qqt)"
        unfolding s_states.simps by assumption

      then show "False"
        using p_find[of 0]
        by (metis \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> a length_0_conv length_greater_0_conv length_pos_if_in_set)  

    next 
      case b
      
      then obtain l' where Suc: "?l = Suc l'" using gr0_conv_Suc by blast
      moreover obtain l where "l = ?l" by auto
      ultimately have "l = Suc l'" by auto

      have "s_states ?PM ?l = s_states ?PM (Suc ?l)"
        using s_states_prefix[of ?l "Suc ?l"] s_states_max_iterations
      proof -
        have "\<forall>n. n \<le> Suc n"
          by simp
        then show ?thesis
          by (metis Suc_le_mono \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> s_states_length s_states_max_iterations s_states_prefix take_all)
      qed 

      have "length (s_states ?PM l') < length (s_states ?PM ?l)" using Suc
        using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> less_Suc_eq_le s_states_length by auto

      have "length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) = l"
        using \<open>l = length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))\<close> \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))))\<close> by auto
      then have "\<not>(length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) < l)"
        by force

      have "\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). (q1, q2) \<noteq> fst qx'"
        using l_assm \<open>l = ?l\<close>
        by auto 

      have "s_states ?PM l = s_states ?PM (Suc l)"
      proof -
        show ?thesis
          using \<open>length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2)))) = Suc l'\<close> \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))) = s_states (product (from_FSM M q1) (from_FSM M q2)) (Suc (length (s_states (product (from_FSM M q1) (from_FSM M q2)) (FSM.size (product (from_FSM M q1) (from_FSM M q2))))))\<close> 
          using \<open>l = Suc l'\<close>
          by presburger
      qed
      then have "s_states ?PM l = (case find
                (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                          fst qx \<noteq> fst qx') \<and>
                      (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                              fst qx' = t_target t)))
                (concat
                  (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) of
          None \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l
          | Some qx \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [qx])"
        unfolding s_states.simps
        using \<open>\<not>(length (s_states (product (from_FSM M q1) (from_FSM M q2)) l) < l)\<close> by force

      then have "find
                (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                          fst qx \<noteq> fst qx') \<and>
                      (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l).
                              fst qx' = t_target t)))
                (concat
                  (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2))))
                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) = None"
      proof -
        have "s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [the (find (\<lambda>p. (\<forall>pa. pa \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) l) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<forall>pa. pa \<in> (transitions (product (from_FSM M q1) (from_FSM M q2))) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> (\<exists>p. p \<in> set (s_states (product (from_FSM M q1) (from_FSM M q2)) l) \<and> fst p = t_target pa))) (concat (map (\<lambda>p. map (Pair p) (inputs (product (from_FSM M q1) (from_FSM M q2)))) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))] \<noteq> s_states (product (from_FSM M q1) (from_FSM M q2)) l"
          by force
        then show ?thesis
          using \<open>s_states (product (from_FSM M q1) (from_FSM M q2)) l = (case find (\<lambda>qx. (\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). fst qx \<noteq> fst qx') \<and> (\<forall>t\<in>(transitions (product (from_FSM M q1) (from_FSM M q2))). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> (\<exists>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs (product (from_FSM M q1) (from_FSM M q2)))) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))) of None \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l | Some qx \<Rightarrow> s_states (product (from_FSM M q1) (from_FSM M q2)) l @ [qx])\<close> by force
      qed 

      then show "False" using p_find_alt[OF \<open>\<forall>qx'\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2)) l). (q1, q2) \<noteq> fst qx'\<close>] by blast
    next
      case c
      have "distinct (map fst (s_states ?PM ?l))"
        using s_states_distinct_states by blast
      then have "card (set (map fst (s_states ?PM ?l))) = size ?PM"
        using c distinct_card by fastforce 
      moreover have "set (map fst (s_states ?PM ?l)) \<subseteq> nodes ?PM"
        using s_states_nodes by metis
      ultimately have "set (map fst (s_states ?PM ?l)) = nodes ?PM"
        using nodes_finite[of ?PM]
        by (simp add: card_subset_eq) 

      then  have "(q1,q2) \<notin> nodes ?PM"
        using \<open>(q1,q2) \<notin> set (map fst (s_states ?PM ?l))\<close>
        by blast 
      moreover have "(q1,q2) \<in> nodes ?PM"
        using nodes.initial[of ?PM] product_simps(1) from_FSM_simps(1) by metis
      ultimately show "False" 
        by blast
    qed 
  qed

  then show ?case
    by (meson fst_conv)
next
  case (Suc k)

  (* sketch: 
    \<longrightarrow> cases Suc k = LEAST,
      \<longrightarrow> FALSE: then also k \<longrightarrow> by IH
      \<longrightarrow> TRUE
        \<longrightarrow> \<noteq> 0
        \<longrightarrow> exists input x such that for every ((q1,q2),x,y,(s1,s2)) \<in> transitions ?PM , s1 and s2 are r(k)-d
          \<longrightarrow> (s1,s2) is contained in s_states for product for s1 s2
          \<longrightarrow> also: (s1,s2) (initial state of the above) is a node of product for q1 q2
          \<longrightarrow> then (s1,s2) is in s_states for product for q1 q2
          \<longrightarrow> by construction there must then exist some x' s.t. ((q1,q2),x') \<in> s_states 
  *)
  
  let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"

  show ?case proof (cases "r_distinguishable_k M q1 q2 k")
    case True
    show ?thesis using Suc.IH[OF True Suc.prems(2,3)] by assumption
  next
    case False
    then obtain x where "x \<in> (inputs M)"
                    and "\<forall>t1\<in>(transitions M).
                           \<forall>t2\<in>(transitions M).
                              t_source t1 = q1 \<and>
                              t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                              r_distinguishable_k M (t_target t1) (t_target t2) k"
      using Suc.prems(1) unfolding r_distinguishable_k.simps by blast
    then have x_transitions: "\<forall>t1\<in>(transitions (from_FSM M q1)).
                               \<forall>t2\<in>(transitions (from_FSM M q2)).
                                  t_source t1 = q1 \<and>
                                  t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                                  r_distinguishable_k M (t_target t1) (t_target t2) k"
      using from_FSM_h[OF Suc.prems(2)] from_FSM_h[OF Suc.prems(3)] by blast
    


    have x_prop: "\<And> t . t \<in> transitions ?PM \<Longrightarrow> t_source t = (q1,q2) \<Longrightarrow> t_input t = x \<Longrightarrow> 
                (\<exists>qqt\<in>set (s_states ?PM (size ?PM)) .
                   fst qqt = t_target t)"
    proof -
      fix t assume "t \<in> transitions ?PM" and "t_source t = (q1,q2)" and "t_input t = x"

      have *: "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> (transitions (from_FSM M q1))"
      and **: "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> (transitions (from_FSM M q2))"
        using product_transition_t[of t "from_FSM M q1" "from_FSM M q2"] \<open>t \<in> transitions ?PM\<close>  by simp+

      then have "(q1,x,t_output t,fst (t_target t)) \<in> transitions (from_FSM M q1)"
           and  "(q2,x,t_output t,snd (t_target t)) \<in> transitions (from_FSM M q2)"
        using \<open>t_source t = (q1,q2)\<close> \<open>t_input t = x\<close> by simp+

      then have "r_distinguishable_k M (fst (t_target t)) (snd (t_target t)) k"
        using x_transitions by auto
      moreover have "fst (t_target t) \<in> nodes M"
        using from_FSM_nodes[OF Suc.prems(2)] wf_transition_target[OF *] by auto
      moreover have "snd (t_target t) \<in> nodes M"
        using from_FSM_nodes[OF Suc.prems(3)] wf_transition_target[OF **] by auto

      ultimately have "\<exists>qqt\<in>set (s_states (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))
                                  (FSM.size (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))))).
                         fst qqt = (fst (t_target t), snd (t_target t))"
        using Suc.IH[of "(fst (t_target t))" "(snd (t_target t))"] by blast

      then obtain qqt where qqt_def: "qqt\<in>set (s_states (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))
                                  (FSM.size (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))))"
                      and   "fst qqt = (fst (t_target t), snd (t_target t))" 
        by blast


      let ?PM' = "product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t)))"
      have "?PM = ?PM'"
        using \<open>t_source t = (q1,q2)\<close> by auto
      then have "t \<in> transitions ?PM'"
        using \<open>t \<in> transitions ?PM\<close> by simp

      show "\<exists>qqt\<in>set (s_states (product (from_FSM M q1) (from_FSM M q2))
                     (FSM.size (product (from_FSM M q1) (from_FSM M q2)))).
            fst qqt = t_target t"
        using s_states_step_prod[OF qqt_def \<open>t \<in> transitions ?PM'\<close>] \<open>?PM = ?PM'\<close> 
              \<open>fst qqt = (fst (t_target t), snd (t_target t))\<close>
        by (metis prod.collapse)
    qed


    let ?l = "length (s_states ?PM (size ?PM))"
    have "s_states ?PM (size ?PM) = s_states ?PM ?l"
      using s_states_self_length by blast
    then have "s_states ?PM ?l = s_states ?PM (Suc ?l)"
      by (metis Suc_n_not_le_n nat_le_linear s_states_max_iterations s_states_prefix take_all)

    have "\<exists>qqx'\<in>set (s_states ?PM ?l). (q1,q2) = fst qqx'"  proof (rule ccontr)
      assume c_assm: "\<not> (\<exists>qqx'\<in>set (s_states ?PM ?l). (q1,q2) = fst qqx')"
      

      have "(\<forall>qx'\<in>set (s_states ?PM ?l). (q1,q2) \<noteq> fst qx')"
        using c_assm by blast
      moreover have "\<And> t . t \<in> transitions ?PM \<Longrightarrow>
                t_source t = fst ((q1,q2),x) \<Longrightarrow> 
                t_input t = snd ((q1,q2),x) \<Longrightarrow>
                (\<exists>qx'\<in>set (s_states ?PM ?l). fst qx' = t_target t)"
        using x_prop snd_conv[of "(q1,q2)" x] fst_conv[of "(q1,q2)" x] \<open>s_states ?PM (size ?PM) = s_states ?PM ?l\<close> by auto 
      ultimately have "(\<lambda> qx . (\<forall> qx' \<in> set (s_states ?PM ?l) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> transitions ?PM . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM ?l) . fst qx' = (t_target t)))) ((q1,q2),x)"
        by auto
      moreover have "((q1,q2),x) \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))"
      proof -
        have "fst ((q1,q2),x) \<in> set (nodes_from_distinct_paths ?PM)" 
          using nodes.initial nodes_code 
                fst_conv product_simps(1) from_FSM_simps(1)
          by metis 
        moreover have "snd ((q1,q2),x) \<in> (inputs ?PM)"
          using \<open>x \<in> (inputs M)\<close>
          by (simp add: from_FSM_simps(2) product_simps(2)) 
        ultimately show ?thesis using concat_pair_set[of "inputs ?PM" "nodes_from_distinct_paths ?PM"]
          by blast 
      qed
      ultimately have "find 
                  (\<lambda> qx . (\<forall> qx' \<in> set (s_states ?PM ?l) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> transitions ?PM . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM ?l) . fst qx' = (t_target t)))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?PM)) (nodes_from_distinct_paths ?PM))) \<noteq> None"
        using find_from[of "(concat (map (\<lambda>q. map (Pair q) (inputs ?PM)) (nodes_from_distinct_paths ?PM)))" "(\<lambda> qx . (\<forall> qx' \<in> set (s_states ?PM ?l) . fst qx \<noteq> fst qx') \<and> (\<forall> t \<in> transitions ?PM . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (\<exists> qx' \<in> set (s_states ?PM ?l) . fst qx' = (t_target t))))"] by blast

      then have "s_states ?PM (Suc ?l) \<noteq> s_states ?PM ?l"
        unfolding s_states.simps
        using \<open>s_states ?PM (FSM.size ?PM) = s_states ?PM ?l\<close> by auto
      then show "False"
        using \<open>s_states ?PM ?l = s_states ?PM (Suc ?l)\<close>
        by simp
    qed

    then show ?thesis
      using \<open>s_states ?PM (size ?PM) = s_states ?PM ?l\<close>
      by force 
  qed
qed



lemma calculate_state_separator_from_s_states_exhaustiveness :
  assumes "r_distinguishable_k M q1 q2 k"
  and "q1 \<in> nodes M"
  and "q2 \<in> nodes M"   
shows "calculate_state_separator_from_s_states M q1 q2 \<noteq> None" 
proof -

  let ?PM = "product (from_FSM M q1) (from_FSM M q2)"
  let ?SS = "s_states_opt ?PM (FSM.size ?PM)"

  have "\<exists> qqt \<in> set (s_states ?PM (size ?PM)) . fst qqt = (q1, q2)"
    using s_states_exhaustiveness[OF \<open>r_distinguishable_k M q1 q2 k\<close> assms(2,3)] by blast

  have "find_index (\<lambda>qqt. fst qqt = (q1, q2)) ?SS \<noteq> None"
    using find_index_exhaustive[OF \<open>\<exists> qqt \<in> set (s_states ?PM (size ?PM)) . fst qqt = (q1, q2)\<close>]
    by (simp add: s_states_code) 


  then obtain S where "calculate_state_separator_from_s_states M q1 q2 = Some S"
    unfolding calculate_state_separator_from_s_states_def Let_def
    by (meson option.case_eq_if)

  then show ?thesis by auto
qed

*)







(* lemma r_distinguishability_implies_state_separator :
  assumes "r_distinguishable M q1 q2"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "completely_specified M"
shows "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
proof -

  let ?PM = "product (from_FSM M q1) (from_FSM M q2)"
  let ?SS = "s_states_opt ?PM (FSM.size ?PM)"

  obtain k where "r_distinguishable_k M q1 q2 k"
    by (meson assms r_distinguishable_alt_def) 

  then obtain S where "calculate_state_separator_from_s_states M q1 q2 = Some S"
    using calculate_state_separator_from_s_states_exhaustiveness[OF _ assms(2,3)] by blast

  show ?thesis
    using calculate_state_separator_from_s_states_soundness
            [OF \<open>calculate_state_separator_from_s_states M q1 q2 = Some S\<close> assms(2,3,4,5)] by blast
qed



lemma r_distinguishable_iff_state_separator_exists :
  assumes "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "completely_specified M"
shows "r_distinguishable M q1 q2 \<longleftrightarrow> (\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S)"
  using r_distinguishability_implies_state_separator[OF _ assms] state_separator_r_distinguishes_k r_distinguishable_alt_def[OF assms(1,2)]  
  by metis

*)



end