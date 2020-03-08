theory State_Preamble_Completeness
  imports State_Preamble
begin

subsubsection \<open>Simpler Versions of the Preamble Calculation Algorithm\<close>

fun d_states'_without_shortcut :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "d_states'_without_shortcut f q inputList nodeList nodeSet 0 m = m" |
  "d_states'_without_shortcut f q inputList nodeList nodeSet (Suc k) m = 
    (case find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList
          of None            \<Rightarrow> m |
             Some (q',x,nodeList') \<Rightarrow> d_states'_without_shortcut f q inputList nodeList' (insert q' nodeSet) k (m@[(q',x)]))"

lemma d_states'_without_shortcut_eq :
  assumes "q0 \<notin> set (map fst (d_states' f q q0 iL nL nS k m))"
  shows "(d_states' f q q0 iL nL nS k m) = (d_states'_without_shortcut f q iL nL nS k m)" 
using assms proof (induction k arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL"; auto)
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)
      have "(d_states' f q q0 iL nL nS (Suc k) m) = (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)]))"
      and  "(d_states'_without_shortcut f q iL nL nS (Suc k) m) = (d_states'_without_shortcut f q iL nL' (insert q' nS) k (m@[(q',x)]))"
        unfolding None * d_states'.simps d_states'_without_shortcut.simps by auto
      then show ?thesis using Suc by presburger 
    qed
  next
    case (Some a)
    then show ?thesis using Suc by auto
  qed
qed



fun d_states'_without_nodeList_removal :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "d_states'_without_nodeList_removal f q inputList nodeList 0 m = m" |
  "d_states'_without_nodeList_removal f q inputList nodeList (Suc k) m = 
    (case find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nodeList inputList
          of None            \<Rightarrow> m |
             Some (q',x,_) \<Rightarrow> d_states'_without_nodeList_removal f q inputList nodeList k (m@[(q',x)]))"

lemma filter_filter' :
  "filter P1 (filter P2 xs) = filter (\<lambda> x . P1 x \<and> P2 x) xs"
  by (metis (mono_tags, lifting) filter_cong filter_filter) 




lemma d_states'_without_nodeList_removal_eq :
  assumes "distinct nL"
shows "d_states'_without_shortcut f q iL (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) (insert q (set (map fst m))) k m = d_states'_without_nodeList_removal f q iL nL k m" 
proof (induction k arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc k)

  show ?case 
  proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> (insert q (set (map fst m)))))) (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) iL")
    case None
    then have "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL = None"
      unfolding find_remove_2_None_iff by auto
    then show ?thesis using None by auto
  next
    case (Some a)
    then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> (insert q (set (map fst m)))))) (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) iL = Some (q',x,nL')"
      by (metis prod_cases3)
    
    have "d_states'_without_shortcut f q iL (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) (insert q (set (map fst m))) (Suc k) m
          = (d_states'_without_shortcut f q iL (remove1 q' (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL)) (insert q' (insert q (set (map fst m)))) k (m@[(q',x)]))"
      unfolding d_states'_without_shortcut.simps * find_remove_2_set(6)[OF *] by auto
    moreover have "(remove1 q' (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL)) = (filter (\<lambda>q'' . q'' \<notin> insert q (set (map fst (m@[(q',x)])))) nL)"
    proof -
      have "insert q' (insert q (set (map fst m))) = insert q (set (map fst (m@[(q',x)])))"
        by auto

      have "(remove1 q' (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL)) = (removeAll q' (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL))"
        using \<open>distinct nL\<close>
        by (simp add: distinct_remove1_removeAll) 
      also have "... = filter (\<lambda> q'' . q'' \<noteq> q') ((filter (\<lambda>q'' . q'' \<notin> insert q (set (map fst m))) nL))"
        by (metis (mono_tags, lifting) filter_cong removeAll_filter_not_eq)
      also have "... = (filter (\<lambda>q'' . q'' \<notin> insert q (set (map fst m)) \<and> q'' \<noteq> q') nL)"
        using filter_filter by blast 
      also have "... = (filter (\<lambda>q'' . q'' \<notin> insert q' (insert q (set (map fst m)))) nL)"
        by (metis insert_iff)
      also have "... = (filter (\<lambda>q'' . q'' \<notin> insert q (set (map fst (m@[(q',x)])))) nL)"
        unfolding \<open>insert q' (insert q (set (map fst m))) = insert q (set (map fst (m@[(q',x)])))\<close> by auto
      finally show ?thesis by assumption
    qed
    moreover have "(insert q' (insert q (set (map fst m)))) = (insert q (set (map fst (m@[(q',x)]))))"
      by auto
    ultimately have d1: "d_states'_without_shortcut f q iL (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) (insert q (set (map fst m))) (Suc k) m
                   = (d_states'_without_shortcut f q iL (filter (\<lambda>q'' . q'' \<notin> insert q (set (map fst (m@[(q',x)])))) nL) (insert q (set (map fst (m@[(q',x)])))) k (m@[(q',x)]))"
      by simp

    
    have **: "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) iL = Some (q',x,nL')"
      using find_remove_2_strengthening[OF \<open>find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> (insert q (set (map fst m)))))) (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) iL = Some (q',x,nL')\<close>,
                                        of \<open>(\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m)))))\<close>]
            find_remove_2_set(1,2)[OF \<open>find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> (insert q (set (map fst m)))))) (filter (\<lambda>q' . q' \<notin> insert q (set (map fst m))) nL) iL = Some (q',x,nL')\<close>]
      by simp

    obtain nL'' where ***: "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL = Some (q',x,nL'')"
      using find_remove_2_filter[OF **]
      by blast 

    have d2: "d_states'_without_nodeList_removal f q iL nL (Suc k) m = d_states'_without_nodeList_removal f q iL nL k (m@[(q',x)])"
      using *** by auto

    

    show ?thesis
      using Suc.IH[of "m@[(q',x)]"] unfolding d1 d2 by assumption
  qed
qed

value "d_states'_without_nodeList_removal (h m_ex_DR) 400 (inputs_as_list m_ex_DR) (nodes_as_list m_ex_DR) 0 [(1000,1000)]"
value "d_states'_without_nodeList_removal (h m_ex_DR) 400 (inputs_as_list m_ex_DR) (nodes_as_list m_ex_DR) 1 [(1000,1000)]"
value "d_states'_without_nodeList_removal (h m_ex_DR) 400 (inputs_as_list m_ex_DR) (nodes_as_list m_ex_DR) 2 [(1000,1000)]"
value "d_states'_without_nodeList_removal (h m_ex_DR) 400 (inputs_as_list m_ex_DR) (nodes_as_list m_ex_DR) 3 [(1000,1000)]"



lemma d_states'_without_nodeList_removal_take_m : "take (length m) (d_states'_without_nodeList_removal f q iL nL k m) = m" 
proof (induction k arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc k)
  show ?case proof (cases "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL")
    case None
    then show ?thesis by auto
  next
    case (Some a)
    then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL = Some (q',x,nL')"
      by (metis prod_cases3)
    then have **: "(d_states'_without_nodeList_removal f q iL nL k (m@[(q',x)])) = (d_states'_without_nodeList_removal f q iL nL (Suc k) m)"
      by auto
    have scheme : "\<And> xs ys y . (take (length (ys@y)) xs = (ys@y)) \<Longrightarrow> (take (length ys) xs = ys)"
      by (metis append.assoc append_eq_conv_conj) 

    then show ?thesis using Suc.IH[of "m@[(q',x)]"] unfolding **  by blast
  qed
qed

lemma d_states'_without_nodeList_removal_length : "length (d_states'_without_nodeList_removal f q iL nL k m) \<le> length m + k" 
proof (induction k arbitrary: m)
  case 0
  then show ?case by auto
next
  case (Suc k)
  show ?case proof (cases "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL")
    case None
    then show ?thesis by auto
  next
    case (Some a)
    then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL = Some (q',x,nL')"
      by (metis prod_cases3)
    then show ?thesis using Suc.IH[of "m@[(q',x)]"] by simp
  qed
qed



lemma d_states'_without_nodeList_removal_take :
  (*assumes "(length m + i) \<le> length (d_states'_without_nodeList_removal f q iL nL k m)"*)
  assumes "i \<le> k"
  shows   "take (length m + i) (d_states'_without_nodeList_removal f q iL nL k m) = (d_states'_without_nodeList_removal f q iL nL i m)" 
using assms proof (induction "k - i" arbitrary: m i k)
  case 0
  then have "i = k" by auto
  then show ?case
    by (simp add: d_states'_without_nodeList_removal_length) 
next
  case (Suc d)
  

  then show ?case proof (induction i arbitrary: m d)
    case 0
    show ?case using d_states'_without_nodeList_removal_take_m by auto
  next
    case (Suc i)
    
    have "d = k - Suc (Suc i)" using Suc.prems(2)
      by auto 
    moreover obtain k' where "k = Suc k'" using Suc.prems(3)
      using Suc_le_D by auto 
    ultimately have "d = k' - Suc i" by auto

    consider (a) "Suc i = k" |
             (b) "Suc i < k"
      using Suc.prems(3)
      using le_neq_implies_less by blast 
    then show ?case proof cases
      case a
      then  show ?thesis by (simp add: d_states'_without_nodeList_removal_length) 
    next
      case b
      then have "Suc (Suc i) \<le> k" by auto
      then have "Suc i \<le> k'"
        using \<open>k = Suc k'\<close> by auto
      have "d = k - Suc (Suc i)"
        using Suc.prems(2) by auto

      thm Suc.IH
      thm Suc.prems(1)[of k "Suc (Suc i)", OF \<open>d = k - Suc (Suc i)\<close> \<open>Suc (Suc i) \<le> k\<close>]

      thm Suc.hyps(1)[OF \<open>d = k - Suc (Suc i)\<close> \<open>Suc (Suc i) \<le> k\<close>]
      thm Suc.hyps(1)[OF \<open>d = k' - (Suc i)\<close> \<open>(Suc i) \<le> k'\<close>]
      
      have ih: "\<And> m . Suc d = k - i \<Longrightarrow> i \<le> k \<Longrightarrow> take (length m + i) (d_states'_without_nodeList_removal f q iL nL k m) = d_states'_without_nodeList_removal f q iL nL i m"
        using Suc.IH[OF Suc.hyps(1)] by blast


      show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL")
        case None 
        then show ?thesis by (cases k; cases i; auto)
      next
        case (Some a)
        then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst m)) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst m))))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)
    
        then have d1: "(d_states'_without_nodeList_removal f q iL nL (Suc k') m) = (d_states'_without_nodeList_removal f q iL nL k' (m@[(q',x)]))"
             and  d2: "(d_states'_without_nodeList_removal f q iL nL (Suc i) m) = (d_states'_without_nodeList_removal f q iL nL i (m@[(q',x)]))"
             and  d3: "(d_states'_without_nodeList_removal f q iL nL (Suc (Suc i)) m) = (d_states'_without_nodeList_removal f q iL nL (Suc i) (m@[(q',x)]))" 
          by auto
    
        show ?thesis
          using Suc.hyps(1)[OF \<open>d = k' - Suc i\<close> \<open>Suc i' \<le> k'\<close>, of "m@[(q',x)]"]
          unfolding \<open>k = Suc k'\<close> \<open>i = Suc i'\<close> d1[symmetric] d2[symmetric]
  qed

  
qed

end (*


fun d_states'_append :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "d_states'_append f q inputList nodeList 0 m = m" |
  "d_states'_append f q inputList nodeList (Suc k) m = 
    (case find_remove_2 (\<lambda> q' x . q' \<notin> insert q (set (map fst (d_states'_append f q inputList nodeList k m))) \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> insert q (set (map fst (d_states'_append f q inputList nodeList k m)))))) nodeList inputList
          of None            \<Rightarrow> (d_states'_append f q inputList nodeList k m) |
             Some (q',x,_) \<Rightarrow> (d_states'_append f q inputList nodeList k m)@[(q',x)])"

end (*

lemma calculate_state_preamble_from_d_states_exhaustiveness :
  assumes "is_preamble S M q"
  shows "calculate_state_preamble_from_d_states M q \<noteq> None"
proof -
  have "acyclic S"
  and  "single_input S" 
  and  "is_submachine S M" 
  and  "q \<in> reachable_nodes S"
  and  "deadlock_state S q" 
  and  *: "\<And> q' . q' \<in> reachable_nodes S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state S q')"
  and **: "\<And> q' x . q' \<in> reachable_nodes S \<Longrightarrow> x \<in> inputs M \<Longrightarrow> (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)"
    using assms(1) unfolding is_preamble_def by blast+

  obtain p where "path S (initial S) p" and "target (initial S) p = q"
    using \<open>q \<in> reachable_nodes S\<close> unfolding reachable_nodes_def by blast
  then have "is_preamble S M (target (initial S) p)"
    using assms by auto

  have ***: "\<And> q' t t' . q' \<in> reachable_nodes S \<Longrightarrow> t \<in> transitions S \<Longrightarrow> t_source t = q' \<Longrightarrow> t' \<in> transitions M  \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = t_input t \<Longrightarrow> t' \<in> transitions S"
  proof -
    fix q' t t' assume "q' \<in> reachable_nodes S" and "t_source t = q'" and "t \<in> transitions S" and "t' \<in> transitions M" and "t_source t' = q'" and "t_input t' = t_input t"
    then have "t_input t \<in> inputs M"
      using \<open>is_submachine S M\<close> unfolding is_submachine.simps by auto
    
    show "t' \<in> transitions S"
      using **[OF \<open>q' \<in> reachable_nodes S\<close> \<open>t_input t \<in> inputs M\<close> ] \<open>t_source t = q'\<close> \<open>t_source t' = q'\<close> \<open>t_input t' = t_input t\<close>
      using \<open>t \<in> FSM.transitions S\<close> \<open>t' \<in> FSM.transitions M\<close> by blast
  qed



  have "\<forall>qa\<in>reachable_nodes S. qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (size_r (from_FSM M qa)-1) q). fst qx = qa)"
    using \<open>acyclic S\<close> proof (induction rule:
                              acyclic_induction[of S "\<lambda> q' . q' = q \<or> (\<exists> qx \<in> set (d_states (from_FSM M q') (size_r (from_FSM M q') - 1) q) . fst qx = q')" ])
    case (reachable_node qs)

    have "qs \<in> nodes M" 
      using reachable_node reachable_node_is_node
      using \<open>is_submachine S M\<close> by fastforce 

    obtain pq where "path S qs pq" and "target qs pq = q"
      using * by (metis \<open>FSM.acyclic S\<close> acyclic_paths_to_single_deadlock reachable_node.IH(1))
    then have "q \<in> reachable_nodes (from_FSM M qs)"
      using \<open>is_submachine S M\<close> \<open>qs \<in> nodes M\<close>
      by (metis from_FSM_path_rev_initial from_FSM_simps(1) reachable_nodes_intro submachine_path)
      


    

    have "q \<in> reachable_nodes M"
      using \<open>q \<in> reachable_nodes S\<close> submachine_path_initial[OF \<open>is_submachine S M\<close>] \<open>is_submachine S M\<close>
      unfolding reachable_nodes_def is_submachine.simps
      by auto 


    have "inputs_as_list (from_FSM M qs) = inputs_as_list M"
    and  "h (from_FSM M qs) = h M"
      using from_FSM_simps(2,4)[OF \<open>qs \<in> nodes M\<close>] by auto

    show ?case proof (cases "qs = q")
      case True
      then show ?thesis by auto
    next
      case False
      then have "q \<noteq> initial (from_FSM M qs)"
        unfolding from_FSM_simps(1)[OF \<open>qs \<in> nodes M\<close>] by simp
      

      then have "d_states (from_FSM M qs) (size_r (from_FSM M qs) - 1) q = d_states' (h M) q qs (inputs_as_list M) (removeAll q (removeAll qs (reachable_nodes_as_list (from_FSM M qs)))) {q} (size_r (from_FSM M qs) - 1) []"
                (is "?ds = ?ds'")
           and  "d_states (from_FSM M qs) (Suc (size_r (from_FSM M qs) - 1)) q = d_states' (h M) q qs (inputs_as_list M) (removeAll q (removeAll qs (reachable_nodes_as_list (from_FSM M qs)))) {q} (Suc (size_r (from_FSM M qs) - 1)) []"
                (is "?ds = ?ds''")
        unfolding d_states.simps
                  from_FSM_simps[OF \<open>qs \<in> nodes M\<close>] 
                  \<open>inputs_as_list (from_FSM M qs) = inputs_as_list M\<close>
                  \<open>h (from_FSM M qs) = h M\<close> 
        by simp+

      then have "?ds' = ?ds''" 
        using d_states_max_iterations[of _ "(Suc (size_r (from_FSM M qs) - 1))", OF _ \<open>q \<in> reachable_nodes (from_FSM M qs)\<close>] by simp

      have "(\<exists>qx\<in>set (d_states (FSM.from_FSM M qs) (size_r (FSM.from_FSM M qs) - 1) q). fst qx = qs)"
      proof (rule ccontr)
        assume "\<not> (\<exists>qx\<in>set (d_states (FSM.from_FSM M qs) (size_r (FSM.from_FSM M qs) - 1) q). fst qx = qs)"
        


      
        obtain ts where "ts \<in> transitions S" and "t_source ts = qs"
          using *[OF \<open>qs \<in> reachable_nodes S\<close>] False unfolding deadlock_state.simps by blast
        then have "ts \<in> transitions M"
          using \<open>ts \<in> transitions S\<close> \<open>is_submachine S M\<close> by auto
        then have "(t_output ts, t_target ts) \<in> h M (qs, t_input ts)"
          unfolding h.simps \<open>t_source ts = qs\<close>[symmetric] by simp 
        then have "h M (qs, t_input ts) \<noteq> {}"
          by blast
          

        (* TODO? : use different node list for targets
          \<rightarrow> based on reachable nodes of S from target
          \<rightarrow> each gets (reachable nodes of S from qs - targets)@[target]
             \<rightarrow> all but the last node are shared between each d_states call
             \<rightarrow> all but the last elements in the d_states results are identical between calls
             \<rightarrow> last elements are unique (due to fixed input list order)
             \<rightarrow> qs not contained
          \<rightarrow> BUT: requires transfer from d-reachable nodes in S to all nodes in M?
          \<rightarrow> MAIN BUT: requires result that (\<exists>qx\<in>set (d_states ...). fst qx = t_target t) is independent of the chosen node order
        *)
  
        have ****: "\<And> t . t \<in> transitions S \<Longrightarrow> t_source t = qs \<Longrightarrow> t_input t = t_input ts"
          using \<open>single_input S\<close> by (metis \<open>t_source ts = qs\<close> \<open>ts \<in> FSM.transitions S\<close> single_input.elims(2)) 
  
        have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
                          t_source t = qs \<Longrightarrow>
                          t_input t = t_input ts \<Longrightarrow>
                          t_target t = q \<or>
                          (\<exists>qx\<in>set (d_states (FSM.from_FSM M (t_target t)) (size_r (FSM.from_FSM M (t_target t)) - 1) q).
                              fst qx = t_target t)"
          
          using  ***[OF \<open>qs \<in> reachable_nodes S\<close> \<open>ts \<in> transitions S\<close> \<open>t_source ts = qs\<close>]
          using reachable_node.IH(2)  ****
          by blast 
        then have "\<forall>(y, q'')\<in>h M (qs, t_input ts). q'' \<in> ?nS"

        thm d_states'_q0_containment[of "h M", OF \<open>h M (qs, t_input ts) \<noteq> {}\<close>]



end (*

lemma calculate_state_preamble_from_d_states_exhaustiveness :
  assumes "is_preamble S M q"
  shows "calculate_state_preamble_from_d_states M q \<noteq> None"
proof -
  have "acyclic S"
  and  "single_input S" 
  and  "is_submachine S M" 
  and  "q \<in> reachable_nodes S"
  and  "deadlock_state S q" 
  and  *: "\<And> q' . q' \<in> reachable_nodes S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state S q')"
  and **: "\<And> q' x . q' \<in> reachable_nodes S \<Longrightarrow> x \<in> inputs M \<Longrightarrow> (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)"
    using assms(1) unfolding is_preamble_def by blast+

  obtain p where "path S (initial S) p" and "target (initial S) p = q"
    using \<open>q \<in> reachable_nodes S\<close> unfolding reachable_nodes_def by blast
  then have "is_preamble S M (target (initial S) p)"
    using assms by auto

  have ***: "\<And> q' t t' . q' \<in> reachable_nodes S \<Longrightarrow> t \<in> transitions S \<Longrightarrow> t_source t = q' \<Longrightarrow> t' \<in> transitions M  \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = t_input t \<Longrightarrow> t' \<in> transitions S"
  proof -
    fix q' t t' assume "q' \<in> reachable_nodes S" and "t_source t = q'" and "t \<in> transitions S" and "t' \<in> transitions M" and "t_source t' = q'" and "t_input t' = t_input t"
    then have "t_input t \<in> inputs M"
      using \<open>is_submachine S M\<close> unfolding is_submachine.simps by auto
    
    show "t' \<in> transitions S"
      using **[OF \<open>q' \<in> reachable_nodes S\<close> \<open>t_input t \<in> inputs M\<close> ] \<open>t_source t = q'\<close> \<open>t_source t' = q'\<close> \<open>t_input t' = t_input t\<close>
      using \<open>t \<in> FSM.transitions S\<close> \<open>t' \<in> FSM.transitions M\<close> by blast
  qed



  have "\<forall>qa\<in>reachable_nodes S. qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (size_r (from_FSM M qa)-1) q). fst qx = qa)"
    using \<open>acyclic S\<close> proof (induction rule:
                              acyclic_induction[of S "\<lambda> q' . q' = q \<or> (\<exists> qx \<in> set (d_states (from_FSM M q') (size_r (from_FSM M q') - 1) q) . fst qx = q')" ])
    case (reachable_node qs)
    show ?case proof (cases "qs = q")
      case True
      then show ?thesis by auto
    next
      case False
      
      obtain ts where "ts \<in> transitions S" and "t_source ts = qs"
        using *[OF \<open>qs \<in> reachable_nodes S\<close>] False unfolding deadlock_state.simps by blast

      have ****: "\<And> t . t \<in> transitions S \<Longrightarrow> t_source t = qs \<Longrightarrow> t_input t = t_input ts"
        using \<open>single_input S\<close> by (metis \<open>t_source ts = qs\<close> \<open>ts \<in> FSM.transitions S\<close> single_input.elims(2)) 

      have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
                        t_source t = qs \<Longrightarrow>
                        t_input t = t_input ts \<Longrightarrow>
                        t_target t = q \<or>
                        (\<exists>qx\<in>set (d_states (FSM.from_FSM M (t_target t)) (size_r (FSM.from_FSM M (t_target t)) - 1) q).
                            fst qx = t_target t)"
        
        using  ***[OF \<open>qs \<in> reachable_nodes S\<close> \<open>ts \<in> transitions S\<close> \<open>t_source ts = qs\<close>]
        using reachable_node.IH(2)  ****
        by blast 



  
      then have "qs \<in> nodes S" using reachable_node_is_node by auto
      then have "qs \<in> nodes M" using \<open>is_submachine S M\<close> by auto




end (*


lemma d_states'_from :
  assumes "distinct nL"
  assumes "Suc k \<ge> Suc (length nL)"
  assumes "q \<in> set nL"
  and     "x \<in> set iL"
  and     "f (q,x) \<noteq> {}"
  and     "(\<forall> (y,q'') \<in> f (q,x) . (q'' \<in> nS))"
  and     "q \<noteq> q0"
  and "\<And> y q' . (y,q') \<in> f (q,x) \<Longrightarrow> \<exists> qx \<in> set (d_states' f q' q0 iL nL nS (Suc k) []) . fst qx = q0"
shows "\<exists> qx \<in> set (d_states' f q q0 iL nL nS (Suc k) []) . fst qx = q0"
proof (rule ccontr)
  assume c_assm: "\<not> (\<exists>qx\<in>set (d_states' f q q0 iL nL nS (Suc k) []). fst qx = q0)"

  have "(d_states' f q q0 iL nL nS (Suc (Suc k)) []) = (d_states' f q q0 iL nL nS (Suc k) [])"
    using assms(2) d_states'_max_length[OF assms(1), of f q q0 iL nS _ "[]"]
    by (metis Suc_n_not_le_n antisym_conv comm_monoid_add_class.add_0 d_states'_Suc_length d_states'_prefix list.size(3) nat_le_linear take_all) 

  have "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL = None"
  proof (rule ccontr)
    assume "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL \<noteq> None"
    then obtain a where *: "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL = Some a" by auto
    show "False" using c_assm unfolding d_states'_helper1[OF *] by auto
  qed

  have 
  

  show "False" proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show "False" unfolding find_remove_2_None_iff
        using assms(3,4,5,6) by blast 
    next
      case (Some a)
      then show ?thesis sorry
    qed
  next
    case (Some a)
    show ?thesis using c_assm unfolding d_states'_helper1[OF Some] by auto
  qed

end (*

lemma d_states_from :
  assumes "q' \<in> reachable_nodes M"
  and     "x \<in> inputs M"
  and     "h M (q',x) \<noteq> {}"
  and "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow> calculate_state_preamble_from_d_states (from_FSM M (t_target t)) q \<noteq> None"
shows "calculate_state_preamble_from_d_states (from_FSM M q') q \<noteq> None"
proof (cases "q = q'")
  case True
  then have "calculate_state_preamble_from_d_states (from_FSM M q') q = Some (initial_preamble (from_FSM M q'))"
    using from_FSM_simps(1)[OF reachable_node_is_node[OF assms(1)]] by simp
  then show ?thesis by simp
next
  case False
  show ?thesis 
  proof
    assume "calculate_state_preamble_from_d_states (FSM.from_FSM M q') q = None"
    
qed

  
  



end (*
lemma calculate_state_preamble_from_d_states_exhaustiveness :
  assumes "is_preamble S M q"
  shows "calculate_state_preamble_from_d_states M q \<noteq> None"
proof -
  have "acyclic S" 
  and  "q \<in> reachable_nodes S"
  and  "is_submachine S M"
    using assms unfolding is_preamble_def
    by blast+ 

  obtain p where "path S (initial S) p" and "target (initial S) p = q"
    using \<open>q \<in> reachable_nodes S\<close> unfolding reachable_nodes_def by blast
  then have "is_preamble S M (target (initial S) p)"
    using assms by auto




  have "\<forall>qa\<in>reachable_nodes S. qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (FSM.size (from_FSM M qa)-1) q). fst qx = qa)"
    using \<open>acyclic S\<close> proof (induction rule:
                              acyclic_induction[of S "\<lambda> q' . q' = q \<or> (\<exists> qx \<in> set (d_states (from_FSM M q') (size (from_FSM M q') - 1) q) . fst qx = q')" ])
    case (reachable_node qs)
    then have "qs \<in> nodes S" using reachable_node_is_node by auto
    then have "qs \<in> nodes M" using \<open>is_submachine S M\<close> by auto

    show ?case proof (cases "deadlock_state S qs")
      case True
      then have "qs = q"
        using reachable_node(1) assms unfolding is_preamble_def by auto
      then show ?thesis by simp
    next
      case False
      
      have "\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)-1) q). fst qx = qs"
      proof (rule ccontr)
        assume "\<not>(\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)-1) q). fst qx = qs)"

        let ?ds = "d_states' (h (from_FSM M qs)) q (initial (from_FSM M qs)) (inputs_as_list (from_FSM M qs)) (removeAll q (removeAll (initial (from_FSM M qs)) (nodes_as_list (from_FSM M qs)))) {q} (FSM.size (from_FSM M qs)-1) []"
        
         


        show "False" proof (cases "q = initial (from_FSM M qs)")
          case True
          then show ?thesis using \<open>qs \<in> nodes M\<close>
            using False assms is_preamble_def by fastforce 
        next
          case False
          then have "(d_states (from_FSM M qs) (FSM.size (from_FSM M qs)-1) q) = ?ds"
            by auto
          then have "\<not>(\<exists>qx\<in>set ?ds. fst qx = qs)"
            using \<open>\<not>(\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)-1) q). fst qx = qs)\<close> by auto

          have "find (\<lambda> x . (h (from_FSM M qs)) ((initial (from_FSM M qs)),x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h (from_FSM M qs)) ((initial (from_FSM M qs)),x) . (q'' \<in> {q}))) (inputs_as_list (from_FSM M qs)) 

          then show ?thesis sorry
        qed
      
      then show ?thesis sorry
    qed


  then have "calculate_state_preamble_from_d_states M (target (initial S) p) \<noteq> None" 
    using \<open>path S (initial S) p\<close>
  proof (induction p arbitrary: S M rule: list.induct)
    case Nil
    then have "(target (FSM.initial S) []) = initial M" unfolding is_preamble_def is_submachine.simps by simp
    then show ?case by simp       
  next
    case (Cons t p)
    then have "t \<in> transitions S" and "t_source t = initial M" unfolding is_preamble_def is_submachine.simps by auto
    

    show ?case proof (cases "(target (FSM.initial S) (t # p)) = initial M")
      case True
      then show ?thesis by auto
    next
      case False

      have "is_preamble (FSM.from_FSM S (t_target t)) (FSM.from_FSM M (t_target t)) (target (FSM.initial S) (t # p))"
        using is_preamble_next[OF \<open>is_preamble S M (target (FSM.initial S) (t # p))\<close> False \<open>t \<in> transitions S\<close> \<open>t_source t = initial M\<close>] by assumption
      then have "is_preamble (FSM.from_FSM S (t_target t)) (FSM.from_FSM M (t_target t)) (target (t_target t) p)"
        by auto
      then have *: "is_preamble (FSM.from_FSM S (t_target t)) (FSM.from_FSM M (t_target t)) (target (initial (FSM.from_FSM S (t_target t))) p)"
        using from_FSM_simps(1) by (simp add: \<open>t \<in> FSM.transitions S\<close> fsm_transition_target)

      have **: "path (FSM.from_FSM S (t_target t)) (FSM.initial (FSM.from_FSM S (t_target t))) p"
        by (meson Cons.prems(2) from_FSM_path_initial fsm_transition_target path_cons_elim)
        

      thm Cons.IH[OF * **]


      then show ?thesis sorry
    qed

    


    then show ?case sorry
  qed


end (*



  have "\<forall>qa\<in>reachable_nodes S. qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (FSM.size (from_FSM M qa)-1) q). fst qx = qa)"
    using \<open>acyclic S\<close> proof (induction rule:
                              acyclic_induction[of S "\<lambda> q' . q' = q \<or> (\<exists> qx \<in> set (d_states (from_FSM M q') (size (from_FSM M q') - 1) q) . fst qx = q')" ])
    case (reachable_node qs)


    
    
    thm is_preamble_next


proof (cases "q = initial M")
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis sorry
qed






end (* lemma d_states_find_props :
  assumes "d_states M (Suc k) q = d_states M k q @ [qqx]"
  shows "fst qqx \<noteq> q"
  and   "(\<forall>qx'\<in>set (d_states M k q). fst qqx \<noteq> fst qx')" 
  and   "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qqx \<and> t_input t = snd qqx)"
  and   "(\<forall>t\<in>set (wf_transitions M).
                          t_source t = fst qqx \<and> t_input t = snd qqx \<longrightarrow>
                          t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
  and   "fst qqx \<in> nodes M"
  and   "snd qqx \<in> inputs M"
proof -
  have *: "find
              (\<lambda>qx. fst qx \<noteq> q \<and>
                    (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                    (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                    (\<forall>t\<in>set (wf_transitions M).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))
              (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some qqx"
    using assms unfolding d_states.simps
  proof -
    assume "(if length (d_states M k q) < k then d_states M k q else case find (\<lambda>qx. fst qx \<noteq> q \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some qx \<Rightarrow> d_states M k q @ [qx]) = d_states M k q @ [qqx]"
    have f1: "d_states M (Suc k) q \<noteq> d_states M k q"
      using assms by auto
    have "\<not> length (d_states M k q) < k"
      using assms by force
    then have f2: "(case find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some p \<Rightarrow> d_states M k q @ [p]) = d_states M (Suc k) q"
      by (metis \<open>(if length (d_states M k q) < k then d_states M k q else case find (\<lambda>qx. fst qx \<noteq> q \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some qx \<Rightarrow> d_states M k q @ [qx]) = d_states M k q @ [qqx]\<close> assms)
    then have f3: "find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
      using f1 by (metis (no_types) option.case_eq_if)
    obtain pp :: "('a \<times> integer) option \<Rightarrow> 'a \<times> integer" where
      f4: "\<And>z. z = None \<or> Some (pp z) = z"
      by (metis not_None_eq)
    then have "\<And>z ps f. z = None \<or> (case z of None \<Rightarrow> ps::('a \<times> integer) list | Some x \<Rightarrow> f x) = f (pp z)"
      by (metis option.case_eq_if option.sel)
    then have "find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = None \<or> d_states M k q @ [pp (find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))] = d_states M (Suc k) q"
      using f2 by fastforce
    then have "d_states M k q @ [pp (find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))] = d_states M (Suc k) q"
      using f3 by meson
    then have "pp (find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M)))) = last (d_states M (Suc k) q)"
      by (metis (no_types, lifting) last_snoc)
    then have "find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = None \<or> find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<longrightarrow> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) = Some qqx"
      using f4 assms by fastforce
    then show ?thesis
      using f3 by meson
  qed 

  show  "fst qqx \<noteq> q"
  and   "(\<forall>qx'\<in>set (d_states M k q). fst qqx \<noteq> fst qx')" 
  and   "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qqx \<and> t_input t = snd qqx)"
  and   "(\<forall>t\<in>set (wf_transitions M).
                          t_source t = fst qqx \<and> t_input t = snd qqx \<longrightarrow>
                          t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
    using find_condition[OF *] by blast+

  have "qqx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
    using find_set[OF *] by assumption

  then show "fst qqx \<in> nodes M"
       and  "snd qqx \<in> inputs M"
    using concat_pair_set[of "inputs M" "nodes_from_distinct_paths M"] nodes_code[of M] by blast+
qed
  





end (* lemma d_states_step :
  assumes "qx \<in> set (d_states (from_FSM M q') k q)"
  and "q' \<in> nodes M"
shows "\<exists> qx' \<in> set (d_states M (size M) q) . fst qx = fst qx'" 
using assms(1) proof (induction k arbitrary: qx)
case 0
  then show ?case by auto

next
  case (Suc k)
  
  show ?case proof (cases "qx \<in> set (d_states (from_FSM M q') k q)")
    case True
    then show ?thesis using Suc.IH by blast
  next
    case False

    let ?l = "length (d_states M (size M) q)"
    have "d_states M (size M) q = d_states M ?l q"
      using d_states_self_length
      by fastforce 
    then have "d_states M ?l q = d_states M (Suc ?l) q"
      by (metis Suc_n_not_le_n nat_le_linear d_states_max_iterations d_states_prefix take_all)
      

    have "\<exists>qx'\<in>set (d_states M ?l q). fst qx = fst qx'"  proof (rule ccontr)
      assume c_assm: "\<not> (\<exists>qx'\<in>set (d_states M ?l q). fst qx = fst qx')"
      

      from False have *: "(d_states (from_FSM M q') (Suc k) q) \<noteq> (d_states (from_FSM M q') k q)"
        using Suc.prems by auto
      have qqx_last: "(d_states (from_FSM M q') (Suc k) q) = (d_states (from_FSM M q') k q) @ [qx]"
        using Suc.prems False d_states_last[OF *]
        by force
      
      have "fst qx \<noteq> q"
        and "\<forall>qx'\<in>set (d_states (from_FSM M q') k q). fst qx \<noteq> fst qx'"
        and "\<exists>t\<in>set (wf_transitions (from_FSM M q')). t_source t = fst qx \<and> t_input t = snd qx"
        and **: "\<forall>t\<in>set (wf_transitions (from_FSM M q')).
           t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
           t_target t = q \<or> (\<exists>qx'\<in>set (d_states (from_FSM M q') k q). fst qx' = t_target t)"
        and "fst qx \<in> nodes (from_FSM M q')"
        and "snd qx \<in> set (inputs (from_FSM M q'))"
        using d_states_find_props[OF qqx_last] by blast+
  

      have "(\<forall>qx'\<in>set (d_states M ?l q). fst qx \<noteq> fst qx')"
        using c_assm by blast
      moreover have "\<And> t . t \<in> transitions M \<Longrightarrow>
                t_source t = fst qx \<Longrightarrow> 
                t_input t = snd qx \<Longrightarrow>
                t_target t = q \<or> (\<exists>qx'\<in>set (d_states M ?l q). fst qx' = t_target t)"
      proof - 
        fix t assume "t \<in> transitions M"
                 and "t_source t = fst qx" 
                 and "t_input t = snd qx"
        then have "t \<in> transitions (from_FSM M q')"
          using from_FSM_nodes_transitions \<open>fst qx \<in> nodes (from_FSM M q')\<close> by metis
        then have "t_target t = q \<or> (\<exists>qx'\<in>set (d_states (from_FSM M q') k q). fst qx' = t_target t)"
          using ** \<open>t_source t = fst qx\<close> \<open>t_input t = snd qx\<close> by blast
        moreover have "(\<exists>qx'\<in>set (d_states (from_FSM M q') k q). fst qx' = t_target t) \<Longrightarrow> (\<exists>qx'\<in>set (d_states M ?l q). fst qx' = t_target t)"
        proof -
          assume "(\<exists>qx'\<in>set (d_states (from_FSM M q') k q). fst qx' = t_target t)"
          then obtain qx' where "qx'\<in>set (d_states (from_FSM M q') k q)" and "fst qx' = t_target t"
            by blast
          then obtain qx'' where "qx''\<in>set (d_states M (FSM.size M) q)" and "fst qx' = fst qx''"
            using Suc.IH by blast
          then have "qx''\<in>set (d_states M ?l q)"
            using \<open>d_states M (size M) q = d_states M ?l q\<close> by simp
          then show "(\<exists>qx'\<in>set (d_states M ?l q). fst qx' = t_target t)"
            using \<open>fst qx' = t_target t\<close>  \<open>fst qx' = fst qx''\<close> by auto
        qed
        ultimately show "t_target t = q \<or> (\<exists>qx'\<in>set (d_states M ?l q). fst qx' = t_target t)"
          by blast
      qed
        
      ultimately have "(\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M ?l q) . fst qx' = (t_target t))))) qx"
        using \<open>fst qx \<noteq> q\<close> \<open>\<exists>t\<in>set (wf_transitions (from_FSM M q')). t_source t = fst qx \<and> t_input t = snd qx\<close>
        by (meson assms(2) from_FSM_h subsetCE) 
      moreover have "qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
      proof -
        have "fst qx \<in> set (nodes_from_distinct_paths M)" 
          using from_FSM_nodes[OF assms(2)] \<open>fst qx \<in> nodes (from_FSM M q')\<close> nodes_code
          by (metis subsetCE) 
        moreover have "snd qx \<in> inputs M"
          using from_FSM_simps(2) \<open>snd qx \<in> set (inputs (from_FSM M q'))\<close> by metis
        ultimately show ?thesis using concat_pair_set[of "inputs M" "nodes_from_distinct_paths M"]
          by blast 
      qed

      ultimately have "find 
                  (\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M ?l q) . fst qx' = (t_target t))))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
        using find_from[of "(concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))" 
                           "(\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M ?l q) . fst qx' = (t_target t)))))"] 
        by blast

      then have "d_states M (Suc ?l) q \<noteq> d_states M ?l q"
        unfolding d_states.simps
        using \<open>d_states M (FSM.size M) q = d_states M (length (d_states M (FSM.size M) q)) q\<close> by auto
      then show "False"
        using \<open>d_states M ?l q = d_states M (Suc ?l) q\<close>
        by simp
    qed

    then show ?thesis
      using \<open>d_states M (size M) q = d_states M ?l q\<close> by auto
  qed
qed








thm acyclic_induction[of]

thm is_preamble_next

end (* lemma d_states_exhaustiveness :
  assumes "is_preamble S M q"
shows "q = initial M \<or> (\<exists> qx \<in> set (d_states M (size M) q) . fst qx = initial M)" 
proof -

  have "acyclic S"
  and  "single_input S" 
  and  "is_submachine S M" 
  and  "q \<in> nodes S"
  and  "deadlock_state S q" 
  and  *: "(\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)))"
    using assms(1) unfolding is_preamble_def by linarith+

  have "\<forall>qa\<in>nodes S. qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (FSM.size (from_FSM M qa)) q). fst qx = qa)"
    using \<open>acyclic S\<close> proof (induction rule:
                              acyclic_induction[of S "\<lambda> q' . q' = q \<or> (\<exists> qx \<in> set (d_states (from_FSM M q') (size (from_FSM M q')) q) . fst qx = q')" ])
    case (node qs)

    show ?case proof (cases "qs = q")
      case True
      then show ?thesis by simp
    next
      case False


      

      have "\<not> deadlock_state S qs"
        using "*" False node.IH(1) by fastforce
      then obtain x where "x \<in> set (inputs S)" and "\<exists> t \<in> transitions S . t_source t = qs \<and> t_input t = x"
        by auto



      have "\<And> t . t \<in> transitions S \<Longrightarrow> t_source t = qs \<Longrightarrow>
         t_target t = q \<or>
        (\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q). fst qx = t_target t)"
      proof -
        fix t assume "t \<in> transitions S" and "t_source t = qs"
        then consider 
          (a) "t_target t = q" |
          (b) "(\<exists>qx\<in>set (d_states (from_FSM M (t_target t)) (FSM.size (from_FSM M (t_target t))) q). fst qx = t_target t)"
          using node(2) by blast
        then show "t_target t = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q). fst qx = t_target t)"
        proof cases
          case a
          then show ?thesis by auto
        next
          case b
          then obtain qx where "qx \<in> set (d_states (from_FSM M (t_target t)) (FSM.size (from_FSM M (t_target t))) q)"
                           and "fst qx = t_target t"
            by blast
  
          have "qx \<in> set (d_states (from_FSM (from_FSM M qs) (t_target t)) (FSM.size (from_FSM (from_FSM M qs) (t_target t))) q)"
            using \<open>qx \<in> set (d_states (from_FSM M (t_target t)) (FSM.size (from_FSM M (t_target t))) q)\<close>
            using from_from by metis
  
          have "t_target t \<in> nodes (from_FSM M qs)"
            by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>t \<in> set (wf_transitions S)\<close> \<open>t_source t = qs\<close> from_FSM_transition_initial submachine_h subsetCE wf_transition_target)
  
          have "(\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q). fst qx = t_target t)"
            using d_states_step[OF \<open>qx \<in> set (d_states (from_FSM (from_FSM M qs) (t_target t)) (FSM.size (from_FSM (from_FSM M qs) (t_target t))) q)\<close> \<open>t_target t \<in> nodes (from_FSM M qs)\<close>] 
            using \<open>fst qx = t_target t\<close> by metis
            
          then show ?thesis by blast
        qed
      qed

      moreover have "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = qs \<Longrightarrow> t_input t = x \<Longrightarrow> t \<in> transitions S"
        using * \<open>x \<in> set (inputs S)\<close> \<open>\<exists> t \<in> transitions S . t_source t = qs \<and> t_input t = x\<close>
        by (metis wf_transition_simp) 

      moreover have "\<And> t . t \<in> transitions S \<Longrightarrow> t_source t = qs \<Longrightarrow> t_input t = x \<Longrightarrow> t \<in> transitions (from_FSM M qs)"
        using from_FSM_nodes_transitions[of _ S qs] submachine_from[OF \<open>is_submachine S M\<close> node(1)]
        by (meson from_FSM_transition_initial submachine_h subsetCE) 

      ultimately have t_prop : "\<And> t . t \<in> transitions (from_FSM M qs) \<Longrightarrow> t_source t = qs \<Longrightarrow> t_input t = x \<Longrightarrow>
         t_target t = q \<or>
        (\<exists>qx\<in>set (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q). fst qx = t_target t)"
        by (metis (no_types, lifting) \<open>is_submachine S M\<close> from_FSM_h node.IH(1) submachine_nodes subsetCE) 


      let ?M = "(from_FSM M qs)"
      let ?l = "length (d_states ?M (size ?M) q)"
      have "d_states ?M (size ?M) q = d_states ?M ?l q"
        using d_states_self_length by fastforce
      then have "d_states ?M ?l q = d_states ?M (Suc ?l) q"
        by (metis Suc_n_not_le_n nat_le_linear d_states_max_iterations d_states_prefix take_all)
  
      have "\<exists>qqx'\<in>set (d_states ?M ?l q). qs = fst qqx'"  proof (rule ccontr)
        assume c_assm: "\<not> (\<exists>qqx'\<in>set (d_states ?M ?l q). qs = fst qqx')"


        have "fst (qs, x) \<noteq> q" 
          using False by auto

        moreover have "(\<forall>qx'\<in>set (d_states (from_FSM M qs) ?l q). fst (qs, x) \<noteq> fst qx')" 
          using c_assm by auto

        moreover have "(\<exists>t\<in>set (wf_transitions (from_FSM M qs)). t_source t = fst (qs, x) \<and> t_input t = snd (qs, x))"
          by (metis (no_types, lifting) \<open>\<exists>t\<in>set (wf_transitions S). t_source t = qs \<and> t_input t = x\<close> \<open>is_submachine S M\<close> from_FSM_transition_initial fst_conv snd_conv submachine_h subsetCE) 
          
          
        moreover have "(\<forall>t\<in>set (wf_transitions (from_FSM M qs)).
            t_source t = fst (qs, x) \<and> t_input t = snd (qs, x) \<longrightarrow>
            t_target t = q \<or>
            (\<exists>qx'\<in>set (d_states (from_FSM M qs) ?l q). fst qx' = t_target t))" 
          using t_prop
          using \<open>d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q = d_states (from_FSM M qs) (length (d_states (from_FSM M qs) (FSM.size (from_FSM M qs)) q)) q\<close> by fastforce 

        ultimately have "(\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states ?M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions ?M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions ?M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states ?M ?l q) . fst qx' = (t_target t))))) (qs,x)"
          by blast
          

        moreover have "(qs,x) \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs ?M)) (nodes_from_distinct_paths ?M)))"
        proof -
          have "qs \<in> nodes ?M"
            by (metis nodes.initial from_FSM_simps(1)) 
          then have "fst (qs,x) \<in> set (nodes_from_distinct_paths ?M)" 
            by (simp add: nodes_code) 
          moreover have "snd (qs,x) \<in> set (inputs ?M)"
            using \<open>x \<in> set (inputs S)\<close> \<open>is_submachine S M\<close> by auto
          ultimately show ?thesis using concat_pair_set[of "inputs ?M" "nodes_from_distinct_paths ?M"]
            by blast 
        qed
        ultimately have "find 
                    (\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states ?M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions ?M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions ?M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states ?M ?l q) . fst qx' = (t_target t))))) 
                    (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs ?M)) (nodes_from_distinct_paths ?M))) \<noteq> None"
          using find_from[of "(concat (map (\<lambda>q. map (Pair q) (inputs ?M)) (nodes_from_distinct_paths ?M)))" "(\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states ?M ?l q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions ?M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions ?M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states ?M ?l q) . fst qx' = (t_target t)))))"] by blast
    
        then have "d_states ?M (Suc ?l) q \<noteq> d_states ?M ?l q"
          unfolding d_states.simps
          using \<open>d_states ?M (size ?M) q = d_states ?M ?l q\<close> by auto
        then show "False"
          using \<open>d_states ?M ?l q = d_states ?M (Suc ?l) q\<close>
          by simp
      qed

    then show ?thesis
      using \<open>d_states ?M (size ?M) q = d_states ?M ?l q\<close>
      by force 
    qed
  qed

  then have *: "\<And> qa . qa \<in> nodes S \<Longrightarrow> qa = q \<or> (\<exists>qx\<in>set (d_states (from_FSM M qa) (FSM.size (from_FSM M qa)) q). fst qx = qa)"
    by blast
    
  have "initial M \<in> nodes S" 
    using \<open>is_submachine S M\<close> nodes.initial[of S] by auto

  have "from_FSM M (initial M) = M" by auto
  then show ?thesis
    using *[OF \<open>initial M \<in> nodes S\<close>] by presburger
qed 
   

end (* lemma calculate_state_preamble_from_d_states_exhaustiveness :
  assumes "\<exists> S . is_preamble S M q"
  shows "calculate_state_preamble_from_d_states M q \<noteq> None"
proof (cases "q = initial M")
  case True
  then show ?thesis unfolding calculate_state_preamble_from_d_states_def by auto
next
  case False

  obtain S where "is_preamble S M q" using assms by blast

  have "(\<exists>qx\<in>set (d_states M (FSM.size M) q). fst qx = initial M)"
    using d_states_exhaustiveness[OF \<open>is_preamble S M q\<close>] False by blast

  then have "find_index (\<lambda>qqt. fst qqt = initial M) (d_states_opt M (FSM.size M) q) \<noteq> None"
    using find_index_exhaustive
    by (simp add: find_index_exhaustive d_states_code) 
  

  then show ?thesis 
    unfolding calculate_state_preamble_from_d_states_def Let_def using False by force
qed




definition calculate_preamble_set_from_d_states :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list set option" where
  "calculate_preamble_set_from_d_states M q = (case calculate_state_preamble_from_d_states M q of
    Some S \<Rightarrow> Some (LS_acyclic S (initial S)) |
    None \<Rightarrow> None)"

end (* lemma calculate_preamble_set_from_d_states_soundness :
  assumes "calculate_preamble_set_from_d_states M q = Some P"
  and     "observable M"
shows "is_preamble_set M q P"
proof -
  obtain S where *:  "calculate_state_preamble_from_d_states M q = Some S" 
             and **: "P = LS_acyclic S (initial S)"
    using assms(1) unfolding calculate_preamble_set_from_d_states_def
    by (metis (no_types, lifting) option.case_eq_if option.collapse option.distinct(1) option.inject) 

  have "is_preamble S M q"
    using calculate_state_preamble_from_d_states_soundness[OF *] by assumption

  have "acyclic S"
    by (metis (no_types) \<open>is_preamble S M q\<close> is_preamble_def)

  then have "LS_acyclic S (initial S) = L S"
    using LS_acyclic_complete[of S "initial S"] nodes.initial[of S] by auto
  
  then show ?thesis using preamble_has_preamble_set[OF assms(2) \<open>is_preamble S M q\<close>] \<open>P = LS_acyclic S (initial S)\<close>
    by presburger 
qed




end (* lemma calculate_preamble_set_from_d_states_exhaustiveness :
  assumes "\<exists> P . is_preamble_set M q P"
  and     "observable M"
shows "calculate_preamble_set_from_d_states M q \<noteq> None"
  using preamble_set_implies_preamble(1)[OF assms(2), of q] calculate_state_preamble_from_d_states_exhaustiveness[of M q]
proof -
  have "calculate_state_preamble_from_d_states M q \<noteq> None"
    using \<open>\<And>P. is_preamble_set M q P \<Longrightarrow> is_preamble (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M q\<close> \<open>\<exists>S. is_preamble S M q \<Longrightarrow> calculate_state_preamble_from_d_states M q \<noteq> None\<close> assms(1) by blast
  then show ?thesis
    by (simp add: calculate_preamble_set_from_d_states_def option.case_eq_if)
qed 


(* TODO: implement faster acyclic language calculation, e.g. using paths_up_to_length_or_condition *)


fun distinct_paths_up_to_length :: "'a Transition list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "distinct_paths_up_to_length H q 0 = [[]]" |
  "distinct_paths_up_to_length H q (Suc n) = 
      [] # concat
        (map 
          (\<lambda> t . (map (\<lambda> p . t # p) (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) n)))
          (filter (\<lambda> t . t_source t = q \<and> t_target t \<noteq> q) H))"

value "distinct_paths_up_to_length (wf_transitions M_ex_H) 1 3"

(* TODO: move *)
end (* lemma path_sources : 
  assumes "path M q (t#p)"
  shows "map t_target (butlast (t#p)) = map t_source p"
  using assms proof (induction p arbitrary: q t)
  case Nil
  then show ?case by auto
next
  case (Cons t' p)
  then have "path M (t_target t) (t'#p)" using Cons.prems by auto
  then have "map t_target (butlast (t' # p)) = map t_source p" using Cons.IH by auto
  then show ?case using Cons.prems by auto
qed

end (* lemma path_sources' : 
  assumes "path M q (t#p@[t'])"
  shows "map t_target (t#p@[t']) = (map t_source (p@[t'])) @ [t_target t']"
  using path_sources[OF assms] by auto

end (* lemma distinct_path_sources :
  assumes "path M q (t#p)"
  and     "distinct (visited_states q (t#p))"
shows "distinct (map t_source p)" and "t_source t \<notin> set (map t_source p)"
proof -
  have "distinct (map t_target (t#p))"
    using assms(2) by auto
  then show "distinct (map t_source p)"
    using path_sources[OF assms(1)] 
    by (metis distinct_butlast map_butlast)

  show "t_source t \<notin> set (map t_source p)"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis by auto
  next
    case (snoc p' t')
    then have "path M q (t#p'@[t'])"
          and "distinct (q # map t_target (t # p'@[t']))" 
      using assms by simp+
    
    have "t_source t \<notin> set (map t_source (p'@[t']))"
      using path_sources'[OF \<open>path M q (t#p'@[t'])\<close>]
            \<open>distinct (q # map t_target (t # p'@[t']))\<close>
    proof -
      have "t_source t = q"
        using \<open>path M q (t # p' @ [t'])\<close> by force
      then show ?thesis
        by (metis (no_types) \<open>distinct (q # map t_target (t # p' @ [t']))\<close> \<open>map t_target (t # p' @ [t']) = map t_source (p' @ [t']) @ [t_target t']\<close> butlast_snoc distinct.simps(2) in_set_butlastD)
    qed
      
      
    show ?thesis
      using path_sources'[OF \<open>path M q (t#p'@[t'])\<close>]
      using assms(2) snoc unfolding visited_states.simps
      using \<open>t_source t \<notin> set (map t_source (p' @ [t']))\<close> by blast 
  qed
qed




end (* lemma distinct_paths_up_to_length_set :
  assumes "set H \<subseteq> h M"
  and     "q \<in> nodes M"
shows "set (distinct_paths_up_to_length H q k) = {p . path M q p \<and> distinct (visited_states q p) \<and> set p \<subseteq> set H \<and> length p \<le> k}"
using assms proof (induction k arbitrary: q H)
  case 0
  then show ?case unfolding distinct_paths_up_to_length.simps by auto
next
  case (Suc k)

  have "\<And> p . p \<in> set (distinct_paths_up_to_length H q (Suc k)) \<Longrightarrow> path M q p \<and> distinct (visited_states q p) \<and> set p \<subseteq> set H \<and> length p \<le> Suc k"
  proof - 
    fix p assume "p \<in> set (distinct_paths_up_to_length H q (Suc k))"
    then obtain t where *:  "p = [] \<or> t \<in> set (filter (\<lambda>t . t_source t = q \<and> t_target t \<noteq> q) H)"
                    and **: "p = [] \<or> p \<in> (set ( 
                                       map ((#) t)
                                        (distinct_paths_up_to_length (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)
                                          (t_target t) k)))"
      unfolding distinct_paths_up_to_length.simps 
      by auto

    show "path M q p \<and> distinct (visited_states q p) \<and> set p \<subseteq> set H \<and> length p \<le> Suc k"
    proof (cases "p = []")
      case True
      then show ?thesis using Suc by force 
    next
      case False
      
    

      have "t \<in> set H" and "t_source t = q" and "t_target t \<noteq> q"
        using * False by auto
      then have "t \<in> transitions M"
        using Suc.prems(1) by auto
      then have "t_target t \<in> nodes M"
        by auto
  
      from ** consider
        (a) "p = [t]" |
        (b) "\<exists> p' \<in> set (distinct_paths_up_to_length (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) k) . p = t#p'" 
        using False by auto
      then show "path M q p \<and> distinct (visited_states q p) \<and> set p \<subseteq> set H \<and> length p \<le> Suc k"
      proof cases
        case a
        then show ?thesis using  \<open>t \<in> set H\<close> \<open>t \<in> transitions M\<close> \<open>t_source t = q\<close> \<open>t_target t \<noteq> q\<close> by force
      next
        case b
        then obtain p' where "p' \<in> set (distinct_paths_up_to_length (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) k)" and "p = t#p'"
          by blast
        moreover have "set (filter (\<lambda>p. t_source p \<noteq> q \<and> t_target p \<noteq> q) H) \<subseteq> set (wf_transitions M)"
          by (meson Suc.prems(1) filter_is_subset subset_trans)
        ultimately have "path M (t_target t) p'" 
                    and "distinct (visited_states (t_target t) p')"
                    and "set p' \<subseteq> set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)" 
                    and "length p' \<le> k"
          using Suc.IH[OF _ \<open>t_target t \<in> nodes M\<close>]
          by blast+
  
        have "q \<notin> set (map t_target p')"
          using \<open>set p' \<subseteq> set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)\<close> by auto
        then have "distinct (visited_states q p)"
          unfolding visited_states.simps using \<open>t_target t \<noteq> q\<close>
          using \<open>distinct (visited_states (t_target t) p')\<close> \<open>p = t # p'\<close> by auto 
        then show ?thesis
          using \<open>length p' \<le> k\<close> \<open>p = t # p'\<close> \<open>path M (t_target t) p'\<close> \<open>set p' \<subseteq> set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)\<close> \<open>t \<in> set (wf_transitions M)\<close> \<open>t \<in> set H\<close> \<open>t_source t = q\<close> by auto         
      qed
    qed
  qed

  

  moreover have "\<And> p . set H \<subseteq> h M \<Longrightarrow> path M q p \<Longrightarrow> distinct (visited_states q p) \<Longrightarrow> set p \<subseteq> set H \<Longrightarrow> length p \<le> Suc k \<Longrightarrow> p \<in> set (distinct_paths_up_to_length H q (Suc k))"
  proof - 
    fix p assume "set H \<subseteq> h M" and "path M q p" and "distinct (visited_states q p)" and "set p \<subseteq> set H" and "length p \<le> Suc k"
    then show "p \<in> set (distinct_paths_up_to_length H q (Suc k))"

    proof (induction k arbitrary: p q H)
      case 0
      then consider (a) "p = []" | (b) "\<exists> t . p = [t]"
        by (metis le_SucE le_zero_eq length_0_conv length_Suc_conv) 
      then show ?case proof cases
        case a
        then show ?thesis by auto
      next
        case b
        then show ?thesis unfolding distinct_paths_up_to_length.simps using 0 by auto
      qed 
    next
      case (Suc k)
      
      show ?case using Suc.prems proof (induction p  rule: list.induct)
        case Nil
        then show ?case unfolding distinct_paths_up_to_length.simps by auto
      next
        case (Cons t p)
        have "t_source t = q"
          using Cons.prems(2) by auto
        moreover have "t_target t \<noteq> q"
          using calculation Cons.prems(3) unfolding visited_states.simps by auto
        moreover have "t \<in> set H"
          using Cons.prems(4) by auto
        ultimately have *: "t \<in> set (filter (\<lambda> t . t_source t = q \<and> t_target t \<noteq> q) H)"
          by auto
  
        have "set (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) \<subseteq> h M"
          using \<open>set H \<subseteq> set (wf_transitions M)\<close> by auto
        have "t_target t \<in> nodes M"
          using Cons.prems(2) by auto
  
        have "path M (t_target t) p"
          using Cons by auto
        have "distinct (visited_states (t_target t) p)"
          using Cons by auto
        
        have "p \<in> set (distinct_paths_up_to_length H (t_target t) (Suc k))"
          using Suc.IH[OF Cons.prems(1) \<open>path M (t_target t) p\<close> \<open>distinct (visited_states (t_target t) p)\<close> ] Cons.prems(4,5) by auto

        have "set p \<subseteq> set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)"
        proof -
          have "set p \<subseteq> set H"
            using Cons.prems(4) by auto
          moreover have "\<And> t . t \<in> set p \<Longrightarrow> t_target t \<noteq> q"
            using Cons.prems(3) unfolding visited_states.simps 
            by (metis (no_types, lifting) distinct.simps(2) image_eqI list.set_intros(2) set_map)
          moreover have "\<And> t . t \<in> set p \<Longrightarrow> t_source t \<noteq> q"
            using distinct_path_sources[OF Cons.prems(2)]
            by (metis Cons.prems(3) \<open>t_source t = q\<close> image_eqI set_map)
          ultimately show ?thesis
            by (simp add: subset_iff) 
        qed
        
        have **: "p \<in> set ((distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k)))"
          using Suc.IH[OF _ \<open>path M (t_target t) p\<close> \<open>distinct (visited_states (t_target t) p)\<close>, of "(filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H)" ] Cons.prems(3,4,5)
          using \<open>set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H) \<subseteq> set (wf_transitions M)\<close> \<open>set p \<subseteq> set (filter (\<lambda>t. t_source t \<noteq> q \<and> t_target t \<noteq> q) H)\<close> by auto 

        then have ***: "p \<in> set ((\<lambda>t. (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k))) t)"
          by auto

        have concat_scheme1: "\<And> t p Y . p \<in> set (Y t) \<Longrightarrow> t # p \<in> set ((map (\<lambda>p . t # p) (Y t)))"
          by auto
        have concat_scheme2: "\<And> t p X Y . t # p \<in> set ((map (\<lambda>p . t # p) (Y t))) \<Longrightarrow> t \<in> set X \<Longrightarrow> t # p \<in> set (concat (map (\<lambda>t . map (\<lambda>p . t # p) (Y t)) X))"
          by auto
        
        have "t#p \<in> set ( concat
                                    (map 
                                      (\<lambda> t . (map (\<lambda> p . t # p) (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k))))
                                      (filter (\<lambda> t . t_source t = q \<and> t_target t \<noteq> q) H)))"
          using concat_scheme2[of t p "(\<lambda>t. (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k)))" "filter (\<lambda> t . t_source t = q \<and> t_target t \<noteq> q) H", OF concat_scheme1[of p "(\<lambda>t. (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k)))" t, OF ***] *  ]
          by linarith
          
        moreover have "distinct_paths_up_to_length H q (Suc (Suc k)) = [] # concat
                                                                      (map 
                                                                        (\<lambda> t . (map (\<lambda> p . t # p) (distinct_paths_up_to_length (filter (\<lambda> t . t_source t \<noteq> q \<and> t_target t \<noteq> q) H) (t_target t) (Suc k))))
                                                                        (filter (\<lambda> t . t_source t = q \<and> t_target t \<noteq> q) H))"
          by auto
        
        ultimately show ?case
          by (metis (no_types, lifting) list.set_intros(2)) 
      qed
    qed
  qed

  ultimately show ?case
    using Suc.prems(1) by blast 
qed



end (* lemma distinct_paths_up_to_length_set_initial :
  "set (distinct_paths_up_to_length (wf_transitions M) (initial M) k) = {p . path M (initial M) p \<and> distinct (visited_states (initial M) p) \<and> length p \<le> k}"
proof -
  have *: "set (wf_transitions M) \<subseteq> set (wf_transitions M)" 
    by auto
  show ?thesis 
    using distinct_paths_up_to_length_set[OF * nodes.initial] path_h[of M "initial M"] 
    by auto
qed




fun distinct_paths :: "('a,'b,'c) fsm \<Rightarrow> 'a Transition list list" where
  "distinct_paths M = distinct_paths_up_to_length (wf_transitions M) (initial M) (size M)"

end (* lemma distinct_paths_set :
  "set (distinct_paths M) = {p . path M (initial M) p \<and> distinct (visited_states (initial M) p)}"
  unfolding distinct_paths.simps
  using distinct_paths_up_to_length_set_initial[of M "size M"] distinct_path_length_limit_nodes[of M "initial M"] 
  by (metis (no_types, lifting) Collect_cong less_imp_le_nat)

value "distinct_paths_up_to_length (wf_transitions M_ex_DR) 0 (size M_ex_DR)"


fun LS_acyclic_opt :: "('a,'b,'c) fsm \<Rightarrow> ('a \<times> 'b) list list" where 
  "LS_acyclic_opt M = map p_io (distinct_paths M)"

end (* lemma LS_acyclic_alt_def:
  assumes "acyclic M" 
  shows "set (LS_acyclic_opt M) = LS_acyclic M (initial M)" 
proof -
  have "set (distinct_paths M) = {p . path M (initial M) p}"
    using distinct_paths_set[of M]
    using acyclic_paths_from_nodes[OF assms, of "initial M"] 
    by auto
  then have "set (LS_acyclic_opt M) = {p_io p | p . path M (initial M) p}"
    unfolding LS_acyclic_opt.simps by auto
  then show ?thesis
    using LS_acyclic_complete[OF assms, of "initial M", OF nodes.initial[of M]] by auto
qed


definition calculate_preamble_set_from_d_states_opt :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list set option" where
  "calculate_preamble_set_from_d_states_opt M q = (case calculate_state_preamble_from_d_states M q of
    Some S \<Rightarrow> Some (set (LS_acyclic_opt S)) |
    None \<Rightarrow> None)"


end (* lemma calculate_preamble_set_from_d_states_code[code] :
  "calculate_preamble_set_from_d_states M q = calculate_preamble_set_from_d_states_opt M q"
proof (cases "calculate_state_preamble_from_d_states M q")
  case None
  then show ?thesis 
    unfolding calculate_preamble_set_from_d_states_def calculate_preamble_set_from_d_states_opt_def by auto
next
  case (Some S)
  

  have "acyclic S" 
    using calculate_state_preamble_from_d_states_soundness[OF Some]
    unfolding is_preamble_def 
    by linarith 

  have "calculate_preamble_set_from_d_states M q = Some (LS_acyclic S (initial S))"
  and  "calculate_preamble_set_from_d_states_opt M q = Some (set (LS_acyclic_opt S))"
    using Some unfolding calculate_preamble_set_from_d_states_def calculate_preamble_set_from_d_states_opt_def 
    by auto
  then show ?thesis 
    using LS_acyclic_alt_def[OF \<open>acyclic S\<close>] by force
qed

value "calculate_preamble_set_from_d_states M_ex_9 3"
value "calculate_preamble_set_from_d_states M_ex_DR 400"

value "image (\<lambda> s . calculate_preamble_set_from_d_states M_ex_9 s) (nodes M_ex_9)"

end