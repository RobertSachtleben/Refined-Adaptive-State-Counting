theory State_Preamble
imports Product_FSM 
begin

section \<open>State Preambles\<close>

subsection \<open>Definitions\<close>

(* TODO: use actual definition
fun definitely_reachable :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<forall> S . completely_specified S \<and> is_submachine S M \<longrightarrow> q \<in> nodes S)"
*)

(* TODO: removed all preamble-set results *)

definition is_preamble :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_preamble S M q = 
    ( acyclic S 
    \<and> single_input S 
    \<and> is_submachine S M 
    \<and> q \<in> reachable_nodes S 
    \<and> deadlock_state S q 
    \<and> (\<forall> q' \<in> reachable_nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S))))"

fun definitely_reachable :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<exists> S . is_preamble S M q)"




subsection \<open>Properties\<close>

lift_definition initial_preamble :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.initial_singleton by auto

lemma initial_preamble_simps[simp] :
  "initial (initial_preamble M) = initial M"
  "nodes (initial_preamble M) = {initial M}"
  "inputs (initial_preamble M) = inputs M"
  "outputs (initial_preamble M) = outputs M"
  "transitions (initial_preamble M) = {}"
  by (transfer; auto)+


lemma is_preamble_initial : 
  "is_preamble (initial_preamble M) M (initial M)"
proof -
  have "acyclic (initial_preamble M)"
    by (metis acyclic_code empty_iff initial_preamble_simps(5))
  moreover have "single_input (initial_preamble M)"
    by auto
  moreover have "is_submachine (initial_preamble M) M"
    by (simp add: fsm_initial)
  moreover have "(initial M) \<in> reachable_nodes (initial_preamble M)"
    unfolding reachable_nodes_def using reachable_nodes_intro by auto 
  moreover have "deadlock_state (initial_preamble M) (initial M)"
    by simp
  ultimately show ?thesis  
    unfolding is_preamble_def
    using reachable_node_is_node by force
qed
  
 
 

lemma is_preamble_next :
  assumes "is_preamble S M q"
  and "q \<noteq> initial M"
  and "t \<in> transitions S"  
  and "t_source t = initial M"
shows "is_preamble (from_FSM S (t_target t)) (from_FSM M (t_target t)) q"
(is "is_preamble ?S ?M q")
proof -


  have "acyclic S"
  and  "single_input S" 
  and  "is_submachine S M" 
  and  "q \<in> reachable_nodes S"
  and  "deadlock_state S q" 
  and  *: "(\<forall> q' \<in> reachable_nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)))"
    using assms(1) unfolding is_preamble_def by linarith+

  have "t_target t \<in> nodes S"
    using assms(3) fsm_transition_target by metis
  have "t_target t \<in> nodes M"
    using \<open>is_submachine S M\<close> \<open>t_target t \<in> FSM.nodes S\<close> by auto 

  have is_acyclic: "acyclic ?S" 
    using from_FSM_path_initial[OF \<open>t_target t \<in> nodes S\<close>]
    unfolding acyclic.simps from_FSM_simps[OF \<open>t_target t \<in> nodes S\<close>]
    using acyclic_paths_from_reachable_nodes[OF \<open>acyclic S\<close>, of "[t]" "t_target t"]
    by (metis \<open>is_submachine S M\<close> assms(3) assms(4) is_submachine.elims(2) prod.collapse single_transition_path target_single_transition)

  have is_single_input: "single_input ?S"
    using \<open>single_input S\<close> 
    unfolding single_input.simps from_FSM_simps[OF \<open>t_target t \<in> nodes S\<close>] by blast

  have "initial ?S = initial ?M"
    by (simp add: \<open>t_target t \<in> FSM.nodes M\<close> \<open>t_target t \<in> FSM.nodes S\<close>) 
  moreover have "inputs ?S = inputs ?M"
    using \<open>is_submachine S M\<close> by (simp add: \<open>t_target t \<in> FSM.nodes M\<close> \<open>t_target t \<in> FSM.nodes S\<close>)
  moreover have "outputs ?S = outputs ?M"
    using \<open>is_submachine S M\<close> by (simp add: \<open>t_target t \<in> FSM.nodes M\<close> \<open>t_target t \<in> FSM.nodes S\<close>) 
  moreover have "transitions ?S \<subseteq> transitions ?M"
    using \<open>is_submachine S M\<close>
    by (simp add: \<open>t_target t \<in> FSM.nodes M\<close> \<open>t_target t \<in> FSM.nodes S\<close>)
  ultimately have is_sub : "is_submachine ?S ?M"
    using \<open>is_submachine S M\<close> \<open>t_target t \<in> FSM.nodes M\<close> \<open>t_target t \<in> FSM.nodes S\<close> by auto


  have contains_q : "q \<in> reachable_nodes ?S"
  proof -
    obtain qd where "qd \<in> reachable_nodes ?S" and "deadlock_state ?S qd"
      using is_acyclic
      using acyclic_deadlock_reachable by blast 
    
    have "qd \<in> reachable_nodes S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>qd \<in> reachable_nodes (FSM.from_FSM S (t_target t))\<close> assms(3) assms(4) from_FSM_reachable_nodes in_mono is_submachine.elims(2) prod.collapse reachable_nodes_intro single_transition_path target_single_transition)
    then have "deadlock_state S qd"
      using \<open>deadlock_state ?S qd\<close> unfolding deadlock_state.simps
      by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    then have "qd = q"
      using * \<open>qd \<in> reachable_nodes S\<close>
      by fastforce
    then show ?thesis 
      using \<open>qd \<in> reachable_nodes ?S\<close> by auto
  qed
  
  have has_deadlock_q : "deadlock_state ?S q"
    using *
    by (metis \<open>deadlock_state S q\<close> \<open>t_target t \<in> FSM.nodes S\<close> deadlock_state.simps from_FSM_simps(4))


  have has_nodes_prop_1: "\<And> q' . q' \<in> reachable_nodes ?S \<Longrightarrow> deadlock_state ?S q' \<Longrightarrow> q = q'"
  proof -
    fix q' assume "q' \<in> reachable_nodes ?S" and "deadlock_state ?S q'"
    have "q' \<in> reachable_nodes S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>q' \<in> reachable_nodes (FSM.from_FSM S (t_target t))\<close> assms(3) assms(4) from_FSM_reachable_nodes in_mono is_submachine.elims(2) prod.collapse reachable_nodes_intro single_transition_path target_single_transition)      
    then have "deadlock_state S q'"
      using \<open>deadlock_state ?S q'\<close> unfolding deadlock_state.simps
      using \<open>q' \<in> reachable_nodes ?S\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    then show "q = q'"
      using * \<open>q' \<in> reachable_nodes S\<close> by fastforce 
  qed

  moreover have has_nodes_prop_2: "\<And> x t t' q' .
    q' \<in> reachable_nodes ?S \<Longrightarrow>
    t \<in> transitions ?S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
    t' \<in> transitions ?M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions ?S"
  proof -
    fix x tS tM q' assume "q' \<in> reachable_nodes ?S" and "tS \<in> transitions ?S" and "t_source tS = q'" and "t_input tS = x" and "tM \<in> transitions ?M" and "t_source tM = q'" and "t_input tM = x"


    have "q' \<in> reachable_nodes S"
      by (metis (no_types, lifting) \<open>is_submachine S M\<close> \<open>q' \<in> reachable_nodes (FSM.from_FSM S (t_target t))\<close> assms(3) assms(4) from_FSM_reachable_nodes in_mono is_submachine.elims(2) prod.collapse reachable_nodes_intro single_transition_path target_single_transition)
    

    have "tS \<in> transitions S"
      using \<open>tS \<in> transitions ?S\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    have "tM \<in> transitions M"
      using \<open>tM \<in> transitions ?M\<close>
      using \<open>t_target t \<in> FSM.nodes M\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    have "t_source tS \<in> nodes (from_FSM S (t_target t))"
      using \<open>tS \<in> transitions ?S\<close> by auto
    have "t_source tM \<in> nodes (from_FSM M (t_target t))"
      using \<open>tM \<in> transitions ?M\<close> by auto

    have "q' \<in> reachable_nodes ?M" 
      using \<open>q' \<in> reachable_nodes ?S\<close> submachine_path[OF \<open>is_submachine ?S ?M\<close>]
      unfolding reachable_nodes_def
    proof -
      assume "q' \<in> {target (FSM.initial (FSM.from_FSM S (t_target t))) p |p. path (FSM.from_FSM S (t_target t)) (FSM.initial (FSM.from_FSM S (t_target t))) p}"
      then show "q' \<in> {target (FSM.initial (FSM.from_FSM M (t_target t))) ps |ps. path (FSM.from_FSM M (t_target t)) (FSM.initial (FSM.from_FSM M (t_target t))) ps}"
        using \<open>FSM.initial (FSM.from_FSM S (t_target t)) = FSM.initial (FSM.from_FSM M (t_target t))\<close> \<open>\<And>q p. path (FSM.from_FSM S (t_target t)) q p \<Longrightarrow> path (FSM.from_FSM M (t_target t)) q p\<close> by fastforce
    qed
       

    show "tM \<in> transitions ?S" 
      using * \<open>q' \<in> reachable_nodes S\<close>
      using \<open>tM \<in> FSM.transitions M\<close> \<open>tS \<in> FSM.transitions S\<close> \<open>t_input tM = x\<close> \<open>t_input tS = x\<close> \<open>t_source tM = q'\<close> \<open>t_source tS = q'\<close> \<open>t_target t \<in> FSM.nodes S\<close> by fastforce       
  qed 
     

  show ?thesis
    unfolding is_preamble_def
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_nodes_prop_1
    using has_nodes_prop_2 by blast    
qed










subsubsection \<open>Alternative Calculation\<close>

definition m_ex_DR :: "(integer,integer,integer) fsm" where
  "m_ex_DR = fsm_from_list 0  [(0,0,0,100),
                               (100,0,0,101), 
                               (100,0,1,101),
                               (101,0,0,102),
                               (101,0,1,102),
                               (102,0,0,103),
                               (102,0,1,103),
                               (103,0,0,104),
                               (103,0,1,104),
                               (104,0,0,100),
                               (104,0,1,100),
                               (104,1,0,400),
                               (0,0,2,200),
                               (200,0,2,201),
                               (201,0,2,202),
                               (202,0,2,203),
                               (203,0,2,200),
                               (203,1,0,400),
                               (0,1,0,300),
                               (100,1,0,300),
                               (101,1,0,300),
                               (102,1,0,300),
                               (103,1,0,300),
                               (200,1,0,300),
                               (201,1,0,300),
                               (202,1,0,300),
                               (300,0,0,300),
                               (300,1,0,300),
                               (400,0,0,300),
                               (400,1,0,300)]"




(* TODO: rework to stop if the initial state is added (maybe check initial state first all the time) *)                            


fun d_states' :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "d_states' f q q0 inputList nodeList nodeSet 0 m = (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> m)" |
  "d_states' f q q0 inputList nodeList nodeSet (Suc k) m = 
    (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> (case find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList
          of None            \<Rightarrow> m |
             Some (q',x,nodeList') \<Rightarrow> d_states' f q q0 inputList nodeList' (insert q' nodeSet) k (m@[(q',x)])))"

fun d_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "d_states M k q = (if q = initial M 
                      then [] 
                      else d_states' (h M) q (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (reachable_nodes_as_list M))) {q} k [])"

value "d_states m_ex_H 5 1"
value "d_states m_ex_H 5 2"
value "d_states m_ex_H 5 3"
value "d_states m_ex_H 5 4"

(*
fun d_states_old :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "d_states_old M 0 q = []" |
  "d_states_old M (Suc k) q =  
    (if length (d_states_old M k q) < k 
      then (d_states_old M k q)
      else (case find 
                  (\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states_old M k q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> transitions M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states_old M k q) . fst qx' = (t_target t))))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs_as_list M)) ((initial M) # (removeAll (initial M) (nodes_as_list M)))))
            of Some qx \<Rightarrow> (d_states_old M k q)@[qx] | 
               None \<Rightarrow> (d_states_old M k q)))"


lemma d_states_old_d_states':
shows  "(\<exists> qx \<in> set (d_states' (h M) q (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (reachable_nodes_as_list M))) {q} k []) . fst qx = initial M)
    \<or>((d_states' (h M) q (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (reachable_nodes_as_list M))) {q} k []) = d_states_old M (Suc k) q)" 
proof (induction k)
  case 0
  then show ?case 
next
  case (Suc k)
  then show ?case sorry
qed
*)  






lemma d_states'_length :
  "length (d_states' f q q0 inputList nodeList nodeSet k m) \<le> (length m) + Suc k"
proof (induction k arbitrary: nodeList nodeSet m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList"; auto)
next
  case (Suc k)
  then show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList = Some (q',x,nodeList')"
        by (metis prod_cases3)
      show ?thesis 
        unfolding d_states'.simps None *
        using Suc.IH[of nodeList' "insert q' nodeSet" "m@[(q',x)]"] by auto
    qed
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed

lemma d_states'_length_min :
  "length (d_states' f q q0 inputList nodeList nodeSet k m) \<ge> (length m)"
proof (induction k arbitrary: nodeList nodeSet m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList"; auto)
next
  case (Suc k)
  then show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList = Some (q',x,nodeList')"
        by (metis prod_cases3)
      show ?thesis 
        unfolding d_states'.simps None *
        using Suc.IH[of "m@[(q',x)]" nodeList' "insert q' nodeSet" ] by auto
    qed
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed

lemma d_states_length :
  "length (d_states M k q) \<le> Suc k"
  using d_states'_length unfolding d_states.simps
proof -
  have f1: "\<forall>n. length ([]::('a \<times> 'b) list) \<le> n"
    by auto
  have "length (d_states' (h M) q (FSM.initial M) (inputs_as_list M) (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M))) {q} k []) \<le> Suc k"
    by (metis add.commute d_states'_length gen_length_code(1) gen_length_def)
  then show "length (if q = FSM.initial M then [] else d_states' (h M) q (FSM.initial M) (inputs_as_list M) (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M))) {q} k []) \<le> Suc k"
    using f1 by presburger
qed 



lemma d_states'_helper1 :
  "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x \<Longrightarrow> (d_states' f q q0 iL nL nS k m) = m@[(q0,x)]" 
  by (cases k; auto)




lemma d_states'_next :
  "\<exists> m' . (d_states' f q q0 iL nL nS (Suc k) m) = (d_states' f q q0 iL nL nS k m)@m'" 
proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
  case None
  then show ?thesis proof (induction k arbitrary: nL nS m)
    case 0
    show ?case proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      show ?thesis unfolding d_states'.simps \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
    next
      case (Some a)
      then obtain q' x nodeList' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nodeList')"
          by (metis prod_cases3)
      show ?thesis unfolding d_states'.simps None **
        by (simp add: option.case_eq_if) 
    qed
  next
    case (Suc k')
    show ?case proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis unfolding d_states'.simps \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
    next
      case (Some a)
      then obtain q' x nodeList' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nodeList')"
          by (metis prod_cases3)
      show ?thesis proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>a\<in>f (q0, x). case a of (y, q'') \<Rightarrow> q'' \<in> (insert q' nS))) iL")
        case None
        show ?thesis 
          using Suc.IH[OF None]
          using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> ** by auto
      next
        case (Some x')

        have "d_states' f q q0 iL nL nS (Suc (Suc k')) m = d_states' f q q0 iL nodeList' (insert q' nS) (Suc k') (m@[(q',x)])"
         and "d_states' f q q0 iL nL nS (Suc k') m = d_states' f q q0 iL nodeList' (insert q' nS) k' (m@[(q',x)])"
          using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> ** 
          by auto
        then have "d_states' f q q0 iL nL nS (Suc (Suc k')) m = d_states' f q q0 iL nL nS (Suc k') m"
          unfolding d_states'_helper1[OF Some] by auto

        then show ?thesis by auto
      qed
    qed
  qed
next
  case (Some a)
  show ?thesis using d_states'_helper1[OF Some]
    by (metis append_Nil2) 
qed
  




lemma d_states'_prefix :
  assumes "i \<le> k"
  shows "take (length (d_states' f q q0 iL nL nS i m)) (d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL nL nS i m)" 
using assms proof (induction "k - i" arbitrary: nL nS m k i)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "i < k" by auto
  
  show ?case proof (cases d)
    case 0
    then have "k = Suc i" using Suc by auto
    show ?thesis unfolding \<open>k = Suc i\<close> using d_states'_next[of f q q0 iL nL nS i m]
      by auto 
  next
    case (Suc d')
    moreover obtain k' where "k = Suc k'"
      using Suc.hyps by (metis Suc_le_D diff_le_self) 
    ultimately have "Suc d = Suc k' - i" using Suc.hyps(2) by auto 
    then have "d = k' - i" by auto 

    have "i \<le> k'" using \<open>k = Suc k'\<close> \<open>i < k\<close> by auto

    show ?thesis 
      using Suc.hyps(1)[OF \<open>d = k' - i\<close> \<open>i \<le> k'\<close>]
      by (metis \<open>k = Suc k'\<close> append_assoc append_eq_conv_conj append_take_drop_id d_states'_next) 
  qed
qed


lemma d_states'_prefix_ex :
  assumes "i \<le> k"
  shows "\<exists> m' . (d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL nL nS i m) @ m'" 
  using d_states'_prefix[OF assms] by (metis (no_types) append_take_drop_id)
 
lemma d_states'_take :
  "take (length m) (d_states' f q q0 iL nL nS k m) = m"
proof (induction k arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL"; auto)
next
  case (Suc k)
  then show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nodeList')"
        by (metis prod_cases3)

      have scheme: "\<And> xs ys y . take (length (ys@y)) xs = ys@y \<Longrightarrow> take (length ys) xs = ys"
        by (metis append.assoc append_eq_conv_conj) 
      have "take (length (m @ [(q', x)])) (d_states' f q q0 iL nL nS (Suc k) m) = (m @ [(q', x)])"
        unfolding d_states'.simps None *
        using Suc.IH[of "m@[(q',x)]" nodeList' "insert q' nS" ] by auto
      then show ?thesis
        unfolding d_states'.simps None * 
        using scheme[of m "[(q',x)]"] by force
    qed
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed

lemma d_states'_take' :
  "take (length m) (d_states' f q q0 iL nL nS k (m@m')) = m"
  using d_states'_take
  by (metis (no_types, lifting) add_leE append_eq_append_conv d_states'_length_min length_append length_take min_absorb2 take_add)



lemma d_states'_distinct :
  assumes "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "nS = insert q (set (map fst m))"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
  shows "distinct (map fst (d_states' f q q0 iL nL nS k m))" 
using assms proof (induction k arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL"; auto)
next
  case (Suc k)
  then show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "(d_states' f q q0 iL nL nS (Suc k) m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
      then show ?thesis using Suc.prems by auto
    next
      case (Some a)
      then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      have "q' \<in> set nL"
      and  "set nL' = set nL - {q'}"
      and  "distinct nL'"
        using find_remove_2_set[OF * ]  \<open>distinct nL\<close> by auto

      have "distinct (map fst (m@[(q',x)]))" 
        using \<open>nS = insert q (set (map fst m))\<close> \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
      have "q0 \<notin> insert q' nS"
        using Suc.prems(3) Suc.prems(6) \<open>q' \<in> set nL\<close> by auto
      have "set (map fst (m@[(q',x)])) \<subseteq> insert q' nS" 
        using \<open>nS = insert q (set (map fst m))\<close> by auto
      have "insert q' nS = insert q (set (map fst (m@[(q',x)])))"
        using \<open>nS = insert q (set (map fst m))\<close> by auto
      have "q0 \<notin> set nL'"
        by (simp add: Suc.prems(6) \<open>set nL' = set nL - {q'}\<close>)
      have "set nL' \<inter> insert q' nS = {}"
        using Suc.prems(7) \<open>set nL' = set nL - {q'}\<close> by auto

      show ?thesis 
        unfolding d_states'.simps None *
        using Suc.IH[OF \<open>distinct (map fst (m@[(q',x)]))\<close>
                        \<open>set (map fst (m@[(q',x)])) \<subseteq> insert q' nS\<close>
                        \<open>q0 \<notin> insert q' nS\<close>
                        \<open>insert q' nS = insert q (set (map fst (m@[(q',x)])))\<close>
                        \<open>distinct nL'\<close>
                        \<open>q0 \<notin> set nL'\<close>
                        \<open>set nL' \<inter> insert q' nS = {}\<close>] by auto
    qed
  next
    case (Some a)
    then show ?thesis using Suc by auto
  qed
qed




lemma d_states'_index_properties : 
  assumes "i < length (d_states' (h M) q q0 iL nL nS k m)"
  and     "i \<ge> length m"
  and     "q0 \<noteq> q"
  and     "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "nS = insert q (set (map fst m))"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
shows "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<in> (insert q0 (set nL))" 
      "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> q"
      "snd (d_states' (h M) q q0 iL nL nS k m ! i) \<in> set iL"
      "(\<forall> qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m)) . fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m)) . fst qx' = (t_target t))))"
proof -
  have combined_props : 
    "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<in> (insert q0 (set nL))
      \<and> fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> q
      \<and> snd (d_states' (h M) q q0 iL nL nS k m ! i) \<in> set iL
      \<and> (\<exists> t \<in> transitions M . t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i))
      \<and> (\<forall> t \<in> transitions M . (t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m)) . fst qx' = (t_target t))))"    
  using assms proof (induction k arbitrary: nL nS m)
    case 0
    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      then have "(d_states' (h M) q q0 iL nL nS 0 m) = m" by auto
      then have "False" using "0.prems"(1,2) by auto
      then show ?thesis by simp
    next
      case (Some x)
      have "(d_states' (h M) q q0 iL nL nS 0 m) = m@[(q0,x)]" using d_states'_helper1[OF Some] by assumption
      then have "(d_states' (h M) q q0 iL nL nS 0 m ! i) = (q0,x)" using "0.prems"(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "fst (q0, x) \<noteq> q" using \<open>q0 \<noteq> q\<close> by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
       
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states' (h M) q q0 iL nL nS 0 m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (mono_tags, lifting) case_prod_beta' mem_Collect_eq prod.collapse) 
        then show "t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states' (h M) q q0 iL nL nS 0 m)). fst qx' = t_target t)"
          using \<open>nS = insert q (set (map fst m))\<close>
          using "0.prems"(1) "0.prems"(2) \<open>d_states' (h M) q q0 iL nL nS 0 m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(d_states' (h M) q q0 iL nL nS 0 m ! i) = (q0,x)\<close> by blast
    qed
  next
    case (Suc k)


    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL")
        case None
        then have "(d_states' (h M) q q0 iL nL nS (Suc k) m) = m" using \<open>find (\<lambda>x. h M (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (q0, x). q'' \<in> nS)) iL = None\<close> by auto
        then have "False" using Suc.prems(1,2) by auto
        then show ?thesis by simp
      next
        case (Some a)
        then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)
        then have "d_states' (h M) q q0 iL nL nS (Suc k) m = d_states' (h M) q q0 iL nL' (insert q' nS) k (m@[(q',x)])"
          using None by auto
        then have "i < length (d_states' (h M) q q0 iL nL' (insert q' nS) k (m@[(q',x)]))"
          using Suc.prems(1) by auto

        have "insert q' nS = insert q (set (map fst (m @ [(q', x)])))"
          using Suc.prems(7) by auto

        have "q' \<in> set nL"
        and  "set nL' = set nL - {q'}"
        and  "distinct nL'"
          using find_remove_2_set[OF ** ]  \<open>distinct nL\<close> by auto
        have "set nL' \<subseteq> set nL"
          using find_remove_2_set(4)[OF ** \<open>distinct nL\<close>] by blast

        have "distinct (map fst (m @ [(q', x)]))" 
          using \<open>nS = insert q (set (map fst m))\<close> \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "distinct (map fst (m@[(q',x)]))" 
          using \<open>nS = insert q (set (map fst m))\<close> \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "q0 \<notin> insert q' nS"
          using Suc.prems(9) Suc.prems(6) \<open>q' \<in> set nL\<close> by auto
        have "set (map fst (m@[(q',x)])) \<subseteq> insert q' nS" 
          using \<open>nS = insert q (set (map fst m))\<close> by auto
        have "insert q' nS = insert q (set (map fst (m@[(q',x)])))"
          using \<open>nS = insert q (set (map fst m))\<close> by auto
        have "q0 \<notin> set nL'"
          by (metis Suc.prems(9) \<open>set nL' \<subseteq> set nL\<close> subset_code(1))
        have "set nL' \<inter> insert q' nS = {}"
          using Suc.prems(10) \<open>set nL' = set nL - {q'}\<close> by auto


        show ?thesis proof (cases "length (m @ [(q', x)]) \<le> i")
          case True

          show ?thesis
            using Suc.IH[OF \<open>i < length (d_states' (h M) q q0 iL nL' (insert q' nS) k (m@[(q',x)]))\<close>
                            True
                            \<open>q0 \<noteq> q\<close>
                            \<open>distinct (map fst (m @ [(q', x)]))\<close>
                            \<open>set (map fst (m@[(q',x)])) \<subseteq> insert q' nS\<close>
                            \<open>q0 \<notin> insert q' nS\<close>
                            \<open>insert q' nS = insert q (set (map fst (m@[(q',x)])))\<close>
                            \<open>distinct nL'\<close>
                            \<open>q0 \<notin> set nL'\<close>
                            \<open>set nL' \<inter> insert q' nS = {}\<close> ]
            unfolding \<open>d_states' (h M) q q0 iL nL nS (Suc k) m = d_states' (h M) q q0 iL nL' (insert q' nS) k (m@[(q',x)])\<close> 
            using \<open>set nL' \<subseteq> set nL\<close> by blast
        next
          case False 
          then have "i = length m"
            using Suc.prems(2) by auto
          then have ***: "d_states' (h M) q q0 iL nL nS (Suc k) m ! i = (q',x)"
            unfolding \<open>d_states' (h M) q q0 iL nL nS (Suc k) m = d_states' (h M) q q0 iL nL' (insert q' nS) k (m@[(q',x)])\<close> 
            using d_states'_take
            by (metis length_append_singleton lessI nth_append_length nth_take) 
            
          
          have "q' \<in> insert q0 (set nL)"
            by (simp add: \<open>q' \<in> set nL\<close>) 
          moreover have "q' \<noteq> q"
            using Suc.prems(10) Suc.prems(7) \<open>q' \<in> set nL\<close> by auto  
          moreover have "x \<in> set iL"
            using find_remove_2_set(3)[OF ** ] by auto
          moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x) "
            using find_remove_2_set(1)[OF ** ] unfolding h.simps by force
          moreover have "(\<forall>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x \<longrightarrow> t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states' (h M) q q0 iL nL nS (Suc k) m)). fst qx' = t_target t))"
            unfolding \<open>i = length m\<close> d_states'_take 
            using find_remove_2_set(1)[OF ** ] unfolding h.simps \<open>nS = insert q (set (map fst m))\<close> by force
          ultimately show ?thesis 
            unfolding *** fst_conv snd_conv by blast
        qed 
      qed
    next
      case (Some x)
      have "(d_states' (h M) q q0 iL nL nS (Suc k) m) = m@[(q0,x)]" using d_states'_helper1[OF Some] by assumption
      then have "(d_states' (h M) q q0 iL nL nS (Suc k) m ! i) = (q0,x)" using Suc.prems(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "fst (q0, x) \<noteq> q" using \<open>q0 \<noteq> q\<close> by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
      moreover have "\<And> qx' . qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS (Suc k) m)) - set (take (length m) (d_states' (h M) q q0 iL nL nS (Suc k) m)) \<Longrightarrow> fst (q0, x) \<noteq> fst qx'"
        using Suc.prems(1,2) \<open>d_states' (h M) q q0 iL nL nS (Suc k) m = m @ [(q0, x)]\<close> by auto
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states' (h M) q q0 iL nL nS (Suc k) m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (mono_tags, lifting) case_prod_beta' mem_Collect_eq prod.collapse) 
        then show "t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states' (h M) q q0 iL nL nS (Suc k) m)). fst qx' = t_target t)"
          using \<open>nS = insert q (set (map fst m))\<close>
          using Suc.prems(1,2) \<open>d_states' (h M) q q0 iL nL nS (Suc k) m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(d_states' (h M) q q0 iL nL nS (Suc k) m ! i) = (q0,x)\<close> by blast
    qed
  qed

  then show "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<in> (insert q0 (set nL))" 
            "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> q"
            "snd (d_states' (h M) q q0 iL nL nS k m ! i) \<in> set iL"
            "(\<exists> t \<in> transitions M . t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i))"
            "(\<forall> t \<in> transitions M . (t_source t = fst (d_states' (h M) q q0 iL nL nS k m ! i) \<and> t_input t = snd (d_states' (h M) q q0 iL nL nS k m ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m)) . fst qx' = (t_target t))))"
    by blast+

  show "(\<forall> qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m)) . fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> fst qx')" 
  proof 
    fix qx' assume "qx' \<in> set (take i (d_states' (h M) q q0 iL nL nS k m))"
    then obtain j where "(take i (d_states' (h M) q q0 iL nL nS k m)) ! j = qx'" and "j < length (take i (d_states' (h M) q q0 iL nL nS k m))"
      by (meson in_set_conv_nth)
    then have "fst qx' = (map fst (d_states' (h M) q q0 iL nL nS k m)) ! j" and "j < length (d_states' (h M) q q0 iL nL nS k m)" by auto
      
    moreover have "fst (d_states' (h M) q q0 iL nL nS k m ! i) = (map fst (d_states' (h M) q q0 iL nL nS k m)) ! i"
      using assms(1) by auto

    moreover have "j \<noteq> i" 
      using \<open>j < length (take i (d_states' (h M) q q0 iL nL nS k m))\<close> by auto
      
    ultimately show "fst (d_states' (h M) q q0 iL nL nS k m ! i) \<noteq> fst qx'"
      using assms(1)
      using d_states'_distinct[OF \<open>distinct (map fst m)\<close> \<open>set (map fst m) \<subseteq> nS\<close> \<open>q0 \<notin> nS\<close> \<open>nS = insert q (set (map fst m))\<close> \<open>distinct nL\<close> \<open>q0 \<notin> set nL\<close> \<open>set nL \<inter> nS = {}\<close>]
      by (metis distinct_Ex1 in_set_conv_nth length_map)
  qed
qed 



lemma d_states_index_properties : 
  assumes "i < length (d_states M k q)"
shows "fst (d_states M k q ! i) \<in> (reachable_nodes M - {q})" 
      "fst (d_states M k q ! i) \<noteq> q"
      "snd (d_states M k q ! i) \<in> inputs M"
      "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
proof -
  have combined_goals : "fst (d_states M k q ! i) \<in> (reachable_nodes M - {q})
                          \<and> fst (d_states M k q ! i) \<noteq> q
                          \<and> snd (d_states M k q ! i) \<in> inputs M
                          \<and> (\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')
                          \<and> (\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))
                          \<and> (\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
  proof (cases "q = initial M")
    case True
    then have "d_states M k q = []" by auto
    then have "False" using assms by auto
    then show ?thesis by simp
  next
    case False
    then have *: "d_states M k q = d_states' (h M) q (initial M) (inputs_as_list M) (removeAll q (removeAll (initial M) (reachable_nodes_as_list M))) {q} k []" by auto

    have "initial M \<in> reachable_nodes M" unfolding reachable_nodes_def by auto
    then have "insert (FSM.initial M) (set (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M)))) = reachable_nodes M - {q}"
      using reachable_nodes_as_list_set False by auto 



    have "i < length (d_states' (h M) q (FSM.initial M) (inputs_as_list M) (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M))) {q} k [])"
      using assms * by simp
    moreover have "length [] \<le> i" by auto
    moreover have "initial M \<noteq> q" using False by auto
    moreover have "distinct (map fst [])" by auto
    moreover have "set (map fst []) \<subseteq> {q}" by auto
    moreover have "initial M \<notin> {q}" using False by auto
    moreover have "{q} = insert q (set (map fst []))" by auto
    moreover have "distinct (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M)))" using nodes_as_list_distinct
      by (simp add: distinct_removeAll) 
    moreover have "FSM.initial M \<notin> set (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M)))" by auto
    moreover have "set (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M))) \<inter> {q} = {}" by auto

    moreover show ?thesis 
      using d_states'_index_properties[OF calculation] unfolding *[symmetric] inputs_as_list_set \<open>insert (FSM.initial M) (set (removeAll q (removeAll (FSM.initial M) (reachable_nodes_as_list M)))) = reachable_nodes M - {q}\<close> by blast
  qed

  then show "fst (d_states M k q ! i) \<in> (reachable_nodes M - {q})" 
      "fst (d_states M k q ! i) \<noteq> q"
      "snd (d_states M k q ! i) \<in> inputs M"
      "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
    by blast+
qed




lemma d_states_prefix :
  assumes "i \<le> k"
  shows "take (length (d_states M i q)) (d_states M k q) = (d_states M i q)" 
  using d_states'_prefix[OF assms] by (cases "q = initial M"; auto)

lemma d_states_prefix_ex :
  assumes "i \<le> k"
  shows "\<exists> m' . (d_states M k q) = (d_states M i q) @ m'" 
proof (cases "q = initial M")
  case True
  then show ?thesis by auto
next
  case False
  then have "(q = initial M) = False" by auto
  show ?thesis 
    unfolding d_states.simps \<open>(q = initial M) = False\<close>
    by (meson assms d_states'_prefix_ex)
qed


lemma distinct_not_in_prefix :
  assumes "\<And> i . (\<And> x . x \<in> set (take i xs) \<Longrightarrow> xs ! i \<noteq> x)"
  shows "distinct xs"
  using assms list_distinct_prefix by blast 


lemma d_states_distinct :
  "distinct (map fst (d_states M k q))"
proof -
  have *: "\<And> i q . i < length (map fst (d_states M k q)) \<Longrightarrow> q \<in> set (take i (map fst (d_states M k q))) \<Longrightarrow> ((map fst (d_states M k q)) ! i) \<noteq> q"
    using d_states_index_properties(2,4) by fastforce 
  then have "(\<And>i. i < length (map fst (d_states M k q)) \<Longrightarrow>
          map fst (d_states M k q) ! i \<notin> set (take i (map fst (d_states M k q))))"
  proof -
    fix i :: nat
    assume a1: "i < length (map fst (d_states M k q))"
    then have "\<forall>p. p \<notin> set (take i (d_states M k q)) \<or> fst (d_states M k q ! i) \<noteq> fst p"
      by (metis (no_types) d_states_index_properties(4) length_map)
    then show "map fst (d_states M k q) ! i \<notin> set (take i (map fst (d_states M k q)))"
      using a1 by (metis (no_types) length_map list_map_source_elem nth_map take_map)
  qed
  then show ?thesis
    using list_distinct_prefix[of "map fst (d_states M k q)"] by blast
qed



lemma d_states_nodes : 
  "set (map fst (d_states M k q)) \<subseteq> reachable_nodes M - {q}"
  using d_states_index_properties(1)[of _ M k q] list_property_from_index_property[of "map fst (d_states M k q)" "\<lambda>q' . q' \<in> reachable_nodes M - {q}"]
  by (simp add: subsetI)

(* TODO: move *)
abbreviation "size_r M \<equiv> card (reachable_nodes M)"

lemma d_states_size :
  assumes "q \<in> reachable_nodes M"
  shows "length (d_states M k q) \<le> size_r M - 1"
proof -
  show ?thesis 
    using d_states_nodes[of M k q]
          d_states_distinct[of M k q]
          fsm_nodes_finite[of M]
          assms
    by (metis Diff_empty List.finite_set card_Diff_singleton card_mono distinct_card finite_Diff_insert length_map reachable_nodes_as_list_set)     
qed


lemma d_states'_Suc_length :
  assumes "(d_states' f q q0 iL nL nS (Suc k) m) \<noteq> (d_states' f q q0 iL nL nS k m)"
  shows "length (d_states' f q q0 iL nL nS k m) = (length m) + k"
using assms proof (induction k arbitrary: nS nL m)
  case 0
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis by auto
  next
    case (Some x)
    then have "(d_states' f q q0 iL nL nS (Suc 0) m) = (d_states' f q q0 iL nL nS 0 m)"
      unfolding d_states'_helper1[OF Some] by auto
    then show ?thesis 
      using "0.prems" by simp
  qed
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      have "(d_states' f q q0 iL nL nS (Suc (Suc k)) m) = (d_states' f q q0 iL nL nS (Suc k) m)"
        unfolding d_states'.simps None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
      then show ?thesis 
        using Suc.prems by simp
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)

      have d1:"(d_states' f q q0 iL nL nS (Suc (Suc k)) m) = d_states' f q q0 iL nL' (insert q' nS) (Suc k) (m@[(q',x)])"
      and  d2:"(d_states' f q q0 iL nL nS (Suc k) m) = d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])"
        using None ** by auto


      show ?thesis proof (cases "d_states' f q q0 iL nL' (insert q' nS) (Suc k) (m@[(q',x)]) \<noteq> d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])")
        case True
        show ?thesis 
          using Suc.IH[OF True] unfolding d2 by auto
      next
        case False
        then have "(d_states' f q q0 iL nL nS (Suc (Suc k)) m) = (d_states' f q q0 iL nL nS (Suc k) m)"
          unfolding d1 d2 by auto
        then show ?thesis using Suc.prems by simp
      qed
    qed

  next
    case (Some x)
    then have "(d_states' f q q0 iL nL nS (Suc (Suc k)) m) = (d_states' f q q0 iL nL nS (Suc k) m)"
      unfolding d_states'_helper1[OF Some] by auto
    then show ?thesis 
      using Suc.prems by simp
  qed
qed




lemma d_states'_Suc_eq :
  assumes "(d_states' f q q0 iL nL nS (Suc k) m) = (d_states' f q q0 iL nL nS k m)"
  shows "(d_states' f q q0 iL nL nS (Suc (Suc k)) m) = (d_states' f q q0 iL nL nS k m)" 
using assms proof (induction k arbitrary: nS nL m)
  case 0
  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    then have "(d_states' f q q0 iL nL nS 0 m) = m" using None by auto
    then have "(d_states' f q q0 iL nL nS (Suc 0) m) = m" using 0 by auto
    then have "(d_states' f q q0 iL nL nS (Suc (Suc 0)) m) = m"
      by (metis Zero_not_Suc add_eq_self_zero d_states'_Suc_length) 
    then show ?thesis using \<open>(d_states' f q q0 iL nL nS 0 m) = m\<close> by auto
  next
    case (Some a)
    show ?thesis using assms unfolding d_states'_helper1[OF Some] by simp
  qed
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis unfolding Suc using None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      show ?thesis proof (rule ccontr)
        assume "d_states' f q q0 iL nL nS (Suc (Suc (Suc k))) m \<noteq> d_states' f q q0 iL nL nS (Suc k) m"
        then have "d_states' f q q0 iL nL' (insert q' nS) (Suc (Suc k)) (m@[(q',x)]) \<noteq> d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])"
          using None ** by auto
        then have "d_states' f q q0 iL nL' (insert q' nS) (Suc k) (m @ [(q', x)]) \<noteq> d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])"
          using Suc.IH[of nL' "insert q' nS" "(m@[(q',x)])" ] by blast
        then have "d_states' f q q0 iL nL nS (Suc (Suc k)) m \<noteq> d_states' f q q0 iL nL nS (Suc k) m"
          using None ** by auto
        then show "False"
          using Suc.prems by auto
      qed
    qed
  next
    case (Some a)
    show ?thesis using assms unfolding d_states'_helper1[OF Some] by simp
  qed
qed


lemma d_states'_gte_eq :
  assumes "(d_states' f q q0 iL nL nS (Suc i) m) = (d_states' f q q0 iL nL nS i m)"
  and     "i \<le> k"
shows "(d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL nL nS i m)" 
  using assms proof (induction "k-i" arbitrary: k i)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "d = k - Suc i" and "Suc i \<le> k" by auto

  have "(d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL nL nS (Suc i) m)"
    using Suc.hyps(1)[OF \<open>d = k - Suc i\<close> _ \<open>Suc i \<le> k\<close>]
    using d_states'_Suc_eq[OF Suc.prems(1)] Suc.prems(1) by metis
  then show ?case 
    using Suc.prems(1) by simp
qed


lemma d_states'_prefix_length :
  assumes "i \<le> k"
  and     "(d_states' f q q0 iL nL nS k m) \<noteq> (d_states' f q q0 iL nL nS i m)"
shows "length (d_states' f q q0 iL nL nS i m) = (length m) + i"
  using assms proof (induction "k - i" arbitrary: k i nS nL m)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "d = k - Suc i" and "Suc i \<le> k" by auto


  show ?case proof (cases "d_states' f q q0 iL nL nS (Suc i) m = d_states' f q q0 iL nL nS i m")
    case True
    then have "(d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL nL nS i m)"
      using d_states'_gte_eq[OF _ \<open>i \<le> k\<close>] by metis
    then have "False"
      using \<open>(d_states' f q q0 iL nL nS k m) \<noteq> (d_states' f q q0 iL nL nS i m)\<close> by simp
    then show ?thesis by simp
  next
    case False
    then show ?thesis using d_states'_Suc_length by metis
  qed
qed


  
lemma d_states_max_iterations :
  assumes "k \<ge> size_r M - 1" and "q \<in> reachable_nodes M"
  shows "d_states M k q = d_states M (size_r M - 1) q" 
proof (rule ccontr)
  assume "d_states M k q \<noteq> d_states M (size_r M - 1) q"
  then have "(q = initial M) = False" by auto
  
  have "length (d_states M (size_r M - 1) q) = size_r M - 1"
    using d_states'_prefix_length[OF assms(1)]
    using \<open>d_states M k q \<noteq> d_states M (size_r M - 1) q\<close> 
    unfolding d_states.simps \<open>(q = initial M) = False\<close>
    by fastforce

  moreover have "length (d_states M k q) \<le> size_r M - 1"
    using d_states_size[OF assms(2)] by auto
  ultimately show "False"
    by (metis \<open>d_states M k q \<noteq> d_states M (size_r M - 1) q\<close> assms(1) d_states_prefix take_all)
qed



lemma d_states'_initial :
  assumes "qx \<in> set (d_states' f q q0 iL nL nS k m) - set m"
  and     "fst qx = q0"
  shows "(last (d_states' f q q0 iL nL nS k m)) = qx"
using assms(1) proof (induction k arbitrary: nS nL m)
  case 0
  then have "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL \<noteq> None" 
    unfolding d_states'.simps
    by (metis Diff_cancel empty_iff option.simps(4)) 
  then obtain x where *: "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x" 
    by auto
  
  have "set (d_states' f q q0 iL nL nS k m) - set m = {qx}"
    using "0.prems"(1) unfolding d_states'_helper1[OF *]
    by auto 
  
  then show ?case unfolding d_states'_helper1[OF *]
    by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append) 
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      have "(d_states' f q q0 iL nL nS (Suc k) m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
      then have "False" 
        using Suc.prems(1)
        by simp
      then show ?thesis by simp
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)
      then have "(d_states' f q q0 iL nL nS (Suc k) m) = (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)]))"
        using None by auto
      then have "qx \<in> set (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])) - set m"
        using Suc.prems by auto
      moreover have "q0 \<noteq> q'"
        using None unfolding find_None_iff
        using find_remove_2_set(1,2,3)[OF **]
        by blast
      ultimately have "qx \<in> set (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])) - set (m@[(q',x)])"
        using \<open>fst qx = q0\<close> by auto
      then show ?thesis 
        using Suc.IH unfolding \<open>(d_states' f q q0 iL nL nS (Suc k) m) = (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)]))\<close> by metis
    qed
  next
    case (Some a)

    have "set (d_states' f q q0 iL nL nS k m) - set m = {qx}"
      using Suc.prems(1) unfolding d_states'_helper1[OF Some]
      by auto 
    
    then show ?thesis unfolding d_states'_helper1[OF Some]
      by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append)
  qed 
qed



lemma d_states_initial :
  assumes "qx \<in> set (d_states M k q)" 
  and     "fst qx = initial M"
shows "(last (d_states M k q)) = qx"
  using assms(1) d_states'_initial[of qx "h M" q "initial M" _ _ _ k "[]", OF _ assms(2)]
  by (cases "q = initial M"; auto)




lemma d_states_q_noncontainment :
  shows "\<not>(\<exists> qqx \<in> set (d_states M k q) . fst qqx = q)" 
  using d_states_index_properties(2)
  by (metis in_set_conv_nth) 



(* TODO: rename, move *)
lemma list_index_fun_gt : "\<And> xs (f::'a \<Rightarrow> nat) i j . (\<And> i . Suc i < length xs \<Longrightarrow> f (xs ! i) > f (xs ! (Suc i))) \<Longrightarrow> j < i \<Longrightarrow> i < length xs \<Longrightarrow> f (xs ! j) > f (xs ! i)"
proof -
  fix xs::"'a list" 
  fix f::"'a \<Rightarrow> nat" 
  fix i j 
  assume "(\<And> i . Suc i < length xs \<Longrightarrow> f (xs ! i) > f (xs ! (Suc i)))"
     and "j < i"
     and "i < length xs"
  then show "f (xs ! j) > f (xs ! i)"
  proof (induction "i - j" arbitrary: i j)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    then show ?case
    proof -
      have f1: "\<forall>n. \<not> Suc n < length xs \<or> f (xs ! Suc n) < f (xs ! n)"
        using Suc.prems(1) by presburger
      have f2: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
        using Suc_leI by satx
      have "x = i - Suc j"
        by (metis Suc.hyps(2) Suc.prems(2) Suc_diff_Suc nat.simps(1))
      then have "\<not> Suc j < i \<or> f (xs ! i) < f (xs ! Suc j)"
        using f1 Suc.hyps(1) Suc.prems(3) by blast
      then show ?thesis
        using f2 f1 by (metis Suc.prems(2) Suc.prems(3) leI le_less_trans not_less_iff_gr_or_eq)
    qed 
  qed
qed


lemma d_states_acyclic_paths' :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) q' p"
  and     "target q' p = q'"
  and     "p \<noteq> []"
shows "False"
proof -

  from \<open>p \<noteq> []\<close> obtain p' t' where "p = t'#p'"
    using list.exhaust by blast
  then have "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) q' (p@[t'])"
    using assms(1,2) by fastforce


  define f :: "('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> nat"
    where f_def: "f = (\<lambda> t . the (find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M k q)))"
  

  have f_prop: "\<And> t . t \<in> set (p@[t']) \<Longrightarrow> (f t < length (d_states M k q)) 
                                      \<and> ((d_states M k q) ! (f t) = (t_source t, t_input t))
                                      \<and> (\<forall> j < f t . fst (d_states M k q ! j) \<noteq> t_source t)"
  proof -
    fix t assume "t \<in> set (p@[t'])"
    then have "t \<in> set p" using \<open>p = t'#p'\<close> by auto
    then have "t \<in> transitions M" and "(t_source t, t_input t) \<in> set (d_states M k q)"
      using assms(1) path_transitions by fastforce+
    then have "\<exists> qx \<in> set (d_states M k q) . (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) qx"
      by (meson fst_conv snd_conv)
    then have "find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M k q) \<noteq> None"
      by (simp add: find_index_exhaustive) 
    then obtain i where *: "find_index (\<lambda> qx . fst qx = t_source t \<and> snd qx = t_input t) (d_states M k q) = Some i"
      by auto

    have "f t < length (d_states M k q)"
      unfolding f_def using find_index_index(1)[OF *] unfolding * by simp
    moreover have "((d_states M k q) ! (f t) = (t_source t, t_input t))"
      unfolding f_def using find_index_index(2)[OF *]
      by (metis "*" option.sel prod.collapse) 
    moreover have "\<forall> j < f t . fst (d_states M k q ! j) \<noteq> t_source t"
      unfolding f_def using find_index_index(3)[OF *] unfolding * 
      using d_states_distinct[of M k q]
      by (metis (mono_tags, lifting) calculation(1) calculation(2) distinct_conv_nth fst_conv length_map less_imp_le less_le_trans not_less nth_map option.sel snd_conv) 
    ultimately show "(f t < length (d_states M k q)) 
                                      \<and> ((d_states M k q) ! (f t) = (t_source t, t_input t))
                                      \<and> (\<forall> j < f t . fst (d_states M k q ! j) \<noteq> t_source t)" by simp
  qed


  have *: "\<And> i . Suc i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
  proof -
    fix i assume "Suc i < length (p@[t'])"
    then have "(p@[t']) ! i \<in> set (p@[t'])" and "(p@[t']) ! (Suc i) \<in> set (p@[t'])"
      using Suc_lessD nth_mem by blast+
    then have "(p@[t']) ! i \<in> transitions M" and "(p@[t']) ! Suc i \<in> transitions M" 
      using path_transitions[OF \<open>path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) q' (p@[t'])\<close>]
      using filter_transitions_simps(5) by blast+
            

    have "f ((p@[t']) ! i) < length (d_states M k q)"
    and  "(d_states M k q) ! (f ((p@[t']) ! i)) = (t_source ((p@[t']) ! i), t_input ((p@[t']) ! i))"
    and  "(\<forall>j<f ((p@[t']) ! i). fst (d_states M k q ! j) \<noteq> t_source ((p@[t']) ! i))"
      using f_prop[OF \<open>(p@[t']) ! i \<in> set (p@[t'])\<close>] by auto

    have "f ((p@[t']) ! Suc i) < length (d_states M k q)"
    and  "(d_states M k q) ! (f ((p@[t']) ! Suc i)) = (t_source ((p@[t']) ! Suc i), t_input ((p@[t']) ! Suc i))"
    and  "(\<forall>j<f ((p@[t']) ! Suc i). fst (d_states M k q ! j) \<noteq> t_source ((p@[t']) ! Suc i))"
      using f_prop[OF \<open>(p@[t']) ! Suc i \<in> set (p@[t'])\<close>] by auto

    have "t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)"
      using \<open>Suc i < length (p@[t'])\<close> \<open>path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) q' (p@[t'])\<close>
      by (simp add: path_source_target_index) 
    then have "t_target ((p@[t']) ! i) \<noteq> q"
      using d_states_index_properties(2)[OF \<open>f ((p@[t']) ! Suc i) < length (d_states M k q)\<close>] 
      unfolding \<open>(d_states M k q) ! (f ((p@[t']) ! Suc i)) = (t_source ((p@[t']) ! Suc i), t_input ((p@[t']) ! Suc i))\<close> by auto
    then have "(\<exists>qx'\<in>set (take (f ((p@[t']) ! i)) (d_states M k q)). fst qx' = t_target ((p@[t']) ! i))"
      using d_states_index_properties(6)[OF \<open>f ((p@[t']) ! i) < length (d_states M k q)\<close>] unfolding \<open>(d_states M k q) ! (f ((p@[t']) ! i)) = (t_source ((p@[t']) ! i), t_input ((p@[t']) ! i))\<close> fst_conv snd_conv
      using \<open>(p@[t']) ! i \<in> transitions M\<close>
      by blast
    then have "(\<exists>qx'\<in>set (take (f ((p@[t']) ! i)) (d_states M k q)). fst qx' = t_source ((p@[t']) ! Suc i))" 
      unfolding \<open>t_target ((p@[t']) ! i) = t_source ((p@[t']) ! Suc i)\<close> by assumption
    then obtain j where "fst (d_states M k q ! j) = t_source ((p@[t']) ! Suc i)" and "j < f ((p@[t']) ! i)"
      by (metis (no_types, lifting) \<open>f ((p@[t']) ! i) < length (d_states M k q)\<close> in_set_conv_nth leD length_take min_def_raw nth_take)
      
    then show "f ((p@[t']) ! i) > f ((p@[t']) ! (Suc i))"
      using \<open>(\<forall>j<f ((p@[t']) ! Suc i). fst (d_states M k q ! j) \<noteq> t_source ((p@[t']) ! Suc i))\<close>
      using leI le_less_trans by blast 
  qed
  
  
  

  have "\<And> i j . j < i \<Longrightarrow> i < length (p@[t']) \<Longrightarrow> f ((p@[t']) ! j) > f ((p@[t']) ! i)"
    using list_index_fun_gt[of "p@[t']" f] * by blast
  then have "f t' < f t'"
    unfolding \<open>p = t'#p'\<close> by fastforce 
  then show "False"
    by auto
qed




(* TODO: move *)
lemma cycle_from_cyclic_path :
  assumes "path M q p"
  and     "\<not> distinct (visited_nodes q p)"
obtains i j where
  "take j (drop i p) \<noteq> []"
  "target (target q (take i p)) (take j (drop i p)) = (target q (take i p))"
  "path M (target q (take i p)) (take j (drop i p))"
proof -
  obtain i j where "i < j" and "j < length (visited_nodes q p)" and "(visited_nodes q p) ! i = (visited_nodes q p) ! j"
    using assms(2) non_distinct_repetition_indices by blast 

  have "(target q (take i p)) = (visited_nodes q p) ! i"
    using \<open>i < j\<close> \<open>j < length (visited_nodes q p)\<close>
    by (metis less_trans take_last_index target.simps visited_nodes_take)

  then have "(target q (take i p)) = (visited_nodes q p) ! j"
    using \<open>(visited_nodes q p) ! i = (visited_nodes q p) ! j\<close> by auto

  have p1: "take (j-i) (drop i p) \<noteq> []"
    using \<open>i < j\<close> \<open>j < length (visited_nodes q p)\<close> by auto 

  have "target (target q (take i p)) (take (j-i) (drop i p)) = (target q (take j p))"
    using \<open>i < j\<close> by (metis add_diff_inverse_nat less_asym' path_append_target take_add)
  then have p2: "target (target q (take i p)) (take (j-i) (drop i p)) = (target q (take i p))"
    using \<open>(target q (take i p)) = (visited_nodes q p) ! i\<close>
    using \<open>(target q (take i p)) = (visited_nodes q p) ! j\<close>
    by (metis \<open>j < length (visited_nodes q p)\<close> take_last_index target.simps visited_nodes_take)

  have p3: "path M (target q (take i p)) (take (j-i) (drop i p))"
    by (metis append_take_drop_id assms(1) path_append_elim)

  show ?thesis using p1 p2 p3 that by blast
qed
  



lemma d_states_acyclic_paths :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "path (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) q' p"
          (is "path ?FM q' p")
shows "distinct (visited_nodes q' p)"
proof (rule ccontr)
  assume "\<not> distinct (visited_nodes q' p)"
  
  obtain i j where p1:"take j (drop i p) \<noteq> []"
               and p2:"target (target q' (take i p)) (take j (drop i p)) = (target q' (take i p))"
               and p3:"path ?FM (target q' (take i p)) (take j (drop i p))"
    using cycle_from_cyclic_path[OF assms \<open>\<not> distinct (visited_nodes q' p)\<close>] by blast
  
  show "False"
    using d_states_acyclic_paths'[OF p3 p2 p1] by assumption
qed






lemma d_states_induces_state_preamble_helper_acyclic :
  shows "acyclic (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q)))"
  unfolding acyclic.simps
  using d_states_acyclic_paths by force

lemma d_states_induces_state_preamble_helper_single_input :
  shows "single_input (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q)))"
      (is "single_input ?FM")
  unfolding single_input.simps filter_transitions_simps
  by (metis (no_types, lifting) d_states_distinct eq_key_imp_eq_value mem_Collect_eq)
    



lemma d_states_induces_state_preamble :
  assumes "\<exists> qx \<in> set (d_states M k q) . fst qx = initial M"
  shows "is_preamble (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M k q))) M q" 
    (is "is_preamble ?S M q")
proof (cases "q = initial M")
  case True
  then have "d_states M k q = []" by auto
  then show ?thesis using assms(1) by auto
next
  case False

  have is_acyclic: "acyclic ?S" 
    using d_states_induces_state_preamble_helper_acyclic[of M k q] by presburger

  have is_single_input: "single_input ?S" 
    using d_states_induces_state_preamble_helper_single_input[of M k q] by presburger

  have is_sub : "is_submachine ?S M"
    unfolding is_submachine.simps filter_transitions_simps by blast

  have has_deadlock_q : "deadlock_state ?S q" 
    using d_states_q_noncontainment[of M k q] unfolding deadlock_state.simps
    by fastforce
  

  have "\<And> q' . q' \<in> reachable_nodes ?S \<Longrightarrow> q' \<noteq> q \<Longrightarrow> \<not> deadlock_state ?S q'"
  proof -
    fix q' assume "q' \<in> reachable_nodes ?S" and "q' \<noteq> q"
    then obtain p where "path ?S (initial ?S) p" and "target (initial ?S) p = q'"
      unfolding reachable_nodes_def by auto

    have "\<exists> qx \<in> set (d_states M k q) . fst qx = q'"
    proof (cases p rule: rev_cases)
      case Nil
      then show ?thesis 
        using assms(1) \<open>target (initial ?S) p = q'\<close> unfolding filter_transitions_simps
        by simp
    next
      case (snoc p' t)
      then have "t \<in> transitions ?S" and "t_target t = q'" 
        using \<open>path ?S (initial ?S) p\<close> \<open>target (initial ?S) p = q'\<close> by auto
      then have "(t_source t, t_input t) \<in> set (d_states M k q)"
        by simp 
      then obtain i where "i < length (d_states M k q)" and "d_states M k q ! i = (t_source t, t_input t)"
        by (meson in_set_conv_nth)

      have "t \<in> transitions M"
        using \<open>t \<in> transitions ?S\<close>
        using is_sub by auto
      then show ?thesis
        using \<open>t_target t = q'\<close> \<open>q' \<noteq> q\<close>
        using d_states_index_properties(6)[OF \<open>i < length (d_states M k q)\<close>]
        unfolding \<open>d_states M k q ! i = (t_source t, t_input t)\<close> fst_conv snd_conv
        by (metis in_set_takeD)
    qed

    then obtain qx where "qx \<in> set (d_states M k q)" and "fst qx = q'" by blast

    then have "(\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx)" 
      using d_states_index_properties(5)[of _ M k q]
      by (metis in_set_conv_nth)
    then have "(\<exists> t \<in> transitions ?S . t_source t = fst qx \<and> t_input t = snd qx)"
      using \<open>qx \<in> set (d_states M k q)\<close> by fastforce      

    then show "\<not> deadlock_state ?S q'" 
      unfolding deadlock_state.simps using \<open>fst qx = q'\<close> by blast
  qed

  then have has_nodes_prop_1 : "\<And> q' . q' \<in> reachable_nodes ?S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state ?S q')" 
    by blast
  
  have has_nodes_prop_2 : "\<And> q' x t t'. q' \<in> reachable_nodes ?S \<Longrightarrow>  x \<in> inputs M \<Longrightarrow>
            t \<in> transitions ?S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in> transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions ?S"
    by simp


  have contains_q : "q \<in> reachable_nodes ?S" 
    using \<open>\<And>q'. \<lbrakk>q' \<in> reachable_nodes ?S; q' \<noteq> q\<rbrakk> \<Longrightarrow> \<not> deadlock_state ?S q'\<close> acyclic_deadlock_reachable is_acyclic by blast


  show ?thesis
    unfolding is_preamble_def
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_nodes_prop_1 has_nodes_prop_2
    by blast
qed
  




fun calculate_state_preamble_from_d_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> 'a  \<Rightarrow> ('a,'b,'c) fsm option" where
  "calculate_state_preamble_from_d_states M q = (if q = initial M
    then Some (initial_preamble M)
    else 
      (let DS = (d_states M (size_r M-1) q);
           DSS = set DS 
        in (case length DS of
            0 \<Rightarrow> None |
            _ \<Rightarrow> if fst (last DS) = initial M
                  then Some (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> DSS))
                  else None)))"


value "calculate_state_preamble_from_d_states m_ex_H 1"
value "calculate_state_preamble_from_d_states m_ex_H 2"
value "calculate_state_preamble_from_d_states m_ex_H 3"
value "calculate_state_preamble_from_d_states m_ex_H 4"

value "calculate_state_preamble_from_d_states m_ex_DR 400"





lemma calculate_state_preamble_from_d_states_soundness :
  assumes "calculate_state_preamble_from_d_states M q = Some S"
  shows "is_preamble S M q"
proof (cases "q = initial M")
  case True
  then have "S = initial_preamble M" using assms by auto
  then show ?thesis 
    using is_preamble_initial[of M] True by presburger
next
  case False

  then have "S = (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M (size_r M-1) q)))"
       and  "length (d_states M (size_r M-1) q) \<noteq> 0"
       and  "fst (last (d_states M (size_r M-1) q)) = initial M"
    using assms by (cases "length (d_states M (size_r M-1) q)"; cases "fst (last (d_states M (size_r M-1) q)) = initial M"; simp)+

  then have "\<exists> qx \<in> set (d_states M (size_r M-1) q) . fst qx = initial M"
    by auto

  then show ?thesis 
    using d_states_induces_state_preamble
    unfolding \<open>S = (filter_transitions M (\<lambda> t . (t_source t, t_input t) \<in> set (d_states M (size_r M-1) q)))\<close>
    by blast 
qed




lemma d_states'_max_length :
  assumes "distinct nL"
  shows "length (d_states' f q q0 iL nL nS k m) \<le> length m + Suc (length nL)" 
using assms proof (induction k arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL"; auto)
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      show ?thesis unfolding d_states'.simps None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)
      then have "(d_states' f q q0 iL nL nS (Suc k) m) = d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])"
        using None by auto
      
      have "length nL = Suc (length nL') \<and> distinct nL'"
        using find_remove_2_set(2,4,5)[OF **] \<open>distinct nL\<close>
        by (metis One_nat_def Suc_pred distinct_card distinct_remove1 equals0D length_greater_0_conv length_remove1 set_empty2 set_remove1_eq) 
      then have "length (d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])) \<le> length m + Suc (length nL)"
        using Suc.IH
        by (metis add_Suc_shift length_append_singleton)
      then show ?thesis 
        using \<open>(d_states' f q q0 iL nL nS (Suc k) m) = d_states' f q q0 iL nL' (insert q' nS) k (m@[(q',x)])\<close> by simp
    qed
  next
    case (Some a)
    show ?thesis unfolding d_states'_helper1[OF Some] by auto 
  qed
qed




lemma d_states_find_props :
  assumes "d_states M (Suc k) q = d_states M k q @ qxs"
  and     "i < length qxs"
shows "fst (qxs ! i) \<noteq> q"
and   "(\<forall>qx'\<in>set (d_states M k q @ (take i qxs)). fst (qxs ! i) \<noteq> fst qx')" 
and   "(\<exists>t\<in> transitions M. t_source t = fst (qxs ! i) \<and> t_input t = snd (qxs ! i))"
and   "(\<forall>t\<in> transitions M.
                        t_source t = fst (qxs ! i) \<and> t_input t = snd (qxs ! i) \<longrightarrow>
                        t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q @ take i qxs). fst qx' = t_target t))"
and   "fst (qxs ! i) \<in> reachable_nodes M"
and   "snd (qxs ! i) \<in> inputs M"
proof -
  have "length (d_states M k q) + i < length (d_states M (Suc k) q)"
   and "(d_states M (Suc k) q) ! (length (d_states M k q) + i) = (qxs ! i)"
    using assms by auto

  have "d_states M k q @ take i qxs = take (length (d_states M k q) + i) (d_states M (Suc k) q)"
    using assms by auto

  show "fst (qxs ! i) \<noteq> q"
and   "(\<forall>qx'\<in>set (d_states M k q @ (take i qxs)). fst (qxs ! i) \<noteq> fst qx')" 
and   "(\<exists>t\<in> transitions M. t_source t = fst (qxs ! i) \<and> t_input t = snd (qxs ! i))"
and   "(\<forall>t\<in> transitions M.
                        t_source t = fst (qxs ! i) \<and> t_input t = snd (qxs ! i) \<longrightarrow>
                        t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q @ take i qxs). fst qx' = t_target t))"
and   "fst (qxs ! i) \<in> reachable_nodes M"
and   "snd (qxs ! i) \<in> inputs M"

    using d_states_index_properties[OF \<open>length (d_states M k q) + i < length (d_states M (Suc k) q)\<close>]
    unfolding \<open>(d_states M (Suc k) q) ! (length (d_states M k q) + i) = (qxs ! i)\<close> 
              \<open>d_states M k q @ take i qxs = take (length (d_states M k q) + i) (d_states M (Suc k) q)\<close> by blast+
qed



(* TODO: move *)
lemma acyclic_single_deadlock_reachable :
  assumes "acyclic M"
  and     "\<And> q' . q' \<in> reachable_nodes M \<Longrightarrow> q' = qd \<or> \<not> deadlock_state M q'"
shows "qd \<in> reachable_nodes M"
  using acyclic_deadlock_reachable[OF assms(1)]
  using assms(2) by auto 

(* TODO: move *)
lemma acyclic_paths_to_single_deadlock :
  assumes "acyclic M"
  and     "\<And> q' . q' \<in> reachable_nodes M \<Longrightarrow> q' = qd \<or> \<not> deadlock_state M q'"
  and     "q \<in> reachable_nodes M"
obtains p where "path M q p" and "target q p = qd"
proof -
  have "q \<in> nodes M" using assms(3) reachable_node_is_node by metis
  have "acyclic (from_FSM M q)"
    using from_FSM_acyclic[OF assms(3,1)] by assumption

  have *: "(\<And>q'. q' \<in> reachable_nodes (FSM.from_FSM M q) \<Longrightarrow> q' = qd \<or> \<not> deadlock_state (FSM.from_FSM M q) q')"
    using assms(2) from_FSM_reachable_nodes[OF assms(3)] 
    unfolding deadlock_state.simps from_FSM_simps[OF \<open>q \<in> nodes M\<close>] by blast

  obtain p where "path (from_FSM M q) q p" and "target q p = qd"
    using acyclic_single_deadlock_reachable[OF \<open>acyclic (from_FSM M q)\<close> *]
    unfolding reachable_nodes_def from_FSM_simps[OF \<open>q \<in> nodes M\<close>]
    by blast 

  then show ?thesis
    using that by (metis \<open>q \<in> FSM.nodes M\<close> from_FSM_path) 
qed




(* if q0 can be added, it will be added *)
lemma d_states'_q0_containment :
  assumes "f (q0,x) \<noteq> {}"
  and     "(\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))"   
  and     "x \<in> set iL"
shows "(\<exists> qx \<in> set (d_states' f q q0 iL nL nS k m) . fst qx = q0)" 
proof -
  have "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL \<noteq> None"
    using assms unfolding find_None_iff by blast
  then obtain x' where *: "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL = Some x'"
    by auto
  show ?thesis 
    unfolding d_states'_helper1[OF *] by auto
qed


(*
lemma x :
  assumes "t \<in> transitions M"
  and     "t_source t \<in> reachable_nodes M"
  and     "q \<noteq> t_target t"
shows "\<exists> q (d_states (FSM.from_FSM M (t_target t)) (size_r (FSM.from_FSM M (t_target t)) - 1) q)
*)


lemma x :
  assumes "\<not> (\<exists> qx \<in> set (d_states' f q q0 iL nL nS k m) . fst qx = q0)"
  and     "q0 \<noteq> q"
  and     "q0 \<notin> nS"
  and     "q0 \<notin> set nL"
shows "(d_states' f q q0 iL nL nS k m) = (d_states' f q q0 iL (removeAll q0 nL) (nS - {q0}) k m)" 
using assms proof (induction k arbitrary: nL nS m)
  case 0
  then show ?case
    by simp 
next
  case (Suc k)
  then show ?case
    by auto 
qed












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



(* TODO: study old proof again ... *)

end (*

(* show that the result of finding a preamble does not depend on the ordering of iL, only the kind of preamble depends on the ordering of iL *)
lemma y :
  assumes "set nL1 = nLC \<union> nS1X"
  and     "set nL2 = nLC \<union> nS2X"
  and     "nLC \<inter> nS1X = {}"
  and     "nLC \<inter> nS2X = {}"
  and     "nS1X \<inter> nS2X = {}"
  and     "card nS1X = card nS2X"
  and     "distinct nL1"
  and     "distinct nL2"
  and     "set nL1 \<inter> nS1 = {}"
  and     "set nL2 \<inter> nS2 = {}"
  


  and     "q0 \<noteq> q"
  and     "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "nS = insert q (set (map fst m))"
  and     "distinct nL"
  and     "distinct nLX"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
  
shows "(\<exists> qx \<in> set (d_states' f q q0 iL nL nS k m) . fst qx = q0) = (\<exists> qx \<in> set (d_states' f q q0 iL nLX nS k m) . fst qx = q0)" 


(* show that the result of finding a preamble does not depend on the ordering of iL, only the kind of preamble depends on the ordering of iL *)
lemma y :
  assumes "set nLX = set nL"
 and     "set nL \<inter> nS = {}"
  and     "q0 \<noteq> q"
  and     "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "nS = insert q (set (map fst m))"
  and     "distinct nL"
  and     "distinct nLX"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
  
shows "(\<exists> qx \<in> set (d_states' f q q0 iL nL nS k m) . fst qx = q0) = (\<exists> qx \<in> set (d_states' f q q0 iL nLX nS k m) . fst qx = q0)" 
using assms proof (induction k arbitrary: nL nLX nS m)
  case 0 (* nL not used, identical result *)
  show ?case by auto
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nLX iL = None"
        using \<open>set nLX = set nL\<close> unfolding find_remove_2_None_iff
        by blast 
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
    next
      case (Some a)
      then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      have "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> nS)) nLX iL \<noteq> None"
        unfolding find_remove_2_None_iff
        using find_remove_2_set(1,2,3)[OF *] unfolding \<open>set nLX = set nL\<close>[symmetric] by blast
      then obtain q'X xX nL'X where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nLX iL = Some (q'X,xX,nL'X)"
        by auto

      have "set nL' = set nL'X"
        using find_remove_2_set(4)[OF *] find_remove_2_set(4)[OF **] \<open>distinct nL\<close> \<open>distinct nLX\<close>

      thm Suc.IH
      then show ?thesis sorry
    qed
  next
    case (Some a)
    show ?thesis unfolding d_states'_helper1[OF Some] by auto
  qed
qed
proof (cases "q' = q")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "False"
        unfolding find_remove_2_None_iff 
        using \<open>q' \<in> set nL\<close> \<open>x \<in> set iL\<close> \<open>f (q',x) \<noteq> {}\<close> \<open>(\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))\<close> by blast
      then show ?thesis by simp
    next
      case (Some a)
      then show ?thesis sorry
    qed
    
  next
    case (Some a)
    show ?thesis unfolding d_states'_helper1[OF Some] by auto
  qed
qed


end (*

lemma x :
  assumes "f (q',x) \<noteq> {}"
  and     "q' \<in> set nL"
  and     "x \<in> set iL"
  and     "(\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))"
  and     "\<And> y q'' . q'' = q \<or> (\<exists> qx \<in> set (d_states' f q'' q0 iL (removeAll q'' nL) (insert q'' nS) k (m@[(q',x)])) . fst qx = q0)"  
  and     "set nL \<inter> nS = {}"
  and     "q0 \<noteq> q"
  and     "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "nS = insert q (set (map fst m))"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"

  and     "q0 \<notin> set (map fst m)"
  
shows "q' = q \<or> (\<exists> qx \<in> set (d_states' f q q0 iL nL nS (Suc k) m) . fst qx = q0)" 
proof (cases "q' = q")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "False"
        unfolding find_remove_2_None_iff 
        using \<open>q' \<in> set nL\<close> \<open>x \<in> set iL\<close> \<open>f (q',x) \<noteq> {}\<close> \<open>(\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))\<close> by blast
      then show ?thesis by simp
    next
      case (Some a)
      then show ?thesis sorry
    qed
    
  next
    case (Some a)
    show ?thesis unfolding d_states'_helper1[OF Some] by auto
  qed
qed

  


end (*

lemma x :
  assumes "t1 \<in> transitions M"
  assumes "t_source t1 \<in> reachable_nodes M"
  assumes "t2 \<in> transitions M"
  assumes "t_source t2 = t_target t1"
  assumes "q \<noteq> t_source t1"
  assumes "\<And> t . t \<in> transitions M \<Longrightarrow> t_input t \<in> inputs M"
  assumes "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
                        t_source t = t_source t2 \<Longrightarrow>
                        t_input t = t_input t2 \<Longrightarrow>
                        t_target t = q \<or>
                        (\<exists>qx\<in>set (d_states (FSM.from_FSM M (t_source t)) (size_r (FSM.from_FSM M (t_source t)) - 1) q).
                            fst qx = t_source t)"
and "(d_states (FSM.from_FSM M (t_source t1)) (size_r (FSM.from_FSM M (t_source t1)) - 1) q) = T"
  shows "t_target t1 = q \<or> (\<exists>qx\<in>set (d_states (FSM.from_FSM M (t_source t1)) (size_r (FSM.from_FSM M (t_source t1)) - 1) q). fst qx = t_source t1)"  
  nitpick
proof (cases "t_target tS = q")
  case True
  then show ?thesis by auto
next
  case False

  then have 

  

  then show ?thesis sorry
qed
  
  


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





subsection \<open>Minimal Sequences to Failures extending Preambles\<close>



definition sequence_to_failure_extending_preamble :: "('a,'b,'c) fsm \<Rightarrow> 'c FSM \<Rightarrow> ('a \<Rightarrow> ('a,'b,'c) fsm option) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "sequence_to_failure_extending_preamble M M' PS io = (\<exists> q \<in> nodes M . \<exists> P p . PS q = Some P
                                                                                  \<and> path P (initial P) p 
                                                                                  \<and> target p (initial P) = q
                                                                                  \<and> ((p_io p) @ butlast io) \<in> L M   
                                                                                  \<and> ((p_io p) @ io) \<notin> L M
                                                                                  \<and> ((p_io p) @ io) \<in> L M')"

end (* lemma sequence_to_failure_extending_preamble_ex :
  assumes "PS (initial M) = Some \<lparr> initial = initial M,
                                   inputs = inputs M,
                                   outputs = outputs M,
                                   transitions = [],
                                   \<dots> = more M \<rparr>" (is "PS (initial M) = Some ?P")
  and     "\<not> L M' \<subseteq> L M"
obtains io where "sequence_to_failure_extending_preamble M M' PS io"
proof -
  obtain io where "io \<in> L M' - L M"
    using \<open>\<not> L M' \<subseteq> L M\<close> by auto
  
  obtain j where "take j io \<in> L M" and "take (Suc j) io \<notin> L M" 
  proof -
    have "\<exists> j . take j io \<in> L M \<and> take (Suc j) io \<notin> L M"
    proof (rule ccontr)
      assume "\<nexists>j. take j io \<in> LS M (initial M) \<and> take (Suc j) io \<notin> LS M (initial M)"
      then have *: "\<And> j . take j io \<in> LS M (initial M) \<Longrightarrow> take (Suc j) io \<in> LS M (initial M)" by blast
      
      have "\<And> j . take j io \<in> LS M (initial M)"
      proof -
        fix j 
        show "take j io \<in> LS M (initial M)"
          using * by (induction j; auto)
      qed
      then have "take (length io) io \<in> L M" by blast
      then show "False"
        using \<open>io \<in> L M' - L M\<close> by auto
    qed
    then show ?thesis using that by blast
  qed

  have "\<And> i . take i io \<in> L M'" 
  proof -
    fix i show "take i io \<in> L M'" using \<open>io \<in> L M' - L M\<close> language_prefix[of "take i io" "drop i io" M' "initial M'"] by auto
  qed

  let ?io = "take (Suc j) io"
  

  have "initial M \<in> nodes M" by auto
  moreover have "PS (initial M) = Some ?P" using assms by auto
  moreover have "path ?P (initial ?P) []" by force
  moreover have "((p_io []) @ butlast ?io) \<in> L M" using \<open>take j io \<in> L M\<close>  unfolding List.list.map(1) append_Nil 
    by (metis Diff_iff One_nat_def \<open>io \<in> LS M' (initial M') - LS M (initial M)\<close> butlast_take diff_Suc_Suc minus_nat.diff_0 not_less_eq_eq take_all)
  moreover have "((p_io []) @ ?io) \<notin> L M" using \<open>take (Suc j) io \<notin> L M\<close> by auto
  moreover have "((p_io []) @ ?io) \<in> L M'" using \<open>\<And> i . take i io \<in> L M'\<close> by auto
  ultimately have "sequence_to_failure_extending_preamble M M' PS ?io"
    unfolding sequence_to_failure_extending_preamble_def by force
  then show ?thesis using that by blast
qed
  
    
  


definition minimal_sequence_to_failure_extending_preamble :: "('a,'b,'c) fsm \<Rightarrow> 'c FSM \<Rightarrow> ('a \<Rightarrow> ('a,'b,'c) fsm option) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "minimal_sequence_to_failure_extending_preamble M M' PS io = ((sequence_to_failure_extending_preamble M M' PS io)
                                                                \<and> (\<forall> io' . sequence_to_failure_extending_preamble M M' PS io' \<longrightarrow> length io \<le> length io'))"

end (* lemma minimal_sequence_to_failure_extending_preamble_ex :
  assumes "PS (initial M) = Some \<lparr> initial = initial M,
                                   inputs = inputs M,
                                   outputs = outputs M,
                                   transitions = [],
                                   \<dots> = more M \<rparr>" (is "PS (initial M) = Some ?P")
  and     "\<not> L M' \<subseteq> L M"
obtains io where "minimal_sequence_to_failure_extending_preamble M M' PS io"
proof -
  let ?ios = "{io . sequence_to_failure_extending_preamble M M' PS io}"
  let ?io_min = "arg_min length (\<lambda>io . io \<in> ?ios)"


  have "?ios \<noteq> {}"
    using sequence_to_failure_extending_preamble_ex[of PS M M', OF assms] by blast
  then have "?io_min \<in> ?ios \<and> (\<forall> io' \<in> ?ios . length ?io_min \<le> length io')"
    by (meson arg_min_nat_end (* lemma some_in_eq)
  then show ?thesis
    unfolding minimal_sequence_to_failure_extending_preamble_def 
    by (simp add: minimal_sequence_to_failure_extending_preamble_def that)
qed
    
    

end