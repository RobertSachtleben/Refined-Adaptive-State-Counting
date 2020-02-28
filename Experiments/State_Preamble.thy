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
    \<and> q \<in> nodes S 
    \<and> deadlock_state S q 
    \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S))))"

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
  unfolding is_preamble_def deadlock_state.simps initial_preamble_simps
  by (metis acyclic_code bot.extremum empty_iff fsm_initial initial_preamble_simps(2) initial_preamble_simps(3) initial_preamble_simps(4) initial_preamble_simps(5) insert_subset is_submachine.elims(3) single_input.elims(3) singletonD) 
 

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
  and  "q \<in> nodes S"
  and  "deadlock_state S q" 
  and  *: "(\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> inputs M . (\<exists> t \<in> transitions S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> transitions M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> transitions S)))"
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


  have contains_q : "q \<in> nodes ?S"
  proof -
    obtain qd where "qd \<in> nodes ?S" and "deadlock_state ?S qd"
      using is_acyclic
      using acyclic_deadlock_states by blast 
    then have "qd \<in> nodes S"
      by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>) 
    then have "deadlock_state S qd"
      using \<open>deadlock_state ?S qd\<close> unfolding deadlock_state.simps
      using \<open>qd \<in> nodes ?S\<close>
      by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    then have "qd = q"
      using * \<open>qd \<in> nodes S\<close> by fastforce 
    then show ?thesis 
      using \<open>qd \<in> nodes ?S\<close> by auto
  qed
  
  have has_deadlock_q : "deadlock_state ?S q"
    using *
    by (metis \<open>deadlock_state S q\<close> \<open>t_target t \<in> FSM.nodes S\<close> deadlock_state.simps from_FSM_simps(4))


  have has_nodes_prop_1: "\<And> q' . q' \<in> nodes ?S \<Longrightarrow> deadlock_state ?S q' \<Longrightarrow> q = q'"
  proof -
    fix q' assume "q' \<in> nodes ?S" and "deadlock_state ?S q'"
    then have "q' \<in> nodes S" 
      by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    then have "deadlock_state S q'"
      using \<open>deadlock_state ?S q'\<close> unfolding deadlock_state.simps
      using \<open>q' \<in> nodes ?S\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    then show "q = q'"
      using * \<open>q' \<in> nodes S\<close> by fastforce 
  qed

  moreover have has_nodes_prop_2: "\<And> x t t' q' .
    t \<in> transitions ?S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
    t' \<in> transitions ?M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions ?S"
  proof -
    fix x tS tM q' assume "tS \<in> transitions ?S" and "t_source tS = q'" and "t_input tS = x" and "tM \<in> transitions ?M" and "t_source tM = q'" and "t_input tM = x"

    have "tS \<in> transitions S"
      using \<open>tS \<in> transitions ?S\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    have "tM \<in> transitions M"
      using \<open>tM \<in> transitions ?M\<close>
      using \<open>t_target t \<in> FSM.nodes M\<close> by (simp add: \<open>t_target t \<in> FSM.nodes S\<close>)
    have "t_source tS \<in> nodes (from_FSM S (t_target t))"
      using \<open>tS \<in> transitions ?S\<close> by auto
    have "t_source tM \<in> nodes (from_FSM M (t_target t))"
      using \<open>tM \<in> transitions ?M\<close> by auto

    show "tM \<in> transitions ?S"
      using "*" \<open>tM \<in> FSM.transitions M\<close> \<open>tS \<in> FSM.transitions S\<close> \<open>t_input tM = x\<close> \<open>t_input tS = x\<close> \<open>t_source tM = q'\<close> \<open>t_source tS = q'\<close> \<open>t_source tS \<in> FSM.nodes (FSM.from_FSM S (t_target t))\<close> \<open>t_target t \<in> FSM.nodes S\<close> by auto
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




(* TODO: rework, if necessary require nodes and inputs to be of a linorder type to allow reusing at least some part of d_states *)                            

fun d_states' :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> (('a \<times> 'b) list \<times> 'a list \<times> 'a set \<times> nat)" where
  "d_states' f q nodeList inputList 0 = ([], removeAll q nodeList, {q}, 0)" |
  "d_states' f q nodeList inputList (Suc k) = (case d_states' f q nodeList inputList k
    of (m', u', v', k') \<Rightarrow> 
      (if k' < k 
        then (m', u', v', k')
        else case find_remove_2 (\<lambda> q' x . q' \<notin> v' \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' = q \<or> q'' \<in> v'))) u' inputList
          of None            \<Rightarrow> (m', u', v', k') |
             Some (q',x,u'') \<Rightarrow> (m'@[(q',x)], u'', insert q' v', Suc k')))"

value "d_states' (h m_ex_H) 1 (nodes_as_list m_ex_H) (inputs_as_list m_ex_H) 5" 
value "d_states' (h m_ex_H) 2 (nodes_as_list m_ex_H) (inputs_as_list m_ex_H) 5" 
value "d_states' (h m_ex_H) 3 (nodes_as_list m_ex_H) (inputs_as_list m_ex_H) 5" 
value "d_states' (h m_ex_H) 4 (nodes_as_list m_ex_H) (inputs_as_list m_ex_H) 5" 

value "d_states' (h m_ex_DR) 400 (nodes_as_list m_ex_DR) (inputs_as_list m_ex_DR) 100"


fun d_states :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "d_states M k q = fst (d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k)"






(* TODO: rework with better assumptions *)

lemma d_states'_props :
  assumes "(m,u,v,k') = d_states' f q nodeList inputList k"
shows "k' = length m"
and   "k' \<le> k"
and   "q \<in> set nodeList \<Longrightarrow> insert q (set (map fst m)) = v"
and   "q \<in> set nodeList \<Longrightarrow> set (map snd m) \<subseteq> set inputList"
and   "q \<in> set nodeList \<Longrightarrow> q \<in> v"
and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> set u \<inter> v = {}"
and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> set u \<union> v = set nodeList"
and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> distinct (map fst m)"
and   "distinct nodeList \<Longrightarrow> distinct u"
proof -
  have "k' = length m 
        \<and> (q \<in> set nodeList \<longrightarrow> insert q (set (map fst m)) = v)
        \<and> (q \<in> set nodeList \<longrightarrow> set (map snd m) \<subseteq> set inputList)
        \<and> (q \<in> set nodeList \<longrightarrow> q \<in> v)
        \<and> (q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<inter> v = {})
        \<and> (q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<union> v = set nodeList)
        \<and> (q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> distinct (map fst m))
        \<and> (k' \<le> k) 
        \<and> (distinct nodeList \<longrightarrow> distinct u)"
    using assms(1) proof (induction k arbitrary: m u v k')
    case 0
    moreover have "distinct nodeList \<longrightarrow> distinct (removeAll q nodeList)" 
      by (simp add: distinct_removeAll) 
    ultimately show ?case by auto 
  next
    case (Suc k)

    obtain m' u' v' k'' where *: "(m',u',v',k'') = d_states' f q nodeList inputList k"
      by (metis prod_cases4) 
      

    show ?case proof (cases "k'' < k \<or> find_remove_2 (\<lambda> q' x . q' \<notin> v' \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' = q \<or> q'' \<in> v'))) u' inputList = None")
      case True
      then have "(m, u, v, k') = (m',u',v',k'')"
        using Suc.prems unfolding d_states'.simps unfolding *[symmetric] by auto
      then show ?thesis 
        using Suc.IH[OF \<open>(m',u',v',k'') = d_states' f q nodeList inputList k\<close>] by auto
    next
      case False
      then obtain q' x u'' where **: "find_remove_2 (\<lambda> q' x . q' \<notin> v' \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' = q \<or> q'' \<in> v'))) u' inputList = Some (q', x, u'')"
        by auto
      then have ***: "(m, u, v, k') = (m' @ [(q', x)], u'', insert q' v', Suc k'')"
        using Suc.prems False unfolding d_states'.simps unfolding *[symmetric] by auto
      then have "m = m' @ [(q', x)]" by auto

      have "k' = length m" 
      and  "q \<in> set nodeList \<longrightarrow> insert q (set (map fst m)) = v"
      and  "q \<in> set nodeList \<longrightarrow> set (map snd m) \<subseteq> set inputList"
      and  "q \<in> set nodeList \<longrightarrow> q \<in> v" 
        using ***  Suc.IH[OF *] find_remove_2_set[OF **] by auto
      moreover have "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<inter> v = {})"
               and  "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<union> v = set nodeList)" 
               and  "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> distinct (map fst m))"
               and  "(k' \<le> Suc k)" 
               and  "(distinct nodeList \<longrightarrow> distinct u)"
      proof -
        have "u = u''" and "v = insert q' v'" and "k' = Suc k''" using *** by auto
        moreover have "k'' = length m'" and "q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u' \<inter> v' = {}" 
                  and "(q \<in> set nodeList \<longrightarrow> insert q (set (map fst m')) = v')"
                  and "q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u' \<union> v' = set nodeList" 
                  and "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> distinct (map fst m'))"
                  and "(k'' \<le> k)"
                  and "distinct nodeList \<longrightarrow> distinct u'" 
          using Suc.IH[OF *] by auto
        moreover have "q' \<in> set u'" 
                  and "distinct nodeList \<longrightarrow> set u'' = set u' - {q'}" 
                  and "distinct nodeList \<longrightarrow> distinct u''" 
          using find_remove_2_set[OF **] \<open>distinct nodeList \<longrightarrow> distinct u'\<close> by auto

        show "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<inter> v = {})"
          using \<open>q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u' \<inter> v' = {}\<close> \<open>q' \<in> set u'\<close> \<open>distinct nodeList \<longrightarrow> set u'' = set u' - {q'}\<close>
          unfolding \<open>u = u''\<close> \<open>v = insert q' v'\<close> by force
        show "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u \<union> v = set nodeList)"
          using \<open>q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u' \<union> v' = set nodeList\<close> \<open>q' \<in> set u'\<close> \<open>distinct nodeList \<longrightarrow> set u'' = set u' - {q'}\<close>
          unfolding \<open>u = u''\<close> \<open>v = insert q' v'\<close> by force

        show "(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> distinct (map fst m))"
          using \<open>(q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> distinct (map fst m'))\<close> \<open>q' \<in> set u'\<close>
                \<open>q \<in> set nodeList \<longrightarrow> distinct nodeList \<longrightarrow> set u' \<inter> v' = {}\<close> 
                \<open>q \<in> set nodeList \<longrightarrow> insert q (set (map fst m')) = v'\<close> 
          unfolding \<open>m = m' @ [(q', x)]\<close> by auto 

        show "(k' \<le> Suc k)"
          using \<open>(k'' \<le> k)\<close>
          unfolding \<open>k' = Suc k''\<close> \<open>k'' = length m'\<close>  by blast

        show "distinct nodeList \<longrightarrow> distinct u"
          using \<open>distinct nodeList \<longrightarrow> distinct u'\<close>
          using \<open>distinct nodeList \<longrightarrow> distinct u''\<close> unfolding \<open>u = u''\<close> by blast 
      qed
  
      ultimately show ?thesis by blast
    qed
  qed
  then show "k' = length m"
      and   "k' \<le> k"
      and   "q \<in> set nodeList \<Longrightarrow> insert q (set (map fst m)) = v"
      and   "q \<in> set nodeList \<Longrightarrow> set (map snd m) \<subseteq> set inputList"
      and   "q \<in> set nodeList \<Longrightarrow> q \<in> v"
      and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> set u \<inter> v = {}"
      and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> set u \<union> v = set nodeList"
      and   "q \<in> set nodeList \<Longrightarrow> distinct nodeList \<Longrightarrow> distinct (map fst m)"
      and   "distinct nodeList \<Longrightarrow> distinct u"
    by simp+    
qed


  
lemma d_states'_length :
  "length (fst (d_states' f q nodeList inputList k)) \<le> k"
  using d_states'_props(1,2) by (metis prod.exhaust prod.sel(1))

lemma d_states'_length_elem :
  "length (fst (d_states' f q nodeList inputList k)) = snd (snd ((snd (d_states' f q nodeList inputList k))))"
  using d_states'_props(1) by (metis prod.exhaust prod.sel)


lemma d_states_length :
  "length ((d_states M k q)) \<le> k"
  unfolding d_states.simps using d_states'_props(1,2) by (metis prod.exhaust prod.sel(1)) 


lemma d_states'_prefix :
  assumes "i \<le> k"
  shows "take i (fst (d_states' f q nL iL k)) = fst (d_states' f q nL iL i)"
using assms proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)

  obtain m v u k' where "d_states' f q nL iL k = (m,u,v,k')"
    using prod_cases4 by blast
  then have "fst (d_states' f q nL iL k) = m" by simp
  
  have "k' = length m" and "k' \<le> k"
    using d_states'_props(1,2)[OF \<open>d_states' f q nL iL k = (m,u,v,k')\<close>[symmetric]] by simp+


  obtain mi vi ui ki' where "d_states' f q nL iL i = (mi,ui,vi,ki')"
    using prod_cases4 by blast
  then have "fst (d_states' f q nL iL i) = mi" by simp
  
  have "ki' = length mi" and "ki' \<le> i"
    using d_states'_props(1,2)[OF \<open>d_states' f q nL iL i = (mi,ui,vi,ki')\<close>[symmetric]] by simp+
    

  from Suc consider (a) "i \<le> k" | (b) "i = Suc k"
    using le_SucE by blast 
  then show ?case proof cases
    case a
    show ?thesis proof (cases "length (fst (d_states' f q nL iL k)) < k")
      case True
      then show ?thesis using Suc.IH[OF a] unfolding d_states'.simps
        by (simp add: \<open>d_states' f q nL iL k = (m, u, v, k')\<close> \<open>k' = length m\<close>)
    next
      case False      
      then have *: "(d_states' f q nL iL (Suc k)) = 
          (case find_remove_2 (\<lambda> q' x . q' \<notin> v \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' = q \<or> q'' \<in> v))) u iL
          of None            \<Rightarrow> (m, u, v, k') |
             Some (q',x,u'') \<Rightarrow> (m@[(q',x)], u'', insert q' v, Suc k'))"
        unfolding d_states'.simps
        unfolding d_states'_length_elem[of] 
        unfolding \<open>d_states' f q nL iL k = (m,u,v,k')\<close> snd_conv by auto
      
      then consider (a1) "(d_states' f q nL iL (Suc k)) = (d_states' f q nL iL k)" |
                    (a2) "\<exists> q' x u'' . (d_states' f q nL iL (Suc k)) = (m@[(q',x)], u'', insert q' v, Suc k')"  
        unfolding \<open>d_states' f q nL iL k = (m,u,v,k')\<close> 
        by (cases "find_remove_2 (\<lambda> q' x . q' \<notin> v \<and> f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' = q \<or> q'' \<in> v))) u iL"; auto) 
      then show ?thesis proof cases
        case a1
        then show ?thesis using Suc.IH[OF a] by simp
      next
        case a2
        then show ?thesis using Suc.IH[OF a] using False a 
          unfolding \<open>d_states' f q nL iL k = (m,u,v,k')\<close> fst_conv
          using Suc_less_eq d_states'_length by auto
      qed
    qed
  next
    case b
    then show ?thesis
      using \<open>fst (d_states' f q nL iL i) = mi\<close> \<open>ki' = length mi\<close> \<open>ki' \<le> i\<close> take_all by blast 
  qed
qed


lemma d_states_prefix :
  assumes "i \<le> k"
  shows "take i (d_states M k q) = d_states M i q"
  unfolding d_states.simps d_states'_prefix[OF assms] by simp


lemma d_states_self_length :
  "d_states M k q = d_states M (length (d_states M k q)) q" 
  using d_states_prefix 
  by (metis (no_types) nat_le_linear d_states_length d_states_prefix take_all)


lemma case_case_fun: 
  "(case (a, b, c, d) of (a', b', c', d') \<Rightarrow> f a' b' c' d') = f a b c d"
  by auto

lemma d_states_case_helper :
  assumes "fst (if P1 then (xs,a1,a2,a3) else (case P2 of None \<Rightarrow> (xs,a1,a2,a3) | Some (q,x,u) \<Rightarrow> (xs@[(q,x)], f1 (q,x,u), f2 (q,x,u), f3 (q,x,u)))) = xs@[(q,x)]" 
  shows   "\<exists> u . P2 = Some (q,x,u)"
proof (cases P1)
  case True
  then have "fst (if P1 then (xs,a1,a2,a3) else (case P2 of None \<Rightarrow> (xs,a1,a2,a3) | Some (q,x,u) \<Rightarrow> (xs@[(q,x)], f1 (q,x,u), f2 (q,x,u), f3 (q,x,u)))) = xs" by auto
  then show ?thesis using assms by auto
next
  case False
  then show ?thesis proof (cases P2)
    case None
    then have "fst (if P1 then (xs,a1,a2,a3) else (case P2 of None \<Rightarrow> (xs,a1,a2,a3) | Some (q,x,u) \<Rightarrow> (xs@[(q,x)], f1 (q,x,u), f2 (q,x,u), f3 (q,x,u)))) = xs" by auto
    then show ?thesis using assms by auto
  next
    case (Some a)
    then obtain q' x' u' where "P2 = Some (q',x',u')"
      by (metis prod.collapse)
      
    then have "fst (if P1 then (xs,a1,a2,a3) else (case P2 of None \<Rightarrow> (xs,a1,a2,a3) | Some (q,x,u) \<Rightarrow> (xs@[(q,x)], f1 (q,x,u), f2 (q,x,u), f3 (q,x,u)))) = xs@[(q', x')]" 
      using False by force
    then show ?thesis using assms
      by (simp add: \<open>P2 = Some (q', x', u')\<close>) 
  qed 
qed



lemma d_states_index_properties : 
  assumes "i < length (d_states M k q)"
  and     "q \<in> nodes M"
shows "fst (d_states M k q ! i) \<in> nodes M" 
      "fst (d_states M k q ! i) \<noteq> q"
      "snd (d_states M k q ! i) \<in> inputs M"
      "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')" 
      "(\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
proof -
  have combined_properties: "fst (d_states M k q ! i) \<in> nodes M \<and> fst (d_states M k q ! i) \<noteq> q
       \<and> snd (d_states M k q ! i) \<in> inputs M
       \<and> (\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx') 
       \<and> (\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))
       \<and> (\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
    using assms(1) proof (induction k)
    case 0
    then have "i = 0" by auto 
    then have "d_states M 0 q \<noteq> []"
      using 0 by auto
    then show ?case by auto
  next
    case (Suc k)

    obtain m v u k' where "(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')"
      using prod_cases4 by blast


    show ?case proof (cases "i < length (d_states M k q)")
      case True
      then have "d_states M k q ! i = d_states M (Suc k) q ! i"
        using d_states_prefix[of i]
      proof -
        have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
          by (meson Suc_leI)
        then show ?thesis
          by (metis Suc.prems \<open>i < length (d_states M k q)\<close> d_states_prefix d_states_self_length take_last_index)
      qed
      moreover have "take i (d_states M k q) = take i (d_states M (Suc k) q)"
        by (metis Suc.prems Suc_leI less_le_trans nat_less_le not_le d_states_length d_states_prefix)
      ultimately show ?thesis using Suc.IH[OF True] by presburger
    next
      case False
      have "length (d_states M k q) = k"
        by (metis (no_types, lifting) False Suc.prems d_states_prefix length_take min_def_raw nat_le_linear not_less_eq_eq)
      then have "i = length (d_states M k q)"
        by (metis (no_types) False Suc.prems Suc_leI leI less_le_trans nat_less_le d_states_length)
      then have "(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)"
        by (metis Suc.prems \<open>length (d_states M k q) = k\<close> d_states_length take_all take_last_index)
      then have "(d_states M (Suc k) q) = (d_states M k q)@[last (d_states M (Suc k) q)]"
      proof -
        have "i = k"
          using \<open>i = length (d_states M k q)\<close> \<open>length (d_states M k q) = k\<close> by blast
        then show ?thesis
          by (metis Suc.prems Suc_n_not_le_n \<open>d_states M (Suc k) q ! i = last (d_states M (Suc k) q)\<close> nat_le_linear d_states_prefix take_Suc_conv_app_nth)
      qed 
      then obtain q' x where "d_states M (Suc k) q = (d_states M k q)@[(q',x)]"
        by (metis surj_pair)
      then have "d_states M (Suc k) q \<noteq> (d_states M k q)" by auto
      then have "fst (d_states' (h M) q (nodes_as_list M) (inputs_as_list M) (Suc k)) \<noteq> fst (d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k)"
        by auto

      have "\<not> length (d_states M k q) < k"
        using \<open>length (d_states M k q) = k\<close> by simp

      obtain u'' where *: "find_remove_2 (\<lambda>q' x. q' \<notin> v \<and> h M (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (q', x). q'' = q \<or> q'' \<in> v)) u (inputs_as_list M) = Some (q',x,u'')"
        using \<open>d_states M (Suc k) q = (d_states M k q)@[(q',x)]\<close>
        
        unfolding d_states.simps d_states'.simps 
        unfolding \<open>(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')\<close>
        unfolding case_case_fun fst_conv
        using d_states_case_helper[of "k' < k" m u v k' "\<lambda> qxu . snd (snd qxu)" "\<lambda> qxu . insert (fst qxu) v" "\<lambda> qxu . Suc k'" "find_remove_2 (\<lambda>q' x. q' \<notin> v \<and> h M (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (q', x). q'' = q \<or> q'' \<in> v)) u (inputs_as_list M)" q' x]
        unfolding snd_conv fst_conv by blast

      have "q \<in> set (nodes_as_list M)"
        using assms(2) nodes_as_list_set by blast
      
      
      let ?qx = "last (d_states M (Suc k) q)"
      have "?qx = (q',x)" using \<open>d_states M (Suc k) q = (d_states M k q)@[(q',x)]\<close> by auto
      have "q' \<notin> v" and "h M (q', x) \<noteq> {}" and "(\<forall>(y, q'')\<in>h M (q', x). q'' = q \<or> q'' \<in> v)" and "q' \<in> set u" and "x \<in> set (inputs_as_list M)"
        using find_remove_2_set[OF *] by blast+
      
      have "insert q (set (map fst m)) = v"
       and "set (map snd m) \<subseteq> set (inputs_as_list M)"
       and "q \<in> v"
        using d_states'_props(3,4,5)[OF \<open>(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')\<close>[symmetric] \<open>q \<in> set (nodes_as_list M)\<close>] by blast+
      
      have "set u \<inter> v = {}" 
       and "set u \<union> v = set (nodes_as_list M)"
       and "distinct (map fst m)"
        using d_states'_props(6,7,8)[OF \<open>(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')\<close>[symmetric] \<open>q \<in> set (nodes_as_list M)\<close> nodes_as_list_distinct] by blast+

      have "q' \<notin> set (map fst m)"
        using \<open>insert q (set (map fst m)) = v\<close> \<open>q' \<notin> v\<close> by auto
        
      have "take i (d_states M (Suc k) q) = d_states M k q"
        by (metis \<open>d_states M (Suc k) q = d_states M k q @ [last (d_states M (Suc k) q)]\<close> \<open>i = length (d_states M k q)\<close> append_eq_conv_conj)
        

      have "\<And> q'' . q'' \<in> v = (q'' = q \<or> q'' \<in> set (map fst m))"
        unfolding \<open>insert q (set (map fst m)) = v\<close>[symmetric]
        by simp
        



      have "q' \<in> FSM.nodes M"
        using \<open>q' \<in> set u\<close> \<open>set u \<union> v = set (nodes_as_list M)\<close> nodes_as_list_set by auto
      moreover have "q' \<noteq> q" 
        using \<open>q' \<notin> v\<close> \<open>q \<in> v\<close> by blast
      moreover have "x \<in> FSM.inputs M"
        using \<open>x \<in> set (inputs_as_list M)\<close> inputs_as_list_set by blast 
      moreover have "(\<forall>qx'\<in>set (take i (d_states M (Suc k) q)). q' \<noteq> fst qx')" 
        unfolding \<open>d_states M (Suc k) q = (d_states M k q)@[(q',x)]\<close> 
                  \<open>i = length (d_states M k q)\<close> 
                  \<open>length (d_states M k q) = k\<close>
        using     \<open>length (d_states M k q) = k\<close>
        unfolding d_states.simps
                  \<open>(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')\<close> fst_conv
        using \<open>q' \<notin> set (map fst m)\<close>
        by auto 
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x)"
        using \<open>h M (q', x) \<noteq> {}\<close> by fastforce
      moreover have "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow> t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states M (Suc k) q)). fst qx' = t_target t)"
      proof - 
        fix t assume "t \<in> transitions M" and "t_source t = q'" and "t_input t = x"
        then have "(t_output t,t_target t) \<in> h M (q',x)"
          unfolding h.simps by auto
        then have "t_target t = q \<or> t_target t \<in> v"
          using \<open>(\<forall>(y, q'')\<in>h M (q', x). q'' = q \<or> q'' \<in> v)\<close> by blast
        then show "t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states M (Suc k) q)). fst qx' = t_target t)"
          unfolding \<open>take i (d_states M (Suc k) q) = d_states M k q\<close> 
          unfolding d_states.simps \<open>(d_states' (h M) q (nodes_as_list M) (inputs_as_list M) k) = (m,u,v,k')\<close> fst_conv 
          unfolding \<open>\<And> q'' . q'' \<in> v = (q'' = q \<or> q'' \<in> set (map fst m))\<close> by force
      qed
      ultimately show ?thesis
        unfolding \<open>(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)\<close>  \<open>?qx = (q',x)\<close> fst_conv snd_conv by blast
    qed
  qed

  show "fst (d_states M k q ! i) \<in> nodes M" 
       "fst (d_states M k q ! i) \<noteq> q" 
       "snd (d_states M k q ! i) \<in> inputs M"
       "(\<exists> t \<in> transitions M . t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i))"
       "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')" 
       "(\<forall> t \<in> transitions M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
    using combined_properties by presburger+
qed



end (* lemma d_states_distinct_states :
  "distinct (map fst (d_states M k q))" 
proof -
  have "(\<And>i. i < length (map fst (d_states M k q)) \<Longrightarrow>
          map fst (d_states M k q) ! i \<notin> set (take i (map fst (d_states M k q))))"
    using d_states_index_properties(4)[of _ M k]
    by (metis (no_types, lifting) length_map list_map_source_elem nth_map take_map) 
  then show ?thesis
    using list_distinct_prefix[of "map fst (d_states M k q)"] by blast
qed



end (* lemma d_states_nodes : 
  "set (map fst (d_states M k q)) \<subseteq> nodes M"
  using d_states_index_properties(1)[of _ M k]  list_property_from_index_property[of "map fst (d_states M k q)" "\<lambda>q . q \<in> nodes M"]
  by fastforce

end (* lemma d_states_size :
  "length (d_states M k q) \<le> size M"
proof -
  show ?thesis 
    using d_states_nodes[of M k]
          d_states_distinct_states[of M k]
          nodes_finite[of M]
    by (metis card_mono distinct_card length_map size.simps) 
qed
  
end (* lemma d_states_max_iterations :
  assumes "k \<ge> size M"
  shows "d_states M k q = d_states M (size M) q"
  using d_states_size[of M k] d_states_prefix[OF assms, of M]
  by simp 



end (* lemma d_states_by_index :
  assumes "i < length (d_states M k q)"
  shows "(d_states M k q) ! i = last (d_states M (Suc i) q)"
  by (metis Suc_leI assms d_states_prefix d_states_self_length take_last_index) 


end (* lemma d_states_subset :
  "set (d_states M k q) \<subseteq> set (d_states M (Suc k) q)"
  unfolding d_states.simps
  by (simp add: option.case_eq_if subsetI) 

end (* lemma d_states_last :
  assumes "d_states M (Suc k) q \<noteq> d_states M k q"
  shows "\<exists> qx . d_states M (Suc k) q = (d_states M k q)@[qx]
                \<and> fst qx \<noteq> q
                \<and> (\<forall> qx' \<in> set (d_states M k q) . fst qx \<noteq> fst qx') 
                \<and> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) 
                \<and> (\<forall> t \<in> transitions M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M k q) . fst qx' = (t_target t))))
                \<and> fst qx \<in> nodes M
                \<and> snd qx \<in> inputs M"
proof -
  have *: "\<not> (length (d_states M k q) < k)"
    using assms unfolding d_states.simps
    by auto
  have "find
          (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
    using assms unfolding d_states.simps
    by (metis (no_types, lifting) option.simps(4))

  then obtain qx where qx_find: "find
          (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
    by blast

  then have "d_states M (Suc k) q = (d_states M k q)@[qx]"
    using * by auto
  moreover note find_condition[OF qx_find] 
  moreover have "fst qx \<in> nodes M
                \<and> snd qx \<in> inputs M"
    using find_set[OF qx_find]
  proof -
    have "fst qx \<in> set (nodes_from_distinct_paths M) \<and> snd qx \<in> inputs M"
      using \<open>qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))\<close> concat_pair_set by blast
    then show ?thesis
      by (metis (no_types) nodes_code)
  qed 
  ultimately show ?thesis by blast
qed


end (* lemma d_states_transition_target :
  assumes "(t_source t, t_input t) \<in> set (d_states M k q)"
  and     "t \<in> transitions M"
shows "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))"
  and "t_target t \<noteq> t_source t"
proof -
  have "(t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))) \<and> t_target t \<noteq> t_source t"
    using assms(1) proof (induction k)
    case 0 
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "(t_source t, t_input t) \<in> set (d_states M k q)")
      case True
      then have "(t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))) \<and> t_target t \<noteq> t_source t"
        using Suc.IH by auto
      moreover have "set (d_states M (k - 1) q) \<subseteq> set (d_states M (Suc k - 1) q)"
        using d_states_subset
        by (metis Suc_pred' diff_Suc_1 diff_is_0_eq' nat_less_le order_refl zero_le) 
      ultimately show ?thesis by auto
    next
      case False
      then have "set (d_states M k q) \<noteq> set (d_states M (Suc k) q)"
        using Suc.prems by blast
      then have "d_states M (Suc k) q \<noteq> d_states M k q"
        by auto
      
      obtain qx where    "d_states M (Suc k) q = d_states M k q @ [qx]" 
                  and    "fst qx \<noteq> q"
                  and    "(\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx')"
                  and    "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)"
                  and *: "(\<forall>t\<in>set (wf_transitions M).
                         t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                         t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
                  and    "fst qx \<in> nodes M \<and> snd qx \<in> inputs M"
        using d_states_last[OF \<open>d_states M (Suc k) q \<noteq> d_states M k q\<close>] by blast
      
      have "qx = (t_source t, t_input t)"
        using Suc.prems False \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close>
        by auto
      then have "t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)"
        using assms(2) by (simp add: "*")
      then have "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k-1) q))"
        by (metis diff_Suc_1 in_set_zipE prod.collapse zip_map_fst_snd) 
      moreover have \<open>t_target t \<noteq> t_source t\<close>
        using \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> \<open>fst qx \<noteq> q\<close> \<open>qx = (t_source t, t_input t)\<close> \<open>t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)\<close> by auto        
      ultimately show ?thesis by blast
    qed
  qed
  then show "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))"
        and "t_target t \<noteq> t_source t" by simp+
qed



end (* lemma d_states_last_ex :
  assumes "qx1 \<in> set (d_states M k q)"
  shows "\<exists> k' . k' \<le> k \<and> k' > 0 \<and> qx1 \<in> set (d_states M k' q) \<and> qx1 = last (d_states M k' q) \<and> (\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
proof -

  obtain k' where k'_find: "find_index (\<lambda> qqt . qqt = qx1) (d_states M k q) = Some k'"
    using find_index_exhaustive[of "d_states M k q" "(\<lambda> qqt . qqt = qx1)"] assms
    by blast 

  have "Suc k' \<le> k"
    using find_index_index(1)[OF k'_find] d_states_length[of M k q] by presburger
  moreover have "Suc k' > 0" 
    by auto
  moreover have "qx1 \<in> set (d_states M (Suc k') q)"
    using find_index_index(2)[OF k'_find]
    by (metis Suc_neq_Zero \<open>Suc k' \<le> k\<close> assms find_index_index(1) k'_find last_in_set d_states_by_index d_states_prefix take_eq_Nil) 
  moreover have "qx1 = last (d_states M (Suc k') q)"
    by (metis find_index_index(1,2)[OF k'_find] d_states_by_index)
  moreover have "(\<forall> k'' < Suc k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
  proof -
    have "\<And> k'' . k'' < Suc k' \<Longrightarrow> k'' > 0 \<Longrightarrow> qx1 \<noteq> last (d_states M k'' q)" 
    proof -
      fix k'' assume "k'' < Suc k'" and "k'' > 0"
      then have "k'' \<le> k'" by auto
      
      show "qx1 \<noteq> last (d_states M k'' q)" using find_index_index(3)[OF k'_find] d_states_prefix[OF \<open>k'' \<le> k'\<close>]
      proof -
        have f1: "\<forall>n na. \<not> (n::nat) < na \<or> n \<le> na"
          using less_imp_le_nat by satx
        have f2: "k'' \<noteq> 0"
          using \<open>0 < k''\<close> by blast
        obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
          "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
          by moura
        then have "k'' = Suc (nn k' k'') \<and> nn k' k'' < k'"
          using f2 \<open>k'' < Suc k'\<close> less_Suc_eq_0_disj by force
        then show ?thesis
          using f1 by (metis (no_types) \<open>\<And>j. j < k' \<Longrightarrow> d_states M k q ! j \<noteq> qx1\<close> assms d_states_by_index in_set_conv_nth less_le_trans nat_neq_iff)
      qed
    qed
    then show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed



end (* lemma d_states_last_least : 
  assumes "qx1 \<in> set (d_states M k' q)"
  and "qx1 = last (d_states M k' q)"
  and "(\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
shows "(k' = (LEAST k' . qx1 \<in> set (d_states M k' q)))" 
proof (rule ccontr)
  assume "k' \<noteq> (LEAST k'. qx1 \<in> set (d_states M k' q))"
  then obtain k'' where "k'' < k'" and "qx1 \<in> set (d_states M k'' q)"
    by (metis (no_types, lifting) LeastI assms(1) nat_neq_iff not_less_Least)

  obtain k''' where "k''' \<le> k''" and "k'''>0" and "qx1 = last (d_states M k''' q)" and "(\<forall>k''<k'''. 0 < k'' \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
    using d_states_last_ex[OF \<open>qx1 \<in> set (d_states M k'' q)\<close>] by blast

  have "k''' < k'"
    using \<open>k''' \<le> k''\<close> \<open>k'' < k'\<close> by simp

  show "False"
    using assms(3) \<open>k'''>0\<close> \<open>k''' < k'\<close> \<open>qx1 = last (d_states M k''' q)\<close>  by blast
qed




end (* lemma d_states_distinct_least :
  assumes "t \<in> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  shows "(t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
          \<or> (t_target t = q)"
    and "t_source t \<in> set (map fst (d_states M k q))"
proof -
  have "((t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
          \<or> (t_target t = q))
         \<and> t_source t \<in> set (map fst (d_states M k q))"
  using assms proof (induction k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "d_states M (Suc k) q = d_states M k q")
      case True
      then show ?thesis using Suc by auto
    next
      case False
  
      obtain qx where "d_states M (Suc k) q = d_states M k q @ [qx]"
                      "fst qx \<noteq> q"
                      "(\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx')"
                      "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)"
                      "(\<forall>t\<in>set (wf_transitions M).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
                      "fst qx \<in> nodes M \<and> snd qx \<in> inputs M"
        using d_states_last[OF False] by blast
  
      
  
      then show ?thesis proof (cases "t_source t = fst qx")
        case True
  
        
        
        have "fst qx \<notin> set (map fst (d_states M k q))"
          using \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> by auto
        then have "\<And> k' . k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (d_states M k' q))"
          using d_states_prefix[of _ k M]
          by (metis \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> in_set_takeD less_Suc_eq_le list_map_source_elem) 
        moreover have "fst qx \<in> set (map fst (d_states M (Suc k) q))"
          using \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by auto
          
        ultimately have "(LEAST k' . fst qx \<in> set (map fst (d_states M k' q))) = Suc k"
        proof -
          have "\<not> (LEAST n. fst qx \<in> set (map fst (d_states M n q))) < Suc k"
            by (meson LeastI_ex \<open>\<And>k'. k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (d_states M k' q))\<close> \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close>)
          then show ?thesis
            by (meson \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close> not_less_Least not_less_iff_gr_or_eq)
        qed 
  
  
        have "(t_source t, t_input t) \<in> set (d_states M (Suc k) q) \<and> t \<in> set (wf_transitions M)"
          using Suc.prems by auto 
        then have "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k - 1) q))"
          using d_states_transition_target(1)[of t M "Suc k" q] by auto
        then have "t_target t = q \<or> ((LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) \<le> k)"
          by (metis Least_le diff_Suc_1)
          
        then have "t_target t = q \<or> ((LEAST k'. t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k'. t_source t \<in> set (map fst (d_states M k' q))))" 
          using \<open>(LEAST k' . fst qx \<in> set (map fst (d_states M k' q))) = Suc k\<close> True by force
        then show ?thesis
          using \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close> True 
                \<open>t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k - 1) q))\<close>
                \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by auto
      next
        case False
        then show ?thesis
          using Suc.IH Suc.prems \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by fastforce 
      qed
    qed
  qed

  then show "(t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
              \<or> (t_target t = q)"
        and "t_source t \<in> set (map fst (d_states M k q))" by simp+
qed



end (* lemma d_states_q_noncontainment :
  shows "\<not>(\<exists> qqx \<in> set (d_states M k q) . fst qqx = q)" 
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  
  show ?case proof (cases "length (d_states M k q) < k")
    case True
    then show ?thesis unfolding d_states.simps using Suc by auto
  next
    case False

    show ?thesis proof (cases "find
                             (\<lambda>qx. fst qx \<noteq> q \<and>
                                   (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                                   (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                                   (\<forall>t\<in>set (wf_transitions M).
                                       t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                                       t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))
                             (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))")
      case None
      then show ?thesis unfolding d_states.simps using Suc False by auto
    next
      case (Some a)
      then have "(d_states M (Suc k) q) = (d_states M k q)@[a]"
        unfolding d_states.simps using False by auto
      then show ?thesis using Suc find_condition[OF Some] by auto
    qed
  qed  
qed





end (* lemma d_states_induces_state_preamble_helper_distinct_pathlikes :
  assumes "\<And> i . (Suc i) < length (t#p) \<Longrightarrow> t_source ((t#p) ! (Suc i)) = t_target ((t#p) ! i)"
  assumes "set (t#p) \<subseteq> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  
  shows "distinct ((t_source t) # map t_target (t#p))" 
proof - 

  let ?f = "\<lambda> q' . if q' = q then 0 else LEAST k' . q' \<in> set (map fst (d_states M k' q))"
  let ?p = "(t_source t) # map t_target (t#p)"

  have "\<And> t' . t' \<in> set (t#p) \<Longrightarrow> t_source t' \<noteq> q"
    using d_states_q_noncontainment[of M k q] assms(2)
  proof -
    fix t' :: "'a \<times> integer \<times> integer \<times> 'a"
    assume "t' \<in> set (t # p)"
    then have "\<And>P. \<not> set (t # p) \<subseteq> P \<or> t' \<in> P"
      by (metis subset_code(1))
    then have "t' \<in> set (filter (\<lambda>p. \<exists>pa. pa \<in> set (d_states M k q) \<and> t_source p = fst pa \<and> t_input p = snd pa) (wf_transitions M))"
      by (metis (no_types, lifting) assms(2))
    then show "t_source t' \<noteq> q"
      using \<open>\<not> (\<exists>qqx\<in>set (d_states M k q). fst qqx = q)\<close> by auto
  qed 

  have f1: "\<And> i . (Suc i) < length ?p \<Longrightarrow> ?f (?p ! i) > ?f (?p ! (Suc i))"
  proof -
    fix i assume "Suc i < length ?p"
    
    
    let ?t1 = "(t#t#p) ! i"
    let ?t2 = "(t#t#p) ! (Suc i)"

    have "length (t#t#p) = length ?p" by auto
    



    show "?f (?p ! i) > ?f (?p ! (Suc i))" proof (cases i)
      case 0
      then have "?t1 = ?t2"
        by auto

      have "?t1 \<in> transitions M"
        using assms(2) 
        by (metis (no_types, lifting) Suc_lessD \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>length (t # t # p) = length (t_source t # map t_target (t # p))\<close> filter_is_subset list.set_intros(1) nth_mem set_ConsD subsetD)  
      have "?t1 \<in> set (t#t#p)"
        using \<open>length (t#t#p) = length ?p\<close>
              \<open>Suc i < length ?p\<close>
        by (metis Suc_lessD nth_mem)
      have "?t1 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t1 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then consider
          (a) "t_target ?t1 \<in> set (map fst (d_states M k q)) \<and>
                      (LEAST k'. t_target ?t1 \<in> set (map fst (d_states M k' q)))
                      < (LEAST k'. t_source ?t1 \<in> set (map fst (d_states M k' q)))" |
          (b) "t_target ?t1 = q"
          using d_states_distinct_least(1)[of ?t1 M k q] by presburger

      then show ?thesis proof cases
        case a
        moreover have "(t_source t # map t_target (t # p)) ! Suc i \<noteq> q" 
          using 0 assms(2) d_states_q_noncontainment
          using a by fastforce 
        moreover have "(t_source t # map t_target (t # p)) !i \<noteq> q" 
          using 0 assms(2) d_states_q_noncontainment
          using a by fastforce 
        ultimately show ?thesis using \<open>?t1 = ?t2\<close> 0
          by (simp add: "0") 
      next
        case b
        then have "t_target t = q"
          using 0 by auto
        then have "?f (?p ! (Suc i)) = 0" using 0 by auto
        
        have "?p ! i \<in> set (map fst (d_states M k q))"
          using assms(2) 0 by auto
        have "?p ! i \<notin> set (map fst (d_states M 0 q))"
          by auto
        have "(LEAST k'. ?p ! i \<in> set (map fst (d_states M k' q))) > 0"
          by (metis (no_types) LeastI_ex \<open>(t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k q))\<close> \<open>(t_source t # map t_target (t # p)) ! i \<notin> set (map fst (d_states M 0 q))\<close> neq0_conv)
        moreover have "?p ! i \<noteq> q"
          using assms(2) d_states_q_noncontainment 0 by force
        ultimately have "?f (?p ! i) > 0" by auto
          

        then show ?thesis 
          using \<open>?f (?p ! (Suc i)) = 0\<close> by auto 
      qed 
        
    next
      case (Suc m)

      have "?t2 \<in> set (t#t#p)"
        using \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (metis nth_mem) 
      
      have "?t2 \<in> transitions M"
        using assms(2) using \<open>(t#t#p) ! (Suc i) \<in> set (t#t#p)\<close> by auto 
  
      have "?t2 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t2 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then consider
        (a) "t_target ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k q)) \<and> 
              (LEAST k'. t_target ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k' q)))
                < (LEAST k'. t_source ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k' q)))" |
        (b) "t_target ((t # t # p) ! Suc i) = q"
        using d_states_distinct_least(1)[of ?t2 M k q] by presburger

      then show ?thesis proof cases
        case a

        have "t_source ?t2 = t_target ?t1"
        using assms(1) \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (simp add: Suc) 

        then have " t_target ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! Suc i"
          by (metis Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> length_Cons length_map nth_Cons_Suc nth_map)
        moreover have "t_source ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! i"
          by (metis Suc Suc_lessD Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>t_source ((t # t # p) ! Suc i) = t_target ((t # t # p) ! i)\<close> length_Cons length_map nth_Cons_Suc nth_map)  
        moreover have "(t_source t # map t_target (t # p)) ! Suc i \<noteq> q"
          using a d_states_q_noncontainment
          using calculation(1) by fastforce 
        moreover have "(t_source t # map t_target (t # p)) ! i \<noteq> q"
          by (metis \<open>(t # t # p) ! Suc i \<in> set (t # t # p)\<close> \<open>\<And>t'. t' \<in> set (t # p) \<Longrightarrow> t_source t' \<noteq> q\<close> calculation(2) list.set_intros(1) set_ConsD)
        ultimately show "?f (?p ! i) > ?f (?p ! (Suc i))" 
          using a by simp
      next
        case b 


        then have "?f (?p ! (Suc i)) = 0" using Suc
          using \<open>Suc i < length (t_source t # map t_target (t # p))\<close> by auto 

        have "?p ! i = t_target ((t#p) ! (i - 1))"
          using Suc \<open>Suc i < length ?p\<close>
          by (metis Suc_lessD Suc_less_eq diff_Suc_1 length_Cons length_map nth_Cons_Suc nth_map) 
        then have "?p ! i = t_source ((t#p) ! i)"
          using Suc assms(1)
          using \<open>Suc i < length (t_source t # map t_target (t # p))\<close> by auto 
        then have "?p ! i \<in> set (map fst (d_states M k q))"
          using assms(2)
          using \<open>(t # t # p) ! Suc i \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))\<close> by auto 
        have "?p ! i \<notin> set (map fst (d_states M 0 q))"
          by auto
        have "(LEAST k'. ?p ! i \<in> set (map fst (d_states M k' q))) > 0"
          by (metis (no_types) LeastI_ex \<open>(t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k q))\<close> \<open>(t_source t # map t_target (t # p)) ! i \<notin> set (map fst (d_states M 0 q))\<close> neq0_conv)
        moreover have "?p ! i \<noteq> q"
          using \<open>(t # t # p) ! Suc i \<in> set (t # t # p)\<close> \<open>(t_source t # map t_target (t # p)) ! i = t_source ((t # p) ! i)\<close> \<open>\<And>t'. t' \<in> set (t # p) \<Longrightarrow> t_source t' \<noteq> q\<close> by auto 
        ultimately have "?f (?p ! i) > 0" by auto

        then show ?thesis 
          using \<open>?f (?p ! (Suc i)) = 0\<close> by auto 
      qed 
    qed
  qed


  moreover have f2: "\<And> i . i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! i = (if (t_source t # map t_target (t # p)) ! i = q then 0 else LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k' q)))"
  proof -
    fix i assume "i < length (map ?f ?p)"
    have map_index : "\<And> xs f i . i < length (map f xs) \<Longrightarrow> (map f xs) ! i = f (xs ! i)"
      by simp
    show "map ?f ?p ! i = (if (t_source t # map t_target (t # p)) ! i = q then 0 else LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k' q)))"
      using map_index[OF \<open>i < length (map ?f ?p)\<close>] by assumption
  qed

  ultimately have "(\<And>i. Suc i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! Suc i < map ?f ?p ! i)"
  proof -
    fix i assume "Suc i < length (map ?f ?p)"
    then have "Suc i < length ?p" 
              "i < length (map ?f ?p)"
              "i < length ?p"
       by auto

    note f2[OF \<open>Suc i < length (map ?f ?p)\<close>] 
    moreover note f2[OF \<open>i < length (map ?f ?p)\<close>]
    moreover note f1[OF \<open>Suc i < length ?p\<close>]
    ultimately show "map ?f ?p ! Suc i < map ?f ?p ! i"
      by linarith
  qed

  then have "distinct (map ?f ?p)"
    using ordered_list_distinct_rev[of "map ?f ?p"] by blast

  then show "distinct ?p"
    using distinct_map[of ?f ?p] by linarith
qed


end (* lemma d_states_induces_state_preamble_helper_distinct_paths :
  assumes "path  \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>
                 q'
                 p"
    (is "path ?S q' p")
  shows "distinct (visited_states q' p)" 
proof (cases p)
  case Nil
  then show ?thesis by auto
next
  case (Cons t p')

  then have *: "\<And> i . (Suc i) < length (t#p') \<Longrightarrow> t_source ((t#p') ! (Suc i)) = t_target ((t#p') ! i)"
    using assms(1) by (simp add: path_source_target_index) 
  
  have "set (t#p') \<subseteq> set (transitions ?S)"
    using Cons path_h[OF assms(1)] unfolding wf_transitions.simps 
    by (meson filter_is_subset subset_code(1)) 
  then have **: "set (t#p') \<subseteq> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                      (wf_transitions M))"
    by simp

  have "distinct (t_source t # map t_target (t # p'))"
    using d_states_induces_state_preamble_helper_distinct_pathlikes[OF * **]
    by auto
  moreover have "visited_states q' p = (t_source t # map t_target (t # p'))"
    using Cons assms(1) unfolding visited_states.simps target.simps
    by blast 
  ultimately show "distinct (visited_states q' p)"
    by auto
qed
  

end (* lemma d_states_induces_state_preamble_helper_acyclic :
  shows "acyclic \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>"
    (is "acyclic ?S")

proof -
  have "\<And> p . path ?S (initial ?S) p \<Longrightarrow> distinct (visited_states (initial ?S) p)"
  proof -
    fix p assume "path ?S (initial ?S) p"
    show "distinct (visited_states (initial ?S) p)"
      using d_states_induces_state_preamble_helper_distinct_paths[OF \<open>path ?S (initial ?S) p\<close>] by assumption
  qed
  then show ?thesis unfolding acyclic.simps by blast
qed


end (* lemma d_states_induces_state_preamble_helper_h :
  assumes "t \<in> transitions \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>"
  shows "(t_source t, t_input t) \<in> set (d_states M k q)" 
  using assms by force

end (* lemma d_states_induces_state_preamble_helper_single_input :
  "single_input \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>"
  (is "single_input ?S")
proof -
  have "\<And> t1 t2 . t1 \<in> transitions ?S \<Longrightarrow> t2 \<in> transitions ?S \<Longrightarrow> t_source t1 = t_source t2 \<Longrightarrow> t_input t1 = t_input t2"
  proof -
    fix t1 t2 assume "t1 \<in> transitions ?S"
                 and "t2 \<in> transitions ?S"
                 and "t_source t1 = t_source t2"

    have "(t_source t1, t_input t1) \<in> set (d_states M k q)"
      using d_states_induces_state_preamble_helper_h[OF \<open>t1 \<in> transitions ?S\<close>] by assumption
    moreover have "(t_source t1, t_input t2) \<in> set (d_states M k q)"
      using d_states_induces_state_preamble_helper_h[OF \<open>t2 \<in> transitions ?S\<close>] \<open>t_source t1 = t_source t2\<close> by auto
    ultimately show "t_input t1 = t_input t2"
      using d_states_distinct_states[of M k q]
      by (meson eq_key_imp_eq_value) 
  qed
  then show ?thesis
    unfolding single_input.simps by blast
qed


end (* lemma d_states_induces_state_preamble_helper_retains_outputs :
  "retains_outputs_for_states_and_inputs 
          M 
          \<lparr> initial = initial M,
             inputs = inputs M,
             outputs = outputs M,
             transitions = 
                   filter 
                     (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                (wf_transitions M),
             \<dots> = more M \<rparr>"
  (is "retains_outputs_for_states_and_inputs M ?S")
proof -
  have "\<And> tS tM . tS \<in> transitions ?S \<Longrightarrow> tM \<in> transitions M \<Longrightarrow> t_source tS = t_source tM \<Longrightarrow> t_input tS = t_input tM \<Longrightarrow> tM \<in> transitions ?S"
  proof -
    fix tS tM assume "tS \<in> transitions ?S" 
                 and "tM \<in> transitions M" 
                 and "t_source tS = t_source tM" 
                 and "t_input tS = t_input tM"

    have "(t_source tS, t_input tS) \<in> set (d_states M k q)"
      using d_states_induces_state_preamble_helper_h[OF \<open>tS \<in> transitions ?S\<close>] by assumption
    then have "\<exists> qqx \<in> set (d_states M k q) . t_source tS = fst qqx \<and> t_input tS = snd qqx"
      by force
    then have "\<exists> qqx \<in> set (d_states M k q) . t_source tM = fst qqx \<and> t_input tM = snd qqx"
      using \<open>t_source tS = t_source tM\<close> \<open>t_input tS = t_input tM\<close> by simp
    then have "tM \<in> set (transitions ?S)"
      using \<open>tM \<in> transitions M\<close> by force
    moreover have "t_source tM \<in> nodes ?S"
      using \<open>t_source tS = t_source tM\<close> \<open>tS \<in> transitions ?S\<close>
      by (metis (no_types, lifting) wf_transition_simp) 
    ultimately show "tM \<in> transitions ?S"
      by simp
  qed
  then show ?thesis
    unfolding retains_outputs_for_states_and_inputs_def by blast
qed





end (* lemma d_states_last_ex_k :
  assumes "qqx \<in> set (d_states M k q)"  
  shows "\<exists> k' . d_states M (Suc k') q = (d_states M k' q) @ [qqx]"
proof -
  obtain k' where "k'\<le>k" and "0 < k'" and "qqx = last (d_states M k' q)" 
                  "(\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (d_states M k'' q))"
    using d_states_last_ex[OF assms] by blast

  have "k' = (LEAST k' . qqx \<in> set (d_states M k' q))"
    by (metis \<open>0 < k'\<close> \<open>\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (d_states M k'' q)\<close> \<open>qqx = last (d_states M k' q)\<close> assms nat_neq_iff d_states_last_ex d_states_last_least)

  from \<open>0 < k'\<close> obtain k'' where Suc: "k' = Suc k''"
    using gr0_conv_Suc by blast 

  then have "qqx = last (d_states M (Suc k'') q)"
    using \<open>qqx = last (d_states M k' q)\<close> by auto
  have "Suc k'' = (LEAST k' . qqx \<in> set (d_states M k' q))"
    using \<open>k' = (LEAST k' . qqx \<in> set (d_states M k' q))\<close> Suc by auto
  then have "qqx \<notin> set (d_states M k'' q)"
    by (metis lessI not_less_Least)
  then have "(d_states M (Suc k'') q) \<noteq> (d_states M k'' q)"
    using \<open>Suc k'' = (LEAST k' . qqx \<in> set (d_states M k' q))\<close>
    by (metis Suc Suc_neq_Zero \<open>k' \<le> k\<close> \<open>qqx = last (d_states M (Suc k'') q)\<close> assms last_in_set d_states_prefix take_eq_Nil)

  have "d_states M (Suc k'') q = d_states M k'' q @ [qqx]"
    by (metis \<open>qqx = last (d_states M (Suc k'') q)\<close> \<open>d_states M (Suc k'') q \<noteq> d_states M k'' q\<close> last_snoc d_states_last)
  then show ?thesis by blast
qed











thm is_preamble_def


end (* lemma d_states_induces_state_preamble :
  assumes "\<exists> qx \<in> set (d_states M k q) . fst qx = initial M"
  and     "q \<noteq> initial M" (* TODO: add special case in final function *)  
  and     "S = \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>"
shows "is_preamble S M q" 
proof -

  have is_acyclic: "acyclic S" 
    using d_states_induces_state_preamble_helper_acyclic[of M k q] assms(3) by presburger
    
  have is_single_input: "single_input S" 
    using d_states_induces_state_preamble_helper_single_input[of M k q] assms(3) by presburger


   
  have "initial S = initial M"
    using assms(3) by simp 
  moreover have "inputs S = inputs M"
    using assms(3) by simp 
  moreover have "outputs S = outputs M"
    using assms(3) by simp 
  moreover have "h S \<subseteq> h M"
    using assms(3)
    by force 
  ultimately have is_sub : "is_submachine S M"
    unfolding is_submachine.simps by blast



  have has_deadlock_q : "deadlock_state S q" using assms(3) d_states_q_noncontainment[of M k q] unfolding deadlock_state.simps
  proof -
    { fix pp :: "'a \<times> integer \<times> integer \<times> 'a"
      have "\<forall>p. (t_source p, t_input p) \<in> set (d_states M k q) \<or> p \<notin> set (wf_transitions S)"
        using assms(3) by fastforce        
      then have "pp \<notin> set (wf_transitions S) \<or> t_source pp \<noteq> q"
        by (metis \<open>\<not> (\<exists>qqx\<in>set (d_states M k q). fst qqx = q)\<close> fst_conv) }
    then show "\<not> (\<exists>p\<in>set (wf_transitions S). t_source p = q)"
      by blast
  qed

  
        

  have "\<And> q' . q' \<in> nodes S \<Longrightarrow> q' \<noteq> q \<Longrightarrow> \<not> deadlock_state S q'"
  proof -
    fix q' assume "q' \<in> nodes S" and "q' \<noteq> q"

    then consider 
      (a) "q' = initial M" |
      (b) "\<exists> t \<in> transitions S . t_target t = q'"
      by (metis \<open>initial S = initial M\<close> nodes_initial_or_target)
    then have "\<exists> qx \<in> set (d_states M k q) . fst qx = q'"
    proof cases
      case a
      then show ?thesis using assms(1) by auto
    next
      case b
      then obtain t where "t \<in> transitions S" and "t_target t = q'" by blast
      then have "(t_source t, t_input t) \<in> set (d_states M k q)"
        using assms(3) 
        by (metis (mono_tags, lifting) d_states_induces_state_preamble_helper_h)
      moreover have "t \<in> transitions M"
        using \<open>t \<in> transitions S\<close> \<open>h S \<subseteq> h M\<close> by blast
      ultimately have "t_target t \<in> set (map fst (d_states M (k - 1) q))"
        using d_states_transition_target(1) \<open>t_target t = q'\<close> \<open>q' \<noteq> q\<close> by metis
      then show ?thesis 
        using \<open>t_target t = q'\<close>
      proof -
        have f1: "\<And>P. \<not> set (d_states M k q) \<subseteq> P \<or> (t_source t, t_input t) \<in> P"
          using \<open>(t_source t, t_input t) \<in> set (d_states M k q)\<close> by blast
        have "\<forall>ps a f. \<exists>p. ((a::'a) \<notin> set (map f ps) \<or> (p::'a \<times> integer) \<in> set ps) \<and> (a \<notin> set (map f ps) \<or> f p = a)"
          by (metis list_map_source_elem)
        then show ?thesis
          using f1 by (metis (no_types) One_nat_def \<open>q' \<noteq> q\<close> \<open>t \<in> set (wf_transitions M)\<close> \<open>t_target t = q'\<close> d_states_subset d_states_transition_target(1) diff_Suc_Suc diff_zero)
      qed 
    qed 
    then obtain qx where "qx \<in> set (d_states M k q)" and "fst qx = q'" by blast

    then have "(\<exists> t \<in> transitions M . t_source t = fst qx \<and> t_input t = snd qx)" 
      using d_states_index_properties(5)[of _ M k q]
      by (metis in_set_conv_nth)
    then have "(\<exists> t \<in> transitions S . t_source t = fst qx \<and> t_input t = snd qx)"
      using assms(3)
      by (metis (mono_tags, lifting) \<open>fst qx = q'\<close> \<open>inputs S = inputs M\<close> \<open>outputs S = outputs M\<close> \<open>q' \<in> nodes S\<close> \<open>qx \<in> set (d_states M k q)\<close> filter_set member_filter select_convs(4) wf_transition_simp) 

    then show "\<not> deadlock_state S q'" 
      unfolding deadlock_state.simps using \<open>fst qx = q'\<close> by blast
  qed

  then have has_nodes_prop_1 : "\<And> q' . q' \<in> nodes S \<Longrightarrow> (q = q' \<or> \<not> deadlock_state S q')" 
    by blast
  
  have has_nodes_prop_2 : "\<And> q' x t t'. q' \<in> nodes S \<Longrightarrow>  x \<in> inputs M \<Longrightarrow>
            t \<in> transitions S \<Longrightarrow> t_source t = q' \<Longrightarrow> t_input t = x \<Longrightarrow>
            t'\<in> transitions M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> transitions S"
    using d_states_induces_state_preamble_helper_retains_outputs[of M k q] unfolding retains_outputs_for_states_and_inputs_def
    by (metis (no_types, lifting) assms(3))
  
  
  have contains_q : "q \<in> nodes S" using assms(3)
  proof -
    obtain qd where "qd \<in> nodes S" and "deadlock_state S qd"
      using acyclic_deadlock_states[OF \<open>acyclic S\<close>] by blast
    then have "qd = q"
      using has_nodes_prop_1 by blast
    then show ?thesis 
      using \<open>qd \<in> nodes S\<close> by auto
  qed
  
  have has_nodes_prop : "(\<forall>q'\<in>nodes S.
        (q = q' \<or> \<not> deadlock_state S q') \<and>
        (\<forall>x\<in>inputs M.
            (\<exists>t\<in>set (wf_transitions S). t_source t = q' \<and> t_input t = x) \<longrightarrow>
            (\<forall>t'\<in>set (wf_transitions M). t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> set (wf_transitions S))))" 
    using has_nodes_prop_1 has_nodes_prop_2 by blast

  show ?thesis
    unfolding is_preamble_def
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_nodes_prop
    by presburger
qed


definition calculate_state_preamble_from_d_states :: "('a,'b,'c) fsm \<Rightarrow> 'a  \<Rightarrow> ('a,'b,'c) fsm option" where
  "calculate_state_preamble_from_d_states M q = (if q = initial M
    then Some \<lparr> initial = initial M,
                         inputs = inputs M,
                         outputs = outputs M,
                         transitions = [],
                         \<dots> = more M \<rparr>
    else 
      (let DS = (d_states_opt M (size M) q)  in
        (case find_index (\<lambda>qqt . fst qqt = initial M) DS of
          Some i \<Rightarrow> Some \<lparr> initial = initial M,
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = 
                                 filter 
                                   (\<lambda>t . \<exists> qqx \<in> set (take (Suc i) DS) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                              (wf_transitions M),
                           \<dots> = more M \<rparr> |
          None \<Rightarrow> None)))"





end (* lemma calculate_state_preamble_from_d_states_soundness :
  assumes "calculate_state_preamble_from_d_states M q = Some S"
  shows "is_preamble S M q"
proof (cases "q = initial M")
  case True
  then have "S = \<lparr> initial = initial M,
                         inputs = inputs M,
                         outputs = outputs M,
                         transitions = [],
                         \<dots> = more M \<rparr>" using assms unfolding calculate_state_preamble_from_d_states_def by auto
  then show ?thesis 
    using is_preamble_initial[of M] True by presburger
next
  case False
  then have "calculate_state_preamble_from_d_states M q = (case find_index (\<lambda>qqt . fst qqt = initial M) (d_states M (size M) q) of
          Some i \<Rightarrow> Some \<lparr> initial = initial M,
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = 
                                 filter 
                                   (\<lambda>t . \<exists> qqx \<in> set (take (Suc i) (d_states M (size M) q)) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                              (wf_transitions M),
                           \<dots> = more M \<rparr> |
          None \<Rightarrow> None)"
    unfolding calculate_state_preamble_from_d_states_def Let_def using assms
    by (metis d_states_code) 
  then obtain i where  *: "find_index (\<lambda>qqt . fst qqt = initial M) (d_states M (size M) q) = Some i"
                  and **: "S = \<lparr> initial = initial M,
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = 
                                 filter 
                                   (\<lambda>t . \<exists> qqx \<in> set (take (Suc i) (d_states M (size M) q)) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                              (wf_transitions M),
                           \<dots> = more M \<rparr>"
    by (metis (no_types, lifting) assms option.case_eq_if option.collapse option.distinct(1) option.inject) 

  have "(take (Suc i) (d_states M (size M) q)) = d_states M (Suc i) q"
    using find_index_index(1)[OF *]
    by (metis Suc_leI d_states_prefix d_states_self_length) 

  then have "\<exists>qx\<in>set (d_states M (Suc i) q). fst qx = initial M"
    using find_index_index(1,2)[OF *]
    by (metis d_states_by_index last_in_set length_0_conv nat.distinct(1) not_less0 take_eq_Nil)
  moreover have "S = \<lparr> initial = initial M,
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = 
                                 filter 
                                   (\<lambda>t . \<exists> qqx \<in> set (d_states M (Suc i) q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                              (wf_transitions M),
                           \<dots> = more M \<rparr>"
    using ** \<open>(take (Suc i) (d_states M (size M) q)) = d_states M (Suc i) q\<close> by force

  ultimately show ?thesis 
    using d_states_induces_state_preamble[OF _ False] by blast
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