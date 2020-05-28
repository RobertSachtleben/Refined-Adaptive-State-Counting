theory State_Separator_Calculation_Alternative
imports State_Separator
begin

section \<open>Alternative Method of Calculating r-distinguishable State Pairs with Separators\<close>

subsection \<open>Input Selection Without Early Termination\<close>

(* find and remove all found elements *)
fun find_remove_2_all' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> (('a \<times> 'b) list \<times> 'a list)" where
  "find_remove_2_all' P [] _  prevSuccesses prevFailures = (prevSuccesses, prevFailures)" |
  "find_remove_2_all' P (x#xs) ys prevSuccesses prevFailures = (case find (\<lambda>y . P x y) ys of
      Some y \<Rightarrow> find_remove_2_all' P xs ys ((x,y) # prevSuccesses) prevFailures |
      None   \<Rightarrow> find_remove_2_all' P xs ys (prevSuccesses) (x#prevFailures))"

fun find_remove_2_all :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> (('a \<times> 'b) list \<times> 'a list)" where
  "find_remove_2_all P xs ys = find_remove_2_all' P xs ys [] []"

function select_inputs_complete :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "select_inputs_complete f inputList [] nodeSet m = m" |
  "select_inputs_complete f inputList (n#nL) nodeSet m = 
    (case find_remove_2_all (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) (n#nL) inputList
          of ([],_)            \<Rightarrow> m |
             (qx#qxs,nL')      \<Rightarrow> select_inputs_complete f inputList nL' (foldr insert (map fst (qx#qxs)) nodeSet) (m@(qx#qxs)))"
  by pat_completeness auto
termination sorry 
(*
 apply (relation "measure (\<lambda> (f,iL,nL,nS,m) . length nL)")
 apply simp
proof -
  fix f :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set)"
  fix inputList :: "'b list"
  fix n :: 'a
  fix nL :: "'a list" 
  fix nodeSet :: "'a set"
  fix m :: "('a \<times> 'b) list" 
  fix qynL' q ynL' x nL'
  assume "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> nodeSet)) (n # nL) inputList = Some qynL'"
     and "(q, ynL') = qynL'"
     and "(x, nL') = ynL'"

  then have *: "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> nodeSet)) (n # nL) inputList = Some (q,x,nL')"
    by auto

  have "q \<in> set (n # nL)"
  and  "nL' = remove1 q (n # nL)"
    using find_remove_2_set(2,6)[OF *] by simp+

  then have "length nL' < length (n # nL)"
    using remove1_length by metis
    

  then show "((f, inputList, nL', insert q nodeSet, m @ [(q, x)]), f, inputList, n # nL, nodeSet, m) \<in> measure (\<lambda>(f, iL, nL, nS, m). length nL)"
    by auto
qed
*)







subsection \<open>Alternative Calculation\<close>

subsubsection \<open>Canonical Separator Generator\<close>

text \<open>Generalises the concept of a canonical separator for 2 states to an FSM from which a canonical separator for each pair of states can be extracted simply by moving the initial state to that state pair (encased in an Inl constructor)\<close>

lift_definition canonical_separator_generator :: "('a,'b,'c) fsm \<Rightarrow> (('a \<times> 'a) + LR,'b,'c) fsm" is FSM_Impl.canonical_separator_complete'
proof -
  fix A :: "('a,'b,'c) fsm_impl"
  assume "well_formed_fsm A"

  then have p1a: "fsm_impl.initial A \<in> fsm_impl.nodes A"
        and p2a: "finite (fsm_impl.nodes A)"
        and p3a: "finite (fsm_impl.inputs A)"
        and p4a: "finite (fsm_impl.outputs A)"
        and p5a: "finite (fsm_impl.transitions A)"
        and p6a: "(\<forall>t\<in>fsm_impl.transitions A.
            t_source t \<in> fsm_impl.nodes A \<and>
            t_input t \<in> fsm_impl.inputs A \<and> t_target t \<in> fsm_impl.nodes A \<and>
                                             t_output t \<in> fsm_impl.outputs A)"        
    by simp+

  let ?P = "FSM_Impl.canonical_separator_complete' A"

  show "well_formed_fsm ?P" 
  proof -
    
    let ?f = "(\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  
    have "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx"
    proof -
      fix qx
      show "\<And> qx . (\<lambda>qx . (case (set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (fsm_impl.transitions A))) qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {})) qx = (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx"
        unfolding set_as_map_def by (cases "\<exists>z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A"; auto)
    qed
    moreover have "\<And> qx . (\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A}) qx"
    proof -
      fix qx 
      show "(\<lambda> qx . {z. (qx, z) \<in> (\<lambda>(q, x, y, q'). ((q, x), y)) ` fsm_impl.transitions A}) qx = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A}) qx"
        by force
    qed
    ultimately have *:" ?f = (\<lambda> qx . {y | y . \<exists> q' . (fst qx, snd qx, y, q') \<in> fsm_impl.transitions A})" 
      by blast
      
  
    let ?AA = "FSM_Impl.product A A"
    let ?shifted_transitions' = "shifted_transitions (fsm_impl.transitions ?AA)"
    let ?distinguishing_transitions_lr = "distinguishing_transitions_LR ?f (fsm_impl.nodes ?AA) (fsm_impl.inputs ?AA)"
    let ?ts = "?shifted_transitions' \<union> ?distinguishing_transitions_lr"


  
    have pAA: "well_formed_fsm ?AA"
      using p1a p2a p3a p4a p5a p6a unfolding product_code_naive by fastforce


    have "FSM_Impl.nodes ?P = (image Inl (FSM_Impl.nodes ?AA)) \<union> {Inr Left, Inr Right}"
    and  "FSM_Impl.transitions ?P = ?ts"
      by simp+
  
    
  
    
    have p2: "finite (fsm_impl.nodes ?P)"
      using pAA unfolding \<open>FSM_Impl.nodes ?P = (image Inl (FSM_Impl.nodes ?AA)) \<union> {Inr Left, Inr Right}\<close> by auto

    have "fsm_impl.initial ?P = Inl (fsm_impl.initial ?AA)" 
      by auto
    then have p1: "fsm_impl.initial ?P \<in> fsm_impl.nodes ?P" 
      using p1a unfolding canonical_separator'.simps by auto
    have p3: "finite (fsm_impl.inputs ?P)"
      using p3a by auto
    have p4: "finite (fsm_impl.outputs ?P)"
      using p4a by auto


    have "finite (fsm_impl.nodes ?AA \<times> fsm_impl.inputs ?AA)"
      using pAA by auto
    moreover have **: "\<And> x q1 . finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A})"
    proof - 
      fix x q1
      have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A} = {t_output t | t . t \<in> fsm_impl.transitions A \<and> t_source t = q1 \<and> t_input t = x}"
        by auto
      then have "{y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A} \<subseteq> image t_output (fsm_impl.transitions A)"
        unfolding fst_conv snd_conv by blast
      moreover have "finite (image t_output (fsm_impl.transitions A))"
        using p5a by auto
      ultimately show "finite ({y |y. \<exists>q'. (fst (q1, x), snd (q1, x), y, q') \<in> fsm_impl.transitions A})"
        by (simp add: finite_subset)
    qed
    ultimately have "finite ?distinguishing_transitions_lr"
      unfolding * distinguishing_transitions_LR_def by force
    moreover have "finite ?shifted_transitions'"
      using pAA unfolding shifted_transitions_def by auto
    ultimately have "finite ?ts" 
      by blast
    then have p5: "finite (fsm_impl.transitions ?P)"
      by simp
  
    
    have "fsm_impl.inputs ?P = fsm_impl.inputs A"
      by auto
    have "fsm_impl.outputs ?P = fsm_impl.outputs A"
      by auto
  

    have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_source t \<in> fsm_impl.nodes ?P \<and> t_target t \<in> fsm_impl.nodes ?P"
      using pAA unfolding \<open>FSM_Impl.nodes ?P = (image Inl (FSM_Impl.nodes ?AA)) \<union> {Inr Left, Inr Right}\<close> shifted_transitions_def by auto
    moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_source t \<in> fsm_impl.nodes ?P \<and> t_target t \<in> fsm_impl.nodes ?P"
      using pAA unfolding \<open>FSM_Impl.nodes ?P = (image Inl (FSM_Impl.nodes ?AA)) \<union> {Inr Left, Inr Right}\<close> distinguishing_transitions_LR_def * by force
    ultimately have "\<And> t . t \<in> ?ts \<Longrightarrow> t_source t \<in> fsm_impl.nodes ?P \<and> t_target t \<in> fsm_impl.nodes ?P"
      by blast
    moreover have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
    proof -
      have "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?AA \<and> t_output t \<in> fsm_impl.outputs ?AA"
        using pAA unfolding shifted_transitions_def by auto
      then show "\<And> t . t \<in> ?shifted_transitions' \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
        using pAA unfolding \<open>fsm_impl.inputs ?P = fsm_impl.inputs A\<close> \<open>fsm_impl.outputs ?P = fsm_impl.outputs A\<close> by auto
    qed
    moreover have "\<And> t . t \<in> ?distinguishing_transitions_lr \<Longrightarrow> t_input t \<in> fsm_impl.inputs ?P \<and> t_output t \<in> fsm_impl.outputs ?P"
      unfolding * distinguishing_transitions_LR_def using p6a pAA by auto
    ultimately have p6: "(\<forall>t\<in>fsm_impl.transitions ?P.
              t_source t \<in> fsm_impl.nodes ?P \<and>
              t_input t \<in> fsm_impl.inputs ?P \<and> t_target t \<in> fsm_impl.nodes ?P \<and>
                                               t_output t \<in> fsm_impl.outputs ?P)"
      unfolding \<open>FSM_Impl.transitions ?P = ?ts\<close> by blast
  
    show "well_formed_fsm ?P"
      using p1 p2 p3 p4 p5 p6 by linarith
  qed
qed 


value "canonical_separator m_ex_H 1 2"
value "canonical_separator_generator m_ex_H"




definition s_states_generator :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> ((('a \<times> 'a) + LR) \<times> 'b) list" where
  "s_states_generator M = (let CG = canonical_separator_generator M
   in select_inputs_complete (h CG) (inputs_as_list CG) (remove1 (Inr Left) (remove1 (Inr Right) (nodes_as_list CG))) {Inr Left, Inr Right} [])"

value "s_states_generator m_ex_H"



definition state_separator_generator_from_input_choices :: "('a,'b,'c) fsm \<Rightarrow> (('a \<times> 'a) + LR,'b,'c) fsm \<Rightarrow> ((('a \<times> 'a) + LR) \<times> 'b) list \<Rightarrow> (('a \<times> 'a) + LR, 'b, 'c) fsm" where
  "state_separator_generator_from_input_choices M CG cs = 
    (let css  = set cs;
         cssQ = (set (map fst cs)) \<union> {Inr Left, Inr Right};
         S0   = filter_nodes CG (\<lambda> q . q \<in> cssQ);
         S1   = filter_transitions S0 (\<lambda> t . (t_source t, t_input t) \<in> css)          
    in S1)"

definition state_separators_from_s_states_generator :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> (('a \<times> 'a) \<times> ((('a \<times> 'a) + LR, 'b, 'c) fsm)) list" where
  "state_separators_from_s_states_generator M = 
    (let 
          CG = canonical_separator_generator M;
          cs = filter (\<lambda> (qq,x) . case qq of (Inl (q1,q2)) \<Rightarrow> q1 < q2 | _ \<Rightarrow> False) (s_states_generator M);
          SG = state_separator_generator_from_input_choices M CG cs         
    in 
      concat (map (\<lambda> (qq,x) . case qq of (Inl (q1,q2)) \<Rightarrow> [((q1,q2), from_FSM SG (Inl (q1,q2))),((q2,q1), from_FSM SG (Inl (q1,q2)))] | _ \<Rightarrow> [] ) cs))"






end 