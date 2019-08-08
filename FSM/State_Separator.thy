theory State_Separator
imports R_Distinguishability IO_Sequence_Set
begin

section \<open>State Separators\<close>

subsection \<open>Definitions\<close>

(* TODO: reinstate trim_transitions call? *)
(*
definition canonical_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme" where
  "canonical_separator M q1 q2 = 
    (let PM = (product (from_FSM M q1) (from_FSM M q2)) in
      \<lparr> initial = Inl (initial PM),
        inputs = inputs M,
        outputs = outputs M,
        transitions = 
          (map (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t)) :: (('a \<times> 'a) + 'a) Transition) (transitions PM))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM)))))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM))))),
        \<dots> = FSM.more M \<rparr> :: (('a \<times> 'a) + 'a,'b) FSM_scheme)"
*)





abbreviation(input) "shift_Inl \<equiv> (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t)))"

definition shifted_transitions :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a) Transition list" where
  "shifted_transitions M q1 q2 = map shift_Inl (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))"

definition distinguishing_transitions_left :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a) Transition list" where
  "distinguishing_transitions_left M q1 q2 = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 )) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))))"

definition distinguishing_transitions_right :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a) Transition list" where
  "distinguishing_transitions_right M q1 q2 = (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2 )) (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))))"

definition canonical_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme" where
  "canonical_separator M q1 q2 = 
    \<lparr> initial = Inl (initial (product (from_FSM M q1) (from_FSM M q2))),
        inputs = inputs M,
        outputs = outputs M,
        transitions = 
          shifted_transitions M q1 q2
          @ distinguishing_transitions_left M q1 q2
          @ distinguishing_transitions_right M q1 q2,
        \<dots> = FSM.more M \<rparr>"


value[code] "(canonical_separator M_ex 2 3)"
value[code] "trim_transitions (canonical_separator M_ex 2 3)"


lemma canonical_separator_simps :
  "initial (canonical_separator M q1 q2) = Inl (initial (product (from_FSM M q1) (from_FSM M q2)))" 
  "inputs (canonical_separator M q1 q2) = inputs M" 
  "outputs (canonical_separator M q1 q2) = outputs M"
  "transitions (canonical_separator M q1 q2) =  
          shifted_transitions M q1 q2
          @ distinguishing_transitions_left M q1 q2
          @ distinguishing_transitions_right M q1 q2"
  unfolding canonical_separator_def by fastforce+ 



definition is_state_separator_from_canonical_separator :: "(('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_state_separator_from_canonical_separator CSep q1 q2 S = (
    is_submachine S CSep 
    \<and> single_input S
    \<and> acyclic S
    \<and> deadlock_state S (Inr q1)
    \<and> deadlock_state S (Inr q2)
    \<and> ((Inr q1) \<in> nodes S)
    \<and> ((Inr q2) \<in> nodes S)
    \<and> (\<forall> q \<in> nodes S . (q \<noteq> Inr q1 \<and> q \<noteq> Inr q2) \<longrightarrow> (isl q \<and> \<not> deadlock_state S q))
    \<and> (\<forall> q \<in> nodes S . \<forall> x \<in> set (inputs CSep) . (\<exists> t \<in> h S . t_source t = q \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h CSep . t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))
)"

subsection \<open>Calculating State Separators\<close>

fun calculate_state_separator_from_canonical_separator_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme option" where
  "calculate_state_separator_from_canonical_separator_naive M q1 q2 = 
    (let CSep = canonical_separator M q1 q2 in
      find 
        (\<lambda> S . is_state_separator_from_canonical_separator CSep q1 q2 S) 
        (map 
          (\<lambda> assn . generate_submachine_from_assignment CSep assn) 
          (generate_choices 
            (map 
              (\<lambda>q . (q, filter 
                          (\<lambda>x . \<exists> t \<in> h CSep . t_source t = q \<and> t_input t = x) 
                          (inputs CSep))) 
              (nodes_from_distinct_paths CSep)))))"

lemma trim_transitions_state_separator_from_canonical_separator : 
  assumes "is_state_separator_from_canonical_separator CSep q1 q2 S"
  shows   "is_state_separator_from_canonical_separator CSep q1 q2 (trim_transitions S)"
  using assms  unfolding is_state_separator_from_canonical_separator_def
  by (metis trim_transitions_acyclic trim_transitions_deadlock_state_nodes trim_transitions_nodes trim_transitions_simps(4) trim_transitions_single_input trim_transitions_submachine)

lemma transition_reorder_is_state_separator_from_canonical_separator : 
  assumes "is_state_separator_from_canonical_separator CSep q1 q2 S"
  and     "initial S' = initial S"
  and     "inputs S' = inputs S"
  and     "outputs S' = outputs S"
  and     "set (transitions S') = set (transitions S)"
shows "is_state_separator_from_canonical_separator CSep q1 q2 S'"
proof -
  have "is_submachine S CSep"
        and "single_input S"
        and "acyclic S"
        and "deadlock_state S (Inr q1)"
        and "deadlock_state S (Inr q2)"
        and "Inr q1 \<in> nodes S"
        and "Inr q2 \<in> nodes S"
        and "(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)"
        and "(\<forall>q\<in>nodes S.
              \<forall>x\<in>set (inputs CSep).
                 (\<exists>t\<in>h S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))"
    using assms(1) unfolding is_state_separator_from_canonical_separator_def by linarith+

  note transitions_reorder[OF assms(2-5)]

  have "is_submachine S' CSep"
    using \<open>is_submachine S CSep\<close> \<open>h S' = h S\<close> assms(2-4) by auto 
  moreover have "single_input S' " 
    using \<open>single_input S\<close>  unfolding single_input.simps \<open>h S' = h S\<close> \<open>nodes S' = nodes S\<close> by blast
  moreover have "acyclic S'"
    using \<open>acyclic S\<close> assms(2) transitions_reorder(2)[OF assms(2-5)] unfolding acyclic.simps by simp
  moreover have "deadlock_state S' (Inr q1)"
    using \<open>deadlock_state S (Inr q1)\<close> \<open>nodes S' = nodes S\<close> \<open>h S' = h S\<close> by auto
  moreover have "deadlock_state S' (Inr q2)"
    using \<open>deadlock_state S (Inr q2)\<close> \<open>nodes S' = nodes S\<close> \<open>h S' = h S\<close> by auto
  moreover have "Inr q1 \<in> nodes S'" and "Inr q2 \<in> nodes S'"
    using \<open>Inr q1 \<in> nodes S\<close> \<open>Inr q2 \<in> nodes S\<close> \<open>nodes S' = nodes S\<close> by blast+
  moreover have "(\<forall>q\<in>nodes S'. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S' q)"
    using \<open>(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close> \<open>nodes S' = nodes S\<close> \<open>h S' = h S\<close> unfolding deadlock_state.simps by blast
  moreover have "(\<forall>q\<in>nodes S'.
              \<forall>x\<in>set (inputs CSep).
                 (\<exists>t\<in>h S'. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S'))"
    using \<open>(\<forall>q\<in>nodes S.
              \<forall>x\<in>set (inputs CSep).
                 (\<exists>t\<in>h S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))\<close> 
          \<open>h S' = h S\<close> \<open>nodes S' = nodes S\<close> by blast
  ultimately show ?thesis unfolding is_state_separator_from_canonical_separator_def by linarith
qed


lemma calculate_state_separator_from_canonical_separator_naive_soundness :
  assumes "calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S"
shows "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  using assms unfolding calculate_state_separator_from_canonical_separator_naive.simps 
  using find_condition[of "(is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2)"
                          "(map (generate_submachine_from_assignment (canonical_separator M q1 q2))
                             (generate_choices
                               (map (\<lambda>q. (q, filter (\<lambda>x. \<exists>t\<in>h (canonical_separator M q1 q2). t_source t = q \<and> t_input t = x) (inputs (canonical_separator M q1 q2))))
                                 (nodes_from_distinct_paths (canonical_separator M q1 q2)))))", of S] 
  by metis 


lemma calculate_state_separator_from_canonical_separator_naive_exhaustiveness :
  assumes "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  shows "\<exists> S' . calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S'"
proof -
  let ?CSep = "(canonical_separator M q1 q2)"
  from assms obtain S where "is_state_separator_from_canonical_separator ?CSep q1 q2 S" by blast
  let ?S = "trim_transitions S"

  have "is_state_separator_from_canonical_separator ?CSep q1 q2 ?S"
    using trim_transitions_state_separator_from_canonical_separator[OF \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 S\<close>] by assumption

  then have "is_submachine ?S ?CSep"
        and "single_input ?S"
        and "acyclic ?S"
        and "deadlock_state ?S (Inr q1)"
        and "deadlock_state ?S (Inr q2)"
        and "Inr q1 \<in> nodes ?S"
        and "Inr q2 \<in> nodes ?S"
        and "(\<forall>q\<in>nodes ?S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state ?S q)"
        and "(\<forall>q\<in>nodes ?S.
              \<forall>x\<in>set (inputs ?CSep).
                 (\<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h ?CSep. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
    unfolding is_state_separator_from_canonical_separator_def by linarith+

  have "finite (nodes ?S)"
    by (simp add: nodes_finite) 
  moreover have "nodes ?S \<subseteq> nodes ?CSep"
    using submachine_nodes[OF \<open>is_submachine ?S ?CSep\<close>] by assumption
  moreover have "\<And> NS . finite NS \<Longrightarrow> NS \<subseteq> nodes ?CSep 
        \<Longrightarrow> \<exists> f . (\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
  proof -
    fix NS assume "finite NS" and "NS \<subseteq> nodes ?CSep"
    then show "\<exists> f . (\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
    proof (induction)
      case empty
      then show ?case by auto
    next
      case (insert s NS)
      then have "NS \<subseteq> nodes (canonical_separator M q1 q2)" by auto
      then obtain f where f_def : "(\<forall> q . (q \<notin> NS \<longrightarrow> f q = None) \<and> (q \<in> NS \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
        using insert.IH by blast
      
      show ?case proof (cases "s \<in> nodes ?S")
        case True
        then show ?thesis proof (cases "deadlock_state ?S s")
          case True
          let ?f = "f( s := None)"
          have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
            by (metis (no_types, lifting) True f_def insert_iff)
          then show ?thesis by blast
        next
          case False
          then obtain t where "t\<in>h ?S" and "t_source t = s"
            by (meson True deadlock_state.elims(3))
          then have theEx: "\<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = t_input t" 
            using \<open>t_source t = s\<close> \<open>s \<in> nodes ?S\<close> by blast
          
          have "\<forall> t' \<in> h ?S . (t_source t' = s) \<longrightarrow> t_input t' = t_input t"
            using \<open>single_input ?S\<close> \<open>t_source t = s\<close> \<open>s \<in> nodes ?S\<close> unfolding single_input.simps
            by (metis \<open>t \<in> h ?S\<close>) 
          then have theAll: "\<And>x . (\<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x) \<Longrightarrow> x = t_input t"
            by blast


          let ?f = "f( s := Some (t_input t))"
          have "t_input t = (THE x .  \<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x)"
            using the_equality[of "\<lambda> x . \<exists>t'\<in>h ?S. t_source t' = s \<and> t_input t' = x" "t_input t", OF theEx theAll] by simp


          then have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> ?f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> ?f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
            using \<open>s \<in> nodes ?S\<close> False f_def by auto
          then show ?thesis by blast
        qed
      next
        case False
        let ?f = "f( s := None)"
        have "(\<forall> q . (q \<notin> (insert s NS) \<longrightarrow> ?f q = None) \<and> (q \<in> (insert s NS) \<longrightarrow> ((q \<notin> nodes ?S \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> ?f q = None) \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> ?f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
            using False f_def by auto
        then show ?thesis by blast
      qed
    qed
  qed

  ultimately obtain f where f_def : "(\<forall> q . 
                                        (q \<notin> nodes ?S \<longrightarrow> f q = None) 
                                        \<and> (q \<in> nodes ?S \<longrightarrow> ((q \<notin> nodes ?S \<and> f q = None) 
                                                            \<or> (q \<in> nodes ?S \<and> deadlock_state ?S q \<and> f q = None) 
                                                            \<or> (q \<in> nodes ?S \<and> \<not> deadlock_state ?S q \<and> f q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = q \<and> t_input t = x)))))"
    by blast

  let ?assn = "map (\<lambda>q . (q,f q)) (nodes_from_distinct_paths ?CSep)"
  let ?possible_choices = "(map 
              (\<lambda>q . (q, filter 
                          (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = q \<and> t_input t = x) 
                          (inputs ?CSep))) 
              (nodes_from_distinct_paths ?CSep))"
  let ?filtered_transitions = "filter
        (\<lambda>t. (t_source t, Some (t_input t))
             \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep)))
        (wf_transitions ?CSep)"


  (* FSM equivalent to S but possibly with a different order of transitions *)
  let ?S' = "generate_submachine_from_assignment ?CSep ?assn"
  
  have p1: "length ?assn = length ?possible_choices" by auto

  have p2a: "(\<forall> i < length ?assn . (fst (?assn ! i)) = (fst (?possible_choices ! i)))"
    by auto
  have p2b: "(\<And> i . i < length ?assn \<Longrightarrow> ((snd (?assn ! i)) = None \<or> ((snd (?assn ! i)) \<noteq> None \<and> the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i)))))"
  proof -
    fix i assume "i < length ?assn"
    let ?q = "(fst (?assn ! i))"
    have "(fst (?possible_choices ! i)) = ?q" using p2a \<open>i < length ?assn\<close> by auto
    
    have "snd (?assn ! i) = f ?q"
      using \<open>i < length ?assn\<close> by auto 
    have "snd (?possible_choices ! i) = filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep)"
       using \<open>i < length ?assn\<close> p2a by auto 
    
     show "((snd (?assn ! i)) = None \<or> ((snd (?assn ! i)) \<noteq> None \<and> the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i))))" 
     proof (cases "?q \<in> nodes ?S")
      case True
      then show ?thesis proof (cases "deadlock_state ?S ?q")
        case True
        then have "f ?q = None" using f_def \<open>?q \<in> nodes ?S\<close> by blast
        then have "snd (?assn ! i) = None" using \<open>snd (?assn ! i) = f ?q\<close> by auto
        then show ?thesis by blast
      next
        case False
        then obtain x where "\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"
          by (metis (no_types, lifting) deadlock_state.elims(3))
        then have "\<exists>! x . \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"
          using \<open>single_input ?S\<close> unfolding single_input.simps
          by (metis (mono_tags, lifting)) 
        then have "(THE x .  \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x) = x"
          using the1_equality[of "\<lambda> x . \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x"] \<open>\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x\<close> by blast
        moreover have "f ?q = Some (THE x .  \<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x)"
          using False \<open>?q \<in> nodes ?S\<close> f_def by blast
        ultimately have *: "f ?q = Some x" 
          by auto

        have "h ?S \<subseteq> h ?CSep" using \<open>is_submachine ?S ?CSep\<close> by auto
        then have "\<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x"
          using \<open>\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x\<close> by blast
        moreover have "x \<in> set (inputs ?CSep)"
          using \<open>\<exists>t\<in>h ?S. t_source t = ?q \<and> t_input t = x\<close> \<open>is_submachine ?S ?CSep\<close> by auto
        ultimately have **: "x \<in> set (filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep))"
          by auto

        have "the (snd (?assn ! i)) \<in> set (snd (?possible_choices ! i))"
          using * ** \<open>snd (?possible_choices ! i) = filter (\<lambda>x . \<exists> t \<in> h ?CSep . t_source t = ?q \<and> t_input t = x) (inputs ?CSep)\<close> \<open>snd (?assn ! i) = f ?q\<close> by fastforce 

        then show ?thesis by auto
      qed
    next
      case False
      then have "snd (?assn ! i) = None" using \<open>snd (?assn ! i) = f ?q\<close> f_def by auto
      then show ?thesis by auto
    qed
  qed

  then have "?assn \<in> set (generate_choices ?possible_choices)"    
    using generate_choices_idx[of ?assn ?possible_choices] by auto

  have "set (transitions ?S) = set ?filtered_transitions"
  proof -
    have "\<And> t . t \<in> set (transitions ?S) \<Longrightarrow> t \<in> set (?filtered_transitions)"
    proof -
      fix t assume "t \<in> set (transitions ?S)"
      then have "t \<in> set (wf_transitions ?CSep)"
        by (metis (no_types, hide_lams) \<open>is_submachine (trim_transitions S) (canonical_separator M q1 q2)\<close> contra_subsetD submachine_h trim_transitions_transitions)
        

      have "t \<in> h ?S"
        using trim_transitions_transitions \<open>t \<in> set (transitions ?S)\<close> by auto

      have "t_source t \<in> nodes ?S"
        using trim_transitions_t_source[OF \<open>t \<in> set (transitions ?S)\<close>] by assumption
      have "\<not> deadlock_state ?S (t_source t)"
        unfolding deadlock_state.simps using \<open>t \<in> h ?S\<close> by blast
      
      have the1: "\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t"
        using \<open>t \<in> h ?S\<close> by blast
      then have the2: "\<exists>! x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>single_input ?S\<close> unfolding single_input.simps by metis

      
      have "f (t_source t) = Some (t_input t)"
        using f_def \<open>t_source t \<in> nodes ?S\<close> \<open>\<not> deadlock_state ?S (t_source t)\<close> the1_equality[OF the2 the1] by fastforce 
      moreover have "t_source t \<in> nodes ?CSep"
        using \<open>t_source t \<in> nodes ?S\<close> submachine_nodes[OF \<open>is_submachine ?S ?CSep\<close>] by blast
      ultimately have "(t_source t, Some (t_input t)) \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep))"
        using nodes_code[of ?CSep] by fastforce
      
      then show "t \<in> set (?filtered_transitions)"
        using filter_list_set[OF \<open>t \<in> set (wf_transitions ?CSep)\<close>, of "(\<lambda> t . (t_source t, Some (t_input t)) \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep)))"] by blast
    qed

    moreover have "\<And> t . t \<in> set (?filtered_transitions) \<Longrightarrow> t \<in> set (transitions ?S)"
    proof -
      fix t assume a: "t\<in>set (?filtered_transitions)"
      then have "t \<in> set (wf_transitions ?CSep)" 
            and "(t_source t, Some (t_input t))
                        \<in> set (map (\<lambda>q. (q, f q)) (nodes_from_distinct_paths ?CSep))"
        by auto
      then have "f (t_source t) = Some (t_input t)" by auto 
      then have "f (t_source t) \<noteq> None" by auto
      moreover have "t_source t \<in> nodes ?S"
        using calculation f_def by auto
      moreover have "\<not>deadlock_state ?S (t_source t)"
      proof -
        show ?thesis
          by (meson calculation(1) f_def)
      qed
      ultimately have "f (t_source t) = Some (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)"
        using f_def by auto
      then have "t_input t = (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)"
        using \<open>f (t_source t) = Some (t_input t)\<close> by auto


      have "\<exists> x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>\<not>deadlock_state ?S (t_source t)\<close> unfolding deadlock_state.simps
        using \<open>t_source t \<in> nodes (trim_transitions S)\<close> by blast 

      then obtain x where the1: \<open>\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x\<close> by blast
      then have the2: "\<exists>! x . \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x"
        using \<open>single_input ?S\<close> unfolding single_input.simps by metis

      have "x = t_input t"
        using \<open>t_input t = (THE x. \<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = x)\<close> the1_equality[OF the2 the1] by auto
      then have "(\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t)"
        using the1 by blast

      have "t_input t \<in> set (inputs ?CSep)"
        using \<open>t \<in> set (wf_transitions ?CSep)\<close> by auto
      
      have "(\<forall>t'\<in>h ?CSep. t_source t' = t_source t \<and> t_input t' = t_input t \<longrightarrow> t' \<in> h ?S)"
        using \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 ?S\<close> unfolding is_state_separator_from_canonical_separator_def
        using \<open>t_source t \<in> nodes ?S\<close>
              \<open>t_input t \<in> set (inputs ?CSep)\<close>
              \<open>\<exists>t'\<in>h ?S. t_source t' = t_source t \<and> t_input t' = t_input t\<close> by blast
      then have "t \<in> h ?S"
        using \<open>t \<in> set (wf_transitions ?CSep)\<close> by blast
      then show "t \<in> set (transitions ?S)"
        using trim_transitions_transitions[of S] by blast
    qed

    ultimately show ?thesis by blast
  qed

  moreover have "set (transitions ?S') = set (?filtered_transitions)" 
    unfolding generate_submachine_from_assignment.simps by fastforce
  ultimately have "set (transitions ?S') = set (transitions ?S)"
    by blast

  have "initial ?S' = initial ?S \<and> inputs ?S' = inputs ?S \<and> outputs ?S' = outputs ?S"
    using \<open>is_submachine ?S ?CSep\<close> by auto
  then have "is_state_separator_from_canonical_separator ?CSep q1 q2 ?S'"
    using transition_reorder_is_state_separator_from_canonical_separator[OF \<open>is_state_separator_from_canonical_separator ?CSep q1 q2 ?S\<close> _ _ _ \<open>set (transitions ?S') = set (transitions ?S)\<close>] by metis
  moreover have "?S' \<in> set (map (\<lambda> assn . generate_submachine_from_assignment ?CSep assn) (generate_choices ?possible_choices))"
    using generate_submachine_for_contained_assn[OF \<open>?assn \<in> set (generate_choices ?possible_choices)\<close>] by assumption
  ultimately have "calculate_state_separator_from_canonical_separator_naive M q1 q2 \<noteq> None"
    unfolding calculate_state_separator_from_canonical_separator_naive.simps
    using find_None_iff[of "(is_state_separator_from_canonical_separator ?CSep q1 q2)" "(map (generate_submachine_from_assignment ?CSep) (generate_choices ?possible_choices))"]
    by meson
  then show "\<exists> S' . calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S'"
    by blast
qed

lemma calculate_state_separator_from_canonical_separator_naive_ex :
  "(\<exists>S. is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S) 
    = (\<exists> S' . calculate_state_separator_from_canonical_separator_naive M q1 q2 = Some S')"
  using calculate_state_separator_from_canonical_separator_naive_soundness
        calculate_state_separator_from_canonical_separator_naive_exhaustiveness
  by metis


value[code] "image (\<lambda> qq . (qq, (case calculate_state_separator_from_canonical_separator_naive M_ex_9 (fst qq) (snd qq) of None \<Rightarrow> None | Some wt \<Rightarrow> Some (transitions wt)))) {qq \<in> {(q1,q2) | q1 q2 . q1 \<in> nodes M_ex_H \<and> q2 \<in> nodes M_ex_H} . fst qq < snd qq}"
value[code] "image (\<lambda> qq . (qq, (case calculate_state_separator_from_canonical_separator_naive M_ex_9 (fst qq) (snd qq) of None \<Rightarrow> None | Some wt \<Rightarrow> Some (transitions wt)))) {qq \<in> {(q1,q2) | q1 q2 . q1 \<in> nodes M_ex_9 \<and> q2 \<in> nodes M_ex_9} . fst qq < snd qq}"



subsection \<open>State Separators and R-Distinguishability\<close>

(* TODO: move *)
lemma acyclic_finite_paths :
  assumes "acyclic M"
    shows "finite {p . path M q p}"
proof -
  from assms have "{ p . path M (initial M) p} \<subseteq> set (paths_up_to_length M (initial M) (size M))"
    using distinct_path_length_limit_nodes[of M "initial M"] paths_up_to_length_path_set[OF nodes.initial[of M], of "size M"]
    by fastforce 
  moreover have "finite (set (paths_up_to_length M (initial M) (size M)))"
    by auto
  ultimately have "finite { p . path M (initial M) p}"
    using finite_subset by blast

  show "finite {p . path M q p}"
  proof (cases "q \<in> nodes M")
    case True
    then obtain p where "path M (initial M) p" and "target p (initial M) = q" 
      by (metis path_to_node)
    
    have "image (\<lambda>p' . p@p') {p' . path M q p'} \<subseteq> {p' . path M (initial M) p'}"
    proof 
      fix x assume "x \<in> image (\<lambda>p' . p@p') {p' . path M q p'}"
      then obtain p' where "x = p@p'" and "p' \<in> {p' . path M q p'}"
        by blast
      then have "path M q p'" by auto
      then have "path M (initial M) (p@p')"
        using path_append[OF \<open>path M (initial M) p\<close>] \<open>target p (initial M) = q\<close> by auto
      then show "x \<in> {p' . path M (initial M) p'}" using \<open>x = p@p'\<close> by blast
    qed
    
    then have "finite (image (\<lambda>p' . p@p') {p' . path M q p'})"
      using \<open>finite { p . path M (initial M) p}\<close> finite_subset by auto 
    show ?thesis using finite_imageD[OF \<open>finite (image (\<lambda>p' . p@p') {p' . path M q p'})\<close>]
      by (meson inj_onI same_append_eq) 
  next
    case False
    then show ?thesis
      by (meson not_finite_existsD path_begin_node) 
  qed
qed



(* TODO: move *)

lemma acyclic_induction [consumes 1, case_names node]:
  assumes "acyclic M"
      and "\<And> q . q \<in> nodes M \<Longrightarrow> (\<And> t . t \<in> h M \<Longrightarrow> ((t_source t = q) \<Longrightarrow> P (t_target t))) \<Longrightarrow> P q"
    shows "\<forall> q \<in> nodes M . P q"
proof 
  fix q assume "q \<in> nodes M"

  let ?k = "Max (image length {p . path M q p})"
  have "finite {p . path M q p}" using acyclic_finite_paths[OF assms(1)] by auto
  then have k_prop: "(\<forall> p . path M q p \<longrightarrow> length p \<le> ?k)" by auto

  moreover have "\<And> q k . q \<in> nodes M \<Longrightarrow> (\<forall> p . path M q p \<longrightarrow> length p \<le> k) \<Longrightarrow> P q"
  proof -
    fix q k assume "q \<in> nodes M" and "(\<forall> p . path M q p \<longrightarrow> length p \<le> k)"
    then show "P q" 
    proof (induction k arbitrary: q)
      case 0
      then have "{p . path M q p} = {[]}" by blast 
      then have "LS M q \<subseteq> {[]}" unfolding LS.simps by blast
      then have "deadlock_state M q" using deadlock_state_alt_def by metis
      then show ?case using assms(2)[OF \<open>q \<in> nodes M\<close>] unfolding deadlock_state.simps by blast
    next
      case (Suc k)
      have "\<And> t . t \<in> h M \<Longrightarrow> (t_source t = q) \<Longrightarrow> P (t_target t)"
      proof -
        fix t assume "t \<in> h M" and "t_source t = q" 
        then have "t_target t \<in> nodes M"
          using wf_transition_target by metis
        moreover have "\<forall>p. path M (t_target t) p \<longrightarrow> length p \<le> k"
          using Suc.prems(2) \<open>t \<in> set (wf_transitions M)\<close> \<open>t_source t = q\<close> by auto
        ultimately show "P (t_target t)" 
          using Suc.IH by auto
      qed
      then show ?case using assms(2)[OF Suc.prems(1)] by blast
    qed
  qed

  ultimately show "P q" using \<open>q \<in> nodes M\<close> by blast
qed


(* TODO: move *)



lemma path_shift_Inl :
  assumes "(set (map shift_Inl (wf_transitions M))) \<subseteq> set (transitions C)"
      and "\<And> t . t \<in> set (transitions C) \<Longrightarrow> isl (t_target t) \<Longrightarrow> \<exists> t' \<in> set (wf_transitions M) . t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
      and "initial C = Inl (initial M)"
      and "set (inputs C) = set (inputs M)"
      and "set (outputs C) = set (outputs M)"
    shows "path M (initial M) p = path C (initial C) (map shift_Inl p)"
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t p)

  have "path M (initial M) (p@[t]) \<Longrightarrow> path C (initial C) (map shift_Inl (p@[t]))"
  proof -
    assume "path M (initial M) (p@[t])"
    then have "path M (initial M) p" by auto
    then have "path C (initial C) (map shift_Inl p)" using snoc.IH by auto

    have "t_source t = target p (initial M)"
      using \<open>path M (initial M) (p@[t])\<close> by auto
    then have "t_source (shift_Inl t) = target (map shift_Inl p) (Inl (initial M))"
      by (cases p rule: rev_cases; auto)
    then have "t_source (shift_Inl t) = target (map shift_Inl p) (initial C)"
      using assms(3) by auto
    moreover have "target (map shift_Inl p) (initial C) \<in> nodes C"
      using path_target_is_node[OF \<open>path C (initial C) (map shift_Inl p)\<close>] by assumption
    ultimately have "t_source (shift_Inl t) \<in> nodes C"
      by auto
    moreover have "t \<in> h M"
      using \<open>path M (initial M) (p@[t])\<close> by auto
    ultimately have "(shift_Inl t) \<in> h C"
      using assms by auto

    show "path C (initial C) (map shift_Inl (p@[t]))"
      using path_append [OF \<open>path C (initial C) (map shift_Inl p)\<close>, of "[shift_Inl t]"]
      using \<open>(shift_Inl t) \<in> h C\<close> \<open>t_source (shift_Inl t) = target (map shift_Inl p) (initial C)\<close>
      using single_transition_path by force 
  qed

  moreover have "path C (initial C) (map shift_Inl (p@[t])) \<Longrightarrow> path M (initial M) (p@[t])" 
  proof -
    assume "path C (initial C) (map shift_Inl (p@[t]))"
    then have "path C (initial C) (map shift_Inl p)" by auto
    then have "path M (initial M) p" using snoc.IH by auto

    have "t_source (shift_Inl t) = target (map shift_Inl p) (initial C)"
      using \<open>path C (initial C) (map shift_Inl (p@[t]))\<close> by auto
    then have "t_source (shift_Inl t) = target (map shift_Inl p) (Inl (initial M))"
      using assms(3) by (cases p rule: rev_cases; auto)
    then have "t_source t = target p (initial M)"
      by (cases p rule: rev_cases; auto)
    moreover have "target p (initial M) \<in> nodes M"
      using path_target_is_node[OF \<open>path M (initial M) p\<close>] by assumption
    ultimately have "t_source t \<in> nodes M"
      by auto
    moreover have "shift_Inl t \<in> h C"
      using \<open>path C (initial C) (map shift_Inl (p@[t]))\<close> by auto
    moreover have "isl (t_target (shift_Inl t))"
      by auto
    ultimately have "t \<in> h M"
      using assms by fastforce 

    show "path M (initial M) (p@[t])"
      using path_append [OF \<open>path M (initial M) p\<close>, of "[t]"]
            single_transition_path[OF \<open>t \<in> h M\<close>]
            \<open>t_source t = target p (initial M)\<close> by auto
  qed

  ultimately show ?case
    by linarith 
qed




lemma canonical_separator_product_transitions_subset : "(set (map shift_Inl (wf_transitions (product (from_FSM M q1) (from_FSM M q2))))) \<subseteq> set (transitions (canonical_separator M q1 q2))"
proof -
  let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"

  have *: "\<exists> ts2 . transitions (canonical_separator M q1 q2) = (map shift_Inl (wf_transitions ?PM)) @ ts2"
    by (metis (no_types) canonical_separator_simps(4) shifted_transitions_def)
  show ?thesis
    using list_prefix_subset[OF *] by assumption
qed



lemma canonical_separator_product_transitions_isl : 
  assumes "t \<in> set (transitions (canonical_separator M q1 q2))" 
  and "isl (t_target t)" 
shows "\<exists> t' \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2))) . t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
proof -
  let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"

  let ?ts1 = "map shift_Inl (wf_transitions ?PM)"
  let ?ts2 = "distinguishing_transitions_left M q1 q2"
  let ?ts3 = "distinguishing_transitions_right M q1 q2"
  

  have *: "transitions (canonical_separator M q1 q2) = ?ts1 @ ?ts2 @ ?ts3"
    by (metis (no_types) canonical_separator_simps(4) shifted_transitions_def)


  have "\<forall> t' . \<not> isl (t_target ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)) t'))"
    by auto
  have "\<And> t' . t' \<in> set ?ts2 \<Longrightarrow> \<not> isl (t_target t')" 
    using list_map_set_prop[of _ "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1))" "(filter
                       (\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                              \<not> (\<exists>t'\<in>set (transitions M).
                                     t_source t' = snd (fst qqt) \<and>
                                     t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt)))
                       (concat
                         (map (\<lambda>qq'. map (Pair qq') (transitions M))
                           (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))"
                  "\<lambda> t . \<not> isl (t_target t)", OF _ \<open>\<forall> t' . \<not> isl (t_target ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)) t'))\<close>] unfolding distinguishing_transitions_left_def by assumption
  then have **: "t \<notin> set ?ts2" using assms(2) by blast


  have "\<forall> t' . \<not> isl (t_target ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)) t'))"
    by auto
  have "\<And> t' . t' \<in> set ?ts3 \<Longrightarrow> \<not> isl (t_target t')" 
    using list_map_set_prop[of _ "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2))" "(filter
                       (\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                              \<not> (\<exists>t'\<in>set (transitions M).
                                     t_source t' = fst (fst qqt) \<and>
                                     t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt)))
                       (concat
                         (map (\<lambda>qq'. map (Pair qq') (transitions M))
                           (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))"
                  "\<lambda> t . \<not> isl (t_target t)", OF _ \<open>\<forall> t' . \<not> isl (t_target ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)) t'))\<close>] unfolding distinguishing_transitions_right_def by assumption
  then have ***: "t \<notin> set ?ts3" using assms(2) by blast

  have ****: "t \<in> set (?ts1 @ (?ts2 @ ?ts3))" 
    using assms(1) * by metis
  have *****: "t \<notin> set (?ts2 @ ?ts3)" using ** *** by auto
  have ******: "t \<in> set ?ts1" using **** *****
    by (metis (no_types, lifting) Un_iff set_append)
  show ?thesis 
    using list_map_source_elem[OF ******] by assumption
qed



lemma canonical_separator_path_shift :
  "path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) p 
    = path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (map shift_Inl p)"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  have "set (inputs ?C) = set (inputs ?P)" 
    using canonical_separator_simps(2)[of M q1 q2] by auto
  have "set (outputs ?C) = set (outputs ?P)" 
    using canonical_separator_simps(3)[of M q1 q2] by auto

  show ?thesis 
    using path_shift_Inl[OF 
            canonical_separator_product_transitions_subset[of M q1 q2]  
            _
            canonical_separator_simps(1)[of M q1 q2] 
            \<open>set (inputs ?C) = set (inputs ?P)\<close>
            \<open>set (outputs ?C) = set (outputs ?P)\<close>, of p]
    using canonical_separator_product_transitions_isl[of _ M q1 q2] by blast
qed

lemma canonical_separator_product_h_isl : 
  assumes "t \<in> h (canonical_separator M q1 q2)" 
  and "isl (t_target t)" 
shows "\<exists> t' \<in> h (product (from_FSM M q1) (from_FSM M q2)) . t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
  using canonical_separator_product_transitions_isl[OF _ assms(2), of M q1 q2] assms(1) unfolding wf_transitions.simps by (simp del: product.simps from_FSM.simps)

lemma canonical_separator_t_source_isl :
  assumes "t \<in> set (transitions (canonical_separator M q1 q2))"
  shows "isl (t_source t)"
proof -
  let ?PM = "(product (from_FSM M q1) (from_FSM M q2))"

  let ?ts1 = "shifted_transitions M q1 q2"
  let ?ts2 = "distinguishing_transitions_left M q1 q2"
  let ?ts3 = "distinguishing_transitions_right M q1 q2"

  have *: "transitions (canonical_separator M q1 q2) = ?ts1 @ ?ts2 @ ?ts3"
    by (metis (no_types) canonical_separator_simps(4))

  have "\<forall> t' . isl (t_source (shift_Inl t'))"
    by auto
  have "\<forall> t' . isl (t_source ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)) t'))"
    by auto
  have "\<forall> t' . isl (t_source ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)) t'))"
    by auto
  
  have "\<And> t . t \<in> set ?ts1 \<Longrightarrow> isl (t_source t)"
    using list_map_set_prop[of _ shift_Inl "(wf_transitions (product (from_FSM M q1) (from_FSM M q2)))", OF _ \<open>\<forall> t' . isl (t_source (shift_Inl t'))\<close>] unfolding shifted_transitions_def by assumption

  moreover have "\<And> t' . t' \<in> set ?ts2 \<Longrightarrow> isl (t_source t')" 
    using list_map_set_prop[of _ "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1))" "(filter
                       (\<lambda>qqt. t_source (snd qqt) = fst (fst qqt) \<and>
                              \<not> (\<exists>t'\<in>set (transitions M).
                                     t_source t' = snd (fst qqt) \<and>
                                     t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt)))
                       (concat
                         (map (\<lambda>qq'. map (Pair qq') (transitions M))
                           (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))", OF _ \<open>\<forall> t' . isl (t_source ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)) t'))\<close>] unfolding distinguishing_transitions_left_def by assumption

  moreover have "\<And> t' . t' \<in> set ?ts3 \<Longrightarrow> isl (t_source t')" 
    using list_map_set_prop[of _ "(\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2))" "(filter
                       (\<lambda>qqt. t_source (snd qqt) = snd (fst qqt) \<and>
                              \<not> (\<exists>t'\<in>set (transitions M).
                                     t_source t' = fst (fst qqt) \<and>
                                     t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt)))
                       (concat
                         (map (\<lambda>qq'. map (Pair qq') (transitions M))
                           (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))))))", OF _ \<open>\<forall> t' . isl (t_source ((\<lambda>qqt. (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)) t'))\<close>] unfolding distinguishing_transitions_right_def by assumption

  ultimately show ?thesis using \<open>transitions (canonical_separator M q1 q2) = ?ts1 @ ?ts2 @ ?ts3\<close>
    by (metis assms list_prefix_elem) 
qed
  



lemma canonical_separator_path_from_shift :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p"
      and "isl (target p (initial (canonical_separator M q1 q2)))"
  shows "\<exists> p' . path (product (from_FSM M q1) (from_FSM M q2)) (initial (product (from_FSM M q1) (from_FSM M q2))) p' \<and> p = (map shift_Inl p')"
using assms proof (induction p rule: rev_induct)
  case Nil
  show ?case using canonical_separator_path_shift[of M q1 q2 "[]"] by fast
next
  case (snoc t p)
  then have "isl (t_target t)" by auto

  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"

  have "t \<in> h ?C" and "t_source t = target p (initial ?C)" 
    using snoc.prems by auto
  then have "isl (t_source t)"
    using canonical_separator_t_source_isl[of t M q1 q2] by auto  
  then have "isl (target p (initial (canonical_separator M q1 q2)))"
    using \<open>t_source t = target p (initial ?C)\<close> by auto

  have "path ?C (initial ?C) p" using snoc.prems by auto
  then obtain p' where "path ?P (initial ?P) p'"
                   and "p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
    using snoc.IH[OF _ \<open>isl (target p (initial (canonical_separator M q1 q2)))\<close>] by blast
  then have "target p (initial ?C) = Inl (target p' (initial ?P))"
  proof (cases p rule: rev_cases)
    case Nil
    then show ?thesis 
      unfolding target.simps visited_states.simps using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> canonical_separator_simps(1)[of M q1 q2] by auto
  next
    case (snoc ys y)
    then show ?thesis 
      unfolding target.simps visited_states.simps using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> by (cases p' rule: rev_cases; auto)
  qed
  

  obtain t' where "t' \<in> h ?P" 
              and "t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))"
    using canonical_separator_product_h_isl[OF \<open>t \<in> h ?C\<close> \<open>isl (t_target t)\<close>] by blast

  
  have "path ?P (initial ?P) (p'@[t'])"
  proof -
    have "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (map (\<lambda>p. (Inl (t_source p), t_input p, t_output p, Inl (t_target p))) (p' @ [t']))"
      using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))\<close> snoc.prems(1) by auto
    then show ?thesis
      by (metis (no_types) canonical_separator_path_shift)
  qed

  moreover have "p@[t] = map shift_Inl (p'@[t'])"
    using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>t = (Inl (t_source t'), t_input t', t_output t', Inl (t_target t'))\<close> by auto

  ultimately show ?case by meson
qed
  
  
lemma canonical_separator_h_from_product :
  assumes "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
  shows "shift_Inl t \<in> h (canonical_separator M q1 q2)"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?C = "(canonical_separator M q1 q2)"

  have "shift_Inl t \<in> set (transitions ?C)"
    using canonical_separator_product_transitions_subset[of M q1 q2] assms
    by (metis (no_types, lifting) image_iff set_map subsetCE) 

  have "t_source t \<in> nodes ?P" 
    using assms by blast 
  obtain p where "path ?P (initial ?P) p" and "target p (initial ?P) = t_source t"
    using path_to_node[OF \<open>t_source t \<in> nodes ?P\<close>] by metis
  then have "path ?P (initial ?P) (p@[t])"
    using assms path_append_last by metis
  then have "path ?C (initial ?C) (map shift_Inl (p@[t]))"
    using canonical_separator_path_shift[of M q1 q2 "p@[t]"] by linarith
  then have "path ?C (initial ?C) ((map shift_Inl p)@[shift_Inl t])"
    by auto
  then show "shift_Inl t \<in> h ?C"
    by blast
qed


(* TODO: move *)

lemma r_distinguishable_k_by_larger :
  assumes "r_distinguishable_k M q1 q2 k"
      and "k \<le> k'"
    shows "r_distinguishable_k M q1 q2 k'"
  using assms(1) assms(2) nat_induct_at_least by fastforce
  


lemma state_separator_r_distinguishes_k :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  shows "\<exists> k . r_distinguishable_k M q1 q2 k"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?C = "(canonical_separator M q1 q2)"
  
  have "is_submachine S ?C"
        and "single_input S"
        and "acyclic S"
        and "deadlock_state S (Inr q1)"
        and "deadlock_state S (Inr q2)"
        and "Inr q1 \<in> nodes S"
        and "Inr q2 \<in> nodes S"
        and "(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)"
        and tc: "(\<forall>q\<in>nodes S.
              \<forall>x\<in>set (inputs ?C).
                 (\<exists>t\<in>h S. t_source t = q \<and> t_input t = x) \<longrightarrow>
                 (\<forall>t'\<in>h ?C. t_source t' = q \<and> t_input t' = x \<longrightarrow> t' \<in> h S))"
    using assms(1) unfolding is_state_separator_from_canonical_separator_def by linarith+

  let ?Prop = "(\<lambda> q . case q of 
                    (Inl (q1',q2')) \<Rightarrow> (\<exists> k . r_distinguishable_k M q1' q2' k) |
                    (Inr qr) \<Rightarrow> True)"
  have rprop: "\<forall> q \<in> nodes S . ?Prop q"
  using \<open>acyclic S\<close> proof (induction rule: acyclic_induction)
  case (node q)
    then show ?case proof (cases "\<not> isl q")
      case True
      then have "q = Inr q1 \<or> q = Inr q2"
        using \<open>(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close> node(1) by blast
      then show ?thesis by auto
    next
      case False
      then obtain q1' q2' where "q = Inl (q1',q2')" 
        using isl_def prod.collapse by metis
      then have "\<not> deadlock_state S q"
        using \<open>(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close> node(1) by blast

      then obtain t where "t \<in> h S" and "t_source t = q"
        unfolding deadlock_state.simps by blast
      then have "(\<forall>t'\<in>h ?C. t_source t' = q \<and> t_input t' = t_input t \<longrightarrow> t' \<in> h S)"
        using node(1) tc by (metis wf_transition_simp) 


      have "Inl (q1',q2') \<in> nodes ?C"
        using node(1) \<open>q = Inl (q1',q2')\<close> submachine_nodes[OF \<open>is_submachine S ?C\<close>] by auto
      then obtain p where "path ?C (initial ?C) p"
                      and "target p (initial ?C) = Inl (q1',q2')"
        by (metis path_to_node)
      then have "isl (target p (initial ?C))" by auto
      then obtain p' where "path ?P (initial ?P) p'"
                       and "p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
        using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) p\<close>] by blast


      have "path (from_FSM M q1) (initial (from_FSM M q1)) (left_path p')"
          and "path (from_FSM M q2) (initial (from_FSM M q2)) (right_path p')"
        using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p'] \<open>path ?P (initial ?P) p'\<close> by auto
      moreover have "target (left_path p') (initial (from_FSM M q1)) = q1'"
        using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>target p (initial ?C) = Inl (q1',q2')\<close> canonical_separator_simps(1)[of M q1 q2] 
        unfolding target.simps visited_states.simps by (cases p' rule: rev_cases; auto)
      moreover have "target (right_path p') (initial (from_FSM M q2)) = q2'"
        using \<open>p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'\<close> \<open>target p (initial ?C) = Inl (q1',q2')\<close> canonical_separator_simps(1)[of M q1 q2] 
        unfolding target.simps visited_states.simps by (cases p' rule: rev_cases; auto)
      moreover have "p_io (left_path p') = p_io (right_path p')" by auto
      ultimately have p12' : "\<exists>p1 p2.
               path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
               path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
               target p1 (initial (from_FSM M q1)) = q1' \<and>
               target p2 (initial (from_FSM M q2)) = q2' \<and> p_io p1 = p_io p2"
        by blast

      have "q1' \<in> nodes (from_FSM M q1)"
        using path_target_is_node[OF \<open>path (from_FSM M q1) (initial (from_FSM M q1)) (left_path p')\<close>] \<open>target (left_path p') (initial (from_FSM M q1)) = q1'\<close> by auto
      have "q2' \<in> nodes (from_FSM M q2)"
        using path_target_is_node[OF \<open>path (from_FSM M q2) (initial (from_FSM M q2)) (right_path p')\<close>] \<open>target (right_path p') (initial (from_FSM M q2)) = q2'\<close> by auto

      have "t_input t \<in> set (inputs S)"
        using \<open>t \<in> h S\<close> by auto
      then have "t_input t \<in> set (inputs ?C)"
        using \<open>is_submachine S ?C\<close> by auto
      then have "t_input t \<in> set (inputs M)"
        using canonical_separator_simps(2) by metis

      have *: "\<And> t1 t2 . t1 \<in> h M \<Longrightarrow> t2 \<in> h M \<Longrightarrow> t_source t1 = q1' \<Longrightarrow> t_source t2 = q2' \<Longrightarrow> t_input t1 = t_input t \<Longrightarrow> t_input t2 = t_input t \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> (\<exists> k . r_distinguishable_k M (t_target t1) (t_target t2) k)"
      proof -
        fix t1 t2 assume "t1 \<in> h M" 
                     and "t2 \<in> h M" 
                     and "t_source t1 = q1'" 
                     and "t_source t2 = q2'" 
                     and "t_input t1 = t_input t" 
                     and "t_input t2 = t_input t" 
                     and "t_output t1 = t_output t2"
        then have "t_input t1 = t_input t2" by auto

        have "t1 \<in> h (from_FSM M q1)" 
          using \<open>t_source t1 = q1'\<close> \<open>q1' \<in> nodes (from_FSM M q1)\<close> \<open>t1 \<in> h M\<close> by auto
        have "t2 \<in> h (from_FSM M q2)"
          using \<open>t_source t2 = q2'\<close> \<open>q2' \<in> nodes (from_FSM M q2)\<close> \<open>t2 \<in> h M\<close> by auto

        let ?t = "((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)"

        have "\<exists>p1 p2.
               path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
               path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
               target p1 (initial (from_FSM M q1)) = t_source t1 \<and>
               target p2 (initial (from_FSM M q2)) = t_source t2 \<and> p_io p1 = p_io p2"
          using p12' \<open>t_source t1 = q1'\<close> \<open>t_source t2 = q2'\<close> by auto
        
        then have "?t \<in> h ?P"
          using product_transition_from_transitions[OF \<open>t1 \<in> h (from_FSM M q1)\<close> \<open>t2 \<in> h (from_FSM M q2)\<close> \<open>t_input t1 = t_input t2\<close> \<open>t_output t1 = t_output t2\<close>] by presburger

        then have "shift_Inl ?t \<in> h ?C"
          using canonical_separator_h_from_product[of _ M q1 q2] by blast
        moreover have "t_source (shift_Inl ?t) = q"
          using \<open>t_source t1 = q1'\<close> \<open>t_source t2 = q2'\<close> \<open>q = Inl (q1',q2')\<close> by auto
        ultimately have "shift_Inl ?t \<in> h S"
          using \<open>(\<forall>t'\<in>h ?C. t_source t' = q \<and> t_input t' = t_input t \<longrightarrow> t' \<in> h S)\<close> \<open>t_input t1 = t_input t\<close> by auto

        
        have "case t_target (shift_Inl ?t) of Inl (q1', q2') \<Rightarrow> \<exists>k. r_distinguishable_k M q1' q2' k | Inr qr \<Rightarrow> True"
          using node.IH(2)[OF \<open>shift_Inl ?t \<in> h S\<close> \<open>t_source (shift_Inl ?t) = q\<close>] by (cases q; auto)
        moreover have "t_target (shift_Inl ?t) = Inl (t_target t1, t_target t2)" 
          by auto
        ultimately show "\<exists>k. r_distinguishable_k M (t_target t1) (t_target t2) k"
          by auto
      qed

      (* TODO: extract *)

      let ?hs = "{(t1,t2) | t1 t2 . t1 \<in> h M \<and> t2 \<in> h M \<and> t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = t_input t \<and> t_input t2 = t_input t \<and> t_output t1 = t_output t2}"
      have "finite ?hs"
      proof -
        have "?hs \<subseteq> (h M \<times> h M)" by blast
        moreover have "finite (h M \<times> h M)" by blast
        ultimately show ?thesis
          by (simp add: finite_subset) 
      qed
      obtain fk where fk_def : "\<And> tt . tt \<in> ?hs \<Longrightarrow> r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (fk tt)"
      proof 
        let ?fk = "\<lambda> tt . SOME k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k"
        show "\<And> tt . tt \<in> ?hs \<Longrightarrow> r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (?fk tt)"
        proof -
          fix tt assume "tt \<in> ?hs"
          then have "(fst tt) \<in> h M \<and> (snd tt) \<in> h M \<and> t_source (fst tt) = q1' \<and> t_source (snd tt) = q2' \<and> t_input (fst tt) = t_input t \<and> t_input (snd tt) = t_input t \<and> t_output (fst tt) = t_output (snd tt)"
            by force 
          then have "\<exists> k . r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) k"
            using * by blast
          then show "r_distinguishable_k M (t_target (fst tt)) (t_target (snd tt)) (?fk tt)"
            by (simp add: someI_ex)
        qed
      qed

      let ?k = "Max (image fk ?hs)"
      have "\<And> t1 t2 . t1 \<in> h M \<Longrightarrow> t2 \<in> h M \<Longrightarrow> t_source t1 = q1' \<Longrightarrow> t_source t2 = q2' \<Longrightarrow> t_input t1 = t_input t \<Longrightarrow> t_input t2 = t_input t \<Longrightarrow> t_output t1 = t_output t2 \<Longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) ?k"
      proof -
        fix t1 t2 assume "t1 \<in> h M" 
                     and "t2 \<in> h M" 
                     and "t_source t1 = q1'" 
                     and "t_source t2 = q2'" 
                     and "t_input t1 = t_input t" 
                     and "t_input t2 = t_input t" 
                     and "t_output t1 = t_output t2"   
        then have "(t1,t2) \<in> ?hs"
          by force
        then have "r_distinguishable_k M (t_target t1) (t_target t2) (fk (t1,t2))"
          using fk_def by force
        have "fk (t1,t2) \<le> ?k"
          using \<open>(t1,t2) \<in> ?hs\<close> \<open>finite ?hs\<close> by auto
        show "r_distinguishable_k M (t_target t1) (t_target t2) ?k" 
          using r_distinguishable_k_by_larger[OF \<open>r_distinguishable_k M (t_target t1) (t_target t2) (fk (t1,t2))\<close> \<open>fk (t1,t2) \<le> ?k\<close>] by assumption
      qed


      then have "r_distinguishable_k M q1' q2' (Suc ?k)"
        unfolding r_distinguishable_k.simps 
        using \<open>t_input t \<in> set (inputs M)\<close> by blast
      then show "?Prop q"
        using \<open>q = Inl (q1',q2')\<close>
        by (metis (no_types, lifting) case_prodI old.sum.simps(5)) 
    qed
  qed

          


  moreover have "Inl (q1,q2) \<in> nodes S" 
    using \<open>is_submachine S ?C\<close> canonical_separator_simps(1)[of M q1 q2] nodes.initial[of S] by auto
  ultimately show "\<exists>k. r_distinguishable_k M q1 q2 k"
    by auto 
qed




(* TODO: move *)
datatype 'a RD_tree = RD_Node 'a 'a Input nat "Output \<Rightarrow> 'a RD_tree option" 

(*
inductive path :: "('state, 'b) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state Transition list \<Rightarrow> bool" where
  nil[intro!] : "q \<in> nodes M \<Longrightarrow> path M q []" |
  cons[intro!] : "t \<in> h M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_nil_elim[elim!]: "path M q []"
inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"
*)

inductive rd_tree_path :: "'a RD_tree \<Rightarrow> ('a \<times> 'a \<times> Input \<times> nat) list \<Rightarrow> bool" where
  nil[intro!] : "rd_tree_path tr []" |
  unit[intro!] : "rd_tree_path (RD_Node q1 q2 x k f) [(q1,q2,x,k)]" |
  cons[intro!] : "rd_tree_path tr p \<Longrightarrow> \<exists> y . f y = Some tr \<Longrightarrow> rd_tree_path (RD_Node q1 q2 x k f) ((q1,q2,x,k)#p)"

inductive_cases rd_tree_path_nil_elim[elim!]: "rd_tree_path tr []"
inductive_cases rd_tree_path_unit_elim[elim!]: "rd_tree_path tr [t]"
inductive_cases rd_tree_path_cons_elim[elim!]: "rd_tree_path tr (t#p)"



fun r_distinguishable_k_tree :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a RD_tree option" where
  "r_distinguishable_k_tree M q1 q2 0 = (case find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) of
    Some x \<Rightarrow> Some (RD_Node q1 q2 x 0 (\<lambda> y . None)) |
    None \<Rightarrow> None)" |
  "r_distinguishable_k_tree M q1 q2 (Suc k) = (case r_distinguishable_k_tree M q1 q2 k of
    Some t \<Rightarrow> Some t |
    None \<Rightarrow> (case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k) (inputs M) of
      Some x \<Rightarrow> Some (RD_Node q1 q2 x (Suc k) 
          (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) k |
                    None \<Rightarrow> None))) | 
      None \<Rightarrow> None))"

value "r_distinguishable_k_tree M_ex_9 0 3 100"
value "case (r_distinguishable_k_tree M_ex_9 0 3 100) of
        Some (RD_Node q1 q2 x k f) \<Rightarrow> map (\<lambda> y . (y, f y)) (outputs M_ex_9)"

lemma r_distinguishable_k_tree_0_some_unfold : 
  assumes "r_distinguishable_k_tree M q1 q2 0 = Some tr" 
  shows "\<exists> x \<in> set (inputs M) . tr = RD_Node q1 q2 x 0 Map.empty"
proof -
  have "find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) \<noteq> None"                 
    using assms unfolding r_distinguishable_k_tree.simps
    by (metis option.distinct(1) option.simps(4)) 
  then obtain x where x_def : "find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) = Some x" by blast
  then have "tr = RD_Node q1 q2 x 0 Map.empty"
    using assms unfolding r_distinguishable_k_tree.simps by auto
  moreover have "x \<in> set (inputs M)"
    using x_def by (simp add: find_set) 
  ultimately show ?thesis by blast
qed


lemma r_distinguishable_k_tree_Suc_some_unfold : 
  assumes "r_distinguishable_k_tree M q1 q2 (Suc k) = Some tr" 
  shows "\<exists> x \<in> set (inputs M) . \<exists> k' \<le> Suc k . \<exists> f . tr = RD_Node q1 q2 x k' f"
using assms proof (induction k arbitrary: q1 q2 tr)
  case 0
  then show ?case proof (cases "r_distinguishable_k_tree M q1 q2 0")
    case None
    then have c_def : "(case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) of
      Some x \<Rightarrow> Some (RD_Node q1 q2 x (Suc 0) 
          (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 |
                    None \<Rightarrow> None))) | 
      None \<Rightarrow> None) = Some tr"
      unfolding r_distinguishable_k_tree.simps(2) using 0 by auto
    then have "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) \<noteq> None"
      by (metis (no_types, lifting) option.discI option.simps(4))
    then obtain x where x_def : "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) = Some x"
      by auto
    then have *: "tr = RD_Node q1 q2 x (Suc 0) (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 |
                    None \<Rightarrow> None))"
      using c_def unfolding r_distinguishable_k_tree.simps by auto  
    have **: "x \<in> set (inputs M)" 
      using x_def by (simp add: find_set) 

    from * ** show ?thesis by blast
  next
    case (Some tr')
    then have "tr = tr'"
      unfolding r_distinguishable_k_tree.simps(2) using 0 by auto
    moreover obtain x where "x \<in> set (inputs M)" and "tr' = RD_Node q1 q2 x 0 Map.empty"
      using r_distinguishable_k_tree_0_some_unfold[OF Some] by blast
    ultimately show ?thesis by blast
  qed
next
  case (Suc k)
  then show ?case proof (cases "r_distinguishable_k_tree M q1 q2 (Suc k)")
    case None
    then have c_def : "(case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) of
      Some x \<Rightarrow> Some (RD_Node q1 q2 x (Suc (Suc k)) 
          (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))) | 
      None \<Rightarrow> None) = Some tr"
      using Suc unfolding r_distinguishable_k_tree.simps(2)  by auto
    then have "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) \<noteq> None"
      by (metis (no_types, lifting) option.discI option.simps(4))
    then obtain x where x_def : "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) = Some x"
      by auto
    then have *: "tr = RD_Node q1 q2 x (Suc (Suc k)) (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))"
      using c_def unfolding r_distinguishable_k_tree.simps by auto  
    have **: "x \<in> set (inputs M)" 
      using x_def by (simp add: find_set) 

    let ?f = "(\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))"
    from * ** show ?thesis by blast
  next
    case (Some tr')
    then have "tr = tr'"
      unfolding r_distinguishable_k_tree.simps(2) using Suc by auto
    moreover obtain x k' f where "x \<in> set (inputs M)" and "k' \<le> Suc k" and "tr' = RD_Node q1 q2 x k' f"
      using Suc.IH[OF Some] by blast
    ultimately show ?thesis by auto
  qed
qed


lemma r_distinguishable_k_tree_leq : 
  assumes "r_distinguishable_k_tree M q1' q2' k = Some tr"
  and "k \<le> k'"
shows "r_distinguishable_k_tree M q1' q2' k' = Some tr"
  using nat_induct_at_least[OF assms(2), of "\<lambda> k . r_distinguishable_k_tree M q1' q2' k = Some tr", OF assms(1)] by auto 




lemma r_distinguishable_k_tree_min_k_helper :
  assumes "r_distinguishable_k_tree M q1 q2 (k'+k) = Some (RD_Node q1 q2 x k' f)"
  shows "r_distinguishable_k_tree M q1 q2 k' = Some (RD_Node q1 q2 x k' f)"
using assms proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then have *: "r_distinguishable_k_tree M q1 q2 (Suc (k'+k)) = Some (RD_Node q1 q2 x k' f)" by auto
  show ?case
  proof (cases "r_distinguishable_k_tree M q1 q2 (k'+k)")
    case None
    have "find
               (\<lambda>x. \<forall>t1\<in>set (wf_transitions M).
                       \<forall>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                          r_distinguishable_k M (t_target t1) (t_target t2) (k'+k))
               (inputs M) \<noteq> None"
      using * None unfolding r_distinguishable_k_tree.simps
      by (metis (no_types, lifting) option.discI option.simps(4))
    then obtain x where "find
               (\<lambda>x. \<forall>t1\<in>set (wf_transitions M).
                       \<forall>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<longrightarrow>
                          r_distinguishable_k M (t_target t1) (t_target t2) (k'+k))
               (inputs M) = Some x" by blast
    then have "r_distinguishable_k_tree M q1 q2 (Suc (k'+k)) = Some
              (RD_Node q1 q2 x (Suc (k'+k))
                (\<lambda>y. case find
                           (\<lambda>tt. t_source (fst tt) = q1 \<and>
                                 t_source (snd tt) = q2 \<and>
                                 t_input (fst tt) = x \<and>
                                 t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y)
                           (concat (map (\<lambda>t1. map (Pair t1) (wf_transitions M)) (wf_transitions M))) of
                     None \<Rightarrow> None | Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (k'+k)))"
      using assms(1) None unfolding r_distinguishable_k_tree.simps by auto
    then show ?thesis using * by auto
  next
    case (Some a)
    then have "r_distinguishable_k_tree M q1 q2 (Suc (k'+k)) = Some a" by auto
    then have "r_distinguishable_k_tree M q1 q2 (k'+k) = Some (RD_Node q1 q2 x k' f)" using Some * by auto
    then show ?thesis using Suc.IH by auto
  qed
qed

lemma r_distinguishable_k_tree_min_k :
  assumes "r_distinguishable_k_tree M q1 q2 k = Some (RD_Node q1 q2 x k' f)"
      and "k' \<le> k"
    shows "r_distinguishable_k_tree M q1 q2 k' = Some (RD_Node q1 q2 x k' f)"
  using r_distinguishable_k_tree_min_k_helper[of M q1 q2 k' _ x f] assms
  using nat_le_iff_add by auto 



(* TODO: remove duplications from r_distinguishable_k_tree_Suc_some_unfold *)
lemma r_distinguishable_k_tree_Suc_some_unfold_f : 
  assumes "r_distinguishable_k_tree M q1 q2 (Suc k) = Some tr" 
  shows "\<exists> x \<in> set (inputs M) . \<exists> k' \<le> Suc k . \<exists> f . 
          tr = RD_Node q1 q2 x k' f 
          \<and> (\<forall> y q1' q2' x' k'' f' . f y = Some (RD_Node q1' q2' x' k'' f') \<longrightarrow> 
              k'' < k' 
              \<and> r_distinguishable_k_tree M q1' q2' k'' = Some (RD_Node q1' q2' x' k'' f') 
              \<and> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2'))"
using assms proof (induction k arbitrary: q1 q2 tr)
  case 0
  then show ?case proof (cases "r_distinguishable_k_tree M q1 q2 0")
    case None
    then have c_def : "(case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) of
      Some x \<Rightarrow> Some (RD_Node q1 q2 x (Suc 0) 
          (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 |
                    None \<Rightarrow> None))) | 
      None \<Rightarrow> None) = Some tr"
      unfolding r_distinguishable_k_tree.simps(2) using 0 by auto
    then have "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) \<noteq> None"
      by (metis (no_types, lifting) option.discI option.simps(4))
    then obtain x where x_def : "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) 0) (inputs M) = Some x"
      by auto
    then have *: "tr = RD_Node q1 q2 x (Suc 0) (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 |
                    None \<Rightarrow> None))"
      using c_def unfolding r_distinguishable_k_tree.simps by auto  
    have **: "x \<in> set (inputs M)" 
      using x_def by (simp add: find_set) 

    let ?f = "(\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 |
                    None \<Rightarrow> None))"
    have ***: "\<And> y q1' q2' x' k'' f' . ?f y = Some (RD_Node q1' q2' x' k'' f') \<Longrightarrow> k'' < Suc 0 \<and> r_distinguishable_k_tree M q1' q2' k'' = Some (RD_Node q1' q2' x' k'' f') \<and> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')"
    proof -
      fix y q1' q2' x' k' f' assume "?f y = Some (RD_Node q1' q2' x' k' f')"
      then obtain tt where tt_def : "find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) = Some tt"
        by (metis (lifting) option.discI option.exhaust option.simps(4))
      then have "r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 = Some (RD_Node q1' q2' x' k' f')"
        using \<open>?f y = Some (RD_Node q1' q2' x' k' f')\<close> by auto
      then have"r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f')"
        by (metis RD_tree.inject r_distinguishable_k_tree_0_some_unfold)
      have "k' < Suc 0"
        by (metis RD_tree.inject \<open>r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 = Some (RD_Node q1' q2' x' k' f')\<close> less_Suc0 r_distinguishable_k_tree_0_some_unfold)

      have "t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y" using find_condition[OF tt_def] by assumption
      moreover have "t_target (fst tt) = q1'" and "t_target (snd tt) = q2'"
        using \<open>r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) 0 = Some (RD_Node q1' q2' x' k' f')\<close>
        by (metis RD_tree.inject r_distinguishable_k_tree_0_some_unfold)+
      ultimately have "t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_target (fst tt) = q1' \<and> t_target (snd tt) = q2'"
        by auto
      moreover have "fst tt \<in> h M" and "snd tt \<in> h M" using find_set[OF tt_def] by auto    
      ultimately have "(\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')" by blast

      then show "k' < Suc 0 \<and> r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f') \<and> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')" 
        using \<open>k' < Suc 0\<close> \<open>r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f')\<close>  by auto
    qed

    from * ** *** show ?thesis by blast
  next
    case (Some tr')
    then have "tr = tr'"
      unfolding r_distinguishable_k_tree.simps(2) using 0 by auto
    moreover obtain x where "x \<in> set (inputs M)" and "tr' = RD_Node q1 q2 x 0 Map.empty"
      using r_distinguishable_k_tree_0_some_unfold[OF Some] by blast
    ultimately show ?thesis by blast
  qed
next
  case (Suc k)
  then show ?case proof (cases "r_distinguishable_k_tree M q1 q2 (Suc k)")
    case None
    then have c_def : "(case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) of
      Some x \<Rightarrow> Some (RD_Node q1 q2 x (Suc (Suc k)) 
          (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))) | 
      None \<Rightarrow> None) = Some tr"
      using Suc unfolding r_distinguishable_k_tree.simps(2)  by auto
    then have "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) \<noteq> None"
      by (metis (no_types, lifting) option.discI option.simps(4))
    then obtain x where x_def : "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (Suc k)) (inputs M) = Some x"
      by auto
    then have *: "tr = RD_Node q1 q2 x (Suc (Suc k)) (\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))"
      using c_def unfolding r_distinguishable_k_tree.simps by auto  
    have **: "x \<in> set (inputs M)" 
      using x_def by (simp add: find_set) 

    let ?f = "(\<lambda> y . (case find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) of
                    Some tt \<Rightarrow> r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) |
                    None \<Rightarrow> None))"
    have ***: "\<And> y q1' q2' x' k' f' . ?f y = Some (RD_Node q1' q2' x' k' f') \<Longrightarrow> k' < Suc (Suc k) \<and> r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f') \<and> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')"
    proof -
      fix y q1' q2' x' k' f' assume "?f y = Some (RD_Node q1' q2' x' k' f')"
      then obtain tt where tt_def : "find (\<lambda> tt . t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y) (concat (map (\<lambda> t1 . map (\<lambda> t2 . (t1,t2)) (wf_transitions M)) (wf_transitions M))) = Some tt"
        by (metis (lifting) option.discI option.exhaust option.simps(4))
      then have ttd: "r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) = Some (RD_Node q1' q2' x' k' f')"
        using \<open>?f y = Some (RD_Node q1' q2' x' k' f')\<close> by auto
      then have "t_target (fst tt) = q1'" and "t_target (snd tt) = q2'" and "k' \<le> Suc k" unfolding r_distinguishable_k_tree.simps
        using Suc.IH by auto 
      then have "r_distinguishable_k_tree M q1' q2' (Suc k) = Some (RD_Node q1' q2' x' k' f')"
        using ttd by auto
      have "k' < Suc (Suc k) \<and> r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f')"
        using r_distinguishable_k_tree_min_k[OF \<open>r_distinguishable_k_tree M q1' q2' (Suc k) = Some (RD_Node q1' q2' x' k' f')\<close> \<open>k' \<le> Suc k\<close>]  \<open>k' \<le> Suc k\<close> by auto

      have "t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_output (fst tt) = y" using find_condition[OF tt_def] by assumption
      moreover have "t_target (fst tt) = q1'" and "t_target (snd tt) = q2'"
        using \<open>r_distinguishable_k_tree M (t_target (fst tt)) (t_target (snd tt)) (Suc k) = Some (RD_Node q1' q2' x' k' f')\<close>
        by (metis RD_tree.inject r_distinguishable_k_tree_Suc_some_unfold)+
      ultimately have "t_source (fst tt) = q1 \<and> t_source (snd tt) = q2 \<and> t_input (fst tt) = x \<and> t_input (snd tt) = x \<and> t_output (fst tt) = t_output (snd tt) \<and> t_target (fst tt) = q1' \<and> t_target (snd tt) = q2'"
        by auto
      moreover have "fst tt \<in> h M" and "snd tt \<in> h M" using find_set[OF tt_def] by auto    
      ultimately have "(\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')" by blast

      then show "k' < Suc (Suc k) \<and> r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f') \<and> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')"
        using \<open>k' < Suc (Suc k) \<and> r_distinguishable_k_tree M q1' q2' k' = Some (RD_Node q1' q2' x' k' f')\<close> by auto
    qed

    from * ** *** show ?thesis by blast
  next
    case (Some tr')
    then have "tr = tr'"
      unfolding r_distinguishable_k_tree.simps(2) using Suc by auto
    then show ?thesis using Suc.IH[OF Some] by auto
  qed
qed





lemma r_distinguishable_k_tree_height :
  assumes "r_distinguishable_k_tree M q1 q2 k = Some tr"
      and "q1 \<in> nodes M"
      and "q2 \<in> nodes M"
  and "rd_tree_path tr p"
shows "length p \<le> Suc k 
        \<and> (length p > 1 \<longrightarrow> (\<forall> i < (length p - 1) . (snd (snd (snd (p ! (Suc i))))) < (snd (snd (snd (p ! i))))))
        \<and> (\<forall> qqxk \<in> set p . \<exists> p1 p2 . path (from_FSM M q1) q1 p1 \<and> path (from_FSM M q2) q2 p2 \<and> target p1 q1 = fst qqxk \<and> target p2 q2 = fst (snd qqxk) \<and> p_io p1 = p_io p2)"
      (is "?length_prop p k \<and> ?sort_prop p \<and> (\<forall> qqxk \<in> set p . ?path_prop qqxk q1 q2)")
using assms proof (induction k arbitrary: q1 q2 p tr)
  case 0
  then obtain x where "tr = RD_Node q1 q2 x 0 Map.empty"
    using r_distinguishable_k_tree_0_some_unfold by metis
  moreover have "\<And> y . Map.empty y = None" by auto
  ultimately consider "p = []" | "p = [(q1,q2,x,0)]"
    using "0.prems"(4) rd_tree_path.simps  by fastforce
  then show ?case proof (cases)
    case 1
    then show ?thesis by auto
  next
    case 2
    have "path (from_FSM M q1) q1 []" and "path (from_FSM M q2) q2 []"
      using path.nil[OF nodes.initial] from_FSM_simps(1) by metis+
    moreover have "target [] q1 = fst (q1,q2,x,0) \<and> target [] q2 = fst (snd (q1,q2,x,k)) \<and> p_io [] = p_io []"
      by auto
    ultimately have "?path_prop (q1,q2,x,0) q1 q2" by auto
    moreover have "set p = {(q1,q2,x,0)}" using 2 by auto
    ultimately have "(\<forall> qqxk \<in> set p . ?path_prop qqxk q1 q2)" by auto 
    moreover have "?length_prop p 0" and "?sort_prop p" using 2 by auto
    ultimately show ?thesis by auto
  qed
next
  case (Suc k)
  obtain x k' f where "x \<in> set (inputs M)" and "k' \<le> Suc k" and "tr = RD_Node q1 q2 x k' f" and *: "\<And> y q1' q2' x' k'' f'.
                  f y = Some (RD_Node q1' q2' x' k'' f') \<Longrightarrow> 
                    k'' < k' 
                    \<and> r_distinguishable_k_tree M q1' q2' k'' = Some (RD_Node q1' q2' x' k'' f')
                    \<and> (\<exists>t1\<in>h M.
                      \<exists>t2\<in>h M.
                         t_source t1 = q1 \<and>
                         t_source t2 = q2 \<and>
                         t_input t1 = x \<and>
                         t_input t2 = x \<and> t_output t1 = t_output t2 \<and> t_target t1 = q1' \<and> t_target t2 = q2')"
    using r_distinguishable_k_tree_Suc_some_unfold_f[OF Suc.prems(1)] by blast 
  
  show ?case proof (cases p)
    case Nil
    then show ?thesis by auto
  next
    case (Cons t ts)
    then show ?thesis proof (cases ts)
      case Nil
      then have "p = [t]" using Cons by auto
      then have "p = [(q1,q2,x,k')]" using Suc.prems(4)
        using \<open>tr = RD_Node q1 q2 x k' f\<close> by auto 

      have "path (from_FSM M q1) q1 []" and "path (from_FSM M q2) q2 []"
        using path.nil[OF nodes.initial] from_FSM_simps(1) by metis+
      moreover have "target [] q1 = fst (q1,q2,x,0) \<and> target [] q2 = fst (snd (q1,q2,x,k)) \<and> p_io [] = p_io []"
        by auto
      ultimately have "?path_prop (q1,q2,x,0) q1 q2" by auto
      then have "(\<forall> qqxk \<in> set p . ?path_prop qqxk q1 q2)" using \<open>p = [(q1,q2,x,k')]\<close> by auto
      moreover have "?length_prop p (Suc k)" and "?sort_prop p" using \<open>p = [t]\<close> by auto
      
      ultimately show ?thesis by auto
    next
      case (Cons t' ts')
      then have "p = t#(t'#ts')"  
        using \<open>p = t#ts\<close> by auto
      then have "rd_tree_path (RD_Node q1 q2 x k' f) (t#(t'#ts'))" 
        using Suc.prems(4) \<open>tr = RD_Node q1 q2 x k' f\<close> by auto
      then obtain tr' y where "f y = Some tr'" and "rd_tree_path tr' (t'#ts')"
        using rd_tree_path_cons_elim[OF \<open>rd_tree_path (RD_Node q1 q2 x k' f) (t#(t'#ts'))\<close>] by blast
      
      obtain q1' q2' x' k'' f' where "tr' = RD_Node q1' q2' x' k'' f'"
        using RD_tree.exhaust by blast 
      then have "r_distinguishable_k_tree M q1' q2' k'' = Some (RD_Node q1' q2' x' k'' f')"
            and "r_distinguishable_k_tree M q1' q2' k'' = Some tr'"
        using * \<open>f y = Some tr'\<close> by blast+

      have "k'' < k'" using * \<open>f y = Some tr'\<close> \<open>tr' = RD_Node q1' q2' x' k'' f'\<close> by auto
      then have "k'' \<le> k" using \<open>k' \<le> Suc k\<close> by auto

      obtain t1 t2 where "t1 \<in> h M" and "t2 \<in> h M"
                     and "t_source t1 = q1" and "t_source t2 = q2"
                     and "t_input t1 = x" and "t_input t2 = x" 
                     and "t_output t1 = t_output t2" 
                     and "t_target t1 = q1'" and "t_target t2 = q2'"
        using * \<open>f y = Some tr'\<close> \<open>tr' = RD_Node q1' q2' x' k'' f'\<close> by blast

      have "q1' \<in> nodes M"
        using wf_transition_target[OF \<open>t1 \<in> h M\<close>] \<open>t_target t1 = q1'\<close> by auto  
      have "q2' \<in> nodes M"
        using wf_transition_target[OF \<open>t2 \<in> h M\<close>] \<open>t_target t2 = q2'\<close> by auto

      have "length (t'#ts') \<le> Suc k" 
        and sort_prop: "(length (t'#ts') > 1 \<longrightarrow> (\<forall> i < (length (t'#ts') - 1) . (snd (snd (snd ((t'#ts') ! (Suc i))))) < (snd (snd (snd ((t'#ts') ! i))))))"
        and path_prop: "(\<forall>qqxk\<in>set (t' # ts').
                          \<exists>p1 p2.
                             path (from_FSM M q1') q1' p1 \<and>
                             path (from_FSM M q2') q2' p2 \<and> target p1 q1' = fst qqxk \<and> target p2 q2' = fst (snd qqxk) \<and> p_io p1 = p_io p2)"
        using Suc.IH[OF r_distinguishable_k_tree_leq[OF \<open>r_distinguishable_k_tree M q1' q2' k'' = Some tr'\<close> \<open>k'' \<le> k\<close>] \<open>q1' \<in> nodes M\<close> \<open>q2' \<in> nodes M\<close> \<open>rd_tree_path tr' (t'#ts')\<close>] by auto
      then have "length p \<le> Suc (Suc k)"
        using \<open>p = t#(t'#ts')\<close> by auto
      
      have "snd (snd (snd ((t#t'#ts') ! 0))) = k'"
        using Suc.prems(4) \<open>p = t # t' # ts'\<close> \<open>tr = RD_Node q1 q2 x k' f\<close> by fastforce
      moreover have "snd (snd (snd ((t#t'#ts') ! 1))) = k''"
        using \<open>p = t # t' # ts'\<close> \<open>rd_tree_path tr' (t' # ts')\<close> \<open>tr' = RD_Node q1' q2' x' k'' f'\<close> by fastforce 
      ultimately have s1: "snd (snd (snd ((t#t'#ts') ! (Suc 0)))) < snd (snd (snd ((t#t'#ts') ! 0)))"
        using \<open>k'' < k'\<close> by auto
      
      have "\<And> i . i < (length (t'#ts') - 1) \<Longrightarrow> (snd (snd (snd ((t'#ts') ! (Suc i))))) < (snd (snd (snd ((t'#ts') ! i))))"
        using sort_prop by auto
      then have s2: "\<And> i . i < (length (t#t'#ts') - 1) \<Longrightarrow> i > 0 \<Longrightarrow> (snd (snd (snd ((t#t'#ts') ! (Suc i))))) < (snd (snd (snd ((t#t'#ts') ! i))))"
        using sort_prop by auto
      
      have s12: "\<And> i . i < length (t#t'#ts') - 1  \<Longrightarrow> (snd (snd (snd ((t#t'#ts') ! (Suc i))))) < (snd (snd (snd ((t#t'#ts') ! i))))"
        using s1 s2 by blast 


      then have "p = (q1,q2,x,k')#(t'#ts')"
        using Suc.prems(4) \<open>p = t # t' # ts'\<close> \<open>tr = RD_Node q1 q2 x k' f\<close> by auto

      have "path (from_FSM M q1) q1 []" and "path (from_FSM M q2) q2 []"
        using path.nil[OF nodes.initial] from_FSM_simps(1) by metis+
      moreover have "target [] q1 = fst (q1,q2,x,k') \<and> target [] q2 = fst (snd (q1,q2,x,k)) \<and> p_io [] = p_io []"
        by auto
      ultimately have "?path_prop (q1,q2,x,k') q1 q2" by auto
      moreover have "\<And> qqxk . qqxk \<in> set (t'#ts') \<Longrightarrow> ?path_prop qqxk q1 q2"
      proof -
        fix qqxk assume "qqxk \<in> set (t'#ts')"
        then obtain p1 p2 where "path (from_FSM M q1') q1' p1"
                            and "path (from_FSM M q2') q2' p2" 
                            and "target p1 q1' = fst qqxk" 
                            and "target p2 q2' = fst (snd qqxk)" 
                            and "p_io p1 = p_io p2"
          using path_prop by blast
        
        have "path M q1' p1" using from_FSM_path[OF \<open>q1' \<in> nodes M\<close> \<open>path (from_FSM M q1') q1' p1\<close>] by assumption
        
        have "path M q2' p2" using from_FSM_path[OF \<open>q2' \<in> nodes M\<close> \<open>path (from_FSM M q2') q2' p2\<close>] by assumption

        have "path (from_FSM M q1) q1 (t1#p1)"
          using \<open>t1 \<in> h M\<close> \<open>t_source t1 = q1\<close> \<open>path M q1' p1\<close> \<open>t_target t1 = q1'\<close>
          by (meson from_FSM_path_rev_initial path.cons)
        moreover have "path (from_FSM M q2) q2 (t2#p2)"
          using \<open>t2 \<in> h M\<close> \<open>t_source t2 = q2\<close> \<open>path M q2' p2\<close> \<open>t_target t2 = q2'\<close> 
          by (meson from_FSM_path_rev_initial path.cons)
        moreover have "target (t1#p1) q1 = fst qqxk"
          using \<open>target p1 q1' = fst qqxk\<close> \<open>t_target t1 = q1'\<close> by auto
        moreover have "target (t2#p2) q2 = fst (snd qqxk)"
          using \<open>target p2 q2' = fst (snd qqxk)\<close> \<open>t_target t2 = q2'\<close> by auto
        moreover have "p_io (t1#p1) = p_io (t2#p2)"
          using \<open>t_input t1 = x\<close> \<open>t_input t2 = x\<close> \<open>t_output t1 = t_output t2\<close> \<open>p_io p1 = p_io p2\<close> by auto
        ultimately show "?path_prop qqxk q1 q2" by blast
      qed

      ultimately have "(\<forall> qqxk \<in> set p . ?path_prop qqxk q1 q2)" using \<open>p = (q1,q2,x,k')#(t'#ts')\<close> by auto

      then show ?thesis 
        using \<open>length p \<le> Suc (Suc k)\<close> s12 \<open>p = t#t'#ts'\<close> by auto
    qed
  qed
qed




lemma rd_tree_from_r_distinguishable_k :
  assumes "r_distinguishable_k M q1 q2 k"
  shows "r_distinguishable_k_tree M q1 q2 k \<noteq> None"
using assms proof (induction k arbitrary: q1 q2)
  case 0
  then have "find
           (\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
           (inputs M) \<noteq> None"                 
    unfolding r_distinguishable_k.simps using find_None_iff[of "(\<lambda>x. \<not> (\<exists>t1\<in>set (wf_transitions M).
                       \<exists>t2\<in>set (wf_transitions M).
                          t_source t1 = q1 \<and>
                          t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" "inputs M"] by blast
  then show ?case unfolding r_distinguishable_k_tree.simps by auto
next
  case (Suc k)
  then show ?case 
  proof (cases "r_distinguishable_k M q1 q2 k")
    case True
    then have "r_distinguishable_k_tree M q1 q2 k \<noteq> None"
      using Suc.IH by metis
    then show ?thesis 
      unfolding r_distinguishable_k_tree.simps by auto
  next
    case False
    then have "\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k"
      using Suc.prems unfolding r_distinguishable_k.simps by blast
    then have fx: "find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k) (inputs M) \<noteq> None"
      using find_None_iff[of "(\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k)" "inputs M"] by blast
    then show ?thesis by (cases "r_distinguishable_k_tree M q1 q2 k"; auto)
  qed
qed


lemma r_distinguishable_k_tree_least_path_decreasing :
  assumes "r_distinguishable_k_tree M q1 q2 k0 = Some tr"
      and "rd_tree_path tr (t1#t2#ts)"
  shows "fst (snd (snd t1)) > fst (snd (snd t2))"

lemma r_distinguishable_k_tree_least_path_unique :
  assumes "r_distinguishable_k_tree M q1 q2 k0 = Some tr"
      and "rd_tree_path tr p"
  shows "(LEAST k . r_distinguishable_k_tree M q1 q2 k \<noteq> None) < 2 * size M"


lemma r_distinguishable_k_tree_least :
  assumes "\<exists> k . r_distinguishable_k_tree M q1 q2 k \<noteq> None"
  shows "(LEAST k . r_distinguishable_k_tree M q1 q2 k \<noteq> None) < 2 * size M"




end (*



(* TODO: move *)
(*
fun r_distinguishable_k :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "r_distinguishable_k M q1 q2 0 = (\<exists> x \<in> set (inputs M) . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))" |
  "r_distinguishable_k M q1 q2 (Suc k) = (r_distinguishable_k M q1 q2 k                                           \<or> (\<exists> x \<in> set (inputs M) . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k))"
*)

fun r_distinguishable_k_test :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> Input) option" where
  "r_distinguishable_k_test M q1 q2 0 = (case find (\<lambda> x . \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2)) (inputs M) of
    Some x \<Rightarrow> Some (0,x) |
    None \<Rightarrow> None)"  |
  "r_distinguishable_k_test M q1 q2 (Suc k) = (case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k) (inputs M) of
      Some x \<Rightarrow> Some (Suc k,x) |
      None \<Rightarrow> None)"
  (*
  "r_distinguishable_k_test M q1 q2 (Suc k) = (case r_distinguishable_k_test M q1 q2 k of
    Some xk \<Rightarrow> Some xk |
    None \<Rightarrow> (case find (\<lambda> x . \<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1 \<and> t_source t2 = q2 \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) k) (inputs M) of
      Some x \<Rightarrow> Some (Suc k,x) |
      None \<Rightarrow> None))"
  *)

value "r_distinguishable_k_test M_ex_9 0 3 0"
value "r_distinguishable_k_test M_ex_9 0 3 1"
value "r_distinguishable_k_test M_ex_9 0 3 2"

fun r_distinguishable_k_least :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> (nat \<times> Input) option" where
  "r_distinguishable_k_least M q1 q2 n = (case find (\<lambda> k . r_distinguishable_k_test M q1 q2 k \<noteq> None) (upt 0 (Suc n)) of
    Some k \<Rightarrow> r_distinguishable_k_test M q1 q2 k |
    None \<Rightarrow> None)"

value "r_distinguishable_k_least M_ex_9 0 3 0"
value "r_distinguishable_k_least M_ex_9 0 3 1"
value "r_distinguishable_k_least M_ex_9 0 3 2"


lemma x :
  assumes "\<exists> k . r_distinguishable_k M q1' q2' k"
  shows "(LEAST k . r_distinguishable_k M q1' q2' k) < 2 * size M"
proof -
  (* construct submachine of product automaton from LEAST *)
  let ?k = "(LEAST k . r_distinguishable_k M q1' q2' k)"
  have "r_distinguishable_k M q1' q2' ?k" 
    using assms LeastI by blast 
  
  

end (*

fun r_distinguishable_k_witness :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (nat \<times> Input) option" where
"r_distinguishable_k_witness M q1' q2' = (if (\<exists> k . r_distinguishable_k M q1' q2' k)
            then (let lk = LEAST k . r_distinguishable_k M q1' q2' k in
                    (if lk = 0
                      then Some (lk, SOME x . x \<in> set (inputs M) \<and> \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                      else Some (lk, SOME x . x \<in> set (inputs M) \<and> (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (lk-1)))))
            else None)"

value "r_distinguishable_k_witness M_ex_9 1 3"

lemma r_distinguishable_k_witnesses :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
  shows "\<exists> fk . \<forall> q1' \<in> nodes M . \<forall> q2' \<in> nodes M . 
          ((fk q1 q2) = (if (\<exists> k . r_distinguishable M q1' q2' k)
            then (let lk = LEAST k . r_distinguishable M q1' q2' k in
                    (if lk = 0
                      then (k, SOME x . x \<in> set (inputs M) \<and> \<not> (\<exists> t1 \<in> h M . \<exists> t2 \<in> h M . t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2))
                      else (k, SOME x . x \<in> set (inputs M) \<and> (\<forall> t1 \<in> h M . \<forall> t2 \<in> h M . (t_source t1 = q1' \<and> t_source t2 = q2' \<and> t_input t1 = x \<and> t_input t2 = x \<and> t_output t1 = t_output t2) \<longrightarrow> r_distinguishable_k M (t_target t1) (t_target t2) (k-1))))"


(* Note: requires observability, a (per definition) even states in non-observable FSMs may be r-d, but this might require different inputs *)
lemma state_separator_from_r_distinguishable_k :
  assumes "\<exists> k . r_distinguishable_k M q1 q2 k"
  assumes "observable M"
  assumes "q1 \<in> nodes M" and "q2 \<in> nodes M"
  shows "\<exists> S . is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
proof (rule ccontr) 
  let ?CSep = "canonical_separator M q1 q2"

  obtain fk where 
       



(* TODO:
 - r_dist \<Longrightarrow> EX SSep (prove via r_compatible)

 - Rethink effort required here: Algorithm likely relies on some distinction property only 
    - formulate basic requirements:  
        - finite 
        - subset of L q1 UN L q2
        - sequences in L q1 IN L q2 are not maximal
        - prefix-closed (?)
        - maximal sequences are marked q1/q2, depending on containment in L q1 or L q2
        - output completed / transition completed (?)

 - State Separator (general def)
 - State Separator vs State Separator from CSep
 - State Separator Set
*)






end