theory State_Separator
imports R_Distinguishability IO_Sequence_Set
begin

section \<open>State Separators\<close>

subsection \<open>Definitions\<close>

definition canonical_separator :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme" where
  "canonical_separator M q1 q2 = 
    (let PM = (product (from_FSM M q1) (from_FSM M q2)) in
      trim_transitions \<lparr> initial = Inl (initial PM),
        inputs = inputs M,
        outputs = outputs M,
        transitions = 
          (map (\<lambda> t . (Inl (t_source t), t_input t, t_output t, Inl (t_target t)) :: (('a \<times> 'a) + 'a) Transition) (transitions PM))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = fst (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = snd (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM)))))
          @ (map (\<lambda> qqt . (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2 ) :: (('a \<times> 'a) + 'a) Transition) (filter (\<lambda> qqt . t_source (snd qqt) = snd (fst qqt) \<and> \<not>(\<exists> t' \<in> set (transitions M) . t_source t' = fst (fst qqt) \<and> t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))) (concat (map (\<lambda> qq' . map (\<lambda> t . (qq',t)) (transitions M)) (nodes_from_distinct_paths PM))))),
        \<dots> = FSM.more M \<rparr> :: (('a \<times> 'a) + 'a,'b) FSM_scheme)"



value[code] "(canonical_separator M_ex 2 3)"
value[code] "trim_transitions (canonical_separator M_ex 2 3)"


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

lemma acyclic_induction [consumes 1, case_names deadlock non_deadlock]:
  assumes "acyclic M"
      and "\<And> q . q \<in> nodes M \<Longrightarrow> deadlock_state M q \<Longrightarrow> P q"
      and "\<And> q . q \<in> nodes M \<Longrightarrow> (\<forall> t \<in> h M . ((t_source t = q) \<longrightarrow> P (t_target t))) \<Longrightarrow> P q"
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
      then show ?case using \<open>q \<in> nodes M\<close> assms(2) by metis
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
      then show ?case using assms(3)[OF Suc.prems(1)] by blast
    qed
  qed

  ultimately show "P q" using \<open>q \<in> nodes M\<close> by blast
qed


      
lemma x :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
      and "path S (Inl (q1',q2')) p"
      and "target p (Inl (q1',q2')) = Inr q1 \<or> target p (Inl (q1',q2')) = Inr q2"
      and "q1 \<in> nodes M" 
      and "q2 \<in> nodes M"
    shows "\<exists> k . r_distinguishable_k M q1' q2' k" 
using assms proof(induction p arbitrary: q1' q2' )
  case Nil
  then show ?case by auto
next
  case (Cons t p)
  then show ?case sorry
qed
  

lemma state_separator_states_r_distinguishable_k :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
      and "Inl (q1',q2') \<in> nodes S"
      and "q1 \<in> nodes M" 
      and "q2 \<in> nodes M"
    shows "\<exists> k . r_distinguishable_k M q1' q2' k"
proof -

lemma state_separator_r_distinguishes :
  assumes "(\<exists>S. is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S)"
  shows "\<exists> k . r_distinguishable_k M q1 q2 k" 
proof 


end