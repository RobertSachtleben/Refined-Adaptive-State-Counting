theory Test_Case_Sequences
imports State_Separator
begin

subsection \<open>State Separation Sets as Test Cases\<close>

(* TODO: introduce Petrenko's notion of test cases? *)

lemma state_separation_set_sym : "is_state_separation_set M q1 q2 = is_state_separation_set M q2 q1"
  unfolding is_state_separation_set_def by blast

(* note that no handling of pass traces is required, as Petrenko's pass relies only on the reachability of Fail states *)
(* TODO: incorporate fault_model ? *)
definition fail_sequence_set :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "fail_sequence_set M q Fail = (LS M q \<inter> Fail = {})"

lemma fail_sequence_set_application : 
  assumes "fail_sequence_set M q Fail"
      and "LS M' q' \<inter> Fail \<noteq> {}"      
shows "\<exists> io \<in> Fail . io \<in> (LS M' q' - LS M q)"
  using assms unfolding fail_sequence_set_def by blast



definition state_separation_fail_sequence_set_from_state_separator :: "('a, 'c) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('b + 'a, 'c) FSM_scheme \<Rightarrow> (Input \<times> Output) list set" where
  "state_separation_fail_sequence_set_from_state_separator M q1 S = 
          output_completion_for_FSM M (LS_acyclic S (initial S)) - (insert [] (LS M q1))"
(*        output_completion_for_FSM M (L S) - (LS M q1)" *)
(*      output_completion_for_FSM M (L S) - {io | io p . path S (initial S) p \<and> target p (initial S) = Inr q1 \<and> (\<exists> io' . p_io p = io@io')}"*)
(* TODO: prove equivalency with above alternative definition? *)

lemma state_separation_fail_sequence_set_from_state_separator_code[code] :
  "state_separation_fail_sequence_set_from_state_separator M q1 S = 
    output_completion_for_FSM M (LS_acyclic S (initial S)) - set (map p_io (paths_up_to_length M q1 (card (h S))))"
proof -
  

  have "(insert [] (LS M q1)) - set (map p_io (paths_up_to_length M q1 (card (h S))))
         = {io \<in> LS M q1 . length io > (card (h S))}" (*{p_io p | p . path M q1 p \<and> length p > length (wf_transitions S)}"*)
  proof (cases "q1 \<in> nodes M")
    case True

    have "set (map p_io (paths_up_to_length M q1 (card (h S)))) = 
            {p_io p | p . path M q1 p \<and> length p \<le> (card (h S))}"
      using paths_up_to_length_path_set[OF True, of "(card (h S))"] by auto
    then have "set (map p_io (paths_up_to_length M q1 (card (h S)))) = {io \<in> LS M q1 . length io \<le> (card (h S))}"
      unfolding LS.simps by force
    moreover have "insert [] (LS M q1) = LS M q1"
      using True unfolding LS.simps by auto
    moreover have "(LS M q1) - {io \<in> LS M q1 . length io \<le> (card (h S))} = {io \<in> LS M q1 . length io > (card (h S))}"
      by auto
    ultimately have "(insert [] (LS M q1)) - set (map p_io (paths_up_to_length M q1 (card (h S)))) = {io \<in> LS M q1 . length io > (card (h S))}"
      by auto
    moreover have "{io \<in> LS M q1 . length io > length (wf_transitions S)} = {p_io p | p . path M q1 p \<and> length p > length (wf_transitions S)}"
      unfolding LS.simps by force 
    ultimately show ?thesis by auto
  next
    case False
    have "\<And> n . paths_up_to_length M q1 n = [[]]"
    proof -
      fix n show "paths_up_to_length M q1 n = [[]]" 
      proof (induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        have "\<And> p. \<not> path M q1 p"
          using False by (meson path_begin_node) 
        then have *: "\<And> n . filter (path M q1) (lists_of_length (wf_transitions M) (Suc n)) = []"
          by auto
        show ?case
          using Suc *[of n] unfolding paths_up_to_length.simps paths_of_length.simps by force
      qed 
    qed
    then have "paths_up_to_length M q1 (card (h S)) = [[]]"
      by blast
    moreover have "(insert [] (LS M q1)) = {[]}"
      unfolding LS.simps using False path_begin_node by fastforce
    ultimately show ?thesis by auto
  qed

  moreover have "\<And> io . io \<in> output_completion_for_FSM M (LS_acyclic S (initial S)) \<Longrightarrow> length io \<le> (card (h S))"
    using paths_up_to_length_path_set[OF nodes.initial[of S], of "(card (h S))"] 
    using output_completion_for_FSM_length[of "LS_acyclic S (initial S)", of "(card (h S))" M]
    unfolding LS_acyclic_def by force

  ultimately have "output_completion_for_FSM M (LS_acyclic S (initial S)) \<inter> ((insert [] (LS M q1)) - set (map p_io (paths_up_to_length M q1 (card (h S))))) = {}"
    by force

  moreover have "set (map p_io (paths_up_to_length M q1 (card (h S)))) \<subseteq> (insert [] (LS M q1))"
  proof (cases "q1 \<in> nodes M")
    case True
    show ?thesis 
      using paths_up_to_length_path_set[OF True, of "(card (h S))"] unfolding LS.simps by force
  next
    case False
    
    have "\<And> n . paths_up_to_length M q1 n = [[]]"
    proof -
      fix n show "paths_up_to_length M q1 n = [[]]" 
      proof (induction n)
        case 0
        then show ?case by auto
      next
        case (Suc n)
        have "\<And> p. \<not> path M q1 p"
          using False by (meson path_begin_node) 
        then have *: "\<And> n . filter (path M q1) (lists_of_length (wf_transitions M) (Suc n)) = []"
          by auto
        show ?case
          using Suc *[of n] unfolding paths_up_to_length.simps paths_of_length.simps by force
      qed 
    qed
    then have "paths_up_to_length M q1 (card (h S)) = [[]]"
      by blast
    moreover have "(insert [] (LS M q1)) = {[]}"
      unfolding LS.simps using False path_begin_node by fastforce
    ultimately show ?thesis by auto
  qed

  ultimately show ?thesis
    unfolding state_separation_fail_sequence_set_from_state_separator_def
    by blast
qed


value "calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2"
value "case calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2 of
        Some S \<Rightarrow> Some (LS_acyclic S (initial S)) |
        None \<Rightarrow> None"
value "case calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2 of
        Some S \<Rightarrow> Some (output_completion_for_FSM M_ex_9 (LS_acyclic S (initial S))) |
        None \<Rightarrow> None"
value "case calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2 of
        Some S \<Rightarrow> Some (state_separation_fail_sequence_set_from_state_separator M_ex_9 0 S) |
        None \<Rightarrow> None"


lemma state_separation_fail_sequence_set_from_state_separator :
  "fail_sequence_set M q1 (state_separation_fail_sequence_set_from_state_separator M q1 S)"
  unfolding fail_sequence_set_def state_separation_fail_sequence_set_from_state_separator_def by blast


  
lemma state_separator_language_intersection :
  assumes "completely_specified M'"
      and "set (inputs M) \<subseteq> set (inputs M')"
      and "set (outputs M) = set (outputs M')"
      and "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S" 
      and "q1' \<in> nodes M'"
    shows "LS M' q1' \<inter> output_completion_for_FSM M (L S) \<noteq> {}" 
proof -
  obtain p where "path S (initial S) p" and "target p (initial S) = Inr q1"
    using assms(4) path_to_node unfolding is_state_separator_from_canonical_separator_def by metis
  moreover have "initial S = Inl (q1,q2)"
    using assms(4) unfolding is_state_separator_from_canonical_separator_def is_submachine.simps canonical_separator_simps(1) product_simps(1) from_FSM_simps(1) by presburger
  ultimately have "p \<noteq> []"
    by force
  then have "p = [hd p] @ (tl p)"
    by auto
  then have "path S (initial S) [hd p]"
    using \<open>path S (initial S) p\<close> using path_prefix by metis
  then have "p_io [hd p] \<in> L S"  
    unfolding LS.simps by force
  then have "\<exists> y . [(t_input (hd p), y)] \<in> (L S)"
    by (metis (no_types, lifting) list.simps(8) list.simps(9))
  moreover have "set (outputs S) = set (outputs M)"
    using assms(4) unfolding is_state_separator_from_canonical_separator_def is_submachine.simps canonical_separator_simps(3) product_simps(3) by presburger
  ultimately have "\<forall> y \<in> set (outputs M') . [(t_input (hd p), y)] \<in> output_completion_for_FSM M (L S)"
    using assms(3) unfolding output_completion_for_FSM_def by simp
  
  have "t_input (hd p) \<in> set (inputs S)"
    using \<open>path S (initial S) [hd p]\<close> by auto
  moreover have "set (inputs S) = set (inputs M)"
    using assms(4) unfolding is_state_separator_from_canonical_separator_def is_submachine.simps canonical_separator_simps(2) product_simps(2) by force
  ultimately have "t_input (hd p) \<in> set (inputs M')"
    using assms(2) by blast
  then obtain t' where "t' \<in> h M'" and "t_source t' = q1'" and "t_input t' = t_input (hd p)"
    using assms(1,5) unfolding completely_specified.simps by blast
  then have "path M' q1' [t']" by auto
  then have "[(t_input (hd p), t_output t')] \<in> LS M' q1'"
    using \<open>t_input t' = t_input (hd p)\<close> unfolding LS.simps by force 

  have "t_output t' \<in> set (outputs M')" 
    using \<open>t' \<in> h M'\<close> by auto
  then have "[(t_input (hd p), t_output t')] \<in> output_completion_for_FSM M (L S)"
    using \<open>\<forall> y \<in> set (outputs M') . [(t_input (hd p), y)] \<in> output_completion_for_FSM M (L S)\<close> by blast

  then show ?thesis
    using \<open>[(t_input (hd p), t_output t')] \<in> LS M' q1'\<close> by blast
qed

end