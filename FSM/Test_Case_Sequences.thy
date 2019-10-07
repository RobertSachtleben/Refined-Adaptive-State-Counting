theory Test_Case_Sequences
imports State_Separator
begin

section \<open>Test Cases as Sequence Sets\<close>

(* TODO: find better suiting theory file *)
subsection \<open>Fault Domain\<close>
definition fault_domain :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ('a,'b) FSM_scheme set" where
  "fault_domain M m = { M' . inputs M' = inputs M \<and> outputs M' = outputs M \<and> size M' \<le> size M + m \<and> observable M' \<and> completely_specified M'}"



subsection \<open>State Separation Sets\<close>




(* TODO: relax completely_specified M' to the easier requirement that the LSin on M' are non-empty? *)
(*definition is_state_separation_set :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Input list set \<Rightarrow> bool" where
  "is_state_separation_set M q1 q2 S = (
    finite S
    \<and> (\<forall> s \<in> S . set s \<subseteq> set (inputs M))
    \<and> (\<forall> M'::('a,'b) FSM_scheme . ((\<forall> s \<in> S . set s \<subseteq> set (inputs M')) \<and> completely_specified M') \<longrightarrow> (*(inputs M' = inputs M \<and> outputs M' = outputs M \<and> completely_specified M') \<longrightarrow> *)
        (\<forall> q1' \<in> nodes M' . \<forall> q2' \<in> nodes M' .  ((LS\<^sub>i\<^sub>n M' q1' S \<subseteq> LS\<^sub>i\<^sub>n M q1 S) \<and> (LS\<^sub>i\<^sub>n M' q2' S \<subseteq> LS\<^sub>i\<^sub>n M q2 S)) \<longrightarrow> q1' \<noteq> q2'))
  )"
*)
(* TODO: LSin is incorrect, as it ignores adaptivity *)
(*
definition is_state_separation_set :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Input list set \<Rightarrow> bool" where
  "is_state_separation_set M q1 q2 S = (
    finite S
    \<and> (\<forall> M'::('a,'b) FSM_scheme . 
        (\<forall> q1' \<in> nodes M' . \<forall> q2' \<in> nodes M' .  ((LS\<^sub>i\<^sub>n M' q1' S \<noteq> {}) \<and> (LS\<^sub>i\<^sub>n M' q2' S \<noteq> {}) \<and> (LS\<^sub>i\<^sub>n M' q1' S \<subseteq> LS\<^sub>i\<^sub>n M q1 S) \<and> (LS\<^sub>i\<^sub>n M' q2' S \<subseteq> LS\<^sub>i\<^sub>n M q2 S)) \<longrightarrow> q1' \<noteq> q2'))
  )"
*)

definition is_state_separation_set :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "is_state_separation_set M q1 q2 S = (
    finite S
    \<and> ((LS M q1 \<inter> S) \<inter> (LS M q2 \<inter> S) = {})
    \<and> (\<forall> M'::('a,'b) FSM_scheme . 
        (\<forall> q1' \<in> nodes M' . \<forall> q2' \<in> nodes M' .  (((LS M' q1' \<inter> S \<noteq> {}) \<or> (LS M' q2' \<inter> S \<noteq> {})) \<and> (LS M' q1' \<inter> S \<subseteq> LS M q1 \<inter> S) \<and> (LS M' q2' \<inter> S \<subseteq> LS M q2 \<inter> S)) \<longrightarrow> LS M' q1' \<noteq> LS M' q2'))
  )"


definition state_separation_set_from_state_separator :: "('a + 'b, 'c) FSM_scheme \<Rightarrow> (Input \<times> Output) list set" where
  (*"state_separation_set_from_state_separator S = {map t_input p | p .path S (initial S) p \<and> \<not> isl (target p (initial S)) }"*)
  "state_separation_set_from_state_separator S = {p_io p | p .path S (initial S) p \<and> \<not> isl (target p (initial S)) }"

definition state_separation_set_from_state_separator_naive :: "('a + 'b, 'c) FSM_scheme \<Rightarrow> (Input \<times> Output) list list" where
  "state_separation_set_from_state_separator_naive S = map p_io (paths_up_to_length_or_condition S (initial S) (size S) (\<lambda> p . \<not> isl (target p (initial S))) [])"

value "calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2"
value "state_separation_set_from_state_separator_naive (the (calculate_state_separator_from_canonical_separator_naive M_ex_9 0 2))"





lemma state_separation_set_from_state_separator_finite :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  shows "finite (state_separation_set_from_state_separator S)"
proof -
  have "acyclic S"
    using assms unfolding is_state_separator_from_canonical_separator_def by blast
  show ?thesis 
    using acyclic_finite_paths[OF \<open>acyclic S\<close>] unfolding state_separation_set_from_state_separator_def by simp 
qed





lemma state_separation_set_from_state_separator_naive_set :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
  shows "set (state_separation_set_from_state_separator_naive S) = state_separation_set_from_state_separator S"
proof 
  have "acyclic S"
   and "deadlock_state S (Inr q1)"
       "deadlock_state S (Inr q2)"
       "(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)"
    using assms unfolding is_state_separator_from_canonical_separator_def by blast+

  show "state_separation_set_from_state_separator S \<subseteq> set (state_separation_set_from_state_separator_naive S)"
  proof 
    fix io assume "io \<in> state_separation_set_from_state_separator S"
    then obtain p where "io = p_io p"
                    and "path S (initial S) p"
                    and "\<not> isl (target p (initial S))"
      unfolding state_separation_set_from_state_separator_def by blast

    have "length p \<le> size S"
      using acyclic_path_length[OF \<open>acyclic S\<close>] \<open>path S (initial S) p\<close>
      using less_imp_le_nat by blast 
    moreover have "(\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> isl (target p' (initial S)))"
    proof -
      have "\<And> p' p''. p = p' @ p'' \<Longrightarrow> p'' \<noteq> [] \<Longrightarrow> isl (target p' (initial S))"
      proof -
        fix p' p'' assume "p = p' @ p''" and "p'' \<noteq> []"
        show "isl (target p' (initial S))"
        proof (rule ccontr)
          assume "\<not> isl (target p' (initial S))"
          then have "target p' (initial S) = Inr q1 \<or> target p' (initial S) = Inr q2"
            using \<open>(\<forall>q\<in>nodes S. q \<noteq> Inr q1 \<and> q \<noteq> Inr q2 \<longrightarrow> isl q \<and> \<not> deadlock_state S q)\<close>
            using \<open>p = p' @ p''\<close> \<open>path S (initial S) p\<close> nodes_path_initial by blast 
          then have "deadlock_state S (target p' (initial S))"
            using \<open>deadlock_state S (Inr q1)\<close> \<open>deadlock_state S (Inr q2)\<close> by presburger 

          obtain t p''' where "p'' = t#p'''" using \<open>p'' \<noteq> []\<close> list.exhaust_sel by blast 
          then have "path S (target p' (initial S)) (t#p''')"
            using \<open>path S (initial S) p\<close> \<open>p = p' @ p''\<close> by auto
          then have "path S (target p' (initial S)) [t]"
            by auto
          then have "t \<in> h S \<and> t_source t = (target p' (initial S))" 
            by auto
          then show "False"
            using \<open>deadlock_state S (target p' (initial S))\<close> unfolding deadlock_state.simps by blast
        qed
      qed
      then show ?thesis by blast
    qed

    ultimately show "io \<in> set (state_separation_set_from_state_separator_naive S)"
      unfolding state_separation_set_from_state_separator_naive_def 
      using paths_up_to_length_or_condition_path_set_nil[OF nodes.initial[of S], of "size S" "(\<lambda> p . \<not> isl (target p (initial S)))"] 
            \<open>path S (initial S) p\<close> \<open>\<not> isl (target p (initial S))\<close> \<open>io = p_io p\<close> by force
  qed

  show "set (state_separation_set_from_state_separator_naive S) \<subseteq> state_separation_set_from_state_separator S"
    unfolding state_separation_set_from_state_separator_naive_def state_separation_set_from_state_separator_def
    using paths_up_to_length_or_condition_path_set_nil[OF nodes.initial[of S], of "size S" "(\<lambda> p . \<not> isl (target p (initial S)))"] by auto

qed











lemma state_separation_set_from_state_separator :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 S"
      and "observable M"
      and "q1 \<in> nodes M"
      and "q2 \<in> nodes M"
      and "q1 \<noteq> q2"
  shows "is_state_separation_set M q1 q2 (state_separation_set_from_state_separator S)" (is "is_state_separation_set M q1 q2 ?SS")
proof -

  have "acyclic S"
    using assms(1) is_state_separator_from_canonical_separator_def by metis 

  have "(LS M q1 \<inter> ?SS) \<inter> (LS M q2 \<inter> ?SS) = {}"
  proof -
    have "\<And> io . io \<in> ?SS \<Longrightarrow> \<not>(io \<in> LS M q1 \<and> io \<in> LS M q2)"
    proof -
      fix io assume "io \<in> ?SS"
      then obtain p where "path S (initial S) p" and  "\<not> isl (target p (initial S))" and "p_io p = io"
        unfolding state_separation_set_from_state_separator_def by blast

      have "target p (initial S) \<in> nodes S"
        using \<open>path S (initial S) p\<close> path_target_is_node by metis
      then consider "target p (initial S) = Inr q1" | 
                    "target p (initial S) = Inr q2"
        using \<open>\<not> isl (target p (initial S))\<close> assms(1) unfolding is_state_separator_from_canonical_separator_def
        by blast 
      then show "\<not>(io \<in> LS M q1 \<and> io \<in> LS M q2)" 
      proof (cases)
        case 1
        have "p_io p \<in> LS M q1 - LS M q2"
          using canonical_separator_maximal_path_distinguishes_left[OF assms(1) \<open>path S (initial S) p\<close> 1 assms(2,3,4,5)] by assumption
        then show ?thesis using \<open>p_io p = io\<close> by blast
      next
        case 2
        have "p_io p \<in> LS M q2 - LS M q1"
          using canonical_separator_maximal_path_distinguishes_right[OF assms(1) \<open>path S (initial S) p\<close> 2 assms(2,3,4,5)] by assumption
        then show ?thesis using \<open>p_io p = io\<close> by blast
      qed
    qed
    then show ?thesis by blast
  qed

      
  

  have "finite ?SS"
    using state_separation_set_from_state_separator_finite[OF assms(1)] by assumption
  moreover have "(\<And> M'::('a,'b) FSM_scheme . \<And> q1' q2' . 
        q1' \<in> nodes M' \<Longrightarrow> q2' \<in> nodes M' \<Longrightarrow> (LS M' q1' \<inter> ?SS \<noteq> {} \<or> LS M' q2' \<inter> ?SS \<noteq> {}) \<Longrightarrow> (LS M' q1' \<inter> ?SS \<subseteq> LS M q1 \<inter> ?SS) \<Longrightarrow> (LS M' q2' \<inter> ?SS \<subseteq> LS M q2 \<inter> ?SS) \<Longrightarrow> LS M' q1' \<noteq> LS M' q2')"
  proof -
    fix M'::"('a,'b) FSM_scheme"
    fix q1' q2' assume "(LS M' q1' \<inter> ?SS \<noteq> {}) \<or> (LS M' q2' \<inter> ?SS \<noteq> {})"
                   and "(LS M' q1' \<inter> ?SS \<subseteq> LS M q1 \<inter> ?SS)" 
                   and "(LS M' q2' \<inter> ?SS \<subseteq> LS M q2 \<inter> ?SS)"

    show "LS M' q1' \<noteq> LS M' q2'"
    proof (cases "(LS M' q1' \<inter> ?SS \<noteq> {})")
      case True
      then obtain io1 where "io1 \<in> (LS M' q1' \<inter> ?SS)" by blast
      then have "io1 \<in> LS M q1 \<inter> ?SS"
        using \<open>(LS M' q1' \<inter> ?SS \<subseteq> LS M q1 \<inter> ?SS)\<close> by blast
      then have "io1 \<notin> LS M q2 \<inter> ?SS"
        using \<open>(LS M q1 \<inter> ?SS) \<inter> (LS M q2 \<inter> ?SS) = {}\<close> by blast
      then have "io1 \<notin> LS M' q2' \<inter> ?SS"
        using \<open>(LS M' q2' \<inter> ?SS \<subseteq> LS M q2 \<inter> ?SS)\<close> by blast
      then have "io1 \<notin> LS M' q2'"
        using \<open>io1 \<in> (LS M' q1' \<inter> ?SS)\<close> by blast
      moreover have "io1 \<in> LS M' q1'" 
        using \<open>io1 \<in> (LS M' q1' \<inter> ?SS)\<close> by blast
      ultimately show ?thesis by blast
    next
      case False
      then have "LS M' q2' \<inter> ?SS \<noteq> {}"
        using \<open>(LS M' q1' \<inter> ?SS \<noteq> {}) \<or> (LS M' q2' \<inter> ?SS \<noteq> {})\<close> by blast
      then obtain io2 where "io2 \<in> (LS M' q2' \<inter> ?SS)" by blast
      then have "io2 \<in> LS M q2 \<inter> ?SS"
        using \<open>(LS M' q2' \<inter> ?SS \<subseteq> LS M q2 \<inter> ?SS)\<close> by blast
      then have "io2 \<notin> LS M q1 \<inter> ?SS"
        using \<open>(LS M q1 \<inter> ?SS) \<inter> (LS M q2 \<inter> ?SS) = {}\<close> by blast
      then have "io2 \<notin> LS M' q1' \<inter> ?SS"
        using \<open>(LS M' q1' \<inter> ?SS \<subseteq> LS M q1 \<inter> ?SS)\<close> by blast
      then have "io2 \<notin> LS M' q1'"
        using \<open>io2 \<in> (LS M' q2' \<inter> ?SS)\<close> by blast
      moreover have "io2 \<in> LS M' q2'" 
        using \<open>io2 \<in> (LS M' q2' \<inter> ?SS)\<close> by blast
      ultimately show ?thesis by blast
    qed
  qed

  ultimately show ?thesis 
    unfolding is_state_separation_set_def using \<open>(LS M q1 \<inter> ?SS) \<inter> (LS M q2 \<inter> ?SS) = {}\<close> by blast
qed




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