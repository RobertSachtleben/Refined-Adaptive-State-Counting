theory Adaptive_Test_Case
imports State_Separator 
begin

(* TODO: move *)
lemma from_FSM_completely_specified : 
  assumes "q \<in> nodes M"
  and     "completely_specified M"
shows "completely_specified (from_FSM M q)"
  using from_FSM_h[OF assms(1)] from_FSM_simps(2)[of M q] from_FSM_nodes[OF assms(1)] unfolding completely_specified.simps 
  by (metis (no_types, hide_lams) assms(2) completely_specified_alt_def from_FSM_h from_FSM_simps(2) from_FSM_transition_initial from_from  fst_eqD set_rev_mp snd_eqD)

lemma from_FSM_single_input : 
  assumes "q \<in> nodes M"
  and     "single_input M"
shows "single_input (from_FSM M q)"
  using from_FSM_h[OF assms(1)] unfolding single_input.simps 
  by (meson assms(2) rev_subsetD single_input.simps)

lemma from_FSM_acyclic :
  assumes "q \<in> nodes M"
  and     "acyclic M"
shows "acyclic (from_FSM M q)"
  using acyclic_paths_from_nodes[OF assms(2) from_FSM_path[OF assms(1)], of "initial (from_FSM M q)"] unfolding acyclic.simps by blast

lemma from_FSM_observable :
  assumes "q \<in> nodes M"
  and     "observable M"
shows "observable (from_FSM M q)"
  using assms(2) from_FSM_h[OF assms(1)] unfolding observable.simps by blast





definition is_ATC :: "('a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_ATC M = (single_input M \<and> acyclic M \<and> observable M)"

lemma is_ATC_from :
  assumes "t \<in> h A"
  and     "is_ATC A"
shows "is_ATC (from_FSM A (t_target t))"
  using from_FSM_acyclic[OF wf_transition_target[OF assms(1)]] 
        from_FSM_single_input[OF wf_transition_target[OF assms(1)]]
        from_FSM_observable[OF wf_transition_target[OF assms(1)]]
        assms(2)
  unfolding is_ATC_def
  by blast




(* FSM A passes ATC A if and only if the parallel execution of M and A does not visit a fail_state in A and M produces no output not allowed in A *)
fun pass_ATC' :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> nat \<Rightarrow> bool" where
  "pass_ATC' M A fail_states 0 = (\<not> (initial A \<in> fail_states))" |
  "pass_ATC' M A fail_states (Suc k) = ((\<not> (initial A \<in> fail_states)) \<and> (case find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) of
    None \<Rightarrow> True |
    Some x \<Rightarrow> \<forall> t \<in> h M . (t_input t = x \<and> t_source t = initial M) \<longrightarrow> (\<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<and> t_output t' = t_output t \<and> pass_ATC' (from_FSM M (t_target t)) (from_FSM A (t_target t')) fail_states k)))"

fun pass_ATC :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> bool" where
  "pass_ATC M A fail_states = pass_ATC' M A fail_states (size A)"

fun pass_separator_ATC :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pass_separator_ATC M S q1 q2 = pass_ATC (from_FSM M q1) S {Inr q2}"

value "the (calculate_state_separator_from_s_states M_ex_H 1 4)"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 4)) 1 4"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 4)) 4 1"

value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 4}"
value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 1}"
value "pass_ATC (from_FSM M_ex_H 4) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 4}"
value "pass_ATC (from_FSM M_ex_H 4) (the (calculate_state_separator_from_s_states M_ex_H 1 4)) {Inr 1}"

value "the (calculate_state_separator_from_s_states M_ex_H 1 3)"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 3)) 1 3"
value "pass_separator_ATC M_ex_H (the (calculate_state_separator_from_s_states M_ex_H 1 3)) 3 1"

value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 3}"
value "pass_ATC (from_FSM M_ex_H 1) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 1}"
value "pass_ATC (from_FSM M_ex_H 3) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 3}"
value "pass_ATC (from_FSM M_ex_H 3) (the (calculate_state_separator_from_s_states M_ex_H 1 3)) {Inr 1}"


lemma pass_ATC'_initial :
  assumes "pass_ATC' M A FS k"
  shows "initial A \<notin> FS"
using assms by (cases k; auto) 


(* TODO: move *)
lemma observable_language_next :
  assumes "io#ios \<in> LS M (t_source t)"
  and     "observable M"
  and     "t \<in> h M"
  and     "t_input t = fst io"
  and     "t_output t = snd io"
shows "ios \<in> L (from_FSM M (t_target t))"
proof -
  obtain p where "path M (t_source t) p" and "p_io p = io#ios"
    using assms(1)
  proof -
    assume a1: "\<And>p. \<lbrakk>path M (t_source t) p; p_io p = io # ios\<rbrakk> \<Longrightarrow> thesis"
    obtain pps :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
      "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (pps x0 x1 x2) \<and> path x2 x1 (pps x0 x1 x2))"
      by moura
    then have "\<exists>ps. path M (t_source t) ps \<and> p_io ps = io # ios"
      using assms(1) by auto
    then show ?thesis
      using a1 by meson
  qed 
  then obtain t' p' where "p = t' # p'"
    by auto
  then have "t' \<in> h M" and "t_source t' = t_source t" and "t_input t' = fst io" and "t_output t' = snd io" 
    using \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "t = t'"
    using assms(2,3,4,5) unfolding observable.simps
    by (metis (no_types, hide_lams) prod.expand) 

  then have "path M (t_target t) p'" and "p_io p' = ios"
    using \<open>p = t' # p'\<close> \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "path (from_FSM M (t_target t)) (initial (from_FSM M (t_target t))) p'"
    using from_FSM_path_initial[OF wf_transition_target[OF \<open>t \<in> h M\<close>]] by auto

  then show ?thesis using \<open>p_io p' = ios\<close> by auto
qed








lemma pass_ATC'_io :
  assumes "pass_ATC' M A FS k"
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM"
  and     "length (io@[ioA]) \<le> k" 
shows "io@[ioM] \<in> L A"
and   "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
proof -
  have "io@[ioM] \<in> L A \<and> io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    using assms proof (induction k arbitrary: io A M)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    then show ?case proof (cases io)
      case Nil
      
      obtain tA where "tA \<in> h A"
                  and "t_source tA = initial A"
                  and "t_input tA = fst ioA"
                  and "t_output tA = snd ioA"
        using Nil \<open>io@[ioA] \<in> L A\<close> by auto
      then have "fst ioA \<in> set (inputs A)"
        by auto

      have *: "\<And> x . x \<in> set (inputs A) \<Longrightarrow> \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<Longrightarrow> x = fst ioA"
        using \<open>is_ATC A\<close> \<open>tA \<in> h A\<close> unfolding is_ATC_def single_input.simps
        using \<open>t_source tA = initial A\<close> \<open>t_input tA = fst ioA\<close>
        by metis 

      have find_scheme : "\<And> P xs x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> (\<And> x' . x' \<in> set xs \<Longrightarrow> P x' \<Longrightarrow> x' = x) \<Longrightarrow> find P xs = Some x"
        by (metis find_None_iff find_condition find_set option.exhaust)

      have "find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) = Some (fst ioA)"
        using find_scheme[OF \<open>fst ioA \<in> set (inputs A)\<close>, of "\<lambda>x . \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A"]
        using * \<open>tA \<in> h A\<close> \<open>t_source tA = initial A\<close> by blast

      
      then have ***: "\<And> tM . tM \<in> h M \<Longrightarrow> t_input tM = fst ioA \<Longrightarrow> t_source tM = initial M \<Longrightarrow>
        (\<exists> tA \<in> h A .
            t_input tA = fst ioA \<and>
            t_source tA = initial A \<and> t_output tA = t_output tM \<and> pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k)"
        using Suc.prems(1) unfolding pass_ATC'.simps by auto

      obtain tM where "tM \<in> h M"
                  and "t_source tM = initial M"
                  and "t_input tM = fst ioA"
                  and "t_output tM = snd ioM"
        using Nil \<open>io@[ioM] \<in> L M\<close> \<open>fst ioA = fst ioM\<close> by auto

      then obtain tA' where "tA' \<in> h A"
                       and "t_input tA' = fst ioM"
                       and "t_source tA' = initial A" 
                       and "t_output tA' = snd ioM" 
                       and "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k"
        using ***[of tM] \<open>fst ioA = fst ioM\<close> by auto

      then have "path A (initial A) [tA']"
        using single_transition_path[OF \<open>tA' \<in> h A\<close>] by auto
      moreover have "p_io [tA'] = [ioM]"
        using \<open>t_input tA' = fst ioM\<close> \<open>t_output tA' = snd ioM\<close> by auto
      ultimately have "[ioM] \<in> LS A (initial A)"
        unfolding LS.simps
        by (metis (mono_tags, lifting) mem_Collect_eq) 
      then have "io @ [ioM] \<in> LS A (initial A)"
        using Nil by auto

      have "target [tA'] (initial A) = t_target tA'"
        by auto
      then have "t_target tA' \<in> io_targets A [ioM] (initial A)"
        unfolding io_targets.simps 
        using \<open>path A (initial A) [tA']\<close> \<open>p_io [tA'] = [ioM]\<close>
        by (metis (mono_tags, lifting) mem_Collect_eq)
      then have "io_targets A (io @ [ioM]) (initial A) = {t_target tA'}"
        using observable_io_targets[OF _ \<open>io @ [ioM] \<in> LS A (initial A)\<close>] \<open>is_ATC A\<close> Nil
        unfolding is_ATC_def
        by (metis append_self_conv2 singletonD) 
      moreover have "t_target tA' \<notin> FS"
        using \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k\<close>
        by (metis from_FSM_simps(1) pass_ATC'_initial) 
      ultimately have "io_targets A (io @ [ioM]) (initial A) \<inter> FS = {}"
        by auto
      
      then show ?thesis
        using \<open>io @ [ioM] \<in> LS A (initial A)\<close> by auto
    next
      case (Cons io' io'')

      have "[io'] \<in> L A"
        using Cons \<open>io@[ioA] \<in> L A\<close>
        by (metis append.left_neutral append_Cons language_prefix)


      then obtain tA where "tA \<in> h A"
                  and "t_source tA = initial A"
                  and "t_input tA = fst io'"
                  and "t_output tA = snd io'"
        by auto
      then have "fst io' \<in> set (inputs A)"
        by auto

      have *: "\<And> x . x \<in> set (inputs A) \<Longrightarrow> \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<Longrightarrow> x = fst io'"
        using \<open>is_ATC A\<close> \<open>tA \<in> h A\<close> unfolding is_ATC_def single_input.simps
        using \<open>t_source tA = initial A\<close> \<open>t_input tA = fst io'\<close>
        by metis 

      have find_scheme : "\<And> P xs x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> (\<And> x' . x' \<in> set xs \<Longrightarrow> P x' \<Longrightarrow> x' = x) \<Longrightarrow> find P xs = Some x"
        by (metis find_None_iff find_condition find_set option.exhaust)

      have "find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) = Some (fst io')"
        using find_scheme[OF \<open>fst io' \<in> set (inputs A)\<close>, of "\<lambda>x . \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A"]
        using * \<open>tA \<in> h A\<close> \<open>t_source tA = initial A\<close> by blast

      
      then have ***: "\<And> tM . tM \<in> h M \<Longrightarrow> t_input tM = fst io' \<Longrightarrow> t_source tM = initial M \<Longrightarrow>
        (\<exists> tA \<in> h A .
            t_input tA = fst io' \<and>
            t_source tA = initial A \<and> t_output tA = t_output tM \<and> pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k)"
        using Suc.prems(1) unfolding pass_ATC'.simps by auto

      have "[io'] \<in> L M"
        using Cons \<open>io@[ioM] \<in> L M\<close>
        by (metis append.left_neutral append_Cons language_prefix)
      then obtain tM where "tM \<in> h M"
                  and "t_source tM = initial M"
                  and "t_input tM = fst io'"
                  and "t_output tM = snd io'"
        by auto

      
      then obtain tA' where "tA' \<in> h A"
                       and "t_input tA' = fst io'"
                       and "t_source tA' = initial A" 
                       and "t_output tA' = snd io'" 
                       and "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k"
        using ***[of tM] by auto
      
      then have "tA = tA'"
        using \<open>is_ATC A\<close>
        unfolding is_ATC_def observable.simps
        by (metis \<open>tA \<in> set (wf_transitions A)\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> \<open>t_source tA = initial A\<close> prod.collapse) 
      
      then have "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k"
        using \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA')) FS k\<close> by auto

      





      
      have "set (inputs (from_FSM A (t_target tA))) \<subseteq> set (inputs (from_FSM M (t_target tM)))"
        by (simp add: Suc.prems(4) from_FSM_simps(2))

      have "length (io'' @ [ioA]) \<le> k"
        using Cons \<open>length (io @ [ioA]) \<le> Suc k\<close> by auto

      have "(io' # (io''@[ioA])) \<in> LS A (t_source tA)"
        using \<open>t_source tA = initial A\<close> \<open>io@[ioA] \<in> L A\<close> Cons by auto
      have "io'' @ [ioA] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))"
        using observable_language_next[OF \<open>(io' # (io''@[ioA])) \<in> LS A (t_source tA)\<close>]
              \<open>is_ATC A\<close> \<open>tA \<in> h A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close>
        using is_ATC_def by blast 

      have "(io' # (io''@[ioM])) \<in> LS M (t_source tM)"
        using \<open>t_source tM = initial M\<close> \<open>io@[ioM] \<in> L M\<close> Cons by auto
      have "io'' @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))"
        using observable_language_next[OF \<open>(io' # (io''@[ioM])) \<in> LS M (t_source tM)\<close>]
              \<open>observable M\<close> \<open>tM \<in> h M\<close> \<open>t_input tM = fst io'\<close> \<open>t_output tM = snd io'\<close>
        by blast
        
      have "observable (from_FSM M (t_target tM))"
        using \<open>observable M\<close> \<open>tM \<in> h M\<close>
        by (meson from_FSM_observable wf_transition_target) 
      
      have "io'' @ [ioM] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))"
       and "io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA))) \<inter> FS = {}" 
        using Suc.IH[OF \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k\<close>
                        is_ATC_from[OF \<open>tA \<in> h A\<close> \<open>is_ATC A\<close>]
                        \<open>observable (from_FSM M (t_target tM))\<close>
                        \<open>set (inputs (from_FSM A (t_target tA))) \<subseteq> set (inputs (from_FSM M (t_target tM)))\<close>
                        \<open>io'' @ [ioA] \<in> LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA)))\<close>
                        \<open>io'' @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))\<close>
                        \<open>fst ioA = fst ioM\<close>
                        \<open>length (io'' @ [ioA]) \<le> k\<close>]
        by blast+

      then obtain pA where "path (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))) pA" and "p_io pA = io'' @ [ioM]"
        by auto

      have "path A (initial A) (tA#pA)"
        using \<open>path (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))) pA\<close> \<open>tA \<in> h A\<close> 
        by (metis \<open>t_source tA = initial A\<close> cons from_FSM_path_initial wf_transition_target)
      moreover have "p_io (tA#pA) = io' # io'' @ [ioM]"
        using \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close> \<open>p_io pA = io'' @ [ioM]\<close> by auto
      ultimately have "io' # io'' @ [ioM] \<in> L A"
        unfolding LS.simps
        by (metis (mono_tags, lifting) mem_Collect_eq) 
      then have "io @ [ioM] \<in> L A"
        using Cons by auto

      have "observable A"
        using Suc.prems(2) is_ATC_def by blast

      (* TODO: maybe move *)
      have ex_scheme: "\<And> xs P x . (\<exists>! x' . x' \<in> set xs \<and> P x') \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> set (filter P xs) = {x}"
        by force
        
      have "set (filter (\<lambda>t. t_source t = initial A \<and> t_input t = fst io' \<and> t_output t = snd io') (wf_transitions A)) = {tA}"
        using ex_scheme[of "wf_transitions A" "(\<lambda> t' . t_source t' = initial A \<and> t_input t' = fst io' \<and> t_output t' = snd io')", OF
                          observable_transition_unique[OF \<open>observable A\<close> \<open>tA \<in> h A\<close> \<open>t_source tA = initial A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close>]]
        using \<open>tA \<in> h A\<close> \<open>t_source tA = initial A\<close> \<open>t_input tA = fst io'\<close> \<open>t_output tA = snd io'\<close>
        by blast


      have concat_scheme: "\<And> f g h xs x. set (filter h xs) = {x} \<Longrightarrow> set (concat (map f (map g (filter h xs)))) = set (f (g x))"
      proof -
        {
          fix x :: 'a 
          and xs h 
          and g :: "'a \<Rightarrow> 'b"
          and f :: "'b \<Rightarrow> 'c list"
          assume "set (filter h xs) = {x}"
          then have "\<And> y . y \<in> set (map f (map g (filter h xs))) \<Longrightarrow> y = f (g x)"
            by auto
          then have "\<And> y . y \<in> set (concat (map f (map g (filter h xs)))) \<Longrightarrow> y \<in> set (f (g x))"
            by fastforce
          moreover have "\<And> y . y \<in> set (f (g x)) \<Longrightarrow> y \<in> set (concat (map f (map g (filter h xs))))"
          proof -
            fix y :: 'c
            assume a1: "y \<in> set (f (g x))"
            have "set (filter h xs) \<noteq> {}"
              using \<open>set (filter h xs) = {x}\<close> by fastforce
            then have "filter h xs \<noteq> []"
              by blast
            then show "y \<in> set (concat (map f (map g (filter h xs))))"
              using a1 by (metis (no_types) UN_I \<open>\<And>y. y \<in> set (map f (map g (filter h xs))) \<Longrightarrow> y = f (g x)\<close> ex_in_conv list.map_disc_iff set_concat set_empty)
          qed
          ultimately have "set (concat (map f (map g (filter h xs)))) = set (f (g x))" by blast
        }
        thus "\<And> f g h xs x. set (filter h xs) = {x} \<Longrightarrow> set (concat (map f (map g (filter h xs)))) = set (f (g x))"
          by simp 
      qed
        

      have "set (io_targets_list A (io' # (io'' @ [ioM])) (initial A)) = set (io_targets_list A (io'' @ [ioM]) (t_target tA))"
        unfolding io_targets_list.simps 
        using concat_scheme[OF \<open>set (filter (\<lambda>t. t_source t = initial A \<and> t_input t = fst io' \<and> t_output t = snd io') (wf_transitions A)) = {tA}\<close>]
        by metis

      then have "io_targets A (io' # (io'' @ [ioM])) (initial A) = io_targets A (io'' @ [ioM]) (t_target tA)"
        using nodes.initial[of A] wf_transition_target[OF \<open>tA \<in> h A\<close>]
        by (metis io_targets_from_list) 

      then have "io_targets A (io' # (io'' @ [ioM])) (initial A) = io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA)))"
        unfolding io_targets.simps using from_FSM_path_initial[OF wf_transition_target[OF \<open>tA \<in> h A\<close>]]
        by auto

      then have "io_targets A (io @ [ioM]) (initial A) \<inter> FS = {}"
        using \<open>io_targets (from_FSM A (t_target tA)) (io'' @ [ioM]) (initial (from_FSM A (t_target tA))) \<inter> FS = {}\<close> Cons by auto
        
      show ?thesis
        using \<open>io @ [ioM] \<in> L A\<close> \<open>io_targets A (io @ [ioM]) (initial A) \<inter> FS = {}\<close> by simp
    qed
  qed

  thus "io@[ioM] \<in> L A"
  and  "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    by auto
qed



lemma pass_ATC_io :
  assumes "pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM" 
shows "io@[ioM] \<in> L A"
and   "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
proof -

  have "acyclic A"
    using \<open>is_ATC A\<close> is_ATC_def by blast 

  have "length (io @ [ioA]) \<le> (size A)"
    using \<open>io@[ioA] \<in> L A\<close> unfolding LS.simps using acyclic_path_length[OF \<open>acyclic A\<close>]
    by force 
  
  show "io@[ioM] \<in> L A"
  and  "io_targets A (io@[ioM]) (initial A) \<inter> FS = {}"
    using pass_ATC'_io[OF _ assms(2-7) \<open>length (io @ [ioA]) \<le> (size A)\<close>]
    using assms(1) by simp+
qed


lemma pass_ATC_io_explicit_io_tuple :
  assumes "pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "io@[(x,y)] \<in> L A"
  and     "io@[(x,y')] \<in> L M" 
shows "io@[(x,y')] \<in> L A"
and   "io_targets A (io@[(x,y')]) (initial A) \<inter> FS = {}"
  apply (metis pass_ATC_io(1) assms fst_conv)
  by (metis pass_ATC_io(2) assms fst_conv)





lemma pass_ATC_io_fail_fixed_io :
  assumes "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "io@[ioA] \<in> L A"
  and     "io@[ioM] \<in> L M"
  and     "fst ioA = fst ioM" 
  and     "io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}"
shows "\<not>pass_ATC M A FS" 
proof -
  consider (a) "io@[ioM] \<notin> L A" |
           (b) "io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}"
    using assms(7) by blast 
  then show ?thesis proof (cases)
    case a
    then show ?thesis using pass_ATC_io(1)[OF _ assms(1-6)] by blast
  next
    case b
    then show ?thesis using pass_ATC_io(2)[OF _ assms(1-6)] by blast
  qed
qed



(* TODO: move *)
(* TODO: add version for paths *)
lemma language_state_prepend_transition : 
  assumes "io \<in> LS (from_FSM A (t_target t)) (initial (from_FSM A (t_target t)))"
  and     "t \<in> h A"
shows "p_io [t] @ io \<in> LS A (t_source t)"
proof -
  obtain p where "path (from_FSM A (t_target t)) (initial (from_FSM A (t_target t))) p"
           and   "p_io p = io"
    using assms(1) unfolding LS.simps by blast
  then have "path A (t_target t) p"
    using from_FSM_path_initial[OF wf_transition_target[OF assms(2)]] by auto
  then have "path A (t_source t) (t # p)"
    using assms(2) by auto
  then show ?thesis 
    using \<open>p_io p = io\<close> unfolding LS.simps
    by force 
qed


(* TODO: understand why path_append_elim works better(?) with obtains instead of shows *)

lemma language_state_split :
  assumes "io1 @ io2 \<in> LS M q1"
  obtains  p1 p2 where "path M q1 p1" and "path M (target p1 q1) p2"  and "p_io p1 = io1" and "p_io p2 = io2"
proof -
  obtain p12 where "path M q1 p12" and "p_io p12 = io1 @ io2"
    using assms unfolding LS.simps by auto

  let ?p1 = "take (length io1) p12"
  let ?p2 = "drop (length io1) p12"

  have "p12 = ?p1 @ ?p2" 
    by auto
  then have "path M q1 (?p1 @ ?p2)"
    using \<open>path M q1 p12\<close> by auto

  have "path M q1 ?p1" and "path M (target ?p1 q1) ?p2"
    using path_append_elim[OF \<open>path M q1 (?p1 @ ?p2)\<close>] by blast+
  moreover have "p_io ?p1 = io1"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis append_eq_conv_conj take_map)
  moreover have "p_io ?p2 = io2"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis (no_types) \<open>p_io p12 = io1 @ io2\<close> append_eq_conv_conj drop_map) 
  ultimately show ?thesis using that by blast
qed
    

(* TODO: move *)
(* TODO: generalize ? *)
lemma observable_io_targets_language :
  assumes "io1 @ io2 \<in> LS M q1"
  and     "observable M"
  and     "q2 \<in> io_targets M io1 q1"
shows "io2 \<in> LS M q2" 
proof -
  obtain p1 p2 where "path M q1 p1" and "path M (target p1 q1) p2"  and "p_io p1 = io1" and "p_io p2 = io2"
    using language_state_split[OF assms(1)] by blast
  then have "io1 \<in> LS M q1" and "io2 \<in> LS M (target p1 q1)"
    by auto
  
  have "target p1 q1 \<in> io_targets M io1 q1"
    using \<open>path M q1 p1\<close> \<open>p_io p1 = io1\<close>
    unfolding io_targets.simps by blast
  then have "target p1 q1 = q2"
    using observable_io_targets[OF assms(2) \<open>io1 \<in> LS M q1\<close>]
    by (metis assms(3) singletonD) 
  then show ?thesis
    using \<open>io2 \<in> LS M (target p1 q1)\<close> by auto
qed
  





lemma io_targets_next :
  assumes "t \<in> h M"
  shows "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
unfolding io_targets.simps
proof 
  fix q assume "q \<in> {target p (t_target t) |p. path M (t_target t) p \<and> p_io p = io}"
  then obtain p where "path M (t_target t) p \<and> p_io p = io \<and> target p (t_target t) = q"
    by auto
  then have "path M (t_source t) (t#p) \<and> p_io (t#p) = p_io [t] @ io \<and> target (t#p) (t_source t) = q"
    using FSM.path.cons[OF assms] by auto
  then show "q \<in> {target p (t_source t) |p. path M (t_source t) p \<and> p_io p = p_io [t] @ io}"
    by blast
qed
  



lemma observable_io_targets_next :
  assumes "observable M"
  and     "t \<in> h M"
shows "io_targets M (p_io [t] @ io) (t_source t) = io_targets M io (t_target t)" 
proof 
  show "io_targets M (p_io [t] @ io) (t_source t) \<subseteq> io_targets M io (t_target t)"
  proof 
    fix q assume "q \<in> io_targets M (p_io [t] @ io) (t_source t)"
    then obtain p where "q = target p (t_source t)" and "path M (t_source t) p" and "p_io p = p_io [t] @ io"
      unfolding io_targets.simps by blast
    then have "q = t_target (last p)" unfolding target.simps visited_states.simps
      using last_map by auto 

    obtain t' p' where "p = t' # p'"
      using \<open>p_io p = p_io [t] @ io\<close> by auto
    then have "t' \<in> h M" and "t_source t' = t_source t"
      using \<open>path M (t_source t) p\<close> by auto
    moreover have "t_input t' = t_input t" and "t_output t' = t_output t"
      using \<open>p = t' # p'\<close> \<open>p_io p = p_io [t] @ io\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> h M\<close> \<open>observable M\<close> unfolding observable.simps
      by (meson prod.expand) 

    then have "path M (t_target t) p'"
      using \<open>path M (t_source t) p\<close> \<open>p = t' # p'\<close> by auto
    moreover have "p_io p' = io"
      using \<open>p_io p = p_io [t] @ io\<close> \<open>p = t' # p'\<close> by auto
    moreover have "q = target p' (t_target t)"
      using \<open>q = target p (t_source t)\<close> \<open>p = t' # p'\<close> \<open>t' = t\<close> by auto
    ultimately show "q \<in> io_targets M io (t_target t)"
      by auto
  qed

  show "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
    using io_targets_next[OF assms(2)] by assumption
qed
  






lemma pass_ATC'_io_fail :
  assumes "\<not>pass_ATC' M A FS k "
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
shows "initial A \<in> FS \<or> (\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          (*\<and> length (io@[ioA]) \<le> k*)
                          \<and> (io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}))"
using assms proof (induction k arbitrary: M A)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case proof (cases "initial A \<in> FS")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain x where "find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) = Some x"
      using Suc.prems(1) unfolding pass_ATC'.simps
      by fastforce 
    then have "pass_ATC' M A FS (Suc k) = (\<forall>t\<in>set (wf_transitions M).
                                            t_input t = x \<and> t_source t = initial M \<longrightarrow>
                                            (\<exists>t'\<in>set (wf_transitions A).
                                                t_input t' = x \<and>
                                                t_source t' = initial A \<and>
                                                t_output t' = t_output t \<and>
                                                pass_ATC' (from_FSM M (t_target t)) (from_FSM A (t_target t')) FS k))"
      using False unfolding pass_ATC'.simps by fastforce
    then obtain tM where "tM \<in> h M" 
                   and   "t_input tM = x" 
                   and   "t_source tM = initial M"
                   and *:"\<not>(\<exists>t'\<in>set (wf_transitions A).
                            t_input t' = x \<and>
                            t_source t' = initial A \<and>
                            t_output t' = t_output tM \<and>
                            pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target t')) FS k)" 
      using Suc.prems(1) by blast

    obtain tA where "tA \<in> h A" and "t_input tA = x" and "t_source tA = initial A"
      using find_condition[OF \<open>find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) = Some x\<close>] by blast

    let ?ioA = "(x, t_output tA)"
    let ?ioM = "(x, t_output tM)"

    have "[?ioA] \<in> L A"
      using \<open>tA \<in> h A\<close> \<open>t_input tA = x\<close> \<open>t_source tA = initial A\<close> unfolding LS.simps
    proof -
      have "[(x, t_output tA)] = p_io [tA]"
        by (simp add: \<open>t_input tA = x\<close>)
      then have "\<exists>ps. [(x, t_output tA)] = p_io ps \<and> path A (initial A) ps"
        by (metis (no_types) \<open>tA \<in> set (wf_transitions A)\<close> \<open>t_source tA = initial A\<close> single_transition_path)
      then show "[(x, t_output tA)] \<in> {p_io ps |ps. path A (initial A) ps}"
        by blast
    qed

    (* TODO: extract *)
    have "[?ioM] \<in> L M"
      using \<open>tM \<in> h M\<close> \<open>t_input tM = x\<close> \<open>t_source tM = initial M\<close> unfolding LS.simps
    proof -
      have "[(x, t_output tM)] = p_io [tM]"
        by (simp add: \<open>t_input tM = x\<close>)
      then have "\<exists>ps. [(x, t_output tM)] = p_io ps \<and> path M (initial M) ps"
        by (metis (no_types) \<open>tM \<in> set (wf_transitions M)\<close> \<open>t_source tM = initial M\<close> single_transition_path)
      then show "[(x, t_output tM)] \<in> {p_io ps |ps. path M (initial M) ps}"
        by blast
    qed

    have "fst ?ioA = fst ?ioM"
      by auto

    consider (a) "\<not>(\<exists>t'\<in>set (wf_transitions A).
                            t_input t' = x \<and>
                            t_source t' = initial A \<and>
                            t_output t' = t_output tM)" |
             (b) "\<exists>t'\<in>set (wf_transitions A).
                            t_input t' = x \<and>
                            t_source t' = initial A \<and>
                            t_output t' = t_output tM \<and>
                            \<not>(pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target t')) FS k)"
      using * by blast
       
    then show ?thesis proof cases
      case a

      have "[?ioM] \<notin> L A"
      proof 
        assume "[?ioM] \<in> L A"
        then obtain p where "path A (initial A) p" and "p_io p = [?ioM]" (* TODO: extract *)
          unfolding LS.simps
        proof -
          assume a1: "[(x, t_output tM)] \<in> {p_io p |p. path A (initial A) p}"
          assume a2: "\<And>p. \<lbrakk>path A (initial A) p; p_io p = [(x, t_output tM)]\<rbrakk> \<Longrightarrow> thesis"
          have "\<exists>ps. [(x, t_output tM)] = p_io ps \<and> path A (initial A) ps"
            using a1 by force
          then show ?thesis
            using a2 by (metis (lifting))
        qed 
        then obtain t where "p = [t]" and "t \<in> h A" and "t_source t = initial A" and "t_input t = x" and "t_output t = t_output tM"
          by auto
        then show "False" 
          using a by blast
      qed

      then have "\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> io@[ioM] \<notin> L A"
        using \<open>[?ioA] \<in> L A\<close> \<open>[?ioM] \<in> L M\<close> \<open>fst ?ioA = fst ?ioM\<close>
        by (metis append_Nil)
      thus ?thesis by blast
        
    next
      case b
      then obtain t' where "t' \<in> h A"
                       and "t_input t' = x"
                       and "t_source t' = initial A"
                       and "t_output t' = t_output tM"
                       and "\<not>(pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target t')) FS k)"
        by blast

      have "set (inputs (from_FSM A (t_target t'))) \<subseteq> set (inputs (from_FSM M (t_target tM)))"
        using \<open>set (inputs A) \<subseteq> set (inputs M)\<close> 
        by (simp add: from_FSM_simps(2)) 

      have "observable A"
        using \<open>is_ATC A\<close> unfolding is_ATC_def by auto

      consider (b1) "initial (from_FSM A (t_target t')) \<in> FS" |
               (b2) "(\<exists>io ioA ioM.
                        io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<and>
                        io @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM))) \<and>
                        fst ioA = fst ioM \<and>
                        (io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or>
                        io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {}))"
        using Suc.IH[OF \<open>\<not>(pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target t')) FS k)\<close>
                        is_ATC_from[OF \<open>t' \<in> h A\<close> \<open>is_ATC A\<close>]
                        from_FSM_observable[OF wf_transition_target[OF \<open>tM \<in> h M\<close>] \<open>observable M\<close>]
                        \<open>set (inputs (from_FSM A (t_target t'))) \<subseteq> set (inputs (from_FSM M (t_target tM)))\<close> ] 
        by blast              
      then show ?thesis proof cases
        case b1 (* analogous to case a *)

        have "p_io [t'] = [(x, t_output tM)]"
          using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close>
          by auto
        moreover have "target [t'] (initial A) = t_target t'"
          using \<open>t_source t' = initial A\<close> by auto
        ultimately have "t_target t' \<in> io_targets A [?ioM] (initial A)"
          unfolding io_targets.simps
          using single_transition_path[OF \<open>t' \<in> h A\<close>]
          by (metis (mono_tags, lifting) \<open>t_source t' = initial A\<close> mem_Collect_eq)
        then have "initial (from_FSM A (t_target t')) \<in> io_targets A [?ioM] (initial A)"
          by (simp add: from_FSM_simps(1))
        then have "io_targets A ([] @ [?ioM]) (initial A) \<inter> FS \<noteq> {}"
          using b1 by (metis IntI append_Nil empty_iff) 

        then have "\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> io_targets A (io @ [ioM]) (initial A) \<inter> FS \<noteq> {}"
          using \<open>[?ioA] \<in> L A\<close> \<open>[?ioM] \<in> L M\<close> \<open>fst ?ioA = fst ?ioM\<close> 
          using append_Nil by metis
        
        then show ?thesis by blast

      next
        case b2 (* obtain io ioA ioM and prepend (x,t_output tM) *)

        then obtain io ioA ioM where
              "io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t')))"
          and "io @ [ioM] \<in> LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM)))"
          and "fst ioA = fst ioM"
          and "(io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or> io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {})"
          by blast

        have "(?ioM # io) @ [ioA] \<in> L A"
          using language_state_prepend_transition[OF \<open>io @ [ioA] \<in> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t')))\<close> \<open>t' \<in> h A\<close>]
          using \<open>t_input t' = x\<close> \<open>t_source t' = initial A\<close> \<open>t_output t' = t_output tM\<close>
          by simp

        moreover have "(?ioM # io) @ [ioM] \<in> L M"
          using language_state_prepend_transition[OF \<open>io @ [ioM] \<in> L (from_FSM M (t_target tM))\<close> \<open>tM \<in> h M\<close>]
          using \<open>t_input tM = x\<close> \<open>t_source tM = initial M\<close>
          by simp

        moreover have "((?ioM # io) @ [ioM] \<notin> L A \<or> io_targets A ((?ioM # io) @ [ioM]) (initial A) \<inter> FS \<noteq> {})"
        proof -
          consider (f1) "io @ [ioM] \<notin> L (from_FSM A (t_target t'))" |
                   (f2) "io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {}"
            using \<open>(io @ [ioM] \<notin> LS (from_FSM A (t_target t')) (initial (from_FSM A (t_target t'))) \<or> io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t'))) \<inter> FS \<noteq> {})\<close>
            by blast
          then show ?thesis proof cases
            case f1

            have "p_io [t'] = [(x, t_output tM)]"
              using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close>
              by auto
            moreover have "target [t'] (initial A) = t_target t'"
              using \<open>t_source t' = initial A\<close> by auto
            ultimately have "t_target t' \<in> io_targets A [?ioM] (initial A)"
              unfolding io_targets.simps
              using single_transition_path[OF \<open>t' \<in> h A\<close>]
              by (metis (mono_tags, lifting) \<open>t_source t' = initial A\<close> mem_Collect_eq)
              
            
            show ?thesis 
              using observable_io_targets_language[of "[(x, t_output tM)]" "io@[ioM]" A "initial A" "t_target t'", OF _ \<open>observable A\<close> \<open>t_target t' \<in> io_targets A [?ioM] (initial A)\<close>]
              using f1
              by (metis \<open>observable A\<close> \<open>t' \<in> set (wf_transitions A)\<close> \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close> \<open>t_source t' = initial A\<close> append_Cons fst_conv observable_language_next snd_conv) 
              
          next
            case f2

            
            have "io_targets A (p_io [t'] @ io @ [ioM]) (t_source t') = io_targets A ([?ioM] @ io @ [ioM]) (t_source t')"
              using \<open>t_input t' = x\<close> \<open>t_output t' = t_output tM\<close> by auto 
            moreover have "io_targets A (io @ [ioM]) (t_target t') = io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t')))"
              unfolding io_targets.simps
              using from_FSM_path_initial[OF wf_transition_target[OF \<open>t' \<in> h A\<close>]] by auto
            ultimately have "io_targets A ([?ioM] @ io @ [ioM]) (t_source t') = io_targets (from_FSM A (t_target t')) (io @ [ioM]) (initial (from_FSM A (t_target t')))"
              using observable_io_targets_next[OF \<open>observable A\<close> \<open>t' \<in> h A\<close>, of "io @ [ioM]"] by auto

            then show ?thesis
              using f2 \<open>t_source t' = initial A\<close> by auto
          qed
        qed
          
        
          

        ultimately show ?thesis using \<open>fst ioA = fst ioM\<close> by blast
      qed
    qed
  qed
qed







lemma pass_ATC_io_fail :
  assumes "\<not>pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
shows "initial A \<in> FS \<or> (\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> (io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {}))"
  using pass_ATC'_io_fail[OF _ assms(2-4)] using assms(1) by auto



lemma pass_ATC_fail :
  assumes "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "io@[(x,y)] \<in> L A"
  and     "io@[(x,y')] \<in> L M" 
  and     "io@[(x,y')] \<notin> L A"
(*and   "io_targets A (io@[(x,y')]) (initial A) \<inter> FS = {}"*)
shows "\<not> pass_ATC M A FS"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) pass_ATC_io_explicit_io_tuple(1) by blast



lemma pass_ATC_reduction :
  assumes "L M2 \<subseteq> L M1"
  and     "is_ATC A"
  and     "observable M1"
  and     "observable M2"
  and     "set (inputs A) \<subseteq> set (inputs M1)"
  and     "set (inputs M2) = set (inputs M1)"
  and     "pass_ATC M1 A FS"
shows "pass_ATC M2 A FS"
proof (rule ccontr)
  assume "\<not> pass_ATC M2 A FS"
  have "set (inputs A) \<subseteq> set (inputs M2)"
    using assms(5,6) by blast
  
  have "initial A \<notin> FS"
    using \<open>pass_ATC M1 A FS\<close> by (cases "size A"; auto)  
  then show "False"
    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC M2 A FS\<close> assms(2,4) \<open>set (inputs A) \<subseteq> set (inputs M2)\<close>] using assms(1)
  proof -
    obtain pps :: "(integer \<times> integer) list" and pp :: "integer \<times> integer" and ppa :: "integer \<times> integer" where
      f1: "pps @ [pp] \<in> LS A (initial A) \<and> pps @ [ppa] \<in> LS M2 (initial M2) \<and> fst pp = fst ppa \<and> (pps @ [ppa] \<notin> LS A (initial A) \<or> io_targets A (pps @ [ppa]) (initial A) \<inter> FS \<noteq> {})"
      using \<open>initial A \<in> FS \<or> (\<exists>io ioA ioM. io @ [ioA] \<in> LS A (initial A) \<and> io @ [ioM] \<in> LS M2 (initial M2) \<and> fst ioA = fst ioM \<and> (io @ [ioM] \<notin> LS A (initial A) \<or> io_targets A (io @ [ioM]) (initial A) \<inter> FS \<noteq> {}))\<close> \<open>initial A \<notin> FS\<close> by blast
    then have "pps @ [ppa] \<in> LS M1 (initial M1)"
      using \<open>LS M2 (initial M2) \<subseteq> LS M1 (initial M1)\<close> by blast
    then show ?thesis
      using f1 by (metis (no_types) assms(2) assms(3) assms(5) assms(7) pass_ATC_fail pass_ATC_io_explicit_io_tuple(2) prod.collapse)
  qed 
qed









lemma shifted_transitions_observable_against_distinguishing_transitions_left :
  assumes "t1 \<in> set (shifted_transitions M q1 q2)"
  and     "t2 \<in> set (distinguishing_transitions_left M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
proof 
  assume *: "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"

  obtain t where "t1 = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))"
           and   "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
           and   "(\<exists>t'\<in>set (transitions M).
                           t_source t' = fst (t_source t) \<and>
                           t_input t' = t_input t \<and> t_output t' = t_output t)"
           and   **: "(\<exists>t'\<in>set (transitions M).
                           t_source t' = snd (t_source t) \<and>
                           t_input t' = t_input t \<and> t_output t' = t_output t)"
    using shifted_transitions_underlying_transition[OF assms(1,3,4)] by blast

  obtain qqt where "qqt \<in> set (concat
                                (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
             and   "t2 = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)"
             and   ***: "\<not> (\<exists>t'\<in>set (transitions M).
                            t_source t' = snd (fst qqt) \<and>
                            t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
    using distinguishing_transitions_left_underlying_data[OF assms(2)] by blast

  have "t_source t = fst qqt" and "t_input t = t_input (snd qqt)" and "t_output t = t_output (snd qqt)"
    using \<open>t1 = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))\<close>
          \<open>t2 = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)\<close>
          * 
    by auto
  then show "False"
    using ** *** by auto
qed

lemma shifted_transitions_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> set (shifted_transitions M q1 q2)"
  and     "t2 \<in> set (distinguishing_transitions_right M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
proof 
  assume *: "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"

  obtain t where "t1 = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))"
           and   "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
           and   **: "(\<exists>t'\<in>set (transitions M).
                           t_source t' = fst (t_source t) \<and>
                           t_input t' = t_input t \<and> t_output t' = t_output t)"
           and   "(\<exists>t'\<in>set (transitions M).
                           t_source t' = snd (t_source t) \<and>
                           t_input t' = t_input t \<and> t_output t' = t_output t)"
    using shifted_transitions_underlying_transition[OF assms(1,3,4)] by blast

  obtain qqt where "qqt \<in> set (concat
                                (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
             and   "t2 = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)"
             and   ***: "\<not> (\<exists>t'\<in>set (transitions M).
                            t_source t' = fst (fst qqt) \<and>
                            t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
    using distinguishing_transitions_right_underlying_data[OF assms(2)] by blast

  have "t_source t = fst qqt" and "t_input t = t_input (snd qqt)" and "t_output t = t_output (snd qqt)"
    using \<open>t1 = (Inl (t_source t), t_input t, t_output t, Inl (t_target t))\<close>
          \<open>t2 = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)\<close>
          * 
    by auto
  then show "False"
    using ** *** by auto
qed

lemma distinguishing_transitions_left_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> set (distinguishing_transitions_left M q1 q2)"
  and     "t2 \<in> set (distinguishing_transitions_right M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "\<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)"
proof 
  assume *: "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"

  obtain qqtL where **: "qqtL \<in> set (concat
                                (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
             and   "t1 = (Inl (fst qqtL), t_input (snd qqtL), t_output (snd qqtL), Inr q1)"
             and   ***: "t_source (snd qqtL) = fst (fst qqtL)"
             and   "\<not> (\<exists>t'\<in>set (transitions M).
                            t_source t' = snd (fst qqtL) \<and>
                            t_input t' = t_input (snd qqtL) \<and> t_output t' = t_output (snd qqtL))"
    using distinguishing_transitions_left_underlying_data[OF assms(1)] by blast

  have "snd qqtL \<in> h M"
    using ** concat_pair_set by blast
  then have ****: "snd qqtL \<in> set (transitions M) \<and> t_source (snd qqtL) = fst (fst qqtL) \<and> t_input (snd qqtL) = t_input (snd qqtL) \<and> t_output (snd qqtL) = t_output (snd qqtL)"
    using *** by auto
  

  obtain qqtR where "qqtR \<in> set (concat
                                (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                  (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
             and   "t2 = (Inl (fst qqtR), t_input (snd qqtR), t_output (snd qqtR), Inr q2)"
             and   "t_source (snd qqtR) = snd (fst qqtR)"
             and   *****: "\<not> (\<exists>t'\<in>set (transitions M).
                            t_source t' = fst (fst qqtR) \<and>
                            t_input t' = t_input (snd qqtR) \<and> t_output t' = t_output (snd qqtR))"
    using distinguishing_transitions_right_underlying_data[OF assms(2)] by blast

  have "fst qqtL = fst qqtR" and "t_input (snd qqtL) = t_input (snd qqtR)" and "t_output (snd qqtL) = t_output (snd qqtR)"
    using \<open>t1 = (Inl (fst qqtL), t_input (snd qqtL), t_output (snd qqtL), Inr q1)\<close>
          \<open>t2 = (Inl (fst qqtR), t_input (snd qqtR), t_output (snd qqtR), Inr q2)\<close>
          * 
    by auto
  then show "False"
    using **** ***** by auto
qed

lemma distinguishing_transitions_left_observable_against_distinguishing_transitions_left :
  assumes "t1 \<in> set (distinguishing_transitions_left M q1 q2)"
  and     "t2 \<in> set (distinguishing_transitions_left M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2"
  using distinguishing_transitions_left_sources_targets(2)[OF assms(1,3,4)]
        distinguishing_transitions_left_sources_targets(2)[OF assms(2,3,4)]
        \<open>t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close>
  by (simp add: prod_eqI) 


lemma distinguishing_transitions_right_observable_against_distinguishing_transitions_right :
  assumes "t1 \<in> set (distinguishing_transitions_right M q1 q2)"
  and     "t2 \<in> set (distinguishing_transitions_right M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2"
  using distinguishing_transitions_right_sources_targets(2)[OF assms(1,3,4)]
        distinguishing_transitions_right_sources_targets(2)[OF assms(2,3,4)]
        \<open>t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close>
  by (simp add: prod_eqI) 







lemma shifted_transitions_observable_against_shifted_transitions :
  assumes "t1 \<in> set (shifted_transitions M q1 q2)"
  and     "t2 \<in> set (shifted_transitions M q1 q2)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "observable M"
  and     "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
shows "t1 = t2"
proof -
  obtain t1' where d1: "t1 = (Inl (t_source t1'), t_input t1', t_output t1', Inl (t_target t1'))"
             and   h1: "t1' \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))"
    using shifted_transitions_underlying_transition[OF assms(1,3,4)] by blast

  obtain t2' where d2: "t2 = (Inl (t_source t2'), t_input t2', t_output t2', Inl (t_target t2'))"
             and   h2: "t2' \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))"
    using shifted_transitions_underlying_transition[OF assms(2,3,4)] by blast

  have "observable (product (from_FSM M q1) (from_FSM M q2))"
    using from_FSM_observable[OF assms(3,5)] from_FSM_observable[OF assms(4,5)] 
          product_observable 
    by metis
  
  then have "t1' = t2'"
    using d1 d2 h1 h2 \<open>t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close>
    by (metis fst_conv observable.elims(2) prod.expand snd_conv sum.inject(1)) 
  then show ?thesis using d1 d2 by auto
qed
  




lemma canonical_separator_observable :
  assumes "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "observable (canonical_separator M q1 q2)" (is "observable ?CSep")
proof -

  

  have  "\<And> t1 t2 . t1 \<in> set (transitions ?CSep) \<Longrightarrow> 
                             t2 \<in> set (transitions ?CSep) \<Longrightarrow> 
                    t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<Longrightarrow> t_target t1 = t_target t2" 
  proof -
    fix t1 t2 assume "t1 \<in> set (transitions ?CSep)" 
              and    "t2 \<in> set (transitions ?CSep)"
              and    "t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
    
    moreover have "transitions ?CSep = shifted_transitions M q1 q2 @
                                       distinguishing_transitions_left M q1 q2 @ 
                                       distinguishing_transitions_right M q1 q2"
      unfolding canonical_separator_def by auto
    moreover note shifted_transitions_observable_against_distinguishing_transitions_left[OF _ _ assms(2,3)]
    moreover note shifted_transitions_observable_against_distinguishing_transitions_right[OF _ _ assms(2,3)]
    moreover note distinguishing_transitions_left_observable_against_distinguishing_transitions_right[OF _ _ assms(2,3)]
    moreover note shifted_transitions_observable_against_shifted_transitions[OF _ _ assms(2,3)]
    moreover note distinguishing_transitions_left_observable_against_distinguishing_transitions_left[OF _ _ assms(2,3)]
    moreover note distinguishing_transitions_right_observable_against_distinguishing_transitions_right[OF _ _ assms(2,3)]
    ultimately show "t_target t1 = t_target t2"
    proof -
      have "\<forall>p. (p \<in> set (distinguishing_transitions_left M q1 q2 @ distinguishing_transitions_right M q1 q2) \<or> p \<in> set (shifted_transitions M q1 q2)) \<or> p \<notin> set (transitions (canonical_separator M q1 q2))"
        by (metis \<open>transitions (canonical_separator M q1 q2) = shifted_transitions M q1 q2 @ distinguishing_transitions_left M q1 q2 @ distinguishing_transitions_right M q1 q2\<close> list_concat_non_elem)
      then have "t1 = t2"
        by (metis (no_types) \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (distinguishing_transitions_left M q1 q2); t2 \<in> set (distinguishing_transitions_left M q1 q2); t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<rbrakk> \<Longrightarrow> t1 = t2\<close> \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (distinguishing_transitions_left M q1 q2); t2 \<in> set (distinguishing_transitions_right M q1 q2)\<rbrakk> \<Longrightarrow> \<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)\<close> \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (distinguishing_transitions_right M q1 q2); t2 \<in> set (distinguishing_transitions_right M q1 q2); t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<rbrakk> \<Longrightarrow> t1 = t2\<close> \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (shifted_transitions M q1 q2); t2 \<in> set (distinguishing_transitions_left M q1 q2)\<rbrakk> \<Longrightarrow> \<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)\<close> \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (shifted_transitions M q1 q2); t2 \<in> set (distinguishing_transitions_right M q1 q2)\<rbrakk> \<Longrightarrow> \<not> (t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)\<close> \<open>\<And>t2 t1. \<lbrakk>t1 \<in> set (shifted_transitions M q1 q2); t2 \<in> set (shifted_transitions M q1 q2); observable M; t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<rbrakk> \<Longrightarrow> t1 = t2\<close> \<open>t1 \<in> set (transitions (canonical_separator M q1 q2))\<close> \<open>t2 \<in> set (transitions (canonical_separator M q1 q2))\<close> \<open>t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2\<close> assms(1) list_concat_non_elem)
      then show ?thesis
        by meson
    qed 
  qed
  then show ?thesis unfolding observable.simps by blast
qed

lemma state_separator_from_canonical_separator_observable :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "observable A"
  using submachine_observable[OF _ canonical_separator_observable[OF assms(2,3,4)]]
  using assms(1) unfolding is_state_separator_from_canonical_separator_def 
  by metis


        


lemma separator_is_atc :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "is_ATC A"
  using state_separator_from_canonical_separator_observable[OF assms] 
  using assms(1) unfolding is_state_separator_from_canonical_separator_def is_ATC_def by metis


lemma canonical_separator_initial :
  shows "initial (canonical_separator M q1 q2) = Inl (q1,q2)" 
    unfolding canonical_separator_def 
    using from_FSM_simps(1) product_simps(1)
    by (metis (no_types, lifting) select_convs(1))


lemma state_separator_from_canonical_separator_initial :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
shows "initial A = Inl (q1,q2)"
    using assms unfolding is_state_separator_from_canonical_separator_def canonical_separator_def 
    using is_submachine.simps from_FSM_simps(1) product_simps(1)
    by (metis (no_types, lifting) select_convs(1))


lemma canonical_separator_target_possibilities :
  assumes "t \<in> h (canonical_separator M q1 q2)" (is "t \<in> h ?C")
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "isl (t_target t) \<or> t_target t = Inr q1 \<or> t_target t = Inr q2"
proof -
  have *: "set (transitions ?C) = (set (shifted_transitions M q1 q2)) \<union> (set (distinguishing_transitions_left M q1 q2)) \<union> (set (distinguishing_transitions_right M q1 q2))"
    using canonical_separator_simps(4)[of M q1 q2] by auto
  then consider  (a) "t \<in> set (shifted_transitions M q1 q2)" |
                 (b) "t \<in> set (distinguishing_transitions_left M q1 q2)" |
                 (c) "t \<in> set (distinguishing_transitions_right M q1 q2)"
    using assms(1) by blast
  then show ?thesis proof cases
    case a
    then show ?thesis unfolding shifted_transitions_def by auto
  next
    case b
    then show ?thesis unfolding distinguishing_transitions_left_def
      by (meson assms(2) assms(3) b distinguishing_transitions_left_sources_targets(2)) 
  next
    case c
    then show ?thesis unfolding distinguishing_transitions_right_def
      by (meson assms(2) assms(3) c distinguishing_transitions_right_sources_targets(2)) 
  qed
qed
                      

lemma canonical_separator_nodes :
  assumes "Inl (s1,s2) \<in> nodes (canonical_separator M q1 q2)"
  shows "(s1,s2) \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  consider (a) "Inl (s1,s2) = initial ?C" |
           (b) "\<exists> t \<in> h ?C . t_target t = Inl (s1,s2)"
    using nodes_initial_or_target[OF assms] by blast
  then show ?thesis proof cases
    case a
    then have "(s1,s2) = (q1,q2)"
      unfolding canonical_separator_def product_simps(1) from_FSM_simps(1) by auto
    then show ?thesis 
      using nodes.initial[of ?P] unfolding product_simps(1) from_FSM_simps(1) by auto
  next
    case b
    then obtain t where "t \<in> h ?C" and "t_target t = Inl (s1,s2)"
      by blast
    then have "isl (t_target t)"
      by auto

    note State_Separator.canonical_separator_product_h_isl[OF \<open>t \<in> h ?C\<close> \<open>isl (t_target t)\<close>]

    show ?thesis 
      using State_Separator.canonical_separator_product_h_isl[OF \<open>t \<in> h ?C\<close> \<open>isl (t_target t)\<close>]
      using \<open>t_target t = Inl (s1, s2)\<close> wf_transition_target by fastforce
  qed
qed

lemma canonical_separator_transition :
  assumes "t \<in> h (canonical_separator M q1 q2)" (is "t \<in> h ?C")
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "t_source t = Inl (s1,s2)"
shows "(\<exists> t1 \<in> h M . t_source t1 = s1 \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t) \<or>
       (\<exists> t2 \<in> h M . t_source t2 = s2 \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t)"
proof -           

  have "t_source t \<in> nodes ?C"
    using assms(1) by auto

  have *: "set (transitions ?C) = (set (shifted_transitions M q1 q2)) \<union> (set (distinguishing_transitions_left M q1 q2)) \<union> (set (distinguishing_transitions_right M q1 q2))"
    using canonical_separator_simps(4)[of M q1 q2] by auto
  then consider  (a) "t \<in> set (shifted_transitions M q1 q2)" |
                 (b) "t \<in> set (distinguishing_transitions_left M q1 q2)" |
                 (c) "t \<in> set (distinguishing_transitions_right M q1 q2)"
    using assms(1) by blast
  then show ?thesis proof cases
    case a
    then obtain ta where **: "t = (Inl (t_source ta), t_input ta, t_output ta, Inl (t_target ta))"
                   and   ***: "ta \<in> set (wf_transitions (product (from_FSM M q1) (from_FSM M q2)))"
                   and   "\<exists>t'\<in>set (transitions M).
                            t_source t' = fst (t_source ta) \<and> t_input t' = t_input ta \<and> t_output t' = t_output ta"
                   and   "\<exists>t'\<in>set (transitions M).
                            t_source t' = snd (t_source ta) \<and> t_input t' = t_input ta \<and> t_output t' = t_output ta"
      using shifted_transitions_underlying_transition[OF a assms(2,3)] by blast
    

    let ?t = "(fst (t_source ta), t_input ta, t_output ta, fst (t_target ta))"
    have "?t \<in> h M"
      using product_transition_split(1)[OF ***] from_FSM_h[OF \<open>q1 \<in> nodes M\<close>] by blast
    then show ?thesis
      using ** \<open>t_source t = Inl (s1,s2)\<close> by auto 
  next
    case b

    obtain qqt where **: "qqt \<in> set (concat
                                  (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
               and   ***:"t = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q1)"
               and   ****:"t_source (snd qqt) = fst (fst qqt)"
               and   "\<not> (\<exists>t'\<in>set (transitions M).
                              t_source t' = snd (fst qqt) \<and>
                              t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
      using distinguishing_transitions_left_underlying_data[OF b] by blast

    let ?t = "snd qqt"
    have "?t \<in> h M"
      using concat_pair_set[of "wf_transitions M" "nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))"] ** by blast
    moreover have "t_source ?t = s1"
      using *** **** \<open>t_source t = Inl (s1,s2)\<close> by auto
    moreover have "t_input ?t = t_input t" and "t_output ?t = t_output t"
      using *** by auto
    ultimately show ?thesis by blast
  next
    case c
    obtain qqt where **: "qqt \<in> set (concat
                                  (map (\<lambda>qq'. map (Pair qq') (wf_transitions M))
                                    (nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2)))))"
               and   ***:"t = (Inl (fst qqt), t_input (snd qqt), t_output (snd qqt), Inr q2)"
               and   ****:"t_source (snd qqt) = snd (fst qqt)"
               and   "\<not> (\<exists>t'\<in>set (transitions M).
                              t_source t' = fst (fst qqt) \<and>
                              t_input t' = t_input (snd qqt) \<and> t_output t' = t_output (snd qqt))"
      using distinguishing_transitions_right_underlying_data[OF c] by blast

    let ?t = "snd qqt"
    have "?t \<in> h M"
      using concat_pair_set[of "wf_transitions M" "nodes_from_distinct_paths (product (from_FSM M q1) (from_FSM M q2))"] ** by blast
    moreover have "t_source ?t = s2"
      using *** **** \<open>t_source t = Inl (s1,s2)\<close> by auto
    moreover have "t_input ?t = t_input t" and "t_output ?t = t_output t"
      using *** by auto
    ultimately show ?thesis by blast
  qed 
qed


lemma canonical_separator_path_split_target_isl :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) (p@[t])"
  shows "isl (target p (initial (canonical_separator M q1 q2)))"
proof -
  let ?C = "(canonical_separator M q1 q2)"
  have "t \<in> h ?C"
    using assms by auto
  have "\<not> deadlock_state ?C (t_source t)"
    using assms unfolding deadlock_state.simps by blast
  then show ?thesis 
    using canonical_separator_t_source_isl[of t] \<open>t \<in> h ?C\<close> assms
    by fastforce
qed
  


lemma canonical_separator_path_initial :
  assumes "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p" (is "path ?C (initial ?C) p")
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "(\<exists> p1 . path M q1 p1 \<and> p_io p1 = p_io p) \<or> (\<exists> p2 . path M q2 p2 \<and> p_io p2 = p_io p)"
using assms proof (induction p rule: rev_induct) 
  case Nil
  then show ?case by auto
next
  case (snoc t p)
  then have "path ?C (initial ?C) p" and "t \<in> h ?C" and "t_source t = target p (initial ?C)"
    by auto

  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  
  obtain p' where "path ?P (initial ?P) p'"
            and   *:"p = map (\<lambda>t. (Inl (t_source t), t_input t, t_output t, Inl (t_target t))) p'"
    using canonical_separator_path_from_shift[OF \<open>path ?C (initial ?C) p\<close> canonical_separator_path_split_target_isl[OF snoc.prems(1)]]
    by blast

  let ?pL = "(map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p')"
  let ?pR = "(map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p')"

  have "path ?P (q1,q2) p'"
    using \<open>path ?P (initial ?P) p'\<close> unfolding product_simps(1) from_FSM_simps(1) by assumption

  then have pL: "path (from_FSM M q1) q1 ?pL"
       and  pR: "path (from_FSM M q2) q2 ?pR"
       and  pN: "(\<exists>p1 p2.
                   path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
                   path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
                   target p1 (initial (from_FSM M q1)) = q1 \<and> target p2 (initial (from_FSM M q2)) = q2 \<and> p_io p1 = p_io p2)"
    using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p'] by auto


  
  
  
  obtain s1 s2 where "t_source t = Inl (s1,s2)"
    using canonical_separator_path_split_target_isl[OF snoc.prems(1)] 
    by (metis \<open>t_source t = target p (initial (canonical_separator M q1 q2))\<close> isl_def old.prod.exhaust)

  have "map t_target p = map (Inl o t_target) p'"
    using * by auto
  then have "target p (initial ?C) = Inl (target p' (q1,q2))"
    unfolding target.simps visited_states.simps canonical_separator_simps(1) product_simps(1) from_FSM_simps(1)
    by (simp add: last_map) 
  then have "target p' (q1,q2)= (s1,s2)"
    using \<open>t_source t = target p (initial ?C)\<close> \<open>t_source t = Inl (s1,s2)\<close>
    by auto 
    
  have "target ?pL q1 = s1" and "target ?pR q2 = s2"  
    using product_target_split[OF \<open>target p' (q1,q2)= (s1,s2)\<close>] by auto

  consider (a) "(\<exists>t1\<in>set (wf_transitions M). t_source t1 = s1 \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t)" |
           (b) "(\<exists>t2\<in>set (wf_transitions M). t_source t2 = s2 \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t)"
    using canonical_separator_transition[OF \<open>t \<in> h ?C\<close> \<open>q1 \<in> nodes M\<close> \<open>q2 \<in> nodes M\<close> \<open>t_source t = Inl (s1,s2)\<close>] by blast
  then show ?case proof cases
    case a
    then obtain t1 where "t1 \<in> h M" and "t_source t1 = s1" and "t_input t1 = t_input t" and "t_output t1 = t_output t" 
      by blast

    have "t_source t1 = target ?pL q1"
      using \<open>target ?pL q1 = s1\<close> \<open>t_source t1 = s1\<close> by auto
    then have "path M q1 (?pL@[t1])"
      using pL \<open>t1 \<in> h M\<close>
      by (meson from_FSM_path path_append_last snoc.prems(2))
    moreover have "p_io (?pL@[t1]) = p_io (p@[t])"
      using * \<open>t_input t1 = t_input t\<close> \<open>t_output t1 = t_output t\<close> by auto
    ultimately show ?thesis
      by meson
  next
    case b
    then obtain t2 where "t2 \<in> h M" and "t_source t2 = s2" and "t_input t2 = t_input t" and "t_output t2 = t_output t" 
      by blast

    have "t_source t2 = target ?pR q2"
      using \<open>target ?pR q2 = s2\<close> \<open>t_source t2 = s2\<close> by auto
    then have "path M q2 (?pR@[t2])"
      using pR \<open>t2 \<in> h M\<close>
      by (meson from_FSM_path path_append_last snoc.prems(3))
    moreover have "p_io (?pR@[t2]) = p_io (p@[t])"
      using * \<open>t_input t2 = t_input t\<close> \<open>t_output t2 = t_output t\<close> by auto
    ultimately show ?thesis
      by meson
  qed
qed

 



lemma canonical_separator_language :
  assumes "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
shows "L (canonical_separator M q1 q2) \<subseteq> L (from_FSM M q1) \<union> L (from_FSM M q2)" (is "L ?C \<subseteq> L ?M1 \<union> L ?M2")
proof 
  fix io assume "io \<in> L (canonical_separator M q1 q2)"
  then obtain p where *: "path (canonical_separator M q1 q2) (initial (canonical_separator M q1 q2)) p" and **: "p_io p = io"
    by auto
  
  show "io \<in> L (from_FSM M q1) \<union> L (from_FSM M q2)"
    using canonical_separator_path_initial[OF * assms] unfolding ** 
    using from_FSM_path_initial[OF assms(1)] from_FSM_path_initial[OF assms(2)]  
    unfolding LS.simps by blast
qed



lemma pass_separator_ATC_from_pass_ATC :
  assumes "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A" 
shows "pass_separator_ATC M A q1 q2"
proof (rule ccontr)
  assume "\<not> pass_separator_ATC M A q1 q2"

  have "initial A = Inl (q1,q2)"
    using state_separator_from_canonical_separator_initial[OF assms(7)] by assumption
  then have "initial A \<notin> {Inr q2}" by auto
  
  have *: "observable (from_FSM M q1)"
    using assms(2,4) from_FSM_observable by metis
  have **: "set (inputs A) \<subseteq> set (inputs (from_FSM M q1))"
    using from_FSM_simps(2) assms(3) by metis
  have "q1 \<in> nodes (from_FSM M q1)"
    using from_FSM_simps(1) nodes.initial by metis
      

  obtain io ioA ioM where "io @ [ioA] \<in> LS A (initial A)" 
                    and   "io @ [ioM] \<in> LS (from_FSM M q1) (initial (from_FSM M q1))" 
                    and   "fst ioA = fst ioM" 
                    and   "(io @ [ioM] \<notin> LS A (initial A) \<or> io_targets A (io @ [ioM]) (initial A) \<inter> {Inr q2} \<noteq> {})"
    using \<open>\<not> pass_separator_ATC M A q1 q2\<close>
    unfolding pass_separator_ATC.simps
    using pass_ATC_io_fail[OF _ \<open>is_ATC A\<close> * **, of "{Inr q2}"] 
    using \<open>initial A \<notin> {Inr q2}\<close> 
    by blast

  thm canonical_separator_maximal_path_distinguishes_right[OF assms(7) _ _ assms(2,4,5,6)]

  


lemma pass_ATC_reduction_distinction : 
  assumes "is_ATC A"
  and     "observable M"
  and     "observable T"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "set (inputs A) \<subseteq> set (inputs T)"
  and     "pass_separator_ATC T A q1 q2"
  and     "pass_separator_ATC T A q2 q1"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "t1 \<in> nodes T"
  and     "t2 \<in> nodes T"
  and     "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"  
shows "t1 \<noteq> t2"
proof 

  thm separator_is_atc[OF assms(13,2,8,9)]
  
  thm pass_ATC_reduction


  thm canonical_separator_maximal_path_distinguishes_left[OF assms(13) _ _ \<open>observable M\<close> assms(8,9,10)]
  thm canonical_separator_maximal_path_distinguishes_right[OF assms(13) _ _ \<open>observable M\<close> assms(8,9,10)]

end (*

(* TODO: add lemma that 







lemma pass_ATC_state_reduction :
  assumes "L M2 \<subseteq> L M1"
  and     "is_ATC A"
  and     "observable M1"
  and     "observable M2"
  and     "set (inputs A) \<subseteq> set (inputs M1)"
  and     "set (inputs M2) = set (inputs M1)"
  and     "pass_ATC M1 A FS"
shows "pass_ATC M2 A FS"

end (*
lemma pass_ATC_state_reduction :
  assumes "L M2 \<subseteq> L M1"
  and     "is_ATC A"
  and     "observable M1"
  and     "observable M2"
  and     "set (inputs A) \<subseteq> set (inputs M1)"
  and     "set (inputs M2) = set (inputs M1)"
  and     "pass_ATC M1 A FS"
shows "pass_ATC M2 A FS"


end (*


lemma x :
  assumes "pass_ATC' M A FS k"
      and "is_ATC A"
      and "completely_specified M"
      and "set (inputs A) \<subseteq> set (inputs M)"   
  shows (*"\<not> (\<exists> ioA \<in> L A . length ioA \<le> k \<and> \<not> (\<exists> ioM \<in> L M . map fst ioA = map fst ioM))"*)
        "\<And> io ioA ioM . (io@[ioA]) \<in> L A \<Longrightarrow> length (io@[ioA]) \<le> k \<Longrightarrow> (io@[ioM]) \<in> L M \<Longrightarrow> fst ioM = fst ioA \<Longrightarrow> (io@[ioM]) \<in> L A"  
    and "\<not> (\<exists> ioM \<in> L M . \<exists> p . path A (initial A) p \<and> p_io p = ioM \<and> length p \<le> k \<and> set (visited_states (initial A) p) \<inter> FS \<noteq> {})" 
proof -
  have "\<not> (\<exists> ioA \<in> L A . length ioA \<le> k \<and> \<not> (\<exists> ioM \<in> L M . map fst ioA = map fst ioM))
        \<and> \<not> (\<exists> ioM \<in> L M . \<exists> p . path A (initial A) p \<and> p_io p = ioM \<and> length p \<le> k \<and> set (visited_states (initial A) p) \<inter> FS \<noteq> {})"
    using assms proof (induction k arbitrary: M A) (* rule: less_induct) *)
      case 0
      then show ?case by auto
    next
      case (Suc k)

      have "\<And> ioA . ioA \<in> L A \<Longrightarrow> length ioA \<le> Suc k \<Longrightarrow> (\<exists>ioM\<in>LS M (initial M). map fst ioA = map fst ioM)"
      proof -
        fix ioA 
        assume "ioA \<in> L A"
           and "length ioA \<le> Suc k"
        
        show "(\<exists>ioM\<in>LS M (initial M). map fst ioA = map fst ioM)"
        proof (cases ioA)
          case Nil
          then show ?thesis by auto
        next
          case (Cons ioAt ioAp)

          obtain p' where "path A (initial A) p'" and "p_io p' = ioA"
            using \<open>ioA \<in> L A\<close> unfolding LS.simps by auto
          then obtain t p where "path A (initial A) (t#p)" and "p_io (t#p) = ioA"
            using Cons 
          proof -
            assume a1: "\<And>t p. \<lbrakk>path A (initial A) (t # p); p_io (t # p) = ioA\<rbrakk> \<Longrightarrow> thesis"
            have "length p' = length ioA"
              using \<open>p_io p' = ioA\<close> by force
            then show ?thesis
              using a1 by (metis (no_types) \<open>ioA = ioAt # ioAp\<close> \<open>p_io p' = ioA\<close> \<open>path A (initial A) p'\<close> length_Suc_conv)
          qed

          then have "t \<in> h A" and "t_source t = initial A" and "t_input t \<in> set (inputs A)" by auto
          then have "\<And> t' . t' \<in> h A \<Longrightarrow> t_source t' = t_source t \<Longrightarrow> t_input t' = t_input t"
            using \<open>is_ATC A\<close> unfolding is_ATC_def single_input.simps by blast
          then have *: "\<And> x . x \<in> set (inputs A) \<Longrightarrow> \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<Longrightarrow> x = t_input t"
            using \<open>t_source t = initial A\<close> by force

          have find_scheme : "\<And> P xs x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> (\<And> x' . x' \<in> set xs \<Longrightarrow> P x' \<Longrightarrow> x' = x) \<Longrightarrow> find P xs = Some x"
            by (metis find_None_iff find_condition find_set option.exhaust)

          have "find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) = Some (t_input t)"
            using find_scheme[OF \<open>t_input t \<in> set (inputs A)\<close>, of "\<lambda>x . \<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A"]
            using * \<open>t \<in> set (wf_transitions A)\<close> \<open>t_source t = initial A\<close> by blast

          
          
          then have ***: "\<And> tM . tM \<in> h M \<Longrightarrow> t_input tM = t_input t \<Longrightarrow> t_source tM = initial M \<Longrightarrow>
            (\<exists> tA \<in> h A .
                t_input tA = t_input t \<and>
                t_source tA = initial A \<and> t_output tA = t_output tM \<and> pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k)"
            using Suc.prems(1) unfolding pass_ATC'.simps by auto

          obtain tM where "tM \<in> h M" and "t_input tM = t_input t" and "t_source tM = initial M"
            using Suc.prems(3,4) unfolding completely_specified.simps using nodes.initial[of M] \<open>t \<in> h A\<close> 
            by (meson \<open>t_input t \<in> set (inputs A)\<close> set_rev_mp)
  
          then obtain tA where "tA \<in> h A"
                           and "t_input tA = t_input t"
                           and "t_source tA = initial A" 
                           and "t_output tA = t_output tM" 
                           and "pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k"
            using ***[of tM] by auto

           
          have "completely_specified (from_FSM M (t_target tM))"
            using Suc.prems(3)  from_FSM_completely_specified[OF wf_transition_target[OF \<open>tM \<in> h M\<close>]] by auto

          have "set (inputs (from_FSM A (t_target tA))) \<subseteq> set (inputs (from_FSM M (t_target tM)))"
            using Suc.prems(4) by (simp add: from_FSM_simps(2))

          have "\<not> (\<exists>ioA\<in>LS (from_FSM A (t_target tA)) (initial (from_FSM A (t_target tA))).
                   length ioA \<le> k \<and> \<not> (\<exists>ioM\<in>LS (from_FSM M (t_target tM)) (initial (from_FSM M (t_target tM))). map fst ioA = map fst ioM))"
            using Suc.IH[OF \<open>pass_ATC' (from_FSM M (t_target tM)) (from_FSM A (t_target tA)) FS k\<close>
                            is_ATC_from[OF \<open>tA \<in> h A\<close> \<open>is_ATC A\<close>] 
                            \<open>completely_specified (from_FSM M (t_target tM))\<close>
                            \<open>set (inputs (from_FSM A (t_target tA))) \<subseteq> set (inputs (from_FSM M (t_target tM)))\<close>]
            by auto

          then obtain ioM' where "ioM' \<in> L (from_FSM M (t_target tM))" and "map fst ioA = map fst ioM'"
            sorry    
            

          show ?thesis 


        qed
         
    
        

      then show ?case unfolding pass_ATC'.simps
    qed
  
  
  
  then show "\<not> (\<exists> ioA \<in> L A . \<not> (\<exists> ioM \<in> L M . map fst ioA = map fst ioM))"
        and "\<not> (\<exists> ioM \<in> L M . \<exists> p . path A (initial A) p \<and> p_io p = ioM \<and> set (visited_states (initial A) p) \<inter> FS \<noteq> {})"
    by presburger +
qed

end