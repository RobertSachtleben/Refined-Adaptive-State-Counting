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
      moreover have "[?ioM] \<in> L M"
        using \<open>tM \<in> h M\<close> \<open>t_input tM = x\<close> \<open>t_source tM = initial M\<close> unfolding LS.simps
      proof -
        have "[(x, t_output tM)] = p_io [tM]"
          by (simp add: \<open>t_input tM = x\<close>)
        then have "\<exists>ps. [(x, t_output tM)] = p_io ps \<and> path M (initial M) ps"
          by (metis (no_types) \<open>tM \<in> set (wf_transitions M)\<close> \<open>t_source tM = initial M\<close> single_transition_path)
        then show "[(x, t_output tM)] \<in> {p_io ps |ps. path M (initial M) ps}"
          by blast
      qed

      moreover have "fst ?ioA = fst ?ioM"
        by auto

      moreover have "[?ioM] \<notin> L A"
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

      ultimately have "\<exists> io ioA ioM . io@[ioA] \<in> L A
                          \<and> io@[ioM] \<in> L M
                          \<and> fst ioA = fst ioM
                          \<and> io@[ioM] \<notin> L A"
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
        case b1 (* like case a *)
        then show ?thesis sorry
      next
        case b2 (* obtain io ioA ioM and prepend (x,t_output tM) *)
        then show ?thesis sorry
      qed
    qed
  qed
qed


end (*


lemma pass_ATC_io_fail :
  assumes "\<not>pass_ATC M A FS"
  and     "is_ATC A"
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
shows "\<exists> io ioA ioM . io@[ioA] \<in> L A
                    \<and> io@[ioM] \<in> L M
                    \<and> fst ioA = fst ioM
                    \<and> (io@[ioM] \<notin> L A \<or> io_targets A (io@[ioM]) (initial A) \<inter> FS \<noteq> {})"
  

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