theory Adaptive_Test_Case
imports State_Separator 
begin

section \<open>Adaptive Test Cases\<close>

subsection \<open>Basic Definition\<close>

(* An ATC is a single input, acyclic, observable FSM, which is equivalent to a tree whose inner 
   nodes are labeled with inputs and whose edges are labeled with outputs *)
definition is_ATC :: "('a,'b) FSM_scheme \<Rightarrow> bool" where
  "is_ATC M = (single_input M \<and> acyclic M \<and> observable M)"

lemma is_ATC_from :
  assumes "t \<in> h A"
  and     "is_ATC A"
shows "is_ATC (from_FSM A (t_target t))"
  using from_FSM_acyclic[OF wf_transition_target[OF assms(1)]] 
        from_FSM_single_input[OF wf_transition_target[OF assms(1)]]
        from_FSM_observable[OF _ wf_transition_target[OF assms(1)]]
        assms(2)
  unfolding is_ATC_def
  by blast


subsection \<open>Applying Adaptive Test Cases\<close>


(* FSM A passes ATC A if and only if the parallel execution of M and A does not visit a fail_state in A and M produces no output not allowed in A *)
fun pass_ATC' :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> nat \<Rightarrow> bool" where
  "pass_ATC' M A fail_states 0 = (\<not> (initial A \<in> fail_states))" |
  "pass_ATC' M A fail_states (Suc k) = ((\<not> (initial A \<in> fail_states)) \<and> (case find (\<lambda> x . \<exists> t \<in> h A . t_input t = x \<and> t_source t = initial A) (inputs A) of
    None \<Rightarrow> True |
    Some x \<Rightarrow> \<forall> t \<in> h M . (t_input t = x \<and> t_source t = initial M) \<longrightarrow> (\<exists> t' \<in> h A . t_input t' = x \<and> t_source t' = initial A \<and> t_output t' = t_output t \<and> pass_ATC' (from_FSM M (t_target t)) (from_FSM A (t_target t')) fail_states k)))"

(* Applies pass_ATC' for a depth of at most (size A) (i.e., an upper bound on the length of paths in A) *)
fun pass_ATC :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'c set \<Rightarrow> bool" where
  "pass_ATC M A fail_states = pass_ATC' M A fail_states (size A)"



lemma pass_ATC'_initial :
  assumes "pass_ATC' M A FS k"
  shows "initial A \<notin> FS"
using assms by (cases k; auto) 


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
                        from_FSM_observable[OF \<open>observable M\<close> wf_transition_target[OF \<open>tM \<in> h M\<close>]]
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


lemma pass_ATC_fail_no_reduction :
  assumes "is_ATC A"
  and     "observable T" 
  and     "observable M"
  and     "set (inputs A) \<subseteq> set (inputs M)"
  and     "set (inputs T) = set (inputs M)"
  and     "pass_ATC M A FS"
  and     "\<not>pass_ATC T A FS"
shows   "\<not> (L T \<subseteq> L M)" 
  using pass_ATC_reduction[OF _ assms(1,3,2,4,5,6)] assms(7) by blast









subsection \<open>State Separators as Adaptive Test Cases\<close>

fun pass_separator_ATC :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" where
  "pass_separator_ATC M S q1 t2 = pass_ATC (from_FSM M q1) S {t2}"

(*
fun pass_separator_ATC :: "('a,'b) FSM_scheme \<Rightarrow> (('a \<times> 'a) + 'a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "pass_separator_ATC M S q1 q2 = pass_ATC (from_FSM M q1) S {Inr q2}"
*)


lemma separator_is_ATC :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  shows "is_ATC A"
unfolding is_ATC_def 
  using is_separator_simps(1,2,3)[OF assms(1)] by blast



(*
lemma state_separator_from_canonical_separator_is_ATC :
  assumes "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A"
  and     "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  shows "is_ATC A"
unfolding is_ATC_def 
  using is_state_separator_from_canonical_separator_simps(2,3)[OF assms(1)]
  using submachine_observable[OF is_state_separator_from_canonical_separator_simps(1)[OF assms(1)] canonical_separator_observable[OF assms(2,3,4)]]
  by blast
*)

(* todo: move *)
lemma nodes_initial_deadlock :
  assumes "deadlock_state M (initial M)"
  shows "nodes M = {initial M}"
proof -
  have "initial M \<in> nodes M"
    by auto
  moreover have "\<And> q . q \<in> nodes M \<Longrightarrow> q \<noteq> initial M \<Longrightarrow> False"
  proof -
    fix q assume "q \<in> nodes M" and "q \<noteq> initial M"
    
    obtain p where "path M (initial M) p" and "q = target p (initial M)"
      using path_to_node[OF \<open>q \<in> nodes M\<close>] by auto
    
    have "p \<noteq> []" 
    proof
      assume "p = []"
      then have "q = initial M" using \<open>q = target p (initial M)\<close> by auto
      then show "False" using \<open>q \<noteq> initial M\<close> by simp
    qed
    then obtain t p' where "p = t # p'" 
      using list.exhaust by blast
    then have "t \<in> h M" and "t_source t = initial M"
      using \<open>path M (initial M) p\<close> by auto
    then show "False"
      using \<open>deadlock_state M (initial M)\<close> unfolding deadlock_state.simps by blast
  qed
  ultimately show ?thesis by blast
qed
    
(* TODO: move *)
lemma separator_initial :
  assumes "is_separator M q1 q2 A t1 t2"
shows "initial A \<noteq> t1"
and   "initial A \<noteq> t2"
proof -
  show "initial A \<noteq> t1"
  proof 
    assume "initial A = t1"
    then have "deadlock_state A (initial A)"
      using is_separator_simps(4)[OF assms] by auto
    then have "nodes A = {initial A}" 
      using nodes_initial_deadlock by blast
    then show "False"
      using is_separator_simps(7,15)[OF assms] \<open>initial A = t1\<close> by auto
  qed

  show "initial A \<noteq> t2"
  proof 
    assume "initial A = t2"
    then have "deadlock_state A (initial A)"
      using is_separator_simps(5)[OF assms] by auto
    then have "nodes A = {initial A}" 
      using nodes_initial_deadlock by blast
    then show "False"
      using is_separator_simps(6,15)[OF assms] \<open>initial A = t2\<close> by auto
  qed
qed



lemma pass_separator_ATC_from_separator_left :
  assumes "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2" 
shows "pass_separator_ATC M A q1 t2" (* note t2 instead of previously used q2*)
proof (rule ccontr)
  assume "\<not> pass_separator_ATC M A q1 t2"

  then have "\<not> pass_ATC (from_FSM M q1) A {t2}"
    by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(4,1,2,3)] by assumption

  have "initial A \<notin> {t2}"
    using separator_initial(2)[OF assms(4)] by blast
  then obtain io ioA ioM where
    "io @ [ioA] \<in> L A"
    "io @ [ioM] \<in> LS M q1"
    "fst ioA = fst ioM"
    "io @ [ioM] \<notin> L A \<or> io_targets A (io @ [ioM]) (initial A) \<inter> {t2} \<noteq> {}"

    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC (from_FSM M q1) A {t2}\<close> \<open>is_ATC A\<close> from_FSM_observable[OF \<open>observable M\<close> \<open>q1 \<in> nodes M\<close>] ] 
    using is_separator_simps(16)[OF assms(4)]
    using from_FSM_language[OF \<open>q1 \<in> nodes M\<close>]
    unfolding from_FSM_simps by blast
  then obtain x ya ym where
    "io @ [(x,ya)] \<in> L A"
    "io @ [(x,ym)] \<in> LS M q1"
    "io @ [(x,ym)] \<notin> L A \<or> io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} \<noteq> {}"
    by (metis fst_eqD old.prod.exhaust)

  have "io @ [(x,ym)] \<in> L A"
    using is_separator_simps(9)[OF assms(4) \<open>io @ [(x,ym)] \<in> LS M q1\<close> \<open>io @ [(x,ya)] \<in> L A\<close>] by assumption

  have "t1 \<noteq> t2" using is_separator_simps(15)[OF assms(4)] by assumption
  
  consider (a) "io @ [(x, ym)] \<in> LS M q1 - LS M q2" |
           (b) "io @ [(x, ym)] \<in> LS M q1 \<inter> LS M q2"
    using \<open>io @ [(x,ym)] \<in> LS M q1\<close> by blast 
  then have "io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} = {}"
    
  proof (cases)
    case a
    show ?thesis using separator_language(1)[OF assms(4) \<open>io @ [(x,ym)] \<in> L A\<close> a] \<open>t1 \<noteq> t2\<close> by auto      
  next
    case b
    show ?thesis using separator_language(3)[OF assms(4) \<open>io @ [(x,ym)] \<in> L A\<close> b] \<open>t1 \<noteq> t2\<close> by auto
  qed
  
  then show "False"
    using \<open>io @ [(x,ym)] \<in> L A\<close>
    using \<open>io @ [(x,ym)] \<notin> L A \<or> io_targets A (io @ [(x,ym)]) (initial A) \<inter> {t2} \<noteq> {}\<close> by blast
qed

lemma pass_separator_ATC_from_separator_right :
  assumes "observable M"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2" 
shows "pass_separator_ATC M A q2 t1"
  using assms(1-3) is_separator_sym[OF assms(4)] pass_separator_ATC_from_separator_left by metis


(*
lemma is_separator_language :
  assumes "is_separator M q1 q2 A t1 t2"
  shows "L A \<subseteq> LS M q1 \<union> LS M q2"


lemma is_separator_target :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "path A (initial A) p"
shows "target p (initial A) = t1 \<Longrightarrow> p_io p \<in> LS M q1 - LS M q2"
and   "target p (initial A) = t2 \<Longrightarrow> p_io p \<in> LS M q2 - LS M q1"
and   "isl (target p (initial A)) \<Longrightarrow> p_io p \<in> LS M q2 \<inter> LS M q1"
and   "target p (initial A) = t1 \<or> target p (initial A) = t2 \<or> isl (target p (initial A))"
  *)


lemma pass_separator_ATC_path_left :
  assumes "pass_separator_ATC S A s1 t2"
  and     "observable S" 
  and     "observable M"
  and     "s1 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "q1 \<noteq> q2"
  and     "path A (initial A) pA"
  and     "path S s1 pS"
  and     "p_io pA = p_io pS"
shows "target pA (initial A) \<noteq> t2"
and   "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
proof -

  have "pass_ATC (from_FSM S s1) A {t2}"
    using \<open>pass_separator_ATC S A s1 t2\<close> by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(7,3,5,6)] by assumption

  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(2,4)] by assumption

  have "set (inputs A) \<subseteq> set (inputs (from_FSM S s1))"
    using is_separator_simps(16)[OF assms(7)] \<open>set (inputs S) = set (inputs M)\<close>
    unfolding from_FSM_simps by blast

  have "target pA (initial A) \<noteq> t2 \<and> (\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA)"
  proof (cases pA rule: rev_cases)
    case Nil
    then have "target pA (initial A) \<noteq> t2"
      using separator_initial(2)[OF assms(7)] by auto
    moreover have "(\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA)"
      unfolding Nil using \<open>q1 \<in> nodes M\<close> by auto
    ultimately show ?thesis by auto
  next
    case (snoc ys y)
    then have "p_io pA = (p_io ys)@[(t_input y,t_output y)]"
      by auto
    then have *: "(p_io ys)@[(t_input y,t_output y)] \<in> L A"
      using language_state_containment[OF \<open>path A (initial A) pA\<close>] by blast
    then have "p_io pS = (p_io ys)@[(t_input y,t_output y)]"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> \<open>p_io pA = p_io pS\<close> by auto
    then have **: "(p_io ys)@[(t_input y,t_output y)] \<in> L (from_FSM S s1)"
      using language_state_containment[OF \<open>path S s1 pS\<close>] 
      unfolding from_FSM_language[OF \<open>s1 \<in> nodes S\<close>] by blast
    
    have "io_targets A ((p_io ys)@[(t_input y,t_output y)]) (initial A) \<inter> {t2} = {}"
      using pass_ATC_io(2)[OF \<open>pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>set (inputs A) \<subseteq> set (inputs (from_FSM S s1))\<close> * **]
      unfolding fst_conv by auto
    then have "target pA (initial A) \<noteq> t2"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> \<open>path A (initial A) pA\<close>
      unfolding io_targets.simps
      by blast 

    have "p_io ys @ [(t_input y, t_output y)] \<in> LS M q1"
      using separator_language(2,4)[OF assms(7) \<open>(p_io ys)@[(t_input y,t_output y)] \<in> L A\<close>]
      using \<open>io_targets A ((p_io ys)@[(t_input y,t_output y)]) (initial A) \<inter> {t2} = {}\<close> by blast
    then have "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
      using \<open>p_io pA = (p_io ys)@[(t_input y,t_output y)]\<close> by auto

    then show ?thesis using \<open>target pA (initial A) \<noteq> t2\<close> by auto
  qed

  then show "target pA (initial A) \<noteq> t2" and   "\<exists> pM . path M q1 pM \<and> p_io pM = p_io pA"
    by blast+
qed




lemma pass_separator_ATC_path_right :
  assumes "pass_separator_ATC S A s2 t1"
  and     "observable S" 
  and     "observable M"
  and     "s2 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "q1 \<noteq> q2"
  and     "path A (initial A) pA"
  and     "path S s2 pS"
  and     "p_io pA = p_io pS"
shows "target pA (initial A) \<noteq> t1"
and   "\<exists> pM . path M q2 pM \<and> p_io pM = p_io pA" 
  using pass_separator_ATC_path_left[OF assms(1-4,6,5) is_separator_sym[OF assms(7)] assms(8) _ assms(10-12)] assms(9) by blast+




    




lemma pass_separator_ATC_fail_no_reduction :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "\<not>pass_separator_ATC S A s1 t2"
shows   "\<not> (LS S s1 \<subseteq> LS M q1)" 
proof 
  assume "LS S s1 \<subseteq> LS M q1"

  have "is_ATC A"
    using separator_is_ATC[OF assms(6,2,4,5)] by assumption

  have *: "set (inputs A) \<subseteq> set (inputs (from_FSM M q1))"
    using is_separator_simps(16)[OF assms(6)]
    unfolding is_submachine.simps canonical_separator_simps from_FSM_simps by auto

  have "pass_ATC (from_FSM M q1) A {t2}"
    using pass_separator_ATC_from_separator_left[OF assms(2,4,5,6)] by auto

  have "\<not> pass_ATC (from_FSM S s1) A {t2}"
    using \<open>\<not>pass_separator_ATC S A s1 t2\<close> by auto

  moreover have "pass_ATC (from_FSM S s1) A {t2}"
    using pass_ATC_reduction[OF _ \<open>is_ATC A\<close> from_FSM_observable[OF \<open>observable M\<close> \<open>q1 \<in> nodes M\<close>] from_FSM_observable[OF \<open>observable S\<close> \<open>s1 \<in> nodes S\<close>] *]
    using \<open>LS S s1 \<subseteq> LS M q1\<close> \<open>pass_ATC (from_FSM M q1) A {t2}\<close>  
    unfolding from_FSM_language[OF assms(3)] from_FSM_language[OF assms(4)]
    unfolding from_FSM_simps \<open>set (inputs S) = set (inputs M)\<close> by blast
  ultimately show "False" by simp
qed





lemma pass_separator_ATC_pass_left :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS S s1"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s1 t2"
shows "target p (initial A) \<noteq> t2"
and   "target p (initial A) = t1 \<or> (target p (initial A) \<noteq> t1 \<and> target p (initial A) \<noteq> t2)" (* useless? *)
proof -

  from \<open>p_io p \<in> LS S s1\<close> obtain pS where "path S s1 pS" and "p_io p = p_io pS"
    by auto

  then show "target p (initial A) \<noteq> t2" 
    using pass_separator_ATC_path_left[OF assms(11,1-7,10,8)] by simp

  obtain pM where "path M q1 pM" and "p_io pM = p_io p"
    using pass_separator_ATC_path_left[OF assms(11,1-7,10,8) \<open>path S s1 pS\<close> \<open>p_io p = p_io pS\<close>]  by blast
  then have "p_io p \<in> LS M q1"
    unfolding LS.simps by force

  then show "target p (initial A) = t1 \<or> (target p (initial A) \<noteq> t1 \<and> target p (initial A) \<noteq> t2)"
    using separator_path_targets(1,3,4)[OF assms(6,8)] by blast
qed


lemma pass_separator_ATC_pass_right :
  assumes "observable S" 
  and     "observable M"
  and     "s2 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "path A (initial A) p"
  and     "p_io p \<in> LS S s2"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s2 t1"
shows "target p (initial A) \<noteq> t1"
and   "target p (initial A) = t2 \<or> (target p (initial A) \<noteq> t2 \<and> target p (initial A) \<noteq> t2)" (* useless? *)
  using pass_separator_ATC_pass_left[OF assms(1,2,3,5,4) is_separator_sym[OF assms(6)] assms(7-9) _ assms(11)] assms(10) by blast+


(* TODO: move *)
lemma completely_specified_path_extension : 
  assumes "completely_specified M"
  and     "q \<in> nodes M"
  and     "path M q p"
  and     "x \<in> set (inputs M)"
obtains t where "t \<in> h M" and "t_input t = x" and "t_source t = target p q"
proof -
  have "target p q \<in> nodes M"
    using path_target_is_node \<open>path M q p\<close> by metis
  then obtain t where "t \<in> h M" and "t_input t = x" and "t_source t = target p q"
    using \<open>completely_specified M\<close> \<open>x \<in> set (inputs M)\<close> 
    unfolding completely_specified.simps by blast
  then show ?thesis using that by blast
qed

lemma completely_specified_language_extension :
  assumes "completely_specified M"
  and     "q \<in> nodes M"
  and     "io \<in> LS M q"
  and     "x \<in> set (inputs M)"
obtains y where "io@[(x,y)] \<in> LS M q"
proof -
  obtain p where "path M q p" and "p_io p = io"
    using \<open>io \<in> LS M q\<close> by auto
  
  moreover obtain t where "t \<in> h M" and "t_input t = x" and "t_source t = target p q"
    using completely_specified_path_extension[OF assms(1,2) \<open>path M q p\<close> assms(4)] by blast

  ultimately have "path M q (p@[t])" and "p_io (p@[t]) = io@[(x,t_output t)]"
    by (simp add: path_append_last)+
    
  then have "io@[(x,t_output t)] \<in> LS M q"
    using language_state_containment[of M q "p@[t]" "io@[(x,t_output t)]"] by auto
  then show ?thesis using that by blast
qed
  
  
lemma language_path_append_transition_observable :
  assumes "(p_io p) @ [(x,y)] \<in> LS M q"
  and     "path M q p"
  and     "observable M"
  obtains t where "path M q (p@[t])" and "t_input t = x" and "t_output t = y"
proof -
  obtain p' t where "path M q (p'@[t])" and "p_io (p'@[t]) = (p_io p) @ [(x,y)]"
    using language_path_append_transition[OF assms(1)] by blast
  then have "path M q p'" and "p_io p' = p_io p" and "t_input t = x" and "t_output t = y"
    by auto

  have "p' = p"
    using observable_path_unique[OF assms(3) \<open>path M q p'\<close> \<open>path M q p\<close> \<open>p_io p' = p_io p\<close>] by assumption
  then have "path M q (p@[t])"
    using \<open>path M q (p'@[t])\<close> by auto
  then show ?thesis using that \<open>t_input t = x\<close> \<open>t_output t = y\<close> by metis
qed
  




lemma pass_separator_ATC_completely_specified_left :
  assumes "observable S" 
  and     "observable M"
  and     "s1 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s1 t2"
  and     "completely_specified S"
shows "\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t1"
and   "\<not> (\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t2)"
proof -
  have p1: "pass_ATC (from_FSM S s1) A {t2}"
    using assms(9) by auto

  have p2: "is_ATC A"
    using separator_is_ATC[OF assms(6,2,4,5)] by assumption

  have p3: "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(1,3)] by assumption

  have p4: "set (inputs A) \<subseteq> set (inputs (from_FSM S s1))"
    using is_separator_simps(16)[OF assms(6)] 
    unfolding from_FSM_simps is_submachine.simps canonical_separator_simps assms(7) by auto

  have "t1 \<noteq> t2" and "observable A"
    using is_separator_simps(15,3)[OF assms(6)] by simp+


  have path_ext: "\<And> p . path A (initial A) p \<Longrightarrow> p_io p \<in> LS S s1 \<Longrightarrow> (target p (initial A) \<noteq> t2) \<and> (target p (initial A) = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1))"
  proof -
    fix p assume "path A (initial A) p" and "p_io p \<in> LS S s1"

    

    consider (a) "target p (initial A) = t1" |
             (b) "target p (initial A) \<noteq> t1 \<and> target p (initial A) \<noteq> t2"
      using pass_separator_ATC_pass_left(2)[OF assms(1,2,3,4,5,6,7) \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> assms(8,9)] by blast
    then have "target p (initial A) = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1)"
    proof cases
      case a
      then show ?thesis by blast
    next
      case b

      let ?t3 = "target p (initial A)"
      have "?t3 \<noteq> t1" and "?t3 \<noteq> t2"
        using b by auto
      moreover have "?t3 \<in> nodes A"
        using path_target_is_node \<open>path A (initial A) p\<close> by metis
      ultimately have "\<not> deadlock_state A ?t3"
        using is_separator_simps(8)[OF assms(6)] by blast
      then obtain tt where "tt \<in> h A" and "t_source tt = ?t3"
        by auto
      
      then have "path A (initial A) (p@[tt])" 
        using \<open>path A (initial A) p\<close> using path_append_last by metis

      moreover have "p_io (p@[tt]) = (p_io p)@[(t_input tt, t_output tt)]"
        by auto

      ultimately have "(p_io p)@[(t_input tt,t_output tt)] \<in> L A"
        using language_state_containment[of A "initial A" "p@[tt]"] by metis

      let ?x = "t_input tt"
      have "?x \<in> set (inputs S)"
        using \<open>tt \<in> h A\<close> is_separator_simps(16)[OF assms(6)] assms(7) by auto
      then obtain y where "(p_io p)@[(?x,y)] \<in> LS S s1"
        using completely_specified_language_extension[OF \<open>completely_specified S\<close> \<open>s1 \<in> nodes S\<close> \<open>p_io p \<in> LS S s1\<close> ] by auto

      then have "p_io p @ [(?x, y)] \<in> LS A (initial A)"
        using pass_ATC_io_explicit_io_tuple(1)[OF p1 p2 p3 p4 \<open>(p_io p)@[(t_input tt,t_output tt)] \<in> L A\<close>]
        unfolding from_FSM_language[OF \<open>s1 \<in> nodes S\<close>] by auto

      then obtain tt' where "path A (initial A) (p@[tt'])" and "t_input tt' = ?x" and "t_output tt' = y"
        using language_path_append_transition_observable[OF _ \<open>path A (initial A) p\<close> \<open>observable A\<close>] by blast

      then have "p_io (p @ [tt']) \<in> LS S s1"
        using \<open>(p_io p)@[(?x,y)] \<in> LS S s1\<close> by auto

      
      then show ?thesis
        using \<open>path A (initial A) (p@[tt'])\<close> by meson 
    qed

    moreover have "target p (initial A) \<noteq> t2"
      using pass_separator_ATC_pass_left(1)[OF assms(1,2,3,4,5,6,7) \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> assms(8,9)] by assumption

    ultimately show "(target p (initial A) \<noteq> t2) \<and> (target p (initial A) = t1 \<or> (\<exists> t . path A (initial A) (p@[t]) \<and> p_io (p@[t]) \<in> LS S s1))"
      by simp
  qed


  (* largest path that satisfies (path A (initial A) p) and (p_io p \<in> LS T t1) cannot be extended further and must thus target (Inr q1)  *)

  have "acyclic A"
    using \<open>is_ATC A\<close> is_ATC_def by auto
  then have "finite {p . path A (initial A) p}"
    by (meson acyclic_finite_paths) 
  then have "finite {p . path A (initial A) p \<and> p_io p \<in> LS S s1}"
    by auto

  have "[] \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1}"
    using \<open>s1 \<in> nodes S\<close> by auto
  then have "{p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<noteq> {}"
    by blast

  have scheme: "\<And> S . finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> x \<in> S . \<forall> y \<in> S . length y \<le> length x"
    by (meson leI max_length_elem)
    
    
  obtain p where "p \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1}" and "\<And> p' . p' \<in> {p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<Longrightarrow> length p' \<le> length p"
    using scheme[OF \<open>finite {p . path A (initial A) p \<and> p_io p \<in> LS S s1}\<close> \<open>{p . path A (initial A) p \<and> p_io p \<in> LS S s1} \<noteq> {}\<close>] 
    by blast
  then have "path A (initial A) p" and "p_io p \<in> LS S s1" and "\<And> p' . path A (initial A) p' \<Longrightarrow> p_io p' \<in> LS S s1 \<Longrightarrow> length p' \<le> length p"
    by blast+

  have "target p (initial A) = t1"
    using path_ext[OF \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close>] \<open>\<And> p' . path A (initial A) p' \<Longrightarrow> p_io p' \<in> LS S s1 \<Longrightarrow> length p' \<le> length p\<close>
    by (metis (no_types, lifting) Suc_n_not_le_n length_append_singleton) 

  then show "\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t1"
    using \<open>path A (initial A) p\<close> \<open>p_io p \<in> LS S s1\<close> by blast

  show "\<nexists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t2"
    using path_ext by blast
qed


lemma pass_separator_ATC_completely_specified_right :
  assumes "observable S" 
  and     "observable M"
  and     "s2 \<in> nodes S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "is_separator M q1 q2 A t1 t2"
  and     "set (inputs S) = set (inputs M)"
  and     "q1 \<noteq> q2"
  and     "pass_separator_ATC S A s2 t1"
  and     "completely_specified S"
shows "\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target p (initial A) = t2"
and   "\<not> (\<exists> p . path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target p (initial A) = t1)"
  using pass_separator_ATC_completely_specified_left[OF assms(1,2,3,5,4) is_separator_sym[OF assms(6)] assms(7) _ assms(9,10)] assms(8) by blast+





  





lemma pass_separator_ATC_reduction_distinction : 
  assumes "observable M"
  and     "observable S"
  and     "set (inputs S) = set (inputs M)"
  and     "pass_separator_ATC S A s1 t2"
  and     "pass_separator_ATC S A s2 t1"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "s1 \<in> nodes S"
  and     "s2 \<in> nodes S"
  and     "is_separator M q1 q2 A t1 t2"  
  and     "completely_specified S"
shows "s1 \<noteq> s2"
proof -



  (* As s1 passes A against t2, t1 must be reached during application, while
     at the same time t2 is never reached *)

  have "\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t1"
  and  "\<not> (\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s1 \<and> target p (initial A) = t2)"
    using pass_separator_ATC_completely_specified_left[OF assms(2,1,9,6,7,11,3,8,4,12)] by blast+

  (* As s2 passes A against t1, t2 must be reached during application, while
     at the same time t1 is never reached *)
  
  moreover have "\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target p (initial A) = t2"
           and  "\<not> (\<exists>p. path A (initial A) p \<and> p_io p \<in> LS S s2 \<and> target p (initial A) = t1)"
    using pass_separator_ATC_completely_specified_right[OF assms(2,1,10,6,7,11,3,8,5,12)] by blast+

  (* Thus it is not possible for (s1 = s2) to hold *)

  ultimately show "s1 \<noteq> s2"
    by blast
qed



lemma pass_separator_ATC_failure_left : 
  assumes "observable M"
  and     "observable S"
  and     "set (inputs S) = set (inputs M)"
  and     "is_separator M q1 q2 A t1 t2"
  and     "\<not> pass_separator_ATC S A s1 t2"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "s1 \<in> nodes S"  
shows "LS S s1 - LS M q1 \<noteq> {}"
proof -
  
  have p1: "is_ATC A"
    using separator_is_ATC[OF assms(4,1,6,7)] by assumption

  have p2: "observable (from_FSM S s1)"
    using from_FSM_observable[OF assms(2,9)] by assumption

  have p3: "observable (from_FSM M q1)"
    using from_FSM_observable[OF assms(1,6)] by assumption

  have p4: "set (inputs A) \<subseteq> set (inputs (from_FSM M q1))"
    using is_separator_simps(16)[OF assms(4)] 
    unfolding from_FSM_simps is_submachine.simps canonical_separator_simps assms(3) by auto

  have p5: "set (inputs (from_FSM S s1)) = set (inputs (from_FSM M q1))"
    using assms(3) unfolding from_FSM_simps by assumption

  have p6: "pass_ATC (from_FSM M q1) A {t2}"
    using pass_separator_ATC_from_separator_left[OF assms(1,6,7,4)] by auto

  have p7: "\<not> pass_ATC (from_FSM S s1) A {t2}"
    using assms(5) by auto

  show ?thesis
    using pass_ATC_fail_no_reduction[OF p1 p2 p3 p4 p5 p6 p7]
    unfolding from_FSM_language[OF \<open>q1 \<in> nodes M\<close>] from_FSM_language[OF \<open>s1 \<in> nodes S\<close>] by blast
qed


lemma pass_separator_ATC_failure_right : 
  assumes "observable M"
  and     "observable S"
  and     "set (inputs S) = set (inputs M)"
  and     "is_separator M q1 q2 A t1 t2"
  and     "\<not> pass_separator_ATC S A s2 t1"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "q1 \<noteq> q2"
  and     "s2 \<in> nodes S"  
shows "LS S s2 - LS M q2 \<noteq> {}"
  using pass_separator_ATC_failure_left[OF assms(1-3) is_separator_sym[OF assms(4)] assms(5,7,6) _ assms(9)] assms(8) by blast



subsection \<open>ATCs Represented as Sets of IO Sequences\<close>

fun atc_to_io_set :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> (Input \<times> Output) list set" where
  "atc_to_io_set M A = L M \<inter> L A"


(* very inefficient calculation *)
fun atc_to_io_list :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> (Input \<times> Output) list list" where
  "atc_to_io_list M A = (let LA = set (map p_io (distinct_paths_up_to_length_from_initial A (size A -1)));
                             LM = map p_io (paths_up_to_length M (initial M) (size A -1))
                          in filter (\<lambda>io . io \<in> LA) LM)"

value "the (calculate_state_separator_from_s_states M_ex_9 0 3)"
value "atc_to_io_list M_ex_9 (the (calculate_state_separator_from_s_states M_ex_9 0 3))"

lemma acyclic_language_alt_def :
  assumes "acyclic M"
  shows "set (map p_io (distinct_paths_up_to_length_from_initial M (size M -1))) = L M"
proof -
  let ?ps = "distinct_paths_up_to_length_from_initial M (size M - 1)"
  have "\<And> p . path M (initial M) p \<Longrightarrow> length p \<le> FSM.size M - 1"
    using acyclic_path_length[OF assms] by fastforce
  then have "set ?ps = {p. path M (initial M) p}"
    using distinct_paths_up_to_length_path_set[of M "size M - 1"]
    using assms unfolding acyclic.simps by blast
  then show ?thesis unfolding LS.simps by auto
qed


lemma atc_to_io_set_code : 
  assumes "acyclic A"
  shows "atc_to_io_set M A = set (atc_to_io_list M A)"
proof -

  have "set (map p_io (distinct_paths_up_to_length_from_initial A (size A -1))) = L A"
    using acyclic_language_alt_def[OF assms]  by assumption
  have "set (map p_io (paths_up_to_length M (initial M) (size A -1))) = {io \<in> L M . length io \<le> size A - 1}"
    using paths_up_to_length_path_set[OF nodes.initial, of M "size A - 1"] unfolding LS.simps by auto
   
  
  have "set (atc_to_io_list M A) = Set.filter (\<lambda>io. io \<in> L A)  {io \<in> L M. length io \<le> FSM.size A - 1}"
    unfolding atc_to_io_list.simps Let_def 
    using filter_set[of "(\<lambda>io . io \<in> set (map p_io (distinct_paths_up_to_length_from_initial A (size A -1))))" "map p_io (paths_up_to_length M (initial M) (size A -1))"] 
    unfolding \<open>set (map p_io (distinct_paths_up_to_length_from_initial A (size A -1))) = L A\<close>
    unfolding \<open>set (map p_io (paths_up_to_length M (initial M) (size A -1))) = {io \<in> L M . length io \<le> size A - 1}\<close> by blast
  then have *: "set (atc_to_io_list M A) = {io \<in> L M . io \<in> L A \<and> length io \<le> FSM.size A - 1}"
    by force
  
  
  moreover have "\<And> io . io \<in> L A \<Longrightarrow> length io \<le> FSM.size A - 1"
    using acyclic_path_length'[OF assms] by auto
  ultimately show ?thesis by force
qed



(* TODO: define pass relation on io sequence sets and relate to pass_ATC *)

definition pass_io_set :: "('a,'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "pass_io_set M ios = (\<forall> io x y . io@[(x,y)] \<in> ios \<longrightarrow> (\<forall> y' . io@[(x,y')] \<in> L M \<longrightarrow> io@[(x,y')] \<in> ios))"

definition pass_io_set_maximal :: "('a,'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "pass_io_set_maximal M ios = (\<forall> io x y io' . io@[(x,y)]@io' \<in> ios \<longrightarrow> (\<forall> y' . io@[(x,y')] \<in> L M \<longrightarrow> (\<exists> io''. io@[(x,y')]@io'' \<in> ios)))"


lemma pass_io_set_from_pass_io_set_maximal :
  "pass_io_set_maximal M ios = pass_io_set M {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios}"
proof -
  have "\<And> io x y io' . io@[(x,y)]@io' \<in> ios \<Longrightarrow> io@[(x,y)] \<in> {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios}"
    by auto
  moreover have "\<And> io x y . io@[(x,y)] \<in> {io' . \<exists> io io'' . io = io'@io'' \<and> io \<in> ios} \<Longrightarrow> \<exists> io' . io@[(x,y)]@io' \<in> ios"
    by auto
  ultimately show ?thesis
    unfolding pass_io_set_def pass_io_set_maximal_def
    by meson 
qed



(* TODO: move *)
lemma finite_set_elem_maximal_extension_ex :
  assumes "xs \<in> S"
  and     "finite S"
shows "\<exists> ys . xs@ys \<in> S \<and> \<not> (\<exists> zs . zs \<noteq> [] \<and> xs@ys@zs \<in> S)"
using \<open>finite S\<close> \<open>xs \<in> S\<close> proof (induction S arbitrary: xs)
  case empty
  then show ?case by auto
next
  case (insert x S)

  consider (a) "\<exists> ys . x = xs@ys \<and> \<not> (\<exists> zs . zs \<noteq> [] \<and> xs@ys@zs \<in> (insert x S))" |
           (b) "\<not>(\<exists> ys . x = xs@ys \<and> \<not> (\<exists> zs . zs \<noteq> [] \<and> xs@ys@zs \<in> (insert x S)))"
    by blast
  then show ?case proof cases
    case a
    then show ?thesis by auto
  next
    case b
    then show ?thesis proof (cases "\<exists> vs . vs \<noteq> [] \<and> xs@vs \<in> S")
      case True
      then obtain vs where "vs \<noteq> []" and "xs@vs \<in> S"
        by blast
      
      have "\<exists>ys. xs @ (vs @ ys) \<in> S \<and> (\<nexists>zs. zs \<noteq> [] \<and> xs @ (vs @ ys) @ zs \<in> S)"
        using insert.IH[OF \<open>xs@vs \<in> S\<close>] by auto
      then have "\<exists>ys. xs @ (vs @ ys) \<in> S \<and> (\<nexists>zs. zs \<noteq> [] \<and> xs @ (vs @ ys) @ zs \<in> (insert x S))"
        using b 
        unfolding append.assoc append_is_Nil_conv append_self_conv insert_iff
        by (metis append.assoc append_Nil2 append_is_Nil_conv same_append_eq) 
      then show ?thesis by blast
    next
      case False
      then show ?thesis using insert.prems
        by (metis append_is_Nil_conv append_self_conv insertE same_append_eq) 
    qed
  qed
qed




lemma pass_io_set_maximal_from_pass_io_set :
  assumes "finite ios"
  and     "\<And> io' io'' . io'@io'' \<in> ios \<Longrightarrow> io' \<in> ios"
shows "pass_io_set M ios = pass_io_set_maximal M {io' \<in> ios . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> ios)}"
proof -
  have "\<And> io x y . io@[(x,y)] \<in> ios \<Longrightarrow> \<exists> io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)}"
  proof -
    fix io x y assume "io@[(x,y)] \<in> ios"
    show "\<exists> io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)}"
      using finite_set_elem_maximal_extension_ex[OF \<open>io@[(x,y)] \<in> ios\<close> assms(1)] by force
  qed
  moreover have "\<And> io x y io' . io@[(x,y)]@io' \<in> {io'' \<in> ios . \<not> (\<exists> io''' . io''' \<noteq> [] \<and> io''@io''' \<in> ios)} \<Longrightarrow> io@[(x,y)] \<in> ios"
    using \<open>\<And> io' io'' . io'@io'' \<in> ios \<Longrightarrow> io' \<in> ios\<close> by force
  ultimately show ?thesis
    unfolding pass_io_set_def pass_io_set_maximal_def 
    by meson 
qed

(* TODO: move *)
lemma language_split :
  assumes "io1@io2 \<in> L M"
  obtains p1 p2 where "path M (initial M) (p1@p2)" and "p_io p1 = io1" and "p_io p2 = io2"
proof -
  from assms obtain p where "path M (initial M) p" and "p_io p = io1 @ io2"
    by auto

  let ?p1 = "take (length io1) p"
  let ?p2 = "drop (length io1) p"

  have "path M (initial M) (?p1@?p2)"
    using \<open>path M (initial M) p\<close> by simp 
  moreover have "p_io ?p1 = io1" 
    using \<open>p_io p = io1 @ io2\<close>
    by (metis append_eq_conv_conj take_map) 
  moreover have "p_io ?p2 = io2" 
    using \<open>p_io p = io1 @ io2\<close>
    by (metis append_eq_conv_conj drop_map)
  ultimately show ?thesis using that by blast
qed

(* TODO: move *)
lemma acyclic_observable_maximal_io_sequences :
  assumes "acyclic M"
  and     "observable M"
  shows "set (map p_io (maximal_acyclic_paths M)) = {io' \<in> L M . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> L M)}"
proof -

  let ?ps = "distinct_paths_up_to_length_from_initial M (size M - 1)"

  have "\<And> p . path M (initial M) p \<Longrightarrow> length p \<le> FSM.size M - 1"
    using acyclic_path_length[OF assms(1)] by fastforce
  then have "set ?ps = {p. path M (initial M) p}"
    using distinct_paths_up_to_length_path_set[of M "size M - 1"]
    using assms unfolding acyclic.simps by blast
  then have "set (maximal_acyclic_paths M) = {p. path M (initial M) p \<and> \<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')}"
    by auto
  then have "set (map p_io (maximal_acyclic_paths M)) = {p_io p | p . path M (initial M) p \<and> \<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')}"
    by auto
  also have "... = {p_io p | p. path M (initial M) p \<and> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))}"
    unfolding is_prefix_prefix by auto
  also have "... = {io' \<in> L M . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> L M)}"
  proof -
    have "\<And> io . io \<in> {p_io p | p. path M (initial M) p \<and> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))} \<Longrightarrow> io \<in> {io' \<in> L M . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> L M)}"
    proof -
      fix io assume "io \<in> {p_io p | p. path M (initial M) p \<and> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))}"
      then obtain p where "p_io p = io" and "path M (initial M) p" and "\<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))"
        by blast
      then have "io \<in> L M" by auto
      moreover have "\<not> (\<exists> io'' . io'' \<noteq> [] \<and> io@io'' \<in> L M)"
      proof 
        assume "\<exists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS M (initial M)"
        then obtain io'' where "io'' \<noteq> []" and "io @ io'' \<in> LS M (initial M)" by blast
        then obtain p' p'' where "path M (initial M) (p'@p'')" and "p_io p' = io" and "p_io p'' = io''" 
          using language_split by blast
        then have "path M (initial M) p'" and "p_io p' = p_io p"
          using \<open>p_io p = io\<close> by auto
        
        have "\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p')"
          using observable_path_unique[OF assms(2) \<open>path M (initial M) p'\<close> \<open>path M (initial M) p\<close> \<open>p_io p' = p_io p\<close>] 
          using \<open>io'' \<noteq> []\<close> \<open>path M (initial M) (p'@p'')\<close> \<open>p_io p'' = io''\<close> by auto
        then show "False" 
          using \<open>\<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))\<close> by blast
      qed
      ultimately show "io \<in> {io' \<in> L M . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> L M)}" by blast
    qed
    moreover have "\<And> io . io \<in> {io' \<in> L M . \<not> (\<exists> io'' . io'' \<noteq> [] \<and> io'@io'' \<in> L M)} \<Longrightarrow> io \<in> {p_io p | p. path M (initial M) p \<and> \<not>(\<exists> p' . p' \<noteq> [] \<and> path M (initial M) (p@p'))}"
    proof -
    fix io :: "(integer \<times> integer) list"
      assume "io \<in> {io' \<in> LS M (initial M). \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> LS M (initial M)}"
      then have f1: "io \<in> LS M (initial M) \<and> (\<forall>ps. ps = [] \<or> io @ ps \<notin> LS M (initial M))"
        by blast
      obtain pps :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
        f2: "\<forall>x0. (\<exists>v2. v2 \<noteq> [] \<and> path M (initial M) (x0 @ v2)) = (pps x0 \<noteq> [] \<and> path M (initial M) (x0 @ pps x0))"
        by moura
      have f3: "\<exists>ps. io = p_io ps \<and> path M (initial M) ps"
        using f1 by simp
      obtain ppsa :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
        "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (ppsa x0 x1 x2) \<and> path x2 x1 (ppsa x0 x1 x2))"
        by moura
      then have "\<forall>f a ps. ((\<nexists>psa. ps = p_io psa \<and> path f a psa) \<or> ps = p_io (ppsa ps a f) \<and> path f a (ppsa ps a f)) \<and> ((\<exists>psa. ps = p_io psa \<and> path f a psa) \<or> (\<forall>psa. ps \<noteq> p_io psa \<or> \<not> path f a psa))"
        by blast
      then have f4: "io = p_io (ppsa io (initial M) M) \<and> path M (initial M) (ppsa io (initial M) M)"
        using f3 by blast
      moreover
      { assume "io @ p_io (pps (ppsa io (initial M) M)) \<notin> LS M (initial M)"
        then have "\<forall>ps. p_io (ppsa io (initial M) M) @ p_io (pps (ppsa io (initial M) M)) \<noteq> p_io ps \<or> \<not> path M (initial M) ps"
          using f4 by simp
        then have "pps (ppsa io (initial M) M) = [] \<or> \<not> path M (initial M) (ppsa io (initial M) M @ pps (ppsa io (initial M) M))"
          by simp
        then have "\<exists>ps. io = p_io ps \<and> path M (initial M) ps \<and> (\<forall>psa. psa = [] \<or> \<not> path M (initial M) (ps @ psa))"
          using f4 f2 by (metis (no_types)) }
      ultimately have "\<exists>ps. io = p_io ps \<and> path M (initial M) ps \<and> (\<forall>psa. psa = [] \<or> \<not> path M (initial M) (ps @ psa))"
        using f2 f1 by (meson map_is_Nil_conv)
      then show "io \<in> {p_io ps |ps. path M (initial M) ps \<and> (\<nexists>psa. psa \<noteq> [] \<and> path M (initial M) (ps @ psa))}"
        by simp
    qed
    ultimately show ?thesis by blast
  qed
  finally show ?thesis by assumption
qed


(* Attempt to calc atc_to_io_list_maximal for ATCs, probably unnecessary *)
(* 

definition atc_to_io_set_maximal :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> (Input \<times> Output) list set" where
  "atc_to_io_set_maximal M A = {io' \<in> atc_to_io_set M A. \<nexists>io''. io'' \<noteq> [] \<and> io' @ io'' \<in> atc_to_io_set M A}"

fun atc_to_io_list_maximal :: "('a,'b) FSM_scheme \<Rightarrow> ('c,'d) FSM_scheme \<Rightarrow> (Input \<times> Output) list list" where
  "atc_to_io_list_maximal M A = (let LA = set (map p_io (maximal_acyclic_paths A));
                                     LM = map p_io (paths_up_to_length M (initial M) (size A -1))
                                  in filter (\<lambda>io . io \<in> LA) LM)"

lemma atc_to_io_list_maximal_code :
  assumes "is_ATC A"
  shows "atc_to_io_set_maximal M A = set (atc_to_io_list_maximal M A)"
proof -

  have "acyclic A" and "observable A"
    using assms unfolding is_ATC_def by auto

  have "set (map p_io (maximal_acyclic_paths A)) = {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)}"
    using acyclic_observable_maximal_io_sequences[OF \<open>acyclic A\<close> \<open>observable A\<close>] by assumption
  have "set (map p_io (paths_up_to_length M (initial M) (size A -1))) = {io \<in> L M . length io \<le> size A - 1}"
    using paths_up_to_length_path_set[OF nodes.initial, of M "size A - 1"] unfolding LS.simps by auto
   
  have scheme: "\<And> S2 S1 . Set.filter (\<lambda>x . x \<in> S2) S1 = S1 \<inter> S2" by auto

  have "set (atc_to_io_list_maximal M A) = Set.filter (\<lambda>io. io \<in> {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)})  {io \<in> L M. length io \<le> FSM.size A - 1}"
    unfolding atc_to_io_list_maximal.simps Let_def 
    using filter_set[of "(\<lambda>io. io \<in> {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)})" "map p_io (paths_up_to_length M (initial M) (size A -1))"] 
    unfolding \<open>set (map p_io (maximal_acyclic_paths A)) = {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)}\<close>
    unfolding \<open>set (map p_io (paths_up_to_length M (initial M) (size A -1))) = {io \<in> L M . length io \<le> size A - 1}\<close> by force
  then have "set (atc_to_io_list_maximal M A) = {io \<in> LS M (initial M). length io \<le> FSM.size A - 1} \<inter> {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)}"
    unfolding scheme by assumption
  moreover have "\<And> io . io \<in> L A \<Longrightarrow> length io \<le> FSM.size A - 1"
    using acyclic_path_length'[OF \<open>acyclic A\<close>] by auto
  ultimately have *: "set (atc_to_io_list_maximal M A) = L M \<inter> {io \<in> LS A (initial A). \<nexists>io''. io'' \<noteq> [] \<and> io @ io'' \<in> LS A (initial A)}"
    by blast
  
  show ?thesis
    unfolding atc_to_io_set_maximal_def atc_to_io_set.simps * 
qed

*)






lemma pass_io_set_from_pass_separator :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "pass_separator_ATC S A s1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "s1 \<in> nodes S"
  and     "set (inputs S) = set (inputs M)"
shows "pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
proof (rule ccontr) 
  assume "\<not> pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  then obtain io x y y' where "io@[(x,y)] \<in> (atc_to_io_set (from_FSM M q1) A)" and "io@[(x,y')] \<in> L (from_FSM S s1)" and "io@[(x,y')] \<notin> (atc_to_io_set (from_FSM M q1) A)" 
    unfolding pass_io_set_def by blast

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,3,5,6)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF \<open>observable S\<close> \<open>s1 \<in> nodes S\<close>] by assumption
  have "set (inputs A) \<subseteq> set (inputs (from_FSM S s1))"
    using assms(1) unfolding is_separator_def from_FSM_simps \<open>set (inputs S) = set (inputs M)\<close> by auto

  obtain y'' where "io @ [(x, y'')] \<in> LS A (initial A)"
    using \<open>io@[(x,y)] \<in> (atc_to_io_set (from_FSM M q1) A)\<close> unfolding atc_to_io_set.simps by blast

  have "pass_ATC (from_FSM S s1) A {t2}"
    using \<open>pass_separator_ATC S A s1 t2\<close> by auto

  then have "io @ [(x, y')] \<in> L A"
    using pass_ATC_fail[OF \<open>is_ATC A\<close> 
                           \<open>observable (from_FSM S s1)\<close> 
                           \<open>set (inputs A) \<subseteq> set (inputs (from_FSM S s1))\<close> 
                           \<open>io @ [(x, y'')] \<in> LS A (initial A)\<close>
                           \<open>io@[(x,y')] \<in> L (from_FSM S s1)\<close>,
                        of "{t2}" ]
    by auto

  have "io_targets A (io @ [(x, y')]) (initial A) \<inter> {t2} = {}"  
    using pass_ATC_io(2)[OF \<open>pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>set (inputs A) \<subseteq> set (inputs (from_FSM S s1))\<close> \<open>io @ [(x, y')] \<in> L A\<close> \<open>io@[(x,y')] \<in> L (from_FSM S s1)\<close>]
    unfolding fst_conv by blast

  then have "io @ [(x, y')] \<in> LS M q1"
    using separator_language(1,3,4)[OF assms(1) \<open>io @ [(x, y')] \<in> L A\<close>] 
    by (metis UnE Un_Diff_cancel \<open>io @ [(x, y')] \<in> LS A (initial A)\<close> assms(1) disjoint_insert(2) is_separator_sym separator_language(1) singletonI)
  then show "False"
    using \<open>io @ [(x, y')] \<in> L A\<close> \<open>io@[(x,y')] \<notin> (atc_to_io_set (from_FSM M q1) A)\<close> 
    unfolding atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> nodes M\<close>]
    by blast
qed

(* TODO: move *)
lemma language_io : 
  assumes "io \<in> L M"
  and     "(x,y) \<in> set io"
shows "x \<in> set (inputs M)"
and   "y \<in> set (outputs M)"
proof -
  obtain p where "path M (initial M) p" and "p_io p = io"
    using \<open>io \<in> L M\<close> by auto
  then obtain t where "t \<in> set p" and "t_input t = x" and "t_output t = y"
    using \<open>(x,y) \<in> set io\<close> by auto
  
  have "t \<in> h M"
    using \<open>path M (initial M) p\<close> \<open>t \<in> set p\<close>
    by (induction p; auto)

  show "x \<in> set (inputs M)"
    using \<open>t \<in> h M\<close> \<open>t_input t = x\<close> by auto

  show "y \<in> set (outputs M)"
    using \<open>t \<in> h M\<close> \<open>t_output t = y\<close> by auto
qed


lemma separator_language_last_left :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "completely_specified M"
  and     "q1 \<in> nodes M"
  and     "io @ [(x, y)] \<in> L A"
obtains y'' where "io@[(x,y'')] \<in> L A \<inter> LS M q1"
proof -
  obtain p t where "path A (initial A) (p@[t])" and "p_io (p@[t]) = io@[(x,y)]"
    using language_initial_path_append_transition[OF \<open>io @ [(x, y)] \<in> L A\<close>] by blast
  then have "\<not> deadlock_state A (target p (initial A))"
    unfolding deadlock_state.simps by fastforce
  have "path A (initial A) p"
    using \<open>path A (initial A) (p@[t])\<close> by auto

  have "p_io p \<in> LS M q1"
    using separator_path_targets(1,2,4)[OF assms(1) \<open>path A (initial A) p\<close>]
    using is_separator_simps(4,5)[OF assms(1)] 
    using \<open>\<not> deadlock_state A (target p (initial A))\<close> by fastforce
  then have "io \<in> LS M q1"
    using \<open>p_io (p@[t]) = io@[(x,y)]\<close> by auto

  have "x \<in> set (inputs A)"
    using \<open>io @ [(x, y)] \<in> L A\<close> language_io(1) 
    by (metis in_set_conv_decomp)
  then have "x \<in> set (inputs M)"
    using is_separator_simps(16)[OF assms(1)] by blast

  then obtain y'' where "io@[(x,y'')] \<in> LS M q1"
    using completely_specified_language_extension[OF \<open>completely_specified M\<close> \<open>q1 \<in> nodes M\<close> \<open>io \<in> LS M q1\<close>] by blast
  then have "io@[(x,y'')] \<in> L A \<inter> LS M q1"
    using is_separator_simps(9)[OF assms(1) _ \<open>io @ [(x, y)] \<in> L A\<close>] by blast
  then show ?thesis 
    using that by blast
qed


lemma separator_language_last_right :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "completely_specified M"
  and     "q2 \<in> nodes M"
  and     "io @ [(x, y)] \<in> L A"
obtains y'' where "io@[(x,y'')] \<in> L A \<inter> LS M q2"
  using separator_language_last_left[OF is_separator_sym[OF assms(1)] assms(2,3,4)] by blast




lemma pass_separator_from_pass_io_set :
  assumes "is_separator M q1 q2 A t1 t2"
  and     "pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "s1 \<in> nodes S"
  and     "set (inputs S) = set (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2"
proof (rule ccontr)
  assume "\<not> pass_separator_ATC S A s1 t2"
  then have "\<not> pass_ATC (from_FSM S s1) A {t2}" by auto

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,3,5,6)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  have "observable (from_FSM S s1)"
    using from_FSM_observable[OF \<open>observable S\<close> \<open>s1 \<in> nodes S\<close>] by assumption
  have "set (inputs A) \<subseteq> set (inputs (from_FSM S s1))"
    using assms(1) unfolding is_separator_def from_FSM_simps \<open>set (inputs S) = set (inputs M)\<close> by auto

  obtain io x y y' where "io @ [(x,y)] \<in> L A"
                         "io @ [(x,y')] \<in> L (from_FSM S s1)"
                         "(io @ [(x,y')] \<notin> L A \<or> io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {})"
    using pass_ATC_io_fail[OF \<open>\<not> pass_ATC (from_FSM S s1) A {t2}\<close> \<open>is_ATC A\<close> \<open>observable (from_FSM S s1)\<close> \<open>set (inputs A) \<subseteq> set (inputs (from_FSM S s1))\<close>]
    using separator_initial(2)[OF assms(1)]  
    using prod.exhaust fst_conv 
    by (metis empty_iff insert_iff)

  show "False" 
  proof (cases "io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {}")
    case True
    then have "io @ [(x,y')] \<in> L A"
      unfolding io_targets.simps LS.simps by force
    
    have "io @ [(x,y')] \<in> LS M q2 - LS M q1"
    proof -
      have "t2 \<noteq> t1"
        by (metis (full_types) \<open>is_separator M q1 q2 A t1 t2\<close> is_separator_simps(15))
      then show ?thesis
        using True separator_language[OF assms(1) \<open>io @ [(x,y')] \<in> L A\<close>] 
        by blast
    qed
    then have "io @ [(x,y')] \<notin> LS M q1" by blast

    obtain y'' where "io @ [(x, y'')] \<in> LS M q1 \<inter> L A"
      using separator_language_last_left[OF assms(1,9,5) \<open>io @ [(x,y)] \<in> L A\<close>] by blast
    then have "io @ [(x, y')] \<in> LS M q1 \<inter> LS A (initial A)"
      using \<open>pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)\<close>
      using \<open>io @ [(x,y')] \<in> L (from_FSM S s1)\<close> 
      unfolding pass_io_set_def atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> nodes M\<close>] by blast

    then show "False" 
      using \<open>io @ [(x,y')] \<notin> LS M q1\<close> by blast
  
  next
    case False  
    then have "io @ [(x,y')] \<notin> L A"
      using \<open>(io @ [(x,y')] \<notin> L A \<or> io_targets A (io @ [(x,y')]) (initial A) \<inter> {t2} \<noteq> {})\<close>
      by blast

    obtain y'' where "io @ [(x, y'')] \<in> LS M q1 \<inter> L A"
      using separator_language_last_left[OF assms(1,9,5) \<open>io @ [(x,y)] \<in> L A\<close>] by blast
    then have "io @ [(x, y')] \<in> L A"
      using \<open>pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)\<close>
      using \<open>io @ [(x,y')] \<in> L (from_FSM S s1)\<close> 
      unfolding pass_io_set_def atc_to_io_set.simps from_FSM_language[OF \<open>q1 \<in> nodes M\<close>] by blast

    then show "False"
      using \<open>io @ [(x,y')] \<notin> L A\<close> by blast
  qed
qed



lemma pass_separator_pass_io_set_iff:
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "s1 \<in> nodes S"
  and     "set (inputs S) = set (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2 \<longleftrightarrow> pass_io_set (from_FSM S s1) (atc_to_io_set (from_FSM M q1) A)"
  using pass_separator_from_pass_io_set[OF assms(1) _ assms(2-8)]
        pass_io_set_from_pass_separator[OF assms(1) _ assms(2-7)] by blast










definition maximal_contained_lists :: "'a list set \<Rightarrow> 'a list set" where 
  "maximal_contained_lists S = {xs \<in> S . \<nexists>ys . ys \<noteq> [] \<and> xs @ ys \<in> S }"

definition maximal_contained_lists' :: "'a list list \<Rightarrow> 'a list list" where
  "maximal_contained_lists' xs = filter (\<lambda>x . (\<forall> y \<in> set xs . is_prefix x y \<longrightarrow> x = y)) xs"


lemma maximal_contained_lists_code[code] :
  "maximal_contained_lists (set xs) = set (maximal_contained_lists' xs)"
proof -
  
  have *: "maximal_contained_lists (set xs) = Set.filter (\<lambda> zs . \<nexists>ys . ys \<noteq> [] \<and> zs @ ys \<in> (set xs)) (set xs)"
    unfolding maximal_contained_lists_def by force

  have "\<And> zs . (\<nexists>ys . ys \<noteq> [] \<and> zs @ ys \<in> (set xs)) = (\<forall> ys \<in> set xs . is_prefix zs ys \<longrightarrow> zs = ys)"
    unfolding is_prefix_prefix by auto
  
  then show ?thesis
    unfolding * maximal_contained_lists'_def 
    unfolding filter_set by auto
qed


lemma pass_separator_pass_io_set_maximal_iff:
  assumes "is_separator M q1 q2 A t1 t2"
  and     "observable M"
  and     "observable S"
  and     "q1 \<in> nodes M"
  and     "q2 \<in> nodes M"
  and     "s1 \<in> nodes S"
  and     "set (inputs S) = set (inputs M)"
  and     "completely_specified M"
shows "pass_separator_ATC S A s1 t2 \<longleftrightarrow> pass_io_set_maximal (from_FSM S s1) (maximal_contained_lists (atc_to_io_set (from_FSM M q1) A))"
proof -

  have "is_ATC A"
    using separator_is_ATC[OF assms(1,2,4,5)]  by assumption
  then have "acyclic A" 
    unfolding is_ATC_def by auto
  then have "finite (L A)"
    unfolding acyclic_alt_def by assumption
  then have *: "finite (atc_to_io_set (from_FSM M q1) A)"
    unfolding atc_to_io_set.simps by blast

  have **: "\<And>io' io''. io' @ io'' \<in> atc_to_io_set (from_FSM M q1) A \<Longrightarrow> io' \<in> atc_to_io_set (from_FSM M q1) A"
    unfolding atc_to_io_set.simps
    using language_prefix[of _ _ "from_FSM M q1" "initial (from_FSM M q1)"]
    using language_prefix[of _ _ "A" "initial A"] by blast

  show ?thesis  
    unfolding pass_separator_pass_io_set_iff[OF assms] maximal_contained_lists_def
    using pass_io_set_maximal_from_pass_io_set[of "(atc_to_io_set (from_FSM M q1) A)" "(from_FSM S s1)", OF * ] ** by blast
qed
  


end