theory Traversal_Set
imports R_Distinguishability
begin

fun paths_for_input :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> Input list \<Rightarrow> 'a Transition list list" where
  "paths_for_input M q [] = [[]]" |
  "paths_for_input M q (x#xs) = 
    concat (map 
      (\<lambda>y . concat (map 
              (\<lambda> t . (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs)))
              (filter (\<lambda> t . t_source t = q \<and> t_input t = x \<and> t_output t = y) (wf_transitions M)))) 
      (outputs M))"



value "paths_for_input M_ex_9 0 []"
value "paths_for_input M_ex_9 0 [1]"
value "paths_for_input M_ex_9 0 [1,1]"
value "paths_for_input M_ex_9 0 [1,1,1]"
value "paths_for_input M_ex_9 0 [1,1,1,1,1,1,1,1]"


lemma paths_for_input_path_set : 
  assumes "q \<in> nodes M"
  shows "set (paths_for_input M q xs) = {p . path M q p \<and> map t_input p = xs}"
using assms proof (induction xs arbitrary: q)
  case Nil
  then show ?case unfolding paths_for_input.simps by auto
next
  case (Cons x xs)

  have *: "{p . path M q p \<and> map t_input p = x#xs} = {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
  proof -
    have "\<And> p . p \<in> {p . path M q p \<and> map t_input p = x#xs} \<Longrightarrow> p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"    
      using Collect_cong Cons_eq_map_D[of x xs t_input] list.simps(9)[of t_input] by blast
    moreover have "\<And> p . p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}} \<Longrightarrow> p \<in> {p . path M q p \<and> map t_input p = x#xs}"
    proof -
      fix p :: "('a \<times> integer \<times> integer \<times> 'a) list"
      assume "p \<in> {t # p |t p. t \<in> set (wf_transitions M) \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p'. path M (t_target t) p' \<and> map t_input p' = xs}}"
      then obtain pp :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> 'a \<times> integer \<times> integer \<times> 'a" and pps :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
        f1: "p = pp p # pps p \<and> pp p \<in> set (wf_transitions M) \<and> t_source (pp p) = q \<and> t_input (pp p) = x \<and> pps p \<in> {ps. path M (t_target (pp p)) ps \<and> map t_input ps = xs}"
        by fastforce
      then have f2: "path M (t_target (pp p)) (pps p) \<and> map t_input (pps p) = xs"
        by force
      have f3: "path M (t_source (pp p)) (pp p # pps p)"
        using f1 by blast
      have "map t_input p = x # xs"
        using f2 f1 by (metis (no_types) list.simps(9)[of t_input])
      then show "p \<in> {ps. path M q ps \<and> map t_input ps = x # xs}"
        using f3 f1 by simp
    qed
    ultimately show ?thesis by blast
  qed
      
  have "set (paths_for_input M q (x#xs)) \<subseteq> {p . path M q p \<and> map t_input p = x#xs}"
  proof 
    fix p assume "p \<in> set (paths_for_input M q (x#xs))"
    then obtain y where "y \<in> set (outputs M)"
                    and "p \<in> set (concat (map 
                                    (\<lambda> t . (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs)))
                                    (filter (\<lambda> t . t_source t = q \<and> t_input t = x \<and> t_output t = y) (wf_transitions M))))"
      unfolding paths_for_input.simps by force
    then obtain t where "t \<in> h M" and "t_source t = q \<and> t_input t = x" and "t_output t = y"
                    and "p \<in> set (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs))"
      by force
    then obtain p' where "p = t#p'"
                     and "p' \<in> set (paths_for_input M (t_target t) xs)"
      by force

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> h M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      using \<open>p' \<in> set (paths_for_input M (t_target t) xs)\<close> by blast
  
    then have "(t#p') \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using \<open>t \<in> h M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by blast
    then show "p \<in> {p . path M q p \<and> map t_input p = x#xs}" 
      using \<open>p = t#p'\<close> * by blast
  qed
  moreover have "{p . path M q p \<and> map t_input p = x#xs} \<subseteq> set (paths_for_input M q (x#xs))"
  proof 
    fix p assume "p \<in> {p . path M q p \<and> map t_input p = x#xs}"
    then have "p \<in> {t#p | t p . t \<in> h M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using * by blast
    then obtain t p' where "p = t#p'" and "t \<in> h M" and "t_source t = q \<and> t_input t = x" and "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      by blast

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> h M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> set (paths_for_input M (t_target t) xs)" 
      using \<open>p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}\<close> by blast
    moreover have "t_output t \<in> set (outputs M)" 
      using \<open>t \<in> h M\<close> by auto
    ultimately have "t#p' \<in> set (paths_for_input M q (x#xs))"
      unfolding paths_for_input.simps 
      using \<open>t \<in> h M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by force
    then show "p \<in> set (paths_for_input M q (x#xs))"
      using \<open>p = t#p'\<close> by blast
  qed
  
  ultimately show ?case ..
qed



fun paths_up_to_length_or_condition :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a Transition list \<Rightarrow> bool) \<Rightarrow> 'a Transition list \<Rightarrow> 'a Transition list list" where
  "paths_up_to_length_or_condition M q 0 f pref = (if f pref
    then [pref]
    else [])" | 
  "paths_up_to_length_or_condition M q (Suc k) f pref = (if f pref
    then [pref]
    else (concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M (t_target t) k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))"

lemma paths_up_to_length_or_condition_path_set :
  assumes "path M q pref"      
  shows "set (paths_up_to_length_or_condition M q k f pref) = {(pref@p) | p . path M q (pref@p) \<and> length p \<le> k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
using assms proof (induction k arbitrary: q pref)
  case 0
  then show ?case 
      using 0 assms unfolding paths_up_to_length_or_condition.simps by force  
next
  case (Suc k)

  show ?case proof (cases "f pref")
    case True
    then show ?thesis using Suc.prems unfolding paths_up_to_length_or_condition.simps by force
  next
    case False
    then have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M (t_target t) k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    also have "\<dots> = \<Union>{set (paths_up_to_length_or_condition M (t_target t) k f (pref@[t])) | t . t \<in> h M \<and> t_source t = target pref q}"
      by force


    have "\<And> t . t \<in> h M \<Longrightarrow> t_source t = target pref q \<Longrightarrow> set (paths_up_to_length_or_condition M (t_target t) k f (pref@[t])) 
                                                            =  {((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
    proof -
      fix t assume "t \<in> h M" and "t_source t = target pref q"
      then have "path M q (pref@[t])"
        using Suc.prems
        by (simp add: path_append_last) 
      show "set (paths_up_to_length_or_condition M (t_target t) k f (pref@[t])) 
                                                            =  {((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
      using Suc.IH[OF ]

    also have "\<dots> = \<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> h M \<and> t_source t = target pref q}"
      using Suc.IH 

    then show ?thesis using assms Suc unfolding paths_up_to_length_or_condition.simps 
  qed

   

  then show ?case using assms unfolding paths_up_to_length_or_condition.simps
qed


end (*


(* N - helper *)
(*
fun m_traversal_sequences' :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list set \<Rightarrow> Input list set \<Rightarrow> Input list set" where
  "m_traversal_sequences' M q D m 0 current finished = finished" |
  "m_traversal_sequences' M q D m (Suc k) current finished = 
    m_traversal_sequences' M q D m k
      (image (\<lambda>xsx . (fst xsx)@[snd xsx]) ({xs \<in> current . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<times> (set (inputs M))))
      (finished \<union> {xs \<in> current . \<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))})"

value "m_traversal_sequences' M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 3 {[]} {}"
value "m_traversal_sequences' M_ex_9 2 {({0},{0}),({1},{}),({2},{2}),({3},{3})} 4 100  {[]} {}"*)

fun lists_up_to_length :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "lists_up_to_length xs 0 = [[]]" |
  "lists_up_to_length xs (Suc n) = (lists_up_to_length xs n) @ (lists_of_length xs (Suc n))"

lemma lists_up_to_length_list_set : "set (lists_up_to_length xs k) = {xs' . length xs' \<le> k \<and> set xs' \<subseteq> set xs}"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case 
    using lists_of_length_list_set[of xs "Suc k"] unfolding lists_up_to_length.simps by auto
qed


(* TODO: extremely slow *)
fun m_traversal_sequences_list :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list list" where
  "m_traversal_sequences_list M q D m k = (filter ((\<lambda> xs . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                          \<not>(\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))))
                                          (lists_up_to_length (inputs M) k))"

lemma m_traversal_sequences_list_set :
  "set (m_traversal_sequences_list M q D m k) = {xs . length xs \<le> k \<and> set xs \<subseteq> set (inputs M) \<and>
                                                  (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                  \<not>(\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
  unfolding m_traversal_sequences_list.simps using lists_up_to_length_list_set[of "inputs M" k] by force

value "m_traversal_sequences_list M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 4"


lemma m_traversal_sequences_bound :
  assumes "\<And> q . q \<in> nodes M \<Longrightarrow> \<exists> d \<in> D . q \<in> fst d"
      and "path M q p"
      and "length p \<ge> Suc ((size M)*m)"
    shows "\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))"
  sorry
  


(* TODO: very awkward, try forward approach similar to distinct path calculation? *)
fun m_traversal_sequences' :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list set \<Rightarrow> Input list set \<Rightarrow> Input list set" where
  "m_traversal_sequences' M q D m 0 current finished = finished" |
  "m_traversal_sequences' M q D m (Suc k) current finished = 
    m_traversal_sequences' M q D m k
      ({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (current \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})
      (finished \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (current \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"

value "m_traversal_sequences' M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 3 {[]} {}"
(*value "m_traversal_sequences' M_ex_9 2 {({0},{0}),({1},{}),({2},{2}),({3},{3})} 4 100  {[]} {}"*)


lemma m_traversal_sequences'_set_internal : 
  assumes "\<And> xs p . xs \<in> X \<Longrightarrow> \<not> (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"
  shows "m_traversal_sequences' M q D m k X Y = Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> X \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
using assms proof (induction k arbitrary: X Y)
  case 0
  then show ?case unfolding m_traversal_sequences'.simps by force
next
  case (Suc k)

  have *: "(\<And>xs. xs \<in> {xs \<in> (\<lambda>xsx. fst xsx @ [snd xsx]) ` (X \<times> set (inputs M)).
               \<not> (\<forall>p\<in>set (paths_for_input M q xs).
                      \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))} \<Longrightarrow>
         \<not> (\<forall>p\<in>set (paths_for_input M q xs).
                \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)))"
    by blast

  have "m_traversal_sequences' M q D m (Suc k) X Y =
          m_traversal_sequences' M q D m k
            ({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})
            (Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
    (is "?m1 = m_traversal_sequences' M q D m k ?X ?Y")
    by auto

  moreover have "m_traversal_sequences' M q D m k ?X ?Y = 
          ?Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> ?X \<and>
                  (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                  \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
    using Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                     "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"]
    
          *
    by blast
  

  moreover have 
    "{xs' @ xs |xs' xs. set xs \<subseteq> set (inputs M) \<and> length xs \<le> Suc k \<and>  xs' \<in> X \<and>
           (\<forall>p \<in> set (paths_for_input M q (xs' @ xs)). \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) \<and>
           \<not>(\<forall>p \<in> set (paths_for_input M q (butlast (xs' @ xs))). \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))}
    = {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}
        \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<and>
            (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
            \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
    (is "?S1 = ?S2")
  proof 
    show "?S1 \<subseteq> ?S2"
    
    

end (*
  ultimately show ?case by auto
qed




  note Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                 "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})",
              OF ]

  show ?case unfolding m_traversal_sequences'.simps 
    using Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                 "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"]
          *  
qed


lemma m_traversal_sequences'_set_internal : 
  (*assumes "q \<in> nodes M"*)
  (*assumes "\<And> xs p . xs \<in> X \<Longrightarrow> \<not> (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"*)
  assumes "X \<inter> Y = {}"
  shows "m_traversal_sequences' M q D m (Suc k) X Y = Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> (Suc k) \<and> xs' \<in> X \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
using assms proof (induction k arbitrary: X Y)
  case 0
  then show ?case unfolding m_traversal_sequences'.simps by forc
next
  case (Suc k)
  note Suc.IH[of "(image (\<lambda>xsx . (fst xsx)@[snd xsx]) ({xs \<in> X . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<times> (set (inputs M))))"
                 "(Y \<union> {xs \<in> X . \<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))})"]
  then show ?case unfolding m_traversal_sequences'.simps 
qed



lemma m_traversal_sequences'_set : 
  (*assumes "q \<in> nodes M"*)
  shows "m_traversal_sequences' M q D m k {[]} {} = {xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
proof (induction k arbitrary: q)
  case 0
  
  then show ?case unfolding m_traversal_sequences'.simps by force 
next
  case (Suc k)
  then show ?case unfolding m_traversal_sequences'.simps sorry
qed


(* N *)
fun m_traversal_sequences :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> Input list set" where
  "m_traversal_sequences M q D m = m_traversal_sequences' M q D m (Suc ((size M) * m)) {[]} {}"

end