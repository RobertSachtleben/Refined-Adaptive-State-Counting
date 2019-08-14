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
  shows "set (paths_for_input M q xs) = {p . path M q p \<and> map t_target p = xs}"
using assms proof (induction xs arbitrary: q)
  case Nil
  then show ?case unfolding paths_for_input.simps by auto
next
  case (Cons x xs)
  then show ?case sorry
qed

end (*

(* N - helper *)
fun m_traversal_sequences' :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list set \<Rightarrow> Input list set \<Rightarrow> Input list set" where
  "m_traversal_sequences' M q D m 0 current finished = finished" |
  "m_traversal_sequences' M q D m (Suc k) current finished = 
    m_traversal_sequences' M q D m k
      (image (\<lambda>xsx . (fst xsx)@[snd xsx]) ({xs \<in> current . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . map t_input p = xs \<longrightarrow> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> d) p) \<ge> m))} \<times> (set (outputs M))))
      (finished \<union> {xs \<in> current . \<forall> p \<in> set (paths_for_input M q xs) . map t_input p = xs \<longrightarrow> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> d) p) \<ge> m)})"

(* N *)
fun m_traversal_sequences :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> Input list set" where
  "m_traversal_sequences M q D m = m_traversal_sequences' M q D m (Suc (m * m)) {[]} {}"

end