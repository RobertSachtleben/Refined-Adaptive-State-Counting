theory FSM3
imports Main
begin

type_synonym State = nat
type_synonym Input = nat
type_synonym Output = nat
type_synonym Transition = "(nat \<times> nat \<times> nat \<times> nat)"

record FSM = 
  initial :: State 
  inputs  :: "Input list"
  outputs  :: "Output list"  
  transitions :: "Transition list" 

abbreviation "t_source (a :: Transition) \<equiv> fst a" 
abbreviation "t_input  (a :: Transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: Transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: Transition) \<equiv> snd (snd (snd a))"

value "t_source (1,2,3,4)"
value "t_input  (1,2,3,4)"
value "t_output (1,2,3,4)"
value "t_target (1,2,3,4)"



fun is_wf_transition :: "FSM \<Rightarrow> Transition \<Rightarrow> bool" where
  "is_wf_transition M t = ((t_input t) \<in> set (inputs M) \<and> (t_output t) \<in> set (outputs M))"

fun wf_transitions :: "FSM \<Rightarrow> Transition list" where
  "wf_transitions M = filter (is_wf_transition M) (transitions M)"

abbreviation "h M \<equiv> set (wf_transitions M)"



fun pairwise_immediately_reachable :: "FSM \<Rightarrow> (State \<times> State) set" where
  "pairwise_immediately_reachable M =  image (\<lambda> t. (t_source t, t_target t)) (h M)"

lemma wf_transrel_transition_ob : 
  assumes "(q,q') \<in> pairwise_immediately_reachable M"
  obtains t
  where "t \<in> h M"
    and "t_source t = q"
    and "t_target t = q'"
    and "is_wf_transition M t"
  using assms by auto

fun pairwise_reachable :: "FSM \<Rightarrow> (State \<times> State) set" where
  "pairwise_reachable M = trancl (pairwise_immediately_reachable M)"

fun reachable :: "FSM \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool" where
  "reachable M q q' = (q = q' \<or> (q, q') \<in> pairwise_reachable M)"

fun initially_reachable :: "FSM \<Rightarrow> State \<Rightarrow> bool" where
  "initially_reachable M q = reachable M (initial M) q"

fun nodes :: "FSM \<Rightarrow> State set" where
  "nodes M = insert (initial M) (set (filter (initially_reachable M) (map t_target (wf_transitions M))))"


lemma reachable_next :
  assumes "reachable M q (t_source t)"
  and     "t \<in> h M"
shows "reachable M q (t_target t)"
proof -
  have "q = t_source t \<or> (q, t_source t) \<in> pairwise_reachable M"
    using assms(1) by auto
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately show ?thesis 
  proof (cases "q = t_source t")
    case True
    then show ?thesis
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> reachable.simps by blast 
  next
    case False
    then have "(q, t_source t) \<in> pairwise_reachable M" 
      using \<open>q = t_source t \<or> (q, t_source t) \<in> pairwise_reachable M\<close> by auto
    then have "(q, t_target t) \<in> pairwise_reachable M" 
      using \<open>(t_source t, t_target t) \<in> pairwise_reachable M\<close> by auto
    then show ?thesis 
      by auto
  qed
qed

lemma nodes_next :
  assumes "t_source t \<in> nodes M"
  and     "t \<in> h M"
shows "t_target t \<in> nodes M"
proof (cases "t_source t = initial M")
  case True
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately have "(initial M, t_target t) \<in> pairwise_reachable M"
    by auto
  then show ?thesis 
    using assms(2) by auto
next
  case False
  then have "(initial M, t_source t) \<in> pairwise_reachable M"
    using assms(1) by auto
  moreover have "(t_source t, t_target t) \<in> pairwise_reachable M"
    using assms(2) by auto
  ultimately have "(initial M, t_target t) \<in> pairwise_reachable M"
    by auto
  then show ?thesis 
    using assms(2) by auto
qed

fun path :: "FSM \<Rightarrow> State \<Rightarrow> Transition list \<Rightarrow> bool" where
  "path M q [] = True" |
  "path M q (t#ts) = (t \<in> h M \<and> q = t_source t \<and> path M (t_target t) ts)"


(* Example FSM *)
definition "M_ex = (\<lparr> 
                      initial = 2, 
                      inputs = [0,1,2], 
                      outputs = [10,20,30], 
                      transitions = [ (2,1,20,3),
                                      (2,1,30,4),
                                      (3,1,10,5),
                                      (5,2,30,3)]\<rparr>)"

value "nodes M_ex"
value "path M_ex 2 []"
value "path M_ex 3 [(3,1,10,5),(5,2,30,3)]"
value "path M_ex 3 [(3,1,10,5),(5,2,30,4)]"
value "path M_ex 3 [(2,1,20,3)]"
value "path M_ex 2 [(2,1,20,3),(3,1,10,5),(5,2,30,3),(3,1,10,5),(5,2,30,3),(3,1,10,5),(5,2,30,3)]"



end