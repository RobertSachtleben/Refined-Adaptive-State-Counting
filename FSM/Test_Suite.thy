theory Test_Suite
imports Traversal_Set State_Preamble State_Separator
begin

type_synonym IO_Sequence = "(Input \<times> Output) list"
type_synonym Preamble_Sequence = IO_Sequence
type_synonym Traversal_Sequence = IO_Sequence
type_synonym Test_Sequences = "IO_Sequence list"

type_synonym Test_Case = "(Preamble_Sequence \<times> ((Traversal_Sequence \<times> Test_Sequences) list))"
type_synonym Test_Case' = "(Preamble_Sequence set \<times> ((Traversal_Sequence \<times> Test_Sequences) list))"

fun contains_io_sequence' :: "'a Transition set \<Rightarrow> 'a \<Rightarrow> IO_Sequence \<Rightarrow> bool" where
  "contains_io_sequence' H q [] = True" |
  "contains_io_sequence' H q (io#ios) = (\<exists> t \<in> H . t_source t = q \<and> t_input t = fst io \<and> t_output t = snd io \<and> contains_io_sequence' H (t_target t) ios)"

value "contains_io_sequence' (h M_ex_H) 1 [(0,0)]"
value "contains_io_sequence' (h M_ex_H) 1 [(0,1),(0,0)]"
value "contains_io_sequence' (h M_ex_H) 1 [(0,1),(0,0),(0,1),(0,0),(0,1),(0,0),(0,1),(0,0)]"
value "contains_io_sequence' (h M_ex_H) 1 [(0,1),(0,0),(0,1),(0,0),(0,1),(0,0),(0,1),(0,0),(0,0)]"


definition contains_io_sequence :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> IO_Sequence \<Rightarrow> bool" where
  "contains_io_sequence M q io = contains_io_sequence' (h M) q io"



lemma contains_io_sequence_soundness :
  assumes "q \<in> nodes M"
  and     "contains_io_sequence M q io"
shows "io \<in> LS M q"
proof -
  have "\<exists> p . path M q p \<and> p_io p = io"
  using assms proof (induction io arbitrary: q)
    case Nil
    then show ?case by auto
  next
    case (Cons io ios)
    then obtain t where "t \<in> h M" and "t_source t = q" and "t_input t = fst io" and "t_output t = snd io" and "contains_io_sequence M (t_target t) ios"
      unfolding contains_io_sequence_def by auto
   
    obtain p where "path M (t_target t) p" and "p_io p = ios"
      using Cons.IH[OF wf_transition_target[OF \<open>t \<in> h M\<close>] \<open>contains_io_sequence M (t_target t) ios\<close>] by blast
  
    have "path M q (t#p)" 
      using \<open>path M (t_target t) p\<close> \<open>t \<in> h M\<close> \<open>t_source t = q\<close> by auto
    moreover have "p_io (t#p) = io#ios"
      using \<open>p_io p = ios\<close> \<open>t_input t = fst io\<close> \<open>t_output t = snd io\<close> by auto
    ultimately show ?case
      by auto   
  qed

  then show ?thesis by auto
qed

lemma contains_io_sequence_exhaustiveness :
  assumes "io \<in> LS M q"
  shows "contains_io_sequence M q io"
proof -
  from assms obtain p where "length p = length io" and  "path M q p" and "p_io p = io"
    by auto
  then show ?thesis
  proof (induction p io arbitrary: q rule: list_induct2)
    case Nil
    then show ?case 
      unfolding contains_io_sequence_def using contains_io_sequence'.simps(1) by auto
  next
    case (Cons t p io ios)
    then have "path M (t_target t) p" and "p_io p = ios" 
      by auto
      
    then have "contains_io_sequence M (t_target t) ios" 
      using Cons.IH by auto
    moreover have "t \<in> h M" and "t_source t = q" and "t_input t = fst io" and "t_output t = snd io"
      using Cons by auto
    ultimately have "t \<in> h M" and "t_source t = q \<and> t_input t = fst io \<and> t_output t = snd io \<and> contains_io_sequence' (h M) (t_target t) ios"
      unfolding contains_io_sequence_def using Cons by auto
      
    then show ?case 
      unfolding contains_io_sequence_def contains_io_sequence'.simps by blast
  qed
qed

  

(* TODO: only apply fail sequences? state_separation_fail_sequence_set_from_state_separator *)
(* TODO: implement faster state_separation_fail_sequence_set_from_state_separator using the above function instead of calculating L M *)

(* after each traversal sequence all state separators that r-d the reached state from some other state are added *)
(* TODO: add only relevant separators *)
fun test_suite_naive :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> Test_Case' list" where
  "test_suite_naive M m = (let qqSS = r_distinguishable_state_pairs_with_separators_naive M; 
                               MRS = maximal_repetition_sets_from_separators M;
                               Q = map 
                                    (\<lambda> qp . (snd qp, map 
                                              (\<lambda> t . (p_io t, concat (map 
                                                          (\<lambda> qqS . LS_acyclic_opt (snd qqS))
                                                          (filter 
                                                                  (\<lambda> qqS . fst (fst qqS) = target t (fst qp))
                                                                  qqSS))))
                                              (m_traversal_paths M (fst qp) MRS m))) 
                                    (d_reachable_states_with_preambles M) 

                          in Q)"

value "test_suite_naive M_ex_H 4"
value "test_suite_naive M_ex_9 4"

end