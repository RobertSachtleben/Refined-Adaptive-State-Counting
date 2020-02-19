theory FSM
  imports FSM_Impl "HOL-Library.Quotient_Type"
begin

abbreviation(input) "well_formed_fsm (M :: ('state, 'input, 'output) fsm_impl) \<equiv> (initial M \<in> nodes M
      \<and> finite (nodes M)
      \<and> finite (inputs M)
      \<and> finite (outputs M)
      \<and> finite (transitions M)
      \<and> (\<forall> t \<in> transitions M . t_source t \<in> nodes M \<and> t_input t \<in> inputs M \<and> t_target t \<in> nodes M \<and> t_output t \<in> outputs M)) " 

typedef ('state, 'input, 'output) fsm = 
  "{ M :: ('state, 'input, 'output) fsm_impl . well_formed_fsm M}"
  morphisms fsm_impl Fsm
proof -
  obtain q :: 'state where "True" by blast
  define M :: "('state, 'input, 'output) fsm_impl" where "M = \<lparr> initial = q, nodes = {q}, inputs = {}, outputs = {}, transitions = {} \<rparr>"
  then have "initial M \<in> nodes M
              \<and> finite (nodes M)
              \<and> finite (inputs M)
              \<and> finite (outputs M)
              \<and> finite (transitions M)
              \<and> (\<forall> t \<in> transitions M . t_source t \<in> nodes M \<and> t_input t \<in> inputs M \<and> t_target t \<in> nodes M \<and> t_output t \<in> outputs M)"
    by auto
  then show ?thesis by blast
qed


setup_lifting type_definition_fsm

lift_definition initial :: "('state, 'input, 'output) fsm \<Rightarrow> 'state" is FSM_Impl.initial done
lift_definition nodes :: "('state, 'input, 'output) fsm \<Rightarrow> 'state set" is FSM_Impl.nodes done
lift_definition inputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'input set" is FSM_Impl.inputs done
lift_definition outputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'output set" is FSM_Impl.outputs done
lift_definition transitions :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input \<times> 'output \<times> 'state) set" is FSM_Impl.transitions done

lift_definition fsm_from_list :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm" is FSM_Impl.fsm_impl_from_list 
proof -
  fix q  :: 'a 
  fix ts :: "('a \<times> 'b \<times> 'c \<times> 'a) list"
  show "well_formed_fsm (fsm_impl_from_list q ts)" 
    by (induction ts; auto)
qed

value "fsm_from_list 1 [(2::nat,3::nat,4::nat,5::nat)]"

subsubsection \<open>Well-Formedness Properties Revisited\<close>

lemma fsm_initial: "initial M \<in> nodes M" by (transfer; blast)
lemma fsm_nodes_finite: "finite (nodes M)" by (transfer; blast)
lemma fsm_inputs_finite: "finite (inputs M)" by (transfer; blast)
lemma fsm_outputs_finite: "finite (outputs M)" by (transfer; blast)
lemma fsm_transitions_finite: "finite (transitions M)" by (transfer; blast)
lemma fsm_transition_source: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_source t \<in> nodes M" by (transfer; blast)
lemma fsm_transition_target: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_target t \<in> nodes M" by (transfer; blast)
lemma fsm_transition_input: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_input t \<in> inputs M" by (transfer; blast)
lemma fsm_transition_output: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_output t \<in> outputs M" by (transfer; blast)


subsection \<open>Example FSMs\<close>

(* example FSM of Hieron's paper *)
definition m_ex_H :: "(integer,integer,integer) fsm" where
  "m_ex_H = fsm_from_list 0 [ (1,0,0,2),
                              (1,0,1,4),
                              (1,1,1,4),
                              (2,0,0,2),
                              (2,1,1,4),
                              (3,0,1,4),
                              (3,1,0,1),
                              (3,1,1,3),
                              (4,0,0,3),
                              (4,1,0,1)]"

subsection \<open>Transition Function h\<close>

fun h :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" where
  "h M (q,x) = { (y,q') . (q,x,y,q') \<in> transitions M }"


lemma h_code[code] : "h M (q,x) = (let m = set_as_map (transitions M) in (case m (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding set_as_map_def by auto


value "h m_ex_H (1,0)"
value "h m_ex_H (1,1)"
value "h m_ex_H (1,2)"









lemma fsm_eq :
  fixes M1 :: "('a,'b,'c) fsm"
  fixes M2 :: "('a,'b,'c) fsm"
  shows "M1 = M2 \<longleftrightarrow> initial M1 = initial M2 \<and> nodes M1 = nodes M2 \<and> inputs M1 = inputs M2 \<and> outputs M1 = outputs M2 \<and> transitions M1 = transitions M2"
  apply transfer by auto


(*declare [[code drop: h]] *)
(*declare [[code drop: set_as_map]]*)

end