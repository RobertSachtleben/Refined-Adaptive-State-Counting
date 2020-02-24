theory FSM_Impl
  imports Util
begin

record ('state, 'input, 'output) fsm_impl =
  initial :: 'state
  nodes :: "'state set"
  inputs  :: "'input set"
  outputs  :: "'output set"
  transitions :: "('state \<times> 'input \<times> 'output \<times> 'state) set"






subsection \<open>Further Types\<close>

type_synonym ('a,'b,'c) transition = "('a \<times> 'b \<times> 'c \<times> 'a)"
type_synonym ('a,'b,'c) path = "('a,'b,'c) transition list"

abbreviation "t_source (a :: ('a,'b,'c) transition) \<equiv> fst a" 
abbreviation "t_input  (a :: ('a,'b,'c) transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: ('a,'b,'c) transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: ('a,'b,'c) transition) \<equiv> snd (snd (snd a))"

subsection \<open>Reading FSMs from Lists\<close>

fun fsm_impl_from_list :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_impl" where
  "fsm_impl_from_list q [] = \<lparr> initial = q, nodes = {q}, inputs = {}, outputs = {}, transitions = {} \<rparr>" |
  "fsm_impl_from_list q (t#ts) = (let ts' = set (t#ts) 
                                   in \<lparr> initial = t_source t
                                      , nodes = (image t_source ts') \<union> (image t_target ts')
                                      , inputs = image t_input ts'
                                      , outputs = image t_output ts'
                                      , transitions = ts' \<rparr>)"

subsection \<open>Changing the initial State\<close>

fun from_FSM :: "('a,'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "from_FSM M q = (if q \<in> nodes M then \<lparr> initial = q, nodes = nodes M, inputs = inputs M, outputs = outputs M, transitions = transitions M \<rparr> else M)"



end