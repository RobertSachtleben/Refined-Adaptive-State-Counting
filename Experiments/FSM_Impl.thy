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

subsection \<open>Product Construction\<close>

fun product :: "('a,'b,'c) fsm_impl \<Rightarrow> ('d,'b,'c) fsm_impl \<Rightarrow> ('a \<times> 'd,'b,'c) fsm_impl" where
  "product A B = \<lparr> initial = (initial A, initial B),
                   nodes   = (nodes A) \<times> (nodes B),
                   inputs  = inputs A \<union> inputs B,
                   outputs  = outputs A \<union> outputs B,
                   transitions = {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B} \<rparr>"

lemma product_code_naive[code] :
  "product A B = \<lparr> initial = (initial A, initial B),
                   nodes   = (nodes A) \<times> (nodes B) ,
                   inputs  = inputs A \<union> inputs B,
                   outputs  = outputs A \<union> outputs B,
                   transitions = image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))) \<rparr>"
  (is "?P1 = ?P2")
proof -
  have "(\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A))) = {(tA,tB) | tA tB . tA \<in> transitions A \<and> tB \<in> transitions B}"
    by auto
  then have "(Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))) = {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by auto
  then have "image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) (Set.filter (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . x = x' \<and> y = y') (\<Union>(image (\<lambda> tA . image (\<lambda> tB . (tA,tB)) (transitions B)) (transitions A)))) 
              = image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by auto
  moreover have "image (\<lambda>((qA,x,y,qA'), (qB,x',y',qB')) . ((qA,qB),x,y,(qA',qB'))) {((qA,x,y,qA'),(qB,x,y,qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B} =  {((qA,qB),x,y,(qA',qB')) | qA qB x y qA' qB' . (qA,x,y,qA') \<in> transitions A \<and> (qB,x,y,qB') \<in> transitions B}"
    by force
  ultimately have "transitions ?P1 = transitions ?P2" 
    unfolding product.simps by auto
  moreover have "initial ?P1 = initial ?P2" by auto
  moreover have "nodes ?P1 = nodes ?P2" by auto
  moreover have "inputs ?P1 = inputs ?P2" by auto
  moreover have "outputs ?P1 = outputs ?P2" by auto
  ultimately show ?thesis by auto
qed

 
subsubsection \<open>Initial Singleton FSM (For Trivial Preamble)\<close>    

fun initial_singleton :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "initial_singleton M = \<lparr> initial = initial M,
                           nodes = {initial M},
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = {} \<rparr>"






end