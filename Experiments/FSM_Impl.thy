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

fun fsm_impl_from_list' :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_impl" where
  "fsm_impl_from_list' q [] = \<lparr> initial = q, nodes = {q}, inputs = {}, outputs = {}, transitions = {} \<rparr>" |
  "fsm_impl_from_list' q (t#ts) = (let tsr = (remdups (t#ts))
                                   in \<lparr> initial = t_source t
                                      , nodes = set (remdups ((map t_source tsr) @ (map t_target tsr)))
                                      , inputs = set (remdups (map t_input tsr))
                                      , outputs = set (remdups (map t_output tsr))
                                      , transitions = set tsr \<rparr>)"

lemma fsm_impl_from_list_code[code] :
  "fsm_impl_from_list q ts = fsm_impl_from_list' q ts" 
  by (cases ts; auto)

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


subsubsection \<open>Filtering Transitions\<close>

fun filter_transitions :: "('a,'b,'c) fsm_impl \<Rightarrow> (('a \<times> 'b \<times> 'c \<times> 'a) \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "filter_transitions M P = \<lparr> initial = initial M
                            , nodes = nodes M
                            , inputs = inputs M
                            , outputs = outputs M
                            , transitions = Set.filter P (transitions M) \<rparr>"


subsubsection \<open>Filtering Nodes\<close>

fun filter_nodes :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "filter_nodes M P = (if P (initial M) then \<lparr> initial = initial M
                                              , nodes = Set.filter P (nodes M)
                                              , inputs = inputs M
                                              , outputs = outputs M
                                              , transitions = Set.filter (\<lambda> t . P (t_source t) \<and> P (t_target t)) (transitions M) \<rparr>
                                         else M)"
 
subsubsection \<open>Initial Singleton FSM (For Trivial Preamble)\<close>    

fun initial_singleton :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "initial_singleton M = \<lparr> initial = initial M,
                           nodes = {initial M},
                           inputs = inputs M,
                           outputs = outputs M,
                           transitions = {} \<rparr>"


subsubsection \<open>Canonical Separator\<close>

abbreviation (*shift_Inl :: "(('a \<times> 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a)) \<Rightarrow> (('a \<times> 'a + 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a + 'a))" where*)
  "shift_Inl t \<equiv> (Inl (t_source t),t_input t, t_output t, Inl (t_target t))"

definition shifted_transitions :: "(('a \<times> 'a) \<times> 'b \<times> 'c \<times> ('a \<times> 'a)) set \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> 'b \<times> 'c \<times> (('a \<times> 'a) + 'a)) set" where
  "shifted_transitions ts = image shift_Inl ts"

definition distinguishing_transitions :: "(('a \<times> 'b) \<Rightarrow> 'c set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'b set \<Rightarrow> ((('a \<times> 'a) + 'a) \<times> 'b \<times> 'c \<times> (('a \<times> 'a) + 'a)) set" where
  "distinguishing_transitions f q1 q2 nodeSet inputSet = \<Union> (Set.image (\<lambda>((q1',q2'),x) .  
                                                                (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr q1)) (f (q1',x) - f (q2',x))) 
                                                                \<union> (image (\<lambda>y . (Inl (q1',q2'),x,y,Inr q2)) (f (q2',x) - f (q1',x))))
                                                            (nodeSet \<times> inputSet))"



(* Note: parameter P is added to allow usage of different restricted versions of the product machine *)
fun canonical_separator' :: "('a,'b,'c) fsm_impl \<Rightarrow> (('a \<times> 'a),'b,'c) fsm_impl \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> (('a \<times> 'a) + 'a,'b,'c) fsm_impl" where
  "canonical_separator' M P q1 q2 = (if initial P = (q1,q2) 
  then
    (let f'  = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y)) (transitions M));
         f   = (\<lambda>qx . (case f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (transitions P);
         distinguishing_transitions_lr = distinguishing_transitions f q1 q2 (nodes P) (inputs P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr
     in 
  
      \<lparr> initial = Inl (q1,q2)
      , nodes = (image Inl (nodes P)) \<union> {Inr q1, Inr q2}
      , inputs = inputs M \<union> inputs P
      , outputs = outputs M \<union> outputs P
      , transitions = ts \<rparr>)
  else \<lparr> initial = Inl (q1,q2), nodes = {Inl (q1,q2)}, inputs = {}, outputs = {}, transitions = {}\<rparr>)"


subsection \<open>Adding Transitions\<close>

fun create_unconnected_fsm :: "'a \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'c set \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "create_unconnected_fsm q ns ins outs = (if (finite ns \<and> finite ins \<and> finite outs)
    then \<lparr> initial = q, nodes = insert q ns, inputs = ins, outputs = outs, transitions = {} \<rparr>
    else \<lparr> initial = q, nodes = {q}, inputs = {}, outputs = {}, transitions = {} \<rparr>)"

fun add_transitions :: "('a,'b,'c) fsm_impl \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) set \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "add_transitions M ts = (if (\<forall> t \<in> ts . t_source t \<in> nodes M \<and> t_input t \<in> inputs M \<and> t_output t \<in> outputs M \<and> t_target t \<in> nodes M)
    then  M\<lparr> transitions := transitions M \<union> ts\<rparr>
    else M)"




end