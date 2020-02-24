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

lemma fsm_initial[intro]: "initial M \<in> nodes M" by (transfer; blast)
lemma fsm_nodes_finite: "finite (nodes M)" by (transfer; blast)
lemma fsm_inputs_finite: "finite (inputs M)" by (transfer; blast)
lemma fsm_outputs_finite: "finite (outputs M)" by (transfer; blast)
lemma fsm_transitions_finite: "finite (transitions M)" by (transfer; blast)
lemma fsm_transition_source[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_source t \<in> nodes M" by (transfer; blast)
lemma fsm_transition_target[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_target t \<in> nodes M" by (transfer; blast)
lemma fsm_transition_input[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_input t \<in> inputs M" by (transfer; blast)
lemma fsm_transition_output[intro]: "\<And> t . t \<in> (transitions M) \<Longrightarrow> t_output t \<in> outputs M" by (transfer; blast)


instantiation fsm :: (type,type,type) equal
begin                                  
definition equal_fsm :: "('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> bool" where
  "equal_fsm x y = (initial x = initial y \<and> nodes x = nodes y \<and> inputs x = inputs y \<and> outputs x = outputs y \<and> transitions x = transitions y)"

instance
  apply (intro_classes)
  unfolding equal_fsm_def 
  apply transfer by auto
end 

(*
lemma fsm_eq :
  fixes x :: "('a,'b,'c) fsm"
  and   y :: "('a,'b,'c) fsm"
shows "HOL.equal x y = (x = y)" using equal_class.equal by (metis (full_types))

lemma fsm_eq[iff] :
  fixes M  :: "('a,'b,'c) fsm"
  fixes M' :: "('a,'b,'c) fsm"
  shows "M = M' \<longleftrightarrow> (initial M = initial M' \<and> nodes M = nodes M' \<and> inputs M = inputs M' \<and> outputs M = outputs M' \<and> transitions M = transitions M')"
  apply transfer by force
*)

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

(* TODO: main idea for later common subexpression elimination: calculate all kinds of h functions once
         and pass them through *)

fun h :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" where
  "h M (q,x) = { (y,q') . (q,x,y,q') \<in> transitions M }"


lemma h_code[code] : "h M (q,x) = (let m = set_as_map (image (\<lambda>(q,x,y,q') . ((q,x),y,q')) (transitions M)) in (case m (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding set_as_map_def by force




fun defined_inputs' :: "(('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "defined_inputs' hM iM q = {x \<in> iM . hM (q,x) \<noteq> {}}"

fun defined_inputs :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "defined_inputs M q = defined_inputs' (h M) (inputs M) q"

value "defined_inputs m_ex_H 1"

lemma defined_inputs_set : "defined_inputs M q = {x \<in> inputs M . h M (q,x) \<noteq> {} }"
  by auto

(* TODO: is defined_inputs' necessary? *)
fun transitions_from' :: "(('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) transition set" where
  "transitions_from' hM iM q = \<Union>(image (\<lambda>x . image (\<lambda>(y,q') . (q,x,y,q')) (hM (q,x))) (defined_inputs' hM iM q))"

fun transitions_from :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) transition set" where
  "transitions_from M q = transitions_from' (h M) (inputs M) q"

value "transitions_from m_ex_H 1"

lemma transitions_from_set : 
  assumes "q \<in> nodes M" 
  shows "transitions_from M q = {t \<in> transitions M . t_source t = q}"
proof -
  have "\<And> t . t \<in> transitions_from M q \<Longrightarrow> t \<in> transitions M \<and> t_source t = q" by auto
  moreover have "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = q \<Longrightarrow> t \<in> transitions_from M q" 
  proof -
    fix t assume "t \<in> transitions M" and "t_source t = q"
    then have "(t_output t, t_target t) \<in> h M (q,t_input t)" and "t_input t \<in> inputs M" by auto
    then have "t_input t \<in> defined_inputs' (h M) (inputs M) q" 
      unfolding defined_inputs'.simps \<open>t_source t = q\<close> by blast

    have "(q, t_input t, t_output t, t_target t) \<in> transitions M"
      using \<open>t_source t = q\<close> \<open>t \<in> transitions M\<close> by auto
    then have "(q, t_input t, t_output t, t_target t) \<in> (\<lambda>(y, q'). (q, t_input t, y, q')) ` h M (q, t_input t)"
      using \<open>(t_output t, t_target t) \<in> h M (q,t_input t)\<close>
      unfolding h.simps
      by (metis (no_types, lifting) image_iff prod.case_eq_if surjective_pairing)
    then have "t \<in> (\<lambda>(y, q'). (q, t_input t, y, q')) ` h M (q, t_input t)"
      using \<open>t_source t = q\<close> by (metis prod.collapse) 
    then show "t \<in> transitions_from M q" 
       
      unfolding transitions_from.simps transitions_from'.simps 
      using \<open>t_input t \<in> defined_inputs' (h M) (inputs M) q\<close>
      by blast 
  qed
  ultimately show ?thesis by blast
qed


fun h_from :: "('state, 'input, 'output) fsm \<Rightarrow> 'state \<Rightarrow> ('input \<times> 'output \<times> 'state) set" where
  "h_from M q = { (x,y,q') . (q,x,y,q') \<in> transitions M }"


lemma h_from[code] : "h_from M q = (let m = set_as_map (transitions M) in (case m q of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding set_as_map_def by force


subsection \<open>Size\<close>

instantiation fsm  :: (type,type,type) size 
begin

definition size where [simp, code]: "size (m::('a, 'b, 'c) fsm) = card (nodes m)"

instance ..

end



subsection \<open>Paths\<close>

inductive path :: "('state, 'input, 'output) fsm \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'input \<times> 'output \<times> 'state) list \<Rightarrow> bool" where
  nil[intro!] : "q \<in> nodes M \<Longrightarrow> path M q []" |
  cons[intro!] : "t \<in> transitions M \<Longrightarrow> path M (t_target t) ts \<Longrightarrow> path M (t_source t) (t#ts)"

inductive_cases path_nil_elim[elim!]: "path M q []"
inductive_cases path_cons_elim[elim!]: "path M q (t#ts)"

(*
fun target :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state" where
  "target q [] = q" |
  "target q p  = t_target (last p)"
*)
fun visited_nodes :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state list" where
  "visited_nodes q p = (q # map t_target p)"

fun target :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state" where
  "target q p = last (visited_nodes q p)"

lemma[simp] : "target q [] = q" by auto
lemma[simp] : "target q (p@[t]) = t_target t" by auto


lemma path_begin_node :
  assumes "path M q p"
  shows   "q \<in> nodes M" 
  using assms by (cases; auto) 

lemma path_append[intro!] :
  assumes "path M q p1"
      and "path M (target q p1) p2"
  shows "path M q (p1@p2)"
  using assms by (induct p1 arbitrary: p2; auto) 

lemma path_target_is_node :
  assumes "path M q p"
  shows   "target q p \<in> nodes M"
using assms by (induct p; auto)

lemma path_suffix :
  assumes "path M q (p1@p2)"
  shows "path M (target q p1) p2"
using assms by (induction p1 arbitrary: q; auto)

lemma path_prefix :
  assumes "path M q (p1@p2)"
  shows "path M q p1"
using assms by (induction p1 arbitrary: q; auto; (metis path_begin_node))


lemma path_append_elim[elim!] :
  assumes "path M q (p1@p2)"
  obtains "path M q p1"
      and "path M (target q p1) p2"
  by (meson assms path_prefix path_suffix)

lemma path_append_target:
  "target q (p1@p2) = target (target q p1) p2" 
  by (induction p1) (simp+)

lemma path_append_target_hd :
  assumes "length p > 0"
  shows "target q p = target (t_target (hd p)) (tl p)"
using assms by (induction p) (simp+)


lemma path_transitions :
  assumes "path M q p"
  shows "set p \<subseteq> transitions M"
  using assms by (induct p arbitrary: q; fastforce)

(* TODO: add simp ? *)
lemma path_append_transition[intro!] :
  assumes "path M q p"
  and     "t \<in> transitions M"
  and     "t_source t = target q p" 
shows "path M q (p@[t])"
  by (metis assms(1) assms(2) assms(3) cons fsm_transition_target nil path_append)


lemma path_append_transition_elim[elim!] :
  assumes "path M q (p@[t])"
shows "path M q p"
and   "t \<in> transitions M"
and   "t_source t = target q p" 
  using assms by auto

lemma path_prepend_t : "path M q' p \<Longrightarrow> (q,x,y,q') \<in> transitions M \<Longrightarrow> path M q ((q,x,y,q')#p)" 
  by (metis (mono_tags, lifting) fst_conv path.intros(2) prod.sel(2)) 

lemma path_target_append : "target q1 p1 = q2 \<Longrightarrow> target q2 p2 = q3 \<Longrightarrow> target q1 (p1@p2) = q3" by auto

lemma single_transition_path : "t \<in> transitions M \<Longrightarrow> path M (t_source t) [t]" by auto

lemma path_source_target_index :
  assumes "Suc i < length p"
  and     "path M q p"
shows "t_target (p ! i) = t_source (p ! (Suc i))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t ps)
  then have "path M q ps" and "t_source t = target q ps" and "t \<in> transitions M" by auto
  
  show ?case proof (cases "Suc i < length ps")
    case True
    then have "t_target (ps ! i) = t_source (ps ! Suc i)" 
      using snoc.IH \<open>path M q ps\<close> by auto
    then show ?thesis
      by (simp add: Suc_lessD True nth_append) 
  next
    case False
    then have "Suc i = length ps"
      using snoc.prems(1) by auto
    then have "(ps @ [t]) ! Suc i = t"
      by auto

    show ?thesis proof (cases "ps = []")
      case True
      then show ?thesis using \<open>Suc i = length ps\<close> by auto
    next
      case False
      then have "target q ps = t_target (last ps)"
        unfolding target.simps visited_nodes.simps
        by (simp add: last_map) 
      then have "target q ps = t_target (ps ! i)"
        using \<open>Suc i = length ps\<close>
        by (metis False diff_Suc_1 last_conv_nth) 
      then show ?thesis 
        using \<open>t_source t = target q ps\<close>
        by (metis \<open>(ps @ [t]) ! Suc i = t\<close> \<open>Suc i = length ps\<close> lessI nth_append) 
    qed
  qed   
qed

subsubsection \<open>Paths of fixed length\<close>

fun paths_of_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> (('a \<times>'b) \<Rightarrow> ('c\<times>'a) set) \<Rightarrow> 'b set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_of_length' prev q hM iM 0 = {prev}" |
  "paths_of_length' prev q hM iM (Suc k) = 
    (let hF = transitions_from' hM iM q
      in \<Union> (image (\<lambda> t . paths_of_length' (prev@[t]) (t_target t) hM iM k) hF))"

fun paths_of_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_of_length M q k = paths_of_length' [] q (h M) (inputs M) k"

value "paths_of_length m_ex_H 1 5"

(* TODO: correctness / completeness properties *)

subsubsection \<open>Paths up to fixed length\<close>

fun paths_up_to_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> (('a \<times>'b) \<Rightarrow> (('c\<times>'a) set)) \<Rightarrow> 'b set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_up_to_length' prev q hM iM 0 = {prev}" |
  "paths_up_to_length' prev q hM iM (Suc k) = 
    (let hF = transitions_from' hM iM q
      in insert prev (\<Union> (image (\<lambda> t . paths_up_to_length' (prev@[t]) (t_target t) hM iM k) hF)))"

fun paths_up_to_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "paths_up_to_length M q k = paths_up_to_length' [] q (h M) (inputs M) k"

value "paths_up_to_length m_ex_H 1 0"
value "paths_up_to_length m_ex_H 1 1"
value "paths_up_to_length m_ex_H 1 2"

(* TODO: correctness / completeness properties *)

subsubsection \<open>Calculating Acyclic Paths\<close>

abbreviation "member_option x ms \<equiv> (case ms of None \<Rightarrow> False | Some xs \<Rightarrow> x \<in> xs)"
notation member_option ("(_\<in>\<^sub>o_)" [1000] 1000)

abbreviation(input) "lookup_with_default f d \<equiv> (\<lambda> x . case f x of None \<Rightarrow> d | Some xs \<Rightarrow> xs)"
abbreviation(input) "m2f f \<equiv> lookup_with_default f {}" (* map to (set-valued) fun *)


fun acyclic_paths_up_to_length' :: "('a,'b,'c) path \<Rightarrow> 'a \<Rightarrow> ('a  \<Rightarrow> (('b\<times>'c\<times>'a) set)) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "acyclic_paths_up_to_length' prev q hF visitedNodes 0 = {prev}" |
  "acyclic_paths_up_to_length' prev q hF visitedNodes (Suc k) = 
    (let tF = Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedNodes) (hF q)
      in (insert prev (\<Union> (image (\<lambda> (x,y,q') . acyclic_paths_up_to_length' (prev@[(q,x,y,q')]) q' hF (insert q' visitedNodes) k) tF))))"


fun p_source :: "'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> 'a"
  where "p_source q p = hd (visited_nodes q p)"

lemma acyclic_paths_up_to_length'_prev : 
  "p' \<in> acyclic_paths_up_to_length' (prev@prev') q hF visitedNodes k \<Longrightarrow> \<exists> p'' . p' = prev@p''" 
  by (induction k arbitrary: p' q visitedNodes prev'; auto)

lemma acyclic_paths_up_to_length'_set :
  assumes "path M (p_source q prev) prev"
  and     "\<And> q' . hF q' = {(x,y,q'') | x y q'' . (q',x,y,q'') \<in> transitions M}"
  and     "distinct (visited_nodes (p_source q prev) prev)"
  and     "visitedNodes = set (visited_nodes (p_source q prev) prev)"
shows "acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes k = { prev@p | p . path M (p_source q prev) (prev@p) \<and> length p \<le> k \<and> distinct (visited_nodes (p_source q prev) (prev@p)) }"
using assms proof (induction k arbitrary: q hF prev visitedNodes)
  case 0
  then show ?case by auto
next
  case (Suc k)

  let ?tgt = "(target (p_source q prev) prev)"

  have "\<And> p . (prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k) \<Longrightarrow> path M (p_source q prev) (prev@p) \<and> length p \<le> Suc k \<and> distinct (visited_nodes (p_source q prev) (prev@p))"
  proof -
    fix p assume "(prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k)"
    then consider (a) "(prev@p) = prev" |
                  (b) "(prev@p) \<in> (\<Union> (image (\<lambda> (x,y,q') . acyclic_paths_up_to_length' (prev@[(?tgt,x,y,q')]) q' hF (insert q' visitedNodes) k) (Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedNodes) (hF (target (p_source q prev) prev)))))"
      by auto
    then show "path M (p_source q prev) (prev@p) \<and> length p \<le> Suc k \<and> distinct (visited_nodes (p_source q prev) (prev@p))"
    proof (cases)
      case a
      then show ?thesis using Suc.prems(1,3) by auto
    next
      case b
      then obtain x y q' where *: "(x,y,q') \<in> Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedNodes) (hF ?tgt)"
                         and   **:"(prev@p) \<in> acyclic_paths_up_to_length' (prev@[(?tgt,x,y,q')]) q' hF (insert q' visitedNodes) k"
        by auto

      let ?t = "(?tgt,x,y,q')"

      from * have "?t \<in> transitions M" and "q' \<notin> visitedNodes"
        using Suc.prems(2)[of ?tgt] by simp+ 
      moreover have "t_source ?t = target (p_source q prev) prev"
        by simp
      moreover have "p_source (p_source q prev) (prev@[?t]) = p_source q prev"
        by auto
      ultimately have p1: "path M (p_source (p_source q prev) (prev@[?t])) (prev@[?t])" using Suc.prems(1)
        by (simp add: path_append_transition) 
      
      
      have "q' \<notin> set (visited_nodes (p_source q prev) prev)"
        using \<open>q' \<notin> visitedNodes\<close> Suc.prems(4) by auto
      then have p2: "distinct (visited_nodes (p_source (p_source q prev) (prev@[?t])) (prev@[?t]))"
        using Suc.prems(3) by auto

      have p3: "(insert q' visitedNodes) = set (visited_nodes (p_source (p_source q prev) (prev@[?t])) (prev@[?t]))"
        using Suc.prems(4) by auto

      have ***: "(target (p_source (p_source q prev) (prev @ [(target (p_source q prev) prev, x, y, q')])) (prev @ [(target (p_source q prev) prev, x, y, q')])) = q'"
        by auto

      show ?thesis
        using Suc.IH[OF p1 Suc.prems(2) p2 p3] ** 
        unfolding *** 
        unfolding \<open>p_source (p_source q prev) (prev@[?t]) = p_source q prev\<close>
      proof -
        assume "acyclic_paths_up_to_length' (prev @ [(target (p_source q prev) prev, x, y, q')]) q' hF (insert q' visitedNodes) k = {(prev @ [(target (p_source q prev) prev, x, y, q')]) @ p |p. path M (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ p) \<and> length p \<le> k \<and> distinct (visited_nodes (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ p))}"
        then have "\<exists>ps. prev @ p = (prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps \<and> path M (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps) \<and> length ps \<le> k \<and> distinct (visited_nodes (p_source q prev) ((prev @ [(target (p_source q prev) prev, x, y, q')]) @ ps))"
          using \<open>prev @ p \<in> acyclic_paths_up_to_length' (prev @ [(target (p_source q prev) prev, x, y, q')]) q' hF (insert q' visitedNodes) k\<close> by blast
        then show ?thesis
          by (metis (no_types) Suc_le_mono append.assoc append.right_neutral append_Cons length_Cons same_append_eq)
      qed 
    qed
  qed
  moreover have "\<And> p' . p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k) \<Longrightarrow> \<exists> p'' . p' = prev@p''"
    using acyclic_paths_up_to_length'_prev[of _ prev "[]" "target (p_source q prev) prev" hF visitedNodes "Suc k"] by force
  ultimately have fwd: "\<And> p' . p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k) \<Longrightarrow> p' \<in> { prev@p | p . path M (p_source q prev) (prev@p) \<and> length p \<le> Suc k \<and> distinct (visited_nodes (p_source q prev) (prev@p)) }"
    by blast

  have "\<And> p . path M (p_source q prev) (prev@p) \<Longrightarrow> length p \<le> Suc k \<Longrightarrow> distinct (visited_nodes (p_source q prev) (prev@p)) \<Longrightarrow> (prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k)"
  proof -
    fix p assume "path M (p_source q prev) (prev@p)"
          and    "length p \<le> Suc k"
          and    "distinct (visited_nodes (p_source q prev) (prev@p))"

    show "(prev@p) \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k)"
    proof (cases p)
      case Nil
      then show ?thesis by auto
    next
      case (Cons t p')

      then have "t_source t = target (p_source q (prev)) (prev)" and "t \<in> transitions M"
        using \<open>path M (p_source q prev) (prev@p)\<close> by auto
      
      have "path M (p_source q (prev@[t])) ((prev@[t])@p')"
      and  "path M (p_source q (prev@[t])) ((prev@[t]))"
        using Cons \<open>path M (p_source q prev) (prev@p)\<close> by auto
      have "length p' \<le> k"
        using Cons \<open>length p \<le> Suc k\<close> by auto
      have "distinct (visited_nodes (p_source q (prev@[t])) ((prev@[t])@p'))"
      and  "distinct (visited_nodes (p_source q (prev@[t])) ((prev@[t])))" 
        using Cons \<open>distinct (visited_nodes (p_source q prev) (prev@p))\<close> by auto
      then have "t_target t \<notin> visitedNodes"
        using Suc.prems(4) by auto

      let ?vN = "insert (t_target t) visitedNodes"
      have "?vN = set (visited_nodes (p_source q (prev @ [t])) (prev @ [t]))"
        using Suc.prems(4) by auto

      have "prev@p = prev@([t]@p')"
        using Cons by auto

      have "(prev@[t])@p' \<in> acyclic_paths_up_to_length' (prev @ [t]) (target (p_source q (prev @ [t])) (prev @ [t])) hF (insert (t_target t) visitedNodes) k" 
        using Suc.IH[of q "prev@[t]", OF \<open>path M (p_source q (prev@[t])) ((prev@[t]))\<close> Suc.prems(2)
                                         \<open>distinct (visited_nodes (p_source q (prev@[t])) ((prev@[t])))\<close> 
                                         \<open>?vN = set (visited_nodes (p_source q (prev @ [t])) (prev @ [t]))\<close> ]
        using \<open>path M (p_source q (prev@[t])) ((prev@[t])@p')\<close>
              \<open>length p' \<le> k\<close>
              \<open>distinct (visited_nodes (p_source q (prev@[t])) ((prev@[t])@p'))\<close> 
        by force

      then have "(prev@[t])@p' \<in> acyclic_paths_up_to_length' (prev@[t]) (t_target t) hF ?vN k"
        by auto
      moreover have "(t_input t,t_output t, t_target t) \<in> Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedNodes) (hF (t_source t))"
        using Suc.prems(2)[of "t_source t"] \<open>t \<in> transitions M\<close> \<open>t_target t \<notin> visitedNodes\<close>
      proof -
        have "\<exists>b c a. snd t = (b, c, a) \<and> (t_source t, b, c, a) \<in> FSM.transitions M"
          by (metis (no_types) \<open>t \<in> FSM.transitions M\<close> prod.collapse)
        then show ?thesis
          using \<open>hF (t_source t) = {(x, y, q'') |x y q''. (t_source t, x, y, q'') \<in> FSM.transitions M}\<close> \<open>t_target t \<notin> visitedNodes\<close> by fastforce
      qed 
      ultimately have "\<exists> (x,y,q') \<in> (Set.filter (\<lambda> (x,y,q') . q' \<notin> visitedNodes) (hF (target (p_source q prev) prev))) .
                        (prev@[t])@p' \<in> (acyclic_paths_up_to_length' (prev@[((target (p_source q prev) prev),x,y,q')]) q' hF (insert q' visitedNodes) k)"
        unfolding \<open>t_source t = target (p_source q (prev)) (prev)\<close>
        by (metis (no_types, lifting) \<open>t_source t = target (p_source q prev) prev\<close> case_prodI prod.collapse) 
       
      then show ?thesis unfolding \<open>prev@p = prev@[t]@p'\<close> 
        unfolding acyclic_paths_up_to_length'.simps Let_def by force
    qed
  qed
  then have rev: "\<And> p' . p' \<in> {prev@p | p . path M (p_source q prev) (prev@p) \<and> length p \<le> Suc k \<and> distinct (visited_nodes (p_source q prev) (prev@p))} \<Longrightarrow> p' \<in> acyclic_paths_up_to_length' prev (target (p_source q prev) prev) hF visitedNodes (Suc k)"
    by blast
  
  show ?case
    using fwd rev by blast
qed 


fun acyclic_paths_up_to_length :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) path set" where
  "acyclic_paths_up_to_length M q k = { p . path M q p \<and> length p \<le> k \<and> distinct (visited_nodes q p) }"

lemma acyclic_paths_up_to_length_code[code] :
  "acyclic_paths_up_to_length M q k = (if q \<in> nodes M 
      then acyclic_paths_up_to_length' [] q (m2f (set_as_map (transitions M))) {q} k
      else {})"
proof (cases "q \<in> nodes M")
  case False
  then have "acyclic_paths_up_to_length M q k = {}" 
    using path_begin_node by fastforce
  then show ?thesis using False by auto
next
  case True
  then have *: "path M (p_source q []) []" by auto
  have **: "(\<And>q'. (m2f (set_as_map (transitions M))) q' = {(x, y, q'') |x y q''. (q', x, y, q'') \<in> FSM.transitions M})"
    unfolding set_as_map_def by auto 
  have ***: "distinct (visited_nodes (p_source q []) [])"
    by auto
  have ****: "{q} = set (visited_nodes (p_source q []) [])"
    by auto
  
  show ?thesis
    using acyclic_paths_up_to_length'_set[OF * ** *** ****, of k ] 
    using True by auto
qed
  

value "acyclic_paths_up_to_length m_ex_H 1 0"
value "acyclic_paths_up_to_length m_ex_H 1 1"
value "acyclic_paths_up_to_length m_ex_H 1 2"
value "acyclic_paths_up_to_length m_ex_H 1 3"
value "acyclic_paths_up_to_length m_ex_H 1 4"
value "acyclic_paths_up_to_length m_ex_H 1 5"


subsection \<open>Acyclic Paths\<close>

lemma visited_nodes_prefix :
  assumes "q' \<in> set (visited_nodes q p)"
  shows   "\<exists> p1 p2 . p = p1@p2 \<and> target q p1 = q'"
using assms proof (induction p arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case 
  proof (cases "q' \<in> set (visited_nodes (t_target a) p)")
    case True
    then obtain p1 p2 where "p = p1 @ p2 \<and> target (t_target a) p1 = q'"
      using Cons.IH by blast
    then have "(a#p) = (a#p1)@p2 \<and> target q (a#p1) = q'"
      by auto
    then show ?thesis by blast
  next
    case False
    then have "q' = q" 
      using Cons.prems by auto     
    then show ?thesis
      by auto 
  qed
qed 


lemma cyclic_path_loop :
  assumes "path M q p"
  and     "\<not> distinct (visited_nodes q p)"
shows "\<exists> p1 p2 p3 . p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target q p1 = target q (p1@p2)"
using assms proof (induction p arbitrary: q)
  case (nil M q)
  then show ?case by auto
next
  case (cons t M ts)
  then show ?case 
  proof (cases "distinct (visited_nodes (t_target t) ts)")
    case True
    then have "q \<in> set (visited_nodes (t_target t) ts)"
      using cons.prems by simp 
    then obtain p2 p3 where "ts = p2@p3" and "target (t_target t) p2 = q" 
      using visited_nodes_prefix[of q "t_target t" ts] by blast
    then have "(t#ts) = []@(t#p2)@p3 \<and> (t#p2) \<noteq> [] \<and> target q [] = target q ([]@(t#p2))"
      using cons.hyps by auto
    then show ?thesis by blast
  next
    case False
    then obtain p1 p2 p3 where "ts = p1@p2@p3" and "p2 \<noteq> []" and "target (t_target t) p1 = target (t_target t) (p1@p2)" 
      using cons.IH by blast
    then have "t#ts = (t#p1)@p2@p3 \<and> p2 \<noteq> [] \<and> target q (t#p1) = target q ((t#p1)@p2)"
      by simp
    then show ?thesis by blast    
  qed
qed


lemma cyclic_path_pumping :
  assumes "path M (initial M) p" 
      and "\<not> distinct (visited_nodes (initial M) p)"
  shows "\<exists> p . path M (initial M) p \<and> length p \<ge> n"
proof -
  from assms obtain p1 p2 p3 where "p = p1 @ p2 @ p3" and "p2 \<noteq> []" and "target (initial M) p1 = target (initial M) (p1 @ p2)"
    using cyclic_path_loop[of M "initial M" p] by blast
  then have "path M (target (initial M) p1) p3"
    using path_suffix[of M "initial M" "p1@p2" p3] \<open>path M (initial M) p\<close> by auto
  
  have "path M (initial M) p1"
    using path_prefix[of M "initial M" p1 "p2@p3"] \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> by auto
  have "path M (initial M) ((p1@p2)@p3)"
    using \<open>path M (initial M) p\<close> \<open>p = p1 @ p2 @ p3\<close> by auto
  have "path M (target (initial M) p1) p2" 
    using path_suffix[of M "initial M" p1 p2, OF path_prefix[of M "initial M" "p1@p2" p3, OF \<open>path M (initial M) ((p1@p2)@p3)\<close>]] by assumption
  have "target (target (initial M) p1) p2 = (target (initial M) p1)"
    using path_append_target \<open>target (initial M) p1 = target (initial M) (p1 @ p2)\<close> by auto
  
  have "path M (initial M) (p1 @ (concat (replicate n p2)) @ p3)"  
  proof (induction n)
    case 0 
    then show ?case using path_append[OF \<open>path M (initial M) p1\<close> \<open>path M (target (initial M) p1) p3\<close>]  by auto
  next
    case (Suc n)
    then show ?case
      using \<open>path M (target (initial M) p1) p2\<close> \<open>target (target (initial M) p1) p2 = target (initial M) p1\<close> by auto 
  qed
  moreover have "length (p1 @ (concat (replicate n p2)) @ p3) \<ge> n"
  proof -
    have "length (concat (replicate n p2)) = n * (length p2)" 
      using concat_replicate_length by metis
    moreover have "length p2 > 0"
      using \<open>p2 \<noteq> []\<close> by auto
    ultimately have "length (concat (replicate n p2)) \<ge> n"
      by (simp add: Suc_leI)
    then show ?thesis by auto
  qed
  ultimately show "\<exists> p . path M (initial M) p \<and> length p \<ge> n" by blast
qed


lemma cyclic_path_shortening : 
  assumes "path M q p"
  and     "\<not> distinct (visited_nodes q p)"
shows "\<exists> p' . path M q p' \<and> target q p' = target q p \<and> length p' < length p"
proof -
  obtain p1 p2 p3 where *: "p = p1@p2@p3 \<and> p2 \<noteq> [] \<and> target q p1 = target q (p1@p2)" 
    using cyclic_path_loop[OF assms] by blast
  then have "path M q (p1@p3)"
    using assms(1) by force
  moreover have "target q (p1@p3) = target q p"
    by (metis (full_types) * path_append_target)
  moreover have "length (p1@p3) < length p"
    using * by auto
  ultimately show ?thesis by blast
qed



lemma paths_finite : "finite { p . path M q p \<and> length p \<le> k }"
proof -
  have "{ p . path M q p \<and> length p \<le> k } \<subseteq> {xs . set xs \<subseteq> transitions M \<and> length xs \<le> k}"
    by (metis (no_types, lifting) Collect_mono path_transitions)     
  then show "finite { p . path M q p \<and> length p \<le> k }"
    using finite_lists_length_le[OF fsm_transitions_finite[of M], of k]
    by (metis (mono_tags) finite_subset) 
qed


lemma acyclic_path_from_cyclic_path :
  assumes "path M q p"
  and     "\<not> distinct (visited_nodes q p)"
obtains p' where "path M q p'" and "target q p = target q p'" and "distinct (visited_nodes q p')"
proof -
  
  let ?paths = "{p' . (path M q p' \<and> target q p' = target q p \<and> length p' \<le> length p)}"
  let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
  have "?paths \<noteq> empty" 
    using assms(1) by auto
  moreover have "finite ?paths" 
    using paths_finite[of M q "length p"]
    by (metis (no_types, lifting) Collect_mono rev_finite_subset)
  ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" 
    by (meson arg_min_nat_lemma equals0I)
  then have "path M q ?minPath" and "target q ?minPath = target q p" 
    by auto
  
  moreover have "distinct (visited_nodes q ?minPath)"
  proof (rule ccontr)
    assume "\<not> distinct (visited_nodes q ?minPath)"
    have "\<exists> p' . path M q p' \<and> target q p' = target q p \<and> length p' < length ?minPath" 
      using cyclic_path_shortening[OF \<open>path M q ?minPath\<close> \<open>\<not> distinct (visited_nodes q ?minPath)\<close>] minPath_def
            \<open>target q ?minPath= target q p\<close> by auto
    then show "False" 
      using minPath_def using arg_min_nat_le dual_order.strict_trans1 by auto 
  qed

  ultimately show ?thesis
    by (simp add: that)
qed    


lemma acyclic_path_length_limit :
  assumes "path M q p"
  and     "distinct (visited_nodes q p)"
shows "length p < size M"
proof (rule ccontr)
  assume *: "\<not> length p < size M"
  then have "length p \<ge> card (nodes M)"
    using size_def by auto
  then have "length (visited_nodes q p) > card (nodes M)"
    by auto
  moreover have "set (visited_nodes q p) \<subseteq> nodes M"
    by (metis assms(1) path_prefix path_target_is_node subsetI visited_nodes_prefix)
  ultimately have "\<not> distinct (visited_nodes q p)"
    using distinct_card[OF assms(2)] 
    using List.finite_set[of "visited_nodes q p"]
    by (metis card_mono fsm_nodes_finite leD) 
  then show "False" using assms(2) by blast
qed

lemma visited_nodes_are_nodes :
  assumes "path M q1 p"
  shows "set (visited_nodes q1 p) \<subseteq> nodes M" 
  by (metis assms path_prefix path_target_is_node subsetI visited_nodes_prefix) 
  
lemma transition_subset_path : 
  assumes "transitions A \<subseteq> transitions B"
  and "path A q p"
  and "q \<in> nodes B"
shows "path B q p"
using assms(2) proof (induction p rule: rev_induct)
  case Nil
  show ?case using assms(3) by auto
next
  case (snoc t p)
  then show ?case using assms(1) path_suffix
    by fastforce   
qed



subsection \<open>Reachable Nodes\<close>

definition reachable :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "reachable M q = (\<exists> p . path M (initial M) p \<and> target (initial M) p = q)"

definition reachable_nodes :: "('a,'b,'c) fsm \<Rightarrow> 'a set" where
  "reachable_nodes M  = {q . \<exists> p . path M (initial M) p \<and> target (initial M) p = q }"

lemma acyclic_paths_set :
  "acyclic_paths_up_to_length M q (size M - 1) = {p . path M q p \<and> distinct (visited_nodes q p)}"
  unfolding acyclic_paths_up_to_length.simps using acyclic_path_length_limit[of M q]
  by (metis (no_types, lifting) One_nat_def Suc_pred cyclic_path_shortening leD list.size(3) not_less_eq_eq not_less_zero path.intros(1) path_begin_node) 


(* inefficient calculation, as a node may be target of a large number of (acyclic) paths *)
lemma reachable_nodes_code[code] : 
  "reachable_nodes M = image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
proof -
  have "\<And> q' . q' \<in> reachable_nodes M \<Longrightarrow> q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
  proof -
    fix q' assume "q' \<in> reachable_nodes M"
    then obtain p where "path M (initial M) p" and "target (initial M) p = q'"
      unfolding reachable_nodes_def by blast
    
    obtain p' where "path M (initial M) p'" and "target (initial M) p' = q'" and "distinct (visited_nodes (initial M) p')"
    proof (cases "distinct (visited_nodes (initial M) p)")
      case True
      then show ?thesis using \<open>path M (initial M) p\<close> \<open>target (initial M) p = q'\<close> that by auto
    next
      case False
      then show ?thesis 
        using acyclic_path_from_cyclic_path[OF \<open>path M (initial M) p\<close>] 
        unfolding \<open>target (initial M) p = q'\<close> using that by blast
    qed
    then show "q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_set by force
  qed
  moreover have "\<And> q' . q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1)) \<Longrightarrow> q' \<in> reachable_nodes M"
    unfolding reachable_nodes_def acyclic_paths_set by blast
  ultimately show ?thesis by blast
qed



subsection \<open>Language\<close>

abbreviation "p_io (p :: ('state,'input,'output) path) \<equiv> map (\<lambda> t . (t_input t, t_output t)) p"

fun language_state_for_input :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> 'input list \<Rightarrow> ('input \<times> 'output) list set" where
  "language_state_for_input M q xs = {p_io p | p . path M q p \<and> map fst (p_io p) = xs}"

fun LS\<^sub>i\<^sub>n :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> 'input list set \<Rightarrow> ('input \<times> 'output) list set" where
  "LS\<^sub>i\<^sub>n M q xss = {p_io p | p . path M q p \<and> map fst (p_io p) \<in> xss}"

abbreviation(input) "L\<^sub>i\<^sub>n M \<equiv> LS\<^sub>i\<^sub>n M (initial M)"

lemma language_state_for_input_inputs : 
  assumes "io \<in> language_state_for_input M q xs"
  shows "map fst io = xs" 
  using assms by auto

lemma language_state_for_inputs_inputs : 
  assumes "io \<in> LS\<^sub>i\<^sub>n M q xss"
  shows "map fst io \<in> xss" using assms by auto 


fun LS :: "('state,'input,'output) fsm \<Rightarrow> 'state \<Rightarrow> ('input \<times> 'output) list set" where
  "LS M q = { p_io p | p . path M q p }"

abbreviation "L M \<equiv> LS M (initial M)"

lemma language_state_containment :
  assumes "path M q p"
  and     "p_io p = io"
shows "io \<in> LS M q"
  using assms by auto

lemma language_prefix : 
  assumes "io1@io2 \<in> LS M q"
  shows "io1 \<in> LS M q"
proof -
  obtain p where "path M q p" and "p_io p = io1@io2" 
    using assms by auto
  let ?tp = "take (length io1) p"
  have "path M q ?tp"
    by (metis (no_types) \<open>path M q p\<close> append_take_drop_id path_prefix) 
  moreover have "p_io ?tp = io1"
    using \<open>p_io p = io1@io2\<close> by (metis append_eq_conv_conj take_map) 
  ultimately show ?thesis
    by force 
qed

lemma language_contains_empty_sequence : "[] \<in> L M" by auto


lemma language_state_split :
  assumes "io1 @ io2 \<in> LS M q1"
  obtains  p1 p2 where "path M q1 p1" and "path M (target q1 p1) p2"  and "p_io p1 = io1" and "p_io p2 = io2"
proof -
  obtain p12 where "path M q1 p12" and "p_io p12 = io1 @ io2"
    using assms unfolding LS.simps by auto

  let ?p1 = "take (length io1) p12"
  let ?p2 = "drop (length io1) p12"

  have "p12 = ?p1 @ ?p2" 
    by auto
  then have "path M q1 (?p1 @ ?p2)"
    using \<open>path M q1 p12\<close> by auto

  have "path M q1 ?p1" and "path M (target q1 ?p1) ?p2"
    using path_append_elim[OF \<open>path M q1 (?p1 @ ?p2)\<close>] by blast+
  moreover have "p_io ?p1 = io1"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis append_eq_conv_conj take_map)
  moreover have "p_io ?p2 = io2"
    using \<open>p12 = ?p1 @ ?p2\<close> \<open>p_io p12 = io1 @ io2\<close>
    by (metis (no_types) \<open>p_io p12 = io1 @ io2\<close> append_eq_conv_conj drop_map) 
  ultimately show ?thesis using that by blast
qed






subsection \<open> Basic FSM properties \<close>

subsubsection \<open>Completely Specified\<close>

fun completely_specified :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> inputs M . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x)"


lemma completely_specified_alt_def : "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> inputs M . \<exists> q' y . (q,x,y,q') \<in> transitions M)"
  by force

lemma completely_specified_alt_def_h : "completely_specified M = (\<forall> q \<in> nodes M . \<forall> x \<in> inputs M . h M (q,x) \<noteq> {})"
  by force


value "completely_specified m_ex_H"



fun completely_specified_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where
  "completely_specified_state M q = (\<forall> x \<in> inputs M . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x)"

lemma completely_specified_states :
  "completely_specified M = (\<forall> q \<in> nodes M . completely_specified_state M q)"
  unfolding completely_specified.simps completely_specified_state.simps by force

lemma completely_specified_state_alt_def_h : "completely_specified_state M q = (\<forall> x \<in> inputs M . h M (q,x) \<noteq> {})"
  by force


subsubsection \<open>Deterministic\<close>

fun deterministic :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "deterministic M = (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<longrightarrow> t_output t1 = t_output t2 \<and> t_target t1 = t_target t2)" 

lemma deterministic_alt_def : "deterministic M = (\<forall> q1 x y' y''  q1' q1'' . (q1,x,y',q1') \<in> transitions M \<and> (q1,x,y'',q1'') \<in> transitions M \<longrightarrow> y' = y'' \<and> q1' = q1'')" 
  by auto

lemma deterministic_alt_def_h : "deterministic M = (\<forall> q1 x yq yq' . (yq \<in> h M (q1,x) \<and> yq' \<in> h M (q1,x)) \<longrightarrow> yq = yq')"
  by auto

value "deterministic m_ex_H"


subsubsection \<open>Observable\<close>

fun observable :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "observable M = (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . t_source t1 = t_source t2 \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2 \<longrightarrow> t_target t1 = t_target t2)" 

lemma observable_alt_def : "observable M = (\<forall> q1 x y q1' q1'' . (q1,x,y,q1') \<in> transitions M \<and> (q1,x,y,q1'') \<in> transitions M \<longrightarrow> q1' = q1'')" 
  by auto

lemma observable_alt_def_h : "observable M = (\<forall> q1 x yq yq' . (yq \<in> h M (q1,x) \<and> yq' \<in> h M (q1,x)) \<longrightarrow> fst yq = fst yq' \<longrightarrow> snd yq = snd yq')"
  by auto

value "observable m_ex_H"



subsubsection \<open>Single Input\<close>


(* each state has at most one input, but may have none *)
fun single_input :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "single_input M = (\<forall> t1 \<in> transitions M . \<forall> t2 \<in> transitions M . t_source t1 = t_source t2 \<longrightarrow> t_input t1 = t_input t2)" 


lemma single_input_alt_def : "single_input M = (\<forall> q1 x x' y y' q1' q1'' . (q1,x,y,q1') \<in> transitions M \<and> (q1,x',y',q1'') \<in> transitions M \<longrightarrow> x = x')"
  by fastforce

lemma single_input_alt_def_h : "single_input M = (\<forall> q x x' . (h M (q,x) \<noteq> {} \<and> h M (q,x') \<noteq> {}) \<longrightarrow> x = x')"
  by force
    
value "single_input m_ex_H"  



subsubsection \<open>Output Complete\<close>

fun output_complete :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "output_complete M = (\<forall> t \<in> transitions M . \<forall> y \<in> outputs M . \<exists> t' \<in> transitions M . t_source t = t_source t' \<and> t_input t = t_input t' \<and> t_output t' = y)" 

lemma output_complete_alt_def : "output_complete M = (\<forall> q x . (\<exists> y q' . (q,x,y,q') \<in> transitions M) \<longrightarrow> (\<forall> y \<in> (outputs M) . \<exists> q' . (q,x,y,q') \<in> transitions M))" 
  by force

lemma output_complete_alt_def_h : "output_complete M = (\<forall> q x . h M (q,x) \<noteq> {} \<longrightarrow> (\<forall> y \<in> outputs M . \<exists> q' . (y,q') \<in> h M (q,x)))"
  by force

value "output_complete m_ex_H"



subsubsection \<open>Acyclic\<close>

fun acyclic :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "acyclic M = (\<forall> p . path M (initial M) p \<longrightarrow> distinct (visited_nodes (initial M) p))"


lemma visited_nodes_length : "length (visited_nodes q p) = Suc (length p)" by auto

lemma visited_nodes_take : 
  "(take (Suc n) (visited_nodes q p)) = (visited_nodes q (take n p))"
proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case by (cases "n \<le> length xs"; auto)
qed


(* very inefficient calculation *)
lemma acyclic_code[code] : "acyclic M = (\<not>(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> t_target t \<in> set (visited_nodes (initial M) p)))"
proof -
  have "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> t_target t \<in> set (visited_nodes (initial M) p)) \<Longrightarrow> \<not> FSM.acyclic M"
  proof -
    assume "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> t_target t \<in> set (visited_nodes (initial M) p))"
    then obtain p t where "path M (initial M) p"
                    and   "distinct (visited_nodes (initial M) p)"
                    and   "t \<in> transitions M"
                    and   "t_source t = target (initial M) p" 
                    and   "t_target t \<in> set (visited_nodes (initial M) p)"
      unfolding acyclic_paths_set by blast
    then have "path M (initial M) (p@[t])"
      by (simp add: path_append_transition) 
    moreover have "\<not> (distinct (visited_nodes (initial M) (p@[t])))"
      using \<open>t_target t \<in> set (visited_nodes (initial M) p)\<close> by auto
    ultimately show "\<not> FSM.acyclic M"
      by (meson acyclic.elims(2))
  qed
  moreover have "\<not> FSM.acyclic M \<Longrightarrow> (\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> t_target t \<in> set (visited_nodes (initial M) p))"
  proof -
    assume "\<not> FSM.acyclic M"
    then obtain p where "path M (initial M) p"
                  and   "\<not> distinct (visited_nodes (initial M) p)"
      by auto
    then obtain n where "distinct (take (Suc n) (visited_nodes (initial M) p))"
                  and   "\<not> distinct (take (Suc (Suc n)) (visited_nodes (initial M) p))"
      using maximal_distinct_prefix by blast
    then have "distinct (visited_nodes (initial M) (take n p))"
         and   "\<not> distinct (visited_nodes (initial M)(take (Suc n) p))"
      unfolding visited_nodes_take by simp+

    then obtain p' t' where *: "take n p = p'"
                      and   **: "take (Suc n) p = p' @ [t']"
      by (metis Suc_less_eq \<open>\<not> distinct (visited_nodes (FSM.initial M) p)\<close> le_imp_less_Suc not_less_eq_eq take_all take_hd_drop)
    
    have ***: "visited_nodes (FSM.initial M) (p' @ [t']) = (visited_nodes (FSM.initial M) p')@[t_target t']"
      by auto

    have "path M (initial M) p'"
      using * \<open>path M (initial M) p\<close>
      by (metis append_take_drop_id path_prefix)
    then have "p' \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      using \<open>distinct (visited_nodes (initial M) (take n p))\<close>
      unfolding * acyclic_paths_set by blast
    moreover have "t' \<in> transitions M \<and> t_source t' = target (initial M) p'"
      using * ** \<open>path M (initial M) p\<close>
      by (metis append_take_drop_id path_append_elim path_cons_elim)
       
    moreover have "t_target t' \<in> set (visited_nodes (initial M) p')"
      using \<open>distinct (visited_nodes (initial M) (take n p))\<close> \<open>\<not> distinct (visited_nodes (initial M)(take (Suc n) p))\<close>
      unfolding * ** *** by auto 
    ultimately show "(\<exists> p \<in> (acyclic_paths_up_to_length M (initial M) (size M - 1)) . \<exists> t \<in> transitions M . t_source t = target (initial M) p \<and> t_target t \<in> set (visited_nodes (initial M) p))"
      by blast
  qed
  ultimately show ?thesis by blast
qed


value "acyclic m_ex_H"


lemma acyclic_alt_def : "acyclic M = finite (L M)"
proof 
  show "acyclic M \<Longrightarrow> finite (L M)"
  proof -
    assume "acyclic M"
    then have "{ p . path M (initial M) p} \<subseteq> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_set by auto
    moreover have "finite (acyclic_paths_up_to_length M (initial M) (size M - 1))"
      unfolding acyclic_paths_up_to_length.simps using paths_finite[of M "initial M" "size M - 1"]
      by (metis (mono_tags, lifting) Collect_cong \<open>FSM.acyclic M\<close> acyclic.elims(2)) 
    ultimately have "finite { p . path M (initial M) p}"
      using finite_subset by blast
    then show "finite (L M)"
      unfolding LS.simps by auto
  qed

  show "finite (L M) \<Longrightarrow> acyclic M"
  proof (rule ccontr)
    assume "finite (L M)"
    assume "\<not> acyclic M"
    
    obtain max_io_len where "\<forall>io \<in> L M . length io < max_io_len"
      using finite_maxlen[OF \<open>finite (L M)\<close>] by blast
    then have "\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len"
    proof -
      fix p assume "path M (initial M) p"
      show "length p < max_io_len"
      proof (rule ccontr)
        assume "\<not> length p < max_io_len"
        then have "\<not> length (p_io p) < max_io_len" by auto
        moreover have "p_io p \<in> L M"
          unfolding LS.simps using \<open>path M (initial M) p\<close> by blast
        ultimately show "False"
          using \<open>\<forall>io \<in> L M . length io < max_io_len\<close> by blast
      qed
    qed

    obtain p where "path M (initial M) p" and "\<not> distinct (visited_nodes (initial M) p)"
      using \<open>\<not> acyclic M\<close> unfolding acyclic.simps by blast
    then obtain pL where "path M (initial M) pL" and "max_io_len \<le> length pL"
      using cyclic_path_pumping[of M p max_io_len] by blast
    then show "False"
      using \<open>\<And> p . path M (initial M) p \<Longrightarrow> length p < max_io_len\<close>
      using not_le by blast 
  qed
qed


lemma acyclic_finite_paths_from_reachable_node :
  assumes "acyclic M"
  and     "path M (initial M) p" 
  and     "target (initial M) p = q"
    shows "finite {p . path M q p}"
proof -
  from assms have "{ p . path M (initial M) p} \<subseteq> (acyclic_paths_up_to_length M (initial M) (size M - 1))"
    unfolding acyclic_paths_set by auto
  moreover have "finite (acyclic_paths_up_to_length M (initial M) (size M - 1))"
    unfolding acyclic_paths_up_to_length.simps using paths_finite[of M "initial M" "size M - 1"]
    by (metis (mono_tags, lifting) Collect_cong \<open>FSM.acyclic M\<close> acyclic.elims(2)) 
  ultimately have "finite { p . path M (initial M) p}"
    using finite_subset by blast

  show "finite {p . path M q p}"
  proof (cases "q \<in> nodes M")
    case True
        
    have "image (\<lambda>p' . p@p') {p' . path M q p'} \<subseteq> {p' . path M (initial M) p'}"
    proof 
      fix x assume "x \<in> image (\<lambda>p' . p@p') {p' . path M q p'}"
      then obtain p' where "x = p@p'" and "p' \<in> {p' . path M q p'}"
        by blast
      then have "path M q p'" by auto
      then have "path M (initial M) (p@p')"
        using path_append[OF \<open>path M (initial M) p\<close>] \<open>target (initial M) p = q\<close> by auto
      then show "x \<in> {p' . path M (initial M) p'}" using \<open>x = p@p'\<close> by blast
    qed
    
    then have "finite (image (\<lambda>p' . p@p') {p' . path M q p'})"
      using \<open>finite { p . path M (initial M) p}\<close> finite_subset by auto 
    show ?thesis using finite_imageD[OF \<open>finite (image (\<lambda>p' . p@p') {p' . path M q p'})\<close>]
      by (meson inj_onI same_append_eq) 
  next
    case False
    then show ?thesis
      by (meson not_finite_existsD path_begin_node) 
  qed
qed


lemma acyclic_paths_from_reachable_nodes :
  assumes "acyclic M" 
  and     "path M (initial M) p'" 
  and     "target (initial M) p' = q"
  and     "path M q p"
shows "distinct (visited_nodes q p)"
proof -
  have "path M (initial M) (p'@p)"
    using assms(2,3,4) path_append by metis
  then have "distinct (visited_nodes (initial M) (p'@p))"
    using assms(1) unfolding acyclic.simps by blast
  then have "distinct (initial M # (map t_target p') @ map t_target p)"
    by auto
  moreover have "initial M # (map t_target p') @ map t_target p = (butlast (initial M # map t_target p')) @ ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  ultimately have "distinct ((last (initial M # map t_target p')) # map t_target p)"
    by auto
  then show ?thesis 
    using \<open>target (initial M) p' = q\<close> unfolding visited_nodes.simps target.simps by simp
qed

definition LS_acyclic :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list set" where
  "LS_acyclic M q = {p_io p | p .  path M q p \<and> distinct (visited_nodes q p)}"

lemma LS_acyclic_code[code] : 
  "LS_acyclic M q = image p_io (acyclic_paths_up_to_length M q (size M - 1))"
  unfolding acyclic_paths_set LS_acyclic_def by blast

lemma LS_from_LS_acyclic : 
  assumes "acyclic M" 
  shows "L M = LS_acyclic M (initial M)"
proof -
  obtain pps :: "(('b \<times> 'c) list \<Rightarrow> bool) \<Rightarrow> (('b \<times> 'c) list \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'c) list" where
    f1: "\<forall>p pa. (\<not> p (pps pa p)) = pa (pps pa p) \<or> Collect p = Collect pa"
    by (metis (no_types) Collect_cong)
  have "\<forall>ps. \<not> path M (FSM.initial M) ps \<or> distinct (visited_nodes (FSM.initial M) ps)"
    using acyclic.simps assms by blast
  then have "(\<nexists>ps. pps (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa) (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa \<and> distinct (visited_nodes (FSM.initial M) psa)) = p_io ps \<and> path M (FSM.initial M) ps \<and> distinct (visited_nodes (FSM.initial M) ps)) \<noteq> (\<exists>ps. pps (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa) (\<lambda>ps. \<exists>psa. ps = p_io psa \<and> path M (FSM.initial M) psa \<and> distinct (visited_nodes (FSM.initial M) psa)) = p_io ps \<and> path M (FSM.initial M) ps)"
    by blast
  then have "{p_io ps |ps. path M (FSM.initial M) ps \<and> distinct (visited_nodes (FSM.initial M) ps)} = {p_io ps |ps. path M (FSM.initial M) ps}"
    using f1 by (meson \<open>\<forall>ps. \<not> path M (FSM.initial M) ps \<or> distinct (visited_nodes (FSM.initial M) ps)\<close>) 
  then show ?thesis
    by (simp add: LS_acyclic_def)
qed



lemma cyclic_cycle :
  assumes "\<not> acyclic M"
  shows "\<exists> q p . path M q p \<and> p \<noteq> [] \<and> target q p = q" 
proof -
  from \<open>\<not> acyclic M\<close> obtain p t where "path M (initial M) (p@[t])" and "\<not>distinct (visited_nodes (initial M) (p@[t]))"
    by (metis (no_types, hide_lams) Nil_is_append_conv acyclic.simps append_take_drop_id maximal_distinct_prefix rev_exhaust visited_nodes_take)
     

  show ?thesis
  proof (cases "initial M \<in> set (map t_target (p@[t]))")
    case True
    then obtain i where "last (take i (map t_target (p@[t]))) = initial M" and "i \<le> length (map t_target (p@[t]))" and "0 < i"
      using list_contains_last_take by metis

    let ?p = "take i (p@[t])"
    have "path M (initial M) (?p@(drop i (p@[t])))" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis append_take_drop_id)  
    then have "path M (initial M) ?p" by auto
    moreover have "?p \<noteq> []" using \<open>0 < i\<close> by auto
    moreover have "target (initial M) ?p = initial M"
      using \<open>last (take i (map t_target (p@[t]))) = initial M\<close> unfolding target.simps visited_nodes.simps
      by (metis (no_types, lifting) calculation(2) last_ConsR list.map_disc_iff take_map) 
    ultimately show ?thesis by blast
  next
    case False
    then have "\<not> distinct (map t_target (p@[t]))"
      using \<open>\<not>distinct (visited_nodes (initial M) (p@[t]))\<close> unfolding visited_nodes.simps by auto
    then obtain i j where "i < j" and "j < length (map t_target (p@[t]))" and "(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j"
      using non_distinct_repetition_indices by blast

    let ?pre_i = "take (Suc i) (p@[t])"
    let ?p = "take ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"
    let ?post_j = "drop ((Suc j)-(Suc i)) (drop (Suc i) (p@[t]))"

    have "p@[t] = ?pre_i @ ?p @ ?post_j"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close>
      by (metis append_take_drop_id) 
    then have "path M (target (initial M) ?pre_i) ?p" 
      using \<open>path M (initial M) (p@[t])\<close>
      by (metis path_prefix path_suffix) 

    have "?p \<noteq> []"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto

    have "i < length (map t_target (p@[t]))"
      using \<open>i < j\<close> \<open>j < length (map t_target (p@[t]))\<close> by auto
    have "(target (initial M) ?pre_i) = (map t_target (p@[t])) ! i"
      unfolding target.simps visited_nodes.simps  
      using take_last_index[OF \<open>i < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>i < length (map t_target (p @ [t]))\<close> last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    
    have "?pre_i@?p = take (Suc j) (p@[t])"
      by (metis (no_types) \<open>i < j\<close> add_Suc add_diff_cancel_left' less_SucI less_imp_Suc_add take_add)
    moreover have "(target (initial M) (take (Suc j) (p@[t]))) = (map t_target (p@[t])) ! j"
      unfolding target.simps visited_nodes.simps  
      using take_last_index[OF \<open>j < length (map t_target (p@[t]))\<close>]
      by (metis (no_types, lifting) \<open>j < length (map t_target (p @ [t]))\<close> last_ConsR snoc_eq_iff_butlast take_Suc_conv_app_nth take_map) 
    ultimately have "(target (initial M) (?pre_i@?p)) = (map t_target (p@[t])) ! j"
      by auto
    then have "(target (initial M) (?pre_i@?p)) = (map t_target (p@[t])) ! i"
      using \<open>(map t_target (p@[t])) ! i = (map t_target (p@[t])) ! j\<close> by simp
    moreover have "(target (initial M) (?pre_i@?p)) = (target (target (initial M) ?pre_i) ?p)"
      unfolding target.simps visited_nodes.simps last.simps by auto
    ultimately have "(target (target (initial M) ?pre_i) ?p) = (map t_target (p@[t])) ! i"
      by auto
    then have "(target (target (initial M) ?pre_i) ?p) = (target (initial M) ?pre_i)"
      using \<open>(target (initial M) ?pre_i) = (map t_target (p@[t])) ! i\<close> by auto

    show ?thesis
      using \<open>path M (target (initial M) ?pre_i) ?p\<close> \<open>?p \<noteq> []\<close> \<open>(target (target (initial M) ?pre_i) ?p) = (target (initial M) ?pre_i)\<close>
      by blast
  qed
qed


lemma cyclic_cycle_rev :
  fixes M :: "('a,'b,'c) fsm"
  assumes "path M (initial M) p'"
  and     "target (initial M) p' = q" 
  and     "path M q p"
  and     "p \<noteq> []"
  and     "target q p = q"
shows "\<not> acyclic M"
  using assms unfolding acyclic.simps target.simps visited_nodes.simps
  using distinct.simps(2) by fastforce

lemma acyclic_initial :
  assumes "acyclic M"
  shows "\<not> (\<exists> t \<in> transitions M . t_target t = initial M \<and> (\<exists> p . path M (initial M) p \<and> target (initial M) p = t_source t))"
  by (metis append_Cons assms cyclic_cycle_rev list.distinct(1) path.simps path_append path_append_transition_elim(3) single_transition_path) 

lemma cyclic_path_shift : 
  assumes "path M q p"
  and     "target q p = q"
shows "path M (target q (take i p)) ((drop i p) @ (take i p))"
  and "target (target q (take i p)) ((drop i p) @ (take i p)) = (target q (take i p))"
proof -
  show "path M (target q (take i p)) ((drop i p) @ (take i p))"
    by (metis append_take_drop_id assms(1) assms(2) path_append path_append_elim path_append_target)
  show "target (target q (take i p)) ((drop i p) @ (take i p)) = (target q (take i p))"
    by (metis append_take_drop_id assms(2) path_append_target)
qed


lemma cyclic_path_transition_nodes_property :
  assumes "\<exists> t \<in> set p . P (t_source t)"
  and     "\<forall> t \<in> set p . P (t_source t) \<longrightarrow> P (t_target t)"
  and     "path M q p"
  and     "target q p = q"
shows "\<forall> t \<in> set p . P (t_source t)"
  and "\<forall> t \<in> set p . P (t_target t)"
proof -
  obtain t0 where "t0 \<in> set p" and "P (t_source t0)"
    using assms(1) by blast
  then obtain i where "i < length p" and "p ! i = t0"
    by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target q (take i p)) ?p"
    using cyclic_path_shift(1)[OF assms(3,4), of i] by assumption
  
  have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed
  then have "\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)"
    using assms(2) by blast
  
  have "\<And> j . j < length ?p \<Longrightarrow> P (t_source (?p ! j))"
  proof -
    fix j assume "j < length ?p"
    then show "P (t_source (?p ! j))"
    proof (induction j)
      case 0
      then show ?case 
        using \<open>p ! i = t0\<close> \<open>P (t_source t0)\<close>
        by (metis \<open>i < length p\<close> drop_eq_Nil hd_append2 hd_conv_nth hd_drop_conv_nth leD length_greater_0_conv)  
    next
      case (Suc j)
      then have "P (t_source (?p ! j))"
        by auto
      then have "P (t_target (?p ! j))"
        using Suc.prems \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        using Suc_lessD nth_mem by blast 
      moreover have "t_target (?p ! j) = t_source (?p ! (Suc j))"
        using path_source_target_index[OF Suc.prems \<open>path M (target q (take i p)) ?p\<close>] by assumption
      ultimately show ?case 
        using \<open>\<And> t . t \<in> set ?p \<Longrightarrow> P (t_source t) \<Longrightarrow> P (t_target t)\<close>[of "?p ! j"]
        by simp
    qed
  qed
  then have "\<forall> t \<in> set ?p . P (t_source t)"
    by (metis in_set_conv_nth)
  then show "\<forall> t \<in> set p . P (t_source t)"
    using \<open>set ?p = set p\<close> by blast
  then show "\<forall> t \<in> set p . P (t_target t)"
    using assms(2) by blast
qed


lemma cycle_incoming_transition_ex :
  assumes "path M q p"
  and     "p \<noteq> []"
  and     "target q p = q"
  and     "t \<in> set p"
shows "\<exists> tI \<in> set p . t_target tI = t_source t"
proof -
  obtain i where "i < length p" and "p ! i = t"
    using assms(4) by (meson in_set_conv_nth)

  let ?p = "(drop i p @ take i p)"
  have "path M (target q (take i p)) ?p"
  and  "target (target q (take i p)) ?p = target q (take i p)"
    using cyclic_path_shift[OF assms(1,3), of i] by linarith+

  have "p = (take i p @ drop i p)" by auto
  then have "path M (target q (take i p)) (drop i p)" 
    using path_suffix assms(1) by metis
  moreover have "t = hd (drop i p)"
    using \<open>i < length p\<close> \<open>p ! i = t\<close>
    by (simp add: hd_drop_conv_nth) 
  ultimately have "path M (target q (take i p)) [t]"
    by (metis \<open>i < length p\<close> append_take_drop_id assms(1) path_append_elim take_hd_drop)
  then have "t_source t = (target q (take i p))"
    by auto  
  moreover have "t_target (last ?p) = (target q (take i p))"
    using \<open>path M (target q (take i p)) ?p\<close> \<open>target (target q (take i p)) ?p = target q (take i p)\<close> assms(2)
    unfolding target.simps visited_nodes.simps last.simps
  proof -
    assume a1: "(if map t_target (drop i p @ take i p) = [] then if map t_target (take i p) = [] then q else last (map t_target (take i p)) else last (map t_target (drop i p @ take i p))) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
    have "drop i p @ take i p \<noteq> [] \<and> map t_target (drop i p @ take i p) \<noteq> []"
      using \<open>p \<noteq> []\<close> by fastforce
    moreover
    { assume "map t_target (take i p) \<noteq> [] \<and> map t_target (drop i p @ take i p) \<noteq> []"
      then have "t_target (last (drop i p @ take i p)) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
        by (simp add: last_map) }
    ultimately show "t_target (last (drop i p @ take i p)) = (if map t_target (take i p) = [] then q else last (map t_target (take i p)))"
      using a1 by (metis (no_types) last_map)
  qed
    
  
  moreover have "set ?p = set p"
  proof -
    have "set ?p = set (take i p @ drop i p)" 
      using list_set_sym by metis
    then show ?thesis by auto
  qed

  ultimately show ?thesis
    by (metis \<open>i < length p\<close> append_is_Nil_conv drop_eq_Nil last_in_set leD) 
qed


subsubsection \<open>Deadlock Nodes\<close>

fun deadlock_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> bool" where 
  "deadlock_state M q = (\<not>(\<exists> t \<in> transitions M . t_source t = q))"

lemma deadlock_state_alt_def : "deadlock_state M q = (LS M q \<subseteq> {[]})" 
proof 
  show "deadlock_state M q \<Longrightarrow> LS M q \<subseteq> {[]}" 
  proof -
    assume "deadlock_state M q"
    moreover have "\<And> p . deadlock_state M q \<Longrightarrow> path M q p \<Longrightarrow> p = []"
      unfolding deadlock_state.simps by (metis path.cases) 
    ultimately show "LS M q \<subseteq> {[]}"
      unfolding LS.simps by blast
  qed
  show "LS M q \<subseteq> {[]} \<Longrightarrow> deadlock_state M q"
    unfolding LS.simps deadlock_state.simps using path.cases[of M q] by blast
qed

lemma deadlock_state_alt_def_h : "deadlock_state M q = (\<forall> x \<in> inputs M . h M (q,x) = {})" 
  unfolding deadlock_state.simps h.simps 
  using fsm_transition_input by force


lemma acyclic_deadlock_states :
  assumes "acyclic M"
  shows "\<exists> q \<in> nodes M . deadlock_state M q"
proof (rule ccontr)
  assume "\<not> (\<exists>q\<in>nodes M. deadlock_state M q)"
  then have *: "\<And> q . q \<in> nodes M \<Longrightarrow> (\<exists> t \<in> transitions M . t_source t = q)"
    unfolding deadlock_state.simps by blast

  let ?p = "arg_max_on length {p. path M (initial M) p}"
  

  have "finite {p. path M (initial M) p}" 
    by (metis Collect_cong acyclic_finite_paths_from_reachable_node assms eq_Nil_appendI fsm_initial nil path_append path_append_elim) 
    
  moreover have "{p. path M (initial M) p} \<noteq> {}" 
    by auto
  ultimately obtain p where "path M (initial M) p" and "\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p" 
    using max_length_elem
    by (metis mem_Collect_eq not_le_imp_less)

  then obtain t where "t \<in> transitions M" and "t_source t = target (initial M) p"
    using * path_target_is_node by metis

  then have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close>
    by (simp add: path_append_transition)

  then show "False"
    using \<open>\<And> p' . path M (initial M) p' \<Longrightarrow> length p' \<le> length p\<close>
    by (metis impossible_Cons length_rotate1 rotate1.simps(2)) 
qed

lemma deadlock_prefix :
  assumes "path M q p"
  and     "t \<in> set (butlast p)"
shows "\<not> (deadlock_state M (t_target t))"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t' p')
  
  show ?case proof (cases "t \<in> set (butlast p')")
    case True
    show ?thesis 
      using snoc.IH[OF _ True] snoc.prems(1)
      by blast 
  next
    case False
    then have "p' = (butlast p')@[t]"
      using snoc.prems(2) by (metis append_butlast_last_id append_self_conv2 butlast_snoc in_set_butlast_appendI list_prefix_elem set_ConsD)
    then have "path M q ((butlast p'@[t])@[t'])"
      using snoc.prems(1)
      by auto 
    
    have "t' \<in> transitions M" and "t_source t' = target q (butlast p'@[t])"
      using path_suffix[OF \<open>path M q ((butlast p'@[t])@[t'])\<close>]
      by auto
    then have "t' \<in> transitions M \<and> t_source t' = t_target t"
      unfolding target.simps visited_nodes.simps by auto
    then show ?thesis 
      unfolding deadlock_state.simps using \<open>t' \<in> transitions M\<close> by blast
  qed
qed


subsubsection \<open>Other\<close>

fun completed_path :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> bool" where
  "completed_path M q p = deadlock_state M (target q p)"

fun minimal :: "('a,'b,'c) fsm \<Rightarrow> bool" where
  "minimal M = (\<forall> q \<in> nodes M . \<forall> q' \<in> nodes M . q \<noteq> q' \<longrightarrow> LS M q \<noteq> LS M q')"

definition retains_outputs_for_states_and_inputs :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "retains_outputs_for_states_and_inputs M S = (\<forall> tS \<in> transitions S . \<forall> tM \<in> transitions M . (t_source tS = t_source tM \<and> t_input tS = t_input tM) \<longrightarrow> tM \<in> transitions S)"





subsection \<open>IO Targets and Observability\<close>


fun paths_for_io' :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) path \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_io' f [] q prev = {prev}" |
  "paths_for_io' f ((x,y)#io) q prev = \<Union>(image (\<lambda>yq' . paths_for_io' f io (snd yq') (prev@[(q,x,y,(snd yq'))])) (Set.filter (\<lambda>yq' . fst yq' = y) (f (q,x))))"

lemma paths_for_io'_set :
  assumes "q \<in> nodes M"
  shows   "paths_for_io' (h M) io q prev = {prev@p | p . path M q p \<and> p_io p = io}"
using assms proof (induction io arbitrary: q prev)
  case Nil
  then show ?case by auto
next
  case (Cons xy io)
  obtain x y where "xy = (x,y)"
    by (meson surj_pair) 

  let ?UN = "\<Union>(image (\<lambda>yq' . paths_for_io' (h M) io (snd yq') (prev@[(q,x,y,(snd yq'))])) (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x))))"

  have "?UN = {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
  proof 
    have "\<And> p . p \<in> ?UN \<Longrightarrow> p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
    proof -
      fix p assume "p \<in> ?UN"
      then obtain q' where "(y,q') \<in> (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x)))"
                     and   "p \<in> paths_for_io' (h M) io q' (prev@[(q,x,y,q')])"
        by auto
      
      from \<open>(y,q') \<in> (Set.filter (\<lambda>yq' . fst yq' = y) (h M (q,x)))\<close> have "q' \<in> nodes M" and "(q,x,y,q') \<in> transitions M"
        using fsm_transition_target unfolding h.simps by auto

      have "p \<in> {(prev @ [(q, x, y, q')]) @ p |p. path M q' p \<and> p_io p = io}"
        using \<open>p \<in> paths_for_io' (h M) io q' (prev@[(q,x,y,q')])\<close>
        unfolding Cons.IH[OF \<open>q' \<in> nodes M\<close>] by assumption
      moreover have " {(prev @ [(q, x, y, q')]) @ p |p. path M q' p \<and> p_io p = io} \<subseteq> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
        using \<open>(q,x,y,q') \<in> transitions M\<close>
        using cons by force 
      ultimately show "p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}" 
        by blast
    qed
    then show "?UN \<subseteq> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
      by blast

    have "\<And> p . p \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io} \<Longrightarrow> p \<in> ?UN"
    proof -
      fix pp assume "pp \<in> {prev@p | p . path M q p \<and> p_io p = (x,y)#io}"
      then obtain p where "pp = prev@p" and "path M q p" and "p_io p = (x,y)#io"
        by fastforce
      then obtain t p' where "p = t#p'" and "path M q (t#p')" and "p_io (t#p') = (x,y)#io" and "p_io p' = io"
        by (metis (no_types, lifting) map_eq_Cons_D)
      then have "path M (t_target t) p'" and "t_source t = q" and "t_input t = x" and "t_output t = y" and "t_target t \<in> nodes M" and "t \<in> transitions M"
        by auto

      have "(y,t_target t) \<in> Set.filter (\<lambda>yq'. fst yq' = y) (h M (q, x))"
        using \<open>t \<in> transitions M\<close> \<open>t_output t = y\<close> \<open>t_input t = x\<close> \<open>t_source t = q\<close>
        unfolding h.simps
        by auto 
      moreover have "(prev@p) \<in> paths_for_io' (h M) io (snd (y,t_target t)) (prev @ [(q, x, y, snd (y,t_target t))])"
        using Cons.IH[OF \<open>t_target t \<in> nodes M\<close>, of "prev@[(q, x, y, t_target t)]"]
        using \<open>p = t # p'\<close> \<open>p_io p' = io\<close> \<open>path M (t_target t) p'\<close> \<open>t_input t = x\<close> \<open>t_output t = y\<close> \<open>t_source t = q\<close> by auto

      ultimately show "pp \<in> ?UN" unfolding \<open>pp = prev@p\<close>
        by blast 
    qed
    then show "{prev@p | p . path M q p \<and> p_io p = (x,y)#io} \<subseteq> ?UN"
      by (meson subsetI) 
  qed

  then show ?case
    by (simp add: \<open>xy = (x, y)\<close>) 
qed



definition paths_for_io :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> ('a,'b,'c) path set" where
  "paths_for_io M q io = {p . path M q p \<and> p_io p = io}"

lemma paths_for_io_set_code[code] :
  "paths_for_io M q io = (if q \<in> nodes M then paths_for_io' (h M) io q [] else {})"
  using paths_for_io'_set[of q M io "[]"]
  unfolding paths_for_io_def
proof -
  have "{[] @ ps |ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.nodes M then paths_for_io' (h M) io q [] else {}) \<longrightarrow> {ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.nodes M then paths_for_io' (h M) io q [] else {})"
    by auto
  moreover
    { assume "{[] @ ps |ps. path M q ps \<and> p_io ps = io} \<noteq> (if q \<in> FSM.nodes M then paths_for_io' (h M) io q [] else {})"
      then have "q \<notin> FSM.nodes M"
        using \<open>q \<in> FSM.nodes M \<Longrightarrow> paths_for_io' (h M) io q [] = {[] @ p |p. path M q p \<and> p_io p = io}\<close> by force
      then have "{ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.nodes M then paths_for_io' (h M) io q [] else {})"
      using path_begin_node by force }
  ultimately show "{ps. path M q ps \<and> p_io ps = io} = (if q \<in> FSM.nodes M then paths_for_io' (h M) io q [] else {})"
    by linarith
qed 

value "paths_for_io m_ex_H 1 []"
value "paths_for_io m_ex_H 1 [(1,1),(1,0)]"

fun io_targets :: "('a,'b,'c) fsm \<Rightarrow> ('b \<times> 'c) list \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "io_targets M io q = {target q p | p . path M q p \<and> p_io p = io}"

lemma io_targets_code[code] : "io_targets M io q = image (target q) (paths_for_io M q io)"
  unfolding io_targets.simps paths_for_io_def by blast

lemma io_targets_nodes :
  "io_targets M io q \<subseteq> nodes M"
  using path_target_is_node by fastforce



lemma observable_transition_unique :
  assumes "observable M"
      and "t \<in> transitions M"
    shows "\<exists>! t' \<in> transitions M . t_source t' = t_source t \<and> t_input t' = t_input t \<and> t_output t' = t_output t"
  by (metis assms observable.elims(2) prod.expand)

lemma observable_path_unique :
  assumes "observable M"
  and     "path M q p"
  and     "path M q p'"
  and     "p_io p = p_io p'"
shows "p = p'"
proof -
  have "length p = length p'"
    using assms(4) map_eq_imp_length_eq by blast 
  then show ?thesis
  using \<open>p_io p = p_io p'\<close> \<open>path M q p\<close> \<open>path M q p'\<close> proof (induction p p' arbitrary: q rule: list_induct2)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs y ys)
    then have *: "x \<in> transitions M \<and> y \<in> transitions M \<and> t_source x = t_source y \<and> t_input x = t_input y \<and> t_output x = t_output y" 
      by auto
    then have "t_target x = t_target y" 
      using assms(1) observable.elims(2) by blast 
    then have "x = y"
      by (simp add: "*" prod.expand) 
      

    have "p_io xs = p_io ys" 
      using Cons by auto

    moreover have "path M (t_target x) xs" 
      using Cons by auto
    moreover have "path M (t_target x) ys"
      using Cons \<open>t_target x = t_target y\<close> by auto
    ultimately have "xs = ys" 
      using Cons by auto

    then show ?case 
      using \<open>x = y\<close> by simp
  qed
qed


lemma observable_io_targets : 
  assumes "observable M"
  and "io \<in> LS M q"
obtains q'
where "io_targets M io q = {q'}"
proof -

  obtain p where "path M q p" and "p_io p = io" 
    using assms(2) by auto 
  then have "target q p \<in> io_targets M io q"
    by auto   

  have "\<exists> q' . io_targets M io q = {q'}"
  proof (rule ccontr)
    assume "\<not>(\<exists>q'. io_targets M io q = {q'})"
    then have "\<exists> q' . q' \<noteq> target q p \<and> q' \<in> io_targets M io q"
    proof -
      have "\<not> io_targets M io q \<subseteq> {target q p}"
        using \<open>\<not>(\<exists>q'. io_targets M io q = {q'})\<close> \<open>target q p \<in> io_targets M io q\<close> by blast
      then show ?thesis
        by blast
    qed       
    then obtain q' where "q' \<noteq> target q p" and "q' \<in> io_targets M io q" 
      by blast
    then obtain p' where "path M q p'" and "target q p' = q'" and "p_io p' = io"
      by auto 
    then have "p_io p = p_io p'" 
      using \<open>p_io p = io\<close> by simp
    then have "p = p'"
      using observable_path_unique[OF assms(1) \<open>path M q p\<close> \<open>path M q p'\<close>] by simp
    then show "False"
      using \<open>q' \<noteq> target q p\<close> \<open>target q p' = q'\<close> by auto
  qed

  then show ?thesis using that by blast
qed


lemma observable_path_io_target : 
  assumes "observable M"
  and     "path M q p"
shows "io_targets M (p_io p) q = {target q p}"
  using observable_io_targets[OF assms(1) language_state_containment[OF assms(2)], of "p_io p"] singletonD[of "target q p"]
  unfolding io_targets.simps
proof -
  assume a1: "\<And>a. target q p \<in> {a} \<Longrightarrow> target q p = a"
  assume "\<And>thesis. \<lbrakk>p_io p = p_io p; \<And>q'. {target q pa |pa. path M q pa \<and> p_io pa = p_io p} = {q'} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis"
  then obtain aa :: 'a where "\<And>b. {target q ps |ps. path M q ps \<and> p_io ps = p_io p} = {aa} \<or> b"
    by meson
  then show "{target q ps |ps. path M q ps \<and> p_io ps = p_io p} = {target q p}"
    using a1 assms(2) by blast
qed


lemma completely_specified_io_targets : 
  assumes "completely_specified M"
  shows "\<forall> q \<in> io_targets M io (initial M) . \<forall> x \<in> (inputs M) . \<exists> t \<in> transitions M . t_source t = q \<and> t_input t = x"
  by (meson assms completely_specified.elims(2) io_targets_nodes subsetD)
  


lemma observable_path_language_step :
  assumes "observable M"
      and "path M q p"
      and "\<not> (\<exists>t\<in>transitions M.
               t_source t = target q p \<and>
               t_input t = x \<and> t_output t = y)"
    shows "(p_io p)@[(x,y)] \<notin> LS M q"
using assms proof (induction p rule: rev_induct)
  case Nil
  show ?case proof
    assume "p_io [] @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = [(x,y)]" unfolding LS.simps
      by force 
    then obtain t where "p' = [t]" by blast
    
    have "t\<in>transitions M" and "t_source t = target q []"
      using \<open>path M q p'\<close> \<open>p' = [t]\<close> by auto
    moreover have "t_input t = x \<and> t_output t = y"
      using \<open>p_io p' = [(x,y)]\<close> \<open>p' = [t]\<close> by auto
    ultimately show "False"
      using Nil.prems(3) by blast
  qed
next
  case (snoc t p)
  
  from \<open>path M q (p @ [t])\<close> have "path M q p" and "t_source t = target q p" and "t \<in> transitions M" by auto

  show ?case proof
    assume "p_io (p @ [t]) @ [(x, y)] \<in> LS M q"
    then obtain p' where "path M q p'" and "p_io p' = p_io (p @ [t]) @ [(x, y)]"
      by auto
    then obtain p'' t' t'' where "p' = p''@[t']@[t'']"
      by (metis (no_types, lifting) append.assoc map_butlast map_is_Nil_conv snoc_eq_iff_butlast)
    then have "path M q p''" 
      using \<open>path M q p'\<close> by blast
    
    
    have "p_io p'' = p_io p"
      using \<open>p' = p''@[t']@[t'']\<close> \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> by auto
    then have "p'' = p"
      using observable_path_unique[OF assms(1) \<open>path M q p''\<close> \<open>path M q p\<close>] by blast

    have "t_source t' = target q p''" and "t' \<in> transitions M"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    then have "t_source t' = t_source t"
      using \<open>p'' = p\<close> \<open>t_source t = target q p\<close> by auto 
    moreover have "t_input t' = t_input t \<and> t_output t' = t_output t"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> transitions M\<close> \<open>t' \<in> transitions M\<close> assms(1) unfolding observable.simps by (meson prod.expand) 

    have "t'' \<in> transitions M" and "t_source t'' = target q (p@[t])"
      using \<open>path M q p'\<close> \<open>p' = p''@[t']@[t'']\<close> \<open>p'' = p\<close> \<open>t' = t\<close> by auto
    moreover have "t_input t'' = x \<and> t_output t'' = y"
      using \<open>p_io p' = p_io (p @ [t]) @ [(x, y)]\<close> \<open>p' = p''@[t']@[t'']\<close> by auto
    ultimately show "False"
      using snoc.prems(3) by blast
  qed
qed

lemma observable_io_targets_language :
  assumes "io1 @ io2 \<in> LS M q1"
  and     "observable M"
  and     "q2 \<in> io_targets M io1 q1"
shows "io2 \<in> LS M q2" 
proof -
  obtain p1 p2 where "path M q1 p1" and "path M (target q1 p1) p2"  and "p_io p1 = io1" and "p_io p2 = io2"
    using language_state_split[OF assms(1)] by blast
  then have "io1 \<in> LS M q1" and "io2 \<in> LS M (target q1 p1)"
    by auto
  
  have "target q1 p1 \<in> io_targets M io1 q1"
    using \<open>path M q1 p1\<close> \<open>p_io p1 = io1\<close>
    unfolding io_targets.simps by blast
  then have "target q1 p1 = q2"
    using observable_io_targets[OF assms(2) \<open>io1 \<in> LS M q1\<close>]
    by (metis assms(3) singletonD) 
  then show ?thesis
    using \<open>io2 \<in> LS M (target q1 p1)\<close> by auto
qed

lemma io_targets_next :
  assumes "t \<in> transitions M"
  shows "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
unfolding io_targets.simps
proof 
  fix q assume "q \<in> {target (t_target t) p |p. path M (t_target t) p \<and> p_io p = io}"
  then obtain p where "path M (t_target t) p \<and> p_io p = io \<and> target (t_target t) p = q"
    by auto
  then have "path M (t_source t) (t#p) \<and> p_io (t#p) = p_io [t] @ io \<and> target (t_source t) (t#p) = q"
    using FSM.path.cons[OF assms] by auto
  then show "q \<in> {target (t_source t) p |p. path M (t_source t) p \<and> p_io p = p_io [t] @ io}"
    by blast
qed




lemma observable_io_targets_next :
  assumes "observable M"
  and     "t \<in> transitions M"
shows "io_targets M (p_io [t] @ io) (t_source t) = io_targets M io (t_target t)" 
proof 
  show "io_targets M (p_io [t] @ io) (t_source t) \<subseteq> io_targets M io (t_target t)"
  proof 
    fix q assume "q \<in> io_targets M (p_io [t] @ io) (t_source t)"
    then obtain p where "q = target (t_source t) p" and "path M (t_source t) p" and "p_io p = p_io [t] @ io"
      unfolding io_targets.simps by blast
    then have "q = t_target (last p)" unfolding target.simps visited_nodes.simps
      using last_map by auto 

    obtain t' p' where "p = t' # p'"
      using \<open>p_io p = p_io [t] @ io\<close> by auto
    then have "t' \<in> transitions M" and "t_source t' = t_source t"
      using \<open>path M (t_source t) p\<close> by auto
    moreover have "t_input t' = t_input t" and "t_output t' = t_output t"
      using \<open>p = t' # p'\<close> \<open>p_io p = p_io [t] @ io\<close> by auto
    ultimately have "t' = t"
      using \<open>t \<in> transitions M\<close> \<open>observable M\<close> unfolding observable.simps
      by (meson prod.expand) 

    then have "path M (t_target t) p'"
      using \<open>path M (t_source t) p\<close> \<open>p = t' # p'\<close> by auto
    moreover have "p_io p' = io"
      using \<open>p_io p = p_io [t] @ io\<close> \<open>p = t' # p'\<close> by auto
    moreover have "q = target (t_target t) p'"
      using \<open>q = target (t_source t) p\<close> \<open>p = t' # p'\<close> \<open>t' = t\<close> by auto
    ultimately show "q \<in> io_targets M io (t_target t)"
      by auto
  qed

  show "io_targets M io (t_target t) \<subseteq> io_targets M (p_io [t] @ io) (t_source t)"
    using io_targets_next[OF assms(2)] by assumption
qed



lemma observable_language_target :
  assumes "observable M"
  and     "q \<in> io_targets M io1 (initial M)"
  and     "t \<in> io_targets T io1 (initial T)"
  and     "L T \<subseteq> L M"
shows "LS T t \<subseteq> LS M q"
proof 
  fix io2 assume "io2 \<in> LS T t"
  then obtain pT2 where "path T t pT2" and "p_io pT2 = io2"
    by auto

  
  
  obtain pT1 where "path T (initial T) pT1" and "p_io pT1 = io1" and "target (initial T) pT1 = t"
    using \<open>t \<in> io_targets T io1 (initial T)\<close> by auto
  then have "path T (initial T) (pT1@pT2)" 
    using \<open>path T t pT2\<close> using path_append by metis
  moreover have "p_io (pT1@pT2) = io1@io2"
    using \<open>p_io pT1 = io1\<close> \<open>p_io pT2 = io2\<close> by auto
  ultimately have "io1@io2 \<in> L T"
    using language_state_containment[of T] by auto
  then have "io1@io2 \<in> L M"
    using \<open>L T \<subseteq> L M\<close> by blast
  then obtain pM where "path M (initial M) pM" and "p_io pM = io1@io2"
    by auto

  let ?pM1 = "take (length io1) pM"
  let ?pM2 = "drop (length io1) pM"

  have "path M (initial M) (?pM1@?pM2)"
    using \<open>path M (initial M) pM\<close> by auto
  then have "path M (initial M) ?pM1" and "path M (target (initial M) ?pM1) ?pM2"
    by blast+
  
  have "p_io ?pM1 = io1"
    using \<open>p_io pM = io1@io2\<close> 
    by (metis append_eq_conv_conj take_map)
  have "p_io ?pM2 = io2"
    using \<open>p_io pM = io1@io2\<close> 
    by (metis append_eq_conv_conj drop_map)

  obtain pM1 where "path M (initial M) pM1" and "p_io pM1 = io1" and "target (initial M) pM1 = q"
    using \<open>q \<in> io_targets M io1 (initial M)\<close> by auto

  have "pM1 = ?pM1"
    using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) pM1\<close> \<open>path M (initial M) ?pM1\<close>]
    unfolding \<open>p_io pM1 = io1\<close> \<open>p_io ?pM1 = io1\<close> by simp

  then have "path M q ?pM2"
    using \<open>path M (target (initial M) ?pM1) ?pM2\<close> \<open>target (initial M) pM1 = q\<close> by auto
  then show "io2 \<in> LS M q"
    using language_state_containment[OF _ \<open>p_io ?pM2 = io2\<close>, of M] by auto
qed


lemma observable_language_target_failure :
  assumes "observable M"
  and     "q \<in> io_targets M io1 (initial M)"
  and     "t \<in> io_targets T io1 (initial T)"
  and     "\<not> LS T t \<subseteq> LS M q"
shows "\<not> L T \<subseteq> L M"
  using observable_language_target[OF assms(1,2,3)] assms(4) by blast
    



subsection \<open>Conformity Relations\<close>

fun is_io_reduction_state :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd \<Rightarrow> bool" where
  "is_io_reduction_state A a B b = (LS A a \<subseteq> LS B b)"

abbreviation(input) "is_io_reduction A B \<equiv> is_io_reduction_state A (initial A) B (initial B)" 
notation 
  is_io_reduction ("_ \<preceq> _")


fun is_io_reduction_state_on_inputs :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'b list set \<Rightarrow> ('d,'b,'c) fsm \<Rightarrow> 'd \<Rightarrow> bool" where
  "is_io_reduction_state_on_inputs A a U B b = (LS\<^sub>i\<^sub>n A a U \<subseteq> LS\<^sub>i\<^sub>n B b U)"

abbreviation(input) "is_io_reduction_on_inputs A U B \<equiv> is_io_reduction_state_on_inputs A (initial A) U B (initial B)" 
notation 
  is_io_reduction_on_inputs ("_ \<preceq>\<lbrakk>_\<rbrakk> _")



subsection \<open>Submachines\<close>

fun is_submachine :: "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where 
  "is_submachine A B = (initial A = initial B \<and> transitions A \<subseteq> transitions B \<and> inputs A = inputs B \<and> outputs A = outputs B \<and> nodes A \<subseteq> nodes B)"
  

lemma submachine_path_initial :
  assumes "is_submachine A B"
  and     "path A (initial A) p"
shows "path B (initial B) p"
  using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a p)
  then show ?case
    by fastforce
qed
   

lemma submachine_path :
  assumes "is_submachine A B"
  and     "path A q p"
shows "path B q p"
  by (meson assms(1) assms(2) is_submachine.elims(2) path_begin_node subsetD transition_subset_path)
  




lemma submachine_reduction : 
  assumes "is_submachine A B"
  shows "is_io_reduction A B"
  using submachine_path[OF assms] assms by auto 

lemma complete_submachine_initial :
  assumes "is_submachine A B"
      and "completely_specified A"
  shows "completely_specified_state B (initial B)"
  using assms(1) assms(2) fsm_initial subset_iff by fastforce




lemma submachine_language :
  assumes "is_submachine S M"
  shows "L S \<subseteq> L M"
  by (meson assms is_io_reduction_state.elims(2) submachine_reduction)

lemma submachine_observable :
  assumes "is_submachine S M"
  and     "observable M"
shows "observable S"
  using assms unfolding is_submachine.simps observable.simps by blast






lemma submachine_transitive :
  assumes "is_submachine S M"
  and     "is_submachine S' S"
shows "is_submachine S' M"
  using assms unfolding is_submachine.simps by force

lemma transitions_subset_path :
  assumes "set p \<subseteq> transitions M"
  and     "p \<noteq> []"
  and     "path S q p"
shows "path M q p"
  using assms by (induction p arbitrary: q; auto)



lemma transition_subset_paths :
  assumes "transitions S \<subseteq> transitions M"
  and "initial S \<in> nodes M"
  and "inputs S = inputs M"
  and "outputs S = outputs M"
  and "path S (initial S) p"
shows "path M (initial S) p"
  using assms(5) proof (induction p rule: rev_induct)
case Nil
  then show ?case using assms(2) by auto
next
  case (snoc t p)
  then have "path S (initial S) p" 
        and "t \<in> transitions S" 
        and "t_source t = target (initial S) p" 
        and "path M (initial S) p"
    by auto

  have "t \<in> transitions M"
    using assms(1) \<open>t \<in> transitions S\<close> by auto
  moreover have "t_source t \<in> nodes M"
    using \<open>t_source t = target (initial S) p\<close> \<open>path M (initial S) p\<close>
    using path_target_is_node by fastforce 
  ultimately have "t \<in> transitions M"
    using \<open>t \<in> transitions S\<close> assms(3,4) by auto
  then show ?case
    using \<open>path M (initial S) p\<close>
    using snoc.prems by auto 
qed 







subsection \<open>Changing Initial States\<close>

lift_definition from_FSM :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> ('a,'b,'c) fsm" is FSM_Impl.from_FSM
  by simp 

lemma from_FSM_simps[simp]:
  assumes "q \<in> nodes M"
  shows
  "initial (from_FSM M q) = q"  
  "inputs (from_FSM M q) = inputs M"
  "outputs (from_FSM M q) = outputs M"
  "transitions (from_FSM M q) = transitions M"
  "nodes (from_FSM M q) = nodes M" using assms by (transfer; simp)+





lemma from_FSM_path_initial :
  assumes "q \<in> nodes M"
  shows "path M q p = path (from_FSM M q) (initial (from_FSM M q)) p"
  by (metis assms from_FSM_simps(1) from_FSM_simps(4) from_FSM_simps(5) order_refl transition_subset_path)

lemma from_FSM_path :
  assumes "q \<in> nodes M"
      and "path (from_FSM M q) q' p"
    shows "path M q' p"
  using assms(1) assms(2) path_transitions transitions_subset_path by fastforce

lemma from_FSM_reachable_nodes :
  assumes "q \<in> reachable_nodes M"
  shows "reachable_nodes (from_FSM M q) \<subseteq> reachable_nodes M"
proof
  from assms obtain p where "path M (initial M) p" and "target (initial M) p = q"
    unfolding reachable_nodes_def by blast
  then have "q \<in> nodes M"
    by (meson path_target_is_node)

  fix q' assume "q' \<in> reachable_nodes (from_FSM M q)"
  then obtain p' where "path (from_FSM M q) q p'" and "target q p' = q'"
    unfolding reachable_nodes_def from_FSM_simps[OF \<open>q \<in> nodes M\<close>] by blast
  then have "path M (initial M) (p@p')" and "target (initial M) (p@p') = q'"
    using from_FSM_path[OF \<open>q \<in> nodes M\<close> ] \<open>path M (initial M) p\<close>
    using \<open>target (FSM.initial M) p = q\<close> by auto

  then show "q' \<in> reachable_nodes M"
    unfolding reachable_nodes_def by blast
qed
  
   


lemma submachine_from :
  assumes "is_submachine S M"
      and "q \<in> nodes S"
  shows "is_submachine (from_FSM S q) (from_FSM M q)"
proof -
  have "path S q []"
    using assms(2) by blast
  then have "path M q []"
    by (meson assms(1) submachine_path)
  then show ?thesis
    using assms(1) assms(2) by force
qed




lemma from_FSM_path_rev_initial :
  assumes "path M q p"
  shows "path (from_FSM M q) q p"
  by (metis (no_types) assms from_FSM_path_initial from_FSM_simps(1) path_begin_node)


lemma from_from[simp] :  
  assumes "q1 \<in> nodes M"
  and     "q1' \<in> nodes M"
shows "from_FSM (from_FSM M q1) q1' = from_FSM M q1'" (is "?M = ?M'") 
proof -
  have *: "q1' \<in> nodes (from_FSM M q1)"
    using assms(2) unfolding from_FSM_simps(5)[OF assms(1)] by assumption
  
  have "initial ?M = initial ?M'"
  and  "nodes ?M = nodes ?M'"
  and  "inputs ?M = inputs ?M'"
  and  "outputs ?M = outputs ?M'"
  and  "transitions ?M = transitions ?M'"
    unfolding  from_FSM_simps[OF *] from_FSM_simps[OF assms(1)] from_FSM_simps[OF assms(2)] by simp+

  then show ?thesis apply transfer by force
qed

end (*
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
  assumes "observable M"
  and     "q \<in> nodes M"
shows "observable (from_FSM M q)"
  using from_FSM_h[OF assms(2)] assms(1) unfolding observable.simps by blast


lemma observable_language_next :
  assumes "io#ios \<in> LS M (t_source t)"
  and     "observable M"
  and     "t \<in> transitions M"
  and     "t_input t = fst io"
  and     "t_output t = snd io"
shows "ios \<in> L (from_FSM M (t_target t))"
proof -
  obtain p where "path M (t_source t) p" and "p_io p = io#ios"
    using assms(1)
  proof -
    assume a1: "\<And>p. \<lbrakk>path M (t_source t) p; p_io p = io # ios\<rbrakk> \<Longrightarrow> thesis"
    obtain pps :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> 'a FSM \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
      "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (pps x0 x1 x2) \<and> path x2 x1 (pps x0 x1 x2))"
      by moura
    then have "\<exists>ps. path M (t_source t) ps \<and> p_io ps = io # ios"
      using assms(1) by auto
    then show ?thesis
      using a1 by meson
  qed 
  then obtain t' p' where "p = t' # p'"
    by auto
  then have "t' \<in> transitions M" and "t_source t' = t_source t" and "t_input t' = fst io" and "t_output t' = snd io" 
    using \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "t = t'"
    using assms(2,3,4,5) unfolding observable.simps
    by (metis (no_types, hide_lams) prod.expand) 

  then have "path M (t_target t) p'" and "p_io p' = ios"
    using \<open>p = t' # p'\<close> \<open>path M (t_source t) p\<close> \<open>p_io p = io#ios\<close> by auto
  then have "path (from_FSM M (t_target t)) (initial (from_FSM M (t_target t))) p'"
    using from_FSM_path_initial[OF wf_transition_target[OF \<open>t \<in> transitions M\<close>]] by auto

  then show ?thesis using \<open>p_io p' = ios\<close> by auto
qed

lemma from_FSM_language :
  assumes "q \<in> nodes M"
  shows "L (from_FSM M q) = LS M q"
  using from_FSM_path_initial[OF assms] unfolding LS.simps by blast


lemma language_state_prepend_transition : 
  assumes "io \<in> LS (from_FSM A (t_target t)) (initial (from_FSM A (t_target t)))"
  and     "t \<in> transitions A"
shows "p_io [t] @ io \<in> LS A (t_source t)" 
proof -
  obtain p where "path (from_FSM A (t_target t)) (initial (from_FSM A (t_target t))) p"
           and   "p_io p = io"
    using assms(1) unfolding LS.simps by blast
  then have "path A (t_target t) p"
    using from_FSM_path_initial[OF wf_transition_target[OF assms(2)]] by auto
  then have "path A (t_source t) (t # p)"
    using assms(2) by auto
  then show ?thesis 
    using \<open>p_io p = io\<close> unfolding LS.simps
    by force 
qed


subsection \<open>Filtering Transitions\<close>

lemma transition_filter_path_initial :
  assumes "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) p"
  shows "path M (initial M) p"
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc t p)
  then have "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)" by auto
  then have "t \<in> set (filter f (transitions M))" by auto
  then have "t \<in> transitions M" by auto

  have "target p (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = t_source t"
    using snoc.prems by auto
  then have "target (initial M) p = t_source t" by auto
  moreover have "path M (initial M) p" using snoc.prems snoc.IH by auto
  ultimately have "t_source t \<in> nodes M"
    using path_target_is_node by metis
  then have "t \<in> transitions M"
    using \<open>t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)\<close> by auto
  then show "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p\<close> \<open>target (initial M) p = t_source t\<close> by auto
qed

lemma transition_filter_path :
  assumes "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) q p"
  shows "path M q p"
proof -
  have "q \<in> nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>)"
    using assms path_begin_node by metis
  then obtain pQ where "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) pQ"
                   and "target pQ (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = q"
    by (metis path_to_node)
  then have "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) (pQ@p)"
    using assms path_append by metis
  then have "path M (initial M) (pQ@p)"
    using transition_filter_path_initial by auto
  then show "path M q p"
    using \<open>target pQ (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) = q\<close> by auto
qed

lemma transition_filter_path_initial_rev :
  assumes "path M (initial M) p" 
      and "list_all f p"
    shows "path (M\<lparr> transitions := filter f (transitions M)\<rparr>) (initial (M\<lparr> transitions := filter f (transitions M)\<rparr>)) p"
          (is "path ?M (initial ?M) p")
using assms proof (induction p rule: rev_induct)
  case Nil
  then show ?case by blast 
next
  case (snoc t p)
  then have "path ?M (initial ?M) p" and "f t" by auto

  have "target p (initial ?M) = t_source t" using snoc.prems(1) by auto
  then have "t_source t \<in> nodes ?M"
    using path_target_is_node[OF \<open>path ?M (initial ?M) p\<close>] by auto

  have "t \<in> transitions M" using snoc.prems(1) by auto
  then have "t \<in> h ?M"
    using \<open>f t\<close> \<open>t_source t \<in> nodes ?M\<close> by auto

  show ?case
    using \<open>path ?M (initial ?M) p\<close> \<open>target p (initial ?M) = t_source t\<close> \<open>t \<in> h ?M\<close> by auto
qed

lemma transition_filter_h :
  assumes "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)"  (is "t \<in> h ?M")
  shows "t \<in> transitions M" and "f t"
proof -
  from assms have "t_source t \<in> nodes ?M" by auto
  then obtain p where "path ?M (initial ?M) p"
                  and "target p (initial ?M) = t_source t"
    by (metis path_to_node)
  then have "path M (initial M) p"
    by (metis transition_filter_path_initial)
  have "t_source t \<in> nodes M"
    using path_target_is_node[OF \<open>path M (initial M) p\<close>] \<open>target p (initial ?M) = t_source t\<close> by auto
  then show "t \<in> transitions M"
    using \<open>t \<in> h ?M\<close> by auto
  from assms show "f t" by auto
qed

lemma transition_filter_nodes :
  "nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>) \<subseteq> nodes M" (is "nodes ?M \<subseteq> nodes M")
proof 
  fix q assume "q \<in> nodes ?M"
  then obtain p where "path ?M (initial ?M) p" 
                  and "target p (initial ?M) = q"
    by (metis path_to_node)
  then have "path M (initial M) p"
    using transition_filter_path_initial by metis
  show "q \<in> nodes M"
    using path_target_is_node[OF \<open>path M (initial M) p\<close>] \<open>target p (initial ?M) = q\<close> by auto
qed


lemma transition_filter_state_transitions :
  assumes "t_source t \<in> nodes (M\<lparr> transitions := filter f (transitions M)\<rparr>)"
      and "t \<in> transitions M"
      and "f t"
    shows "t \<in> h (M\<lparr> transitions := filter f (transitions M)\<rparr>)" (is "t \<in> h ?M")
  using assms by auto

lemma transition_filter_submachine :
  "is_submachine (M\<lparr> transitions := filter f (transitions M)\<rparr>) M" 
proof -
  let ?M = "(M\<lparr> transitions := filter f (transitions M)\<rparr>)"
  have "set (transitions ?M) \<subseteq> transitions M"
    by auto
  then have "h ?M \<subseteq> transitions M" unfolding wf_transitions.simps
  proof -
    have "\<forall>ps P. \<exists>p. (set ps \<subseteq> P \<or> (p::'a \<times> integer \<times> integer \<times> 'a) \<in> set ps) \<and> (p \<notin> P \<or> set ps \<subseteq> P)"
      by (meson subset_code(1))
    then obtain pp :: "('a \<times> integer \<times> integer \<times> 'a) list \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) set \<Rightarrow> 'a \<times> integer \<times> integer \<times> 'a" where
      f1: "\<And>ps P. (set ps \<subseteq> P \<or> pp ps P \<in> set ps) \<and> (pp ps P \<notin> P \<or> set ps \<subseteq> P)"
      by metis
    moreover
    { assume "pp (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) (set (wf_transitions M)) \<notin> set (wf_transitions M)"
      then have "pp (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) (set (wf_transitions M)) \<notin> set (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>))"
        by (metis transition_filter_h(1))
      then have "set (wf_transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>)) \<subseteq> set (filter (\<lambda>p. t_source p \<in> nodes M \<and> t_input p \<in> set (inputs M) \<and> t_output p \<in> set (outputs M)) (transitions M))"
        using f1 by (metis (no_types) wf_transitions.elims) }
    ultimately show "set (filter (\<lambda>p. t_source p \<in> nodes (M\<lparr>transitions := filter f (transitions M)\<rparr>) \<and> t_input p \<in> set (inputs (M\<lparr>transitions := filter f (transitions M)\<rparr>)) \<and> t_output p \<in> set (outputs (M\<lparr>transitions := filter f (transitions M)\<rparr>))) (transitions (M\<lparr>transitions := filter f (transitions M)\<rparr>))) \<subseteq> set (filter (\<lambda>p. t_source p \<in> nodes M \<and> t_input p \<in> set (inputs M) \<and> t_output p \<in> set (outputs M)) (transitions M))"
      by (metis (no_types) wf_transitions.elims)
  qed
     
  then show ?thesis unfolding is_submachine.simps by auto
qed



lemma h_equality :
  assumes "initial A = initial B"
      and "inputs A = inputs B"
      and "outputs A = outputs B"
      and "set (transitions A) = set (transitions B)"
    shows "h A = transitions B"
proof -
  have "\<And> p . path A (initial A) p = path B (initial B) p"
  proof -
    fix p 
    show "path A (initial A) p = path B (initial B) p"
      using assms proof (induction p rule: rev_induct)
      case Nil
      then show ?case
        by blast 
    next
      case (snoc t p)
      then have "path A (initial A) p = path B (initial B) p" by auto
      then show ?case using assms
        by (metis path_append_elim path_cons_elim path_equivalence_by_h path_target_is_node wf_transition_simp) 
    qed
  qed
  then have "nodes A = nodes B"
    using path_to_node
    by (metis assms(1) path_target_is_node subsetI subset_antisym) 
  then show "h A = transitions B"
    using assms(2-4) by auto
qed
    
  
lemma h_equality' :
  assumes "initial A = initial B"
      and "inputs A = inputs B"
      and "outputs A = outputs B"
      and "h A = set (transitions B)"
    shows "h A = transitions B"
proof -
  have "\<And> p . path A (initial A) p = path B (initial B) p"
  proof -
    fix p 
    show "path A (initial A) p = path B (initial B) p"
      using assms proof (induction p rule: rev_induct)
      case Nil
      then show ?case
        by blast 
    next
      case (snoc t p)
      then have "path A (initial A) p = path B (initial B) p" by auto
      then show ?case using assms
        by (metis path_append_elim path_cons_elim path_equivalence_by_h path_target_is_node wf_transition_simp) 
    qed
  qed
  then have "nodes A = nodes B"
    using path_to_node
    by (metis assms(1) path_target_is_node subsetI subset_antisym) 
  then show "h A = transitions B"
    using assms(2-4) by auto
qed



fun trim_transitions :: "'a FSM \<Rightarrow> 'a FSM" where
  "trim_transitions M = M\<lparr> transitions := wf_transitions M\<rparr>"

lemma trim_transitions_simps[simp]:
    "initial (trim_transitions M) = initial M"
    "inputs (trim_transitions M) = inputs M" 
    "outputs (trim_transitions M) = outputs M"
    "h (trim_transitions M) = transitions M"
proof -
  show "initial (trim_transitions M) = initial M" by auto
  moreover show "inputs (trim_transitions M) = inputs M" by auto
  moreover show "outputs (trim_transitions M) = outputs M" by auto
  ultimately have "initial M = initial (trim_transitions M)"
    and "inputs M = inputs (trim_transitions M)"
    and "outputs M = outputs (trim_transitions M)"
    and "set (wf_transitions M) = set (transitions (trim_transitions M))" by auto
  
  then show "h (trim_transitions M) = transitions M" using h_equality'[of M "trim_transitions M"] by presburger
qed

lemma trim_transitions_paths : "path M q p = path (trim_transitions M) q p"
  by (metis eq_iff h_equivalence_path h_subset_path_non_initial nodes.simps trim_transitions_simps(1) trim_transitions_simps(4))

lemma trim_transitions_paths_initial : "path M (initial M) p = path (trim_transitions M) (initial (trim_transitions M)) p"
  by (metis trim_transitions_paths trim_transitions_simps(1))

lemma trim_transitions_language : "L M = L (trim_transitions M)"
  using trim_transitions_paths_initial unfolding LS.simps by blast
  
lemma trim_transitions_nodes : "nodes M = nodes (trim_transitions M)"
  using h_nodes[of M] h_nodes[of "trim_transitions M"] trim_transitions_simps(1)[of M] trim_transitions_simps(4)[of M] by presburger

lemma trim_transitions_submachine : "is_submachine S M \<Longrightarrow> is_submachine (trim_transitions S) M"
  unfolding trim_transitions.simps is_submachine.simps by auto

lemma trim_transitions_single_input : "single_input S \<Longrightarrow> single_input (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_simps(4)[of S] unfolding trim_transitions.simps single_input.simps by blast

lemma trim_transitions_acyclic : "acyclic S \<Longrightarrow> acyclic (trim_transitions S)"
  using trim_transitions_paths[of S]  unfolding trim_transitions.simps acyclic.simps by simp

lemma trim_transitions_deadlock_state_nodes : "deadlock_state S q = deadlock_state (trim_transitions S) q"
  by (metis deadlock_state.simps trim_transitions_simps(4))

lemma trim_transitions_t_source' : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes S"
  unfolding trim_transitions.simps by auto

lemma trim_transitions_t_source : "t \<in> set (transitions (trim_transitions S)) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_nodes[of S] trim_transitions_t_source'[of t S] by blast

lemma trim_transitions_t_source_h : "t \<in> h (trim_transitions S) \<Longrightarrow> t_source t \<in> nodes (trim_transitions S)"
  using trim_transitions_t_source[of t S] unfolding wf_transitions.simps by auto

lemma trim_transitions_transitions : "h (trim_transitions S) = set (transitions (trim_transitions S))"
  unfolding trim_transitions.simps 
proof -
  show "set (wf_transitions (S\<lparr>transitions := wf_transitions S\<rparr>)) = set (transitions (S\<lparr>transitions := wf_transitions S\<rparr>))"
    by (metis (no_types) select_convs(4) surjective trim_transitions.simps trim_transitions_simps(4) update_convs(4))
qed  

lemma transitions_reorder :  
  assumes     "initial S' = initial S"
  and     "inputs S' = inputs S"
  and     "outputs S' = outputs S"
  and     "set (transitions S') = transitions S"
shows "h S' = h S"
  and "path S' q p = path S q p"
  and "nodes S' = nodes S"
proof-
  show "h S' = h S"
    using h_equality[OF assms] by assumption

  show "path S' q p = path S q p"
    by (metis \<open>h S' = h S\<close> assms(1) h_subset_path h_subset_path_non_initial nodes.initial order_refl)
    
  show "nodes S' = nodes S"
  proof -
    have "insert (initial S') {t_target p |p. p \<in> set (wf_transitions S)} = nodes S"
      by (metis (no_types) assms(1) h_nodes)
    then show ?thesis
      by (meson \<open>set (wf_transitions S') = set (wf_transitions S)\<close> assms(1) nodes_paths_by_same_h_initial(1))
  qed
qed

subsection \<open>Further Reachability Formalisations\<close>

(* nodes that are reachable in at most k transitions *)
fun reachable_k :: "'a FSM \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set" where
  "reachable_k M q n = {target p q | p . path M q p \<and> length p \<le> n}" 


lemma reachable_k_0_initial : "reachable_k M (initial M) 0 = {initial M}" 
  by auto

lemma reachable_k_nodes : "nodes M = reachable_k M (initial M) ( size M - 1)"
proof -
  have "\<And>q. q \<in> nodes M \<Longrightarrow> q \<in> reachable_k M (initial M) ( size M - 1)"
  proof -
    fix q assume "q \<in> nodes M"
    then obtain p where "path M (initial M) p" and "target (initial M) p = q"
      by (metis path_to_node) 
    then obtain p' where "path M (initial M) p'"
                     and "target p' (initial M) = target (initial M) p" 
                     and "length p' < size M"
      using distinct_path_length_limit_nodes[of "M" "initial M" p]
      using distinct_path_length[of M "initial M" p] by auto
    then show "q \<in> reachable_k M (initial M) ( size M - 1)"
      using \<open>target (initial M) p = q\<close> list.size(3) mem_Collect_eq not_less_eq_eq reachable_k.simps by auto
  qed

  moreover have "\<And>x. x \<in> reachable_k M (initial M) ( size M - 1) \<Longrightarrow> x \<in> nodes M"
    using nodes_path_initial by auto
  
  ultimately show ?thesis by blast
qed


subsection \<open>Generating Submachines\<close>

lemma nodes_from_transition_targets :
  "nodes M \<subseteq> insert (initial M) (set (map t_target (transitions M)))"
proof -
  have "nodes M \<subseteq> insert (initial M) (set (map t_target (wf_transitions M)))"
    using image_iff nodes_initial_or_target by fastforce
  moreover have "(set (map t_target (wf_transitions M))) \<subseteq> (set (map t_target (transitions M)))"
    by auto
  ultimately show ?thesis by blast
qed


lemma submachine_by_transitions :
  assumes "set ts \<subseteq> transitions M"
  shows "is_submachine (M\<lparr> transitions := ts \<rparr>) M"
proof -
  let ?M = "(M\<lparr> transitions := ts \<rparr>)"
  let ?MF = "M\<lparr> transitions := filter (\<lambda> t . t \<in> set ts) (transitions M) \<rparr>"
  
  have "set (transitions ?M) = set (transitions ?MF)"
    using assms by auto
  have "h ?M = h ?MF"
    using h_equality[OF _ _ _ \<open>set (transitions ?M) = set (transitions ?MF)\<close>] by auto
  moreover have "is_submachine ?MF M"
    using transition_filter_submachine by metis
  ultimately show ?thesis by auto
qed

subsubsection \<open>Generate all Submachines up to h-Equivalence\<close> 

fun generate_submachine :: "'a FSM \<Rightarrow> bool list \<Rightarrow> 'a FSM" where
  "generate_submachine M bs = M\<lparr> transitions := map fst (filter snd (zip (transitions M) bs)) \<rparr>"

lemma generate_submachine_is_submachine : "is_submachine (generate_submachine M bs) M" 
proof -
  have "\<And> x . x \<in> set (map fst (filter snd (zip (transitions M) bs))) \<Longrightarrow> x \<in> transitions M"
    by (metis (no_types, lifting) filter_eq_nths in_set_takeD map_fst_zip_take notin_set_nthsI nths_map)
  then show ?thesis  
    using generate_submachine.simps by (metis submachine_by_transitions subsetI) 
qed

fun generate_submachines :: "'a FSM \<Rightarrow> 'a FSM list" where
  "generate_submachines M = map (generate_submachine M) (generate_selector_lists (length (transitions M)))"

lemma generate_submachines_containment :
  assumes "is_submachine S M"
  shows "\<exists> S' \<in> set (generate_submachines M) . (h S = h S')"
proof -
  let ?ts = "filter (\<lambda> t . t \<in> transitions S) (transitions M)"
  have "h S \<subseteq> transitions M" using assms by auto
  then have "h S = set ?ts" by auto
  
  have "set ?ts \<subseteq> transitions M" by auto
  then obtain bs where "length bs = length (transitions M)"  and "set ?ts = set (map fst (filter snd (zip (transitions M) bs)))"
    using selector_list_ex[of "?ts" "transitions M"] by blast
  then have "bs \<in> set (generate_selector_lists (length (transitions M)))"
    using generate_selector_lists_set[of "length (transitions M)"] by blast
  then have *: "generate_submachine M bs \<in> set (generate_submachines M)" 
    by auto
  
  have "set ?ts = set (transitions (generate_submachine M bs))"
    using \<open>set ?ts = set (map fst (filter snd (zip (transitions M) bs)))\<close> unfolding generate_submachine.simps by auto
  then have "h S = set (transitions (generate_submachine M bs))"
    using \<open>h S = set ?ts\<close> by auto

  have **: "h S = h (generate_submachine M bs)"
    using h_equality'[OF _ _ _ \<open>h S = set (transitions (generate_submachine M bs))\<close>] assms by auto

  show ?thesis using * ** by blast
qed

lemma generate_submachines_are_submachines :
  assumes "S \<in> set (generate_submachines M)"
  shows "is_submachine S M"
  using assms generate_submachine_is_submachine[of M] unfolding generate_submachines.simps by fastforce

value "generate_submachines M_ex"





subsubsection \<open>Generate all Single-Input Submachines up to h-Equivalence\<close> 

fun generate_submachine_from_assignment :: "'a FSM \<Rightarrow> ('a \<times> Input option) list \<Rightarrow> 'a FSM" where
  "generate_submachine_from_assignment M assn = M\<lparr> transitions := filter (\<lambda> t . (t_source t, Some (t_input t)) \<in> set assn) (wf_transitions M)\<rparr>"

lemma generate_submachine_for_contained_assn: "assn \<in> set assns \<Longrightarrow> generate_submachine_from_assignment CSep assn \<in> set (map (\<lambda> assn . generate_submachine_from_assignment CSep assn) assns)"
  by simp

  
subsubsection \<open>Induction Schemes\<close>





lemma acyclic_induction [consumes 1, case_names node]:
  assumes "acyclic M"
      and "\<And> q . q \<in> nodes M \<Longrightarrow> (\<And> t . t \<in> transitions M \<Longrightarrow> ((t_source t = q) \<Longrightarrow> P (t_target t))) \<Longrightarrow> P q"
    shows "\<forall> q \<in> nodes M . P q"
proof 
  fix q assume "q \<in> nodes M"

  let ?k = "Max (image length {p . path M q p})"
  have "finite {p . path M q p}" using acyclic_finite_paths[OF assms(1)] by auto
  then have k_prop: "(\<forall> p . path M q p \<longrightarrow> length p \<le> ?k)" by auto

  moreover have "\<And> q k . q \<in> nodes M \<Longrightarrow> (\<forall> p . path M q p \<longrightarrow> length p \<le> k) \<Longrightarrow> P q"
  proof -
    fix q k assume "q \<in> nodes M" and "(\<forall> p . path M q p \<longrightarrow> length p \<le> k)"
    then show "P q" 
    proof (induction k arbitrary: q)
      case 0
      then have "{p . path M q p} = {[]}" by blast 
      then have "LS M q \<subseteq> {[]}" unfolding LS.simps by blast
      then have "deadlock_state M q" using deadlock_state_alt_def by metis
      then show ?case using assms(2)[OF \<open>q \<in> nodes M\<close>] unfolding deadlock_state.simps by blast
    next
      case (Suc k)
      have "\<And> t . t \<in> transitions M \<Longrightarrow> (t_source t = q) \<Longrightarrow> P (t_target t)"
      proof -
        fix t assume "t \<in> transitions M" and "t_source t = q" 
        then have "t_target t \<in> nodes M"
          using wf_transition_target by metis
        moreover have "\<forall>p. path M (t_target t) p \<longrightarrow> length p \<le> k"
          using Suc.prems(2) \<open>t \<in> set (wf_transitions M)\<close> \<open>t_source t = q\<close> by auto
        ultimately show "P (t_target t)" 
          using Suc.IH by auto
      qed
      then show ?case using assms(2)[OF Suc.prems(1)] by blast
    qed
  qed

  ultimately show "P q" using \<open>q \<in> nodes M\<close> by blast
qed



subsection \<open>Further Path Enumeration Algorithms\<close>

fun paths_for_input :: "'a FSM \<Rightarrow> 'a \<Rightarrow> Input list \<Rightarrow> 'a Transition list list" where
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

  have *: "{p . path M q p \<and> map t_input p = x#xs} = {t#p | t p . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
  proof -
    have "\<And> p . p \<in> {p . path M q p \<and> map t_input p = x#xs} \<Longrightarrow> p \<in> {t#p | t p . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"    
      using Collect_cong Cons_eq_map_D[of x xs t_input] list.simps(9)[of t_input] by blast
    moreover have "\<And> p . p \<in> {t#p | t p . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}} \<Longrightarrow> p \<in> {p . path M q p \<and> map t_input p = x#xs}"
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
    then obtain t where "t \<in> transitions M" and "t_source t = q \<and> t_input t = x" and "t_output t = y"
                    and "p \<in> set (map (\<lambda> p . t#p) (paths_for_input M (t_target t) xs))"
      by force
    then obtain p' where "p = t#p'"
                     and "p' \<in> set (paths_for_input M (t_target t) xs)"
      by force

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> transitions M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      using \<open>p' \<in> set (paths_for_input M (t_target t) xs)\<close> by blast
  
    then have "(t#p') \<in> {t#p | t p . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using \<open>t \<in> transitions M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by blast
    then show "p \<in> {p . path M q p \<and> map t_input p = x#xs}" 
      using \<open>p = t#p'\<close> * by blast
  qed
  moreover have "{p . path M q p \<and> map t_input p = x#xs} \<subseteq> set (paths_for_input M q (x#xs))"
  proof 
    fix p assume "p \<in> {p . path M q p \<and> map t_input p = x#xs}"
    then have "p \<in> {t#p | t p . t \<in> transitions M \<and> t_source t = q \<and> t_input t = x \<and> p \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}}"
      using * by blast
    then obtain t p' where "p = t#p'" and "t \<in> transitions M" and "t_source t = q \<and> t_input t = x" and "p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}"
      by blast

    have "t_target t \<in> nodes M"
      using wf_transition_target \<open>t \<in> transitions M\<close> by metis
    then have "set (paths_for_input M (t_target t) xs) = {p. path M (t_target t) p \<and> map t_input p = xs}"
      using Cons.IH by auto
    then have "p' \<in> set (paths_for_input M (t_target t) xs)" 
      using \<open>p' \<in> {p' . path M (t_target t) p' \<and> map t_input p' = xs}\<close> by blast
    moreover have "t_output t \<in> set (outputs M)" 
      using \<open>t \<in> transitions M\<close> by auto
    ultimately have "t#p' \<in> set (paths_for_input M q (x#xs))"
      unfolding paths_for_input.simps 
      using \<open>t \<in> transitions M\<close> \<open>t_source t = q \<and> t_input t = x\<close> by force
    then show "p \<in> set (paths_for_input M q (x#xs))"
      using \<open>p = t#p'\<close> by blast
  qed
  
  ultimately show ?case ..
qed





fun paths_up_to_length_or_condition :: "'a FSM \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a Transition list \<Rightarrow> bool) \<Rightarrow> 'a Transition list \<Rightarrow> 'a Transition list list" where
  "paths_up_to_length_or_condition M q 0 f pref = (if f pref
    then [pref]
    else [])" | 
  "paths_up_to_length_or_condition M q (Suc k) f pref = (if f pref
    then [pref]
    else (concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
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
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    also have "\<dots> = \<Union>{set (paths_up_to_length_or_condition M q k f (pref@[t])) | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by force
    

    have *: "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = target pref q \<Longrightarrow> set (paths_up_to_length_or_condition M q k f (pref@[t])) 
                                                            =  {((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
    proof -
      fix t :: "'a \<times> integer \<times> integer \<times> 'a"
      assume a1: "t_source t = target pref q"
      assume "t \<in> set (wf_transitions M)"
      then have "path M (t_source t) [t]"
        by blast
      then show "set (paths_up_to_length_or_condition M q k f (pref @ [t])) = {(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))}"
        using a1 by (simp add: Suc.IH Suc.prems path_append)
    qed

    

    from False have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    moreover have "\<dots> = \<Union>{set (paths_up_to_length_or_condition M q k f (pref@[t])) | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by force
    moreover have "\<dots> = \<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      using * by (metis (no_types, lifting))
    ultimately have "set (paths_up_to_length_or_condition M q (Suc k) f pref) = \<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by simp
    moreover have "\<Union>{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> transitions M \<and> t_source t = target pref q}
                  = {(pref@p) | p . path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
    proof -
      let ?UN = "{{((pref @ [t]) @ p) |p .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      let ?UN' = "{((pref @ [t]) @ p) |p t.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"

      have **: "\<And> p t . path M q ((pref @ [t]) @ p) \<Longrightarrow> t \<in> transitions M \<and> t_source t = target pref q"
        by auto
      
      have "\<Union>?UN = ?UN'"
      proof -
        have "\<Union>?UN \<subseteq> ?UN'"
        proof 
          fix p assume "p \<in> \<Union>?UN"
          then obtain P where "p \<in> P" and "P \<in> ?UN"
            by (meson UnionE)
            
          then obtain t where "t \<in> transitions M \<and> t_source t = target pref q"
                          and "P = {((pref @ [t]) @ p) |p .
                                     path M q ((pref @ [t]) @ p) \<and>
                                     length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}"
            by auto
          then obtain p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))"
            using \<open>p \<in> P\<close>
          proof -
            assume a1: "\<And>p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps. p = (pref @ [t]) @ ps \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))"
              using \<open>P = {(pref @ [t]) @ p |p. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> \<open>p \<in> P\<close> by force
            then show ?thesis
              using a1 by moura
          qed

          show "p \<in> ?UN'"
            using \<open>length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<close> \<open>p = (pref @ [t]) @ p'\<close> \<open>path M q ((pref @ [t]) @ p')\<close> by fastforce
        qed

        moreover have "?UN' \<subseteq> \<Union>?UN"
        proof 
          fix p assume "p \<in> ?UN'"
          then obtain t p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))"
          proof -
          assume a1: "\<And>t p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p''))\<rbrakk> \<Longrightarrow> thesis"
          have "\<exists>ps pa. p = (pref @ [pa]) @ ps \<and> path M q ((pref @ [pa]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [pa]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [pa]) @ psa))"
            using \<open>p \<in> {(pref @ [t]) @ p |p t. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> by force
            then show ?thesis
              using a1 by (metis (no_types))
          qed 
          then have "p \<in> {(pref @ [t]) @ p |p.
                      path M q ((pref @ [t]) @ p) \<and>
                      length p \<le> k \<and>
                      f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}" 
            by auto
          then show "p \<in> \<Union>?UN"
            using **[OF \<open> path M q ((pref @ [t]) @ p')\<close>]
          proof -
          have f1: "\<exists>ps. p = (pref @ [t]) @ ps \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))"
          using \<open>p \<in> {(pref @ [t]) @ p |p. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))}\<close> by force
            have f2: "{(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))} \<in> {{(pref @ [p]) @ ps |ps. path M q ((pref @ [p]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [p]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [p]) @ psa))} | p. p \<in> set (wf_transitions M) \<and> t_source p = target pref q}"
              using \<open>t \<in> set (wf_transitions M) \<and> t_source t = target pref q\<close> by blast
            have "p \<in> {(pref @ [t]) @ ps |ps. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ psa))}"
              using f1 by fastforce
            then show ?thesis
              using f2 by (meson Union_iff)
          qed 
        qed
        
        ultimately show ?thesis by blast
      qed



      let ?UN'' = "{((pref @ [t]) @ p) |p t.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))}"
      have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p')) \<Longrightarrow> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))"
        using False by (metis (no_types, hide_lams) append.assoc append_Nil append_Nil2 append_eq_Cons_conv) 
      moreover have "\<And> t p . (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p')) \<Longrightarrow> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p'))"
        using False by (metis (no_types, hide_lams) append.assoc append_Nil append_eq_Cons_conv)
      ultimately have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f ((pref @ [t]) @ p')) = (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))"
        by auto
      then have "?UN' = ?UN''" by auto
      

      let ?P = "{(pref@p) | p . path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f (pref@p'))}"
      have "?UN'' = ?P"
      proof -
        have "?UN'' \<subseteq> ?P" 
        proof 
          fix p assume "p \<in> ?UN''"
          then obtain t p' where "p = (pref @ [t]) @ p'" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') \<and>
                 (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
          proof -
            assume a1: "\<And>t p'. \<lbrakk>p = (pref @ [t]) @ p'; path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') \<and> (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps pa. p = (pref @ [pa]) @ ps \<and> path M q ((pref @ [pa]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [pa]) @ ps) \<and> (\<forall>psa psb. pa # ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> \<not> f (pref @ psa))"
              using \<open>p \<in> {(pref @ [t]) @ p |p t. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) \<and> (\<forall>p' p''. t # p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'))}\<close> by blast
            then show ?thesis
              using a1 by (metis (no_types))
          qed 
          then have "path M q (pref @ ([t] @ p')) \<and>
                    length ([t] @ p') \<le> Suc k \<and> f (pref @ ([t] @ p')) \<and> (\<forall>p'' p'''. ([t] @ p') = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
            by auto
          moreover have "p = pref @ ([t] @ p')" using \<open>p = (pref @ [t]) @ p'\<close> by simp
          ultimately show "p \<in> ?P" by auto
        qed
        moreover have "?P \<subseteq> ?UN''"
        proof 
          fix p assume "p \<in> ?P"
          then obtain p' where "p = pref @ p'" 
                           and ***: "path M q (pref @ p')
                                       \<and> length p' \<le> Suc k
                                       \<and> f (pref @ p')
                                       \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p''))"
            by blast
          
          then have "p' \<noteq> []"
            using False by auto
          then obtain t p'' where "p' = [t] @ p''"
            by (metis append_Cons append_Nil list.exhaust) 
          then have "path M q ((pref @ [t]) @ p'') 
                      \<and> length p'' \<le> k
                      \<and> f ((pref @ [t]) @ p'') \<and> (\<forall>p''' p''''. t # p'' = p''' @ p'''' \<and> p'''' \<noteq> [] \<longrightarrow> \<not> f (pref @ p'''))"
            using *** by auto
          then have "(pref @ [t]) @ p'' \<in> ?UN''"
            by fastforce
          then show "p \<in> ?UN''"
            using \<open>p = pref @ p'\<close> \<open>p' = [t] @ p''\<close> by auto
        qed
        ultimately show ?thesis by blast
      qed
          
      show "\<Union>?UN = ?P"
        using \<open>\<Union>?UN = ?UN'\<close> \<open>?UN' = ?UN''\<close> \<open>?UN'' = ?P\<close> by auto
    qed
    ultimately show ?thesis by auto
  qed
qed
    

lemma paths_up_to_length_or_condition_path_set_nil :
  assumes "q \<in> nodes M" 
  shows "set (paths_up_to_length_or_condition M q k f []) = { p . path M q p \<and> length p \<le> k \<and> f p \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> \<not> f p')}"
proof -
  have "path M q []"
    using assms by auto
  show ?thesis
    using paths_up_to_length_or_condition_path_set[OF \<open>path M q []\<close>] by auto
qed






fun paths_up_to_length_or_condition_with_witness :: "'a FSM \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> ('a Transition list \<Rightarrow> 'c option) \<Rightarrow> 'a Transition list \<Rightarrow> ('a Transition list \<times> 'c) list" where
  "paths_up_to_length_or_condition_with_witness M q 0 f pref = (case f pref of
    Some x \<Rightarrow> [(pref,x)] |
    None   \<Rightarrow> [])" | 
  "paths_up_to_length_or_condition_with_witness M q (Suc k) f pref = (case f pref of
    Some x \<Rightarrow> [(pref,x)] |
    None   \<Rightarrow> (concat (map (\<lambda> t . (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])))
                           (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))"




lemma paths_up_to_length_or_condition_with_witness_path_set :
  assumes "path M q pref" 
  shows "set (paths_up_to_length_or_condition_with_witness M q k f pref) = {(pref@p,x) | p x . path M q (pref@p) \<and> length p \<le> k \<and> f (pref@p) = Some x \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> f (pref@p') = None)}"
using assms proof (induction k arbitrary: q pref)
  case 0
  then show ?case 
      using 0 assms by force
next
  case (Suc k)

  show ?case proof (cases "f pref")
    case (Some a)
    then show ?thesis using Suc.prems by force
  next
    case None
    then have "set (paths_up_to_length_or_condition_with_witness M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    also have "\<dots> = \<Union>{set (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])) | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by force
    

    have *: "\<And> t . t \<in> transitions M \<Longrightarrow> t_source t = target pref q \<Longrightarrow> set (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])) 
                                                            =  {((pref @ [t]) @ p, x) | p x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}"
      by (simp add: Suc.IH Suc.prems path_append_last)

    

    from None have "set (paths_up_to_length_or_condition_with_witness M q (Suc k) f pref) = 
                  set ((concat (map
              (\<lambda> t . (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])))
              (filter (\<lambda> t . t_source t = target pref q) (wf_transitions M)))))" 
      unfolding paths_up_to_length_or_condition.simps by force
    moreover have "\<dots> = \<Union>{set (paths_up_to_length_or_condition_with_witness M q k f (pref@[t])) | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by force
    moreover have "\<dots> = \<Union>{{((pref @ [t]) @ p, x) | p x .
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      using * by (metis (no_types, lifting))
    ultimately have "set (paths_up_to_length_or_condition_with_witness M q (Suc k) f pref) = \<Union>{{((pref @ [t]) @ p, x) | p x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      by simp
    moreover have "\<Union>{{((pref @ [t]) @ p, x) | p x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)} | t . t \<in> transitions M \<and> t_source t = target pref q}
                  = {(pref@p, x) | p x . path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) = Some x \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> f (pref@p') = None)}"
    proof -
      let ?UN = "{{((pref @ [t]) @ p, x) |p x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)} | t . t \<in> transitions M \<and> t_source t = target pref q}"
      let ?UN' = "{((pref @ [t]) @ p, x) |p t x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}"

      have **: "\<And> p t . path M q ((pref @ [t]) @ p) \<Longrightarrow> t \<in> transitions M \<and> t_source t = target pref q"
        by auto
      
      have "\<Union>?UN = ?UN'"
      proof -
        have "\<Union>?UN \<subseteq> ?UN'"
        proof 
          fix px assume "px \<in> \<Union>?UN"
          then obtain P where "px \<in> P" and "P \<in> ?UN"
            by (meson UnionE)
            
          then obtain t where "t \<in> transitions M \<and> t_source t = target pref q"
                          and "P = {((pref @ [t]) @ p, x) |p x.
                                     path M q ((pref @ [t]) @ p) \<and>
                                     length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}"
            by auto
          then obtain p' x where "px = ((pref @ [t]) @ p', x)" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') = Some x \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p'') = None)"
            using \<open>px \<in> P\<close>
          proof -
            assume a1: "\<And>p' x. \<lbrakk>px = ((pref @ [t]) @ p', x); path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') = Some x \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p'') = None)\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps c. px = ((pref @ [t]) @ ps, c) \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) = Some c \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ psa) = None)"
              using \<open>P = {((pref @ [t]) @ p, x) |p x. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}\<close> \<open>px \<in> P\<close> by force
            then show ?thesis
              using a1 by moura
          qed 

          then show "px \<in> ?UN'" by fastforce
        qed

        moreover have "?UN' \<subseteq> \<Union>?UN"
        proof 
          fix px assume "px \<in> ?UN'"
          then obtain t p' x where "px = ((pref @ [t]) @ p',x)" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') = Some x \<and>
                 (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p'') = None)"
          proof -
            assume a1: "\<And>t p' x. \<lbrakk>px = ((pref @ [t]) @ p', x); path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') = Some x \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p'') = None)\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps p c. px = ((pref @ [p]) @ ps, c) \<and> path M q ((pref @ [p]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [p]) @ ps) = Some c \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [p]) @ psa) = None)"
              using \<open>px \<in> {((pref @ [t]) @ p, x) |p t x. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}\<close> by fastforce
            then show ?thesis
              using a1 by (metis (no_types))
          qed 
          then have px_elem: "px \<in> {((pref @ [t]) @ p,x) |p x.
                      path M q ((pref @ [t]) @ p) \<and>
                      length p \<le> k \<and>
                      f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)}" 
            by auto
          then show "px \<in> \<Union>?UN"
            using **[OF \<open> path M q ((pref @ [t]) @ p')\<close>]  
          proof -
            have f1: "\<exists>ps. px = ((pref @ [t]) @ ps,x) \<and> path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) = Some x \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ psa) = None)"
              using px_elem \<open>px = ((pref @ [t]) @ p',x)\<close> by force
            have f2: "{((pref @ [t]) @ ps, x) |ps x. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) = Some x \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ psa) = None)} \<in> {{((pref @ [p]) @ ps,x) |ps x. path M q ((pref @ [p]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [p]) @ ps) = Some x \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [p]) @ psa) = None)} | p. p \<in> set (wf_transitions M) \<and> t_source p = target pref q}"
              using \<open>t \<in> set (wf_transitions M) \<and> t_source t = target pref q\<close> by blast
            have "px \<in> {((pref @ [t]) @ ps,x) |ps x. path M q ((pref @ [t]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [t]) @ ps) = Some x \<and> (\<forall>psa psb. ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ psa) = None)}"
              using f1 by fastforce
            then show ?thesis
              using f2 by (meson Union_iff)
          qed 
        qed
        
        ultimately show ?thesis by blast
      qed



      let ?UN'' = "{((pref @ [t]) @ p,x) |p t x.
                           path M q ((pref @ [t]) @ p) \<and>
                           length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x\<and> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f (pref @ p') = None)}"
      have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None) \<Longrightarrow> (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f (pref @ p') = None)"
        using None by (metis (no_types, hide_lams) append.assoc append_Nil append_Nil2 append_eq_Cons_conv) 
      moreover have "\<And> t p . (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f (pref @ p') = None) \<Longrightarrow> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None)"
        using None by (metis (no_types, hide_lams) append.assoc append_Nil append_eq_Cons_conv)
      ultimately have "\<And> t p . (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f ((pref @ [t]) @ p') = None) = (\<forall>p' p''. (t#p) = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f (pref @ p') = None)"
        by auto
      then have "?UN' = ?UN''" by auto
      

      let ?P = "{((pref@p),x) | p x. path M q (pref@p) \<and> length p \<le> Suc k \<and> f (pref@p) = Some x \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> f (pref@p') = None)}"
      have "?UN'' = ?P"
      proof -
        have "?UN'' \<subseteq> ?P" 
        proof 
          fix px assume "px \<in> ?UN''"
          then obtain t p' x where "px = ((pref @ [t]) @ p',x)" and "path M q ((pref @ [t]) @ p')" and 
                 "length p' \<le> k \<and>
                 f ((pref @ [t]) @ p') = Some x \<and>
                 (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f (pref @ p'') = None)"
          proof -
            assume a1: "\<And>t p' x. \<lbrakk>px = ((pref @ [t]) @ p', x); path M q ((pref @ [t]) @ p'); length p' \<le> k \<and> f ((pref @ [t]) @ p') = Some x \<and> (\<forall>p'' p'''. t # p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f (pref @ p'') = None)\<rbrakk> \<Longrightarrow> thesis"
            have "\<exists>ps p c. px = ((pref @ [p]) @ ps, c) \<and> path M q ((pref @ [p]) @ ps) \<and> length ps \<le> k \<and> f ((pref @ [p]) @ ps) = Some c \<and> (\<forall>psa psb. p # ps = psa @ psb \<and> psb \<noteq> [] \<longrightarrow> f (pref @ psa) = None)"
              using \<open>px \<in> {((pref @ [t]) @ p, x) |p t x. path M q ((pref @ [t]) @ p) \<and> length p \<le> k \<and> f ((pref @ [t]) @ p) = Some x \<and> (\<forall>p' p''. t # p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> f (pref @ p') = None)}\<close> by fastforce
            then show ?thesis
              using a1 by (metis (no_types))
          qed
          then have "path M q (pref @ ([t] @ p')) \<and>
                    length ([t] @ p') \<le> Suc k \<and> f (pref @ ([t] @ p')) = Some x \<and> (\<forall>p'' p'''. ([t] @ p') = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f (pref @ p'') = None)"
            by auto
          moreover note \<open>px = ((pref @ [t]) @ p',x)\<close> 
          ultimately show "px \<in> ?P" by auto
        qed
        moreover have "?P \<subseteq> ?UN''"
        proof 
          fix px assume "px \<in> ?P"
          then obtain p' x  where "px = (pref @ p',x)" 
                           and ***: "path M q (pref @ p')
                                       \<and> length p' \<le> Suc k
                                       \<and> f (pref @ p') = Some x
                                       \<and> (\<forall>p'' p'''. p' = p'' @ p''' \<and> p''' \<noteq> [] \<longrightarrow> f (pref @ p'') = None)"
            by blast
          
          then have "p' \<noteq> []"
            using None by auto
          then obtain t p'' where "p' = [t] @ p''"
            by (metis append_Cons append_Nil list.exhaust) 
          then have "path M q ((pref @ [t]) @ p'') 
                      \<and> length p'' \<le> k
                      \<and> f ((pref @ [t]) @ p'') = Some x \<and> (\<forall>p''' p''''. t # p'' = p''' @ p'''' \<and> p'''' \<noteq> [] \<longrightarrow> f (pref @ p''') = None)"
            using *** by auto
          then have "((pref @ [t]) @ p'',x) \<in> ?UN''"
            by fastforce
          then show "px \<in> ?UN''"
            using \<open>px = (pref @ p',x)\<close> \<open>p' = [t] @ p''\<close> by auto
        qed
        ultimately show ?thesis by blast
      qed
          
      show "\<Union>?UN = ?P"
        using \<open>\<Union>?UN = ?UN'\<close> \<open>?UN' = ?UN''\<close> \<open>?UN'' = ?P\<close> by auto
    qed
    ultimately show ?thesis by auto
  qed
qed
    

lemma paths_up_to_length_or_condition_with_witness_path_set_nil :
  assumes "q \<in> nodes M" 
  shows "set (paths_up_to_length_or_condition_with_witness M q k f []) = { (p,x) . path M q p \<and> length p \<le> k \<and> f p = Some x \<and> (\<forall> p' p'' . (p = p'@p'' \<and> p'' \<noteq> []) \<longrightarrow> f p' = None)}"
proof -
  have "path M q []"
    using assms by auto
  show ?thesis
    using paths_up_to_length_or_condition_with_witness_path_set[OF \<open>path M q []\<close>] by auto
qed


fun is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "is_prefix [] _ = True" |
  "is_prefix (x#xs) [] = False" |
  "is_prefix (x#xs) (y#ys) = (x = y \<and> is_prefix xs ys)" 

lemma is_prefix_prefix : "is_prefix xs ys = (\<exists> xs' . ys = xs@xs')"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case proof (cases "is_prefix (x#xs) ys")
    case True
    then show ?thesis using Cons.IH 
      by (metis Cons_eq_appendI is_prefix.elims(2) list.inject null_rec(1) null_rec(2))
  next
    case False
    then show ?thesis
      using Cons.IH by auto 
  qed
qed


lemma maximal_path_target_deadlock :
  assumes "path M (initial M) p"
  and     "\<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')"
shows "deadlock_state M (target (initial M) p)"
proof -
  have "\<not>(\<exists> t \<in> transitions M . t_source t = target (initial M) p)"
    using assms(2) unfolding is_prefix_prefix
    by (metis append_Nil2 assms(1) not_Cons_self2 path_append_last same_append_eq)
  then show ?thesis by auto
qed

lemma path_to_deadlock_is_maximal :
  assumes "path M (initial M) p"
  and     "deadlock_state M (target (initial M) p)"
shows "\<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')"
proof 
  assume "\<exists>p'. path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p'"
  then obtain p' where "path M (initial M) p'" and "is_prefix p p'" and "p \<noteq> p'" by blast
  then have "length p' > length p"
    unfolding is_prefix_prefix by auto
  then obtain t p2 where "p' = p @ [t] @ p2"
    using \<open>is_prefix p p'\<close> unfolding is_prefix_prefix
    by (metis \<open>p \<noteq> p'\<close> append.left_neutral append_Cons append_Nil2 non_sym_dist_pairs'.cases) 
  then have "path M (initial M) (p@[t])"
    using \<open>path M (initial M) p'\<close> by auto
  then have "t \<in> transitions M" and "t_source t = target (initial M) p"
    by auto
  then show "False"
    using \<open>deadlock_state M (target (initial M) p)\<close> unfolding deadlock_state.simps by blast
qed





fun maximal_acyclic_paths :: "'a FSM \<Rightarrow> 'a Transition list list" where
  "maximal_acyclic_paths M = (let ps = distinct_paths_up_to_length_from_initial M (size M - 1) in
                                  filter (\<lambda> p . \<not> (\<exists> p' \<in> set ps . is_prefix p p' \<and> p \<noteq> p')) ps)"


lemma maximal_acyclic_paths_set : 
  assumes "acyclic M"
  shows "set (maximal_acyclic_paths M) = { p . path M (initial M) p \<and> deadlock_state M (target (initial M) p) }"
proof -
  let ?ps = "distinct_paths_up_to_length_from_initial M (size M - 1)"

  have "\<And> p . path M (initial M) p \<Longrightarrow> length p \<le> FSM.size M - 1"
    using acyclic_path_length[OF assms] by fastforce
  then have "set ?ps = {p. path M (initial M) p}"
    using distinct_paths_up_to_length_path_set[of M "size M - 1"]
    using assms unfolding acyclic.simps by blast
  then have "set (maximal_acyclic_paths M) = {p. path M (initial M) p \<and> \<not>(\<exists> p' . path M (initial M) p' \<and> is_prefix p p' \<and> p \<noteq> p')}"
    by auto
  also have "... = { p . path M (initial M) p \<and> deadlock_state M (target (initial M) p) }"
    using maximal_path_target_deadlock path_to_deadlock_is_maximal by blast
  finally show ?thesis by assumption
qed
     
  

subsection \<open>Total Order on Nodes\<close>

(* TODO: move to Util *)
fun linear_order_from_list_position' :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "linear_order_from_list_position' [] = []" |
  "linear_order_from_list_position' (x#xs) = (x,x) # (map (\<lambda> y . (x,y)) xs) @ (linear_order_from_list_position' xs)"

fun linear_order_from_list_position :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "linear_order_from_list_position xs = linear_order_from_list_position' (remdups xs)"



lemma linear_order_from_list_position_set :
  "set (linear_order_from_list_position xs) = (set (map (\<lambda> x . (x,x)) xs)) \<union> set (non_sym_dist_pairs xs)"
  by (induction xs; auto)

lemma linear_order_from_list_position_total: "total_on (set xs) (set (linear_order_from_list_position xs))"
  unfolding linear_order_from_list_position_set
  using non_sym_dist_pairs_elems[of _ xs]
  by (meson UnI2 total_onI)

lemma linear_order_from_list_position_refl: "refl_on (set xs) (set (linear_order_from_list_position xs))"  
proof 
  show "set (linear_order_from_list_position xs) \<subseteq> set xs \<times> set xs"
    unfolding linear_order_from_list_position_set
    using non_sym_dist_pairs_subset[of xs] by auto
  show "\<And>x. x \<in> set xs \<Longrightarrow> (x, x) \<in> set (linear_order_from_list_position xs)"
    unfolding linear_order_from_list_position_set
    using non_sym_dist_pairs_subset[of xs] by auto
qed

lemma linear_order_from_list_position_antisym: "antisym (set (linear_order_from_list_position xs))"
proof 
  fix x y assume "(x, y) \<in> set (linear_order_from_list_position xs)" and "(y, x) \<in> set (linear_order_from_list_position xs)"
  then have "(x, y) \<in> set (map (\<lambda>x. (x, x)) xs) \<union> set (non_sym_dist_pairs xs)"
       and  "(y, x) \<in> set (map (\<lambda>x. (x, x)) xs) \<union> set (non_sym_dist_pairs xs)"
    unfolding linear_order_from_list_position_set by blast+
  then consider (a) "(x, y) \<in> set (map (\<lambda>x. (x, x)) xs)" |
                (b) "(x, y) \<in> set (non_sym_dist_pairs xs)"
    by blast
  then show "x = y"
  proof cases
    case a
    then show ?thesis by auto
  next
    case b
    then have "x \<noteq> y" and "(y,x) \<notin> set (non_sym_dist_pairs xs)"
      using non_sym_dist_pairs_set_iff[of x y xs] by simp+
    then have "(y, x) \<notin> set (map (\<lambda>x. (x, x)) xs) \<union> set (non_sym_dist_pairs xs)"
      by auto
    then show ?thesis 
     using \<open>(y, x) \<in> set (map (\<lambda>x. (x, x)) xs) \<union> set (non_sym_dist_pairs xs)\<close> by blast
  qed
qed


lemma non_sym_dist_pairs'_indices : "distinct xs \<Longrightarrow> (x,y) \<in> set (non_sym_dist_pairs' xs) \<Longrightarrow> (\<exists> i j . xs ! i = x \<and> xs ! j = y \<and> i < j \<and> i < length xs \<and> j < length xs)"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  show ?case proof (cases "a = x")
    case True
    then have "(a#xs) ! 0 = x" and "0 < length (a#xs)"
      by auto
    
    have "y \<in> set xs"
      using non_sym_dist_pairs'_elems_distinct(2,3)[OF Cons.prems(1,2)] True by auto
    then obtain j where "xs ! j = y" and "j < length xs"
      by (meson in_set_conv_nth)
    then have "(a#xs) ! (Suc j) = y" and "Suc j < length (a#xs)"
      by auto

    then show ?thesis 
      using \<open>(a#xs) ! 0 = x\<close> \<open>0 < length (a#xs)\<close> by blast
  next
    case False
    then have "(x,y) \<in> set (non_sym_dist_pairs' xs)"
      using Cons.prems(2) by auto
    then show ?thesis 
      using Cons.IH Cons.prems(1)
      by (metis Suc_mono distinct.simps(2) length_Cons nth_Cons_Suc)
  qed
qed



lemma non_sym_dist_pairs'_trans: "distinct xs \<Longrightarrow> trans (set (non_sym_dist_pairs' xs))"
proof 
  fix x y z assume "distinct xs" and "(x, y) \<in> set (non_sym_dist_pairs' xs)" and "(y, z) \<in> set (non_sym_dist_pairs' xs)"

  obtain nx ny where "xs ! nx = x" and "xs ! ny = y" and "nx < ny" and "nx < length xs" and "ny < length xs"
    using non_sym_dist_pairs'_indices[OF \<open>distinct xs\<close> \<open>(x, y) \<in> set (non_sym_dist_pairs' xs)\<close>] by blast

  obtain ny' nz where "xs ! ny' = y" and "xs ! nz = z" and "ny'< nz" and "ny' < length xs" and "nz < length xs"
    using non_sym_dist_pairs'_indices[OF \<open>distinct xs\<close> \<open>(y, z) \<in> set (non_sym_dist_pairs' xs)\<close>] by blast

  have "ny' = ny"
    using \<open>distinct xs\<close> \<open>xs ! ny = y\<close> \<open>xs ! ny' = y\<close> \<open>ny < length xs\<close> \<open>ny' < length xs\<close> nth_eq_iff_index_eq by metis
  then have "nx < nz"
    using \<open>nx < ny\<close> \<open>ny' < nz\<close> by auto

  then have "nx \<noteq> nz" by simp
  then have "x \<noteq> z"
    using \<open>distinct xs\<close> \<open>xs ! nx = x\<close> \<open>xs ! nz = z\<close> \<open>nx < length xs\<close> \<open>nz < length xs\<close> nth_eq_iff_index_eq by metis

  have "remdups xs = xs"
    using \<open>distinct xs\<close> by auto

  have "\<not>(z, x) \<in> set (non_sym_dist_pairs' xs)"
  proof 
    assume "(z, x) \<in> set (non_sym_dist_pairs' xs)"
    then obtain nz' nx' where "xs ! nx' = x" and "xs ! nz' = z" and "nz'< nx'" and "nx' < length xs" and "nz' < length xs"
      using non_sym_dist_pairs'_indices[OF \<open>distinct xs\<close>, of z x] by metis

    have "nx' = nx"
      using \<open>distinct xs\<close> \<open>xs ! nx = x\<close> \<open>xs ! nx' = x\<close> \<open>nx < length xs\<close> \<open>nx' < length xs\<close> nth_eq_iff_index_eq by metis
    moreover have "nz' = nz"
      using \<open>distinct xs\<close> \<open>xs ! nz = z\<close> \<open>xs ! nz' = z\<close> \<open>nz < length xs\<close> \<open>nz' < length xs\<close> nth_eq_iff_index_eq by metis
    ultimately have "nz < nx"
      using \<open>nz'< nx'\<close> by auto
    then show "False"
      using \<open>nx < nz\<close> by simp    
  qed
  then show "(x, z) \<in> set (non_sym_dist_pairs' xs)" 
    using non_sym_dist_pairs'_elems_distinct(1)[OF \<open>distinct xs\<close> \<open>(x, y) \<in> set (non_sym_dist_pairs' xs)\<close>]
    using non_sym_dist_pairs'_elems_distinct(2)[OF \<open>distinct xs\<close> \<open>(y, z) \<in> set (non_sym_dist_pairs' xs)\<close>]
    using \<open>x \<noteq> z\<close>
    using non_sym_dist_pairs_elems[of x xs z]
    unfolding non_sym_dist_pairs.simps \<open>remdups xs = xs\<close> by blast
qed


lemma non_sym_dist_pairs_trans: "trans (set (non_sym_dist_pairs xs))"
  using non_sym_dist_pairs'_trans[of "remdups xs", OF distinct_remdups] unfolding non_sym_dist_pairs.simps by assumption



lemma linear_order_from_list_position_trans: "trans (set (linear_order_from_list_position xs))"
proof 
  fix x y z assume "(x, y) \<in> set (linear_order_from_list_position xs)" and "(y, z) \<in> set (linear_order_from_list_position xs)"
  then consider (a) "(x, y) \<in> set (map (\<lambda>x. (x, x)) xs) \<and> (y, z) \<in> set (map (\<lambda>x. (x, x)) xs)" |
                (b) "(x, y) \<in> set (map (\<lambda>x. (x, x)) xs) \<and> (y, z) \<in> set (non_sym_dist_pairs xs)" |
                (c) "(x, y) \<in> set (non_sym_dist_pairs xs) \<and> (y, z) \<in> set (map (\<lambda>x. (x, x)) xs)" |
                (d) "(x, y) \<in> set (non_sym_dist_pairs xs) \<and> (y, z) \<in> set (non_sym_dist_pairs xs)"
    unfolding linear_order_from_list_position_set by blast+
  then show "(x, z) \<in> set (linear_order_from_list_position xs)"
  proof cases
    case a
    then show ?thesis unfolding linear_order_from_list_position_set by auto
  next
    case b
    then show ?thesis unfolding linear_order_from_list_position_set by auto
  next
    case c
    then show ?thesis unfolding linear_order_from_list_position_set by auto
  next
    case d
    then show ?thesis unfolding linear_order_from_list_position_set 
                      using non_sym_dist_pairs_trans 
                      by (metis UnI2 transE)
  qed
qed

  
  
 



definition node_order :: "'a FSM \<Rightarrow> ('a \<times> 'a) set" where
  "node_order M = set (linear_order_from_list_position (nodes_from_distinct_paths M))"

value "node_order M_ex_9"



lemma node_order_refl : "\<And> q1 . q1 \<in> nodes M \<Longrightarrow> (q1,q1) \<in> node_order M"
  using linear_order_from_list_position_refl[of "nodes_from_distinct_paths M"]
  unfolding nodes_code refl_on_def node_order_def by blast

lemma node_order_trans : "\<And> q1 q2 q3 . (q1,q2) \<in> node_order M \<Longrightarrow> (q2,q3) \<in> node_order M \<Longrightarrow> (q1,q3) \<in> node_order M"
  using linear_order_from_list_position_trans[of "nodes_from_distinct_paths M"]
  unfolding nodes_code node_order_def trans_def by blast

lemma node_order_antisym : "\<And> q1 q2 . (q1,q2) \<in> node_order M \<Longrightarrow> (q2,q1) \<in> node_order M \<Longrightarrow> q1 = q2"
  using linear_order_from_list_position_antisym[of "nodes_from_distinct_paths M"]
  unfolding nodes_code refl_on_def antisym_def node_order_def by blast
  
lemma node_order_total : "\<And> q1 q2 . q1 \<in> nodes M \<Longrightarrow> q2 \<in> nodes M \<Longrightarrow> (q1,q2) \<in> node_order M \<or> (q2,q1) \<in> node_order M"
  using linear_order_from_list_position_total[of "nodes_from_distinct_paths M"]
  unfolding nodes_code total_on_def antisym_def node_order_def 
  by (metis linear_order_from_list_position_refl refl_onD)




end