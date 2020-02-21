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


lemma path_h :
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

subsubsection \<open>Calculating Distinct Paths\<close>

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

end