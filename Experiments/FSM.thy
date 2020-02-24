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

lemma visited_states_are_nodes :
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

definition reachable_nodes :: "('a,'b,'c) fsm \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "reachable_nodes M q = {q . \<exists> p . path M (initial M) p \<and> target (initial M) p = q }"

lemma acyclic_paths_set :
  "acyclic_paths_up_to_length M q (size M - 1) = {p . path M q p \<and> distinct (visited_nodes q p)}"
  unfolding acyclic_paths_up_to_length.simps using acyclic_path_length_limit[of M q]
  by (metis (no_types, lifting) One_nat_def Suc_pred cyclic_path_shortening leD list.size(3) not_less_eq_eq not_less_zero path.intros(1) path_begin_node) 


(* inefficient calculation, as a node may be target of a large number of (acyclic) paths *)
lemma reachable_nodes_code[code] : 
  "reachable_nodes M q = image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
proof -
  have "\<And> q' . q' \<in> reachable_nodes M q \<Longrightarrow> q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1))"
  proof -
    fix q' assume "q' \<in> reachable_nodes M q"
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
  moreover have "\<And> q' . q' \<in> image (target (initial M)) (acyclic_paths_up_to_length M (initial M) (size M - 1)) \<Longrightarrow> q' \<in> reachable_nodes M q"
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




end