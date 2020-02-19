theory Experiment
  imports Main "HOL-Library.Mapping" "HOL-Library.RBT_Mapping" "HOL-Library.RBT_Set" "HOL-Library.Quotient_Product"
    (* TODO: import RBT_Set later to get better output? *)
begin


record ('state, 'input, 'output) fsm_impl =
  initial_impl :: 'state
  nodes_impl :: "'state set"
  inputs_impl  :: "'input set"
  outputs_impl  :: "'output set"
  transitions_impl :: "('state \<times> 'input \<times> 'output \<times> 'state) set"


(* TODO: add common subexpression elimination to avoid nested recalculation? *)
definition set_as_map :: "('a \<times> 'b \<times> 'c) set \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c set option)" where
  "set_as_map s = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> s) then Some {z . (x,y,z) \<in> s} else None)"

(* TODO: prove equivalent result for normal Map type to allow for a later import of Maping ? *)
lemma set_as_map_code[code] : "set_as_map (RBT_Set.Set t) = Mapping.lookup (foldl (\<lambda> m ((x,y,z),()) . case Mapping.lookup m (x,y) of
None \<Rightarrow> Mapping.update (x,y) {z} m |
Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
Mapping.empty
(RBT.entries t))"
proof -
  let ?f = "\<lambda> xs . (foldl (\<lambda> m ((x,y,z),()) . case Mapping.lookup m (x,y) of
None \<Rightarrow> Mapping.update (x,y) {z} m |
Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
Mapping.empty
                                                       xs)"

  have *:"\<And> xs :: (('a \<times> 'b \<times> 'c) \<times> unit) list. Mapping.lookup (?f xs) = (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None)"
  proof -
    fix xs :: "(('a \<times> 'b \<times> 'c) \<times> unit) list"
    show "Mapping.lookup (?f xs) = (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None)"
    proof (induction xs rule: rev_induct)
      case Nil
      have "(?f []) = Mapping.empty"  by auto
      then have "Mapping.lookup (?f []) = (\<lambda> (x,y) . None)"
        using Mapping.lookup_empty by fastforce
      moreover have "(\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set []) then Some {z . ((x,y,z),()) \<in> set []} else None) = (\<lambda> (x,y) . None)" by auto
      ultimately show ?case
        by (simp add: cond_case_prod_eta)
    next
      case (snoc xyz xs)
      then obtain x y z where "xyz = ((x,y,z),())"
        by (metis (mono_tags, hide_lams) old.unit.exhaust surj_pair)

      have scheme: "\<And> x xs f y . foldl f y (xs@[x]) = f (foldl f y xs) x"
        by simp
      have *: "(?f (xs@[((x,y,z),())])) = (case Mapping.lookup (?f xs) (x,y) of
                                  None \<Rightarrow> Mapping.update (x,y) {z} (?f xs) |
                                  Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) (?f xs))"
        unfolding scheme by auto


      then show ?case proof (cases "Mapping.lookup (?f xs) (x,y)")
        case None
        then have **: "(?f (xs@[((x,y,z),())])) = Mapping.update (x,y) {z} (?f xs)" using * by auto

        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          using lookup_update lookup_update_neq by metis

        have m1: "Mapping.lookup (?f (xs@[((x,y,z),())])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else Mapping.lookup (?f xs) (x',y'))"
          unfolding ** scheme by force

        have "(\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x,y) = None"
          using None snoc by auto
        then have "\<not>(\<exists> z . ((x,y,z),()) \<in> set xs)"
          by (metis (mono_tags, lifting) case_prod_conv option.distinct(1))
        then have "(\<exists> z . ((x,y,z),()) \<in> set (xs@[((x,y,z),())]))" and "{z' . ((x,y,z'),()) \<in> set (xs@[((x,y,z),())])} = {z}"
          by auto
        then have m2: "(\<lambda> (x',y') . if (\<exists> z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])) then Some {z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])} else None)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x',y'))"
          by auto

        show ?thesis using m1 m2 snoc
          using \<open>xyz = ((x, y, z), ())\<close> by presburger

      next
        case (Some zs)
        then have **: "(?f (xs@[((x,y,z),())])) = Mapping.update (x,y) (insert z zs) (?f xs)" using * by auto
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          using lookup_update lookup_update_neq by metis

        have m1: "Mapping.lookup (?f (xs@[((x,y,z),())])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else Mapping.lookup (?f xs) (x',y'))"
          unfolding ** scheme by force


        have "(\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x,y) = Some zs"
          using Some snoc by auto
        then have "(\<exists> z . ((x,y,z),()) \<in> set xs)"
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "(\<exists> z . ((x,y,z),()) \<in> set (xs@[((x,y,z),())]))" by simp

        have "{z' . ((x,y,z'),()) \<in> set (xs@[((x,y,z),())])} = insert z zs"
        proof -
          have "Some {z . ((x,y,z),()) \<in> set xs} = Some zs"
            using \<open>(\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x,y) = Some zs\<close>
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "{z . ((x,y,z),()) \<in> set xs} = zs" by auto
          then show ?thesis by auto
        qed

        have "\<And> a b . (\<lambda> (x',y') . if (\<exists> z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])) then Some {z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])} else None) (a,b)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x',y')) (a,b)"
        proof -
          fix a b show "(\<lambda> (x',y') . if (\<exists> z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])) then Some {z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])} else None) (a,b)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x',y')) (a,b)"
          using \<open>{z' . ((x,y,z'),()) \<in> set (xs@[((x,y,z),())])} = insert z zs\<close> \<open>(\<exists> z . ((x,y,z),()) \<in> set (xs@[((x,y,z),())]))\<close>
          by (cases "(a,b) = (x,y)"; auto)
        qed

        then have m2: "(\<lambda> (x',y') . if (\<exists> z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])) then Some {z' . ((x',y',z'),()) \<in> set (xs@[((x,y,z),())])} else None)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . ((x,y,z),()) \<in> set xs) then Some {z . ((x,y,z),()) \<in> set xs} else None) (x',y'))"
          by auto


        show ?thesis using m1 m2 snoc
          using \<open>xyz = ((x, y, z), ())\<close> by presburger
      qed
    qed
  qed

  show ?thesis
    using *[of "RBT.entries t"]
    unfolding set_as_map_def
    unfolding member_code(1)[of _ t] unfolding lookup_in_tree[of t _ "()"] by auto
qed

value "set_as_map {(1::nat,1::nat,1::nat),(1,1,2),(1,2,1),(2,4,1),(1,2,2)} (1,1)"



lift_definition set_as_mapping :: "('a \<times> 'b \<times> 'c) set \<Rightarrow> ('a \<times> 'b, 'c set) mapping" is set_as_map done
lemma[code] : "set_as_mapping (RBT_Set.Set t) = (foldl (\<lambda> m ((x,y,z),()) . case Mapping.lookup m (x,y) of
None \<Rightarrow> Mapping.update (x,y) {z} m |
Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
Mapping.empty
(RBT.entries t))"
  using set_as_map_code[of t]
  unfolding set_as_map_def set_as_mapping.abs_eq
  using Mapping.lookup.abs_eq
  by (simp add: Mapping.lookup.abs_eq mapping_eqI)

value "set_as_mapping {(1::nat,1::nat,1::nat),(1,1,2),(1,2,1),(2,4,1),(1,2,2)}"



definition h :: "('state, 'input, 'output) fsm_impl \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" where
  "h M = (\<lambda> (q,x) . {(y,q') . (q,x,y,q') \<in> transitions_impl M})"

lemma[code] : "h M = (let m = set_as_map (transitions_impl M) in (\<lambda> (q,x) . case m (q,x) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}))"
proof
  fix qx
  let ?f = "(let m = set_as_map (transitions_impl M) in (\<lambda> (q,x) . case m (q,x) of Some ts \<Rightarrow> ts | None \<Rightarrow> {}))"

  have "\<And> yq . yq \<in> h M qx \<Longrightarrow> yq \<in> ?f qx"
    unfolding set_as_map_def h_def
    by force
  moreover have "\<And> yq . yq \<in> ?f qx \<Longrightarrow> yq \<in> h M qx"
  proof -
    fix yq assume "yq \<in> ?f qx"
    then obtain zs where "(set_as_map (transitions_impl M)) qx = Some zs" and "yq \<in> zs"
      unfolding Let_def
      by (metis (no_types, lifting) equals0D mem_case_prodE option.case_eq_if option.collapse)
    then have "yq \<in> {z. (fst qx, snd qx, z) \<in> transitions_impl M}"
      unfolding set_as_map_def
    proof -
      assume "(case qx of (x, y) \<Rightarrow> if \<exists>z. (x, y, z) \<in> transitions_impl M then Some {z. (x, y, z) \<in> transitions_impl M} else None) = Some zs"
      then have "(if \<exists>p. (fst qx, snd qx, p) \<in> transitions_impl M then Some {p. (fst qx, snd qx, p) \<in> transitions_impl M} else None) = Some zs"
        by (simp add: case_prod_beta')
      then show ?thesis
        by (metis \<open>yq \<in> zs\<close> option.discI option.inject)
    qed
    then show "yq \<in> h M qx"
      unfolding h_def by auto
  qed
  ultimately show "h M qx = ?f qx" by blast
qed



end (*

fun h_impl :: "('state, 'input, 'output) fsm_impl \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" where
  "h_impl M qx = (case h'_impl M qx of None \<Rightarrow> {} | Some yqs \<Rightarrow> yqs)"


definition fsm_impl_empty :: "'a \<Rightarrow> ('a,'b,'c) fsm_impl" where
  "fsm_impl_empty q = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Map.empty \<rparr>"

definition update_h'_impl :: "('a \<rightharpoonup> ('b set)) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> ('b set))" where
  "update_h'_impl hM qx yq' = (case (hM qx) of None \<Rightarrow> hM (qx \<mapsto> {yq'}) | Some yqs \<Rightarrow> hM (qx \<mapsto> insert yq' yqs))"

lift_definition update_h'_impl' :: "('a, 'b set) mapping \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b set) mapping"
  is update_h'_impl done

lemma[code] : "update_h'_impl' hM qx yq' = (case (Mapping.lookup hM qx) of None \<Rightarrow> Mapping.update qx {yq'} hM | Some yqs \<Rightarrow> Mapping.update qx (insert yq' yqs) hM)"
  by transfer (fact update_h'_impl_def)

value "update_h'_impl' Mapping.empty (1::nat) (2::nat)"
value "update_h'_impl Map.empty (1::nat) (2::nat)"

export_code update_h'_impl update_h'_impl' in Haskell




(*
record ('state, 'input, 'output) fsm_impl_m =
  initial_impl :: 'state
  nodes_impl :: "'state set"
  inputs_impl  :: "'input set"
  outputs_impl  :: "'output set"
  h'_impl :: "(('state \<times> 'input), (('output \<times> 'state) set)) mapping"

lift_definition h_impl_m :: "('state, 'input, 'output) fsm_impl_m \<Rightarrow> ('state \<times> 'input) \<Rightarrow> ('output \<times> 'state) set" is h_impl done
lemma[code] : "h_impl_m M = (case (Mapping.lookup (h'_impl M) qx) of None \<Rightarrow> {} | Some yqs \<Rightarrow> yqs)"
*)


fun fsm_impl_from_list :: "'a \<Rightarrow> ('a \<times> 'x \<times> 'y \<times> 'a) list \<Rightarrow> ('a,'x,'y) fsm_impl" where
  "fsm_impl_from_list q [] = fsm_impl_empty q" |
  "fsm_impl_from_list q ((q1,x,y,q2)#ts) = (let M = fsm_impl_from_list q ts
                                             in \<lparr> initial_impl = initial_impl M,
                                                  nodes_impl = nodes_impl M \<union> {q1,q2},
                                                  inputs_impl = insert x (inputs_impl M),
                                                  outputs_impl = insert y (outputs_impl M),
                                                  h'_impl = update_h'_impl (h'_impl M) (q1,x) (y,q2) \<rparr>)"




value "fsm_impl_from_list 0 ([] :: (nat \<times> nat \<times> nat \<times> nat) list)"

(*
lemma[code] : "fsm_impl_empty q = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Mapping.empty \<rparr>"
*)

typedef ('state, 'input, 'output) fsm = "{ M :: ('state, 'input, 'output) fsm_impl . initial_impl M \<in> nodes_impl M
\<and> finite (nodes_impl M)
\<and> finite (inputs_impl M)
\<and> finite (outputs_impl M)
\<and> (\<forall> q x y q' . (y,q') \<in> h_impl M (q,x) \<longrightarrow> (q \<in> nodes_impl M \<and> x \<in> inputs_impl M \<and> q' \<in> nodes_impl M \<and> y \<in> outputs_impl M))}"
  morphisms fsm_impl Fsm
proof -
  obtain q :: 'state where "True" by blast
  define M :: "('state, 'input, 'output) fsm_impl" where "M = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Map.empty \<rparr>"
  then have "initial_impl M \<in> nodes_impl M
              \<and> finite (nodes_impl M)
              \<and> finite (inputs_impl M)
              \<and> finite (outputs_impl M)
              \<and> (\<forall> q x y q' . (y,q') \<in> h_impl M (q,x) \<longrightarrow> (q \<in> nodes_impl M \<and> x \<in> inputs_impl M \<and> q' \<in> nodes_impl M \<and> y \<in> outputs_impl M))"
    by auto
  then show ?thesis by blast
qed

definition set_mapping_rel :: "('a \<rightharpoonup> 'b set) \<Rightarrow> ('a, 'b set) mapping \<Rightarrow> bool" where
 "set_mapping_rel m1 m2 = (\<forall> a . m1 a = Mapping.lookup m2 a)"

definition rel_mm :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('c, 'd) mapping \<Rightarrow> bool" where
 "rel_mm A B m1 m2 = (\<forall> a c . A a c \<longrightarrow>  rel_option B (m1 a) (Mapping.lookup m2 c))"

definition rel_mm' :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('c, 'd) mapping \<Rightarrow> bool" where
 "rel_mm' A B m1 m2 = (\<forall> a c . A a c \<longrightarrow>  ((m1 a = None \<and> Mapping.lookup m2 c = None) \<or> (\<exists> b d . m1 a = Some b \<and> Mapping.lookup m2 c = Some d \<and> B b d)))"





thm rel_funD
thm rel_optionI

(* TODO: fix warning *)
setup_lifting type_definition_fsm

lift_definition initial :: "('state, 'input, 'output) fsm \<Rightarrow> 'state" is initial_impl done
lift_definition nodes :: "('state, 'input, 'output) fsm \<Rightarrow> 'state set" is nodes_impl done
lift_definition inputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'input set" is inputs_impl done
lift_definition outputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'output set" is outputs_impl done
lift_definition h :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input) \<Rightarrow> (('output \<times> 'state) set)" is h_impl done

lift_definition fsm_empty :: "'a \<Rightarrow> ('a,'b,'c) fsm" is fsm_impl_empty
  unfolding fsm_impl_empty_def by auto

value "(nodes ((fsm_empty 0) :: (nat,nat,nat) fsm))"
value "initial ((fsm_empty 15) :: (nat,nat,nat) fsm)"

lemma "initial M \<in> nodes M" using fsm_impl unfolding initial.rep_eq nodes.rep_eq by blast
lemma "finite (nodes M)" using fsm_impl unfolding nodes.rep_eq by blast
lemma "finite (inputs M)" using fsm_impl unfolding inputs.rep_eq by blast
lemma "finite (outputs M)" using fsm_impl unfolding outputs.rep_eq by blast
lemma "\<And> q x y q' . (y,q') \<in> h M (q,x) \<Longrightarrow> (q \<in> nodes M \<and> x \<in> inputs M \<and> q' \<in> nodes M \<and> y \<in> outputs M)"
  using fsm_impl[of M]
  unfolding nodes.rep_eq inputs.rep_eq outputs.rep_eq h.rep_eq by blast


definition fsm_empty :: "'a \<Rightarrow> ('a,'b,'c) fsm" where
  "fsm_empty q = Fsm \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Map.empty \<rparr>"

lemma fsm_empty_code[code abstract]:
  "fsm_impl (fsm_empty q :: ('a,'b,'c) fsm) = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Map.empty \<rparr>"
  unfolding fsm_empty_def
  using Fsm_inverse[of "\<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h'_impl = Map.empty \<rparr>"] by auto

value "card (nodes ((fsm_empty 0) :: (nat,nat,nat) fsm))"


definition add_transition :: "('a \<times> 'x \<times> 'y \<times> 'a) \<Rightarrow> ('a,'x,'y) fsm \<Rightarrow> ('a,'x,'y) fsm" where
  "add_transition (q,x,y,q') M = (* TODO: define on fsm_impl and then lift? *)


fun fsm_from_list :: "'a \<Rightarrow> ('a \<times> 'x \<times> 'y \<times> 'a) list \<Rightarrow> ('a,'x,'y) fsm" where
  "fsm_from_list q [] = fsm_empty q" |
  "fsm_from_list q (t#ts) =



end (*

(* IDEA: use ('state \<times> 'input) \<Rightarrow> (('output \<times> 'state) set) as h instead of ('state \<times> 'input) \<rightharpoonup> (('output \<times> 'state) set) to avoid always checking whether h M (q,x) is defined *)

record ('state, 'input, 'output) fsm_impl =
  initial_impl :: 'state
  nodes_impl :: "'state set"
  inputs_impl  :: "'input set"
  outputs_impl  :: "'output set"
  h_impl :: "('state \<times> 'input) \<Rightarrow> (('output \<times> 'state) set)"





typedef ('state, 'input, 'output) fsm = "{ M :: ('state, 'input, 'output) fsm_impl . initial_impl M \<in> nodes_impl M
\<and> finite (nodes_impl M)
\<and> finite (inputs_impl M)
\<and> finite (outputs_impl M)
\<and> (\<forall> q x y q' . (y,q') \<in> h_impl M (q,x) \<longrightarrow> (q \<in> nodes_impl M \<and> x \<in> inputs_impl M \<and> q' \<in> nodes_impl M \<and> y \<in> outputs_impl M))}"
  morphisms fsm_impl Fsm
proof -
  obtain q :: 'state where "True" by blast
  define M :: "('state, 'input, 'output) fsm_impl" where "M = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h_impl = (\<lambda> (q,x) . {}) \<rparr>"
  then have "initial_impl M \<in> nodes_impl M
              \<and> finite (nodes_impl M)
              \<and> finite (inputs_impl M)
              \<and> finite (outputs_impl M)
              \<and> (\<forall> q x y q' . (y,q') \<in> h_impl M (q,x) \<longrightarrow> (q \<in> nodes_impl M \<and> x \<in> inputs_impl M \<and> q' \<in> nodes_impl M \<and> y \<in> outputs_impl M))"
    by auto
  then show ?thesis by blast
qed

typedef ('a,'b) set_fun = "UNIV :: ('a \<Rightarrow> ('b set)) set" ..
setup_lifting type_definition_set_fun

definition set_fun_default :: "('a,'b) set_fun \<Rightarrow> 'b set" where
  "set_fun_default f = {}"

definition set_fun_empty :: "('a,'b) set_fun" where
  "set_fun_empty = Abs_set_fun (\<lambda> x . {})"

definition set_fun_update :: "('a, 'b) set_fun \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) set_fun" where
  "set_fun_update f x y = Abs_set_fun ((Rep_set_fun f)(x := y))"

(*
lift_definition fun_update ::  "('a, 'b) set_fun \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) set_fun" is fun_upd .

lemma "set_fun_update = fun_update"
  unfolding set_fun_update_def fun_update_def sledgehammer *)



definition h_empty :: "('state \<times> 'input) \<Rightarrow> (('output \<times> 'state) set)" where
  "h_empty = (\<lambda> (q,x) . {})"

lift_definition h_empty' :: "(('state \<times> 'input), ('output \<times> 'state)) set_mapping" is h_empty done


fun fsm_from_list :: "'state \<Rightarrow> ('state \<times> 'input \<times> 'output 'state) list \<Rightarrow> ('state, 'input, 'output) fsm" where
  "



end (*


record ('state, 'input, 'output) fsm_impl =
  initial_impl :: 'state
  nodes_impl :: "'state set"
  inputs_impl  :: "'input set"
  outputs_impl  :: "'output set"
  h_impl :: "('state \<times> 'input) \<rightharpoonup> (('output \<times> 'state) set)"

fun f_impl :: "('state, 'input, 'output) fsm_impl \<Rightarrow> bool" where
  "f_impl M = False"

typedef ('state, 'input, 'output) fsm = "{ M :: ('state, 'input, 'output) fsm_impl . initial_impl M \<in> nodes_impl M
\<and> finite (nodes_impl M)
\<and> finite (inputs_impl M)
\<and> finite (outputs_impl M)
\<and> (\<forall> (q,x) \<in> dom (h_impl M) . q \<in> nodes_impl M \<and> x \<in> inputs_impl M)
\<and> (\<forall> S \<in> ran (h_impl M) . \<forall> (y,q') \<in> S . q' \<in> nodes_impl M \<and> y \<in> outputs_impl M)}"
  morphisms fsm_impl Fsm
proof -
  obtain q :: 'state where "True" by blast
  define M :: "('state, 'input, 'output) fsm_impl" where "M = \<lparr> initial_impl = q, nodes_impl = {q}, inputs_impl = {}, outputs_impl = {}, h_impl = Map.empty \<rparr>"
  then have "initial_impl M \<in> nodes_impl M
              \<and> finite (nodes_impl M)
              \<and> finite (inputs_impl M)
              \<and> finite (outputs_impl M)
              \<and> (\<forall> (q,x) \<in> dom (h_impl M) . q \<in> nodes_impl M \<and> x \<in> inputs_impl M)
              \<and> (\<forall> S \<in> ran (h_impl M) . \<forall> (y,q') \<in> S . q' \<in> nodes_impl M \<and> y \<in> outputs_impl M)"
    by auto
  then show ?thesis by blast
qed


setup_lifting type_definition_fsm


lift_definition initial :: "('state, 'input, 'output) fsm \<Rightarrow> 'state" is initial_impl done
lift_definition nodes :: "('state, 'input, 'output) fsm \<Rightarrow> 'state set" is nodes_impl done
lift_definition inputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'input set" is inputs_impl done
lift_definition outputs :: "('state, 'input, 'output) fsm \<Rightarrow> 'output set" is outputs_impl done
lift_definition h :: "('state, 'input, 'output) fsm \<Rightarrow> ('state \<times> 'input) \<rightharpoonup> (('output \<times> 'state) set)" is h_impl done

lift_definition f :: "('state, 'input, 'output) fsm \<Rightarrow> bool" is EXP.f_impl done




definition M :: "(nat,nat,nat) fsm_impl" where
  "M = \<lparr> initial_impl = 0, nodes_impl = {0,1,2}, inputs_impl = {0}, outputs_impl = {0,1}, h_impl = Map.empty \<rparr>"

lemma "initial_impl M \<in> nodes_impl M
              \<and> finite (nodes_impl M)
              \<and> finite (inputs_impl M)
              \<and> finite (outputs_impl M)
              \<and> (\<forall> (q,x) \<in> dom (h_impl M) . q \<in> nodes_impl M \<and> x \<in> inputs_impl M)
              \<and> (\<forall> S \<in> ran (h_impl M) . \<forall> (y,q') \<in> S . q' \<in> nodes_impl M \<and> y \<in> outputs_impl M)" unfolding M_def by force
value "M"


value "initial_impl M"
lemma "initial_impl M = initial (Fsm M)"
proof -
  have "initial_impl M \<in> nodes_impl M
              \<and> finite (nodes_impl M)
              \<and> finite (inputs_impl M)
              \<and> finite (outputs_impl M)
              \<and> (\<forall> (q,x) \<in> dom (h_impl M) . q \<in> nodes_impl M \<and> x \<in> inputs_impl M)
              \<and> (\<forall> S \<in> ran (h_impl M) . \<forall> (y,q') \<in> S . q' \<in> nodes_impl M \<and> y \<in> outputs_impl M)" unfolding M_def by force
  then show ?thesis

value "initial (Fsm M)"


end 