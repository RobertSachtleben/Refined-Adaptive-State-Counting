theory FSM_Impl
  imports Main
begin

record ('state, 'input, 'output) fsm_impl =
  initial :: 'state
  nodes :: "'state set"
  inputs  :: "'input set"
  outputs  :: "'output set"
  transitions :: "('state \<times> 'input \<times> 'output \<times> 'state) set"


(* TODO: add common subexpression elimination to avoid nested recalculation? *)
(* possibly as last refinement step (via complete unfolding ...) *)
definition set_as_map :: "('a \<times> 'c) set \<Rightarrow> ('a \<Rightarrow> 'c set option)" where
  "set_as_map s = (\<lambda> x . if (\<exists> z . (x,z) \<in> s) then Some {z . (x,z) \<in> s} else None)"


lemma set_as_map_code[code] : "set_as_map (set xs) = (foldl (\<lambda> m (x,z) . case m x of
                                                                                  None \<Rightarrow> m (x \<mapsto> {z}) |
                                                                                  Some zs \<Rightarrow> m (x \<mapsto>  (insert z zs)))
                                                            Map.empty
                                                            xs)"
proof - 
  let ?f = "\<lambda> xs . (foldl (\<lambda> m (x,z) . case m x of
                                                                                  None \<Rightarrow> m (x \<mapsto> {z}) |
                                                                                  Some zs \<Rightarrow> m (x \<mapsto>  (insert z zs)))
                                                            Map.empty
                                                            xs)"
  have "(?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc xz xs)
    then obtain x z where "xz = (x,z)" 
      by (metis (mono_tags, hide_lams) surj_pair)

    have *: "(?f (xs@[(x,z)])) = (case (?f xs) x of
                                None \<Rightarrow> (?f xs) (x \<mapsto> {z}) |
                                Some zs \<Rightarrow> (?f xs) (x \<mapsto> (insert z zs)))"
      by auto

    then show ?case proof (cases "(?f xs) x")
      case None
      then have **: "(?f (xs@[(x,z)])) = (?f xs) (x \<mapsto> {z})" using * by auto

      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto


      have m1: "(?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some {z} else (?f xs) x')"
        unfolding ** 
        unfolding scheme by force

      have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = None"
        using None snoc by auto
      then have "\<not>(\<exists> z . (x,z) \<in> set xs)"
        by (metis (mono_tags, lifting) case_prod_conv option.distinct(1))
      then have "(\<exists> z . (x,z) \<in> set (xs@[(x,z)]))" and "{z' . (x,z') \<in> set (xs@[(x,z)])} = {z}"
        by auto
      then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                   = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
        by force

      show ?thesis using m1 m2 snoc
        using \<open>xz = (x, z)\<close> by presburger
    next
      case (Some zs)
      then have **: "(?f (xs@[(x,z)])) = (?f xs) (x \<mapsto> (insert z zs))" using * by auto
      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto

      have m1: "(?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some (insert z zs) else (?f xs) x')"
        unfolding ** 
        unfolding scheme by force


      have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs"
        using Some snoc by auto
      then have "(\<exists> z . (x,z) \<in> set xs)"
        unfolding case_prod_conv using  option.distinct(2) by metis
      then have "(\<exists> z . (x,z) \<in> set (xs@[(x,z)]))" by simp

      have "{z' . (x,z') \<in> set (xs@[(x,z)])} = insert z zs"
      proof -
        have "Some {z . (x,z) \<in> set xs} = Some zs"
          using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs\<close>
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "{z . (x,z) \<in> set xs} = zs" by auto
        then show ?thesis by auto
      qed

      have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                   = (\<lambda> x' . if x' = x then Some (insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a" 
      proof -
        fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                   = (\<lambda> x' . if x' = x then Some (insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a"
        using \<open>{z' . (x,z') \<in> set (xs@[(x,z)])} = insert z zs\<close> \<open>(\<exists> z . (x,z) \<in> set (xs@[(x,z)]))\<close>
        by (cases "a = x"; auto)
      qed

      then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                   = (\<lambda> x' . if x' = x then Some (insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
        by auto


      show ?thesis using m1 m2 snoc
        using \<open>xz = (x, z)\<close> by presburger
    qed
  qed

  then show ?thesis
    unfolding set_as_map_def by simp
qed



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



end