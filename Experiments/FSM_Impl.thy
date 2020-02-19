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
definition set_as_map :: "('a \<times> 'b \<times> 'c) set \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c set option)" where
  "set_as_map s = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> s) then Some {z . (x,y,z) \<in> s} else None)"


lemma set_as_map_code[code] : "set_as_map (set xs) = (foldl (\<lambda> m (x,y,z) . case m (x,y) of
                                                                                  None \<Rightarrow> m ((x,y) \<mapsto> {z}) |
                                                                                  Some zs \<Rightarrow> m ((x,y) \<mapsto>  (insert z zs)))
                                                            Map.empty
                                                            xs)"
proof - 
  let ?f = "\<lambda> xs . (foldl (\<lambda> m (x,y,z) . case m (x,y) of
                                                                                  None \<Rightarrow> m ((x,y) \<mapsto> {z}) |
                                                                                  Some zs \<Rightarrow> m ((x,y) \<mapsto>  (insert z zs)))
                                                            Map.empty
                                                            xs)"
  have "(?f xs) = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None)"
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc xyz xs)
    then obtain x y z where "xyz = (x,y,z)" 
      by (metis (mono_tags, hide_lams) surj_pair)

    have *: "(?f (xs@[(x,y,z)])) = (case (?f xs) (x,y) of
                                None \<Rightarrow> (?f xs) ((x,y) \<mapsto> {z}) |
                                Some zs \<Rightarrow> (?f xs) ((x,y) \<mapsto> (insert z zs)))"
      by auto

    then show ?case proof (cases "(?f xs) (x,y)")
      case None
      then have **: "(?f (xs@[(x,y,z)])) = (?f xs) ((x,y) \<mapsto> {z})" using * by auto

      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto


      have m1: "(?f (xs@[(x,y,z)])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else (?f xs) (x',y'))"
        unfolding ** 
        unfolding scheme by force

      have "(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = None"
        using None snoc by auto
      then have "\<not>(\<exists> z . (x,y,z) \<in> set xs)"
        by (metis (mono_tags, lifting) case_prod_conv option.distinct(1))
      then have "(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))" and "{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = {z}"
        by auto
      then have m2: "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None)
                   = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y'))"
        by auto

      show ?thesis using m1 m2 snoc
        using \<open>xyz = (x, y, z)\<close> by presburger
    next
      case (Some zs)
      then have **: "(?f (xs@[(x,y,z)])) = (?f xs) ((x,y) \<mapsto> (insert z zs))" using * by auto
      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto

      have m1: "(?f (xs@[(x,y,z)])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (?f xs) (x',y'))"
        unfolding ** 
        unfolding scheme by force


      have "(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = Some zs"
        using Some snoc by auto
      then have "(\<exists> z . (x,y,z) \<in> set xs)"
        unfolding case_prod_conv using  option.distinct(2) by metis
      then have "(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))" by simp

      have "{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = insert z zs"
      proof -
        have "Some {z . (x,y,z) \<in> set xs} = Some zs"
          using \<open>(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = Some zs\<close>
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "{z . (x,y,z) \<in> set xs} = zs" by auto
        then show ?thesis by auto
      qed

      have "\<And> a b . (\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None) (a,b)
                   = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y')) (a,b)"
      proof -
        fix a b show "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None) (a,b)
                   = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y')) (a,b)"
        using \<open>{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = insert z zs\<close> \<open>(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))\<close>
        by (cases "(a,b) = (x,y)"; auto)
      qed

      then have m2: "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None)
                   = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y'))"
        by auto


      show ?thesis using m1 m2 snoc
        using \<open>xyz = (x, y, z)\<close> by presburger
    qed
  qed

  then show ?thesis
    unfolding set_as_map_def by simp
qed





type_synonym ('a,'b,'c) Transition = "('a \<times> 'b \<times> 'c \<times> 'a)"
abbreviation "t_source (a :: ('a,'b,'c) Transition) \<equiv> fst a" 
abbreviation "t_input  (a :: ('a,'b,'c) Transition) \<equiv> fst (snd a)"
abbreviation "t_output (a :: ('a,'b,'c) Transition) \<equiv> fst (snd (snd a))"
abbreviation "t_target (a :: ('a,'b,'c) Transition) \<equiv> snd (snd (snd a))"


fun fsm_impl_from_list :: "'a \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'a) list \<Rightarrow> ('a, 'b, 'c) fsm_impl" where
  "fsm_impl_from_list q [] = \<lparr> initial = q, nodes = {q}, inputs = {}, outputs = {}, transitions = {} \<rparr>" |
  "fsm_impl_from_list q (t#ts) = (let ts' = set (t#ts) 
                                   in \<lparr> initial = t_source t
                                      , nodes = (image t_source ts') \<union> (image t_target ts')
                                      , inputs = image t_input ts'
                                      , outputs = image t_output ts'
                                      , transitions = ts' \<rparr>)"



end