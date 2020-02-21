theory Util
  imports Main
begin

subsection \<open>Converting Sets to Maps\<close>

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


(* similar to set_as_map but retains the key as part of the value, i.e.
    (set_as_map {(a,b)} maps a to b while set_as_map2 {(a,b)} maps a to (a,b) *)
definition set_as_map2 :: "('a \<times> 'c) set \<Rightarrow> ('a \<Rightarrow> ('a \<times> 'c) set option)" where
  "set_as_map2 s = (\<lambda> x . if (\<exists> xy \<in> s . fst xy = x) then Some {xy \<in> s . fst xy = x} else None)"


lemma set_as_map_code2[code] : "set_as_map2 (set xs) = (foldl (\<lambda> m (x,z) . case m x of
                                                                                  None \<Rightarrow> m (x \<mapsto> {(x,z)}) |
                                                                                  Some zs \<Rightarrow> m (x \<mapsto>  (insert (x,z) zs)))
                                                            Map.empty
                                                            xs)"
proof - 
  let ?f = "\<lambda> xs . (foldl (\<lambda> m (x,z) . case m x of
                                                                                  None \<Rightarrow> m (x \<mapsto> {(x,z)}) |
                                                                                  Some zs \<Rightarrow> m (x \<mapsto>  (insert (x,z) zs)))
                                                            Map.empty
                                                            xs)"
  have "(?f xs) = (\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None)"
  proof (induction xs rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc xz xs)
    then obtain x z where "xz = (x,z)" 
      by (metis (mono_tags, hide_lams) surj_pair)

    have *: "(?f (xs@[(x,z)])) = (case (?f xs) x of
                                None \<Rightarrow> (?f xs) (x \<mapsto> {(x,z)}) |
                                Some zs \<Rightarrow> (?f xs) (x \<mapsto> (insert (x,z) zs)))"
      by auto

    then show ?case proof (cases "(?f xs) x")
      case None
      then have **: "(?f (xs@[(x,z)])) = (?f xs) (x \<mapsto> {(x,z)})" using * by auto

      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto


      have m1: "(?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some {(x,z)} else (?f xs) x')"
        unfolding ** 
        unfolding scheme by force

      have "(\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x = None"
        using None snoc by auto
      then have "\<not>(\<exists> xy \<in> set xs . fst xy = x)"
        by (metis (mono_tags, lifting) case_prod_conv option.distinct(1))
      then have "(\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x)" and "{xy \<in> set (xs@[(x,z)]) . fst xy = x} = {(x,z)}"
        by auto
      then have m2: "(\<lambda> x' . if (\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x') then Some {xy \<in> set (xs@[(x,z)]) . fst xy = x'} else None)
                   = (\<lambda> x' . if x' = x then Some {(x,z)} else (\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x') then Some {xy \<in> set xs . fst xy = x'} else None) x')"
        by force        

      show ?thesis using m1 m2 snoc
        using \<open>xz = (x, z)\<close> by presburger
    next
      case (Some zs)
      then have **: "(?f (xs@[(x,z)])) = (?f xs) (x \<mapsto> (insert (x,z) zs))" using * by auto
      have scheme: "\<And> m k v . (m(k \<mapsto> v)) = (\<lambda>k' . if k' = k then Some v else m k')"
        by auto

      have m1: "(?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some (insert (x,z) zs) else (?f xs) x')"
        unfolding ** 
        unfolding scheme by force


      have "(\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x = Some zs"
        using Some snoc by auto
      then have "(\<exists> xy \<in> set xs . fst xy = x)"
        unfolding case_prod_conv using  option.distinct(2) by metis
      then have "(\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x)" by simp

      have "{xy \<in> set (xs@[(x,z)]) . fst xy = x} = insert (x,z) zs"
      proof -
        have "Some {xy \<in> set xs . fst xy = x} = Some zs"
          using \<open>(\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x = Some zs\<close>
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "{xy \<in> set xs . fst xy = x} = zs" by auto
        then show ?thesis by auto
      qed

      have "\<And> a  . (\<lambda> x' . if (\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x') then Some {xy \<in> set (xs@[(x,z)]) . fst xy = x'} else None) a
                   = (\<lambda> x' . if x' = x then Some (insert (x,z) zs) else (\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x') a" 
      proof -
        fix a show "(\<lambda> x' . if (\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x') then Some {xy \<in> set (xs@[(x,z)]) . fst xy = x'} else None) a
                   = (\<lambda> x' . if x' = x then Some (insert (x,z) zs) else (\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x') a"
        proof (cases "a = x")
          case True
          show ?thesis unfolding True using \<open>{xy \<in> set (xs@[(x,z)]) . fst xy = x} = insert (x,z) zs\<close> \<open>(\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x)\<close> by force
        next
          case False
          then show ?thesis by force
        qed
      qed


      then have m2: "(\<lambda> x' . if (\<exists> xy \<in> set (xs@[(x,z)]) . fst xy = x') then Some {xy \<in> set (xs@[(x,z)]) . fst xy = x'} else None)
                   = (\<lambda> x' . if x' = x then Some (insert (x,z) zs) else (\<lambda> x . if (\<exists> xy \<in> set xs . fst xy = x) then Some {xy \<in> set xs . fst xy = x} else None) x')"
        by auto


      show ?thesis using m1 m2 snoc
        using \<open>xz = (x, z)\<close> by presburger
    qed
  qed

  then show ?thesis
    unfolding set_as_map2_def by simp
qed

end