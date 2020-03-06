theory Util
  imports Main HOL.Finite_Set
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
        by (metis (mono_tags, lifting) option.distinct(1))
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
        by (metis (mono_tags, lifting) option.distinct(1))
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


section \<open>Utility Lemmata\<close>

subsection \<open>Find\<close>

lemma find_result_props : 
  assumes "find P xs = Some x" 
  shows "x \<in> set xs" and "P x"
proof -
  show "x \<in> set xs" using assms by (metis find_Some_iff nth_mem)
  show "P x" using assms by (metis find_Some_iff)
qed

lemma find_set : 
  assumes "find P xs = Some x"
  shows "x \<in> set xs"
using assms proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis find.simps(2) list.set_intros(1) list.set_intros(2) option.inject) 
qed

lemma find_condition : 
  assumes "find P xs = Some x"
  shows "P x"
using assms proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis find.simps(2) option.inject)     
qed

lemma find_from : 
  assumes "\<exists> x \<in> set xs . P x"
  shows "find P xs \<noteq> None"
  by (metis assms find_None_iff)


lemma find_sort_containment :
  assumes "find P (sort xs) = Some x"
shows "x \<in> set xs"
  using assms find_set by force


lemma find_sort_index :
  assumes "find P xs = Some x"
  shows "\<exists> i < length xs . xs ! i = x \<and> (\<forall> j < i . \<not> P (xs ! j))"
using assms proof (induction xs arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  show ?case proof (cases "P a")
    case True
    then show ?thesis 
      using Cons.prems unfolding find.simps by auto
  next
    case False
    then have "find P (a#xs) = find P xs"
      unfolding find.simps by auto
    then have "find P xs = Some x"
      using Cons.prems by auto
    then show ?thesis 
      using Cons.IH False
      by (metis Cons.prems find_Some_iff)  
  qed
qed


lemma find_sort_least :
  assumes "find P (sort xs) = Some x"
  shows "\<forall> x' \<in> set xs . x \<le> x' \<or> \<not> P x'"
  and   "x = (LEAST x' \<in> set xs . P x')"
proof -
  obtain i where "i < length (sort xs)" and "(sort xs) ! i = x" and "(\<forall> j < i . \<not> P ((sort xs) ! j))"
    using find_sort_index[OF assms] by blast
  
  have "\<And> j . j > i \<Longrightarrow> j < length xs \<Longrightarrow> (sort xs) ! i \<le> (sort xs) ! j"
    by (simp add: sorted_nth_mono)
  then have "\<And> j . j < length xs \<Longrightarrow> (sort xs) ! i \<le> (sort xs) ! j \<or> \<not> P ((sort xs) ! j)"
    using \<open>(\<forall> j < i . \<not> P ((sort xs) ! j))\<close>
    by (metis not_less_iff_gr_or_eq order_refl) 
  then show "\<forall> x' \<in> set xs . x \<le> x' \<or> \<not> P x'"
    by (metis \<open>sort xs ! i = x\<close> in_set_conv_nth length_sort set_sort)
  then show "x = (LEAST x' \<in> set xs . P x')"
    using find_set[OF assms] find_condition[OF assms]
    by (metis (mono_tags, lifting) Least_equality set_sort) 
qed





subsection \<open>Enumerating Lists\<close>

fun lists_of_length :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "lists_of_length T 0 = [[]]" |
  "lists_of_length T (Suc n) = concat (map (\<lambda> xs . map (\<lambda> x . x#xs) T ) (lists_of_length T n))" 

lemma lists_of_length_containment :
  assumes "set xs \<subseteq> set T"
  and     "length xs = n"
shows "xs \<in> set (lists_of_length T n)"
using assms proof (induction xs arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then obtain k where "n = Suc k" 
    by auto
  then have "xs \<in> set (lists_of_length T k)" 
    using Cons by auto
  moreover have "a \<in> set T" 
    using Cons by auto
  ultimately show ?case 
    using \<open>n = Suc k\<close> by auto
qed


lemma lists_of_length_length :
  assumes "xs \<in> set (lists_of_length T n)"
  shows "length xs = n"
proof -
  have "\<forall> xs \<in> set (lists_of_length T n) . length xs = n"
    by (induction n; simp)
  then show ?thesis using assms by blast
qed

lemma lists_of_length_elems :
  assumes "xs \<in> set (lists_of_length T n)"
  shows "set xs \<subseteq> set T"
proof -
  have "\<forall> xs \<in> set (lists_of_length T n) . set xs \<subseteq> set T"
    by (induction n; simp)
  then show ?thesis using assms by blast
qed
  
lemma lists_of_length_list_set : "set (lists_of_length xs k) = {xs' . length xs' = k \<and> set xs' \<subseteq> set xs}"
  using lists_of_length_containment[of _ xs k] lists_of_length_length[of _ xs k] lists_of_length_elems[of _ xs k] by blast
    

value "lists_of_length [1,2,3::nat] 3"




fun cartesian_product_list :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list" where 
  "cartesian_product_list xs ys = concat (map (\<lambda> x . map (\<lambda> y . (x,y)) ys) xs)"

value "cartesian_product_list [1,2,3::nat] [10,20,30::nat]"

lemma cartesian_product_list_set : "set (cartesian_product_list xs ys) = {(x,y) | x y . x \<in> set xs \<and> y \<in> set ys}"
  by auto



subsection \<open>Filter\<close>

lemma filter_double :
  assumes "x \<in> set (filter P1 xs)"
  and     "P2 x"
shows "x \<in> set (filter P2 (filter P1 xs))"
  by (metis (no_types) assms(1) assms(2) filter_set member_filter)

lemma filter_list_set :
  assumes "x \<in> set xs"
  and     "P x"
shows "x \<in> set (filter P xs)"
  by (simp add: assms(1) assms(2))

lemma filter_list_set_not_contained :
  assumes "x \<in> set xs"
  and     "\<not> P x"
shows "x \<notin> set (filter P xs)"
  by (simp add: assms(1) assms(2))


lemma filter_map_elem : "t \<in> set (map g (filter f xs)) \<Longrightarrow> \<exists> x \<in> set xs . f x \<and> t = g x" by auto


subsection \<open>Concat\<close>

lemma concat_map_elem :
  assumes "y \<in> set (concat (map f xs))"
  obtains x where "x \<in> set xs"
              and "y \<in> set (f x)"
using assms proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
  proof (cases "y \<in> set (f a)")
    case True
    then show ?thesis 
      using Cons.prems(1) by auto
  next
    case False
    then have "y \<in> set (concat (map f xs))"
      using Cons by auto
    have "\<exists> x . x \<in> set xs \<and> y \<in> set (f x)"  
    proof (rule ccontr)
      assume "\<not>(\<exists>x. x \<in> set xs \<and> y \<in> set (f x))"
      then have "\<not>(y \<in> set (concat (map f xs)))"
        by auto
      then show False 
        using \<open>y \<in> set (concat (map f xs))\<close> by auto
    qed
    then show ?thesis
      using Cons.prems(1) by auto     
  qed
qed

lemma set_concat_map_sublist :
  assumes "x \<in> set (concat (map f xs))"
  and     "set xs \<subseteq> set xs'"
shows "x \<in> set (concat (map f xs'))"
using assms by (induction xs) (auto)

lemma set_concat_map_elem :
  assumes "x \<in> set (concat (map f xs))"
  shows "\<exists> x' \<in> set xs . x \<in> set (f x')"
using assms by auto

lemma concat_replicate_length : "length (concat (replicate n xs)) = n * (length xs)"
  by (induction n; simp)


subsection \<open>Enumerating List Subsets\<close>

fun generate_selector_lists :: "nat \<Rightarrow> bool list list" where
  "generate_selector_lists k = lists_of_length [False,True] k"
  

value "generate_selector_lists 4"

lemma generate_selector_lists_set : "set (generate_selector_lists k) = {(bs :: bool list) . length bs = k}"
  using lists_of_length_list_set by auto 

lemma selector_list_index_set:
  assumes "length ms = length bs"
  shows "set (map fst (filter snd (zip ms bs))) = { ms ! i | i . i < length bs \<and> bs ! i}"
using assms proof (induction bs arbitrary: ms rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc b bs)
  let ?ms = "butlast ms"
  let ?m = "last ms"

  have "length ?ms = length bs" using snoc.prems by auto

  have "map fst (filter snd (zip ms (bs @ [b]))) = (map fst (filter snd (zip ?ms bs))) @ (map fst (filter snd (zip [?m] [b])))"
    by (metis \<open>length (butlast ms) = length bs\<close> append_eq_conv_conj filter_append length_0_conv map_append snoc.prems snoc_eq_iff_butlast zip_append2)
  then have *: "set (map fst (filter snd (zip ms (bs @ [b])))) = set (map fst (filter snd (zip ?ms bs))) \<union> set (map fst (filter snd (zip [?m] [b])))"
    by simp
    

  have "{ms ! i |i. i < length (bs @ [b]) \<and> (bs @ [b]) ! i} = {ms ! i |i. i \<le> (length bs) \<and> (bs @ [b]) ! i}"
    by auto
  moreover have "{ms ! i |i. i \<le> (length bs) \<and> (bs @ [b]) ! i} = {ms ! i |i. i < length bs \<and> (bs @ [b]) ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    by fastforce
  moreover have "{ms ! i |i. i < length bs \<and> (bs @ [b]) ! i} = {?ms ! i |i. i < length bs \<and> bs ! i}"
    using \<open>length ?ms = length bs\<close> by (metis butlast_snoc nth_butlast)  
  ultimately have **: "{ms ! i |i. i < length (bs @ [b]) \<and> (bs @ [b]) ! i} = {?ms ! i |i. i < length bs \<and> bs ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    by simp
  

  have "set (map fst (filter snd (zip [?m] [b]))) = {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
  proof (cases b)
    case True
    then have "set (map fst (filter snd (zip [?m] [b]))) = {?m}" by fastforce
    moreover have "{ms ! i |i. i = length bs \<and> (bs @ [b]) ! i} = {?m}" 
    proof -
      have "(bs @ [b]) ! length bs"
        by (simp add: True) 
      moreover have "ms ! length bs = ?m"
        by (metis last_conv_nth length_0_conv length_butlast snoc.prems snoc_eq_iff_butlast) 
      ultimately show ?thesis by fastforce
    qed
    ultimately show ?thesis by auto
  next
    case False
    then show ?thesis by auto
  qed

  then have "set (map fst (filter snd (zip (butlast ms) bs))) \<union> set (map fst (filter snd (zip [?m] [b])))
             = {butlast ms ! i |i. i < length bs \<and> bs ! i} \<union> {ms ! i |i. i = length bs \<and> (bs @ [b]) ! i}"
    using snoc.IH[OF \<open>length ?ms = length bs\<close>] by blast

  then show ?case using * **
    by simp 
qed

lemma selector_list_ex :
  assumes "set xs \<subseteq> set ms"
  shows "\<exists> bs . length bs = length ms \<and> set xs = set (map fst (filter snd (zip ms bs)))"
using assms proof (induction xs rule: rev_induct)
  case Nil
  let ?bs = "replicate (length ms) False"
  have "set [] = set (map fst (filter snd (zip ms ?bs)))"
    by (metis filter_False in_set_zip length_replicate list.simps(8) nth_replicate)
  moreover have "length ?bs = length ms" by auto
  ultimately show ?case by blast
next
  case (snoc a xs)
  then have "set xs \<subseteq> set ms" and "a \<in> set ms" by auto
  then obtain bs where "length bs = length ms" and "set xs = set (map fst (filter snd (zip ms bs)))" using snoc.IH by auto

  from \<open>a \<in> set ms\<close> obtain i where "i < length ms" and "ms ! i = a"
    by (meson in_set_conv_nth) 

  let ?bs = "list_update bs i True"
  have "length ms = length ?bs" using \<open>length bs = length ms\<close> by auto
  have "length ?bs = length bs" by auto

  have "set (map fst (filter snd (zip ms ?bs))) = {ms ! i |i. i < length ?bs \<and> ?bs ! i}"
    using selector_list_index_set[OF \<open>length ms = length ?bs\<close>] by assumption

  have "\<And> j . j < length ?bs \<Longrightarrow> j \<noteq> i \<Longrightarrow> ?bs ! j = bs ! j"
    by auto
  then have "{ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j} = {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}"
    using \<open>length ?bs = length bs\<close> by fastforce
  
  
  
  have "{ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j} = {a}"
    using \<open>length bs = length ms\<close> \<open>i < length ms\<close> \<open>ms ! i = a\<close> by auto
  then have "{ms ! i |i. i < length ?bs \<and> ?bs ! i} = insert a {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}"
    by fastforce
  

  have "{ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<subseteq> {ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j}"
    by (simp add: Collect_mono)
  then have "{ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<subseteq> {a}"
    using \<open>{ms ! j |j. j < length ?bs \<and> j = i \<and> ?bs ! j} = {a}\<close> by auto
  moreover have "{ms ! j |j. j < length bs \<and> bs ! j} = {ms ! j |j. j < length bs \<and> j = i \<and> bs ! j} \<union> {ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j}"
    by fastforce

  ultimately have "{ms ! i |i. i < length ?bs \<and> ?bs ! i} = insert a {ms ! i |i. i < length bs \<and> bs ! i}"
    using \<open>{ms ! j |j. j < length bs \<and> j \<noteq> i \<and> bs ! j} = {ms ! j |j. j < length ?bs \<and> j \<noteq> i \<and> ?bs ! j}\<close>
    using \<open>{ms ! ia |ia. ia < length (bs[i := True]) \<and> bs[i := True] ! ia} = insert a {ms ! j |j. j < length (bs[i := True]) \<and> j \<noteq> i \<and> bs[i := True] ! j}\<close> by auto 

  moreover have "set (map fst (filter snd (zip ms bs))) = {ms ! i |i. i < length bs \<and> bs ! i}"
    using selector_list_index_set[of ms bs] \<open>length bs = length ms\<close> by auto

  ultimately have "set (a#xs) = set (map fst (filter snd (zip ms ?bs)))"
    using \<open>set (map fst (filter snd (zip ms ?bs))) = {ms ! i |i. i < length ?bs \<and> ?bs ! i}\<close> \<open>set xs = set (map fst (filter snd (zip ms bs)))\<close> by auto
  then show ?case
    using \<open>length ms = length ?bs\<close>
    by (metis Un_commute insert_def list.set(1) list.simps(15) set_append singleton_conv) 
qed

subsection \<open>Enumerating Choices from Lists of Lists\<close>


fun generate_choices :: "('a \<times> ('b list)) list \<Rightarrow> ('a \<times> 'b option) list list" where
  "generate_choices [] = [[]]" |
  "generate_choices (xys#xyss) = concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') (generate_choices xyss)) ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys))))"

value "generate_choices [(0::nat,[0::nat,1,2])]"
value "generate_choices [(0::nat,[0::nat,1]),(1,[10,20])]"

lemma concat_map_hd_tl_elem: 
  assumes "hd cs \<in> set P1"
  and     "tl cs \<in> set P2"
  and     "length cs > 0"
shows "cs \<in> set (concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') P2) P1))"
proof -
  have "hd cs # tl cs = cs" using assms(3) by auto
  moreover have "hd cs # tl cs \<in> set (concat (map (\<lambda> xy' . map (\<lambda> xys' . xy' # xys') P2) P1))" using assms(1,2) by auto
  ultimately show ?thesis by auto
qed





lemma generate_choices_hd_tl : "cs \<in> set (generate_choices (xys#xyss)) = (length cs = length (xys#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices xyss)))"
proof (induction xyss arbitrary: cs xys)
  case Nil
  have "(cs \<in> set (generate_choices [xys])) = (cs \<in> set ([(fst xys, None)] # map (\<lambda>y. [(fst xys, Some y)]) (snd xys)))" 
    unfolding generate_choices.simps by auto
  moreover have "(cs \<in> set ([(fst xys, None)] # map (\<lambda>y. [(fst xys, Some y)]) (snd xys))) \<Longrightarrow> (length cs = length [xys] \<and>
     fst (hd cs) = fst xys \<and>
     (snd (hd cs) = None \<or> snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)) \<and>
     tl cs \<in> set (generate_choices []))"
    by auto
  moreover have "(length cs = length [xys] \<and>
     fst (hd cs) = fst xys \<and>
     (snd (hd cs) = None \<or> snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)) \<and>
     tl cs \<in> set (generate_choices [])) \<Longrightarrow> (cs \<in> set ([(fst xys, None)] # map (\<lambda>y. [(fst xys, Some y)]) (snd xys)))"
    unfolding generate_choices.simps(1)
  proof -
    assume a1: "length cs = length [xys] \<and> fst (hd cs) = fst xys \<and> (snd (hd cs) = None \<or> snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)) \<and> tl cs \<in> set [[]]"
    have f2: "\<forall>ps. ps = [] \<or> ps = (hd ps::'a \<times> 'b option) # tl ps"
      by (meson list.exhaust_sel)
    have f3: "cs \<noteq> []"
      using a1 by fastforce
    have "snd (hd cs) = None \<longrightarrow> (fst xys, None) = hd cs"
      using a1 by (metis prod.exhaust_sel)
    moreover
    { assume "hd cs # tl cs \<noteq> [(fst xys, Some (the (snd (hd cs))))]"
      then have "snd (hd cs) = None"
        using a1 by (metis (no_types) length_0_conv length_tl list.sel(3) option.collapse prod.exhaust_sel) }
    ultimately have "cs \<in> insert [(fst xys, None)] ((\<lambda>b. [(fst xys, Some b)]) ` set (snd xys))"
      using f3 f2 a1 by fastforce
    then show ?thesis
      by simp
  qed 
  ultimately show ?case by blast
next
  case (Cons a xyss)

  have "length cs = length (xys#a#xyss) \<Longrightarrow> fst (hd cs) = fst xys \<Longrightarrow> (snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))) \<Longrightarrow> (tl cs \<in> set (generate_choices (a#xyss))) \<Longrightarrow> cs \<in> set (generate_choices (xys#a#xyss)) "
  proof -
    assume "length cs = length (xys#a#xyss)" and "fst (hd cs) = fst xys" and "(snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))" and "(tl cs \<in> set (generate_choices (a#xyss)))"
    then have "length cs > 0" by auto

    have "(hd cs) \<in> set ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys)))"
      using \<open>fst (hd cs) = fst xys\<close> \<open>(snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))\<close>
      by (metis (no_types, lifting) image_eqI list.set_intros(1) list.set_intros(2) option.collapse prod.collapse set_map)  
    
    show "cs \<in> set (generate_choices ((xys#(a#xyss))))"
      using generate_choices.simps(2)[of xys "a#xyss"] using concat_map_hd_tl_elem[OF \<open>(hd cs) \<in> set ((fst xys, None) # (map (\<lambda> y . (fst xys, Some y)) (snd xys)))\<close> \<open>(tl cs \<in> set (generate_choices (a#xyss)))\<close> \<open>length cs > 0\<close>] by auto
  qed

  moreover have "cs \<in> set (generate_choices (xys#a#xyss)) \<Longrightarrow> length cs = length (xys#a#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices (a#xyss)))"
  proof -
    assume "cs \<in> set (generate_choices (xys#a#xyss))"
    then have p3: "tl cs \<in> set (generate_choices (a#xyss))"
      using generate_choices.simps(2)[of xys "a#xyss"] by fastforce
    then have "length (tl cs) = length (a # xyss)" using Cons.IH[of "tl cs" "a"] by simp
    then have p1: "length cs = length (xys#a#xyss)" by auto

    have p2 : "fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))))"
      using \<open>cs \<in> set (generate_choices (xys#a#xyss))\<close> generate_choices.simps(2)[of xys "a#xyss"] by fastforce
    
    show ?thesis using p1 p2 p3 by simp
  qed

  ultimately show ?case by blast
qed 

lemma list_append_idx_prop : 
  "(\<forall> i . (i < length xs \<longrightarrow> P (xs ! i))) = (\<forall> j . ((j < length (ys@xs) \<and> j \<ge> length ys) \<longrightarrow> P ((ys@xs) ! j)))"
proof -
  have "\<And> j . \<forall>i<length xs. P (xs ! i) \<Longrightarrow> j < length (ys @ xs) \<Longrightarrow> length ys \<le> j \<longrightarrow> P ((ys @ xs) ! j)"
    by (simp add: nth_append)
  moreover have "\<And> i . (\<forall> j . ((j < length (ys@xs) \<and> j \<ge> length ys) \<longrightarrow> P ((ys@xs) ! j))) \<Longrightarrow> i < length xs \<Longrightarrow> P (xs ! i)"
  proof -
    fix i assume "(\<forall> j . ((j < length (ys@xs) \<and> j \<ge> length ys) \<longrightarrow> P ((ys@xs) ! j)))" and "i < length xs"
    then have "P ((ys@xs) ! (length ys + i))"
      by (metis add_strict_left_mono le_add1 length_append)
    moreover have "P (xs ! i) = P ((ys@xs) ! (length ys + i))"
      by simp
    ultimately show "P (xs ! i)" by blast
  qed
  ultimately show ?thesis by blast
qed

lemma list_append_idx_prop2 : 
  assumes "length xs' = length xs"
      and "length ys' = length ys"
  shows "(\<forall> i . (i < length xs \<longrightarrow> P (xs ! i) (xs' ! i))) = (\<forall> j . ((j < length (ys@xs) \<and> j \<ge> length ys) \<longrightarrow> P ((ys@xs) ! j) ((ys'@xs') ! j)))"
proof -

  have "\<forall>i<length xs. P (xs ! i) (xs' ! i) \<Longrightarrow>
    \<forall>j. j < length (ys @ xs) \<and> length ys \<le> j \<longrightarrow> P ((ys @ xs) ! j) ((ys' @ xs') ! j)"
    using assms
  proof -
    assume a1: "\<forall>i<length xs. P (xs ! i) (xs' ! i)"
    { fix nn :: nat
      have ff1: "\<forall>n na. (na::nat) + n - n = na"
        by simp
      have ff2: "\<forall>n na. (na::nat) \<le> n + na"
        by auto
      then have ff3: "\<forall>as n. (ys' @ as) ! n = as ! (n - length ys) \<or> \<not> length ys \<le> n"
        using ff1 by (metis (no_types) add.commute assms(2) eq_diff_iff nth_append_length_plus)
      have ff4: "\<forall>n bs bsa. ((bsa @ bs) ! n::'b) = bs ! (n - length bsa) \<or> \<not> length bsa \<le> n"
        using ff2 ff1 by (metis (no_types) add.commute eq_diff_iff nth_append_length_plus)
      have "\<forall>n na nb. ((n::nat) + nb \<le> na \<or> \<not> n \<le> na - nb) \<or> \<not> nb \<le> na"
        using ff2 ff1 by (metis le_diff_iff)
      then have "(\<not> nn < length (ys @ xs) \<or> \<not> length ys \<le> nn) \<or> P ((ys @ xs) ! nn) ((ys' @ xs') ! nn)"
        using ff4 ff3 a1 by (metis add.commute length_append not_le) }
    then show ?thesis
      by blast
  qed

  moreover have "(\<forall>j. j < length (ys @ xs) \<and> length ys \<le> j \<longrightarrow> P ((ys @ xs) ! j) ((ys' @ xs') ! j)) \<Longrightarrow>\<forall>i<length xs. P (xs ! i) (xs' ! i)"
    using assms
    by (metis le_add1 length_append nat_add_left_cancel_less nth_append_length_plus) 

  ultimately show ?thesis by blast
qed

lemma generate_choices_idx : "cs \<in> set (generate_choices xyss) = (length cs = length xyss \<and> (\<forall> i < length cs . (fst (cs ! i)) = (fst (xyss ! i)) \<and> ((snd (cs ! i)) = None \<or> ((snd (cs ! i)) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd (xyss ! i))))))"
proof (induction xyss arbitrary: cs)
  case Nil
  then show ?case by auto
next
  case (Cons xys xyss)



  have "cs \<in> set (generate_choices (xys#xyss)) = (length cs = length (xys#xyss) \<and> fst (hd cs) = fst xys \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) \<and> (tl cs \<in> set (generate_choices xyss)))"
    using generate_choices_hd_tl by metis

  then have "cs \<in> set (generate_choices (xys#xyss)) 
    = (length cs = length (xys#xyss) 
      \<and> fst (hd cs) = fst xys 
      \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) 
      \<and> (length (tl cs) = length xyss \<and>
        (\<forall>i<length (tl cs).
          fst (tl cs ! i) = fst (xyss ! i) \<and>
          (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i))))))"
    using Cons.IH[of "tl cs"] by blast
  then have *: "cs \<in> set (generate_choices (xys#xyss)) 
    = (length cs = length (xys#xyss) 
      \<and> fst (hd cs) = fst xys 
      \<and> ((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys)))) 
      \<and> (\<forall>i<length (tl cs).
          fst (tl cs ! i) = fst (xyss ! i) \<and>
          (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i)))))"
    by auto


  have "cs \<in> set (generate_choices (xys#xyss)) \<Longrightarrow> (length cs = length (xys # xyss) \<and>
                    (\<forall>i<length cs.
                        fst (cs ! i) = fst ((xys # xyss) ! i) \<and>
                        (snd (cs ! i) = None \<or>
                        snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys # xyss) ! i)))))"
  proof -
    assume "cs \<in> set (generate_choices (xys#xyss))"
    then have p1: "length cs = length (xys#xyss)"
          and p2: "fst (hd cs) = fst xys "
          and p3: "((snd (hd cs) = None \<or> (snd (hd cs) \<noteq> None \<and> the (snd (hd cs)) \<in> set (snd xys))))"
          and p4: "(\<forall>i<length (tl cs).
                  fst (tl cs ! i) = fst (xyss ! i) \<and>
                  (snd (tl cs ! i) = None \<or> snd (tl cs ! i) \<noteq> None \<and> the (snd (tl cs ! i)) \<in> set (snd (xyss ! i))))"
      using * by blast+
    then have "length xyss = length (tl cs)" and "length (xys # xyss) = length ([hd cs] @ tl cs)"
      by auto
    
    have "[hd cs]@(tl cs) = cs"
      by (metis (no_types) p1 append.left_neutral append_Cons length_greater_0_conv list.collapse list.simps(3)) 
    then have p4b: "(\<forall>i<length cs. i > 0 \<longrightarrow>
                    (fst (cs ! i) = fst ((xys#xyss) ! i) \<and>
                      (snd (cs ! i) = None \<or> snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys#xyss) ! i)))))"
      using p4 list_append_idx_prop2[of xyss "tl cs" "xys#xyss" "[hd cs]@(tl cs)" "\<lambda> x y . fst x = fst y \<and>
                    (snd x = None \<or> snd x \<noteq> None \<and> the (snd x) \<in> set (snd y))", OF \<open>length xyss = length (tl cs)\<close> \<open>length (xys # xyss) = length ([hd cs] @ tl cs)\<close>]
      by (metis (no_types, lifting) One_nat_def Suc_pred \<open>length (xys # xyss) = length ([hd cs] @ tl cs)\<close> \<open>length xyss = length (tl cs)\<close> length_Cons list.size(3) not_less_eq nth_Cons_pos nth_append) 

    have p4a :"(fst (cs ! 0) = fst ((xys#xyss) ! 0) \<and> (snd (cs ! 0) = None \<or> snd (cs ! 0) \<noteq> None \<and> the (snd (cs ! 0)) \<in> set (snd ((xys#xyss) ! 0))))"
      using p1 p2 p3 by (metis hd_conv_nth length_greater_0_conv list.simps(3) nth_Cons_0)

    show ?thesis using p1 p4a p4b by fastforce
  qed


  moreover have "(length cs = length (xys # xyss) \<and>
                    (\<forall>i<length cs.
                        fst (cs ! i) = fst ((xys # xyss) ! i) \<and>
                        (snd (cs ! i) = None \<or>
                        snd (cs ! i) \<noteq> None \<and> the (snd (cs ! i)) \<in> set (snd ((xys # xyss) ! i))))) \<Longrightarrow> cs \<in> set (generate_choices (xys#xyss))"
    using * 
    by (metis (no_types, lifting) Nitpick.size_list_simp(2) Suc_mono hd_conv_nth length_greater_0_conv length_tl list.sel(3) list.simps(3) nth_Cons_0 nth_tl) 

  ultimately show ?case by blast
qed


subsection \<open>Finding the Index of the First Element of a List Satisfying a Property\<close>


fun find_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_index f []  = None" |
  "find_index f (x#xs) = (if f x then Some 0 else (case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None))" 

lemma find_index_index :
  assumes "find_index f xs = Some k"
  shows "k < length xs" and "f (xs ! k)" and "\<And> j . j < k \<Longrightarrow> \<not> f (xs ! j)"
proof -
  have "(k < length xs) \<and> (f (xs ! k)) \<and> (\<forall> j < k . \<not> (f (xs ! j)))"
    using assms proof (induction xs arbitrary: k)
    case Nil
    then show ?case by auto
  next
    case (Cons x xs)
    
    show ?case proof (cases "f x")
      case True
      then show ?thesis using Cons.prems by auto
    next
      case False
      then have "find_index f (x#xs) = (case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None)"
        by auto
      then have "(case find_index f xs of Some k \<Rightarrow> Some (Suc k) | None \<Rightarrow> None) = Some k"
        using Cons.prems by auto
      then obtain k' where "find_index f xs = Some k'" and "k = Suc k'"
        by (metis option.case_eq_if option.collapse option.distinct(1) option.sel)
        
      have "k < length (x # xs) \<and> f ((x # xs) ! k)" using Cons.IH[OF \<open>find_index f xs = Some k'\<close>] using \<open>k = Suc k'\<close> by auto
      moreover have "(\<forall>j<k. \<not> f ((x # xs) ! j))"
        using Cons.IH[OF \<open>find_index f xs = Some k'\<close>] using \<open>k = Suc k'\<close> False
        using less_Suc_eq_0_disj by auto 
      ultimately show ?thesis by presburger
    qed
  qed
  then show "k < length xs" and "f (xs ! k)" and "\<And> j . j < k \<Longrightarrow> \<not> f (xs ! j)" by simp+
qed

lemma find_index_exhaustive : 
  assumes "\<exists> x \<in> set xs . f x"
  shows "find_index f xs \<noteq> None"
  using assms proof (induction xs)
case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case by (cases "f x"; auto)
qed



subsection \<open>List Distinctness from Sorting\<close>

lemma non_distinct_repetition_indices :
  assumes "\<not> distinct xs"
  shows "\<exists> i j . i < j \<and> j < length xs \<and> xs ! i = xs ! j"
  by (metis assms distinct_conv_nth le_neq_implies_less not_le)

lemma ordered_list_distinct :
  fixes xs :: "('a::preorder) list"
  assumes "\<And> i . Suc i < length xs \<Longrightarrow> (xs ! i) < (xs ! (Suc i))"
  shows "distinct xs"
proof -
  have "\<And> i j . i < j \<Longrightarrow> j < length xs \<Longrightarrow> (xs ! i) < (xs ! j)"
  proof -
    fix i j assume "i < j" and "j < length xs"
    then show "xs ! i < xs ! j"
      using assms proof (induction xs arbitrary: i j rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a xs)
      show ?case proof (cases "j < length xs")
        case True
        show ?thesis using snoc.IH[OF snoc.prems(1) True] snoc.prems(3)
        proof -
          have f1: "i < length xs"
            using True less_trans snoc.prems(1) by blast
          have f2: "\<forall>is isa n. if n < length is then (is @ isa) ! n = (is ! n::integer) else (is @ isa) ! n = isa ! (n - length is)"
            by (meson nth_append)
          then have f3: "(xs @ [a]) ! i = xs ! i"
            using f1
            by (simp add: nth_append)
          have "xs ! i < xs ! j"
            using f2
            by (metis Suc_lessD \<open>(\<And>i. Suc i < length xs \<Longrightarrow> xs ! i < xs ! Suc i) \<Longrightarrow> xs ! i < xs ! j\<close> butlast_snoc length_append_singleton less_SucI nth_butlast snoc.prems(3)) 
          then show ?thesis
            using f3 f2 True
            by (simp add: nth_append) 
        qed
      next
        case False
        then have "(xs @ [a]) ! j = a"
          using snoc.prems(2)
          by (metis length_append_singleton less_SucE nth_append_length)  
        
        consider "j = 1" | "j > 1"
          using \<open>i < j\<close>
          by linarith 
        then show ?thesis proof cases
          case 1
          then have "i = 0" and "j = Suc i" using \<open>i < j\<close> by linarith+ 
          then show ?thesis 
            using snoc.prems(3)
            using snoc.prems(2) by blast 
        next
          case 2
          then consider "i < j - 1" | "i = j - 1" using \<open>i < j\<close> by linarith+
          then show ?thesis proof cases
            case 1
            
            have "(\<And>i. Suc i < length xs \<Longrightarrow> xs ! i < xs ! Suc i) \<Longrightarrow> xs ! i < xs ! (j - 1)"
              using snoc.IH[OF 1] snoc.prems(2) 2 by simp 
            then have le1: "(xs @ [a]) ! i < (xs @ [a]) ! (j -1)"
              using snoc.prems(2)
              by (metis "2" False One_nat_def Suc_diff_Suc Suc_lessD diff_zero length_append_singleton less_SucE not_less_eq nth_append snoc.prems(1) snoc.prems(3))
            moreover have le2: "(xs @ [a]) ! (j -1) < (xs @ [a]) ! j"
              using snoc.prems(2,3) 2
              by (metis (full_types) One_nat_def Suc_diff_Suc diff_zero less_numeral_extra(1) less_trans)  
            ultimately show ?thesis 
              using less_trans by blast
          next
            case 2
            then have "j = Suc i" using \<open>1 < j\<close> by linarith
            then show ?thesis 
              using snoc.prems(3)
              using snoc.prems(2) by blast
          qed
        qed
      qed
    qed 
  qed

  then show ?thesis
    by (metis less_asym non_distinct_repetition_indices)
qed




lemma ordered_list_distinct_rev :
  fixes xs :: "('a::preorder) list"
  assumes "\<And> i . Suc i < length xs \<Longrightarrow> (xs ! i) > (xs ! (Suc i))"
  shows "distinct xs"
proof -
  have "\<And> i . Suc i < length (rev xs) \<Longrightarrow> ((rev xs) ! i) < ((rev xs) ! (Suc i))"
    using assms
  proof -
    fix i :: nat
    assume a1: "Suc i < length (rev xs)"
    obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
      by moura
    then have f2: "\<forall>n na. (\<not> n < Suc na \<or> n = 0 \<or> n = Suc (nn na n) \<and> nn na n < na) \<and> (n < Suc na \<or> n \<noteq> 0 \<and> (\<forall>nb. n \<noteq> Suc nb \<or> \<not> nb < na))"
      by (meson less_Suc_eq_0_disj)
    have f3: "Suc (length xs - Suc (Suc i)) = length (rev xs) - Suc i"
      using a1 by (simp add: Suc_diff_Suc)
    have "i < length (rev xs)"
      using a1 by (meson Suc_lessD)
    then have "i < length xs"
      by simp
    then show "rev xs ! i < rev xs ! Suc i"
      using f3 f2 a1 by (metis (no_types) assms diff_less length_rev not_less_iff_gr_or_eq rev_nth)
  qed 
  then have "distinct (rev xs)" 
    using ordered_list_distinct[of "rev xs"] by blast
  then show ?thesis by auto
qed


subsection \<open>Calculating Prefixes and Suffixes\<close>

fun suffixes :: "'a list \<Rightarrow> 'a list list" where
  "suffixes [] = [[]]" |
  "suffixes (x#xs) = (suffixes xs) @ [x#xs]"

lemma suffixes_set : 
  "set (suffixes xs) = {zs . \<exists> ys . ys@zs = xs}"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have *: "set (suffixes (x#xs)) = {zs . \<exists> ys . ys@zs = xs} \<union> {x#xs}"
    by auto
  
  have "{zs . \<exists> ys . ys@zs = xs} = {zs . \<exists> ys . x#ys@zs = x#xs}"
    by force
  then have "{zs . \<exists> ys . ys@zs = xs} = {zs . \<exists> ys . ys@zs = x#xs \<and> ys \<noteq> []}"
    by (metis Cons_eq_append_conv list.distinct(1))
  moreover have "{x#xs} = {zs . \<exists> ys . ys@zs = x#xs \<and> ys = []}"
    by force
    
  ultimately show ?case using * by force
qed

(* old definition
fun prefixes :: "'a list \<Rightarrow> 'a list list" where
  "prefixes [] = [[]]" |
  "prefixes (x#xs) = [] # (map (\<lambda> xs' . x#xs') (prefixes xs))"
*)
fun prefixes :: "'a list \<Rightarrow> 'a list list" where
  "prefixes [] = [[]]" |
  "prefixes xs = (prefixes (butlast xs)) @ [xs]"



value "prefixes [1::nat,2,3,4]"

lemma prefixes_set : "set (prefixes xs) = {xs' . \<exists> xs'' . xs'@xs'' = xs}"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  moreover have "prefixes (xs@[x]) = (prefixes xs) @ [xs@[x]]"
    by (metis prefixes.elims snoc_eq_iff_butlast)
  ultimately have *: "set (prefixes (xs@[x])) = {xs'. \<exists>xs''. xs' @ xs'' = xs} \<union> {xs@[x]}"
    by auto
  
  have "{xs'. \<exists>xs''. xs' @ xs'' = xs} = {xs'. \<exists>xs''. xs' @ xs'' @ [x] = xs @[x]}"
    by force
  then have "{xs'. \<exists>xs''. xs' @ xs'' = xs} = {xs'. \<exists>xs''. xs' @ xs'' = xs@[x] \<and> xs'' \<noteq> []}"
    by (metis (no_types, hide_lams) append.assoc snoc_eq_iff_butlast)
  moreover have "{xs@[x]} = {xs'. \<exists>xs''. xs' @ xs'' = xs@[x] \<and> xs'' = []}"
    by auto
  ultimately show ?case 
    using * by force
qed

  



fun add_prefixes :: "'a list list \<Rightarrow> 'a list list" where
  "add_prefixes xs = concat (map prefixes xs)"

value "add_prefixes [[1::nat,2,3], [], [10,100,1000,1000]]"

lemma add_prefixes_set : "set (add_prefixes xs) = {xs' . \<exists> xs'' . xs'@xs'' \<in> set xs}"
proof -
  have "set (add_prefixes xs) = {xs' . \<exists> x \<in> set xs . xs' \<in> set (prefixes x)}"
    unfolding add_prefixes.simps by auto
  also have "\<dots> = {xs' . \<exists> xs'' . xs'@xs'' \<in> set xs}"
  proof (induction xs)
    case Nil
    then show ?case using prefixes_set by auto
  next
    case (Cons a xs)
    then show ?case 
    proof -
      have "\<And> xs' . xs' \<in> {xs'. \<exists>x\<in>set (a # xs). xs' \<in> set (prefixes x)} \<longleftrightarrow> xs' \<in> {xs'. \<exists>xs''. xs' @ xs'' \<in> set (a # xs)}"
      proof -
        fix xs' 
        show "xs' \<in> {xs'. \<exists>x\<in>set (a # xs). xs' \<in> set (prefixes x)} \<longleftrightarrow> xs' \<in> {xs'. \<exists>xs''. xs' @ xs'' \<in> set (a # xs)}"
          using prefixes_set by (cases "xs' \<in> set (prefixes a)"; auto)
      qed
      then show ?thesis by blast
    qed
  qed
  finally show ?thesis by blast
qed





subsection \<open>Set-Operations on Lists\<close>

(* TODO: use selector_lists instead? *)
fun pow_list :: "'a list \<Rightarrow> 'a list list" where
  "pow_list [] = [[]]" |
  "pow_list (x#xs) = (let pxs = pow_list xs in pxs @ map (\<lambda> ys . x#ys) pxs)"

value "pow_list [1,2,3::nat]"


lemma pow_list_set :
  "set (map set (pow_list xs)) = Pow (set xs)"
proof (induction xs)
case Nil
  then show ?case by auto
next
  case (Cons x xs)

  moreover have "Pow (set (x # xs)) = Pow (set xs) \<union> (image (insert x) (Pow (set xs)))"
    by (simp add: Pow_insert)
    
  moreover have "set (map set (pow_list (x#xs))) =  set (map set (pow_list xs)) \<union> (image (insert x) (set (map set (pow_list xs))))"
  proof -
    have "\<And> ys . ys \<in> set (map set (pow_list (x#xs))) \<Longrightarrow> ys \<in> set (map set (pow_list xs)) \<union> (image (insert x) (set (map set (pow_list xs))))" 
    proof -
      fix ys assume "ys \<in> set (map set (pow_list (x#xs)))"
      then consider (a) "ys \<in> set (map set (pow_list xs))" |
                    (b) "ys \<in> set (map set (map ((#) x) (pow_list xs)))"
        unfolding pow_list.simps Let_def by auto
      then show "ys \<in> set (map set (pow_list xs)) \<union> (image (insert x) (set (map set (pow_list xs))))" 
        by (cases; auto)
    qed
    moreover have "\<And> ys . ys \<in> set (map set (pow_list xs)) \<union> (image (insert x) (set (map set (pow_list xs)))) \<Longrightarrow> ys \<in> set (map set (pow_list (x#xs)))"
    proof -
      fix ys assume "ys \<in> set (map set (pow_list xs)) \<union> (image (insert x) (set (map set (pow_list xs))))"
      then consider (a) "ys \<in> set (map set (pow_list xs))" |
                    (b) "ys \<in> (image (insert x) (set (map set (pow_list xs))))"
        by blast
      then show "ys \<in> set (map set (pow_list (x#xs)))" 
        unfolding pow_list.simps Let_def by (cases; auto)
    qed
    ultimately show ?thesis by blast
  qed
    
  ultimately show ?case
    by auto 
qed


fun inter_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "inter_list xs ys = filter (\<lambda> x . x \<in> set ys) xs"

lemma inter_list_set : "set (inter_list xs ys) = (set xs) \<inter> (set ys)"
  by auto

fun subset_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "subset_list xs ys = list_all (\<lambda> x . x \<in> set ys) xs"

lemma subset_list_set : "subset_list xs ys = ((set xs) \<subseteq> (set ys))" 
  unfolding subset_list.simps
  by (simp add: Ball_set subset_code(1)) 



subsection \<open>Calculating Distinct Non-Reflexive Pairs over List Elements\<close> 

(* Could be used to calculate tuples ((q1,q2),A), where A is a separator for q1 q2, such that
   ((q2,q1),_) is skipped *)

fun non_sym_dist_pairs' :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "non_sym_dist_pairs' [] = []" |
  "non_sym_dist_pairs' (x#xs) = (map (\<lambda> y. (x,y)) xs) @ non_sym_dist_pairs' xs"

fun non_sym_dist_pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "non_sym_dist_pairs xs = non_sym_dist_pairs' (remdups xs)"

value "non_sym_dist_pairs' [1,2,3::nat]"
value "non_sym_dist_pairs' [1,2,1,3::nat]"
value "non_sym_dist_pairs [1,2,1,3::nat]"

lemma non_sym_dist_pairs_subset : "set (non_sym_dist_pairs xs) \<subseteq> (set xs) \<times> (set xs)"
  by (induction xs; auto)

lemma non_sym_dist_pairs'_elems_distinct:
  assumes "distinct xs"
  and     "(x,y) \<in> set (non_sym_dist_pairs' xs)"
shows "x \<in> set xs" 
and   "y \<in> set xs"
and   "x \<noteq> y"
proof -
  show "x \<in> set xs" and "y \<in> set xs"
    using non_sym_dist_pairs_subset assms(2) by (induction xs; auto)+
  show "x \<noteq> y"
    using assms by (induction xs; auto)
qed

lemma non_sym_dist_pairs_elems_distinct:
  assumes "(x,y) \<in> set (non_sym_dist_pairs xs)"
shows "x \<in> set xs" 
and   "y \<in> set xs"
and   "x \<noteq> y"
  using non_sym_dist_pairs'_elems_distinct assms
  unfolding non_sym_dist_pairs.simps by fastforce+


lemma non_sym_dist_pairs_elems :
  assumes "x \<in> set xs"
  and     "y \<in> set xs"
  and     "x \<noteq> y"
shows "(x,y) \<in> set (non_sym_dist_pairs xs) \<or> (y,x) \<in> set (non_sym_dist_pairs xs)"
  using assms by (induction xs; auto)



lemma non_sym_dist_pairs'_elems_non_refl :
  assumes "distinct xs"
  and     "(x,y) \<in> set (non_sym_dist_pairs' xs)"
shows "(y,x) \<notin> set (non_sym_dist_pairs' xs)"
  using assms  
proof (induction xs arbitrary: x y)
  case Nil
  then show ?case by auto
next
  case (Cons z zs)
  then have "distinct zs" by auto

  have "x \<noteq> y"
    using non_sym_dist_pairs'_elems_distinct[OF Cons.prems] by simp

  consider (a) "(x,y) \<in> set (map (Pair z) zs)" |
           (b) "(x,y) \<in> set (non_sym_dist_pairs' zs)"
    using \<open>(x,y) \<in> set (non_sym_dist_pairs' (z#zs))\<close> unfolding non_sym_dist_pairs'.simps by auto
  then show ?case proof cases
    case a
    then have "x = z" by auto
    then have "(y,x) \<notin> set (map (Pair z) zs)"
      using \<open>x \<noteq> y\<close> by auto
    moreover have "x \<notin> set zs"
      using \<open>x = z\<close> \<open>distinct (z#zs)\<close> by auto
    ultimately show ?thesis 
      using \<open>distinct zs\<close> non_sym_dist_pairs'_elems_distinct(2) by fastforce
  next
    case b
    then have "x \<noteq> z" and "y \<noteq> z"
      using Cons.prems unfolding non_sym_dist_pairs'.simps 
      by (meson distinct.simps(2) non_sym_dist_pairs'_elems_distinct(1,2))+
    
    then show ?thesis 
      using Cons.IH[OF \<open>distinct zs\<close> b] by auto
  qed
qed


lemma non_sym_dist_pairs_elems_non_refl :
  assumes "(x,y) \<in> set (non_sym_dist_pairs xs)"
  shows "(y,x) \<notin> set (non_sym_dist_pairs xs)"
  using assms by (simp add: non_sym_dist_pairs'_elems_non_refl)


lemma non_sym_dist_pairs_set_iff :
  "(x,y) \<in> set (non_sym_dist_pairs xs) \<longleftrightarrow> (x \<noteq> y \<and> x \<in> set xs \<and> y \<in> set xs \<and> (y,x) \<notin> set (non_sym_dist_pairs xs))"
  using non_sym_dist_pairs_elems_non_refl[of x y xs] 
        non_sym_dist_pairs_elems[of x xs y] 
        non_sym_dist_pairs_elems_distinct[of x y xs] by blast 


subsection \<open>Finite Linear Order From List Positions\<close>

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



subsection \<open>Filter And Remove\<close>

(* note: does only remove from the first list *)
fun find_remove_2' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'b \<times> 'a list) option" where
  "find_remove_2' P [] _ _ = None" |
  "find_remove_2' P (x#xs) ys prev = (case find (\<lambda>y . P x y) ys of
      Some y \<Rightarrow> Some (x,y,prev@xs) |
      None   \<Rightarrow> find_remove_2' P xs ys (prev@[x]))"

fun find_remove_2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b \<times> 'a list) option" where
  "find_remove_2 P xs ys = find_remove_2' P xs ys []"

value "find_remove_2 (\<lambda> x y . y = 2 * x) [1::nat,2,3,4,5] [3,5,1,9,8,10]"
value "find_remove_2 (\<lambda> q x . q \<noteq> 1 \<and> card (h m_ex_H (q,x)) > 1) (nodes_as_list m_ex_H) (inputs_as_list m_ex_H)"

lemma find_remove_2'_set : 
  assumes "find_remove_2' P xs ys prev = Some (x,y,xs')"
shows "P x y"
and   "x \<in> set xs"
and   "y \<in> set ys"
and   "distinct (prev@xs) \<Longrightarrow> set xs' = (set prev \<union> set xs) - {x}"
and   "distinct (prev@xs) \<Longrightarrow> distinct xs'"
and   "xs' = prev@(remove1 x xs)"
proof -
  have "P x y \<and> x \<in> set xs \<and> y \<in> set ys \<and> (distinct (prev@xs) \<longrightarrow> set xs' = (set prev \<union> set xs) - {x}) \<and> (distinct (prev@xs) \<longrightarrow> distinct xs') \<and> (xs' = prev@(remove1 x xs))"
    using assms 
  proof (induction xs arbitrary: prev xs' x y)
    case Nil
    then show ?case by auto 
  next
    case (Cons x' xs)
    then show ?case proof (cases "find (\<lambda>y . P x' y) ys")
      case None
      then have "find_remove_2' P (x' # xs) ys prev = find_remove_2' P xs ys (prev@[x'])"
        using Cons.prems(1) by auto
      hence *: "find_remove_2' P xs ys (prev@[x']) = Some (x, y, xs')"
        using Cons.prems(1) by simp
      
      have "x' \<noteq> x"
        by (metis "*" Cons.IH None find_from)
      moreover have "distinct (prev @ x' # xs) \<longrightarrow> distinct ((x' # prev) @ xs)"
        by auto
      ultimately show ?thesis using Cons.IH[OF *]
        by auto
    next
      case (Some y')
      then have "find_remove_2' P (x' # xs) ys prev = Some (x',y',prev@xs)"
        by auto
      then show ?thesis using Some
        using Cons.prems(1) find_condition find_set by fastforce 
    qed
  qed
  then show "P x y"
      and   "x \<in> set xs"
      and   "y \<in> set ys"
      and   "distinct (prev @ xs) \<Longrightarrow> set xs' = (set prev \<union> set xs) - {x}"
      and   "distinct (prev@xs) \<Longrightarrow> distinct xs'"
      and   "xs' = prev@(remove1 x xs)"
    by blast+
qed


lemma find_remove_2'_index : 
  assumes "find_remove_2' P xs ys prev = Some (x,y,xs')"
  obtains i where "i < length xs" 
                  "xs ! i = x"
                  "\<And> j . j < i \<Longrightarrow> find (\<lambda>y . P (xs ! j) y) ys = None"
proof -
  have "\<exists> i . i < length xs \<and> xs ! i = x \<and> (\<forall> j < i . find (\<lambda>y . P (xs ! j) y) ys = None)"
    using assms 
  proof (induction xs arbitrary: prev xs' x y)
    case Nil
    then show ?case by auto 
  next
    case (Cons x' xs)
    then show ?case proof (cases "find (\<lambda>y . P x' y) ys")
      case None
      then have "find_remove_2' P (x' # xs) ys prev = find_remove_2' P xs ys (prev@[x'])"
        using Cons.prems(1) by auto
      hence *: "find_remove_2' P xs ys (prev@[x']) = Some (x, y, xs')"
        using Cons.prems(1) by simp
      
      have "x' \<noteq> x"
        using find_remove_2'_set(1,3)[OF *] None unfolding find_None_iff
        by blast

      obtain i where "i < length xs" and "xs ! i = x" and "(\<forall> j < i . find (\<lambda>y . P (xs ! j) y) ys = None)"
        using Cons.IH[OF *] by blast

      have "Suc i < length (x'#xs)"
        using \<open>i < length xs\<close> by auto
      moreover have "(x'#xs) ! Suc i = x"
        using \<open>xs ! i = x\<close> by auto
      moreover have "(\<forall> j < Suc i . find (\<lambda>y . P ((x'#xs) ! j) y) ys = None)"
      proof -
        have "\<And> j . j > 0 \<Longrightarrow> j < Suc i \<Longrightarrow> find (\<lambda>y . P ((x'#xs) ! j) y) ys = None"
          using \<open>(\<forall> j < i . find (\<lambda>y . P (xs ! j) y) ys = None)\<close> by auto 
        then show ?thesis using None
          by (metis neq0_conv nth_Cons_0) 
      qed
      
      ultimately show ?thesis using that by blast
    next
      case (Some y')
      then show ?thesis 
        using Cons.prems(1) by fastforce 
    qed
  qed
  then show ?thesis using that by blast
qed

lemma find_remove_2_index : 
  assumes "find_remove_2 P xs ys = Some (x,y,xs')"
  obtains i where "i < length xs" 
                  "xs ! i = x"
                  "\<And> j . j < i \<Longrightarrow> find (\<lambda>y . P (xs ! j) y) ys = None"
  using assms find_remove_2'_index[of P xs ys "[]" x y xs'] by auto


lemma find_remove_2'_set_rev :
  assumes "x \<in> set xs"
  and     "y \<in> set ys"
  and     "P x y"
shows "find_remove_2' P xs ys prev \<noteq> None" 
using assms(1) proof(induction xs arbitrary: prev)
  case Nil
  then show ?case by auto
next
  case (Cons x' xs)
  then show ?case proof (cases "find (\<lambda>y . P x' y) ys")
    case None
    then have "x \<noteq> x'" 
      using assms(2,3) by (metis find_None_iff) 
    then have "x \<in> set xs"
      using Cons.prems by auto
    then show ?thesis 
      using Cons.IH unfolding find_remove_2'.simps None by auto
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed


lemma find_remove_2'_diff_prev_None :
  "(find_remove_2' P xs ys prev = None \<Longrightarrow> find_remove_2' P xs ys prev' = None)" 
proof (induction xs arbitrary: prev prev')
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case proof (cases "find (\<lambda>y . P x y) ys")
    case None
    then have "find_remove_2' P (x#xs) ys prev = find_remove_2' P xs ys (prev@[x])" 
         and  "find_remove_2' P (x#xs) ys prev' = find_remove_2' P xs ys (prev'@[x])"
      by auto
    then show ?thesis using Cons by auto 
  next
    case (Some a)
    then show ?thesis using Cons by auto
  qed
qed

lemma find_remove_2'_diff_prev_Some :
  "(find_remove_2' P xs ys prev = Some (x,y,xs') \<Longrightarrow> \<exists> xs'' . find_remove_2' P xs ys prev' = Some (x,y,xs''))" 
proof (induction xs arbitrary: prev prev')
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  show ?case proof (cases "find (\<lambda>y . P x y) ys")
    case None
    then have "find_remove_2' P (x#xs) ys prev = find_remove_2' P xs ys (prev@[x])" 
         and  "find_remove_2' P (x#xs) ys prev' = find_remove_2' P xs ys (prev'@[x])"
      by auto
    then show ?thesis using Cons by auto 
  next
    case (Some a)
    then show ?thesis using Cons by auto
  qed
qed


lemma find_remove_2_None_iff :
  "find_remove_2 P xs ys = None \<longleftrightarrow> \<not> (\<exists>x y . x \<in> set xs \<and> y \<in> set ys \<and> P x y)"
  unfolding find_remove_2.simps 
  using find_remove_2'_set(1-3) find_remove_2'_set_rev
  by (metis old.prod.exhaust option.exhaust)

lemma find_remove_2_set : 
  assumes "find_remove_2 P xs ys = Some (x,y,xs')"
shows "P x y"
and   "x \<in> set xs"
and   "y \<in> set ys"
and   "distinct xs \<Longrightarrow> set xs' = (set xs) - {x}"
and   "distinct xs \<Longrightarrow> distinct xs'"
and   "xs' = (remove1 x xs)"
  using assms find_remove_2'_set[of P xs ys "[]" x y xs'] unfolding find_remove_2.simps by auto

lemma find_remove_2_removeAll :
  assumes "find_remove_2 P xs ys = Some (x,y,xs')"
  and     "distinct xs"
shows "xs' = removeAll x xs"
  using find_remove_2_set(6)[OF assms(1)]
  by (simp add: assms(2) distinct_remove1_removeAll) 


subsection \<open>Other Lemmata\<close>

lemma list_append_subset3 : "set xs1 \<subseteq> set ys1 \<Longrightarrow> set xs2 \<subseteq> set ys2 \<Longrightarrow> set xs3 \<subseteq> set ys3 \<Longrightarrow> set (xs1@xs2@xs3) \<subseteq> set(ys1@ys2@ys3)" by auto

lemma subset_filter : "set xs \<subseteq> set ys \<Longrightarrow> set xs = set (filter (\<lambda> x . x \<in> set xs) ys)"
  by auto


lemma filter_length_weakening :
  assumes "\<And> q . f1 q \<Longrightarrow> f2 q"
  shows "length (filter f1 p) \<le> length (filter f2 p)"
proof (induction p)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then show ?case using assms by (cases "f1 a"; auto)
qed

lemma max_length_elem :
  fixes xs :: "'a list set"
  assumes "finite xs"
  and     "xs \<noteq> {}"
shows "\<exists> x \<in> xs . \<not>(\<exists> y \<in> xs . length y > length x)" 
using assms proof (induction xs)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case proof (cases "F = {}")
    case True
    then show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> F" and "\<not>(\<exists> y' \<in> F . length y' > length y)"
      using insert.IH by blast
    then show ?thesis using dual_order.strict_trans by (cases "length x > length y"; auto)
  qed
qed

lemma list_property_from_index_property :
  assumes "\<And> i . i < length xs \<Longrightarrow> P (xs ! i)"
  shows "\<And> x . x \<in> set xs \<Longrightarrow> P x"
  by (metis assms in_set_conv_nth) 

lemma list_distinct_prefix :
  assumes "\<And> i . i < length xs \<Longrightarrow> xs ! i \<notin> set (take i xs)"
  shows "distinct xs"
proof -
  have "\<And> j . distinct (take j xs)"
  proof -
    fix j 
    show "distinct (take j xs)"
    proof (induction j)
      case 0
      then show ?case by auto
    next
      case (Suc j)
      then show ?case proof (cases "Suc j \<le> length xs")
        case True
        then have "take (Suc j) xs = (take j xs) @ [xs ! j]"
          by (simp add: Suc_le_eq take_Suc_conv_app_nth)
        then show ?thesis using Suc.IH assms[of j] True by auto
      next
        case False
        then have "take (Suc j) xs = take j xs" by auto
        then show ?thesis using Suc.IH by auto
      qed
    qed 
  qed
  then have "distinct (take (length xs) xs)"
    by blast
  then show ?thesis by auto 
qed


lemma concat_pair_set :
  "set (concat (map (\<lambda>x. map (Pair x) ys) xs)) = {xy . fst xy \<in> set xs \<and> snd xy \<in> set ys}"
  by auto

lemma list_set_sym :
  "set (x@y) = set (y@x)" by auto



lemma list_contains_last_take :
  assumes "x \<in> set xs"
  shows "\<exists> i . 0 < i \<and> i \<le> length xs \<and> last (take i xs) = x"
  by (metis Suc_leI assms hd_drop_conv_nth in_set_conv_nth last_snoc take_hd_drop zero_less_Suc)
  
lemma take_last_index :
  assumes "i < length xs"
  shows "last (take (Suc i) xs) = xs ! i"
  by (simp add: assms take_Suc_conv_app_nth)

lemma integer_singleton_least :
  assumes "{x . P x} = {a::integer}"
  shows "a = (LEAST x . P x)"
  by (metis Collect_empty_eq Least_equality assms insert_not_empty mem_Collect_eq order_refl singletonD)


lemma sort_list_split :
  "\<forall> x \<in> set (take i (sort xs)) . \<forall> y \<in> set (drop i (sort xs)) . x \<le> y"
  using sorted_append by fastforce


lemma set_map_subset :
  assumes "x \<in> set xs"
  and     "t \<in> set (map f [x])"
shows "t \<in> set (map f xs)"
  using assms by auto

lemma rev_induct2[consumes 1, case_names Nil snoc]: 
  assumes "length xs = length ys" 
      and "P [] []"
      and "(\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))"
    shows "P xs ys"
using assms proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case proof (cases ys)
    case Nil
    then show ?thesis
      using snoc.prems(1) by auto 
  next
    case (Cons a list)
    then show ?thesis
      by (metis append_butlast_last_id diff_Suc_1 length_append_singleton list.distinct(1) snoc.hyps snoc.prems) 
  qed
qed

lemma finite_set_min_param_ex :
  assumes "finite XS"
  and     "\<And> x . x \<in> XS \<Longrightarrow> \<exists> k . \<forall> k' . k \<le> k' \<longrightarrow> P x k'"
shows "\<exists> (k::nat) . \<forall> x \<in> XS . P x k"
proof -
  obtain f where f_def : "\<And> x . x \<in> XS \<Longrightarrow> \<forall> k' . (f x) \<le> k' \<longrightarrow> P x k'"
    using assms(2) by meson
  let ?k = "Max (image f XS)"
  have "\<forall> x \<in> XS . P x ?k"
    using f_def by (simp add: assms(1)) 
  then show ?thesis by blast
qed

fun list_max :: "nat list \<Rightarrow> nat" where
  "list_max [] = 0" |
  "list_max xs = Max (set xs)"

lemma list_max_is_max : "q \<in> set xs \<Longrightarrow> q \<le> list_max xs"
  by (metis List.finite_set Max_ge length_greater_0_conv length_pos_if_in_set list_max.elims) 

lemma list_prefix_subset : "\<exists> ys . ts = xs@ys \<Longrightarrow> set xs \<subseteq> set ts" by auto
lemma list_map_set_prop : "x \<in> set (map f xs) \<Longrightarrow> \<forall> y . P (f y) \<Longrightarrow> P x" by auto
lemma list_concat_non_elem : "x \<notin> set xs \<Longrightarrow> x \<notin> set ys \<Longrightarrow> x \<notin> set (xs@ys)" by auto
lemma list_prefix_elem : "x \<in> set (xs@ys) \<Longrightarrow> x \<notin> set ys \<Longrightarrow> x \<in> set xs" by auto
lemma list_map_source_elem : "x \<in> set (map f xs) \<Longrightarrow> \<exists> x' \<in> set xs . x = f x'" by auto


lemma maximal_set_cover : 
  fixes X :: "'a set set"
  assumes "finite X" 
  and     "S \<in> X"  
shows "\<exists> S' \<in> X . S \<subseteq> S' \<and> (\<forall> S'' \<in> X . \<not>(S' \<subset> S''))"
proof (rule ccontr)
  assume "\<not> (\<exists>S'\<in>X. S \<subseteq> S' \<and> (\<forall>S''\<in>X. \<not> S' \<subset> S''))"
  then have *: "\<And> T . T \<in> X \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<exists> T' \<in> X . T \<subset> T'"
    by auto

  have "\<And> k . \<exists> ss . (length ss = Suc k) \<and> (hd ss = S) \<and> (\<forall> i < k . ss ! i \<subset> ss ! (Suc i)) \<and> (set ss \<subseteq> X)"
  proof -
    fix k show "\<exists> ss . (length ss = Suc k) \<and> (hd ss = S) \<and> (\<forall> i < k . ss ! i \<subset> ss ! (Suc i)) \<and> (set ss \<subseteq> X)"
    proof (induction k)
      case 0
      have "length [S] = Suc 0 \<and> hd [S] = S \<and> (\<forall> i < 0 . [S] ! i \<subset> [S] ! (Suc i)) \<and> (set [S] \<subseteq> X)" using assms(2) by auto
      then show ?case by blast
    next
      case (Suc k)
      then obtain ss where "length ss = Suc k" 
                       and "hd ss = S" 
                       and "(\<forall>i<k. ss ! i \<subset> ss ! Suc i)" 
                       and "set ss \<subseteq> X"
        by blast
      then have "ss ! k \<in> X"
        by auto
      moreover have "S \<subseteq> (ss ! k)"
      proof -
        have "\<And> i . i < Suc k \<Longrightarrow> S \<subseteq> (ss ! i)"
        proof -
          fix i assume "i < Suc k"
          then show "S \<subseteq> (ss ! i)"
          proof (induction i)
            case 0
            then show ?case using \<open>hd ss = S\<close> \<open>length ss = Suc k\<close>
              by (metis hd_conv_nth list.size(3) nat.distinct(1) order_refl) 
          next
            case (Suc i)
            then have "S \<subseteq> ss ! i" and "i < k" by auto
            then have "ss ! i \<subset> ss ! Suc i" using \<open>(\<forall>i<k. ss ! i \<subset> ss ! Suc i)\<close> by blast
            then show ?case using \<open>S \<subseteq> ss ! i\<close> by auto
          qed
        qed
        then show ?thesis using \<open>length ss = Suc k\<close> by auto 
      qed
      ultimately obtain T' where "T' \<in> X" and "ss ! k \<subset> T'"
        using * by meson 

      let ?ss = "ss@[T']"

      have "length ?ss = Suc (Suc k)" 
        using \<open>length ss = Suc k\<close> by auto
      moreover have "hd ?ss = S" 
        using \<open>hd ss = S\<close> by (metis \<open>length ss = Suc k\<close> hd_append list.size(3) nat.distinct(1)) 
      moreover have "(\<forall>i < Suc k. ?ss ! i \<subset> ?ss ! Suc i)" 
        using \<open>(\<forall>i<k. ss ! i \<subset> ss ! Suc i)\<close> \<open>ss ! k \<subset> T'\<close> 
        by (metis Suc_lessI \<open>length ss = Suc k\<close> diff_Suc_1 less_SucE nth_append nth_append_length) 
      moreover have "set ?ss \<subseteq> X" 
        using \<open>set ss \<subseteq> X\<close> \<open>T' \<in> X\<close> by auto
      ultimately show ?case by blast
    qed
  qed

  then obtain ss where "(length ss = Suc (card X))"
                   and "(hd ss = S)" 
                   and "(\<forall> i < card X . ss ! i \<subset> ss ! (Suc i))" 
                   and "(set ss \<subseteq> X)" 
    by blast
  then have "(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))"
    by auto

  have **: "\<And> i (ss :: 'a set list) . (\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i)) \<Longrightarrow> i < length ss  \<Longrightarrow> \<forall> s \<in> set (take i ss) . s \<subset> ss ! i"
  proof -
    fix i 
    fix ss :: "'a set list"
    assume "i < length ss " and "(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))"
    then show "\<forall> s \<in> set (take i ss) . s \<subset> ss ! i"
    proof (induction i)
      case 0
      then show ?case by auto
    next
      case (Suc i)
      then have "\<forall>s\<in>set (take i ss). s \<subset> ss ! i" by auto
      then have "\<forall>s\<in>set (take i ss). s \<subset> ss ! (Suc i)" using Suc.prems
        by (metis One_nat_def Suc_diff_Suc Suc_lessE diff_zero dual_order.strict_trans nat.inject zero_less_Suc) 
      moreover have "ss ! i \<subset> ss ! (Suc i)" using Suc.prems by auto
      moreover have "(take (Suc i) ss) = (take i ss)@[ss ! i]" using Suc.prems(1)
        by (simp add: take_Suc_conv_app_nth)
      ultimately show ?case by auto 
    qed
  qed

  have "distinct ss"
    using \<open>(\<forall> i < length ss - 1 . ss ! i \<subset> ss ! (Suc i))\<close>
  proof (induction ss rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc a ss)
    from snoc.prems have "\<forall>i<length ss - 1. ss ! i \<subset> ss ! Suc i"
      by (metis Suc_lessD diff_Suc_1 diff_Suc_eq_diff_pred length_append_singleton nth_append zero_less_diff) 
    then have "distinct ss"
      using snoc.IH by auto
    moreover have "a \<notin> set ss"
      using **[OF snoc.prems, of "length (ss @ [a]) - 1"] by auto
    ultimately show ?case by auto
  qed

  then have "card (set ss) = Suc (card X)"
    using \<open>(length ss = Suc (card X))\<close> by (simp add: distinct_card) 
  then show "False"
    using \<open>set ss \<subseteq> X\<close> \<open>finite X\<close> by (metis Suc_n_not_le_n card_mono) 
qed



lemma map_set : 
  assumes "x \<in> set xs"
  shows "f x \<in> set (map f xs)" using assms by auto


lemma maximal_distinct_prefix :
  assumes "\<not> distinct xs"
  obtains n where "distinct (take (Suc n) xs)"
            and   "\<not> (distinct (take (Suc (Suc n)) xs))"
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  
  show ?case proof (cases "distinct xs")
    case True
    then have "distinct (take (length xs) (xs@[x]))" by auto
    moreover have"\<not> (distinct (take (Suc (length xs)) (xs@[x])))" using snoc.prems(2) by auto
    ultimately show ?thesis using that by (metis Suc_pred distinct_singleton length_greater_0_conv self_append_conv2 snoc.prems(1) snoc.prems(2))
  next
    case False
    
    then show ?thesis using snoc.IH that
      by (metis Suc_mono butlast_snoc length_append_singleton less_SucI linorder_not_le snoc.prems(1) take_all take_butlast) 
  qed
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
      by (metis append_Cons is_prefix.simps(2) is_prefix.simps(3) neq_Nil_conv) 
  next
    case False
    then show ?thesis
      using Cons.IH by auto 
  qed
qed


(* TODO: continue if necessary *)
(*
subsection \<open>Transitive Closure\<close>

inductive trancl_from :: "'a \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a \<Rightarrow> bool" where
  "b \<in> f a \<Longrightarrow> trancl_from a f b" |
  "c \<in> f b \<Longrightarrow> trancl_from a f b \<Longrightarrow> trancl_from a f c"

fun trancl_from' :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "trancl_from' 0 qs f = {}" |
  "trancl_from' (Suc k) qs f = qs \<union> (\<Union> (image (\<lambda> q . trancl_from' k (f q) f) qs))"

(* use (c)sorted_list_of_set *)
fun trancl_from'' :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "trancl_from'' 0 _ _ prev = prev" |
  "trancl_from'' _ [] _ prev = prev" |
  "trancl_from'' (Suc k) (q#qs) f prev = 
    (let unknowns = filter (\<lambda> q' . q' \<notin> prev) (f q)
      in trancl_from'' k (unknowns@qs) f (prev \<union> set unknowns))"


value "trancl_from' 1 {0::nat} ((\<lambda> x . {1,2})(1:={3},2:={4}))"
value "trancl_from'' 0 [0::nat] ((\<lambda> x . [1,2])(1:=[3],2:=[4])) {0}"
*)



fun reachable_nodes_dfs :: "nat \<Rightarrow> ('a::linorder) set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "reachable_nodes_dfs 0 _ _ visitedNodes = visitedNodes" |
  "reachable_nodes_dfs (Suc k) nodesToHandle f visitedNodes = 
    (if nodesToHandle = {} 
      then visitedNodes
      else (let q = Max nodesToHandle;
                visitedNodes'  = (insert q visitedNodes) \<union> f q;
                nodesToHandle' = (nodesToHandle \<union> f q) - (insert q visitedNodes)
             in reachable_nodes_dfs k nodesToHandle' f visitedNodes'))"

value "reachable_nodes_dfs 10 {1::nat} ((\<lambda>x . {})(1:={2,3},2:={1,4},3:={2,4},4:={1,2})) {1}"
                       
  

end