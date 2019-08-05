theory Util
imports Main
begin

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


subsection \<open>Other Lemmata\<close>

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

end