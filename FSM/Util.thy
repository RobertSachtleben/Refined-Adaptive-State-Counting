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

lemma list_prefix_subset : "\<exists> ys . ts = xs@ys \<Longrightarrow> set xs \<subseteq> set ts" by auto
lemma list_map_set_prop : "x \<in> set (map f xs) \<Longrightarrow> \<forall> y . P (f y) \<Longrightarrow> P x" by auto
lemma list_concat_non_elem : "x \<notin> set xs \<Longrightarrow> x \<notin> set ys \<Longrightarrow> x \<notin> set (xs@ys)" by auto
lemma list_prefix_elem : "x \<in> set (xs@ys) \<Longrightarrow> x \<notin> set ys \<Longrightarrow> x \<in> set xs" by auto
lemma list_map_source_elem : "x \<in> set (map f xs) \<Longrightarrow> \<exists> x' \<in> set xs . x = f x'" by auto


end