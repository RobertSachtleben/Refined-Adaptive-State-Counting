theory IO_Tree
imports FSM
begin

subsection \<open>Utils\<close>

fun update_assoc_list_with_default :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "update_assoc_list_with_default k f d [] = [(k,f d)]" |
  "update_assoc_list_with_default k f d ((x,y)#xys) = (if k = x
    then ((x,f y)#xys)
    else (x,y) # (update_assoc_list_with_default k f d xys))"

lemma update_assoc_list_with_default_key_found :
  assumes "distinct (map fst xys)"
  and     "i < length xys"
  and     "fst (xys ! i) = k"
shows "update_assoc_list_with_default k f d xys =
        ((take i xys) @ [(k, f (snd (xys ! i)))] @ (drop (Suc i) xys))" 
using assms proof (induction xys arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a xys)
  
  show ?case
  proof (cases i)
    case 0
    then have "fst a = k" using Cons.prems(3) by auto
    then have "update_assoc_list_with_default k f d (a#xys) = (k, f (snd a)) # xys"
      unfolding 0 by (metis prod.collapse update_assoc_list_with_default.simps(2)) 
    then show ?thesis unfolding 0 by auto
  next
    case (Suc j)
    then have "fst a \<noteq> k"
      using Cons.prems by auto 

    have "distinct (map fst xys)"
    and  "j < length xys"
    and  "fst (xys ! j) = k"
      using Cons.prems unfolding Suc by auto

    then have "update_assoc_list_with_default k f d xys = take j xys @ [(k, f (snd (xys ! j)))] @ drop (Suc j) xys"
      using Cons.IH[of j] by auto

    then show ?thesis unfolding Suc using \<open>fst a \<noteq> k\<close>
      by (metis append_Cons drop_Suc_Cons nth_Cons_Suc prod.collapse take_Suc_Cons update_assoc_list_with_default.simps(2)) 
  qed 
qed 

lemma update_assoc_list_with_default_key_not_found :
  assumes "distinct (map fst xys)"
  and     "k \<notin> set (map fst xys)"
shows "update_assoc_list_with_default k f d xys = xys @ [(k,f d)]"  
  using assms by (induction xys; auto)


lemma update_assoc_list_with_default_key_distinct :
  assumes "distinct (map fst xys)"
  shows "distinct (map fst (update_assoc_list_with_default k f d xys))"
proof (cases "k \<in> set (map fst xys)")
  case True
  then obtain i where "i < length xys" and "fst (xys ! i) = k"
    by (metis in_set_conv_nth length_map nth_map) 
  then have *: "(map fst (take i xys @ [(k, f (snd (xys ! i)))] @ drop (Suc i) xys)) = (map fst xys)"
  proof -
    have "xys ! i # drop (Suc i) xys = drop i xys"
      using Cons_nth_drop_Suc \<open>i < length xys\<close> by blast
    then show ?thesis
      by (metis (no_types) \<open>fst (xys ! i) = k\<close> append_Cons append_self_conv2 append_take_drop_id fst_conv list.simps(9) map_append)
  qed
  show ?thesis
    unfolding update_assoc_list_with_default_key_found[OF assms \<open>i < length xys\<close> \<open>fst (xys ! i) = k\<close>] * 
    using assms by assumption
next
  case False
  have *: "(map fst (xys @ [(k, f d)])) = (map fst xys)@[k]" by auto
  show ?thesis
    using assms False
    unfolding update_assoc_list_with_default_key_not_found[OF assms False] * by auto
qed






subsection \<open>IO Tries\<close>


datatype 'a io_trie = IO_Trie "('a \<times> 'a io_trie) list"

fun io_trie_invar :: "'a io_trie \<Rightarrow> bool" where
  "io_trie_invar (IO_Trie ts) = (distinct (map fst ts) \<and> (\<forall> t \<in> set (map snd ts) . io_trie_invar t))"



definition empty :: "'a io_trie" where
  "empty = IO_Trie []"

lemma empty_invar : "io_trie_invar empty" unfolding empty_def by auto



fun height :: "'a io_trie \<Rightarrow> nat" where
  "height (IO_Trie []) = 0" |
  "height (IO_Trie (xt#xts)) = Suc (foldr (\<lambda> t m . max (height t) m) (map snd (xt#xts)) 0)"

lemma height_0 : 
  assumes "height t = 0" 
  shows "t = empty" 
proof (rule ccontr)
  assume "t \<noteq> empty"
  then obtain xt xts where "t = IO_Trie (xt#xts)"
    by (metis IO_Tree.empty_def height.cases)
  have "height t > 0" 
    unfolding \<open>t = IO_Trie (xt#xts)\<close> height.simps
    by simp
  then show "False"
    using assms by simp
qed


lemma max_by_foldr :
  assumes "x \<in> set xs"
  shows "f x < Suc (foldr (\<lambda> x' m . max (f x') m) xs 0)"
  using assms by (induction xs; auto)

lemma height_inc :
  assumes "t \<in> set (map snd ts)"
  shows "height t < height (IO_Trie ts)"
proof -
  obtain xt xts where "ts = xt#xts"
    using assms
    by (metis list.set_cases list_map_source_elem) 
  
  have "height t < Suc (foldr (\<lambda> t m . max (height t) m) (map snd (xt#xts)) 0)"
    using assms unfolding \<open>ts = xt#xts\<close> using max_by_foldr[of t "(map snd (xt#xts))" height] 
    by blast

  then show ?thesis unfolding \<open>ts = xt#xts\<close> by auto
qed

(*
lemma io_tree_induct :
  assumes "P empty"
  and     "\<And> ts . (\<And> t . t \<in> set (map snd ts) \<Longrightarrow> P t) \<Longrightarrow> P (IO_Trie ts)"
shows "P t"
*)





fun insert :: "'a list \<Rightarrow> 'a io_trie \<Rightarrow> 'a io_trie" where
  "insert [] t = t" |
  "insert (x#xs) (IO_Trie ts) = (IO_Trie (update_assoc_list_with_default x (\<lambda> t . insert xs t) empty ts))"


lemma insert_invar : "io_trie_invar t \<Longrightarrow> io_trie_invar (insert xs t)" 
proof (induction xs arbitrary: t)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  obtain ts where "t = IO_Trie ts"
    using io_trie_invar.cases by auto

  then have "distinct (map fst ts)"
       and  "\<And> t . t \<in> set (map snd ts) \<Longrightarrow> io_trie_invar t"
    using Cons.prems by auto
    
  
  show ?case proof (cases "x \<in> set (map fst ts)")
    case True
    then obtain i where "i < length ts" and "fst (ts ! i) = x"
      by (metis in_set_conv_nth length_map nth_map) 
    have "insert (x#xs) (IO_Trie ts) = (IO_Trie (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      unfolding insert.simps empty_def
      unfolding update_assoc_list_with_default_key_found[OF \<open>distinct (map fst ts)\<close> \<open>i < length ts\<close> \<open>fst (ts ! i) = x\<close>, of "(\<lambda> t . insert xs t)" "(IO_Trie [])"] 
      by simp
    
    have "\<And> t . t \<in> set (map snd (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts)) \<Longrightarrow> io_trie_invar t"
    proof - 
      fix t assume "t \<in> set (map snd (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      then consider (a) "t \<in> set (map snd (take i ts @ drop (Suc i) ts))" |
                    (b) "t = insert xs (snd (ts ! i))" 
        by auto
      then show "io_trie_invar t" proof cases
        case a
        then have "t \<in> set (map snd ts)"
          by (metis drop_map in_set_dropD in_set_takeD list_concat_non_elem map_append take_map) 
        then show ?thesis using \<open>\<And> t . t \<in> set (map snd ts) \<Longrightarrow> io_trie_invar t\<close> by blast
      next
        case b
        have "(snd (ts ! i)) \<in> set (map snd ts)"
          using \<open>i < length ts\<close> by auto
        then have "io_trie_invar (snd (ts ! i))" using \<open>\<And> t . t \<in> set (map snd ts) \<Longrightarrow> io_trie_invar t\<close> by blast 
        then show ?thesis using Cons.IH unfolding b by blast
      qed 
    qed
    moreover have "distinct (map fst (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))"
      using update_assoc_list_with_default_key_distinct[OF \<open>distinct (map fst ts)\<close>]
      by (metis \<open>distinct (map fst ts)\<close> \<open>fst (ts ! i) = x\<close> \<open>i < length ts\<close> update_assoc_list_with_default_key_found)
    
    ultimately show ?thesis 
      unfolding \<open>t = IO_Trie ts\<close> \<open>insert (x#xs) (IO_Trie ts) = (IO_Trie (take i ts @ [(x, insert xs (snd (ts ! i)))] @ drop (Suc i) ts))\<close>
      by auto
  next
    case False

    have "io_trie_invar (IO_Tree.insert xs empty)"
      by (simp add: empty_invar Cons.IH) 

    then show ?thesis
      using Cons.prems update_assoc_list_with_default_key_distinct[OF \<open>distinct (map fst ts)\<close>, of x "(IO_Tree.insert xs)" "(IO_Trie [])"]
      unfolding \<open>t = IO_Trie ts\<close> insert.simps
      unfolding update_assoc_list_with_default_key_not_found[OF \<open>distinct (map fst ts)\<close> False] 
      by auto
  qed
qed 




fun paths :: "'a io_trie \<Rightarrow> 'a list list" where
  "paths (IO_Trie []) = [[]]" |
  "paths (IO_Trie (t#ts)) = concat (map (\<lambda> (x,t) . map ((#) x) (paths t)) (t#ts))"



value "insert [1,2,3,4] (empty :: nat io_trie)"
value "insert [1,2,5,6] (insert [1,2,3,4] (empty :: nat io_trie))"
value "insert [1,2,5,7] (insert [1,2,5,6] (insert [1,2,3,4] (empty :: nat io_trie)))"
value "paths (insert [1,2,5,7] (insert [1,2,5,6] (insert [1,2,3,4] (empty :: nat io_trie))))"



lemma paths_empty :
  assumes "[] \<in> set (paths t)"
  shows "t = empty"
proof (rule ccontr)
  assume "t \<noteq> empty"
  then obtain xt xts where "t = IO_Trie (xt#xts)"
    by (metis IO_Tree.empty_def height.cases)
  then have "[] \<in> set (concat (map (\<lambda> (x,t) . map ((#) x) (paths t)) (xt#xts)))"
    using assms by auto
  then show "False" by auto
qed

lemma paths_nonempty :
  assumes "[] \<notin> set (paths t)"
  shows "set (paths t) \<noteq> {}"
using assms proof (induction t rule: io_trie_invar.induct)
  case (1 ts)
  have "ts \<noteq> []" using "1.prems" by auto
  then obtain x t xts where "ts = ((x,t)#xts)"
    using linear_order_from_list_position'.cases
    by (metis old.prod.exhaust) 
  
  then have "t \<in> set (map snd ts)" by auto
    
  show ?case 
  proof (cases "[] \<in> set (paths t)")
    case True
    then show ?thesis  
      unfolding \<open>ts = ((x,t)#xts)\<close> paths.simps by auto
  next
    case False
    show ?thesis 
      using "1.IH"[OF \<open>t \<in> set (map snd ts)\<close> False]  
      unfolding \<open>ts = ((x,t)#xts)\<close> paths.simps by auto
  qed
qed


lemma paths_maximal: "io_trie_invar t \<Longrightarrow> xs' \<in> set (paths t) \<Longrightarrow> \<not> (\<exists> xs'' . xs'' \<noteq> [] \<and> xs'@xs'' \<in> set (paths t))"
proof (induction xs' arbitrary: t)
  case Nil
  then have "t = empty"
    using paths_empty by blast
  then have "paths t = [[]]"
    by (simp add: empty_def)
  then show ?case by auto
next
  case (Cons x xs')

  then have "t \<noteq> empty" unfolding empty_def by auto
  then obtain xt xts where "t = IO_Trie (xt#xts)"
    by (metis IO_Tree.empty_def height.cases)

  obtain t' where "(x,t') \<in> set (xt#xts)"
            and   "xs' \<in> set (paths t')"
    using Cons.prems(2) 
    unfolding \<open>t = IO_Trie (xt#xts)\<close> paths.simps 
    by force

  have "io_trie_invar t'"
    using Cons.prems(1) \<open>(x,t') \<in> set (xt#xts)\<close> unfolding \<open>t = IO_Trie (xt#xts)\<close> by auto

  show ?case 
  proof 
    assume "\<exists>xs''. xs'' \<noteq> [] \<and> (x # xs') @ xs'' \<in> set (paths t)"
    then obtain xs'' where "xs'' \<noteq> []" and "(x # (xs' @ xs'')) \<in> set (paths (IO_Trie (xt # xts)))"
      unfolding \<open>t = IO_Trie (xt#xts)\<close> by force


    obtain t'' where "(x,t'') \<in> set (xt#xts)"
               and   "(xs' @ xs'') \<in> set (paths t'')"
      using \<open>(x # (xs' @ xs'')) \<in> set (paths (IO_Trie (xt # xts)))\<close>
      unfolding \<open>t = IO_Trie (xt#xts)\<close> paths.simps 
      by force

    have "distinct (map fst (xt#xts))"
      using Cons.prems(1) unfolding \<open>t = IO_Trie (xt#xts)\<close> by simp
    then have "t'' = t'"
      using \<open>(x,t') \<in> set (xt#xts)\<close> \<open>(x,t'') \<in> set (xt#xts)\<close>
      by (meson eq_key_imp_eq_value)  
    then have "xs'@xs'' \<in> set (paths t')"
      using \<open>(xs' @ xs'') \<in> set (paths t'')\<close> by auto
    then show "False"
      using \<open>xs'' \<noteq> []\<close> Cons.IH[OF \<open>io_trie_invar t'\<close> \<open>xs' \<in> set (paths t')\<close>] by blast
  qed
qed
            


lemma paths_insert_empty : 
  "paths (insert xs empty) = [xs]"
proof (induction xs)
  case Nil
  then show ?case unfolding empty_def by auto
next
  case (Cons x xs)
  then show ?case unfolding empty_def insert.simps by auto
qed

lemma paths_order :
  assumes "set ts = set ts'"
  and     "length ts = length ts'" (* length requirement not actually necessary *)
shows "set (paths (IO_Trie ts)) = set (paths (IO_Trie ts'))"
  using assms(2,1) proof (induction ts ts' rule: list_induct2)
  case Nil
  then show ?case by auto
next
  case (Cons x xs y ys)

  have scheme: "\<And> f xs ys . set xs = set ys \<Longrightarrow> set (concat (map f xs)) = set (concat (map f ys))"
    by auto

  show ?case 
    using scheme[OF Cons.prems(1), of "(\<lambda>(x, t). map ((#) x) (paths t))"] by simp
qed


(* TODO: move *)
lemma list_index_split_set: 
  assumes "i < length xs"
shows "set xs = set ((xs ! i) # ((take i xs) @ (drop (Suc i) xs)))"  
using assms proof (induction xs arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case proof (cases i)
    case 0
    then show ?thesis by auto
  next
    case (Suc j)
    then have "j < length xs" using Cons.prems by auto
    then have "set xs = set ((xs ! j) # ((take j xs) @ (drop (Suc j) xs)))" using Cons.IH[of j] by blast
    
    have *: "take (Suc j) (x#xs) = x#(take j xs)" by auto
    have **: "drop (Suc (Suc j)) (x#xs) = (drop (Suc j) xs)" by auto
    have ***: "(x # xs) ! Suc j = xs ! j" by auto
    
    show ?thesis
      using \<open>set xs = set ((xs ! j) # ((take j xs) @ (drop (Suc j) xs)))\<close>
      unfolding Suc * ** *** by auto
  qed
qed
  





lemma paths_insert_maximal :
  assumes "io_trie_invar t" 
  shows "set (paths (insert xs t)) = (if (\<exists> xs' . xs@xs' \<in> set (paths t))
                                         then set (paths t)
                                         else Set.insert xs (set (paths t) - {xs' . \<exists> xs'' . xs'@xs'' = xs}))" 
using assms proof (induction xs arbitrary: t)
  case Nil
  then show ?case
    using paths_nonempty by force    
next
  case (Cons x xs)
  show ?case proof (cases "t = empty")
    case True
    show ?thesis 
      unfolding True
      unfolding paths_insert_empty  
      unfolding empty_def paths.simps by auto
  next
    case False
    
    then obtain xt xts where "t = IO_Trie (xt#xts)"
      by (metis IO_Tree.empty_def height.cases)
    then have "t = IO_Trie ((fst xt, snd xt)#xts)" 
      by auto

    have "distinct (map fst (xt#xts))"
      using Cons.prems \<open>t = IO_Trie (xt#xts)\<close> by auto

     have "(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))"
      unfolding \<open>t = IO_Trie ((fst xt, snd xt)#xts)\<close> by simp
    then have "set (paths t) = {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by auto
    then have "Set.insert (x#xs) (set (paths t)) = Set.insert (x#xs) {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by blast

    show ?thesis proof (cases "x \<in> set (map fst (xt#xts))")
      case True
      case True
      then obtain i where "i < length (xt#xts)" and "fst ((xt#xts) ! i) = x"
        by (metis in_set_conv_nth list_map_source_elem)
      then have "((xt#xts) ! i) = (x,snd ((xt#xts) ! i))" by auto

      have "io_trie_invar (snd ((xt # xts) ! i))"
        using Cons.prems \<open>i < length (xt#xts)\<close> unfolding \<open>t = IO_Trie (xt#xts)\<close>
        by (metis \<open>(xt # xts) ! i = (x, snd ((xt # xts) ! i))\<close> in_set_zipE io_trie_invar.simps nth_mem zip_map_fst_snd) 


      have "insert (x#xs) t = IO_Trie (take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_found[OF \<open>distinct (map fst (xt#xts))\<close> \<open>i < length (xt#xts)\<close> \<open>fst ((xt#xts) ! i) = x\<close>]
        by simp
      
      then have "set (paths (insert (x#xs) t)) = set (paths (IO_Trie (take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))))"
        by simp
      also have "... = set (paths (IO_Trie ((x, IO_Tree.insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        using paths_order[of "(take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))" "((x, IO_Tree.insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))"]
        by force
      also have "... = set ((map ((#) x) (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by force
      finally have "set (paths (insert (x#xs) t)) = 
                      set (map ((#) x) (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force
      also have "\<dots> = (image ((#) x) (set (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))))
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto
      finally have pi1: "set (paths (insert (x#xs) t)) = 
                      image ((#) x) (if \<exists>xs'. xs @ xs' \<in> set (paths (snd ((xt # xts) ! i))) then set (paths (snd ((xt # xts) ! i)))
                                                                                           else Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))
                       \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        unfolding Cons.IH[OF \<open>io_trie_invar (snd ((xt # xts) ! i))\<close>] by blast



      have po1: "set (xt#xts) = set ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using list_index_split_set[OF \<open>i < length (xt#xts)\<close>] 
        unfolding \<open>((xt#xts) ! i) = (x,snd ((xt#xts) ! i))\<close>[symmetric] by assumption
      have po2: "length (xt#xts) = length ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using \<open>i < length (xt#xts)\<close> by auto


      have "set (paths t) = set (paths (IO_Trie ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> 
        using paths_order[OF po1 po2] by assumption
      also have "\<dots> = set ((map ((#) x) (paths (snd ((xt # xts) ! i)))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by auto
      finally have "set (paths t) = 
                      set (map ((#) x) (paths (snd ((xt # xts) ! i)))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force

      then have pi2: "set (paths t) = (image ((#) x) (set (paths (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto


      show ?thesis proof (cases "\<exists>xs'. xs @ xs' \<in> set (paths (snd ((xt # xts) ! i)))")
        case True
        then have pi1': "set (paths (insert (x#xs) t)) = image ((#) x) (set (paths (snd ((xt # xts) ! i))))
                                                         \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
          using pi1 by auto

        have "set (paths (IO_Tree.insert (x # xs) t)) = set (paths t)"
          unfolding pi1' pi2 by simp
        moreover have "\<exists>xs'. (x # xs) @ xs' \<in> set (paths t)"
          using True unfolding pi2 by force
        ultimately show ?thesis by simp
      next
        case False
        then have pi1': "set (paths (insert (x#xs) t)) = image ((#) x) (Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))
                                                         \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
          using pi1 by auto

        have pih: "set (paths (IO_Tree.insert xs (snd ((xt # xts) ! i)))) =  
                      Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs})"
          using Cons.IH[OF \<open>io_trie_invar (snd ((xt # xts) ! i))\<close>] False by auto

        have "((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))  
              = Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" 
        proof -
          have "\<And> a . a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs})) \<Longrightarrow>
                       a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
            by fastforce
          moreover have "\<And> a . a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs}) \<Longrightarrow>
                                a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))"
          proof -
            fix a assume "a \<in> Set.insert (x # xs) ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
            then consider (a) "a = (x#xs)" |
                          (b) "a \<in> ((#) x ` set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})" by blast
            then show "a \<in> ((#) x ` Set.insert xs (set (paths (snd ((xt # xts) ! i))) - {xs'. \<exists>xs''. xs' @ xs'' = xs}))" 
            proof cases
              case a
              then show ?thesis by blast
            next
              case b
              then show ?thesis by force
            qed 
          qed
          ultimately show ?thesis by blast
        qed

        have "set (paths (IO_Tree.insert (x # xs) t)) = Set.insert (x # xs) (set (paths t) - {xs'. \<exists>xs''. xs' @ xs'' = x # xs})"
          unfolding pi1' pi2 
end (*
      
        
        
        
        
        moreover have "\<not>(\<exists>xs'. (x # xs) @ xs' \<in> set (paths t))"
          using False unfolding pi2 
end (*
        ultimately show ?thesis by simp
      qed


end (*
      show ?thesis 
    next
      case False
      have "insert (x#xs) t = IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)]))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_not_found[OF \<open>distinct (map fst (xt#xts))\<close> False]
        by simp
      
      have "(paths (IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)])))) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts @ [(x, IO_Tree.insert xs empty)]))"
        unfolding paths.simps empty_def by simp
      also have "... = (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))) @ (map ((#) x) (paths (insert xs empty))) "
        by auto
      finally have "paths (insert (x#xs) t) = (paths t) @ [x#xs]"
        unfolding \<open>insert (x#xs) t = IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)]))\<close>
                  \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close>[symmetric]
                  paths_insert_empty 
        by auto
      then have "set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))"
        by force
        
        
      have "\<And> p . p \<in> set (paths t) \<Longrightarrow> p \<noteq> [] \<and> hd p \<noteq> x"
        using False
        unfolding \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close> by force
      then have "\<And> xs' . xs' \<in> set (paths t) \<Longrightarrow> \<not>(\<exists> xs'' . xs'@xs'' = x#xs)"
        by (metis hd_append2 list.sel(1))
      then have "set (paths t) = (set (paths t) - {xs' . \<exists> xs'' . xs'@xs'' = x#xs})"
        by blast
      then show ?thesis 
        unfolding \<open>set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))\<close>
        using \<open>\<And>p. p \<in> set (paths t) \<Longrightarrow> p \<noteq> [] \<and> hd p \<noteq> x\<close> by force
    qed
  qed
qed


end (*

lemma "io_trie_invar t \<Longrightarrow> set (paths (insert xs t)) = {xs' . xs' \<in> Set.insert xs (set (paths t)) \<and> \<not> (\<exists> xs'' . xs'' \<noteq> [] \<and> xs'@xs'' \<in> Set.insert xs (set (paths t)))}"
proof (induction xs arbitrary: t)
  case Nil
  show ?case proof (cases "[] \<in> set (paths t)")
    case True
    have "paths t = [[]]"
      using paths_empty[OF True] unfolding empty_def by auto
    show ?thesis using paths_maximal[OF Nil] unfolding insert.simps \<open>paths t = [[]]\<close> by auto
  next
    case False
    then have "\<exists> xs''. xs'' \<noteq> [] \<and> [] @ xs'' \<in> Set.insert [] (set (paths t))"  
      using paths_nonempty[OF False]
      by (metis all_not_in_conv append.left_neutral insert_iff) 
    then have *: "{xs' \<in> Set.insert [] (set (paths t)). \<nexists>xs''. xs'' \<noteq> [] \<and> xs' @ xs'' \<in> Set.insert [] (set (paths t))}
                = {xs' \<in> (set (paths t)). \<nexists>xs''. xs'' \<noteq> [] \<and> xs' @ xs'' \<in> (set (paths t))}"
      by blast
    
    show ?thesis 
      using paths_maximal[OF Nil] unfolding insert.simps * by blast
  qed
next
  case (Cons x xs)

  show ?case proof (cases "t = empty")
    case True
    show ?thesis 
      unfolding True
      unfolding paths_insert_empty  
      unfolding empty_def paths.simps by auto
  next
    case False
    
    then obtain xt xts where "t = IO_Trie (xt#xts)"
      by (metis IO_Tree.empty_def height.cases)
    then have "t = IO_Trie ((fst xt, snd xt)#xts)" 
      by auto

    have "distinct (map fst (xt#xts))"
      using Cons.prems \<open>t = IO_Trie (xt#xts)\<close> by auto

    have "(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))"
      unfolding \<open>t = IO_Trie ((fst xt, snd xt)#xts)\<close> by simp
    then have "set (paths t) = {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by auto
    then have "Set.insert (x#xs) (set (paths t)) = Set.insert (x#xs) {x#xs | x xs t . (x,t) \<in> set (xt#xts) \<and> xs \<in> set (paths t)}"
      by blast

    show ?thesis proof (cases "x \<in> set (map fst (xt#xts))")
      case True
      then obtain i where "i < length (xt#xts)" and "fst ((xt#xts) ! i) = x"
        by (metis in_set_conv_nth list_map_source_elem)
      then have "((xt#xts) ! i) = (x,snd ((xt#xts) ! i))" by auto

      have "io_trie_invar (snd ((xt # xts) ! i))"
        using Cons.prems \<open>i < length (xt#xts)\<close> unfolding \<open>t = IO_Trie (xt#xts)\<close>
        by (metis \<open>(xt # xts) ! i = (x, snd ((xt # xts) ! i))\<close> in_set_zipE io_trie_invar.simps nth_mem zip_map_fst_snd) 


      have "insert (x#xs) t = IO_Trie (take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_found[OF \<open>distinct (map fst (xt#xts))\<close> \<open>i < length (xt#xts)\<close> \<open>fst ((xt#xts) ! i) = x\<close>]
        by simp
      
      then have "set (paths (insert (x#xs) t)) = set (paths (IO_Trie (take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))))"
        by simp
      also have "... = set (paths (IO_Trie ((x, IO_Tree.insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        using paths_order[of "(take i (xt # xts) @ [(x, IO_Tree.insert xs (snd ((xt # xts) ! i)))] @ drop (Suc i) (xt # xts))" "((x, IO_Tree.insert xs (snd ((xt # xts) ! i))) # (take i (xt # xts) @ drop (Suc i) (xt # xts)))"]
        by force
      also have "... = set ((map ((#) x) (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by force
      finally have "set (paths (insert (x#xs) t)) = 
                      set (map ((#) x) (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force
      also have "\<dots> = (image ((#) x) (set (paths (IO_Tree.insert xs (snd ((xt # xts) ! i))))))
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto
      finally have pi1: "set (paths (insert (x#xs) t)) = 
                      (image ((#) x) {xs' \<in> Set.insert xs (set (paths (snd ((xt # xts) ! i)))). \<nexists>xs''. xs'' \<noteq> [] \<and> xs' @ xs'' \<in> Set.insert xs (set (paths (snd ((xt # xts) ! i))))})
                       \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        unfolding Cons.IH[OF \<open>io_trie_invar (snd ((xt # xts) ! i))\<close>] by blast


      have po1: "set (xt#xts) = set ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using list_index_split_set[OF \<open>i < length (xt#xts)\<close>] 
        unfolding \<open>((xt#xts) ! i) = (x,snd ((xt#xts) ! i))\<close>[symmetric] by assumption
      have po2: "length (xt#xts) = length ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        using \<open>i < length (xt#xts)\<close> by auto


      have "set (paths t) = set (paths (IO_Trie ((x,snd ((xt#xts) ! i)) # ((take i (xt # xts) @ drop (Suc i) (xt # xts))))))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> 
        using paths_order[OF po1 po2] by assumption
      also have "\<dots> = set ((map ((#) x) (paths (snd ((xt # xts) ! i)))) @ (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts)))))"
        unfolding paths.simps by auto
      finally have "set (paths t) = 
                      set (map ((#) x) (paths (snd ((xt # xts) ! i)))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by force

      then have pi2: "set (paths t) = (image ((#) x) (set (paths (snd ((xt # xts) ! i))))) 
                      \<union> set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
        by auto
(*      finally have "set (paths t) =  {}"
        using Cons.IH[OF \<open>io_trie_invar (snd ((xt # xts) ! i))\<close>] sorry *)


      define paths_shared where paths_shared_def: "paths_shared = set (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (take i (xt # xts) @ drop (Suc i) (xt # xts))))"
      define paths_inserted where paths_inserted_def: "paths_inserted = (image ((#) x) {xs' \<in> Set.insert xs (set (paths (snd ((xt # xts) ! i)))). \<nexists>xs''. xs'' \<noteq> [] \<and> xs' @ xs'' \<in> Set.insert xs (set (paths (snd ((xt # xts) ! i))))})"
      define paths_orig where paths_orig_def: "paths_orig = set (map ((#) x) (paths (snd ((xt # xts) ! i))))"


      have "set (paths (insert (x#xs) t)) = paths_inserted \<union> paths_shared"
        unfolding paths_inserted_def paths_shared_def pi1 by blast
          

      show ?thesis
        unfolding pi1 pi2  


      
        
        

      then show ?thesis sorry
    next
      case False
      have "insert (x#xs) t = IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)]))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> insert.simps
        unfolding update_assoc_list_with_default_key_not_found[OF \<open>distinct (map fst (xt#xts))\<close> False]
        by simp
      
      have "(paths (IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)])))) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts @ [(x, IO_Tree.insert xs empty)]))"
        unfolding paths.simps empty_def by simp
      also have "... = (concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))) @ (map ((#) x) (paths (insert xs empty))) "
        by auto
      finally have "paths (insert (x#xs) t) = (paths t) @ [x#xs]"
        unfolding \<open>insert (x#xs) t = IO_Trie (xt # (xts @ [(x, IO_Tree.insert xs empty)]))\<close>
                  \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close>[symmetric]
                  paths_insert_empty 
        by auto
      then have "set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))"
        by force
        
        
      have "\<And> p . p \<in> set (paths t) \<Longrightarrow> hd p \<noteq> x"
        using False
        unfolding \<open>(paths t) = concat (map (\<lambda>(x, t). map ((#) x) (paths t)) (xt # xts))\<close> by force
      then have "\<not>(\<exists> xs'' . xs'' \<noteq> [] \<and> (x#xs)@xs'' \<in> Set.insert (x#xs) (set (paths t)))"
        by fastforce

      moreover have "\<And> xs' . xs' \<in> set (paths t) \<Longrightarrow> \<nexists>xs''. xs'' \<noteq> [] \<and> xs' @ xs'' \<in> Set.insert (x#xs) (set (paths t))"
        using paths_maximal[OF Cons.prems(1)] \<open>\<And> p . p \<in> set (paths t) \<Longrightarrow> hd p \<noteq> x\<close>
        by (metis IO_Tree.empty_def \<open>\<And>thesis. (\<And>xt xts. t = IO_Trie (xt # xts) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> hd_append insert_iff io_trie.inject list.distinct(1) list.sel(1) paths_empty) 

      ultimately show ?thesis 
        unfolding \<open>set (paths (insert (x#xs) t)) = Set.insert (x#xs) (set (paths t))\<close> by blast
    qed
  qed
qed

   


end (*
    obtain t' where "(x,t') \<in> set (xt#xts)"
              and   "xs \<in> set (paths t')"
      using Cons.prems 
      unfolding \<open>t = IO_Trie (xt#xts)\<close> paths.simps 
      
  
    have "io_trie_invar t'"
      using Cons.prems(1) \<open>(x,t') \<in> set (xt#xts)\<close> unfolding \<open>t = IO_Trie (xt#xts)\<close> by auto
  
    show ?case 
    proof 
      assume "\<exists>xs''. xs'' \<noteq> [] \<and> (x # xs') @ xs'' \<in> set (paths t)"
      then obtain xs'' where "xs'' \<noteq> []" and "(x # (xs' @ xs'')) \<in> set (paths (IO_Trie (xt # xts)))"
        unfolding \<open>t = IO_Trie (xt#xts)\<close> by force
  
  
      obtain t'' where "(x,t'') \<in> set (xt#xts)"
                 and   "(xs' @ xs'') \<in> set (paths t'')"
        using \<open>(x # (xs' @ xs'')) \<in> set (paths (IO_Trie (xt # xts)))\<close>
        unfolding \<open>t = IO_Trie (xt#xts)\<close> paths.simps 
        by force
  
      have "distinct (map fst (xt#xts))"
        using Cons.prems(1) unfolding \<open>t = IO_Trie (xt#xts)\<close> by simp
      then have "t'' = t'"
        using \<open>(x,t') \<in> set (xt#xts)\<close> \<open>(x,t'') \<in> set (xt#xts)\<close>
        by (meson eq_key_imp_eq_value)  
      then have "xs'@xs'' \<in> set (paths t')"
        using \<open>(xs' @ xs'') \<in> set (paths t'')\<close> by auto
      then show "False"
        using \<open>xs'' \<noteq> []\<close> Cons.IH[OF \<open>io_trie_invar t'\<close> \<open>xs' \<in> set (paths t')\<close>] by blast
    qed
  
  
    then show ?case sorry
qed


end (*

fold-insert over list/set of sequences \<rightarrow> show that all maximal sequences are contained


end 