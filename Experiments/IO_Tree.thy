theory IO_Tree
imports FSM
begin

datatype 'a IO_Tree = IO_Tree 'a "'a IO_Tree list" 
datatype 'a IO_Tree_Set = IO_Tree_Set "'a \<Rightarrow> 'a IO_Tree option"

fun node_value :: "'a IO_Tree \<Rightarrow> 'a" where
  "node_value (IO_Tree a ts) = a"

fun from_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a IO_Tree" where
  "from_list a [] = (IO_Tree a [])" |
  "from_list a (x#xs) = (IO_Tree a [from_list x xs])"

fun insert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a IO_Tree \<Rightarrow> 'a IO_Tree" where
  "insert a [] t = t" |
  "insert a (x#xs) (IO_Tree y ts) = (if a = y 
    then case find_remove (\<lambda> t . node_value t = x) ts of
      Some (t,ts') \<Rightarrow> (IO_Tree y ((insert x xs t)#ts')) |
      None         \<Rightarrow> (IO_Tree y ((from_list x xs)#ts))
    else (IO_Tree y ts))"

value "from_list 0 [1::nat,2,3,4,5]"
value "insert 0 [1,30,80] (from_list 0 [1::nat,2,3,4,5])"
value "insert 0 [1,30,90] (insert 0 [1,30,80] (from_list 0 [1::nat,2,3,4,5]))"



fun paths :: "'a IO_Tree \<Rightarrow> 'a list list" where
  "paths (IO_Tree a []) = [[a]]" |
  "paths (IO_Tree a (t#ts)) = map ((#) a) (concat (map paths (t#ts)))" 

value "paths (insert 0 [1,30,90] (insert 0 [1,30,80] (from_list 0 [1::nat,2,3,4,5])))"


lemma path_from_list :
  "paths (from_list t p) = [(t#p)]"
  by (induction p arbitrary: t; auto)



(* TODO: write induction scheme based on tree height *)

fun max_elem_value_nat_fun :: "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "max_elem_value_nat_fun f x xs = max (f x) (foldr (\<lambda> x' prev_max . max (f x') prev_max) xs 0)"

lemma max_elem_value_nat_fun_ex :
  "\<exists> x' . x' \<in> set (x#xs) \<and> max_elem_value_nat_fun f x xs = f x'"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
qed

end (*

fun height :: "'a IO_Tree \<Rightarrow> nat" where
  "height (IO_Tree a []) = 0" |
  "height (IO_Tree a (t#ts)) = 


lemma paths_non_nil :
  "paths t \<noteq> []"
proof -
  obtain a ts where "t = IO_Tree a ts"
    using IO_Tree.exhaust by auto 
  then show ?thesis proof (cases ts; auto)

lemma path_insert_set : 
  "set (paths (insert x xs (IO_Tree x ts))) = Set.insert (x#xs) (set (paths (IO_Tree x ts)) - {p' . \<exists> p'' .  (x#xs) = p'@p''})"
proof (induction xs arbitrary: x ts)
  case Nil

  have "(insert x [] (IO_Tree x ts)) = (IO_Tree x ts)" by auto
  show ?case proof (cases ts)
    case Nil
    then have "paths (IO_Tree x ts) = [[x]]" by auto
    show ?thesis unfolding \<open>(insert x [] (IO_Tree x ts)) = (IO_Tree x ts)\<close> \<open>paths (IO_Tree x ts) = [[x]]\<close> by auto
  next
    case (Cons t ts')
    have "map paths (t # ts') \<noteq> []" by auto

    have "\<And> t . paths t \<noteq> []" 
    moreover have "\<And> p . p \<in> set (map paths (t # ts')) \<Longrightarrow> p \<noteq> []" 
    proof -
      fix p assume "p \<in> set (map paths (t # ts'))"
      obtain a' ts'' where "t = IO_Tree a' ts''" 


end (*
    then have "\<And> p . p \<in> set (map ((#) x) (concat (map paths (t # ts')))) \<Longrightarrow> length p > 1" 
    proof - 
      fix p assume "p \<in> set (map ((#) x) (concat (map paths (t # ts'))))"
      then obtain p' where "p' \<in> 
    then have "[x] \<notin> set (paths (IO_Tree x ts))"  unfolding Cons paths.simps 
    then show ?thesis sorry
  qed

  have "{p' . \<exists> p'' .  (x#[]) = p'@p''} = {[],[x]}" 

  then show ?case proof (cases 
next
  case (Cons a xs)
  then show ?case sorry
qed



end (* 



lemma path_insert_set : 
  "set (paths (insert x xs (IO_Tree x ts))) 
    = (if (\<exists> p' . ((x#xs)@p') \<in> set (paths (insert x xs (IO_Tree x ts))) \<and> p' \<noteq> []) 
        then set (paths (IO_Tree x ts))
        else Set.insert p (set (paths (IO_Tree x ts)) - {p' . \<exists> p'' .  p = p'@p''}))"


lemma path_insert :
  "\<exists> p' . ((x#xs)@p') \<in> set (paths (insert x xs (IO_Tree x ts)))" 
proof (cases "find_remove (\<lambda> t . node_value t = x) ts")
  case None
  then show ?thesis then have 
next
  case (Some a)
  then show ?thesis sorry
qed



end (*

lemma path_insert_set : "set (paths (insert x xs (IO_Tree x ts))) = (if (\<exists> p' . ((x#xs)@p') \<in> set (paths (insert x xs (IO_Tree x ts))) \<and> p' \<noteq> []) 
                then set (paths (IO_Tree x ts))
                else insert p (set (paths (IO_Tree x ts)) - {p' . prefix p' p}))"


lemma path_insert_fold:
  sth like: folding all lists in list of lists into a tree_set contains (exactly) all maximal lists of the original list of lists as paths





end 