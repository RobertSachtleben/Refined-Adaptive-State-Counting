theory Test_Suite_ATC_RBT
imports Test_Suite_ATC "HOL-Library.RBT_Set" "HOL-Library.RBT_Mapping" (*"HOL-Data_Structures.AVL_Set"*)
begin

(* from RBT_Set : *)
(*
  Users should be aware that by including this file all code equations
  outside of List.thy using 'a list as an implementation of sets cannot be
  used for code generation. If such equations are not needed, they can be
  deleted from the code generator. Otherwise, a user has to provide their 
  own equations using RBT trees. 
*)

lemma x:
  fixes X :: "('a :: linorder) set"
  
  shows "set (sorted_list_of_set X) = X"

end (*
value "sorted_list_of_set (Mapping.keys (Mapping.empty :: (nat,nat) Mapping.mapping))"

instantiation sum :: (ord,ord) ord
begin

fun less_eq_sum ::  "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  "less_eq_sum (Inl a) (Inl b) = (a \<le> b)" |
  "less_eq_sum (Inl a) (Inr b) = True" |
  "less_eq_sum (Inr a) (Inl b) = False" |
  "less_eq_sum (Inr a) (Inr b) = (a \<le> b)" 

fun less_sum ::  "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
  "less_sum a b = (a \<le> b \<and> a \<noteq> b)"

instance by (intro_classes)
end

instantiation sum :: (linorder,linorder) linorder
begin

lemma less_le_not_le_sum :
  fixes x :: "'a + 'b"
  and   y :: "'a + 'b"
shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
  by (induct x; induct y; auto)
  
lemma order_refl_sum :
  fixes x :: "'a + 'b"
shows "x \<le> x"
  by (induct x; auto)

lemma order_trans_sum :
  fixes x :: "'a + 'b"
  fixes y :: "'a + 'b"
  fixes z :: "'a + 'b"
shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  by (induct x; induct y; induct z; auto)

lemma antisym_sum :
  fixes x :: "'a + 'b"
  fixes y :: "'a + 'b"
shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  by (induct x; induct y; auto)

lemma linear_sum :
  fixes x :: "'a + 'b"
  fixes y :: "'a + 'b"
shows "x \<le> y \<or> y \<le> x"
  by (induct x; induct y; auto)




instance 
  using less_le_not_le_sum order_refl_sum order_trans_sum antisym_sum linear_sum 
  by (intro_classes; metis+)
end



instantiation list :: (ord) ord
begin

fun less_eq_list ::  "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "less_eq_list [] xs = True" |
  "less_eq_list (x#xs) [] = False" |
  "less_eq_list (x#xs) (y#ys) = (x < y \<or> (x = y \<and> less_eq_list xs ys))"  

fun less_list ::  "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "less_list a b = (a \<le> b \<and> a \<noteq> b)"

instance by (intro_classes)
end

instantiation list :: (linorder) linorder
begin

lemma less_le_not_le_list :
  fixes x :: "'a list"
  and   y :: "'a list"
shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
proof 
  show "x < y \<Longrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using less_eq_list.elims(2) by (induction rule: less_eq_list.induct; fastforce)
  show "x \<le> y \<and> \<not> y \<le> x \<Longrightarrow> x < y"
    by (induction rule: less_eq_list.induct; auto)
qed

  
lemma order_refl_list :
  fixes x :: "'a list"
shows "x \<le> x"
proof (induction x)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case by (cases xs; auto)
qed





lemma order_trans_list :
  fixes x :: "'a list"
  fixes y :: "'a list"
  fixes z :: "'a list"
shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
proof (induction x arbitrary: y z)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case proof (induction y arbitrary: z)
    case Nil
    then show ?case by auto
  next
    case (Cons y ys)
    then show ?case proof (induction z)
      case Nil
      then show ?case by auto
    next
      case (Cons z zs)
      from \<open>x # xs \<le> y # ys\<close> \<open>y # ys \<le> z # zs\<close>
      consider "x < y" |
               "x = y \<and> y < z" |
               "x = y \<and> xs \<le> ys \<and> y = z \<and> ys \<le> zs"
        using less_eq_list.simps(3) by blast 
      then show ?case using Cons.prems(2,4) by (cases; auto)
    qed
  qed
qed
  

lemma antisym_list :
  fixes x :: "'a list"
  fixes y :: "'a list"
shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  by (meson less_le_not_le_list less_list.elims(3))

lemma linear_list :
  fixes x :: "'a list"
  fixes y :: "'a list"
shows "x \<le> y \<or> y \<le> x"
  by (induct rule: less_eq_list.induct; auto)




instance 
  using less_le_not_le_list order_refl_list order_trans_list antisym_list linear_list 
  by (intro_classes; metis+)
end





instantiation FSM_ext :: (ord,ord) ord
begin

fun less_eq_FSM_ext ::  "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> bool" where
  "less_eq_FSM_ext M1 M2 = 
    (if initial M1 < initial M2 
      then True
      else ((initial M1 = initial M2) \<and> (if inputs M1 < inputs M2
        then True
        else ((inputs M1 = inputs M2) \<and> (if outputs M1 < outputs M2
          then True
          else ((outputs M1 = outputs M2) \<and> (if transitions M1 < transitions M2
            then True
            else ((transitions M1 = transitions M2) \<and> (more M1 \<le> more M2)))))))))"

fun less_FSM_ext ::  "('a,'b) FSM_scheme \<Rightarrow> ('a,'b) FSM_scheme \<Rightarrow> bool" where
  "less_FSM_ext a b = (a \<le> b \<and> a \<noteq> b)"

instance by (intro_classes)
end


instantiation FSM_ext :: (linorder,linorder) linorder
begin



lemma less_le_not_le_FSM :
  fixes x :: "('a,'b) FSM_scheme"
  and   y :: "('a,'b) FSM_scheme"
shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
proof 
  show "x < y \<Longrightarrow> x \<le> y \<and> \<not> y \<le> x" 
    unfolding less_FSM_ext.simps less_eq_FSM_ext.simps
    by (metis dual_order.antisym equality not_less_iff_gr_or_eq) 
  show "x \<le> y \<and> \<not> y \<le> x \<Longrightarrow> x < y"
    unfolding less_FSM_ext.simps less_eq_FSM_ext.simps
    by blast
qed


lemma order_refl_FSM :
  fixes x :: "('a,'b) FSM_scheme"
  shows "x \<le> x" 
  by auto


lemma order_trans_FSM :
  fixes x :: "('a,'b) FSM_scheme"
  fixes y :: "('a,'b) FSM_scheme"
  fixes z :: "('a,'b) FSM_scheme"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  unfolding less_eq_FSM_ext.simps 
  using less_trans[of "initial x" "initial y"]
        less_trans[of "inputs x" "inputs y"]
        less_trans[of "outputs x" "outputs y"]
        less_trans[of "transitions x" "transitions y"]
        less_trans[of "more x" "more y"]
  using order_trans[of "initial x" "initial y"]
        order_trans[of "inputs x" "inputs y"]
        order_trans[of "outputs x" "outputs y"]
        order_trans[of "transitions x" "transitions y"]
        order_trans[of "more x" "more y"]
  by metis 
  

lemma antisym_FSM :
  fixes x :: "('a,'b) FSM_scheme"
  fixes y :: "('a,'b) FSM_scheme"
shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  unfolding less_eq_FSM_ext.simps
  by (metis dual_order.antisym equality not_less_iff_gr_or_eq) 


lemma linear_FSM :
  fixes x :: "('a,'b) FSM_scheme"
  fixes y :: "('a,'b) FSM_scheme"
shows "x \<le> y \<or> y \<le> x"
  unfolding less_eq_FSM_ext.simps
  by (metis linear not_less_iff_gr_or_eq) 




instance 
  using less_le_not_le_FSM order_refl_FSM order_trans_FSM antisym_FSM linear_FSM 
  by (intro_classes; metis+)
end









lemma remdups_by_RBT :
  "set (remdups xs) = set (RBT.keys (foldl (\<lambda> prev t . RBT.insert t () prev) RBT.empty xs))"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: empty_Set set_keys) 
next
  case (snoc x xs)
  then show ?case
    using RBT_Set.insert_code(1) set_keys by fastforce 
qed




value "calculate_test_suite M_ex_H 4"
value "calculate_test_suite_set M_ex_H 4"
(*

lemma x : "set (fst (calculate_test_suite' M m)) = set (fst (calculate_test_suite_rbt M m))"
  unfolding calculate_test_suite_rbt_def calculate_test_suite'_def  
  unfolding Let_def fst_conv
  unfolding set_append set_remdups 
  using set_append set_remdups
  
  unfolding remdups_by_RBT

lemma calculate_test_suite_rbt_calculate_test_suite' :
  assumes "calculate_test_suite' M m = (tl1,pr1)"
  and     "calculate_test_suite_rbt M m = (tl2,pr2)"
shows "set tl1 = set tl2"
and   "pr1 = pr2"
  using assms 
  unfolding calculate_test_suite_rbt_def calculate_test_suite'_def  
  unfolding Let_def
  using remdups_by_RBT
  
  *)


(*

fun convert_test_suite_elem :: "(('a::linorder \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> ('a,'b) Preamble)) \<Rightarrow> ('a \<times> ('a,'b) Preamble) list \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite_elem (q,p,atcs) preambles = empty"

thm foldl.simps

fun convert_test_suite :: "(('a::linorder \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> ('a,'b) Preamble) list) \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite (elems,preambles) = foldl (\<lambda> prev elem . AVL_Set.union prev prev ) empty elems"

*)


end 