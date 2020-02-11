theory Test_Suite_ATC_RBT
imports Test_Suite_ATC "HOL-Library.RBT_Set" (*"HOL-Data_Structures.AVL_Set"*)
begin

(* from RBT_Set : *)
(*
  Users should be aware that by including this file all code equations
  outside of List.thy using 'a list as an implementation of sets cannot be
  used for code generation. If such equations are not needed, they can be
  deleted from the code generator. Otherwise, a user has to provide their 
  own equations using RBT trees. 
*)



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







definition calculate_test_suite_rbt :: "('a::linorder,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> ('a,'b) Preamble) list)" where
  "calculate_test_suite_rbt M m = 
    (let 
         RDSSL = r_distinguishable_state_pairs_with_separators_naive M;
         RDS  = set (map fst RDSSL);
         RDP  = filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> RDS) (map set (pow_list (nodes_from_distinct_paths M))); 
         MPRD = filter (\<lambda> S . \<not>(\<exists> S' \<in> set RDP . S \<subset> S')) RDP;  
         DRSP = d_reachable_states_with_preambles M;
         DRS  = map fst DRSP; 
         MRS  = map (\<lambda>S. (S, S \<inter> set DRS)) MPRD; 
         MTP  = map (\<lambda> q . (q,m_traversal_paths_with_witness M q MRS m)) DRS;
         fTP  = list_as_fun MTP []; 
         fRD  = \<lambda> q1 q2 . snd (the (find (\<lambda> qqA . fst qqA = (q1,q2)) RDSSL)); 
         PMTP = concat (map (\<lambda> (q,P) . map (\<lambda>(p,d) . (q,p)) (fTP q)) DRSP);
         PrefixPairTests 
              = concat (map (\<lambda> (q,P) . prefix_pair_tests' q fRD (fTP q)) DRSP);             
         PreamblePrefixTests
              = concat (map (\<lambda> (q,P) . preamble_prefix_tests' q fRD (fTP q) DRSP) DRSP);              
         PreamblePairTests
              = preamble_pair_tests' DRSP RDSSL
      
    in  (PrefixPairTests @ PreamblePrefixTests @ PreamblePairTests, DRSP))"

value "calculate_test_suite_rbt M_ex_H 4"

lemma calculate_test_suite_rbt_calculate_test_suite' :
  "calculate_test_suite_rbt = calculate_test_suite'"
  unfolding calculate_test_suite_rbt_def calculate_test_suite'_def by force


(*

fun convert_test_suite_elem :: "(('a::linorder \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> ('a,'b) Preamble)) \<Rightarrow> ('a \<times> ('a,'b) Preamble) list \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite_elem (q,p,atcs) preambles = empty"

thm foldl.simps

fun convert_test_suite :: "(('a::linorder \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> ('a,'b) Preamble) list) \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite (elems,preambles) = foldl (\<lambda> prev elem . AVL_Set.union prev prev ) empty elems"

*)


end 