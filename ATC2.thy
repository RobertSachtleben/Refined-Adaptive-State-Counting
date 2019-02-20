theory ATC2
imports FSM2 "~~/src/HOL/Library/Finite_Map"
begin

(* ATCs with maps of possibly infinite range *)
datatype ('in, 'out) ATC_u = Leaf_u | Node_u 'in "('out, (('in, 'out) ATC_u)) map"

inductive subtest :: "('in, 'out) ATC_u \<Rightarrow> ('in, 'out) ATC_u \<Rightarrow> bool" where
  "t \<in> ran f \<Longrightarrow> subtest t (Node_u x f)"

lemma accp_subtest : "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf_u
  then show ?case by (meson ATC_u.distinct(1) accp.simps subtest.cases)
next
  case (Node_u x f)
  have IH: "Wellfounded.accp subtest t" if "t \<in> ran f" for "t"
    using Node_u[of "Some t" t] and that by (auto simp: eq_commute ran_def)
  show ?case by (rule accpI) (auto intro: IH elim!: subtest.cases)
qed


definition subtest_rel where "subtest_rel = {(t, Node_u x f) |f x t. t \<in> ran f}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "t \<in> ran f \<Longrightarrow> (t, Node_u x f) \<in> subtest_rel"
  by (simp add: subtest_rel_def)

lemma subtest_relI' [intro]: "Some t = f y \<Longrightarrow> (t, Node_u x f) \<in> subtest_rel"
  by (auto simp: subtest_rel_def ran_def)

lemma wf_subtest_rel [simp, intro]: "wf subtest_rel" 
  using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  by auto

function finite_ATC :: "('in, 'out) ATC_u \<Rightarrow> bool" where
  "finite_ATC Leaf_u = True" |
  "finite_ATC (Node_u x f) = ((finite (ran f)) \<and> (\<forall> t \<in> ran f . finite_ATC t))"
by pat_completeness auto
termination by (relation subtest_rel) auto

function atc_height_u :: "('in, 'out) ATC_u \<Rightarrow> nat" where
  "atc_height_u Leaf_u = 0" |
  "atc_height_u (Node_u x f) = 1 + Max (image (atc_height_u) (ran f))"
  by pat_completeness auto
termination  by (relation subtest_rel) auto




(* ATCs with maps of finite range *)
typedef ('in, 'out) ATC = "{A :: ('in, 'out) ATC_u . finite_ATC A}" 
  using finite_ATC.simps(1) by blast



setup_lifting type_definition_ATC

lift_definition Leaf :: "('in,'out) ATC" is "Abs_ATC Leaf_u" done
lift_definition Node :: "'in \<Rightarrow> ('out, ('in,'out) ATC) map \<Rightarrow>('in,'out) ATC" is "\<lambda> x f . Abs_ATC (Node_u x (\<lambda> y . case (f y) of
  None \<Rightarrow> None |
  Some t \<Rightarrow> Some (Rep_ATC t)))" done


fun atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
  "atc_height A = atc_height_u (Rep_ATC A)"

lemma atc_height_subtest :
  assumes "Rep_ATC B \<in> ran f"
  and     "Rep_ATC A = Node_u x f"
  shows "atc_height B < atc_height A"
proof -
  have "finite (ran f)" using assms by (metis Rep_ATC finite_ATC.simps(2) mem_Collect_eq) 
  moreover have "atc_height_u (Rep_ATC B) \<in> (image (atc_height_u) (ran f))" using assms by simp 
  ultimately have "atc_height_u (Rep_ATC B) < atc_height_u (Node_u x f)" unfolding atc_height_u.simps
    by (meson Max_ge finite_imageI less_add_same_cancel2 linorder_not_le order_trans zero_less_one) 
  then show ?thesis using assms unfolding atc_height.simps by simp
qed

function IO :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in \<times> 'out) list set" where
  "IO M q A = (case (Rep_ATC A) of
    Leaf_u \<Rightarrow> {[]} |
    (Node_u x f) \<Rightarrow> {[(x,y)] | y q2 . path M [((x,y),q2)] q \<and> f y = None }
                       \<union> {(x,y) # io2 | y q2 t2 io2 . path M [((x,y),q2)] q \<and> f y = Some t2 \<and> io2 \<in> (IO M q2 (Abs_ATC t2))})"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(a,b,c). atc_height c)")
  apply blast 













datatype ('in, 'out) ATC = Leaf | Node 'in "('out, (('in, 'out) ATC)) fmap"



inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
  "t \<in> fmran' f \<Longrightarrow> subtest t (Node x f)"

lemma accp_subtest : "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (meson ATC.distinct(1) accp.simps subtest.cases)
next
  case (Node x f)
  have IH: "Wellfounded.accp subtest t" if "t \<in> fmran' f" for "t"
    using Node[of t] and that by (auto simp: eq_commute ran_def)
  show ?case by (rule accpI) (auto intro: IH elim!: subtest.cases)
qed


definition subtest_rel where "subtest_rel = {(t, Node x f) |f x t. t \<in> fmran' f}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "t \<in> fmran' f \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (simp add: subtest_rel_def)

(*lemma subtest_relI' [intro]: "Some t = f y \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (auto simp: subtest_rel_def ran_def)
*)

lemma wf_subtest_rel [simp, intro]: "wf subtest_rel" 
  using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  by auto

function atc_size :: "('in, 'out) ATC \<Rightarrow> nat" where
  "atc_size Leaf = 0" |
  "atc_size (Node x f) = 1 + \<Sum> (image atc_size (fset (fmran f)))"
 (* "atc_size (Node x f) = 1 + fsum id (fimage atc_size (fmran f))"*)
  by pat_completeness auto
(*termination by (metis "termination" fmran'_alt_def subtest_relI wf_subtest_rel) *)
termination by (metis "termination" fmran'_alt_def subtest_relI wf_subtest_rel) 

function atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
  "atc_height Leaf = 0" |
  "atc_height (Node x f) = 1 + Max (image atc_height (fmran' f))"
  by pat_completeness auto
termination by (relation subtest_rel) auto


lemma subtest_size : 
  assumes "t |\<in>| fmran f"
  shows "atc_size t < atc_size (Node x f)"
proof -
  have size_el : "atc_size t \<in> (image atc_size (fset (fmran f)))" using assms by (simp add: fmember.rep_eq) 
  moreover have "finite (fset (fmran f))" by simp 
  ultimately have "atc_size t \<le> \<Sum> (image atc_size (fset (fmran f)))"
    by (meson finite_surj order_refl sum_nonneg_leq_bound zero_le) 
  then show ?thesis using assms  by auto   
qed


lemma is_measure_atc_height [measure_function] : "is_measure atc_height"
  by (simp add: is_measure_trivial)

lemma is_measure_atc_height_snd_snd [measure_function] : "is_measure (\<lambda> (M,q,t) . atc_height t)"
  by (simp add: is_measure_trivial)


inductive sub_input :: "('x \<times> 'y \<times> ('a, 'b) ATC) \<Rightarrow> ('x \<times> 'y \<times> ('a, 'b) ATC) \<Rightarrow> bool" where
  "atc_height t2 < atc_height t1 \<Longrightarrow> sub_input (_,_,t2) (_,_,t1)"

lemma accp_sub_input : 
  fixes t :: "('a, 'b) ATC"
  shows "Wellfounded.accp sub_input (M,q,t)"
proof (induct "atc_height t" arbitrary: t rule: less_induct)
  case (less k)
  then show ?case  
    by (smt accp.simps prod.sel(2) sub_input.cases sub_input.intros)
qed

definition sub_input_rel where "sub_input_rel = {((M2,q2,t2), (M1,q1,t1)) |M1 M2 q1 q2 t1 t2 . atc_height t2 < atc_height t1}"

lemma sub_input_rel_altdef: "sub_input_rel = {(s, t) |s t. sub_input s t}"
  using sub_input_rel_def sub_input.simps sub_input.cases 
  by (auto simp: sub_input_rel_def sub_input.simps)

lemma sub_input_relI [intro]: "atc_height t2 < atc_height t1 \<Longrightarrow> ((M2,q2,t2), (M1,q1,t1)) \<in> sub_input_rel"
  by (simp add: sub_input_rel_def)

lemma sub_input_relI_ran [intro]: "t \<in> ran f \<Longrightarrow> ((M2,q2,t), (M1,q1,(Node x f))) \<in> sub_input_rel"
  by (simp add: sub_input_rel_def)


lemma wf_sub_input_rel [simp, intro]: "wf sub_input_rel" 
  using accp_sub_input unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  










inductive sub_input :: "(('a, 'b) ATC \<times> 'x \<times> 'y) \<Rightarrow> (('a, 'b) ATC \<times>'x \<times> 'y) \<Rightarrow> bool" where
  "subtest t2 t1 \<Longrightarrow> sub_input (t2,_,_) (t1,_,_)"

(*
inductive sub_input :: "('x \<times> 'y \<times> ('a, 'b) ATC) \<Rightarrow> ('x \<times> 'y \<times> ('a, 'b) ATC) \<Rightarrow> bool" where
  "subtest t2 t1 \<Longrightarrow> sub_input (_,_,t2) (_,_,t1)"
*)

lemma accp_sub_input : "Wellfounded.accp sub_input (t,M,q)"
proof (induction t)
  case Leaf
  then show ?case by (metis (no_types) ATC.distinct(1) Pair_inject not_accp_down sub_input.cases subtest.cases)
next
  case (Node x f) 
  have IH: "Wellfounded.accp sub_input (t2,M,q)" if "subtest t2 (Node x f)" for "t2"
    using Node[of "Some t2" t2] and that
    by (smt ATC.inject mem_Collect_eq option.set_intros ran_def rangeI subtest.cases) 
  show ?case 
    by (smt ATC.inject IH Pair_inject accp.simps sub_input.simps)
qed

definition sub_input_rel where "sub_input_rel = {((t2,M2,q2), (t1,M1,q1)) |M1 M2 q1 q2 t1 t2 . subtest t2 t1}"

(*
lemma sub_input_rel_altdef: "sub_input_rel = {((t2,M,q2), (t1,M,q1)) |M q1 q2 t1 t2 . sub_input (t2,M,q2) (t1,M,q1)}"
  using sub_input_rel_def sub_input.simps sub_input.cases 
  by (auto simp: sub_input_rel_def sub_input.simps)
*)

lemma sub_input_rel_altdef: "sub_input_rel = {(s, t) |s t. sub_input s t}"
  using sub_input_rel_def sub_input.simps sub_input.cases 
  by (auto simp: sub_input_rel_def sub_input.simps)

lemma sub_input_relI [intro]: "subtest t2 t1 \<Longrightarrow> ((t2,M2,q2), (t1,M1,q1)) \<in> sub_input_rel"
  by (simp add: sub_input_rel_def)

(*
lemma sub_input_relI' [intro]: "Some t = f  \<Longrightarrow> ((M,q2,t), (M,q1,Node x f)) \<in> sub_input_rel"
  by (auto simp: sub_input_rel_def ran_def)
*)
lemma wf_sub_input_rel [simp, intro]: "wf sub_input_rel" 
  using accp_sub_input unfolding sub_input_rel_altdef 

  using accp_sub_input unfolding sub_input_rel_altdef accp_eq_acc wf_acc_iff 
  using Collect_cong Pair_inject accp_eq_acc accp_sub_input case_prodE case_prodI mem_Collect_eq not_acc_down sub_input_rel_altdef sub_input_rel_def
  
  

  using accp_sub_input unfolding sub_input_rel_altdef accp_eq_acc wf_acc_iff
  by auto

function IO :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in \<times> 'out) list set" where
  "IO M q Leaf = {[]}" |
  "IO M q (Node x f) = {[(x,y)] | y q2 . path M [((x,y),q2)] q \<and> f y = None }
                       \<union> {(x,y) # io2 | y q2 t2 io2 . path M [((x,y),q2)] q \<and> f y = Some t2 \<and> io2 \<in> (IO M q2 t2)}"
  by pat_completeness auto
termination 
  
  apply (relation "measure (\<lambda>(a,b,c). atc_height c)")
  apply blast
  apply (relation subtest_rel) 
termination sorry


fun IO_set :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set" where
  "IO_set M q \<Omega> = \<Union> { IO M q t | t . t \<in> \<Omega> }"

lemma IO_input : 
  assumes "(x,y) # io \<in> IO M q (Node xt f)"
  shows "x = xt"
proof (cases "f y")
  case None
  then show ?thesis using assms IO.simps(2) by simp 
next
  case (Some a)
  then show ?thesis using assms IO.simps(2) by simp
qed

lemma IO_path :
  assumes "io \<in> IO M q t"
obtains tr
where "path M (io || tr) q" "length io = length tr" 
using assms proof (induction io arbitrary: q t)
  case Nil
  then show ?case by (simp add: FSM.nil) 
next
  case (Cons a io_tl)
  then obtain x y where a_split : "a = (x,y)" by (meson surj_pair)
  have "t \<noteq> Leaf" 
  proof (rule ccontr)
    assume leaf_assm : "\<not> t \<noteq> Leaf"
    moreover have "t = Leaf \<longrightarrow> IO M q t = {[]}" using Cons by simp
    ultimately show "False" using Cons by simp
  qed
  then obtain xt f where t_split : "t = Node xt f" using ATC.exhaust by blast
  then have "xt = x" using IO_input Cons a_split by auto
  then obtain q2 where q2_def : "path M [((x,y),q2)] q" using Cons a_split t_split IO.simps(2) by auto

  then show ?thesis 
  proof (cases "f y")
    case None
    then have "io_tl = []" using Cons a_split t_split IO.simps
    then show ?thesis sorry
  next
    case (Some ty)
    then show ?thesis sorry
  qed


  moreover obtain tr_tl where tr_tl_def : "path M (io_tl || tr_tl) q2" "length io_tl = length tr_tl"
    using Cons 

  then show ?case using Cons 


 
qed
  using language_state_elim 




end 