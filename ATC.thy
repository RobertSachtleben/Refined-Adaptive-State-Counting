theory ATC
  imports Main FSM "~~/src/HOL/Library/Finite_Set" "~~/src/HOL/Library/Finite_Map"
begin

(*
datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> (('in, 'out) ATC) option"



inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
(*subtest_self : "subtest a a" |*)
subtest_direct : "t \<in> ran f \<Longrightarrow> subtest (Node x f) t" 
(*subtest_trans : "t1 \<in> ran f \<Longrightarrow> subtest t1 t2 \<Longrightarrow> subtest (Node x f) t2"*)



function atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x f) = Suc (Max { atc_height t | t . t \<in> ran f})"
  sorry

print_theorems


fun atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set"
where
"atc_io M s1 Leaf = {}"  |
"atc_io M s1 (Node x f) = 
    {[(x,y)] | x y . \<exists> s2 . (s1,x,y,s2) \<in> transitions M \<and> f y = None }
 \<union> { (x,y)#res | x y res . \<exists> s2 t . (s1,x,y,s2) \<in> transitions M \<and> f y = Some t \<and> res \<in> atc_io M s2 t } 
"
*)

(*
datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> (('in, 'out) ATC)"

function atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x f) = Suc (Max { atc_height (f y) | y . True})"
  by pat_completeness auto
termination atc_height 

fun atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set"
where
"atc_io M s1 Leaf = {}"  |
"atc_io M s1 (Node x f) = 
   { (x,y)#res | x y res . \<exists> s2 . (s1,x,y,s2) \<in> transitions M \<and> res \<in> atc_io M s2 (f y)} 
"
*)

datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> (('in, 'out) ATC)"

inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
subtest_direct : "\<exists> y . t = f y \<Longrightarrow> subtest t (Node x f)" 

lemma accp_subtest: "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (meson ATC.distinct(1) accp.intros subtest.cases)
next
  case (Node x1 x2)
  then show ?case by (metis ATC.inject not_accp_down rangeI subtest.cases)
qed

definition subtest_rel where "subtest_rel = {(t, (Node x f)) | x f t . \<exists> y . t = f y}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "\<exists> y . t = f y \<Longrightarrow> (t, (Node x f)) \<in> subtest_rel"
  by (simp add: subtest_rel_def)

lemma subtest_relI' [intro]: "t = f y \<Longrightarrow> (t, (Node x f)) \<in> subtest_rel"
  by (auto simp: subtest_rel_def)

lemma wf_subtest_rel [simp, intro]: "wf subtest_rel"
using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff by sledgehamme


function atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x f) = Suc (Max { atc_height (f y) | y . True})"
  by pat_completeness auto
termination by (relation subtest_rel) auto

(*
datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) fmap"

function atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x f) = Suc (Max { atc_height t | t . t \<in> fmran' f})"
  by pat_completeness auto

lemma test : 
  assumes sub: "t2 \<in> fmran' f1"
  shows "atc_height t2 < atc_height (Node x f1)"
  oops

fun is_subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
"is_subtest Leaf t = False" |
"is_subtest (Node x f) t = ((t \<in> fmran' f) \<or> (\<exists> t2 . fmember t2 (fmran f) \<and> is_subtest t t2))"

fun atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set"
where
"atc_io M s1 Leaf = {}"  |
"atc_io M s1 (Node x f) = 
    {[(x,y)] | x y . \<exists> s2 . (s1,x,y,s2) \<in> transitions M \<and> y \<notin> fmdom' f }
 \<union> { (x,y)#res | x y res . \<exists> s2 t . (s1,x,y,s2) \<in> transitions M \<and> fmlookup f y = Some t \<and> res \<in> atc_io M s2 t } 
"
*)
(*
datatype ('in, 'out) ATC = Leaf | Node 'in "('out * (('in, 'out) ATC)) list"
*)










(*
TODO:
- concat ATCs (for alphabet Y)
- input list \<rightarrow> ATC (for alphabet Y)
*)

end