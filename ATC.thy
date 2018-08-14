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

(*
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
*)


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
datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) fmap"

inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
subtest_direct : "t \<in> fmran' f \<Longrightarrow> subtest t (Node x f)" 

lemma accp_subtest: "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (meson ATC.distinct(1) not_accp_down subtest.simps)
next
  case (Node x1 x2)
  then show ?case by (metis ATC.inject not_accp_down subtest.cases)
qed

definition subtest_rel where "subtest_rel = {(t, (Node x f)) | x f t . t \<in> fmran' f}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "t \<in> fmran' f \<Longrightarrow> (t, (Node x f)) \<in> subtest_rel"
  by (simp add: subtest_rel_def)


lemma wf_subtest_rel [simp, intro]: "wf subtest_rel"
using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  
  using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff by sledgehamme
*)
(*
datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) fmap"
fun atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x f) = 1 + Max ( image atc_height (fmran' f))" 
*)

datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) map"

fun is_atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list \<Rightarrow> bool" where
"is_atc_reaction M s1 Leaf [] = True" |
"is_atc_reaction M s1 Leaf io = False" |
"is_atc_reaction M s1 (Node x f) [] = (\<not>(\<exists> y s2 . (s1,x,y,s2) \<in> transitions M))" | (*only relevant if M not completely specified *)
"is_atc_reaction M s1 (Node x f) ((xi,yi)#io) = (case (f yi) of
  Some t \<Rightarrow> (x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 t io)) |
  None \<Rightarrow> (io = [] \<and> x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M)))"

(*
datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> nat" "('in, 'out) ATC list"

fun atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height Leaf = 0" |
"atc_height (Node x idx []) = 1" |
"atc_height (Node x idx ts) = 1 + Max ( set (map atc_height ts)) "

fun is_atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list \<Rightarrow> bool" where
"is_atc_reaction M s1 Leaf [] = True" |
"is_atc_reaction M s1 Leaf io = False" |
"is_atc_reaction M s1 (Node x idx ts) [] = False" |
"is_atc_reaction M s1 (Node x idx ts) ((xi,yi)#io) = (if (idx yi < length ts)
  then (x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 (ts ! (idx yi)) io))
  else (io = [] \<and> x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M)))" 
*)

(*
fun atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set" where
"atc_io M s1 Leaf = {[]}" |
"atc_io M s1 (Node x idx ts) = 
  {[(x,y)] | y . \<exists> s2 . (s1,x,y,s2) \<in> transitions M \<and> idx y \<ge> length ts }
  \<union> { (x,y)#res | y res . \<exists> s2 . (s1,x,y,s2) \<in> transitions M \<and> res \<in> atc_io M s2 (ts ! (idx y)) }"
*)

definition atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set"
where "atc_io M s T = { io . is_atc_reaction M s T io }"
  

lemma io_dist :
  assumes io_diff : "act_io M s1 \<noteq> act_io M s2"
  shows "s1 \<noteq> s2"
  using io_diff by auto

definition atc_dist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_dist M T s1 s2 \<equiv> atc_io M s1 T \<noteq> atc_io M s2 T"

definition atc_rdist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_rdist M T s1 s2 \<equiv> atc_io M s1 T \<inter> atc_io M s2 T = {}"


lemma atc_rdist_dist :
  assumes wf1 : "well_defined M1"
  assumes wf2 : "well_defined M2"
  assumes ob1 : "observable M1"
  assumes ob2 : "observable M2"
  assumes el_s1 : "s1 \<in> states M1"
  assumes el_s2 : "s2 \<in> states M1"
  assumes el_t1 : "t1 \<in> states M2"
  assumes el_t2 : "t2 \<in> states M2"
  assumes red1 : "io_reduction_state M2 t1 M1 s1"
  assumes red2 : "io_reduction_state M2 t2 M1 s2"
  assumes rdist: "atc_rdist M1 T s1 s2"
  shows "atc_dist M2 T t1 t2"
  oops






(*
TODO:
- concat ATCs (for alphabet Y)
- input list \<rightarrow> ATC (for alphabet Y)
*)

end