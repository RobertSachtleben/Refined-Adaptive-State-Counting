theory ATC
  imports Main FSM "~~/src/HOL/Library/Finite_Set" "~~/src/HOL/Library/Finite_Map"
begin


datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) map"

fun is_atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list \<Rightarrow> bool" where
"is_atc_reaction M s1 Leaf [] = True" |
"is_atc_reaction M s1 Leaf io = False" |
"is_atc_reaction M s1 (Node x f) [] = (\<not>(\<exists> y s2 . (s1,x,y,s2) \<in> transitions M))" | (*only relevant if M not completely specified *)
"is_atc_reaction M s1 (Node x f) ((xi,yi)#io) = (case (f yi) of
  Some t \<Rightarrow> (x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 t io)) |
  None \<Rightarrow> (io = [] \<and> x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M)))"

fun has_height_gte :: "('in, 'out) ATC \<Rightarrow> nat \<Rightarrow> bool" where
"has_height_gte Leaf n = True" |
"has_height_gte (Node x f) 0 = False" |
"has_height_gte (Node x f) (Suc n) = (\<forall> t \<in> ran f .  has_height_gte t n)"
(*"has_height_gte (Node x f) (Suc n) = Ball (ran f) (\<lambda> t . has_height_gte t n)"*)




definition has_height :: "('in, 'out) ATC \<Rightarrow> nat \<Rightarrow> bool" where
"has_height T n \<equiv> has_height_gte T n \<and> (\<forall> i < n . \<not> has_height_gte T i)"

definition height :: "('in, 'out) ATC \<Rightarrow> nat" where
"height T = (THE n . has_height T n)"

fun atc_height :: "('in, 'out) ATC \<Rightarrow> nat" where
"atc_height T = (LEAST n . has_height_gte T n)"

lemma height_inc : "has_height_gte t n1 \<Longrightarrow> n2 > n1 \<Longrightarrow> has_height_gte t n2"
proof (induction t  arbitrary: n1 n2)
  case Leaf
  then show ?case by simp
next
  case (Node x f)
  have gtz : "n1 > 0"
  proof (rule ccontr)
    assume "\<not> (n1 > 0)"
    then have "t = Leaf" using has_height_gte.elims(2) using Node.prems by blast
    then show "False" using Node \<open>\<not> 0 < n1\<close> by auto
  qed
  have "\<forall> t1 \<in> ran f . has_height_gte t1 (n2-1)"
  proof 
    fix t1 
    show "t1 \<in> ran f \<Longrightarrow> has_height_gte t1 (n2-1)"
    proof (rule Node.IH [of "Some t1" "t1" "n1-1" "n2-1"])
      assume el: "t1 \<in> ran f"
      show "Some t1 \<in> range f" using el by (smt mem_Collect_eq ran_def rangeI)
      show "t1 \<in> set_option (Some t1)" by auto
      show "has_height_gte t1 (n1-1)" using Node.prems(1) gtz el gr0_conv_Suc by auto
      show "(n2-1) > (n1-1)" using Node.prems(2) gtz by linarith
    qed
  qed
  then show "has_height_gte (Node x f) n2" using Node.prems(2) diff_Suc_1 has_height_gte.elims(3) less_numeral_extra(3) by fastforce
qed




lemma height_ex : "\<exists> n . has_height_gte t n"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node x f)
  have "\<forall> t1 \<in> ran f . \<exists> n1 . has_height_gte t1 n1" 
    by (smt Node.IH UNIV_I image_eqI mem_Collect_eq option.set_intros ran_def)
  then obtain hc where hc_def : "\<forall> t1 \<in> ran f . \<exists> n1 . has_height_gte t1 n1 \<and> n1 < hc" by sledgehamme
  then obtain hs where hs_def : "\<forall> t1 \<in> ran f . has_height_gte t1 (hs t1)" by sledgehamme
  then have "\<exists> n1 . \<forall> t1 \<in> ran f . has_height_gte t1 n1" using height_inc by sledgehamm
  then show ?case by sledgehamme
qed

lemma test :
  assumes a : "h1 = atc_height T"
  shows "\<forall> i < h1 . \<not> has_height_gte T i"
  using assms by sledgehamme

lemma has_height_subtest :
  assumes st: "t \<in> ran f"
  assumes h1: "has_height t h1" 
  assumes h2: "has_height (Node x f) t2"
  shows "h2 > h1"
  using assms by sledgehamme

lemma has_height_subtest :
  assumes st: "t \<in> ran f"
  assumes h1: "h1 = atc_height t" 
  assumes h2: "h2 = atc_height (Node x f)"
  shows "h2 > h1"
proof (rule ccontr)
  assume "h2 \<le> h1"
  then have "\<forall> i < h1 . \<not>(has_height_gte t i)" using assms by sledgehamme

  then have "\<exists> t2 \<in> ran f . has_height_gte t2 n1" using assms by blast
  then have "n2 > n1" using assms by sledgehamme
  

lemma subtest_height :
  assumes st: "t \<in> ran f"
  shows "atc_height t < atc_height (Node x f)"
proof (rule ccontr)
  assume "atc_height t \<ge> atc_height (Node x f)"
  then obtain n where n_def : "n = atc_height (Node x f)" by auto
  

inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
"t \<in> ran f \<Longrightarrow> subtest t (Node x f)"

lemma accp_subtest : "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (metis ATC.distinct(2) not_accp_down subtest.cases)
next
  case (Node x1 x2)
  then show ?case by sledgehamme
qed

function size :: "('in, 'out) ATC \<Rightarrow> nat" where
"size Leaf = 0" |
"size (Node x f) = Max ( image size (ran f) )"
  by pat_completeness auto
termination 
  apply (relation "measure atc_height")
   apply auto[]
  apply sledgehamme
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
  assumes wf1 : "well_formed M1"
  assumes wf2 : "well_formed M2"
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