theory ATC4
imports FSM2
begin

datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> ('in, 'out) ATC"

inductive atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  leaf[intro!]: "atc_reaction M q1 Leaf []" |
  node[intro!]: "q2 \<in> succ M (x,y) q1 \<Longrightarrow> atc_reaction M q2 (f y) io \<Longrightarrow> atc_reaction M q1 (Node x f) ((x,y)#io)"

inductive_cases leaf_elim[elim!] : "atc_reaction M q1 Leaf []"
inductive_cases node_elim[elim!] : "atc_reaction M q1 (Node x f) ((x,y)#io)"

lemma atc_reaction_empty[simp] :
  assumes "atc_reaction M q t []"
  shows "t = Leaf"
using assms atc_reaction.simps by force 

lemma atc_reaction_nonempty_no_leaf :
  assumes "atc_reaction M q t (Cons a io)"
  shows "t \<noteq> Leaf"
using assms
proof -
  have "\<And>f c a ps. \<not> atc_reaction f (c::'c) (a::('a, 'b) ATC) ps \<or> a \<noteq> Leaf \<or> a \<noteq> Leaf \<or> ps = []"
    using atc_reaction.simps by fastforce
  then show ?thesis
    using assms by blast
qed  

lemma atc_reaction_nonempty :
  assumes "atc_reaction M q1 t (Cons (x,y) io)"
  obtains q2 f 
  where "t = Node x f" "q2 \<in> succ M (x,y) q1"  "atc_reaction M q2 (f y) io"
proof -
  obtain x2 f where "t = Node x2 f"  using assms by (metis ATC.exhaust atc_reaction_nonempty_no_leaf) 
  moreover have "x = x2" using assms calculation atc_reaction.cases by fastforce 
  ultimately show ?thesis using assms using that by blast 
qed

lemma atc_reaction_path_ex : 
  assumes "atc_reaction M q1 t io"
  shows "\<exists> tr . path M (io || tr) q1 \<and> length io = length tr"
using assms proof (induction io arbitrary: q1 t rule: list.induct)
  case Nil
  then show ?case by (simp add: FSM.nil) 
next
  case (Cons io_hd io_tl)
  then obtain x y where io_hd_def : "io_hd = (x,y)" by (meson surj_pair)
  then obtain f where f_def : "t = (Node x f)" using Cons atc_reaction_nonempty by metis
  then obtain q2 where q2_def : "q2 \<in> succ M (x,y) q1" "atc_reaction M q2 (f y) io_tl" using Cons io_hd_def atc_reaction_nonempty by auto
  then obtain tr_tl where tr_tl_def :  "path M (io_tl || tr_tl) q2" "length io_tl = length tr_tl" using Cons.IH[of q2 "f y"] by blast
  then have "path M (io_hd # io_tl || q2 # tr_tl) q1" using Cons q2_def by (simp add: FSM.path.intros(2) io_hd_def)
  then show ?case using tr_tl_def by fastforce   
qed

lemma atc_reaction_path : 
  assumes "atc_reaction M q1 t io"
obtains tr
  where "path M (io || tr) q1" "length io = length tr"
by (meson assms atc_reaction_path_ex) 





inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
  "t \<in> range f \<Longrightarrow> subtest t (Node x f)"

lemma accp_subtest : "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (meson ATC.distinct(1) accp.simps subtest.cases)
next
  case (Node x f)
  have IH: "Wellfounded.accp subtest t" if "t \<in> range f" for "t"
    using Node[of t] and that by (auto simp: eq_commute)
  show ?case by (rule accpI) (auto intro: IH elim!: subtest.cases)
qed

definition subtest_rel where "subtest_rel = {(t, Node x f) |f x t. t \<in> range f}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "t \<in> range f \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (simp add: subtest_rel_def)

lemma subtest_relI' [intro]: "t = f y \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (auto simp: subtest_rel_def ran_def)

lemma wf_subtest_rel [simp, intro]: "wf subtest_rel" 
  using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  by auto



function inputs_atc :: "('a,'b) ATC \<Rightarrow> 'a set" where
  "inputs_atc Leaf = {}" |
  "inputs_atc (Node x f) = insert x (\<Union> (image inputs_atc (range f)))"
by pat_completeness auto
termination by (relation subtest_rel) auto

fun applicable :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
  "applicable M t = (inputs_atc t \<subseteq> inputs M)"

fun applicable_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
  "applicable_set M \<Omega> = (\<forall> t \<in> \<Omega> . applicable M t)"

lemma applicable_subtest :
  assumes "applicable M (Node x f)"
shows "applicable M (f y)"
using assms inputs_atc.simps
by (simp add: Sup_le_iff)


fun IO :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in \<times> 'out) list set" where
  "IO M q t = { tr . atc_reaction M q t tr }"

fun IO_set :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set" where
  "IO_set M q \<Omega> = \<Union> {IO M q t | t . t \<in> \<Omega>}"

lemma IO_language : "IO M q t \<subseteq> language_state M q"
  by (metis atc_reaction_path IO.elims language_state mem_Collect_eq subsetI) 


fun r_dist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"r_dist M t s1 s2 = (IO M s1 t \<inter> IO M s2 t = {})"

fun r_dist_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"r_dist_set M T s1 s2 = (\<exists> t \<in> T . r_dist M t s1 s2)"


lemma applicable_nonempty :
  assumes "applicable M t"
  and     "completely_specified M"
  shows "IO M q1 t \<noteq> {}"
using assms proof (induction t arbitrary: q1)
  case Leaf
  then show ?case by auto
next
  case (Node x f)
  then have "x \<in> inputs M" by auto
  then obtain y q2  where x_appl : "q2 \<in> succ M (x, y) q1" using Node unfolding completely_specified.simps by blast
  then have "applicable M (f y)" using applicable_subtest Node by metis
  then have "IO M q2 (f y) \<noteq> {}" using Node by auto
  then show ?case unfolding IO.simps using x_appl by blast  
qed

lemma r_dist_dist :
  assumes "applicable M t"
  and     "completely_specified M"
  and     "r_dist M t q1 q2"
shows   "q1 \<noteq> q2"
proof (rule ccontr)
  assume "\<not>(q1 \<noteq> q2)" 
  then have "q1 = q2" by simp
  then have "IO M q1 t = {}" using assms by simp
  moreover have "IO M q1 t \<noteq> {}" using assms applicable_nonempty by auto
  ultimately show "False" by simp
qed

lemma r_dist_set_dist :
  assumes "applicable_set M \<Omega>"
  and     "completely_specified M"
  and     "r_dist_set M \<Omega> q1 q2"
shows   "q1 \<noteq> q2"
using assms r_dist_dist by (metis applicable_set.elims(2) r_dist_set.elims(2))  





fun atc_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"atc_reduction M2 s2 M1 s1 \<Omega> = (\<forall> t \<in> \<Omega> . IO M2 s2 t \<subseteq> IO M1 s1 t)"






(* Lemma 5.3.7 *)  
lemma atc_rdist_dist :
  assumes wf2   : "well_formed M2"
  and     cs2   : "completely_specified M2"
  and     ap2   : "applicable_set M2 \<Omega>"
  and     el_t1 : "t1 \<in> nodes M2"
  and     red1  : "atc_reduction M2 t1 M1 s1 \<Omega>"
  and     red2  : "atc_reduction M2 t2 M1 s2 \<Omega>"
  and     rdist : "r_dist_set M1 \<Omega> s1 s2"
  shows "r_dist_set M2 \<Omega> t1 t2"
proof -
  obtain td where td_def : "td \<in> \<Omega> \<and> r_dist M1 td s1 s2" using rdist by auto
  then have "IO M1 s1 td \<inter> IO M1 s2 td = {}" using td_def by simp
  moreover have "IO M2 t1 td \<subseteq> IO M1 s1 td" using red1 td_def by auto
  moreover have "IO M2 t2 td \<subseteq> IO M1 s2 td" using red2 td_def by auto
  ultimately have no_inter : "IO M2 t1 td \<inter> IO M2 t2 td = {}" by blast
  
  then have "td \<noteq> Leaf" by auto
  then have "IO M2 t1 td \<noteq> {}" by (meson ap2 applicable_nonempty applicable_set.elims(2) cs2 td_def) 
  then have "IO M2 t1 td \<noteq> IO M2 t2 td" using no_inter by auto 
  then show ?thesis using no_inter td_def by auto 
qed


(* explicitly requires the ATC set to be applicable to the FSM *)
fun characterizing_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"characterizing_set M \<Omega> = (applicable_set M \<Omega> \<and> (\<forall> s1 \<in> (nodes M) . \<forall> s2 \<in> (nodes M) . 
    (\<exists> td . r_dist M td s1 s2) \<longrightarrow> (\<exists> tt \<in> \<Omega> . r_dist M tt s1 s2)))"


fun B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in * 'out) list set" where
"B M io \<Omega> = \<Union> (image (\<lambda> s . IO_set M s \<Omega>) (io_targets M (initial M) io))"

(* Proposition 5.4.2 *)
lemma B_dist :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     ln1: "io1 \<in> language_state M (initial M)"
  and     ln2: "io2 \<in> language_state M (initial M)"
  and     df: "B M io1 \<Omega> \<noteq> B M io2 \<Omega>"
  shows   "(io_targets M (initial M) io1) \<noteq> (io_targets M (initial M) io2)"
proof -
  obtain q1 where q1_def : "io_targets M (initial M) io1 = {q1}" by (meson assms io_targets_observable_singleton)
  then have B1 : "B M io1 \<Omega> = IO_set M q1 \<Omega>" by auto
  obtain q2 where q2_def : "io_targets M (initial M) io2 = {q2}" by (meson assms io_targets_observable_singleton)
  then have B2 : "B M io2 \<Omega> = IO_set M q2 \<Omega>" by auto
  have "q1 \<noteq> q2" using B1 B2 df by blast
  then show ?thesis using q1_def q2_def by blast
qed

fun D :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in * 'out) list set set" where
"D M T ISeqs = { B M io T | io . \<exists> iseq \<in> ISeqs . (map fst io = iseq \<and> io \<in> language_state M (initial M)) }"



end