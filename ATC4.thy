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

lemma IO_leaf[simp] : "IO M q Leaf = {[]}"
proof   
  show "IO M q Leaf \<subseteq> {[]}" 
  proof (rule ccontr)
    assume assm : "\<not> IO M q Leaf \<subseteq> {[]}"
    then obtain io_hd io_tl where elem_ex : "Cons io_hd io_tl \<in> IO M q Leaf" by (metis (no_types, hide_lams) insertI1 neq_Nil_conv subset_eq) 
    then show "False" using atc_reaction_nonempty_no_leaf assm by (metis IO.simps mem_Collect_eq)
  qed  
next
  show "{[]} \<subseteq> IO M q Leaf" by auto 
qed


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
lemma B_dist' :
  assumes df: "B M io1 \<Omega> \<noteq> B M io2 \<Omega>"
  shows   "(io_targets M (initial M) io1) \<noteq> (io_targets M (initial M) io2)"
  using assms by force 

lemma B_dist :
  assumes "io_targets M (initial M) io1 = {q1}"
  and     "io_targets M (initial M) io2 = {q2}"
  and     "B M io1 \<Omega> \<noteq> B M io2 \<Omega>"
shows   "q1 \<noteq> q2"
  using assms by force





fun D :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in * 'out) list set set" where
  "D M \<Omega> ISeqs = image (\<lambda> io . B M io \<Omega>) (language_state_in M (initial M) ISeqs)"



lemma D_bound :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     fi: "finite ISeqs"
  shows "card (D M \<Omega> ISeqs) \<le> card (nodes M)" 
proof -
  have "D M \<Omega> ISeqs \<subseteq> image (\<lambda> s . IO_set M s \<Omega>) (nodes M)"
  proof 
    fix RS assume RS_def : "RS \<in> D M \<Omega> ISeqs"
    then obtain xs ys where RS_tr : "RS = B M (xs || ys) \<Omega>" "(xs \<in> ISeqs \<and> length xs = length ys \<and> (xs || ys) \<in> language_state M (initial M))"by auto
    then obtain qx where qx_def : "io_targets M (initial M) (xs || ys) = { qx }" by (meson io_targets_observable_singleton_ex ob)  
    then have "RS = IO_set M qx \<Omega>" using RS_tr by auto
    moreover have "qx \<in> nodes M" by (metis FSM.nodes.initial io_targets_nodes qx_def singletonI) 
    ultimately show "RS \<in> image (\<lambda> s . IO_set M s \<Omega>) (nodes M)" by auto
  qed
  moreover have "finite (nodes M)" using assms by auto
  ultimately show ?thesis by (meson Finite_Set.card_image_le surj_card_le)
qed





fun append_io_B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in * 'out) list set" where
"append_io_B M io \<Omega> = { io@res | res . res \<in> B M io \<Omega> }"

fun is_reduction_on :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"is_reduction_on M1 M2 iseq \<Omega> = (language_state_in M1 (initial M1) {iseq} \<subseteq> language_state_in M2 (initial M2) {iseq} 
  \<and> (\<forall> io \<in> language_state_in M1 (initial M1) {iseq} . append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>))"

fun is_reduction_on_sets :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"is_reduction_on_sets M1 M2 TS \<Omega> = (\<forall> iseq \<in> TS . is_reduction_on M1 M2 iseq \<Omega>)"



lemma atc_reaction_reduction :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     rct : "atc_reaction M1 q1 t io"
  and     ob2 : "observable M2"
  and     ob1 : "observable M1"
shows "atc_reaction M2 q2 t io"
using assms proof (induction t arbitrary: io q1 q2)
  case Leaf
  then have "io = []" by (metis atc_reaction_nonempty_no_leaf list.exhaust) 
  then show ?case by (simp add: leaf)  
next
  case (Node x f)
  then obtain io_hd io_tl where io_split : "io = io_hd # io_tl" by (metis ATC.distinct(1) atc_reaction_empty list.exhaust) 
  moreover obtain y where y_def : "io_hd = (x,y)" using Node calculation by (metis ATC.inject atc_reaction_nonempty surj_pair) 
  ultimately  obtain q1x where q1x_def : "q1x \<in> succ M1 (x,y) q1" "atc_reaction M1 q1x (f y) io_tl" using Node.prems(4) by blast 

  then have pt1 : "path M1 ([(x,y)] || [q1x]) q1" by auto
  then have ls1 : "[(x,y)] \<in> language_state M1 q1" unfolding language_state_def path_def using list.simps(9) by force
  moreover have "q1x \<in> io_targets M1 q1 [(x,y)]" unfolding io_targets.simps
  proof -
    have f1: "length [(x, y)] = length [q1x]"
      by simp
    have "q1x = target ([(x, y)] || [q1x]) q1"
      by simp
    then show "q1x \<in> {target ([(x, y)] || cs) q1 |cs. path M1 ([(x, y)] || cs) q1 \<and> length [(x, y)] = length cs}"
      using f1 pt1 by blast
  qed 
  ultimately have tgt1 : "io_targets M1 q1 [(x,y)] = {q1x}" using Node.prems io_targets_observable_singleton_ex q1x_def 
    by (metis (no_types, lifting) singletonD) 

  
  then have ls2 : "[(x,y)] \<in> language_state M2 q2" using Node.prems(1) ls1 by auto
  then obtain q2x where q2x_def : "q2x \<in> succ M2 (x,y) q2" unfolding language_state_def path_def using transition_system.path.cases by fastforce 
  then have pt2 : "path M2 ([(x,y)] || [q2x]) q2" by auto
  then have "q2x \<in> io_targets M2 q2 [(x,y)]" using ls2 unfolding io_targets.simps 
  proof -
    have f1: "length [(x, y)] = length [q2x]"
      by simp
    have "q2x = target ([(x, y)] || [q2x]) q2"
      by simp
    then show "q2x \<in> {target ([(x, y)] || cs) q2 |cs. path M2 ([(x, y)] || cs) q2 \<and> length [(x, y)] = length cs}"
      using f1 pt2 by blast
  qed

  then have tgt2 : "io_targets M2 q2 [(x,y)] = {q2x}" using Node.prems io_targets_observable_singleton_ex ls2 q2x_def 
    by (metis (no_types, lifting) singletonD) 


  then have "language_state M1 q1x \<subseteq> language_state M2 q2x" using language_state_inclusion_next[of M1 q1 M2 q2 "[(x,y)]" q1x q2x] tgt1 tgt2 Node.prems fault_model_m.simps  by auto
  moreover have "q1x \<in> nodes M1" using q1x_def(1) Node.prems(2) by (metis insertI1 io_targets_nodes tgt1)
  moreover have "q2x \<in> nodes M2" using q2x_def(1) Node.prems(3) by (metis insertI1 io_targets_nodes tgt2)
  ultimately have "q2x \<in> succ M2 (x,y) q2 \<and> atc_reaction M2 q2x (f y) io_tl" using Node.IH[of "f y" q1x q2x io_tl] Node.prems fault_model_m.simps q2x_def q1x_def(2) by blast 

  then show "atc_reaction M2 q2 (Node x f) io" using io_split y_def by blast 
qed


lemma IO_reduction :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "IO M1 q1 t \<subseteq> IO M2 q2 t"
  using assms atc_reaction_reduction unfolding IO.simps by auto

lemma IO_set_reduction :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "IO_set M1 q1 \<Omega> \<subseteq> IO_set M2 q2 \<Omega>"
proof -
  have "\<forall> t \<in> \<Omega> . IO M1 q1 t \<subseteq> IO M2 q2 t" using assms IO_reduction by metis 
  then show ?thesis unfolding IO_set.simps by blast
qed

lemma B_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "B M1 io \<Omega> \<subseteq> B M2 io \<Omega>"
proof 
  fix xy assume xy_assm : "xy \<in> B M1 io \<Omega>"
  then obtain q1x where q1x_def : "q1x \<in> (io_targets M1 (initial M1) io) \<and> xy \<in> IO_set M1 q1x \<Omega>" unfolding B.simps by auto
  then obtain tr1 where tr1_def : "path M1 (io || tr1) (initial M1) \<and> length io = length tr1" by auto

  then have q1x_ob : "io_targets M1 (initial M1) io = {q1x}" using assms
    by (metis io_targets_observable_singleton_ex language_state q1x_def singleton_iff) 
  
  then have ls1 : "io \<in> language_state M1 (initial M1)" by auto 
  then have ls2 : "io \<in> language_state M2 (initial M2)" using red by auto

  then obtain tr2 where tr2_def : "path M2 (io || tr2) (initial M2) \<and> length io = length tr2" by auto
  then obtain q2x where q2x_def : "q2x \<in> (io_targets M2 (initial M2) io)" by auto

  then have q2x_ob : "io_targets M2 (initial M2) io = {q2x}" using tr2_def assms
    by (metis io_targets_observable_singleton_ex language_state singleton_iff) 

  then have "language_state M1 q1x \<subseteq> language_state M2 q2x" using q1x_ob assms unfolding io_reduction.simps by (simp add: language_state_inclusion_next) 
  then have "IO_set M1 q1x \<Omega> \<subseteq> IO_set M2 q2x \<Omega>" using assms IO_set_reduction by (metis FSM.nodes.initial io_targets_nodes q1x_def q2x_def) 
  moreover have "B M1 io \<Omega> = IO_set M1 q1x \<Omega>" using q1x_ob by auto
  moreover have "B M2 io \<Omega> = IO_set M2 q2x \<Omega>" using q2x_ob by auto
  ultimately have "B M1 io \<Omega> \<subseteq> B M2 io \<Omega>" by simp
  then show "xy \<in> B M2 io \<Omega>" using xy_assm by blast
qed


lemma append_io_B_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>"
proof 
  fix ioR assume ioR_assm : "ioR \<in> append_io_B M1 io \<Omega>" 
  then obtain res where res_def : "ioR = io @ res" "res \<in> B M1 io \<Omega>" by auto
  then have "res \<in> B M2 io \<Omega>" using assms B_reduction by blast
  then show "ioR \<in> append_io_B M2 io \<Omega>" using ioR_assm res_def by auto
qed 



lemma is_reduction_on_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "is_reduction_on M1 M2 iseq \<Omega>"
unfolding is_reduction_on.simps proof 
  show "language_state_in M1 (initial M1) {iseq} \<subseteq> language_state_in M2 (initial M2) {iseq}" using red by auto 
next
  show "\<forall>io\<in>language_state_in M1 (initial M1) {iseq}. append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>" using  append_io_B_reduction assms by blast
qed
    

lemma is_reduction_on_sets_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "is_reduction_on_sets M1 M2 TS \<Omega>"
  using assms is_reduction_on_reduction by (metis is_reduction_on_sets.elims(3)) 



end