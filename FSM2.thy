theory FSM2
imports
  "Transition_Systems_and_Automata/Basic/Sequence_Zip"
  "Transition_Systems_and_Automata/Transition_Systems/Transition_System"
  "Transition_Systems_and_Automata/Transition_Systems/Transition_System_Extra"
  "Transition_Systems_and_Automata/Transition_Systems/Transition_System_Construction"
begin 

record ('in, 'out, 'state) FSM =
  succ :: "('in \<times> 'out) \<Rightarrow> 'state \<Rightarrow> 'state set"
  inputs :: "'in set"
  outputs :: "'out set"
  initial :: "'state"

global_interpretation FSM : transition_system_initial
"\<lambda> a p. snd a" "\<lambda> a p. snd a \<in> succ A (fst a) p" "\<lambda> p. p = initial A"
  for A
  defines path = FSM.path and run = FSM.run and reachable = FSM.reachable and nodes = FSM.nodes
  by this

abbreviation "target \<equiv> FSM.target"
abbreviation "states \<equiv> FSM.states"
abbreviation "trace \<equiv> FSM.trace"

abbreviation successors :: "('in, 'out, 'state, 'more) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> FSM.successors TYPE('in) TYPE('out) TYPE('more)"

lemma states_alt_def: "states r p = map snd r" by (induct r arbitrary: p) (auto)
lemma trace_alt_def: "trace r p = smap snd r" by (coinduction arbitrary: r p) (auto)

definition language_state :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list set" where
  "language_state M q \<equiv> {map fst r |r . path M r q}"

lemma language_state_alt_def : "language_state M q = { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
proof -
  have "language_state M q \<subseteq> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
  proof 
    fix xr assume xr_assm : "xr \<in> language_state M q"
    then obtain r where r_def : "map fst r = xr" "path M r q" unfolding language_state_def by auto
    then obtain xs ys where xr_split : "xr = xs || ys" "length xs = length ys" "length xs = length xr"
      by (metis length_map zip_map_fst_snd) 
    then have "(xs || ys) \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" using xr_assm r_def
    proof -
    have f1: "xs || ys = map fst r"
      by (simp add: r_def(1) xr_split(1))
      then have f2: "path M ((xs || ys) || take (min (length (xs || ys)) (length (map snd r))) (map snd r)) q"
        by (simp add: r_def(2))
      have "length (xs || ys) = length (take (min (length (xs || ys)) (length (map snd r))) (map snd r))"
    using f1 by force
      then show ?thesis
        using f2 by blast
    qed 
    then show "xr \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" using xr_split by metis
  qed
  moreover have "{ io | io tr . path M  (io || tr) q \<and> length io = length tr } \<subseteq> language_state M q" 
  proof 
    fix xs assume xs_assm : "xs \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
    then obtain ys where ys_def : "path M (xs || ys) q" "length xs = length ys" by auto
    then have "xs = map fst (xs || ys)" by auto
    then show "xs \<in> language_state M q" using ys_def unfolding language_state_def by blast 
  qed
  ultimately show ?thesis by auto
qed
  

lemma language_state[intro]:
  assumes "path M (w || r) q" "length w = length r"
  shows "w \<in> language_state M q"
  using assms unfolding language_state_def by force

lemma language_state_elim[elim]:
  assumes "w \<in> language_state M q"
  obtains r
  where "path M (w || r) q" "length w = length r"
  using assms unfolding language_state_def by (force iff: split_zip_ex)

lemma language_state_split:
  assumes "w1 @ w2 \<in> language_state M q"
  obtains tr1 tr2
  where "path M (w1 || tr1) q" "length w1 = length tr1"
        "path M (w2 || tr2) (target (w1 || tr1) q)" "length w2 = length tr2"
proof -
  obtain tr where tr_def : "path M ((w1 @ w2) || tr) q" "length (w1 @ w2) = length tr"
    using assms by blast 
  let ?tr1 = "take (length w1) tr"
  let ?tr2 = "drop (length w1) tr"
  have tr_split : "?tr1 @ ?tr2 = tr" by auto
  then show ?thesis
  proof -
  have f1: "length w1 + length w2 = length tr"
    using tr_def(2) by auto
    then have f2: "length w2 = length tr - length w1" 
    by presburger
    then have "length w1 = length (take (length w1) tr)"
      using f1 by (metis (no_types) tr_split diff_add_inverse2 length_append length_drop)
    then show ?thesis
      using f2 by (metis (no_types) FSM.path_append_elim length_drop that tr_def(1) zip_append1)
  qed
qed

definition product :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow>
  ('in, 'out, 'state1 \<times>'state2) FSM" where
  "product A B \<equiv>
  \<lparr>
    succ = \<lambda> a (p\<^sub>1, p\<^sub>2). succ A a p\<^sub>1 \<times> succ B a p\<^sub>2,
    inputs = inputs A \<union> inputs B,
    outputs = outputs A \<union> outputs B,
    initial = (initial A, initial B)
  \<rparr>"

lemma product_simps[simp]:
  "succ (product A B) a (p\<^sub>1, p\<^sub>2) = succ A a p\<^sub>1 \<times> succ B a p\<^sub>2"
  "inputs (product A B) = inputs A \<union> inputs B"
  "outputs (product A B) = outputs A \<union> outputs B"
  "initial (product A B) = (initial A, initial B)"
  unfolding product_def by simp+

lemma product_target[simp]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "target (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) = (target (w || r\<^sub>1) p\<^sub>1, target (w || r\<^sub>2) p\<^sub>2)"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)
lemma product_path[iff]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "path (product A B) (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) \<longleftrightarrow> path A (w || r\<^sub>1) p\<^sub>1 \<and> path B (w || r\<^sub>2) p\<^sub>2"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)

lemma product_language_state[simp]: "language_state (product A B) (q1,q2) = language_state A q1 \<inter> language_state B q2"
  by (fastforce iff: split_zip)






fun finite_FSM :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "finite_FSM M = (finite (nodes M) \<and> finite (inputs M) \<and> finite (outputs M))"

fun observable :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "observable M = (\<forall> t . \<forall> s1 . ((succ M) t s1 = {}) \<or> (\<exists> s2 . (succ M) t s1 = {s2}))"

fun completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "completely_specified M = (\<forall> s1 . \<forall> x \<in> inputs M . \<exists> y \<in> outputs M . \<exists> s2 . s2 \<in> (succ M) (x,y) s1)"

fun well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "well_formed M =
    (finite_FSM M
    \<and> (\<forall> s1 x y . (x \<notin> inputs M \<or> y \<notin> outputs M) \<longrightarrow> succ M (x,y) s1 = {}))"


lemma observable_path_unique[simp] :
  assumes "io \<in> language_state M q"
  and     "observable M"
  and     "path M (io || tr1) q" "length io = length tr1"
  and     "path M (io || tr2) q" "length io = length tr2"
shows "tr1 = tr2"
proof (rule ccontr)
  assume tr_assm : "tr1 \<noteq> tr2"
  then have state_diff : "(states (io || tr1) q ) \<noteq> (states (io || tr2) q)"
    by (metis assms(4) assms(6) map_snd_zip states_alt_def)
  show "False"
  using assms tr_assm proof (induction io arbitrary: q tr1 tr2)
    case Nil
    then show ?case using Nil by simp
  next
    case (Cons io_hd io_tl)
    then obtain tr1_hd tr1_tl tr2_hd tr2_tl where tr_split : "tr1 = tr1_hd # tr1_tl \<and> tr2 = tr2_hd # tr2_tl"
      by (metis length_0_conv neq_Nil_conv)

    have p1: "path M ([io_hd] || [tr1_hd]) q"   using Cons.prems tr_split by auto
    have p2: "path M ([io_hd] || [tr2_hd]) q"   using Cons.prems tr_split by auto
    have tr_hd_eq : "tr1_hd = tr2_hd"           using Cons.prems unfolding observable.simps
     proof -
      assume "\<forall>t s1. succ M t s1 = {} \<or> (\<exists>s2. succ M t s1 = {s2})"
      then show ?thesis
        by (metis (no_types) p1 p2 FSM.path_cons_elim empty_iff prod.sel(1) prod.sel(2) singletonD zip_Cons_Cons)
    qed

    then show ?thesis
      using Cons.IH Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) assms(2) tr_split by auto 
  qed
qed


lemma observable_path_unique_ex : 
  assumes "observable M"
  and     "io \<in> language_state M q"
obtains tr 
where "{ t . path M (io || t) q \<and> length io = length t } = { tr }" 
proof -
  obtain tr where tr_def : "path M (io || tr) q" "length io = length tr" using assms by auto
  then have "{ t . path M (io || t) q \<and> length io = length t } \<noteq> {}" by blast
  moreover have "\<forall> t \<in> { t . path M (io || t) q \<and> length io = length t } . t = tr" 
    using assms tr_def by auto  
  ultimately show ?thesis using that by moura
qed

fun io_targets :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'state set" where
  "io_targets M q io = { target (io || tr) q | tr . path M (io || tr) q \<and> length io = length tr }"

lemma io_targets_observable_singleton_ex :
  assumes "observable M"
  and     "io \<in> language_state M q1"
shows "\<exists> q2 . io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" by fastforce 
  then show ?thesis by blast 
qed

lemma io_targets_observable_singleton_ob :
  assumes "observable M"
  and     "io \<in> language_state M q1"
obtains q2 
  where "io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" by fastforce 
  then show ?thesis using that by blast 
qed


lemma io_targets_reachable :
  assumes "q2 \<in> io_targets M q1 io"
  shows "q2 \<in> reachable M q1" 
  using assms  unfolding io_targets.simps by blast

lemma io_targets_nodes :
  assumes "q2 \<in> io_targets M q1 io"
  and     "q1 \<in> nodes M"
shows "q2 \<in> nodes M"
  using assms by auto

  

fun d_reaches :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> 'state \<Rightarrow> bool" where
  "d_reaches M p xs q = ((\<exists> ys tr . length xs = length ys \<and> length xs = length tr \<and> (path M ((xs || ys) || tr) p) \<and> target ((xs || ys) || tr) p = q) 
                            \<and> (\<forall> ys2 tr2 .  (length xs = length ys2 \<and> length xs = length tr2 \<and> path M ((xs || ys2) || tr2) p) \<longrightarrow> target ((xs || ys2) || tr2) p = q))"

lemma d_reaches_unique : 
  assumes "d_reaches M p xs q1"
  and    "d_reaches M p xs q2"
shows "q1 = q2"
using assms unfolding d_reaches.simps by blast

lemma d_reaches_unique_cases : "{ q . d_reaches M (initial M) xs q } = {} \<or> (\<exists> q2 . { q . d_reaches M (initial M) xs q } = { q2 })"
  unfolding d_reaches.simps by blast

lemma d_reaches_unique_obtain[simp] :
  assumes "d_reaches M (initial M) xs q"
shows "{ p . d_reaches M (initial M) xs p } = { q }"
  using assms unfolding d_reaches.simps by blast

fun d_reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'state set" where
  "d_reachable M p = { q . (\<exists> xs . d_reaches M p xs q) }"

lemma d_reachable_reachable : "d_reachable M p \<subseteq> reachable M p" 
unfolding d_reaches.simps d_reachable.simps by blast

fun is_det_state_cover_ass :: "('in, 'out, 'state) FSM \<Rightarrow> ('state \<Rightarrow> 'in list) \<Rightarrow> bool" where
  "is_det_state_cover_ass M f = (f (initial M) = [] \<and> (\<forall> s \<in> d_reachable M (initial M) . d_reaches M (initial M) (f s) s))"

lemma det_state_cover_ass_dist : 
  assumes "is_det_state_cover_ass M f"
  shows "\<forall> s1 \<in> d_reachable M (initial M) . \<forall> s2 \<in> d_reachable M (initial M) . s1 \<noteq> s2 \<longrightarrow> \<not>(d_reaches M (initial M) (f s2) s1)"
  using assms unfolding d_reachable.simps is_det_state_cover_ass.simps 
  proof -
    assume "f (initial M) = [] \<and> (\<forall>s\<in>{q. \<exists>xs. d_reaches M (initial M) xs q}. d_reaches M (initial M) (f s) s)"
    then show "\<forall>c\<in>{c. \<exists>as. d_reaches M (initial M) as c}. \<forall>ca\<in>{c. \<exists>as. d_reaches M (initial M) as c}. c \<noteq> ca \<longrightarrow> \<not> d_reaches M (initial M) (f ca) c" 
      by (meson d_reaches_unique)
  qed

lemma det_state_cover_ass_diff :
  assumes "is_det_state_cover_ass M f"
  shows "\<forall> s1 \<in> d_reachable M (initial M) . \<forall> s2 \<in> d_reachable M (initial M) . s1 \<noteq> s2 \<longrightarrow> f s1 \<noteq> f s2"
  using assms unfolding d_reachable.simps is_det_state_cover_ass.simps
proof -
  assume "f (initial M) = [] \<and> (\<forall>s\<in>{q. \<exists>xs. d_reaches M (initial M) xs q}. d_reaches M (initial M) (f s) s)"
  then show "\<forall>c\<in>{c. \<exists>as. d_reaches M (initial M) as c}. \<forall>ca\<in>{c. \<exists>as. d_reaches M (initial M) as c}. c \<noteq> ca \<longrightarrow> f c \<noteq> f ca"
    by (metis (no_types) d_reaches_unique)
qed 

fun is_det_state_cover :: "('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> bool" where
  "is_det_state_cover M V = (\<exists> f . is_det_state_cover_ass M f \<and> V = image f (d_reachable M (initial M)))"


lemma det_state_cover_card :
  assumes "is_det_state_cover M V"
  and     "finite (nodes M)"
shows   "card V = card (d_reachable M (initial M))"
proof -
  obtain f where f_def : "is_det_state_cover_ass M f \<and> V = image f (d_reachable M (initial M))"
    using assms unfolding is_det_state_cover.simps by blast
  then have card_f : "card V = card (image f (d_reachable M (initial M)))"
    by simp

  have "d_reachable M (initial M) \<subseteq> nodes M"
    unfolding d_reachable.simps d_reaches.simps using d_reachable_reachable by blast
  then have dr_finite : "finite (d_reachable M (initial M))"
    using assms infinite_super by blast 

  then have card_le : "card (image f (d_reachable M (initial M))) \<le> card (d_reachable M (initial M))"
    using card_image_le by blast

  have "card (image f (d_reachable M (initial M))) = card (d_reachable M (initial M))"
    by (meson card_image det_state_cover_ass_diff f_def inj_onI)

  then show ?thesis using card_f by auto
qed



fun io_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> bool" (infix "\<preceq>" 200)
where "M1 \<preceq> M2 = (language_state M1 (initial M1) \<subseteq> language_state M2 (initial M2))"

fun fault_model_m :: "('in, 'out, 'state) FSM \<Rightarrow> nat \<Rightarrow> (('in, 'out, 'state) FSM) set" where
"fault_model_m M1 m = { M2 . 
  well_formed M2 
  \<and> inputs M1 = inputs M2 
  \<and> outputs M1 = outputs M2
  \<and> card (nodes M1) \<ge> m 
  \<and> card (nodes M2) \<le> m 
  \<and> observable M2 
  \<and> completely_specified M2 }"



lemma language_state_inclusion_next : 
  assumes "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     "observable M1"
  and     "observable M2"
  and     "io_targets M1 q1 io = { q1t }"
  and     "io_targets M2 q2 io = { q2t }"
shows "language_state M1 q1t \<subseteq> language_state M2 q2t"
using assms proof (induction io arbitrary: q1 q2)
  case Nil
  then show ?case by auto
next
  case (Cons io_hd io_tl)
  then obtain x y where hs_split : "io_hd = (x,y)"  by (meson surj_pair)
  then obtain tr where tr_def : 
     "target (io_hd # io_tl || tr) q1 = q1t"
     "path M1 (io_hd # io_tl || tr) q1" 
     "length (io_hd # io_tl) = length tr" using Cons unfolding io_targets.simps
  proof -
    assume a1: "{target (io_hd # io_tl || tr) q1 |tr. path M1 (io_hd # io_tl || tr) q1 \<and> length (io_hd # io_tl) = length tr} = {q1t}"
    assume a2: "\<And>tr. \<lbrakk>target (io_hd # io_tl || tr) q1 = q1t; path M1 (io_hd # io_tl || tr) q1; length (io_hd # io_tl) = length tr\<rbrakk> \<Longrightarrow> thesis"
    have "\<exists>cs. q1t = target (io_hd # io_tl || cs) q1 \<and> path M1 (io_hd # io_tl || cs) q1 \<and> length (io_hd # io_tl) = length cs"
      using a1 by blast
    then show ?thesis using a2 by blast
  qed 
  then obtain q1x tr_tl where tr_split : "tr = q1x # tr_tl" by (metis Suc_length_conv)

  then have "{t. path M1 (io_tl || t) q1x \<and> length io_tl = length t} = {tr_tl}" using observable_path_unique tr_def Cons.prems(2)
    by (smt Collect_cong FSM.path_cons_elim language_state length_Cons nat.simps(1) singleton_conv snd_conv zip_Cons_Cons)    
  moreover have 
     "target (io_tl || tr_tl) q1x = q1t"
     "path M1 (io_tl || tr_tl) q1x" 
     "length io_tl = length tr_tl" using Cons tr_def tr_split unfolding io_targets.simps by auto
  ultimately have tgt1 : "io_targets M1 q1x io_tl = { q1t }" using Cons.prems tr_def unfolding io_targets.simps  by auto

  have "io_hd # io_tl \<in> language_state M2 q2" using Cons using tr_def(2) tr_def(3) by blast 
  then obtain tr2 where tr2_def : 
     "target (io_hd # io_tl || tr2) q2 = q2t"
     "path M2 (io_hd # io_tl || tr2) q2" 
     "length (io_hd # io_tl) = length tr2" using Cons unfolding io_targets.simps language_state_def
  proof -
    assume "{target (io_hd # io_tl || tr) q1 |tr. path M1 (io_hd # io_tl || tr) q1 \<and> length (io_hd # io_tl) = length tr} = {q1t}"
    assume a1: "{target (io_hd # io_tl || tr) q2 |tr. path M2 (io_hd # io_tl || tr) q2 \<and> length (io_hd # io_tl) = length tr} = {q2t}"
    assume a2: "\<And>tr2. \<lbrakk>target (io_hd # io_tl || tr2) q2 = q2t; path M2 (io_hd # io_tl || tr2) q2; length (io_hd # io_tl) = length tr2\<rbrakk> \<Longrightarrow> thesis"
    have "\<exists>ds. q2t = target (io_hd # io_tl || ds) q2 \<and> path M2 (io_hd # io_tl || ds) q2 \<and> length (io_hd # io_tl) = length ds"
      using a1 by blast
    then show ?thesis using a2 by blast
  qed 
  then obtain q2x tr2_tl where tr2_split : "tr2 = q2x # tr2_tl" by (metis Suc_length_conv)

  then have "{t. path M2 (io_tl || t) q2x \<and> length io_tl = length t} = {tr2_tl}"
    by (smt Collect_cong FSM.path_cons_elim assms(3) language_state length_Cons nat.simps(1) observable_path_unique singleton_conv snd_conv tr2_def(2) tr2_def(3) zip_Cons_Cons) 
  moreover have 
     "target (io_tl || tr2_tl) q2x = q2t"
     "path M2 (io_tl || tr2_tl) q2x" 
     "length io_tl = length tr2_tl" using Cons tr2_def tr2_split unfolding io_targets.simps by auto
  ultimately have tgt2 : "io_targets M2 q2x io_tl = { q2t }" using Cons.prems tr_def unfolding io_targets.simps  by auto

  have "language_state M1 q1x \<subseteq> language_state M2 q2x" 
  proof 
    fix ioX assume ioX_assm : "ioX \<in> language_state M1 q1x"
    then obtain tr1X where tr1X_def : "path M1 (ioX || tr1X) q1x" "length tr1X = length ioX" by auto
    moreover have "path M1 [(io_hd,q1x)] q1" using tr_def tr_split Cons by auto
    ultimately have "path M1 ((io_hd#ioX)|| (q1x#tr1X)) q1" "length (io_hd#ioX) = length (q1x#tr1X)" using tr1X_def by auto
    then have "io_hd # ioX \<in> language_state M1 q1" by (metis language_state)
    then have "io_hd # ioX \<in> language_state M2 q2" using Cons.prems by auto
    then obtain q2x' tr2X where tr2X_def : "path M2 (io_hd # ioX || q2x' # tr2X) q2" "length tr2X = length ioX" by (metis language_state_elim length_Suc_conv) 

    have "path M2 ([io_hd] || [q2x]) q2" using tr2_def(2) tr2_split by auto 
    moreover have "path M2 ([io_hd] || [q2x']) q2" using tr2X_def(1) by auto 
    moreover have "[io_hd] \<in> language_state M2 q2" using tr2X_def unfolding language_state_def
    proof -
      have "\<exists>ps. [io_hd] = map fst ps \<and> path M2 ps q2"
        by (metis (no_types) calculation(2) list.size(3) list.size(4) map_fst_zip)
      then show "[io_hd] \<in> {map fst ps |ps. path M2 ps q2}"
        by blast
    qed
    ultimately have "q2x = q2x'" using observable_path_unique Cons.prems by (metis length_Cons list.inject list.size(3)) 

    then show  "ioX \<in> language_state M2 q2x" using tr2X_def(1) tr2X_def(2) by auto 
  qed

  then show ?thesis using Cons.prems tgt1 tgt2 Cons.IH by auto
qed


fun language_state_for_input :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> ('in \<times> 'out) list set" where
  "language_state_for_input M q xs = {(xs || ys) | ys . (length xs = length ys \<and> (xs || ys) \<in> language_state M (initial M))}"

fun language_state_in :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set" where
  "language_state_in M q ISeqs = {(xs || ys) | xs ys . (xs \<in> ISeqs \<and> length xs = length ys \<and> (xs || ys) \<in> language_state M (initial M))}"

lemma language_state_in_alt_def :
  "language_state_in M q ISeqs = \<Union> (image (language_state_for_input M q) ISeqs)"
proof 
  show "language_state_in M q ISeqs \<subseteq> UNION ISeqs (language_state_for_input M q)" 
  proof 
    fix x assume "x \<in> language_state_in M q ISeqs"
    then show "x \<in> UNION ISeqs (language_state_for_input M q)" by auto 
  qed
  show "UNION ISeqs (language_state_for_input M q) \<subseteq> language_state_in M q ISeqs"
  proof
    fix x assume x_assm : "x \<in> UNION ISeqs (language_state_for_input M q)"
    then show "x \<in> language_state_in M q ISeqs" by auto
  qed
qed






lemma det_state_cover_empty : 
  assumes "is_det_state_cover M V"
  shows "[] \<in> V"
proof -
  obtain f where f_def : "is_det_state_cover_ass M f \<and> V = f ` d_reachable M (initial M)" using assms by auto
  then have "f (initial M) = []" by auto
  moreover have "initial M \<in> d_reachable M (initial M)" 
  proof -
    have "d_reaches M (initial M) [] (initial M)" by auto
    then show ?thesis by (metis d_reachable.simps mem_Collect_eq) 
  qed
  moreover have "f (initial M) \<in> V" using f_def calculation by blast
  ultimately show ?thesis by auto
qed

lemma language_state_in_empty : 
  assumes "[] \<in> V"
  shows "[] \<in> language_state_in M q V"
proof -
  have "[] \<in> language_state_for_input M q []" by auto
  then show ?thesis using language_state_in_alt_def by (metis UN_I assms) 
qed

lemma language_state_for_input_empty[simp] : 
  "language_state_for_input M q [] = {[]}"
by auto



lemma observable_path_prefix :
  assumes "observable M"
  and     "path M (io || tr) q"
  and     "length io = length tr"
  and     "path M (ioP || trP) q"
  and     "length ioP = length trP"
  and     "prefix ioP io" 
shows "trP = take (length ioP) tr"
proof -
  have ioP_def : "ioP = take (length ioP) io" using assms(6) by (metis append_eq_conv_conj prefixE) 
  then have "take (length ioP) (io || tr) = take (length ioP) io || take (length ioP) tr" using take_zip by blast 
  moreover have "path M (take (length ioP) (io || tr)) q" using assms by (metis FSM.path_append_elim append_take_drop_id)
  ultimately have "path M (take (length ioP) io || take (length ioP) tr) q \<and> length (take (length ioP) io) = length (take (length ioP) tr)" using assms(3) by auto
  then have "path M (ioP || take (length ioP) tr) q \<and> length ioP = length (take (length ioP) tr)" using assms(3) using ioP_def by auto
  then show ?thesis by (meson assms(1) assms(4) assms(5) language_state observable_path_unique)
qed


abbreviation "L M \<equiv> language_state M (initial M)"

end