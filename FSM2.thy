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

(* "\<lambda> a p. snd a" "\<lambda> a p. snd a \<in> succ A (fst a) p \<and> (fst (fst a) \<in> inputs A) \<and> (snd (fst a) \<in> outputs A)" "\<lambda> p. p = initial A" *)

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






definition finite_FSM :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "finite_FSM M \<equiv> finite (nodes M)"

definition observable :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "observable M \<equiv> \<forall> t . \<forall> s1 . ((succ M) t s1 = {}) \<or> (\<exists> s2 . (succ M) t s1 = {s2})"

definition completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "completely_specified M \<equiv> \<forall> s1 . \<forall> x \<in> inputs M . \<exists> y \<in> outputs M . \<exists> s2 . s2 \<in> (succ M) (x,y) s1"

definition well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "well_formed M \<equiv>
    finite_FSM M
    \<and> (\<forall> s1 x y . (x \<notin> inputs M \<or> y \<notin> outputs M) \<longrightarrow> succ M (x,y) s1 = {})"

(*
lemma observable_path_unique_singleton:
  assumes "observable M"
  and     "path M ([io] || [tr1]) q"
  and     "path M ([io] || [tr2]) q"
shows "tr1 = tr2"
using assms unfolding observable_def
proof -
  assume "\<forall>t s1. succ M t s1 = {} \<or> (\<exists>s2. succ M t s1 = {s2})"
  then show ?thesis
    by (metis (no_types) FSM.path_cons_elim assms(2) assms(3) empty_iff prod.sel(1) prod.sel(2) singletonD zip_Cons_Cons)
qed
*)



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
    have tr_hd_eq : "tr1_hd = tr2_hd"           using Cons.prems unfolding observable_def
     proof -
      assume "\<forall>t s1. succ M t s1 = {} \<or> (\<exists>s2. succ M t s1 = {s2})"
      then show ?thesis
        by (metis (no_types) p1 p2 FSM.path_cons_elim empty_iff prod.sel(1) prod.sel(2) singletonD zip_Cons_Cons)
    qed

    then show ?thesis
      using Cons.IH Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) assms(2) tr_split by auto 
  qed
qed


lemma observable_path_unique_ex[elim] : 
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



definition d_reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'state set" where
  "d_reachable M p \<equiv> { q . (\<exists> xs ys tr . (path M ((xs || ys) || tr) p) \<and> target ((xs || ys) || tr) p = q 
                             \<and> (\<forall> ys2 tr2 .  (path M ((xs || ys2) || tr2) p) \<longrightarrow> target ((xs || ys2) || tr2) p = q)) }"

lemma d_reachable_reachable : "d_reachable M p \<subseteq> reachable M p" 
proof -
  have "d_reachable M p \<subseteq> {target r p |r. path M r p}"
  proof -
    obtain aa :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
      f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (aa x0 x1 \<in> x1 \<and> aa x0 x1 \<notin> x0)"
      by moura
    { assume "\<exists>ps. aa {target ps p |ps. path M ps p} (d_reachable M p) = target ps p \<and> path M ps p"
      then have "aa {target ps p |ps. path M ps p} (d_reachable M p) \<notin> d_reachable M p \<or> aa {target ps p |ps. path M ps p} (d_reachable M p) \<in> {target ps p |ps. path M ps p}"
        by blast
      then have ?thesis
        using f1 by (meson subsetI) }
    moreover
    { assume "\<nexists>bs cs as. path M ((bs || cs) || as) p \<and> target ((bs || cs) || as) p = aa {target ps p |ps. path M ps p} (d_reachable M p) \<and> (\<forall>cs as. path M ((bs || cs) || as) p \<longrightarrow> target ((bs || cs) || as) p = aa {target ps p |ps. path M ps p} (d_reachable M p))"
      then have "aa {target ps p |ps. path M ps p} (d_reachable M p) \<notin> d_reachable M p \<or> aa {target ps p |ps. path M ps p} (d_reachable M p) \<in> {target ps p |ps. path M ps p}"
        by (simp add: d_reachable_def)
      then have ?thesis
        using f1 by (meson subsetI) }
    ultimately show ?thesis
      by metis
  qed 
  then show ?thesis by blast
qed
 

end