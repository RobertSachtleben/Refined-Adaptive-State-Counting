theory FSM
imports
  "Transition_Systems_and_Automata.Sequence_Zip"
  "Transition_Systems_and_Automata.Transition_System"
  "Transition_Systems_and_Automata.Transition_System_Extra"
  "Transition_Systems_and_Automata.Transition_System_Construction"
begin 

section {* Finite state machines *}

text \<open>
We formalise finite state machines as a 4-tuples, omitting the explicit formulation of the state 
set,as it can easily be calculated from the successor function.
This definition does not require the successor function to be restricted to the input or output 
alphabet, which is later expressed by the property well_formed, together with the finiteness of
the state set.
\<close>

record ('in, 'out, 'state) FSM =
  succ :: "('in \<times> 'out) \<Rightarrow> 'state \<Rightarrow> 'state set"
  inputs :: "'in set"
  outputs :: "'out set"
  initial :: "'state"



subsection {* FSMs as transition systems *}

text \<open>
We interpret FSMs as transition systems with a singleton initial state set.
\<close>

global_interpretation FSM : transition_system_initial
"\<lambda> a p. snd a" "\<lambda> a p. snd a \<in> succ A (fst a) p" "\<lambda> p. p = initial A"
  for A
  defines path = FSM.path and run = FSM.run and reachable = FSM.reachable and nodes = FSM.nodes
  by this


subsection {* Language *}

text \<open>
The following definitions establish basic notions for FSMs similarly to those of nondeterministic
finite automata as defined in Transition_Systems_and_Automata.Automata.NFA.
\<close>

abbreviation "target \<equiv> FSM.target"
abbreviation "states \<equiv> FSM.states"
abbreviation "trace \<equiv> FSM.trace"

abbreviation successors :: "('in, 'out, 'state, 'more) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> FSM.successors TYPE('in) TYPE('out) TYPE('more)"

lemma states_alt_def: "states r p = map snd r" 
  by (induct r arbitrary: p) (auto)
lemma trace_alt_def: "trace r p = smap snd r" 
  by (coinduction arbitrary: r p) (auto)


definition language_state :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list set" ("LS") where
  "language_state M q \<equiv> {map fst r |r . path M r q}"

text \<open>
The language of an FSM is the language of its initial state.
\<close>
abbreviation "L M \<equiv> LS M (initial M)"
  

lemma language_state_alt_def : "LS M q = { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
proof -
  have "LS M q \<subseteq> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
  proof 
    fix xr assume xr_assm : "xr \<in> LS M q"
    then obtain r where r_def : "map fst r = xr" "path M r q" 
      unfolding language_state_def by auto
    then obtain xs ys where xr_split : "xr = xs || ys" "length xs = length ys" "length xs = length xr"
      by (metis length_map zip_map_fst_snd) 
    then have "(xs || ys) \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" 
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
    then show "xr \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" 
      using xr_split by metis
  qed
  moreover have "{ io | io tr . path M  (io || tr) q \<and> length io = length tr } \<subseteq> LS M q" 
  proof 
    fix xs assume xs_assm : "xs \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
    then obtain ys where ys_def : "path M (xs || ys) q" "length xs = length ys" 
      by auto
    then have "xs = map fst (xs || ys)" 
      by auto
    then show "xs \<in> LS M q" using ys_def unfolding language_state_def 
      by blast 
  qed
  ultimately show ?thesis 
    by auto
qed
  

lemma language_state[intro]:
  assumes "path M (w || r) q" "length w = length r"
  shows "w \<in> LS M q"
  using assms unfolding language_state_def by force

lemma language_state_elim[elim]:
  assumes "w \<in> LS M q"
  obtains r
  where "path M (w || r) q" "length w = length r"
  using assms unfolding language_state_def by (force iff: split_zip_ex)

lemma language_state_split:
  assumes "w1 @ w2 \<in> LS M q"
  obtains tr1 tr2
  where "path M (w1 || tr1) q" "length w1 = length tr1"
        "path M (w2 || tr2) (target (w1 || tr1) q)" "length w2 = length tr2"
proof -
  obtain tr where tr_def : "path M ((w1 @ w2) || tr) q" "length (w1 @ w2) = length tr"
    using assms by blast 
  let ?tr1 = "take (length w1) tr"
  let ?tr2 = "drop (length w1) tr"
  have tr_split : "?tr1 @ ?tr2 = tr" 
    by auto
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

lemma language_state_prefix :
  assumes "w1 @ w2 \<in> LS M q"
shows "w1 \<in> LS M q"
  using assms by (meson language_state language_state_split) 


subsection {* Product machine for language intersection *}

text \<open>
The following describes the classical creation of a product machine from two FSMs.
\<close>

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

lemma product_language_state[simp]: "LS (product A B) (q1,q2) = LS A q1 \<inter> LS B q2"
  by (fastforce iff: split_zip)




subsection {* Required properties *}

text \<open>
FSMs used by the adaptive state counting algorithm are required to satisfy certain properties which
are introduced in here.
Most notably, the observability property (see observable) implies the uniqueness of certain paths 
and hence allows for several stronger reformulations of previous results.
\<close>


fun finite_FSM :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "finite_FSM M = (finite (nodes M) \<and> finite (inputs M) \<and> finite (outputs M))"

fun observable :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "observable M = (\<forall> t . \<forall> s1 . ((succ M) t s1 = {}) \<or> (\<exists> s2 . (succ M) t s1 = {s2}))"

fun completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "completely_specified M = (\<forall> s1 \<in> nodes M . \<forall> x \<in> inputs M . \<exists> y \<in> outputs M . \<exists> s2 . s2 \<in> (succ M) (x,y) s1)"

fun well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "well_formed M =
    (finite_FSM M
    \<and> (\<forall> s1 x y . (x \<notin> inputs M \<or> y \<notin> outputs M) \<longrightarrow> succ M (x,y) s1 = {})
    \<and> inputs M \<noteq> {}
    \<and> outputs M \<noteq> {})"


lemma observable_path_unique[simp] :
  assumes "io \<in> LS M q"
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
    then show ?case using Nil 
      by simp
  next
    case (Cons io_hd io_tl)
    then obtain tr1_hd tr1_tl tr2_hd tr2_tl where tr_split : "tr1 = tr1_hd # tr1_tl \<and> tr2 = tr2_hd # tr2_tl"
      by (metis length_0_conv neq_Nil_conv)

    have p1: "path M ([io_hd] || [tr1_hd]) q"   
      using Cons.prems tr_split by auto
    have p2: "path M ([io_hd] || [tr2_hd]) q"   
      using Cons.prems tr_split by auto
    have tr_hd_eq : "tr1_hd = tr2_hd"           
      using Cons.prems unfolding observable.simps
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
  and     "io \<in> LS M q"
obtains tr 
where "{ t . path M (io || t) q \<and> length io = length t } = { tr }" 
proof -
  obtain tr where tr_def : "path M (io || tr) q" "length io = length tr" 
    using assms by auto
  then have "{ t . path M (io || t) q \<and> length io = length t } \<noteq> {}" 
    by blast
  moreover have "\<forall> t \<in> { t . path M (io || t) q \<and> length io = length t } . t = tr" 
    using assms tr_def by auto  
  ultimately show ?thesis 
    using that by moura
qed



subsection {* States reached by a given IO-sequence *}

text \<open>
The function io_targets collects all states of an FSM reached from a given state by a given 
IO-sequence.
Notably, for any observable FSM, this set contains at most one state.
\<close>

fun io_targets :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'state set" where
  "io_targets M q io = { target (io || tr) q | tr . path M (io || tr) q \<and> length io = length tr }"

lemma io_targets_observable_singleton_ex :
  assumes "observable M"
  and     "io \<in> LS M q1"
shows "\<exists> q2 . io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" 
    using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" 
    by fastforce 
  then show ?thesis 
    by blast 
qed

lemma io_targets_observable_singleton_ob :
  assumes "observable M"
  and     "io \<in> LS M q1"
obtains q2 
  where "io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" 
    using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" 
    by fastforce 
  then show ?thesis using that by blast 
qed

lemma io_targets_elim[elim] :
  assumes "p \<in> io_targets M q io"
obtains tr 
where "target (io || tr) q = p \<and> path M (io || tr) q \<and> length io = length tr" 
  using assms  unfolding io_targets.simps by force 


lemma io_targets_reachable :
  assumes "q2 \<in> io_targets M q1 io"
  shows "q2 \<in> reachable M q1" 
  using assms  unfolding io_targets.simps by blast

lemma io_targets_nodes :
  assumes "q2 \<in> io_targets M q1 io"
  and     "q1 \<in> nodes M"
shows "q2 \<in> nodes M"
  using assms by auto


lemma observable_io_targets_split :
  assumes "observable M"
  and "io_targets M q1 (vs @ xs) = {q3}"
  and "io_targets M q1 vs = {q2}"
shows "io_targets M q2 xs = {q3}"
proof -
  have "vs @ xs \<in> LS M q1" using assms(2) by force 
  then obtain trV trX where tr_def : 
        "path M (vs || trV) q1" "length vs = length trV"
        "path M (xs || trX) (target (vs || trV) q1)" "length xs = length trX" using language_state_split[of vs xs M q1] by auto
  then have tgt_V : "target (vs || trV) q1 = q2" using assms(3) by auto
  then have path_X : "path M (xs || trX) q2 \<and> length xs = length trX" using tr_def by auto

  have tgt_all :  "target (vs @ xs || trV @ trX) q1 = q3"
  proof -
    have f1: "\<exists>cs. q3 = target (vs @ xs || cs) q1 \<and> path M (vs @ xs || cs) q1 \<and> length (vs @ xs) = length cs"
      using assms(2) by auto
    have "length (vs @ xs) = length trV + length trX"
      by (simp add: tr_def(2) tr_def(4))
    then have "length (vs @ xs) = length (trV @ trX)"
      by simp
    then show ?thesis
      using f1 by (metis FSM.path_append \<open>vs @ xs \<in> LS M q1\<close> assms(1) observable_path_unique tr_def(1) tr_def(2) tr_def(3) zip_append)
  qed 
  then have "target ((vs || trV) @ (xs || trX)) q1 = q3" using tr_def by simp 
  then have "target (xs || trX) q2 = q3" using tgt_V by auto
  then have "q3 \<in> io_targets M q2 xs" using path_X by auto
  then show ?thesis by (metis (no_types) \<open>observable M\<close> path_X insert_absorb io_targets_observable_singleton_ex language_state singleton_insert_inj_eq')
qed 



lemma observable_io_target_unique_target :
  assumes "observable M"
  and     "io_targets M q1 io = {q2}"
  and     "path M (io || tr) q1"
  and     "length io = length tr"
shows "target (io || tr) q1 = q2"
  using assms by auto
  
lemma target_in_states : 
  assumes "length io = length tr"
  and     "length io > 0"
  shows "last (states (io || tr) q) = target (io || tr) q"
proof -
  have "0 < length tr"
    using assms(1) assms(2) by presburger
  then show ?thesis
    by (simp add: FSM.target_alt_def assms(1) states_alt_def)
qed 

lemma target_alt_def :
  assumes "length io = length tr"
  shows "length io = 0 \<Longrightarrow> target (io || tr) q = q"
        "length io > 0 \<Longrightarrow> target (io || tr) q = last tr"
proof -
  show "length io = 0 \<Longrightarrow> target (io || tr) q = q" by simp
  show "length io > 0 \<Longrightarrow> target (io || tr) q = last tr" 
    by (metis assms last_ConsR length_greater_0_conv map_snd_zip scan_last states_alt_def) 
qed

lemma obs_target_is_io_targets :
  assumes "observable M"
  and     "path M (io || tr) q"
  and     "length io = length tr"
shows "io_targets M q io = {target (io || tr) q}"
  by (metis assms(1) assms(2) assms(3) io_targets_observable_singleton_ex language_state observable_io_target_unique_target)



lemma io_target_target :
  assumes "io_targets M q1 io = {q2}"
  and     "path M (io || tr) q1"
  and     "length io = length tr"
shows "target (io || tr) q1 = q2"
proof -
  have "target (io || tr) q1 \<in> io_targets M q1 io" using assms(2) assms(3) by auto 
  then show ?thesis using assms(1) by blast
qed 


lemma index_last_take :
  assumes "i < length xs"
  shows "xs ! i = last (take (Suc i) xs)"
  by (simp add: assms take_Suc_conv_app_nth) 

lemma path_last_io_target :
  assumes "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "last tr \<in> io_targets M q xs" 
proof -
  have "last tr = target (xs || tr) q"
    by (metis assms(2) assms(3) map_snd_zip states_alt_def target_in_states)
  then show ?thesis using assms(1) assms(2) by auto
qed


lemma path_prefix_io_targets :
  assumes "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "last (take (Suc i) tr) \<in> io_targets M q (take (Suc i) xs)" 
proof -
  have "path M (take (Suc i) xs || take (Suc i) tr) q" by (metis (no_types) FSM.path_append_elim append_take_drop_id assms(1) take_zip) 
  then show ?thesis using assms(2) assms(3) path_last_io_target by fastforce  
qed


lemma states_index_io_target :
  assumes "i < length xs"
  and     "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "(states (xs || tr) q) ! i \<in> io_targets M q (take (Suc i) xs)"
proof -
  have "(states (xs || tr) q) ! i = last (take (Suc i) (states (xs || tr) q))" by (metis assms(1) assms(3) map_snd_zip states_alt_def index_last_take) 
  then have "(states (xs || tr) q) ! i = last (states (take (Suc i) xs || take (Suc i) tr) q)"by (simp add: take_zip) 
  then have "(states (xs || tr) q) ! i = last (take (Suc i) tr)" by (simp add: assms(3) states_alt_def) 
  moreover have "last (take (Suc i) tr) \<in> io_targets M q (take (Suc i) xs)" by (meson assms(2) assms(3) assms(4) path_prefix_io_targets) 
  ultimately show ?thesis by simp
qed


lemma observable_io_targets_append :
  assumes "observable M"
  and "io_targets M q1 vs = {q2}"
  and "io_targets M q2 xs = {q3}"
shows "io_targets M q1 (vs@xs) = {q3}"
proof -
  obtain trV where "path M (vs || trV) q1 \<and> length trV = length vs \<and> target (vs || trV) q1 = q2" by (metis assms(2) io_targets_elim singletonI) 
  moreover obtain trX where "path M (xs || trX) q2 \<and> length trX = length xs \<and> target (xs || trX) q2 = q3" by (metis assms(3) io_targets_elim singletonI)
  ultimately have "path M (vs @ xs || trV @ trX) q1 \<and> length (trV @ trX) = length (vs @ xs) \<and> target (vs @ xs || trV @ trX) q1 = q3" by auto
  then show ?thesis by (metis assms(1) obs_target_is_io_targets) 
qed


lemma observable_io_target_is_singleton[simp] :
  assumes "observable M"
  and     "p \<in> io_targets M q io"
shows "io_targets M q io = {p}" 
proof -
  have "io \<in> LS M q" using assms(2) by auto
  then obtain p' where "io_targets M q io = {p'}" using assms(1) by (meson io_targets_observable_singleton_ex) 
  then show ?thesis using assms(2) by simp
qed


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



subsection {* D-reachability *}

text \<open>
A state of some FSM is d-reached by some input sequence if any sequence in the language of the FSM
with this input sequence reaches that state. That state is then called d-reachable. 
\<close>

abbreviation  "d_reached_by M p xs q tr ys \<equiv> ((length xs = length ys \<and> length xs = length tr \<and> (path M ((xs || ys) || tr) p) \<and> target ((xs || ys) || tr) p = q) 
                            \<and> (\<forall> ys2 tr2 .  (length xs = length ys2 \<and> length xs = length tr2 \<and> path M ((xs || ys2) || tr2) p) \<longrightarrow> target ((xs || ys2) || tr2) p = q))"  

fun d_reaches :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> 'state \<Rightarrow> bool" where
  "d_reaches M p xs q = (\<exists> tr ys . d_reached_by M p xs q tr ys)"

fun d_reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'state set" where
  "d_reachable M p = { q . (\<exists> xs . d_reaches M p xs q) }"


lemma d_reaches_unique[elim] : 
  assumes "d_reaches M p xs q1"
  and    "d_reaches M p xs q2"
shows "q1 = q2"
using assms unfolding d_reaches.simps by blast

lemma d_reaches_unique_cases[simp] : "{ q . d_reaches M (initial M) xs q } = {} \<or> (\<exists> q2 . { q . d_reaches M (initial M) xs q } = { q2 })"
  unfolding d_reaches.simps by blast

lemma d_reaches_unique_obtain[simp] :
  assumes "d_reaches M (initial M) xs q"
shows "{ p . d_reaches M (initial M) xs p } = { q }"
  using assms unfolding d_reaches.simps by blast

lemma d_reaches_io_target :
  assumes "d_reaches M p xs q"
  and     "length ys = length xs"
shows "io_targets M p (xs || ys) \<subseteq> {q}"
proof 
  fix q' assume "q' \<in> io_targets M p (xs || ys)"
  then obtain trQ where "path M ((xs || ys) || trQ) p \<and> length (xs || ys) = length trQ" 
    by auto
  moreover obtain trD ysD where "d_reached_by M p xs q trD ysD" using assms(1) 
    by auto
  ultimately have "target ((xs || ys) || trQ) p = q" 
    by (simp add: assms(2))
  then show "q' \<in> {q}" 
    using \<open>d_reached_by M p xs q trD ysD\<close> \<open>q' \<in> io_targets M p (xs || ys)\<close> assms(2) by auto
qed
  
lemma d_reachable_reachable : "d_reachable M p \<subseteq> reachable M p" 
unfolding d_reaches.simps d_reachable.simps by blast


subsection {* Deterministic state cover *}

text \<open>
The deterministic state cover of some FSM is a minimal set of input sequences such that every
d-reachable state of the FSM is d-reached by a sequence in the set and the set contains the
empty sequence (which d-reaches the initial state). 
\<close>


fun is_det_state_cover_ass :: "('in, 'out, 'state) FSM \<Rightarrow> ('state \<Rightarrow> 'in list) \<Rightarrow> bool" where
  "is_det_state_cover_ass M f = (f (initial M) = [] \<and> (\<forall> s \<in> d_reachable M (initial M) . d_reaches M (initial M) (f s) s))"

lemma det_state_cover_ass_dist : 
  assumes "is_det_state_cover_ass M f"
  and     "s1 \<in> d_reachable M (initial M)"
  and     "s2 \<in> d_reachable M (initial M)"
  and     "s1 \<noteq> s2"
shows "\<not>(d_reaches M (initial M) (f s2) s1)"
  by (meson assms(1) assms(3) assms(4) d_reaches_unique is_det_state_cover_ass.simps)


lemma det_state_cover_ass_diff :
  assumes "is_det_state_cover_ass M f"
  and     "s1 \<in> d_reachable M (initial M)"
  and     "s2 \<in> d_reachable M (initial M)"
  and     "s1 \<noteq> s2"
shows "f s1 \<noteq> f s2"
  by (metis assms det_state_cover_ass_dist is_det_state_cover_ass.simps)


fun is_det_state_cover :: "('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> bool" where
  "is_det_state_cover M V = (\<exists> f . is_det_state_cover_ass M f \<and> V = image f (d_reachable M (initial M)))"

lemma det_state_cover_d_reachable[elim] :
  assumes "is_det_state_cover M V"
  and     "v \<in> V"
obtains q
where "d_reaches M (initial M) v q"
  by (metis (no_types, hide_lams) assms(1) assms(2) image_iff is_det_state_cover.simps is_det_state_cover_ass.elims(2))



lemma det_state_cover_card[simp] :
  assumes "is_det_state_cover M V"
  and     "finite (nodes M)"
shows   "card (d_reachable M (initial M)) = card V"
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

lemma det_state_cover_finite :
  assumes "is_det_state_cover M V"
  and     "finite (nodes M)"
shows "finite V"
proof -
  have "d_reachable M (initial M) \<subseteq> nodes M"
    by auto 
  show "finite V" using det_state_cover_card[OF assms]
    by (metis \<open>d_reachable M (initial M) \<subseteq> nodes M\<close> assms(1) assms(2) finite_imageI infinite_super is_det_state_cover.simps)    
qed


lemma det_state_cover_initial :
  assumes "is_det_state_cover M V"
  shows   "[] \<in> V"
proof -
  have "d_reached_by M (initial M) [] (initial M) [] []"
    by (simp add: FSM.nil)
  then have "d_reaches M (initial M) [] (initial M)" 
    by auto
  
  have "initial M \<in> d_reachable M (initial M)"
    by (metis (no_types) \<open>d_reaches M (initial M) [] (initial M)\<close> d_reachable.simps mem_Collect_eq)
  then show ?thesis
    by (metis (no_types, lifting) assms image_iff is_det_state_cover.elims(2) is_det_state_cover_ass.simps) 
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




subsection {* IO reduction *}

text \<open>
An FSM is a reduction of another, if its language is a subset of the language of the latter FSM.
\<close>


fun io_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> bool" (infix "\<preceq>" 200) where 
  "M1 \<preceq> M2 = (LS M1 (initial M1) \<subseteq> LS M2 (initial M2))"


lemma language_state_inclusion_of_state_reached_by_same_sequence : 
  assumes "LS M1 q1 \<subseteq> LS M2 q2"
  and     "observable M1"
  and     "observable M2"
  and     "io_targets M1 q1 io = { q1t }"
  and     "io_targets M2 q2 io = { q2t }"
shows "LS M1 q1t \<subseteq> LS M2 q2t"
proof 
  fix x assume "x \<in> LS M1 q1t" 
  obtain q1x where "io_targets M1 q1t x = {q1x}"
    by (meson \<open>x \<in> LS M1 q1t\<close> assms(2) io_targets_observable_singleton_ex) 
  have "io \<in> LS M1 q1" 
    using assms(4) by auto
  have "io@x \<in> LS M1 q1" 
    using observable_io_targets_append[OF assms(2) \<open>io_targets M1 q1 io = { q1t }\<close> \<open>io_targets M1 q1t x = {q1x}\<close>]
    by (metis io_targets_elim language_state singletonI) 
  then have "io@x \<in> LS M2 q2" 
    using assms(1) by blast
  then obtain q2x where "io_targets M2 q2 (io@x) = {q2x}"
    by (meson assms(3) io_targets_observable_singleton_ex)
  show "x \<in> LS M2 q2t"
    using observable_io_targets_split[OF assms(3) \<open>io_targets M2 q2 (io @ x) = {q2x}\<close> assms(5)] by auto
qed




subsection {* Language subsets for input sequences *}

text \<open>
The following definitions describe restrictions of languages to only those IO-sequences that 
exhibit a certain input sequence or whose input sequence is contained in a given set of
input sequences.
This allows to define the notion that some FSM is a reduction of another over a given set of
input sequences, but not necessarily over the entire language of the latter FSM.
\<close>

fun language_state_for_input :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> ('in \<times> 'out) list set" where
  "language_state_for_input M q xs = {(xs || ys) | ys . (length xs = length ys \<and> (xs || ys) \<in> LS M q)}"

fun language_state_for_inputs  :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set" ("(LS\<^sub>i\<^sub>n _ _ _)" [1000,1000,1000]) where
  "language_state_for_inputs  M q ISeqs = {(xs || ys) | xs ys . (xs \<in> ISeqs \<and> length xs = length ys \<and> (xs || ys) \<in> LS M q)}"

abbreviation "L\<^sub>i\<^sub>n M TS \<equiv> LS\<^sub>i\<^sub>n M (initial M) TS"

abbreviation  "io_reduction_on M1 TS M2 \<equiv> (LS\<^sub>i\<^sub>n M1 (initial M1) TS \<subseteq> LS\<^sub>i\<^sub>n M2 (initial M2) TS)" 
notation 
  io_reduction_on ("(_ \<preceq>\<lbrakk>_\<rbrakk> _)" )
notation  (latex output)
  io_reduction_on ("(_ \<preceq>\<^bsub>_\<^esub> _)" [1000,0,0] 61)


lemma language_state_for_input_alt_def :
  "language_state_for_input M q xs = LS\<^sub>i\<^sub>n M q {xs}"
  unfolding language_state_for_input.simps language_state_for_inputs.simps by blast

lemma language_state_for_inputs_alt_def :
  "LS\<^sub>i\<^sub>n M q ISeqs = \<Union> (image (language_state_for_input M q) ISeqs)" 
  by auto

lemma language_state_for_inputs_nonempty :
  assumes "set xs \<subseteq> inputs M"
  and     "completely_specified M"
  and     "q \<in> nodes M"
shows "LS\<^sub>i\<^sub>n M q {xs} \<noteq> {}"
using assms proof (induction xs arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "x \<in> inputs M" 
    by simp
  then obtain y q' where x_step : "q' \<in> succ M (x,y) q" 
    using Cons(3,4) unfolding completely_specified.simps by blast
  then have "path M ([(x,y)] || [q']) q \<and> length [q] = length [(x,y)]" "target ([(x,y)] || [q']) q = q'" 
    by auto
  then have "q' \<in> nodes M" 
    using Cons(4) by (metis FSM.nodes_target)            
  then have "LS\<^sub>i\<^sub>n M q' {xs} \<noteq> {}" 
    using Cons.prems Cons.IH by auto
  then obtain ys where "length xs = length ys \<and> (xs || ys) \<in> LS M q'" 
    by auto
  then obtain tr where "path M ((xs || ys) || tr) q' \<and> length tr = length (xs || ys)" 
    by auto
  then have "path M ([(x,y)] @ (xs || ys) || [q'] @ tr) q \<and> length ([q'] @ tr) = length ([(x,y)] @ (xs || ys))" 
    by (simp add: FSM.path.intros(2) x_step)
  then have "path M ((x#xs || y#ys) || [q'] @ tr) q \<and> length ([q'] @ tr) = length (x#xs || y#ys)" 
    by auto
  then have "(x#xs || y#ys) \<in> LS M q" 
    by (metis language_state)
  moreover have "length (x#xs) = length (y#ys)" 
    by (simp add: \<open>length xs = length ys \<and> xs || ys \<in> LS M q'\<close>) 
  ultimately have "(x#xs || y#ys) \<in> LS\<^sub>i\<^sub>n M q {x # xs}" 
    unfolding language_state_for_inputs.simps by blast
  then show ?case by blast
qed

lemma language_state_for_inputs_empty : 
  assumes "[] \<in> V"
  shows "[] \<in> LS\<^sub>i\<^sub>n M q V"
proof -
  have "[] \<in> language_state_for_input M q []" by auto
  then show ?thesis using language_state_for_inputs_alt_def by (metis UN_I assms) 
qed

lemma language_state_for_input_empty[simp] : 
  "language_state_for_input M q [] = {[]}"
by auto
























end