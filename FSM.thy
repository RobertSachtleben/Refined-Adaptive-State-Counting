theory FSM
  imports Main
begin

record ('in, 'out, 'state) FSM =
  states  :: "'state set"
  initial :: "'state"
  inputs  :: "'in set"
  outputs :: "'out set"
  transitions :: "('state * 'in * 'out * 'state) set"

definition well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
"well_formed M \<equiv> 
    finite (states M)
  \<and> initial M \<in> states M
  \<and> finite (inputs M)
  \<and> finite (outputs M)
  (*\<and> (\<forall> (s1,x,y,s2) \<in> transitions M . 
      s1 \<in> states M \<and> s2 \<in> states M \<and> x \<in> inputs M \<and> y \<in> outputs M)*)
  \<and> transitions M \<subseteq> (states M) \<times> (inputs M) \<times> (outputs M) \<times> (states M)
"

lemma transition_finite : "well_formed M \<Longrightarrow> finite (transitions M)"
  apply (simp add: well_formed_def)
  apply auto
  apply (simp add: finite_subset)
  done



fun h :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in \<Rightarrow> ('out * 'state) set" where
"h M s1 x = { (y,s2) | y s2 . (s1,x,y,s2) \<in> transitions M }"

fun h_out :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in \<Rightarrow> 'out set" where
"h_out M s1 x = { fst r | r . r \<in> h M s1 x }"

fun h_reach :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in \<Rightarrow> 'state set" where
"h_reach M s1 x = { snd r | r . r \<in> h M s1 x }"

fun h_y :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in \<Rightarrow> 'out \<Rightarrow> 'state set" where
"h_y M s1 x y = { s2 . (y,s2) \<in> h M s1 x }"



definition observable :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
(*"observable M \<equiv> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . \<forall> s2a s2b . (s2a \<in> h_y M s1 x y \<and> s2b \<in> h_y M s1 x y) \<longrightarrow> s2a = s2b"*)
"observable M \<equiv> \<forall> s1 x y s2 s3 . ((s1,x,y,s2) \<in> (transitions M) \<and> (s1,x,y,s3) \<in> (transitions M)) \<longrightarrow> s2 = s3"

definition completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
"completely_specified M \<equiv> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<exists> y \<in> outputs M . \<exists> s2 \<in> states M . (s1,x,y,s2) \<in> transitions M"

definition deterministic :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
(*"deterministic M \<equiv> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<forall> ya s2a yb s2b . ((ya,s2a) \<in> h M s1 x \<and> (yb,s2b) \<in> h M s1 x) \<longrightarrow> (ya,s2a) = (yb,s2b)"*)
"deterministic M \<equiv> \<forall> s1 x y1 y2 s2 s3 . ((s1,x,y1,s2) \<in> (transitions M) \<and> (s1,x,y2,s3) \<in> (transitions M)) \<longrightarrow> (s2 = s3 \<and> y1 = y2)"

lemma observable_alt : "well_formed M \<Longrightarrow> observable M \<Longrightarrow> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (h_y M s1 x y = {}) \<or> (\<exists> s2 . h_y M s1 x y = {s2})"
  apply (simp add: well_formed_def observable_def)
  apply auto
  by (metis (mono_tags, lifting) Collect_cong singleton_conv)


inductive enabled_transition_seq :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> (('in * 'out) * 'state) list => bool" where
ets_nil  : "enabled_transition_seq M s Nil" |
ets_one  : "(s1,x,y,s2) \<in> transitions M \<Longrightarrow> enabled_transition_seq M s1 (((x,y),s2)#Nil)" |
ets_long : "(s1,x,y,s2) \<in> transitions M \<Longrightarrow> enabled_transition_seq M s2 seq \<Longrightarrow> enabled_transition_seq M s1 (((x,y),s2)#seq)"

inductive reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> bool" where
reachable_init : "reachable M (initial M)" |
reachable_immediately : "((initial M),x,y,s2) \<in> transitions M \<Longrightarrow> reachable M s2" |
reachable_distant : "(s2,x,y,s3) \<in> transitions M \<Longrightarrow> reachable M s2 \<Longrightarrow> reachable M s3"

inductive reaches :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> 'state \<Rightarrow> bool" where
reaches_nil : "reaches M Nil (initial M)" |
reaches_transition : "reaches M seq s1 \<Longrightarrow> (s1,x,y,s2) \<in> transitions M \<Longrightarrow> reaches M (seq@((x,y)#Nil)) s2"

lemma reachable_seq : "well_formed M \<Longrightarrow> reachable M s \<Longrightarrow> \<exists> seq . reaches M s seq" 
  apply sledgehammer
  apply (induction rule: reachable.induct)

definition reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> bool" where
"reachable M s \<equiv> s = (initial M) \<or> (\<exists> seq . (enabled_transition_seq M (initial M) seq) \<and> s = snd (snd (last seq)))"



fun apply_seq :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> ('in * 'out * 'state) list set" where
"apply_seq M s1 Nil = {Nil}" |
"apply_seq M s1 (x#xs) = {((x,y,s2)#res) | y s2 res . ((s1,x,y,s2) \<in> (transitions M) \<and> (res \<in> apply_seq M s2 xs))}"


lemma apply_seq_input_const : "res \<in> apply_seq M s xs \<Longrightarrow> length xs = length res"
  apply (induction xs)
   apply auto
  apply sledgehammer

lemma apply_seq_input_const : "res \<in> apply_seq M s xs \<Longrightarrow> xs = map fst res"
  apply (induction xs)
  apply auto
  apply sledgehammer

end