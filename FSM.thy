theory FSM
  imports Main
begin

record ('in, 'out, 'state) FSM =
  states  :: "'state set"
  initial :: "'state"
  inputs  :: "'in set"
  outputs :: "'out set"
  transitions :: "('state * 'in * 'out * 'state) set"



(*
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
*)

fun is_enabled_sequence :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list => bool" where
"is_enabled_sequence M s Nil = True" |
"is_enabled_sequence M s ((s1,x,y,s2)#seq) = (s = s1 \<and> (s1,x,y,s2) \<in> transitions M \<and> is_enabled_sequence M s2 seq)"

print_theorems

fun enabled_sequences :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list set" where
"enabled_sequences M s = {seq . is_enabled_sequence M s seq}"

fun get_io :: "('state * 'in * 'out * 'state) list \<Rightarrow> ('in * 'out) list" where
"get_io seq = map (\<lambda> (s1,x,y,s2) . (x,y)) seq"

definition is_enabled_io_sequence :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in * 'out) list => bool" where
"is_enabled_io_sequence M s io \<equiv> \<exists> seq . is_enabled_sequence M s seq \<and> io = get_io seq"

fun is_target :: "('state * 'in * 'out * 'state) list => 'state \<Rightarrow> bool" where
"is_target Nil q = False" |
"is_target ((s1,x,y,s2)#seq) q = (q = s2 \<or> is_target seq q)"

definition visits :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list \<Rightarrow> 'state \<Rightarrow> bool" where
"visits M s seq q \<equiv> is_enabled_sequence M s seq \<and> is_target seq q"

definition reaches :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list \<Rightarrow> 'state \<Rightarrow> bool" where
"reaches M s seq q \<equiv> is_enabled_sequence M s seq \<and> (case seq of
  Nil \<Rightarrow> q = s |
  _   \<Rightarrow> case (last seq) of (s1,x,y,s2) \<Rightarrow> q = s2)"






definition well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
"well_formed M \<equiv> 
    finite (states M)
  \<and> initial M \<in> states M
  \<and> finite (inputs M)
  \<and> finite (outputs M)
  (*\<and> (\<forall> (s1,x,y,s2) \<in> transitions M . 
      s1 \<in> states M \<and> s2 \<in> states M \<and> x \<in> inputs M \<and> y \<in> outputs M)*)
  \<and> transitions M \<subseteq> (states M) \<times> (inputs M) \<times> (outputs M) \<times> (states M)
  \<and> (\<forall> s \<in> states M . \<exists> seq . reaches M (initial M) seq s)
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
"observable M \<equiv> \<forall> s1 x y s2 s3 . ((s1,x,y,s2) \<in> (transitions M) \<and> (s1,x,y,s3) \<in> (transitions M)) \<longrightarrow> s2 = s3"

definition completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
"completely_specified M \<equiv> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<exists> y \<in> outputs M . \<exists> s2 \<in> states M . (s1,x,y,s2) \<in> transitions M"

definition deterministic :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
"deterministic M \<equiv> \<forall> s1 x y1 y2 s2 s3 . ((s1,x,y1,s2) \<in> (transitions M) \<and> (s1,x,y2,s3) \<in> (transitions M)) \<longrightarrow> (s2 = s3 \<and> y1 = y2)"

lemma observable_alt : "well_formed M \<Longrightarrow> observable M \<Longrightarrow> \<forall> s1 \<in> states M . \<forall> x \<in> inputs M . \<forall> y \<in> outputs M . (h_y M s1 x y = {}) \<or> (\<exists> s2 . h_y M s1 x y = {s2})"
  apply (simp add: well_formed_def observable_def)
  apply auto
  by (metis (mono_tags, lifting) Collect_cong singleton_conv)

lemma get_io_length : "
  well_formed M 
  \<Longrightarrow> is_enabled_sequence M s seq 
  \<Longrightarrow> io = get_io seq 
  \<Longrightarrow> is_enabled_sequence M s seq2  
  \<Longrightarrow> io = get_io seq2 
  \<Longrightarrow> length seq = length seq2"
  apply (simp)
  by (metis length_map)

lemma observable_sequence1 : "
  well_formed M 
  \<Longrightarrow> observable M 
  \<Longrightarrow> is_enabled_sequence M s ((s1,x11,y11,s2)#S1)
  \<Longrightarrow> is_enabled_sequence M s ((t1,x12,y12,t2)#S2)  
  \<Longrightarrow> get_io ((s1,x11,y11,s2)#S1) = get_io ((t1,x12,y12,t2)#S2)  
  \<Longrightarrow> (s1,x11,y11,s2) = (t1,x12,y12,t2)"
  by (auto simp: well_formed_def observable_def)

lemma observable_sequence1c : "
  well_formed M 
  \<Longrightarrow> observable M 
  \<Longrightarrow> is_enabled_sequence M s ((s1,x11,y11,s2)#S1)
  \<Longrightarrow> is_enabled_sequence M s ((t1,x12,y12,t2)#S2)  
  \<Longrightarrow> get_io ((s1,x11,y11,s2)#S1) = get_io ((t1,x12,y12,t2)#S2)  
  \<Longrightarrow> S1 = S2
  \<Longrightarrow> ((s1,x11,y11,s2)#S1) = ((t1,x12,y12,t2)#S2)"
  by (auto simp: well_formed_def observable_def)

lemma observable_sequence1d : "
  well_formed M 
  \<Longrightarrow> observable M 
  \<Longrightarrow> is_enabled_sequence M s (a1#S1)
  \<Longrightarrow> is_enabled_sequence M s (a2#S2)  
  \<Longrightarrow> get_io (a1#S1) = get_io (a2#S2)  
  \<Longrightarrow> S1 = S2
  \<Longrightarrow> (a1#S1) = (a2#S2)"
  apply (cases a1)
  apply (cases a2)
  by (auto simp: well_formed_def observable_def)

lemma observable_sequence1e : "
  well_formed M 
  \<Longrightarrow> observable M 
  \<Longrightarrow> is_enabled_sequence M s (a1#S1)
  \<Longrightarrow> is_enabled_sequence M s S2  
  \<Longrightarrow> get_io (a1#S1) = get_io S2  
  \<Longrightarrow> S1 = tl S2
  \<Longrightarrow> (a1#S1) = S2"
  apply (cases a1)
  by (auto simp: well_formed_def observable_def)


lemma observable_sequence : "
  well_formed M 
  \<Longrightarrow> observable M 
  \<Longrightarrow> is_enabled_sequence M s seq 
  \<Longrightarrow> is_enabled_sequence M s seq2  
  \<Longrightarrow> get_io seq = get_io seq2 
  \<Longrightarrow> seq = seq2"
proof (induction seq)
  case Nil
  then show ?case by auto
next
  case (Cons a seq)
  
  

  (*then have "length (a # seq) = length seq2" by (meson get_io_length)*)
  then show ?case sorry
qed
 

  apply (induction seq)
   apply (simp)
  apply (frule get_io_length)
  apply auto

  apply (frule observable_sequence1e)
       apply auto
  apply sledgehammer

  apply (cases seq2)
   apply (simp add: well_formed_def observable_def)
  apply auto
  apply sledgehammer
   apply (simp add: observable_def)
  apply sledgehammer
apply (auto simp: well_formed_def observable_def)

end