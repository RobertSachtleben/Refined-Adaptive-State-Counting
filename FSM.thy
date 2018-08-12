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

fun t_source :: "('state * 'in * 'out * 'state) \<Rightarrow> 'state" where
"t_source (s1,x,y,s2) = s1"

fun t_input :: "('state * 'in * 'out * 'state) \<Rightarrow> 'in" where
"t_input (s1,x,y,s2) = x"

fun t_output :: "('state * 'in * 'out * 'state) \<Rightarrow> 'out" where
"t_output (s1,x,y,s2) = y"

fun t_target :: "('state * 'in * 'out * 'state) \<Rightarrow> 'state" where
"t_target (s1,x,y,s2) = s2"


fun is_sequence :: "('in, 'out, 'state) FSM \<Rightarrow> ('state * 'in * 'out * 'state) list \<Rightarrow> bool" where
"is_sequence M Nil = True" |
"is_sequence M (a#Nil) = (a \<in> transitions M)" |
"is_sequence M (a#b#seq) = (a \<in> transitions M \<and> t_target a = t_source b \<and> is_sequence M (b#seq))" 



lemma sequence_drop :
  assumes "is_sequence M seq"
  shows "is_sequence M (drop n seq)"
proof (induction n)
  case 0
  then show ?case using assms by auto
next
  case (Suc n)
  then show ?case 
  proof (cases "drop (Suc n) seq")
    case Nil
    then show ?thesis by simp
  next
    case (Cons a list)
    let ?d1 = "drop n seq"
    let ?dh = "hd ?d1"
    let ?d2 = "drop (Suc n) seq"
    have "?d1 = ?dh # ?d2" by (metis drop_Suc drop_eq_Nil le_SucI list.exhaust_sel list.simps(3) local.Cons tl_drop)
    then show ?thesis by (metis Suc.IH is_sequence.simps(3) local.Cons)
  qed
qed

lemma sequence_transition :
  assumes is_seq : "is_sequence M seq"
  assumes is_idx : "n < length seq"
  assumes at_idx : "a = seq ! n"
  shows "a \<in> transitions M"
proof -
  let ?fromIdx = "drop n seq"
  have "is_sequence M ?fromIdx" using assms by (simp add: sequence_drop)
  moreover have "a = hd ?fromIdx" using assms by (simp add: hd_drop_conv_nth)
  ultimately show "a \<in> transitions M" using assms by (metis Cons_nth_drop_Suc is_sequence.simps(2) is_sequence.simps(3) length_drop length_greater_0_conv zero_less_diff)
qed
  


fun is_enabled_sequence :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list => bool" where
"is_enabled_sequence M s Nil = True" |
(*"is_enabled_sequence M s ((s1,x,y,s2)#seq) = (s = s1 \<and> (s1,x,y,s2) \<in> transitions M \<and> is_enabled_sequence M s2 seq)"*)
"is_enabled_sequence M s (a#seq) = ((fst a = s) \<and> is_sequence M (a#seq))"

print_theorems

fun enabled_sequences :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('state * 'in * 'out * 'state) list set" where
"enabled_sequences M s = {seq . is_enabled_sequence M s seq}"

fun get_io :: "('state * 'in * 'out * 'state) list \<Rightarrow> ('in * 'out) list" where
"get_io Nil = Nil" |
"get_io ((s1,x,y,s2)#seq) = (x,y) # get_io seq"
(*"get_io seq = zip (map t_input seq) (map t_output seq)"*)
(*"get_io seq = map (\<lambda> (s1,x,y,s2) . (x,y)) seq"*)

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

lemma get_io_length : "length seq = length (get_io seq)"
  apply (induction seq)
  apply auto
  done

lemma get_io_length_eq : 
  assumes "get_io seq1 = get_io seq2"
  shows "length seq1 = length seq2"
  by (metis assms get_io_length)
  


lemma first_list_diff_zip :
  fixes zipSeq :: "('a * 'a) list"
  assumes ineq : "map fst zipSeq \<noteq> map snd zipSeq"
  shows "\<exists> mdi . 
            mdi < length zipSeq 
            \<and> fst (zipSeq ! mdi) \<noteq> snd (zipSeq ! mdi)
            \<and> (\<forall> i . (i < mdi) \<longrightarrow> fst (zipSeq ! i) = snd (zipSeq ! i))"
proof
  let ?twi = "length (takeWhile (\<lambda> (a1,a2) . a1 = a2) zipSeq)"
  have "?twi < length zipSeq" 
  proof (rule ccontr)
    assume "\<not> (?twi < length zipSeq)"
    then have "?twi = length zipSeq" by (simp add: length_takeWhile_le nat_less_le)
    then have "map fst zipSeq = map snd zipSeq" by (metis length_map list_eq_iff_zip_eq nth_equalityI set_takeWhileD takeWhile_nth zip_map_fst_snd)
    then show "False" using ineq by auto
  qed
  moreover have "fst (zipSeq ! ?twi) \<noteq> snd (zipSeq ! ?twi)" using calculation nth_length_takeWhile by fastforce
  moreover have "\<forall> i . (i < ?twi) \<longrightarrow> fst (zipSeq ! i) = snd (zipSeq ! i)" by (metis (full_types) case_prod_beta' nth_mem set_takeWhileD takeWhile_nth)
  ultimately show "?twi < length zipSeq
            \<and> fst (zipSeq ! ?twi) \<noteq> snd (zipSeq ! ?twi)
            \<and> (\<forall> i . (i < ?twi) \<longrightarrow> fst (zipSeq ! i) = snd (zipSeq ! i))" by auto
qed
  

lemma first_list_diff : 
  assumes ineq: "seq1 \<noteq> seq2"
  assumes sameLength: "length seq1 = length seq2"
  shows "\<exists> mdi . 
          mdi < length seq1 
          \<and> seq1 ! mdi \<noteq> seq2 ! mdi 
          \<and> (\<forall> i . i < mdi \<longrightarrow> seq1 ! i = seq2 ! i)"
proof -
  let ?zipSeq = "zip seq1 seq2"
  have "map fst ?zipSeq \<noteq> map snd ?zipSeq" by (simp add: ineq sameLength)
  then have "\<exists> twi .
            twi < length ?zipSeq 
            \<and> fst (?zipSeq ! twi) \<noteq> snd (?zipSeq ! twi)
            \<and> (\<forall> i . (i < twi) \<longrightarrow> fst (?zipSeq ! i) = snd (?zipSeq ! i))" using  first_list_diff_zip by blast
  then show ?thesis by auto
qed

lemma sequence_source_target :
  assumes en : "is_sequence M seq"
  assumes idx: "(Suc j) < length seq"
  shows "t_target (seq ! j) = t_source (seq ! (Suc j))"
proof -
  have "is_sequence M (drop j seq)" using assms sequence_drop by auto
  moreover have "(seq ! j) = hd (drop j seq)" by (metis hd_drop_conv_nth idx lessI less_le_trans order.strict_implies_order)
  moreover have "(seq ! (Suc j)) = hd (tl (drop j seq))" using assms by (metis drop_Suc hd_drop_conv_nth tl_drop)
  ultimately show ?thesis using assms by (metis Cons_nth_drop_Suc Suc_lessD is_sequence.simps(3))
qed 

lemma get_io_input_index : "\<forall> j . ((j < length seq) \<and> (length seq > 0)) \<longrightarrow> t_input (seq ! j) = fst ((get_io seq) ! j)"
  apply (induction seq)
  apply auto
  using less_Suc_eq_0_disj by auto

lemma get_io_output_index : "\<forall> j . ((j < length seq) \<and> (length seq > 0)) \<longrightarrow> t_output (seq ! j) = snd ((get_io seq) ! j)"
  apply (induction seq)
  apply auto
  using less_Suc_eq_0_disj by auto

lemma get_io_index_eq :
  assumes en : "get_io seq1 = get_io seq2"
  assumes idx: "j < length seq1"
  assumes nonempty: " length seq1 > 0"
  shows "t_input (seq1 ! j) = t_input (seq2 ! j) \<and> t_output (seq1 ! j) = t_output (seq2 ! j)"
proof -
  have "length seq1 = length seq2" using assms get_io_length_eq by blast
  moreover have "t_input (seq1 ! j) = fst ((get_io seq1) ! j)" using assms by (simp add: get_io_input_index)
  moreover have "t_input (seq2 ! j) = fst ((get_io seq2) ! j)" using assms by (simp add: calculation(1) get_io_input_index)
  moreover have "t_input (seq1 ! j) = t_input (seq2 ! j)" using assms by (simp add: calculation(2) calculation(3))
  moreover have "t_output (seq1 ! j) = snd ((get_io seq1) ! j)" using assms by (simp add: get_io_output_index)
  moreover have "t_output (seq2 ! j) = snd ((get_io seq2) ! j)" using assms by (simp add: calculation(1) get_io_output_index)
  moreover have "t_output (seq1 ! j) = t_output (seq2 ! j)" using assms by (simp add: calculation(5) calculation(6))
  ultimately show ?thesis by auto
qed

theorem observable_unique_io:
  assumes wf:"well_formed M" 
  assumes ob:"observable M"  
  assumes e1:"is_enabled_sequence M s seq1" 
  assumes e2:"is_enabled_sequence M s seq2 "
  assumes io:"get_io seq1 = get_io seq2 "
  shows
    "seq1 = seq2"
proof (rule ccontr)
  assume ineq: "seq1 \<noteq> seq2"
  have nonempty: "length seq1 > 0" using assms get_io_length_eq ineq by fastforce
  have sameLength : "length seq1 = length seq2" by (metis get_io_length io)
  then obtain mdi where mdi_def : (* minimal difference index *)
        "mdi < length seq1 
          \<and> seq1 ! mdi \<noteq> seq2 ! mdi 
          \<and> (\<forall> i . i < mdi \<longrightarrow> seq1 ! i = seq2 ! i)" using first_list_diff ineq by blast
  then have "take mdi seq1 = take mdi seq2" by (simp add: nth_take_lemma sameLength)
  have seq1_trans : "seq1 ! mdi \<in> transitions M" using assms by (metis is_enabled_sequence.elims(2) length_greater_0_conv mdi_def nonempty sequence_transition)
  have seq2_trans : "seq2 ! mdi \<in> transitions M" using assms by (metis is_enabled_sequence.elims(2) length_greater_0_conv mdi_def sameLength sequence_transition)
  obtain s1 xa ya s2 where diff1_def : "seq1 ! mdi = (s1,xa,ya,s2)" using prod_cases4 by blast
  obtain t1 xb yb t2 where diff2_def : "seq2 ! mdi = (t1,xb,yb,t2)" using prod_cases4 by blast
    
  show "False"
  proof (cases mdi) (* rework case split, as both cases only differ meaningfully in the proof of s1=t1 *)
    case 0
    have "s1 = t1" using assms by (metis "0" diff1_def diff2_def fst_conv is_enabled_sequence.elims(2) list.size(3) mdi_def nth_Cons_0 sameLength)
    moreover have "xa = xb" using assms using "0" diff1_def diff2_def get_io_index_eq mdi_def by fastforce
    moreover have "ya = yb" using assms by (metis "0" diff1_def diff2_def get_io_output_index mdi_def sameLength t_output.simps)
    moreover have "(s1,xa,ya,s2) \<in> transitions M" using diff1_def seq1_trans by auto
    moreover have "(s1,xa,ya,t2) \<in> transitions M" using calculation(1) calculation(2) calculation(3) diff2_def seq2_trans by auto
    moreover have "s2 = t2" using calculation(4) calculation(5) ob observable_def by fastforce
    ultimately have "seq1 ! mdi = seq2 ! mdi" by (simp add: diff1_def diff2_def)
    moreover have "seq1 ! mdi \<noteq> seq2 ! mdi" using mdi_def by auto
    ultimately show ?thesis by auto
  next
    case (Suc lastSame)
    obtain s0 xp yp s1p where same_def : "seq1 ! lastSame = (s0,xp,yp,s1p)" using prod_cases4 by blast
    have same_last : "seq1 ! lastSame = seq2 ! lastSame" using mdi_def by (simp add: Suc)
    have "s1 = s1p" using assms sequence_source_target by (metis Suc diff1_def is_enabled_sequence.elims(2) list.size(3) mdi_def not_less0 same_def t_source.simps t_target.simps)
    moreover have "t1 = s1p" using assms sequence_source_target by (metis Suc diff2_def is_enabled_sequence.elims(2) length_greater_0_conv mdi_def sameLength same_def same_last t_source.simps t_target.simps)
    moreover have "s1 = t1" by (simp add: calculation(1) calculation(2))
    moreover have "xa = xb" using assms diff1_def diff2_def get_io_index_eq mdi_def by fastforce
    moreover have "ya = yb" using diff1_def diff2_def by (metis get_io_output_index io mdi_def nonempty sameLength t_output.simps)
    moreover have "(s1,xa,ya,s2) \<in> transitions M" using diff1_def seq1_trans by auto
    moreover have "(s1,xa,ya,t2) \<in> transitions M" using calculation(3) calculation(4) calculation(5) diff2_def seq2_trans by auto
    moreover have "s2 = t2" using calculation(6) calculation(7) ob observable_def by fastforce
    ultimately have "seq1 ! mdi = seq2 ! mdi" by (simp add: diff1_def diff2_def)
    moreover have "seq1 ! mdi \<noteq> seq2 ! mdi" using mdi_def by auto
    ultimately show ?thesis by auto
  qed
qed
  


end