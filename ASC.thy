theory ASC
imports ATC4 FSM2 FSM_Product
begin 

(* Proposition 5.4.2 *)
(* see B_dist, B_dist' in ATC *)


(* R *)
fun R :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list set" where
  "R M s vs xs = { vs @ xs' | xs' . xs' \<noteq> [] \<and> prefix xs' xs \<and> s \<in> io_targets M (initial M) (vs @ xs') }"

(* Lemma 5.4.5 *)
lemma R_count :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {q}"
  and "path PM (xs || tr) q" 
  and "length tr = length xs"
  and "distinct (states (xs || tr) q)" 
  shows "card (\<Union> (image (io_targets M1 (initial M1)) (R M2 s vs xs))) = card (R M2 s vs xs)"
  by sorry


(* V' *)
fun Perm :: "'in list set \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> ('in \<times> 'out) list set set" where
  "Perm V M = {image f V | f . \<forall> v . f v \<in> language_state_for_input M (initial M) v }"

lemma perm_empty :
  assumes "is_det_state_cover M V"
  and "V'' \<in> Perm V M"
shows "[] \<in> V''"
proof -
  have init_seq : "[] \<in> V" using det_state_cover_empty assms by simp
  obtain f where f_def : "V'' = image f V \<and> (\<forall> v . f v \<in> language_state_for_input M (initial M) v)" using assms by auto
  then have "f [] = []" using init_seq by (metis language_state_for_input_empty singleton_iff) 
  then show ?thesis using init_seq f_def by (metis image_eqI) 
qed


(* R\<^sup>+ *)
fun RP :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> ('in \<times> 'out) list set" where
  "RP M s vs xs V'' = R M s vs xs \<union> {vs' \<in> V'' . io_targets M (initial M) vs' = {s}}"

(* Lemma 5.4.8 *)
lemma RP_count :
  assumes "(vs @ xs) \<in> L M1 \<inter> L M2"
  and "s \<in> nodes M2"
  and "productF M2 M1 FAIL PM"
  and "io_targets PM (initial PM) vs = {q}"
  and "path PM (xs || tr) q" 
  and "length tr = length xs"
  and "distinct (states (xs || tr) q)" 
  and "V'' \<in> Perm V M"
  shows "card (\<Union> (image (io_targets M1 (initial M1)) (RP M2 s vs xs V''))) = card (RP M2 s vs xs V'')"
  by sorry


(* LB *)
fun LB :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> nat" where
  "LB M2 M1 vs xs T S \<Omega> V'' = (sum (\<lambda> s . card (RP M2 s vs xs V'')) S) 
                              + card ( (D M1 \<Omega> T) - {B M1 xs' \<Omega> | xs' s' . s' \<in> S \<and> xs' \<in> RP M2 s' vs xs V''})"


(* Prereq *)
fun Prereq :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'in list set \<Rightarrow> 'state1 set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set \<Rightarrow> bool" where 
  "Prereq M2 M1 vs xs T S \<Omega> V V'' = True"
(* 1 *)
(* 2 *)
(* 3 *)
(* 4 *)
(* 5 *)


(* Rep_pre *)

(* Rep_V *)

(* Lemma 5.4.11 *)


(* Lemma 5.4.13 *)
(* see minimal_sequence_to_failure_extending_det_state_cover_ob in FSM_Product *)








end