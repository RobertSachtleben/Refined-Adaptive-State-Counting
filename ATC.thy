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
  assumes wf1 : "well_defined M1"
  assumes wf2 : "well_defined M2"
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