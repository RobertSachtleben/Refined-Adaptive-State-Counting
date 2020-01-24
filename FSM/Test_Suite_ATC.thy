theory Test_Suite_ATC
imports Adaptive_Test_Case State_Preamble Traversal_Set
begin



type_synonym ('a,'b) Preamble = "('a,'b) FSM_scheme"
type_synonym 'a Traversal_Path = "'a Transition list"
type_synonym ('a,'b) ATC = "('a \<times> 'a + 'a,'b) FSM_scheme"

(* problem: ATCs might not exist, preamble and traversal paths still need to be applied *)
type_synonym ('a,'b) Test_Case = "(('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('a,'b) ATC set)"
type_synonym ('a,'b) Test_Suite = "('a,'b) Test_Case set"

fun calculate_test_cases' :: "('a,'b) FSM_scheme \<Rightarrow> 'a Traversal_Path \<Rightarrow> 'a Traversal_Path \<Rightarrow> ('a,'b) ATC option" where
  "calculate_test_cases' M p1 p2 = calculate_state_separator_from_s_states M (target p1 (initial M)) (target p2 (initial M))" 

fun prefix_pairs :: "'a list \<Rightarrow> ('a list \<times> 'a list) list" 
  where "prefix_pairs [] = []" |
        "prefix_pairs xs = prefix_pairs (butlast xs) @ (map (\<lambda> ys. (ys,xs)) (butlast (prefixes xs)))"

value "prefix_pairs [1,2,3::nat]"




lemma prefixes_butlast :
  "set (butlast (prefixes xs)) = {ys . \<exists> zs . ys@zs = xs \<and> zs \<noteq> []}"
proof (cases xs rule: rev_cases)
  case Nil
  then show ?thesis by auto
next
  case (snoc ys y)
  
  have "prefixes (ys@[y]) = (prefixes ys) @ [ys@[y]]"
    by (metis prefixes.elims snoc_eq_iff_butlast)
  then have "butlast (prefixes xs) = prefixes ys"
    using snoc by auto
  then have "set (butlast (prefixes xs)) = {xs'. \<exists>xs''. xs' @ xs'' = ys}"
    using prefixes_set by auto
  also have "... = {xs'. \<exists>xs''. xs' @ xs'' = ys@[y] \<and> xs'' \<noteq> []}"
    by (metis (no_types, lifting) Nil_is_append_conv append.assoc butlast_append butlast_snoc not_Cons_self2)
  finally show ?thesis
    using snoc by simp
qed


lemma prefix_pairs_set :
  "set (prefix_pairs xs) = {(zs,ys) | zs ys . \<exists> xs1 xs2 . zs@xs1 = ys \<and> ys@xs2 = xs \<and> xs1 \<noteq> []}"  
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto 
next
  case (snoc x xs)
  have "prefix_pairs (xs @ [x]) = prefix_pairs (butlast (xs @ [x])) @ (map (\<lambda> ys. (ys,(xs @ [x]))) (butlast (prefixes (xs @ [x]))))"
    by (cases "(xs @ [x])"; auto)
  then have *: "prefix_pairs (xs @ [x]) = prefix_pairs xs @ (map (\<lambda> ys. (ys,(xs @ [x]))) (butlast (prefixes (xs @ [x]))))"
    by auto

  have "set (prefix_pairs xs) = {(zs, ys) |zs ys. \<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 = xs \<and> xs1 \<noteq> []}"
    using snoc.IH by assumption
  then have "set (prefix_pairs xs) = {(zs, ys) |zs ys. \<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 @ [x] = xs@[x] \<and> xs1 \<noteq> []}"
    by auto
  also have "... = {(zs, ys) |zs ys. \<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 = xs @[x] \<and> xs1 \<noteq> [] \<and> xs2 \<noteq> []}" 
  proof -
    let ?P1 = "\<lambda> zs ys . (\<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 @ [x] = xs@[x] \<and> xs1 \<noteq> [])"
    let ?P2 = "\<lambda> zs ys . (\<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 = xs @[x] \<and> xs1 \<noteq> [] \<and> xs2 \<noteq> [])"

    have "\<And> ys zs . ?P2 zs ys \<Longrightarrow> ?P1 zs ys"
      by (metis append_assoc butlast_append butlast_snoc)
    then have "\<And> ys zs . ?P1 ys zs = ?P2 ys zs"
      by blast
    then show ?thesis by force           
  qed
  finally have "set (prefix_pairs xs) = {(zs, ys) |zs ys. \<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 = xs @ [x] \<and> xs1 \<noteq> [] \<and> xs2 \<noteq> []}"
    by assumption

  moreover have "set (map (\<lambda> ys. (ys,(xs @ [x]))) (butlast (prefixes (xs @ [x])))) = {(zs, ys) |zs ys. \<exists>xs1 xs2. zs @ xs1 = ys \<and> ys @ xs2 = xs @ [x] \<and> xs1 \<noteq> [] \<and> xs2 = []}"
    using prefixes_butlast[of "xs@[x]"] by force

  ultimately show ?case using * by force
qed


(* TODO: review Petrenko/Yevtushenko *)

(* rework sketch:
  1.) calculate d-r states with preambles (set DR of (q,P))
  2.) calculate traversal sequences from d-r states (set DRT of (q,P,p,D) where D is the set satisfying the abortion criterion)
  3.1.) for all (q,P,p,D) calculate prefixes p1 < p2 of p s.t. their targets (from q) are in D
        \<rightarrow> store (q,P,p1,p2,A), where A is an ATC r-d-ing the targets
  3.2.) for all (q,P,p,D) calculate prefixes p1 of p and (q',P') such that the target of p1 (from q) and q1 are in D
        \<rightarrow> store (q,P,p1,q',P',A)
  3.3.) for all (q,P) and (q',P') such that q and q' are r-d (better: in some D actually used)
        \<rightarrow> store (q,P,q',P',A)
*)






(* Test cases between two prefixes of some traversal sequence *)
(* Function parameter f is supposed to be a function that assigns state separators to state pairs,
   e.g. f q1 q2 = calculate_state_separator_from_s_states M q1 q2, but using pre-calculated results
        instead of newly calculating calculate_state_separator_from_s_states all the time 
 *)
fun calculate_test_cases_A :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('a,'b) ATC option) \<Rightarrow> ('a,'b) Preamble \<Rightarrow> 'a Traversal_Path \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('a,'b) ATC) list" where
  "calculate_test_cases_A q f P p = concat (map (\<lambda> ppA . [(P,fst (fst ppA), the (snd ppA)), (P,snd (fst ppA), the (snd ppA))])
                                             (filter (\<lambda>ppA . snd ppA \<noteq> None) 
                                                     (map (\<lambda> pp . (pp, f (target (fst pp) q) (target (snd pp) q)))
                                                          (prefix_pairs p))))"

(* TODO: test *)
(* TODO: visualize? *)




fun calculate_test_suite :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> ('a,'b) Test_Case set" 
  where "calculate_test_suite M m = (let MRS = maximal_repetition_sets_from_separators M;
                                         DRP  = set (d_reachable_states_with_preambles M) 
                                     in \<Union> (image (\<lambda> (q,P) . image (\<lambda> tp . (P,tp,M))
                                                                   (set (m_traversal_paths M q MRS m)))
                                                 DRP))"

(*
type_synonym IO_Sequence = "(Input \<times> Output) list"
type_synonym Preamble_Sequence = IO_Sequence
type_synonym Traversal_Sequence = IO_Sequence

(* TODO: naming *)
type_synonym ('a,'b) Test_Case = "(Preamble_Sequence \<times> Traversal_Sequence \<times> ('a,'b) FSM_scheme list)"
type_synonym ('a,'b) Test_Suite = "('a,'b) Test_Case set"
*)







end