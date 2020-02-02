theory Test_Suite_ATC
imports Adaptive_Test_Case State_Preamble Traversal_Set
begin



type_synonym ('a,'b) Preamble = "('a,'b) FSM_scheme"
type_synonym 'a Traversal_Path = "'a Transition list"
(*type_synonym ('a,'b) ATC = "('a \<times> 'a + 'a,'b) FSM_scheme"*)
type_synonym ('a,'b) ATC = "('a,'b) FSM_scheme"

(* problem: ATCs might not exist, preamble and traversal paths still need to be applied *)
type_synonym ('a,'b) Test_Case = "(('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('a,'b) ATC set)"
type_synonym ('a,'b) Test_Suite = "('a,'b) Test_Case set"

(* todo: rename *)
fun get_atc :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a Traversal_Path \<Rightarrow> 'a \<Rightarrow> 'a Traversal_Path \<Rightarrow> (('a \<times> 'a) \<times> ('c,'d) ATC) list \<Rightarrow> ('c,'d) ATC option" where
  "get_atc M q1 p1 q2 p2 dists = (case find (\<lambda> ((q1',q2'),A) . q1' = target p1 q1 \<and> q2' = target p2 q2) dists of
                              Some ((q1'',q2''),A) \<Rightarrow> Some A |
                              None             \<Rightarrow> None)"

(* todo: move *)
lemma r_distinguishable_state_pairs_with_separators_elem_is_separator:
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  and     "observable M"
  and     "completely_specified M"
shows "is_separator M q1 q2 A (Inr q1) (Inr q2)"
proof -
  have *:"q1 \<in> nodes M" and **:"q2 \<in> nodes M" and ***:"q1 \<noteq> q2" and ****: "q2\<noteq>q1" and *****: "calculate_state_separator_from_s_states M q1 q2 = Some A \<or> calculate_state_separator_from_s_states M q2 q1 = Some A"
    using assms(1) unfolding r_distinguishable_state_pairs_with_separators_def by auto

  from ***** have "is_state_separator_from_canonical_separator (canonical_separator M q1 q2) q1 q2 A \<or> is_state_separator_from_canonical_separator (canonical_separator M q2 q1) q2 q1 A"
    using calculate_state_separator_from_s_states_soundness[of M q1 q2 A, OF _ * ** *** \<open>completely_specified M\<close>]
    using calculate_state_separator_from_s_states_soundness[of M q2 q1 A, OF _ ** * **** \<open>completely_specified M\<close>] by auto
  then show ?thesis
    using state_separator_from_canonical_separator_is_separator[of M q1 q2 A, OF _ \<open>observable M\<close> * ** ***] 
    using state_separator_from_canonical_separator_is_separator[of M q2 q1 A, OF _ \<open>observable M\<close> ** * ****] 
    using is_separator_sym[of M q2 q1 A "Inr q2" "Inr q1"] by auto
qed


lemma get_atc_soundness :                           
  assumes "get_atc M q1 p1 q2 p2 (r_distinguishable_state_pairs_with_separators_naive M) = Some A"
  and     "q1 \<in> nodes M"  
  and     "q2 \<in> nodes M"
  and     "path M q1 p1"
  and     "path M q2 p2"
  and     "observable M"
  and     "completely_specified M"
shows "is_separator M (target p1 q1) (target p2 q2) A (Inr (target p1 q1)) (Inr (target p2 q2))"
proof -

  have "find (\<lambda>((q1', q2'), A). q1' = target p1 q1 \<and> q2' = target p2 q2) (r_distinguishable_state_pairs_with_separators_naive M) \<noteq> None"
    using assms(1) unfolding get_atc.simps 
    by (metis option.case_eq_if option.simps(3))
  then obtain q1' q2' where *: "find (\<lambda>((q1', q2'), A). q1' = target p1 q1 \<and> q2' = target p2 q2) (r_distinguishable_state_pairs_with_separators_naive M) = Some ((q1',q2'),A)"
    using assms(1) unfolding get_atc.simps by auto
  have "((target p1 q1, target p2 q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
    using find_condition[OF *] 
    using find_set[OF *] 
    using r_distinguishable_state_pairs_with_separators_code[of M] by auto

  then show ?thesis 
    using r_distinguishable_state_pairs_with_separators_elem_is_separator[OF _ \<open>observable M\<close> \<open>completely_specified M\<close>] by auto
qed


(* TODO: move to Util *)

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






(* functions to create functions that avoid recalculations, possibly incorrect ... *)
fun update_fun_for_list :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times>'b) list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "update_fun_for_list f [] = f" |
  "update_fun_for_list f (x#xs) = update_fun_for_list (f((fst x):=(snd x))) xs"

fun update_fun_for_fun_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "update_fun_for_fun_on f g [] = f" |
  "update_fun_for_fun_on f g (x#xs) = update_fun_for_fun_on (f(x := g x)) g xs" 

value "map (\<lambda>x . x) [1,2,3,4::nat]"
value "map (update_fun_for_list (\<lambda>x . x) [(1,2),(2,7)]) [1,2,3,4::nat]"
value "map (update_fun_for_fun_on (\<lambda>x . x) (\<lambda> x . 7 * x) [2,4]) [1,2,3,4::nat]"

lemma update_fun_for_fun_on_other :
  assumes "x \<notin> set xs"
  shows "(update_fun_for_fun_on f g xs) x = f x"
  using assms by (induction xs arbitrary: f; auto)

lemma update_fun_for_fun_on_some :
  assumes "x \<in> set xs"
  shows "(update_fun_for_fun_on f g xs) x = g x"
using assms proof (induction xs arbitrary: f)
  case Nil
  then show ?case by auto
next
  case (Cons y ys)
  then have "x \<in> set ys \<Longrightarrow> (update_fun_for_fun_on f g (y#ys)) x = g x"
    by auto
  moreover have "x = y \<Longrightarrow> (update_fun_for_fun_on f g (y#ys)) x = g x"
  proof -
    assume "x = y"
    then show "(update_fun_for_fun_on f g (y#ys)) x = g x"
    proof (cases "x \<in> set ys")
      case True
      then show ?thesis using Cons.IH by auto
    next
      case False
      show ?thesis using update_fun_for_fun_on_other[OF False, of f g] \<open>x = y\<close> 
        by (metis calculation fun_upd_apply update_fun_for_fun_on.simps(2) update_fun_for_fun_on_other)
    qed
  qed
  ultimately show ?case using \<open>x : set (y#ys)\<close> by auto
qed


fun list_as_fun :: "('a \<times> 'b) list \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "list_as_fun xs defaultValue = (\<lambda> x . (case find (\<lambda>(a,b) . a = x) xs of Some (a,b) \<Rightarrow> b | None \<Rightarrow> defaultValue))"

fun list_as_fun' :: "('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "list_as_fun' xs = (\<lambda> x . (case find (\<lambda>(a,b) . a = x) xs of Some (a,b) \<Rightarrow> b ))"

value "(list_as_fun' [(1::nat,2::nat)]) 1"


lemma list_as_fun_on :
  assumes "a \<in> set xs"
shows "(list_as_fun (map (\<lambda> x . (x, f x)) xs) y) a = f a"
  using assms by (induction xs; auto)


(*
lemma rdssl_list_as_fun_helper :
  assumes "((q1,q2),A) \<in> set (r_distinguishable_state_pairs_with_separators_naive M)"
  shows "(list_as_fun (r_distinguishable_state_pairs_with_separators_naive M) (THE A. False)) (q1,q2) = A"
proof -
  have "find (\<lambda>(a,b) . a = (q1,q2)) (r_distinguishable_state_pairs_with_separators_naive M) \<noteq> None"
    using assms find_None_iff[of "(\<lambda>(a,b) . a = (q1,q2))" "r_distinguishable_state_pairs_with_separators_naive M"] by auto
  then obtain q1' q2' A' where *:"find (\<lambda>(a,b) . a = (q1,q2)) (r_distinguishable_state_pairs_with_separators_naive M) = Some ((q1',q2'),A')"
    by auto
  
  have "q1' = q1" and "q2' = q2"
    using find_condition[OF *] by auto
  then have "((q1,q2),A') \<in> set (r_distinguishable_state_pairs_with_separators_naive M)"
    using find_set[OF *] by auto
  then have "A' = A"
    using r_distinguishable_state_pairs_with_separators_same_pair_same_separator[of q1 q2 A' M A] assms
    unfolding r_distinguishable_state_pairs_with_separators_code by blast
  then show ?thesis using * by auto
qed
*)




lemma fRD_helper :
  assumes "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
  shows "(\<lambda> q1 q2 . snd (the (find (\<lambda> qqA . fst qqA = (q1,q2)) (r_distinguishable_state_pairs_with_separators_naive M)))) q1 q2 = A"
proof -
  have "\<And> qqA . fst qqA = (q1, q2) \<Longrightarrow> qqA \<in> r_distinguishable_state_pairs_with_separators M \<Longrightarrow> qqA = ((q1,q2),A)"
    using r_distinguishable_state_pairs_with_separators_same_pair_same_separator[OF assms]
    by auto
  
  then have "(find (\<lambda>qqA. fst qqA = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M)) = Some ((q1,q2),A)"
    
    using find_None_iff[of "(\<lambda>qqA. fst qqA = (q1, q2))" "r_distinguishable_state_pairs_with_separators_naive M"]
    using assms
  proof -
    have f1: "find (\<lambda>p. fst p = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M) = Some (the (find (\<lambda>p. fst p = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M)))"
      by (metis \<open>((q1, q2), A) \<in> r_distinguishable_state_pairs_with_separators M\<close> \<open>(find (\<lambda>qqA. fst qqA = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M) = None) = (\<nexists>x. x \<in> set (r_distinguishable_state_pairs_with_separators_naive M) \<and> fst x = (q1, q2))\<close> fst_conv option.exhaust_sel r_distinguishable_state_pairs_with_separators_code)
    then have f2: "fst (the (find (\<lambda>p. fst p = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M))) = (q1, q2)"
      by (meson find_condition)
    have "the (find (\<lambda>p. fst p = (q1, q2)) (r_distinguishable_state_pairs_with_separators_naive M)) \<in> r_distinguishable_state_pairs_with_separators M"
      using f1 by (simp add: find_set r_distinguishable_state_pairs_with_separators_code)
    then show ?thesis
      using f2 f1 \<open>\<And>qqA. \<lbrakk>fst qqA = (q1, q2); qqA \<in> r_distinguishable_state_pairs_with_separators M\<rbrakk> \<Longrightarrow> qqA = ((q1, q2), A)\<close> by presburger
  qed  

  then show ?thesis by auto
qed

(*
lemma fTP_helper :
  fixes m :: nat
  assumes "q \<in> set (map fst (d_reachable_states_with_preambles M))"
  shows "True"
proof -
  note list_as_fun_on[OF assms, of "\<lambda> q . m_traversal_paths_with_witness M q (map (\<lambda>S. (S, S \<inter> set (map fst (d_reachable_states_with_preambles M)))) (filter (\<lambda> S . \<not>(\<exists> S' \<in> set (filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> (image fst (set (r_distinguishable_state_pairs_with_separators_naive M)))) (map set (pow_list (nodes_from_distinct_paths M)))) . S \<subset> S')) (filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> (image fst (set (r_distinguishable_state_pairs_with_separators_naive M)))) (map set (pow_list (nodes_from_distinct_paths M)))))) m" "[]" ]
  *)
  
(* Test cases between two prefixes of some traversal sequence *)
(* Assumes that states in rd are pairwise r-d and uses fRD to retrieve a separator *)
fun calculate_test_case_for_prefixes :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> 'a Traversal_Path \<Rightarrow> ('a set \<times> 'a set) \<Rightarrow> (('a Traversal_Path \<times> 'a Traversal_Path) \<times> ('c,'d) ATC) list" where
  "calculate_test_case_for_prefixes q fRD p (rd,dr) = (map (\<lambda> (p1,p2) . ((p1,p2), fRD (target p1 q) (target p2 q)))      \<comment> \<open>retrieve separator using fRD\<close>
                                                 (filter (\<lambda> (p1,p2) . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd) \<comment> \<open>ensure that a separator exists, assuming that the states in rd are pairwise r-d\<close>
                                                         (prefix_pairs p)))"

fun calculate_test_cases_for_prefixes :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> ('a Traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) list" where
  "calculate_test_cases_for_prefixes q P fRD pds = concat (map (\<lambda> (p,d) . concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p d))) pds)"


lemma calculate_test_case_for_prefixes_set :
  "set (calculate_test_case_for_prefixes q fRD p (rd,dr)) = {((p1,p2), fRD (target p1 q) (target p2 q)) | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}"
proof -
  have "set (prefix_pairs p) = {(p1, p2) | p1 p2 . \<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> []}"
    using prefix_pairs_set[of p] by assumption
  then have "set (filter (\<lambda> (p1,p2) . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd) (prefix_pairs p)) =  {(p1, p2) | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}"
    by fastforce
  moreover have "image (\<lambda> (p1,p2) . ((p1,p2), fRD (target p1 q) (target p2 q))) {(p1, p2) | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])} = {((p1,p2), fRD (target p1 q) (target p2 q)) | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}"
    by fast
  ultimately show ?thesis unfolding calculate_test_case_for_prefixes.simps by force
qed

(*
lemma calculate_test_cases_for_prefixes_set :
  "set (calculate_test_cases_for_prefixes q P fRD pds) = (\<Union> (p,d) \<in> set pds . (\<Union> {{(P,p1,fRD (target p1 q) (target p2 q)),(P,p2,fRD (target p1 q) (target p2 q))} | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> []) }))"
proof -
  thm concat_map_elem
  
  have scheme : "\<And> f xs . set (concat (map f xs)) = \<Union>(image (set o f) (set xs))" by auto

  have "\<And> p rd dr . set (calculate_test_case_for_prefixes q fRD p (rd,dr)) = {((p1,p2), fRD (target p1 q) (target p2 q)) | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}"
    using calculate_test_case_for_prefixes_set[of q fRD] by blast
  
  have "\<And> p rd dr . set (concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p (rd,dr)))) = \<Union> (image (\<lambda>((p1,p2),A) . set [(P,p1,A),(P,p2,A)]) (set (calculate_test_case_for_prefixes q fRD p (rd,dr))))"
  proof - 
    fix p rd dr

    have "UNION
   {((p1, p2), fRD (target p1 q) (target p2 q)) |p1 p2. target p1 q \<in> rd \<and> target p2 q \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}
   (set \<circ> (\<lambda>((p1, p2), A). [(P, p1, A), (P, p2, A)])) = (\<Union>((p1, p2), A)\<in>set (calculate_test_case_for_prefixes q fRD p (rd, dr)). set [(P, p1, A), (P, p2, A)])" 
      unfolding calculate_test_case_for_prefixes_set[of q fRD p rd dr]
    proof -
      { fix pp :: "(('a \<times> integer \<times> integer \<times> 'a) list \<times> ('a \<times> integer \<times> integer \<times> 'a) list) \<times> ('c, 'd) FSM_scheme"
        have "UNION {((ps, psa), fRD (target ps q) (target psa q)) |ps psa. target ps q \<in> rd \<and> target psa q \<in> rd \<and> (\<exists>psaa psaaa. ps @ psaa = psa \<and> psa @ psaaa = p \<and> psaa \<noteq> [])} (set \<circ> (\<lambda>((ps, psa), f). [(P, ps, f), (P, psa, f)])) = (\<Union>((ps, psa), f)\<in>{((ps, psa), fRD (target ps q) (target psa q)) |ps psa. target ps q \<in> rd \<and> target psa q \<in> rd \<and> (\<exists>psaa psaaa. ps @ psaa = psa \<and> psa @ psaaa = p \<and> psaa \<noteq> [])}. set [(P, ps, f), (P, psa, f)]) \<or> (set \<circ> (\<lambda>((ps, psa), f). [(P, ps, f), (P, psa, f)])) pp = (case pp of (x, xa) \<Rightarrow> (case x of (ps, psa) \<Rightarrow> \<lambda>f. set [(P, ps, f), (P, psa, f)]) xa)"
          by fastforce }
      then show "UNION {((ps, psa), fRD (target ps q) (target psa q)) |ps psa. target ps q \<in> rd \<and> target psa q \<in> rd \<and> (\<exists>psb psc. ps @ psb = psa \<and> psa @ psc = p \<and> psb \<noteq> [])} (set \<circ> (\<lambda>((psa, ps), f). [(P, psa, f), (P, ps, f)])) = (\<Union>((psa, ps), f)\<in>{((ps, psa), fRD (target ps q) (target psa q)) |ps psa. target ps q \<in> rd \<and> target psa q \<in> rd \<and> (\<exists>psb psc. ps @ psb = psa \<and> psa @ psc = p \<and> psb \<noteq> [])}. set [(P, psa, f), (P, ps, f)])"
        by meson
    qed 


    then show "set (concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p (rd,dr)))) = \<Union> (image (\<lambda>((p1,p2),A) . set [(P,p1,A),(P,p2,A)]) (set (calculate_test_case_for_prefixes q fRD p (rd,dr))))"
      using scheme[of "(\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)])" "calculate_test_case_for_prefixes q fRD p (rd,dr)"] 
      unfolding calculate_test_case_for_prefixes_set[of q fRD p rd dr] by force
  qed
  then have "\<And> p rd dr . set (concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p (rd,dr)))) = \<Union> (image (\<lambda>((p1,p2),A) . {(P,p1,A),(P,p2,A)}) (set (calculate_test_case_for_prefixes q fRD p (rd,dr))))"
    by simp
  then have "set (map (\<lambda> (p,d) . concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p d))) pds) = {\<Union> (image (\<lambda>((p1,p2),A) . {(P,p1,A),(P,p2,A)}) (set (calculate_test_case_for_prefixes q fRD p (rd,dr)))) | p rd dr . (p,(rd,dr)) \<in> set pds}"

  ultimately show ?thesis

  then have "\<And> p rd dr . set (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p (rd,dr))) = {[(P, p1, fRD (target p1 q) (target p2 q)), (P, p2, fRD (target p1 q) (target p2 q))] | p1 p2 . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (\<exists>p' p''. p1 @ p' = p2 \<and> p2 @ p'' = p \<and> p' \<noteq> [])}"
        
  define xs1 where "xs1 = concat (map (\<lambda>((p1,p2),A) . [(P,p1,A),(P,p2,A)]) (calculate_test_case_for_prefixes q fRD p d))"
  unfolding calculate_test_cases_for_prefixes.simps
  using calculate_test_case_for_prefixes_set 

*)





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



subsubsection "Calculating Tests along m-Traversal-Paths"

fun prefix_pair_tests'' :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> 'a Traversal_Path \<times> ('a set \<times> 'a set) \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) list list" where
  "prefix_pair_tests'' q P fRD (p, (rd,dr)) = (map (\<lambda> (p1,p2) . [(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))])      \<comment> \<open>retrieve separator using fRD\<close>
                                                 (filter (\<lambda> (p1,p2) . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)) \<comment> \<open>ensure that a separator exists, assuming that the states in rd are pairwise r-d\<close>
                                                         (prefix_pairs p)))"

lemma prefix_pair_tests''_set : 
  "set (prefix_pair_tests'' q P fRD (p, (rd,dr))) = {[(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))] | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}"
proof -

  have scheme: "\<And> S f P . image f {(p1,p2) | p1 p2 . P p1 p2} = {f (p1,p2) | p1 p2 . P p1 p2}" by auto

  have "set (filter (\<lambda> (p1,p2) . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)) (prefix_pairs p)) = {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}"
    by auto
  moreover have "set (prefix_pair_tests'' q P fRD (p, (rd,dr))) = image (\<lambda> (p1,p2) . [(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))]) (set (filter (\<lambda> (p1,p2) . (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)) (prefix_pairs p)))"
    by auto
  ultimately have "set (prefix_pair_tests'' q P fRD (p, (rd,dr))) = image (\<lambda> (p1,p2) . [(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))]) {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}"
    by auto
  moreover have "image (\<lambda> (p1,p2) . [(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))]) {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)} = {[(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))] | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}"
    using scheme[of "(\<lambda> (p1,p2) . [(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))])" "\<lambda> p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)"] by auto
  ultimately show ?thesis by force
qed


fun prefix_pair_tests' :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> ('a Traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) list" where
  "prefix_pair_tests' q P fRD pds = concat (concat (map (prefix_pair_tests'' q P fRD) pds))"


fun prefix_pair_tests :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> ('a Traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) set" where
  "prefix_pair_tests q P fRD pds = \<Union>{{(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))} | p1 p2 . \<exists> (p,(rd,dr)) \<in> set pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}"

lemma prefix_pair_tests_containment :
  assumes "(p,(rd,dr)) \<in> set pds"
  and     "(p1,p2) \<in> set (prefix_pairs p)"
  and     "(target p1 q) \<in> rd"
  and     "(target p2 q) \<in> rd"
  and     "(target p1 q) \<noteq> (target p2 q)"
shows "(P,p1,fRD (target p1 q) (target p2 q)) \<in> prefix_pair_tests q P fRD pds"
and   "(P,p1,fRD (target p1 q) (target p2 q)) \<in> prefix_pair_tests q P fRD pds"
  using assms unfolding prefix_pair_tests.simps by blast+

(* TODO: move and rename *)
lemma union_pair_exists_helper : "\<And> x xs f P . \<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set (x#xs) . P y1 y2 z} = (\<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> (\<Union>{f y1 y2 | y1 y2 . P y1 y2 x})"
proof -
  have "\<And> x xs f P . {f y1 y2 | y1 y2 . \<exists> z \<in> set (x#xs) . P y1 y2 z} = ({f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> ({f y1 y2 | y1 y2 . P y1 y2 x})" by auto
  then have "\<And> x xs f P . \<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set (x#xs) . P y1 y2 z} = \<Union>(({f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> ({f y1 y2 | y1 y2 . P y1 y2 x}))" by metis
  moreover have "\<And> x xs f P . (\<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> (\<Union>{f y1 y2 | y1 y2 . P y1 y2 x}) = \<Union>(({f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> ({f y1 y2 | y1 y2 . P y1 y2 x}))"
    by auto
  ultimately show "\<And> x xs f P . \<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set (x#xs) . P y1 y2 z} = (\<Union>{f y1 y2 | y1 y2 . \<exists> z \<in> set xs . P y1 y2 z}) \<union> (\<Union>{f y1 y2 | y1 y2 . P y1 y2 x})" by metis
qed



lemma prefix_pair_tests_code[code] :
  "prefix_pair_tests q P fRD pds = set (prefix_pair_tests' q P fRD pds)"
  unfolding prefix_pair_tests'.simps
proof (induction pds)
  case Nil
  then show ?case by auto
next
  case (Cons a pds)
  obtain p rd dr where "a = (p,(rd,dr))"
    using prod_cases3 by blast 

  have "prefix_pair_tests q P fRD ((p,(rd,dr))#pds) = (prefix_pair_tests q P fRD pds) \<union> (\<Union>{{(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)})"
    using union_pair_exists_helper[of "\<lambda> p1 p2 . {(P, p1, fRD (target p1 q) (target p2 q)), (P, p2, fRD (target p1 q) (target p2 q))}" "(p,(rd,dr))" pds "\<lambda> p1 p2 (p,(rd,dr)) . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)"]
    unfolding prefix_pair_tests.simps by force

  moreover have "\<Union> (set (map set (concat (map (prefix_pair_tests'' q P fRD) ((p,(rd,dr))#pds))))) = (\<Union> (set (map set (concat (map (prefix_pair_tests'' q P fRD) pds))))) \<union> (\<Union> (set (map set (prefix_pair_tests'' q P fRD (p,(rd,dr))))))"
    by auto


  
  moreover have "(\<Union>{{(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)}) = (\<Union> (set (map set (prefix_pair_tests'' q P fRD (p,(rd,dr))))))"
  proof -
    have scheme1 : "\<And> xs . set (map set xs) = image set (set xs)" by auto
    have scheme2 : "\<And> f xs P . {set (f x1 x2) | x1 x2 . P x1 x2} = image set {f x1 x2 | x1 x2 . P x1 x2}" by auto

    have "{{(P,p1,fRD (target p1 q) (target p2 q)), (P,p2,fRD (target p1 q) (target p2 q))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)} = (set (map set (prefix_pair_tests'' q P fRD (p,(rd,dr)))))"
      unfolding scheme1
      unfolding prefix_pair_tests''_set[of q P fRD p rd dr] 
      using scheme2[of "\<lambda> p1 p2 . [(P, p1, fRD (target p1 q) (target p2 q)), (P, p2, fRD (target p1 q) (target p2 q))]" "\<lambda> p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target p1 q) \<in> rd \<and> (target p2 q) \<in> rd \<and> (target p1 q) \<noteq> (target p2 q)"] by force
    then show ?thesis by force
  qed

  ultimately show ?case 
    using Cons.IH unfolding \<open>a = (p,(rd,dr))\<close> by force
qed
 


subsubsection "Calculating Tests between Preambles"


fun preamble_prefix_tests' :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> ('a Traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> ('a \<times> ('a,'b) Preamble) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) list" where
  "preamble_prefix_tests' q P fRD pds PS = 
    concat (map (\<lambda>((p,(rd,dr)),(q2,P2),p1) . [(P,p1,fRD (target p1 q) q2), (P2,[],fRD (target p1 q) q2)]) 
                (filter (\<lambda>((p,(rd,dr)),(q2,P2),p1) . (target p1 q) \<in> rd \<and> q2 \<in> rd \<and> (target p1 q) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),(q2,P2)) . map (\<lambda>p1 . ((p,(rd,dr)),(q2,P2),p1)) (prefixes p)) (cartesian_product_list pds PS)))))"


fun preamble_prefix_tests :: "'a \<Rightarrow> ('a,'b) Preamble \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('c,'d) ATC) \<Rightarrow> ('a Traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> ('a \<times> ('a,'b) Preamble) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) set" where
  "preamble_prefix_tests q P fRD pds PS = \<Union>{{(P,p1,fRD (target p1 q) q2), (P2,[],fRD (target p1 q) q2)} | p1 q2 P2 . \<exists> (p,(rd,dr)) \<in> set pds . \<exists> (q2,P2) \<in> set PS . \<exists> p2 . p = p1@p2 \<and> (target p1 q) \<in> rd \<and> q2 \<in> rd \<and> (target p1 q) \<noteq> q2}"


(* TODO: code 
lemma preamble_prefix_tests_code[code]:
  "preamble_prefix_tests q P fRD pds PS = set (preamble_prefix_tests' q P fRD pds PS)"
  sorry
*)


subsubsection "Calculating Tests between m-Traversal-Paths Prefixes and Preambles"

fun preamble_pair_tests' :: "('a \<times> ('a,'b) Preamble) list \<Rightarrow> (('a \<times> 'a) \<times> ('c,'d) ATC) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) list" where
  "preamble_pair_tests' PS RDS = 
    concat (map (\<lambda>((q1,P1),(q2,P2)) . (case (find (\<lambda> qqA . fst qqA = (q1,q2)) RDS) of 
                                         Some ((q1',q2'),A) \<Rightarrow> [(P1,[],A),(P2,[],A)] |
                                         None \<Rightarrow> []))
           (cartesian_product_list PS PS))"

fun preamble_pair_tests :: "('a \<times> ('a,'b) Preamble) list \<Rightarrow> (('a \<times> 'a) \<times> ('c,'d) ATC) list \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC) set" where
  "preamble_pair_tests PS RDS = \<Union>{{(P1,[],A),(P2,[],A)} | P1 P2 A . \<exists> q1 q2 . (q1,P1) \<in> set PS \<and> (q2,P2) \<in> set PS \<and> ((q1,q2),A) \<in> set RDS}"

(* TODO: code 
lemma preamble_pair_tests_code[code]:
  "preamble_pair_tests PS RDS = set (preamble_pair_tests' PS RDS)"
  sorry
*)



subsubsection "Collecting Tests"


fun collect_ATCs' :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a \<times> 'b \<times> ('c set)) list" where
  "collect_ATCs' [] ts = []" |
  "collect_ATCs' ((a,b)#xs) ts = (a,b, set (map (\<lambda>(x,y,c) . c) (filter (\<lambda>(x,y,c) . x = a \<and> y = b) ts))) # (collect_ATCs' xs ts)"

value "collect_ATCs' [(1::nat,2::nat),(1,3),(2,3)] [(1,2,1::nat),(1,2,2),(1,2,6),(1,3,5),(1,3,6),(2,3,1)]"

lemma collect_ATCs'_set :
  "set (collect_ATCs' xs ts) = {(a,b,{c . (a,b,c) \<in> set ts}) | a b . (a,b) \<in> set xs}"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  obtain a b where "x=(a,b)" 
    by (meson surj_pair)
  have "(a,b, set (map (\<lambda>(x,y,c) . c) (filter (\<lambda>(x,y,c) . x = a \<and> y = b) ts))) = (a,b,{c . (a,b,c) \<in> set ts})" 
    by force
  moreover have "set (collect_ATCs' ((a,b)#xs) ts) = insert (a,b, set (map (\<lambda>(x,y,c) . c) (filter (\<lambda>(x,y,c) . x = a \<and> y = b) ts))) (set (collect_ATCs' xs ts))"
    by auto
  moreover have "{(a',b',{c . (a',b',c) \<in> set ts}) | a' b' . (a',b') \<in> set ((a,b)#xs)} = insert (a,b,{c . (a,b,c) \<in> set ts}) {(a',b',{c . (a',b',c) \<in> set ts}) | a' b' . (a',b') \<in> set xs}"
    by auto
  ultimately show ?case using Cons.IH unfolding \<open>x=(a,b)\<close> by auto
qed 



fun collect_ATCs :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a \<times> 'b \<times> ('c set)) list" where
  "collect_ATCs xs ts = collect_ATCs' (remdups xs) (remdups ts)"



lemma collect_ATCs_set :
  "set (collect_ATCs xs ts) = {(a,b,{c . (a,b,c) \<in> set ts}) | a b . (a,b) \<in> set xs}"
  using collect_ATCs'_set[of "remdups xs" "remdups ts"] 
  unfolding collect_ATCs.simps set_remdups by assumption




definition calculate_test_suite' :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC set) list" where
  "calculate_test_suite' M m = 
    (let 
         RDSSL \<comment> \<open>R-D States with Separators\<close>
              = r_distinguishable_state_pairs_with_separators_naive M;
         RDSS \<comment> \<open>R-D States with Separators\<close>
              = set RDSSL; \<comment> \<open>corresponds to r_distinguishable_state_pairs_with_separators\<close>
         RDS  \<comment> \<open>R-D States\<close>
              = image fst RDSS;
         RDP  \<comment> \<open>R-D Pairs\<close>
              = filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> RDS) (map set (pow_list (nodes_from_distinct_paths M))); \<comment> \<open>corresponds to pairwise_r_distinguishable_state_sets_from_separators\<close>
         MPRD \<comment> \<open>Maximal Pairwise R-D sets\<close>
              = filter (\<lambda> S . \<not>(\<exists> S' \<in> set RDP . S \<subset> S')) RDP;  \<comment> \<open>corresponds to maximal_pairwise_r_distinguishable_state_sets_from_separators\<close>
         DRSP \<comment> \<open>D-R States with Preambles\<close>
              = d_reachable_states_with_preambles M;
         DRS  \<comment> \<open>D-R States\<close>
              = map fst DRSP; \<comment> \<open>corresponds to d_reachable_states\<close>
         MRS  \<comment> \<open>Maximal Repetition sets (maximal pairwise r-d sets with their d-r subsets)\<close>
              = map (\<lambda>S. (S, S \<inter> set DRS)) MPRD; \<comment> \<open>corresponds to maximal_repetition_sets_from_separators\<close>
         MTP  \<comment> \<open>states and their outgoing m-Traversal Paths\<close>
              = map (\<lambda> q . (q,m_traversal_paths_with_witness M q MRS m)) DRS;
         fTP  \<comment> \<open>function to get Traversal Paths with witnesses for states\<close>
              = list_as_fun MTP []; \<comment> \<open>see list_as_fun_on and the sketch following fRD_helper\<close>
         fRD  \<comment> \<open>function to get separators for R-D states\<close>
              = \<lambda> q1 q2 . snd (the (find (\<lambda> qqA . fst qqA = (q1,q2)) RDSSL)); \<comment> \<open>see fRD_helper\<close>
         PMTP 
              = concat (map (\<lambda> (q,P) . map (\<lambda>(p,d) . (P,p)) (fTP q)) DRSP);
         PrefixPairTests 
              = concat (map (\<lambda> (q,P) . prefix_pair_tests' q P fRD (fTP q)) DRSP);
              \<comment> \<open>= \<Union> (image (\<lambda> (q,P) . prefix_pair_tests q P fRD (fTP q)) (set DRSP));\<close>
         PreamblePrefixTests
              = concat (map (\<lambda> (q,P) . preamble_prefix_tests' q P fRD (fTP q) DRSP) DRSP);
              \<comment> \<open>= \<Union> (image (\<lambda> (q,P) . preamble_prefix_tests q P fRD (fTP q) DRSP) (set DRSP));\<close>
         PreamblePairTests
              = preamble_pair_tests' DRSP RDSSL
      
    in collect_ATCs PMTP (PrefixPairTests @ PreamblePrefixTests @ PreamblePairTests))"


value "calculate_test_suite' M_ex_H 4"








end (*


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