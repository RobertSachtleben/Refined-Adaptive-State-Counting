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

lemma list_as_fun_on :
  assumes "a \<in> set xs"
shows "(list_as_fun (map (\<lambda> x . (x, f x)) xs) y) a = f a"
  using assms by (induction xs; auto)



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



fun calculate_test_suite' :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> (('a,'b) Preamble \<times> 'a Traversal_Path \<times> ('c,'d) ATC set) set" where
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
              = (map fst DRSP); \<comment> \<open>corresponds to d_reachable_states\<close>
         MRS  \<comment> \<open>Maximal Repetition sets (maximal pairwise r-d sets with their d-r subsets\<close>
              = map (\<lambda>S. (S, S \<inter> set DRS)) MPRD; \<comment> \<open>coresponds to maximal_repetition_sets_from_separators\<close>
         MTP  \<comment> \<open>states and their outgoing m-Traversal Paths\<close>
              = map (\<lambda> q . (q,m_traversal_paths_with_witness M q MRS m)) (nodes_from_distinct_paths M);
         fTP  \<comment> \<open>function to get Traversal Paths\<close>
              = list_as_fun MTP [];
         fRD  \<comment> \<open>function to get separators for R-D states\<close>
              = list_as_fun RDSSL (THE A . False) \<comment> \<open>verify usage, see rdssl_list_as_fun_helper, possibly weaken assumption of that lemma\<close>
      in {})"





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