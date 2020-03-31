theory Test_Suite
imports Helper_Algorithms Adaptive_Test_Case
begin

section \<open>Test Suites\<close>

subsection \<open>Preliminary Definitions\<close>


type_synonym ('a,'b,'c) preamble = "('a,'b,'c) fsm"
type_synonym ('a,'b,'c) traversal_Path = "('a \<times> 'b \<times> 'c \<times> 'a) list"
type_synonym ('a,'b,'c) atc = "('a,'b,'c) fsm"

(* path with initial state and a state to r-d the target from *)
type_synonym ('a,'b,'c) test_path = "('a \<times> ('a,'b,'c) traversal_Path \<times> 'a)"





(* TODO: review Petrenko/Yevtushenko *)

(* rework sketch:
  1.) calculate d-r states with preambles (set DR of (q,P))
  2.) calculate traversal sequences from d-r states (set DRT of (q,p,D) where D is the set satisfying the abortion criterion)
  3.1.) for all (q,p,D) calculate prefixes p1 < p2 of p s.t. their targets (from q) are in D
        \<rightarrow> store (q,p1,p2,A), where A is an ATC r-d-ing the targets
  3.2.) for all (q,p,D) calculate prefixes p1 of p and (q',P') such that the target of p1 (from q) and q1 are in D
        \<rightarrow> store (q,p1,q',P',A)
  3.3.) for all (q,P) and (q',P') such that q and q' are r-d (better: in some D actually used)
        \<rightarrow> store (q,P,q',P',A)
*)



subsubsection "Calculating Tests along m-Traversal-Paths"



fun prefix_pair_tests'' :: "'a \<Rightarrow> ('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set) \<Rightarrow> ('a,'b,'c) test_path list list" where
  "prefix_pair_tests'' q (p, (rd,dr)) = (map (\<lambda> (p1,p2) . [(q,p1, (target q p2)), (q,p2, (target q p1))])      
                                                 (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) \<comment> \<open>ensure that a separator exists, assuming that the states in rd are pairwise r-d\<close>
                                                         (prefix_pairs p)))"

lemma prefix_pair_tests''_set : 
  "set (prefix_pair_tests'' q (p, (rd,dr))) = {[(q,p1,(target q p2)), (q,p2,(target q p1))] | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
  
proof -

  have scheme: "\<And> S f P . image f {(p1,p2) | p1 p2 . P p1 p2} = {f (p1,p2) | p1 p2 . P p1 p2}" by auto

  have "set (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)) = {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
    by auto
  moreover have "set (prefix_pair_tests'' q (p, (rd,dr))) = image (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (set (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))"
    by auto
  ultimately have "set (prefix_pair_tests'' q (p, (rd,dr))) = image (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
    by auto
  moreover have "image (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) {(p1,p2) | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)} = {[(q,p1,(target q p2)), (q,p2,(target q p1))] | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
    using scheme[of "(\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))])" "\<lambda> p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"] by auto
  ultimately show ?thesis by force
qed


fun prefix_pair_tests' :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> ('a,'b,'c) test_path list" where
  "prefix_pair_tests' q pds = concat (concat (map (prefix_pair_tests'' q) pds))"


fun prefix_pair_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> ('a,'b,'c) test_path set" where
  "prefix_pair_tests q pds = \<Union>{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . \<exists> (p,(rd,dr)) \<in> set pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"

lemma prefix_pair_tests_containment :
  assumes "(p,(rd,dr)) \<in> set pds"
  and     "(p1,p2) \<in> set (prefix_pairs p)"
  and     "(target q p1) \<in> rd"
  and     "(target q p2) \<in> rd"
  and     "(target q p1) \<noteq> (target q p2)"
shows "(q,p1,(target q p2)) \<in> prefix_pair_tests q pds"
and   "(q,p2,(target q p1)) \<in> prefix_pair_tests q pds"
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
  "prefix_pair_tests q pds = set (prefix_pair_tests' q pds)"
  unfolding prefix_pair_tests'.simps
proof (induction pds)
  case Nil
  then show ?case by auto
next
  case (Cons a pds)
  obtain p rd dr where "a = (p,(rd,dr))"
    using prod_cases3 by blast 

  have "prefix_pair_tests q ((p,(rd,dr))#pds) = (prefix_pair_tests q pds) \<union> (\<Union>{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)})"
    using union_pair_exists_helper[of "\<lambda> p1 p2 . {(q,p1,(target q p2)), (q,p2,(target q p1))}" "(p,(rd,dr))" pds "\<lambda> p1 p2 (p,(rd,dr)) . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"]
    unfolding prefix_pair_tests.simps by force

  moreover have "\<Union> (set (map set (concat (map (prefix_pair_tests'' q) ((p,(rd,dr))#pds))))) = (\<Union> (set (map set (concat (map (prefix_pair_tests'' q) pds))))) \<union> (\<Union> (set (map set (prefix_pair_tests'' q (p,(rd,dr))))))"
    by auto


  
  moreover have "(\<Union>{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}) = (\<Union> (set (map set (prefix_pair_tests'' q (p,(rd,dr))))))"
  proof -
    have scheme1 : "\<And> xs . set (map set xs) = image set (set xs)" by auto
    have scheme2 : "\<And> f xs P . {set (f x1 x2) | x1 x2 . P x1 x2} = image set {f x1 x2 | x1 x2 . P x1 x2}" by auto

    have "{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)} = (set (map set (prefix_pair_tests'' q (p,(rd,dr)))))"
      unfolding scheme1
      unfolding prefix_pair_tests''_set[of q p rd dr] 
      using scheme2[of "\<lambda> p1 p2 . [(q,p1,(target q p2)), (q,p2,(target q p1))]" "\<lambda> p1 p2 . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"] by force
    then show ?thesis by force
  qed

  ultimately show ?case 
    using Cons.IH unfolding \<open>a = (p,(rd,dr))\<close> by force
qed
 


subsubsection "Calculating Tests between Preambles"



fun preamble_prefix_tests' :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> 'a list \<Rightarrow> ('a,'b,'c) test_path list" where
  "preamble_prefix_tests' q pds drs = 
    concat (map (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) 
                (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))))"


definition preamble_prefix_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> 'a set \<Rightarrow> ('a,'b,'c) test_path set" where
  "preamble_prefix_tests q pds drs = \<Union>{{(q,p1,q2), (q2,[],(target q p1))} | p1 q2 . \<exists> (p,(rd,dr)) \<in> set pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2}"



lemma set_concat_elem :
  assumes "x \<in> set (concat xss)"
  obtains xs where "xs \<in> set xss" and "x \<in> set xs" 
  using assms by auto

lemma set_map_elem :
  assumes "y \<in> set (map f xs)"
  obtains x where "y = f x" and "x \<in> set xs" using assms by auto



lemma preamble_prefix_tests'_set:
  "set (preamble_prefix_tests' q pds drs) = preamble_prefix_tests q pds (set drs)"
proof -
  have "\<And> tp . tp \<in> set (preamble_prefix_tests' q pds drs) \<Longrightarrow> tp \<in> preamble_prefix_tests q pds (set drs)"
  proof -
    fix tp assume "tp \<in> set (preamble_prefix_tests' q pds drs)"
    then obtain tpl where *: "tpl \<in> set (map (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) 
                (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))))"
                    and   "tp \<in> set tpl" 
      using set_concat_elem[of tp] unfolding preamble_prefix_tests'.simps by blast
    
    obtain tpp where "tpl = (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) tpp"
                 and **: "tpp \<in> set (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs))))"  
      using set_map_elem[OF *]
      by blast 

    then obtain p rd dr q2 p1 where "tpp = ((p,(rd,dr)),q2,p1)" 
      by auto

    have "(target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
    and  ***: "((p,(rd,dr)),q2,p1) \<in> set (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))"
      using ** unfolding \<open>tpp = ((p,(rd,dr)),q2,p1)\<close> by auto

    have "(p,(rd,dr)) \<in> set pds"
    and  "q2 \<in> set drs"
    and  "p1 \<in> set (prefixes p)"
      using *** cartesian_product_list_set[of pds drs] by auto

    then have "\<exists>(p, rd, dr)\<in>set pds. q2\<in>set drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2"
      using \<open>(target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2\<close> unfolding prefixes_set
      by blast
    then have "{(q,p1,q2), (q2,[],(target q p1))} \<in> {{(q, p1, q2), (q2, [], target q p1)} |p1 q2.
             \<exists>(p, rd, dr)\<in>set pds. q2\<in>set drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2}" by blast
    moreover have "tp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
      using \<open>tp \<in> set tpl\<close> 
      unfolding \<open>tpl = (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) tpp\<close> \<open>tpp = ((p,(rd,dr)),q2,p1)\<close> by auto
    ultimately show "tp \<in> preamble_prefix_tests q pds (set drs)"
      unfolding  preamble_prefix_tests_def
      by (meson UnionI) 
  qed
  moreover have "\<And> tp . tp \<in> preamble_prefix_tests q pds (set drs) \<Longrightarrow> tp \<in> set (preamble_prefix_tests' q pds drs)"
  proof -
    fix tp assume "tp \<in> preamble_prefix_tests q pds (set drs)"
    then obtain q2 p1 where "tp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
                      and *: "\<exists> (p,(rd,dr)) \<in> set pds . q2 \<in> set drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      unfolding preamble_prefix_tests_def
      by blast


    have "tp \<in> set [(q, p1, q2), (q2, [], target q p1)]"
      using \<open>tp \<in> {(q, p1, q2), (q2, [], target q p1)}\<close> by auto

    from * obtain p rd dr where "(p, rd, dr)\<in>set pds" and "q2\<in>set drs" and "\<exists>p2. p = p1 @ p2" and "target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2"
      using * by auto

    have scheme : "\<And> y x xs . y \<in> set x \<Longrightarrow> x \<in> set xs \<Longrightarrow> y \<in> set (concat xs)" by auto

    have "p1 \<in> set (prefixes p)"
      using \<open>\<exists>p2. p = p1 @ p2\<close> unfolding prefixes_set by blast
    then have "((p,(rd,dr)),q2,p1) \<in> set (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))"
      using \<open>(p, rd, dr)\<in>set pds\<close> \<open>q2\<in>set drs\<close> cartesian_product_list_set[of pds drs] by force
    then have "((p,(rd,dr)),q2,p1) \<in> set (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs))))"
      using \<open>target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2\<close> by auto
    then have **: "[(q, p1, q2), (q2, [], target q p1)] \<in> set (map (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) 
                (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))))"
      by force
    
    show "tp \<in> set (preamble_prefix_tests' q pds drs)"
      using scheme[OF \<open>tp \<in> set [(q, p1, q2), (q2, [], target q p1)]\<close> **]
      unfolding preamble_prefix_tests'.simps  by assumption
  qed
  ultimately show ?thesis by blast
qed
    

(*
lemma preamble_prefix_tests_code[code]:
  "preamble_prefix_tests q pds drs = set (preamble_prefix_tests' q pds (sorted_list_of_set drs))"
  using preamble_prefix_tests'_set 
*)






subsubsection "Calculating Tests between m-Traversal-Paths Prefixes and Preambles"

fun preamble_pair_tests' :: "'a list \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a,'b,'c) test_path list" where
  "preamble_pair_tests' drs rds = map (\<lambda>(q1,q2) . (q1,[],q2)) (filter (\<lambda> qq . qq \<in> rds) (cartesian_product_list drs drs))"

fun preamble_pair_tests :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a,'b,'c) test_path set" where
  "preamble_pair_tests drs rds = image (\<lambda> (q1,q2) . (q1,[],q2)) ((drs \<times> drs) \<inter> rds)"





subsubsection "Collecting Tests"




(* Currently disabled.
   TODO: Decide at which point after/during test_path collection is is most appropriate to convert
         from test_paths that store a single state to r-d from to test suite elements that store a
         path and all states its target is to be r-d'd from.
         Also decide whether this is necessary at all.
*)

(*
fun collect_ATCs' :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'd) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> ('d set)) list" where
  "collect_ATCs' [] ts = []" |
  "collect_ATCs' ((a,b,c)#xs) ts = (a,b,c, set (map (\<lambda>(x,y,z,d) . d) (filter (\<lambda>(x,y,z,d) . x = a \<and> y = b \<and> z = c) ts))) # (collect_ATCs' xs ts)"



lemma collect_ATCs'_set :
  "set (collect_ATCs' xs ts) = {(a,b,c,{d . (a,b,c,d) \<in> set ts}) | a b c . (a,b,c) \<in> set xs}"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  obtain a b c where "x=(a,b,c)"
    using prod_cases3 by blast
  have "(a,b,c, set (map (\<lambda>(x,y,z,d) . d) (filter (\<lambda>(x,y,z,d) . x = a \<and> y = b \<and> z = c) ts))) = (a,b,c,{d . (a,b,c,d) \<in> set ts})" 
    by force
  moreover have "set (collect_ATCs' ((a,b,c)#xs) ts) = insert (a,b,c, set (map (\<lambda>(x,y,z,d) . d) (filter (\<lambda>(x,y,z,d) . x = a \<and> y = b \<and> z = c) ts))) (set (collect_ATCs' xs ts))"
    by auto
  moreover have "{(a',b',c',{d . (a',b',c',d) \<in> set ts}) | a' b' c'. (a',b',c') \<in> set ((a,b,c)#xs)} = insert (a,b,c,{d . (a,b,c,d) \<in> set ts}) {(a',b',c',{d . (a',b',c',d) \<in> set ts}) | a' b' c' . (a',b',c') \<in> set xs}"
    by auto
  ultimately show ?case using Cons.IH unfolding \<open>x=(a,b,c)\<close> by auto
qed 



fun collect_ATCs :: "('a \<times> 'b \<times> 'c) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> 'd) list \<Rightarrow> ('a \<times> 'b \<times> 'c \<times> ('d set)) list" where
  "collect_ATCs xs ts = collect_ATCs' (remdups xs) (remdups ts)"



lemma collect_ATCs_set :
  "set (collect_ATCs xs ts) = {(a,b,c,{d . (a,b,c,d) \<in> set ts}) | a b c . (a,b,c) \<in> set xs}"
  using collect_ATCs'_set[of "remdups xs" "remdups ts"] 
  unfolding collect_ATCs.simps set_remdups by assumption
*)


subsection \<open>Calculating the Test Suite\<close>

(* how to build with comments?
definition calculate_test_suite' :: "'a FSM \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a Preamble \<times> ('a,'b,'c) traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC set) list" where
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
              = concat (map (\<lambda> (q,P) . map (\<lambda>(p,d) . (q,p)) (fTP q)) DRSP);
         PrefixPairTests 
              = concat (map (\<lambda> (q,P) . prefix_pair_tests' q fRD (fTP q)) DRSP);             
         PreamblePrefixTests
              = concat (map (\<lambda> (q,P) . preamble_prefix_tests' q fRD (fTP q) DRSP) DRSP);              
         PreamblePairTests
              = preamble_pair_tests' DRSP RDSSL
      
    in collect_ATCs PMTP (PrefixPairTests @ PreamblePrefixTests @ PreamblePairTests))"
*)








definition calculate_test_suite :: "'a FSM \<Rightarrow> nat \<Rightarrow> (('a \<times> ('a,'b,'c) traversal_Path \<times> ('a \<times> 'a + 'a) ATC) list \<times> ('a \<times> 'a Preamble) list)" where
  "calculate_test_suite M m = 
    (let 
         RDSSL = r_distinguishable_state_pairs_with_separators_naive M;
         RDS  = set (map fst RDSSL);
         RDP  = filter (\<lambda> S . \<forall> q1 \<in> S . \<forall> q2 \<in> S . q1 \<noteq> q2 \<longrightarrow> (q1,q2) \<in> RDS) (map set (pow_list (nodes_from_distinct_paths M))); 
         MPRD = filter (\<lambda> S . \<not>(\<exists> S' \<in> set RDP . S \<subset> S')) RDP;  
         DRSP = d_reachable_states_with_preambles M;
         DRS  = map fst DRSP; 
         MRS  = map (\<lambda>S. (S, S \<inter> set DRS)) MPRD; 
         MTP  = map (\<lambda> q . (q,m_traversal_paths_with_witness M q MRS m)) DRS;
         fTP  = list_as_fun MTP []; 
         fRD  = \<lambda> q1 q2 . snd (the (find (\<lambda> qqA . fst qqA = (q1,q2)) RDSSL)); 
         PMTP = concat (map (\<lambda> (q,P) . map (\<lambda>(p,d) . (q,p)) (fTP q)) DRSP);
         PrefixPairTests 
              = concat (map (\<lambda> (q,P) . prefix_pair_tests' q fRD (fTP q)) DRSP);             
         PreamblePrefixTests
              = concat (map (\<lambda> (q,P) . preamble_prefix_tests' q fRD (fTP q) DRSP) DRSP);              
         PreamblePairTests
              = preamble_pair_tests' DRSP RDSSL
      
    in  (PrefixPairTests @ PreamblePrefixTests @ PreamblePairTests, DRSP))"

value "calculate_test_suite M_ex_H 4"

definition calculate_test_suite_set :: "'a FSM \<Rightarrow> nat \<Rightarrow> (('a \<times> ('a,'b,'c) traversal_Path \<times> ('a \<times> 'a + 'a) ATC) set \<times> ('a \<times> 'a Preamble) list)" where
  "calculate_test_suite_set M m = (case calculate_test_suite M m of (ts,ps) \<Rightarrow> (set ts,ps))"


(* TODO:

fun convert_test_suite_elem :: "(('a::linorder \<times> ('a,'b,'c) traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> 'a Preamble)) \<Rightarrow> ('a \<times> 'a Preamble) list \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite_elem (q,p,atcs) preambles = empty"

thm foldl.simps

fun convert_test_suite :: "(('a::linorder \<times> ('a,'b,'c) traversal_Path \<times> ('a \<times> 'a + 'a,'b) ATC) list \<times> ('a \<times> 'a Preamble) list) \<Rightarrow> 'a Transition list avl_tree" where
  "convert_test_suite (elems,preambles) = foldl (\<lambda> prev elem . AVL_Set.union prev prev ) empty elems"
*)


end