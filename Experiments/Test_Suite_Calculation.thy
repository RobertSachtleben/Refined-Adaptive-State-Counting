theory Test_Suite_Calculation
imports Test_Suite
begin

section \<open>Test Suites\<close>

subsection \<open>Preliminary Definitions\<close>



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



fun prefix_pair_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) set \<Rightarrow> ('a,'b,'c) test_path set" where
  "prefix_pair_tests q pds = \<Union>{{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . \<exists> (p,(rd,dr)) \<in> pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"

lemma prefix_pair_tests_code[code] :
  "prefix_pair_tests q pds = (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
proof -
  have "\<And> tp . tp \<in> prefix_pair_tests q pds \<Longrightarrow> tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
  proof -
    fix tp assume "tp \<in> prefix_pair_tests q pds"
    then obtain tps where "tp \<in> tps"
                    and   "tps \<in> {{(q,p1,(target q p2)), (q,p2,(target q p1))} | p1 p2 . \<exists> (p,(rd,dr)) \<in> pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)}"
      unfolding prefix_pair_tests.simps
      by (meson UnionE) 
    then obtain p1 p2 where "tps = {(q,p1,(target q p2)), (q,p2,(target q p1))}"
                      and   "\<exists> (p,(rd,dr)) \<in> pds . (p1,p2) \<in> set (prefix_pairs p) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"
      unfolding mem_Collect_eq by blast

    then obtain p rd dr where "(p,(rd,dr)) \<in> pds" and "(p1,p2) \<in> set (prefix_pairs p)" and "(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)"
      by blast

    have scheme : "\<And> f x xs . x \<in> set xs \<Longrightarrow> f x \<in> set (map f xs)" by auto

    have "(p1,p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))"
      using \<open>(p1,p2) \<in> set (prefix_pairs p)\<close>
            \<open>(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)\<close> 
      by auto
    have "{(q,p1,(target q p2)), (q,p2,(target q p1))} \<in> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))"
      using scheme[OF \<open>(p1,p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))\<close>, of "(\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))})"] 
      by simp


    then show "tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
      using \<open>tp \<in> tps\<close> \<open>(p,(rd,dr)) \<in> pds\<close>
      unfolding \<open>tps = {(q,p1,(target q p2)), (q,p2,(target q p1))}\<close> by blast
  qed
  moreover have "\<And> tp . tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))
                        \<Longrightarrow> tp \<in> prefix_pair_tests q pds"
  proof -
    fix tp assume "tp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) pds))"
    then obtain prddr where "prddr \<in> pds"
                        and "tp \<in> (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) prddr"
      by blast
    then obtain p rd dr where "prddr = (p,(rd,dr))" by auto

    then have "tp \<in> \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))"
      using \<open>tp \<in> (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) prddr\<close> by auto

    then obtain p1 p2 where "(p1,p2) \<in> set (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))"
                      and   "tp \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}" 
      by auto
    then have "(target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)" 
         and  "(p1,p2) \<in> set (prefix_pairs p)"
      by auto

    then show "tp \<in> prefix_pair_tests q pds"
      using \<open>prddr \<in> pds\<close> \<open>tp \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}\<close>
      unfolding prefix_pair_tests.simps  \<open>prddr = (p,(rd,dr))\<close> 
      by blast
  qed
  ultimately show ?thesis by blast
qed



lemma prefix_pair_tests_containment :
  assumes "(p,(rd,dr)) \<in> pds"
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


(*
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
*)
 


subsubsection "Calculating Tests between Preambles"



fun preamble_prefix_tests' :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> 'a list \<Rightarrow> ('a,'b,'c) test_path list" where
  "preamble_prefix_tests' q pds drs = 
    concat (map (\<lambda>((p,(rd,dr)),q2,p1) . [(q,p1,q2), (q2,[],(target q p1))]) 
                (filter (\<lambda>((p,(rd,dr)),q2,p1) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) 
                        (concat (map (\<lambda>((p,(rd,dr)),q2) . map (\<lambda>p1 . ((p,(rd,dr)),q2,p1)) (prefixes p)) (cartesian_product_list pds drs)))))"


definition preamble_prefix_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) set \<Rightarrow> 'a set \<Rightarrow> ('a,'b,'c) test_path set" where
  "preamble_prefix_tests q pds drs = \<Union>{{(q,p1,q2), (q2,[],(target q p1))} | p1 q2 . \<exists> (p,(rd,dr)) \<in> pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2}"

lemma preamble_prefix_tests_code[code] :
  "preamble_prefix_tests q pds drs = (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
proof -
  have "\<And> pp . pp \<in> preamble_prefix_tests q pds drs \<Longrightarrow> pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"  
  proof -
    fix pp assume "pp \<in> preamble_prefix_tests q pds drs"
    then obtain p1 q2 where "pp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
                      and   "\<exists> (p,(rd,dr)) \<in> pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      unfolding preamble_prefix_tests_def by blast
    then obtain p rd dr where "(p,(rd,dr)) \<in> pds" and "q2 \<in> drs" and "(\<exists> p2 . p = p1@p2)" and "(target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      by auto

    then have "(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))"
      unfolding prefixes_set by force
    then show "pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
      using \<open>(p,(rd,dr)) \<in> pds\<close>
            \<open>pp \<in> {(q,p1,q2), (q2,[],(target q p1))}\<close> by blast
  qed
  moreover have "\<And> pp . pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))
                         \<Longrightarrow> pp \<in> preamble_prefix_tests q pds drs"
  proof -
    fix pp assume "pp \<in> (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) pds))"
    then obtain prddr where "prddr \<in> pds"
                      and   "pp \<in> (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) prddr"
      by blast

    obtain p rd dr where "prddr = (p,(rd,dr))"
      using prod_cases3 by blast 

    obtain p1 q2 where "(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))"
                 and   "pp \<in> {(q,p1,q2), (q2,[],(target q p1))}"
      using \<open>pp \<in> (\<lambda> (p,(rd,dr)) . \<Union>(image (\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))}) (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs)))) prddr\<close>
      unfolding \<open>prddr = (p,(rd,dr))\<close> 
      by blast

    have "q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2"
      using \<open>(p1,q2) \<in> (Set.filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) ((set (prefixes p)) \<times> drs))\<close>
      unfolding prefixes_set 
      by auto
    then have "\<exists>(p, rd, dr)\<in>pds. q2 \<in> drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2"
      using \<open>prddr \<in> pds\<close> \<open>prddr = (p,(rd,dr))\<close> 
      by blast
    then have *: "{(q,p1,q2), (q2,[],(target q p1))} \<in> {{(q, p1, q2), (q2, [], target q p1)} |p1 q2.
             \<exists>(p, rd, dr)\<in>pds. q2 \<in> drs \<and> (\<exists>p2. p = p1 @ p2) \<and> target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2}" by blast

    show "pp \<in> preamble_prefix_tests q pds drs"
      using UnionI[OF * \<open>pp \<in> {(q,p1,q2), (q2,[],(target q p1))}\<close>]
      unfolding preamble_prefix_tests_def by assumption
  qed
  ultimately show ?thesis by blast
qed


(*
definition preamble_prefix_tests :: "'a \<Rightarrow> (('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)) list \<Rightarrow> 'a set \<Rightarrow> ('a,'b,'c) test_path set" where
  "preamble_prefix_tests q pds drs = \<Union>{{(q,p1,q2), (q2,[],(target q p1))} | p1 q2 . \<exists> (p,(rd,dr)) \<in> set pds . q2 \<in> drs \<and> (\<exists> p2 . p = p1@p2) \<and> (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2}"
*)




lemma set_concat_elem :
  assumes "x \<in> set (concat xss)"
  obtains xs where "xs \<in> set xss" and "x \<in> set xs" 
  using assms by auto

lemma set_map_elem :
  assumes "y \<in> set (map f xs)"
  obtains x where "y = f x" and "x \<in> set xs" using assms by auto


(*
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
*)    

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





subsection \<open>Calculating the Test Suite\<close>


(* likely too restrictive
fun is_sufficient_for_reduction_testing :: "('a,'b,'c,'d) test_suite \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> nat \<Rightarrow> bool" where
  "is_sufficient_for_reduction_testing (Test_Suite prs tps rd_targets atcs) M m = 
    ( (initial M,initial_preamble M) \<in> prs 
    \<and> (\<forall> q P . (q,P) \<in> prs \<longrightarrow> is_preamble P M q)
    \<and> (\<forall> q P1 P2 . (q,P1) \<in> prs \<longrightarrow> (q,P2) \<in> prs \<longrightarrow> P1 = P2)
    \<and> (\<forall> q P . (q,P) \<in> prs \<longrightarrow> (tps q) \<noteq> {})
    \<and> (\<forall> q p qs . p \<in> tps q \<longrightarrow> qs \<in> rd_targets (q,p) \<longrightarrow> (\<exists> S pFull p' . 
                                                 S \<subseteq> nodes M 
                                              \<and> (pFull = p@p')
                                              \<and> (path M q pFull)
                                              \<and> (\<lambda> d . length (filter (\<lambda>t . t_target t \<in> fst d) pFull) \<ge> Suc (m - (card (snd d)))) (S, S \<inter> image fst prs)                                              
                                              \<and> (\<forall> q1 q2 . q1 \<in> S \<longrightarrow> q2 \<in> S \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})  
                                              \<and> (\<forall> p1 p2 p3 . pFull=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> S \<longrightarrow> target q p2 \<in> S \<longrightarrow> target q p1 \<noteq> target q p2 \<longrightarrow> (p1 \<in> tps q \<and> p2 \<in> tps q \<and> target q p1 \<in> rd_targets (q,p2) \<and> target q p2 \<in> rd_targets (q,p1)))
                                              \<and> (\<forall> p1 p2 q' . pFull=p1@p2 \<longrightarrow> q' \<in> image fst prs \<longrightarrow> target q p1 \<in> S \<longrightarrow> q' \<in> S \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))))
    \<and> (\<forall> q1 q2 . q1 \<in> image fst prs \<longrightarrow> q2 \<in> image fst prs \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {} \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[])))
    \<and> (\<forall> q1 q2 A d1 d2 . ((A,d1,d2) \<in> atcs (q1,q2)) \<longleftrightarrow> ((A,d2,d1) \<in> atcs (q2,q1)))
    \<and> (\<forall> q1 q2 A d1 d2 . (A,d1,d2) \<in> atcs (q1,q2) \<longrightarrow> is_separator M q1 q2 A d1 d2)
    )"
*)






abbreviation(input) "lookup_with_default_by f g d \<equiv> (\<lambda> x . case f x of None \<Rightarrow> g d | Some xs \<Rightarrow> g xs)"
abbreviation(input) "m2f_by g f \<equiv> lookup_with_default_by f g {}" (* map to (set-valued) fun *)




definition calculate_test_paths ::
  "('a,'b,'c) fsm
  \<Rightarrow> nat
  \<Rightarrow> 'a set
  \<Rightarrow> ('a \<times> 'a) set
  \<Rightarrow> ('a set \<times> 'a set) list
  \<Rightarrow> (('a \<Rightarrow> ('a,'b,'c) traversal_Path set) \<times> (('a \<times> ('a,'b,'c) traversal_Path) \<Rightarrow> 'a set))" 
  where
  "calculate_test_paths M m d_reachable_nodes r_distinguishable_pairs repetition_sets =
    (let
         paths_with_witnesses 
              = (image (\<lambda> q . (q,m_traversal_paths_with_witness M q repetition_sets m)) d_reachable_nodes);
         get_paths  
              = m2f (set_as_map paths_with_witnesses);
         PrefixPairTests                    
              = \<Union> q \<in> d_reachable_nodes . \<Union> mrsps \<in> get_paths q . prefix_pair_tests q mrsps;
         PreamblePrefixTests
              = \<Union> q \<in> d_reachable_nodes . \<Union> mrsps \<in> get_paths q . preamble_prefix_tests q mrsps d_reachable_nodes;
         PreamblePairTests
              = preamble_pair_tests d_reachable_nodes r_distinguishable_pairs;
         tests
              = PrefixPairTests \<union> PreamblePrefixTests \<union> PreamblePairTests; 
         tps'  
              = m2f_by \<Union> (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) paths_with_witnesses));
         tps''  
              = m2f (set_as_map (image (\<lambda> (q,p,q') . (q,p)) tests));
         tps  
              = (\<lambda> q . tps' q \<union> tps'' q);
         rd_targets 
              = m2f (set_as_map (image (\<lambda> (q,p,q') . ((q,p),q')) tests))    
  
  in ( tps, rd_targets))"


definition combine_test_suite ::
  "('a,'b,'c) fsm
  \<Rightarrow> nat
  \<Rightarrow> ('a \<times> ('a,'b,'c) preamble) set
  \<Rightarrow> (('a \<times> 'a) \<times> (('d,'b,'c) atc \<times> 'd \<times> 'd)) set
  \<Rightarrow> ('a set \<times> 'a set) list
  \<Rightarrow> ('a,'b,'c,'d) test_suite" 
  where
  "combine_test_suite M m nodes_with_preambles pairs_with_separators repetition_sets =
    (let drs = image fst nodes_with_preambles;
        rds = image fst pairs_with_separators;
        tps_and_targets = calculate_test_paths M m drs rds repetition_sets;
        atcs = m2f (set_as_map pairs_with_separators) 
in (Test_Suite nodes_with_preambles (fst tps_and_targets) (snd tps_and_targets) atcs))"





definition calculate_test_suite_example :: "('a::linorder,'b::linorder,'c) fsm \<Rightarrow> nat \<Rightarrow> ('a,'b,'c, ('a \<times> 'a) + 'a) test_suite" where
  "calculate_test_suite_example M m = 
    (let
         nodes_with_preambles = d_reachable_states_with_preambles M;
         pairs_with_separators = image (\<lambda>((q1,q2),A) . ((q1,q2),A,Inr q1,Inr q2)) (r_distinguishable_state_pairs_with_separators M);
         repetition_sets = maximal_repetition_sets_from_separators_list M
  in combine_test_suite M m nodes_with_preambles pairs_with_separators repetition_sets)" 


value "calculate_test_suite_example m_ex_H 4"
value "case (calculate_test_suite_example m_ex_H 4) of
        (Test_Suite a b c d) \<Rightarrow>
          (image fst a,
           image b (image fst a))"
value "case (calculate_test_suite_example m_ex_H 4) of
        (Test_Suite a b c d) \<Rightarrow>
          (image (\<lambda> (x,_) . image (\<lambda> xy . (xy, c xy)) (image (Pair x) (b x))) a)"


lemma set_as_map_containment :
  assumes "(x,y) \<in> zs"
  shows "y \<in> (m2f (set_as_map zs)) x"
  using assms unfolding set_as_map_def
  by auto 
  
lemma m2f_by_from_m2f :
  "(m2f_by g f xs) = g (m2f f xs)"
  by (simp add: option.case_eq_if) 

lemma prefix_pairs_paths:  "\<And> p p1 p2 (M :: ('a,'b,'c) fsm) q . (p1,p2) \<in> set (prefix_pairs p) \<Longrightarrow> path M q p \<Longrightarrow> path M q p1 \<and> path M q p2"
proof - 
  fix M :: "('a,'b,'c) fsm"
  fix p p1 p2 q assume "(p1,p2) \<in> set (prefix_pairs p)" and "path M q p"
  
  obtain p1' p3  where "p2 = p1@p1'" and "p = p1@p1'@p3"
    using \<open>(p1,p2) \<in> set (prefix_pairs p)\<close>
    unfolding prefix_pairs_set_alt by blast

  have "path M q p1"
    using \<open>path M q p\<close> unfolding \<open>p = p1@p1'@p3\<close>
    by auto 
  moreover have "path M q p2" 
    using \<open>path M q p\<close> unfolding \<open>p = p1@p1'@p3\<close> \<open>p2 = p1@p1'\<close>
    by auto
  ultimately show "path M q p1 \<and> path M q p2"
    by simp
qed



lemma calculate_test_suite_example_sufficient :
  fixes M :: "('a::linorder,'b::linorder,'c) fsm"
  assumes "observable M"
  and     "completely_specified M"
  and     "inputs M \<noteq> {}"
shows "is_sufficient_for_reduction_testing (calculate_test_suite_example M m) M m"
proof -
  obtain nodes_with_preambles tps rd_targets atcs where "calculate_test_suite_example M m = Test_Suite nodes_with_preambles tps rd_targets atcs"
    using test_suite.exhaust by blast


  have nodes_with_preambles_def : "nodes_with_preambles = d_reachable_states_with_preambles M"
  and  tps_def                  : "tps = (\<lambda> q . (m2f_by \<Union> (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))) q
                                                \<union> (m2f (set_as_map (image (\<lambda> (q,p,q') . (q,p)) ((\<Union> q \<in> (image fst (d_reachable_states_with_preambles M)) . \<Union> mrsps \<in> (m2f (set_as_map (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))) q . prefix_pair_tests q mrsps) 
                                                        \<union> (\<Union> q \<in> (image fst (d_reachable_states_with_preambles M)) . \<Union> mrsps \<in> (m2f (set_as_map (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))) q . preamble_prefix_tests q mrsps (image fst (d_reachable_states_with_preambles M))) 
                                                        \<union> (preamble_pair_tests (image fst (d_reachable_states_with_preambles M)) (image fst (image (\<lambda>((q1,q2),A) . ((q1,q2),A,(Inr q1) :: 'a \<times> 'a + 'a, (Inr q2) :: 'a \<times> 'a + 'a)) (r_distinguishable_state_pairs_with_separators M)))))))) q))"
  and  rd_targets_def           : "rd_targets = m2f (set_as_map (image (\<lambda> (q,p,q') . ((q,p),q')) 
                                                        ((\<Union> q \<in> (image fst (d_reachable_states_with_preambles M)) . \<Union> mrsps \<in> (m2f (set_as_map (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))) q . prefix_pair_tests q mrsps) 
                                                        \<union> (\<Union> q \<in> (image fst (d_reachable_states_with_preambles M)) . \<Union> mrsps \<in> (m2f (set_as_map (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))) q . preamble_prefix_tests q mrsps (image fst (d_reachable_states_with_preambles M))) 
                                                        \<union> (preamble_pair_tests (image fst (d_reachable_states_with_preambles M)) (image fst (image (\<lambda>((q1,q2),A) . ((q1,q2),A,(Inr q1) :: 'a \<times> 'a + 'a, (Inr q2) :: 'a \<times> 'a + 'a)) (r_distinguishable_state_pairs_with_separators M)))))))"          
  and  atcs_def                 : "atcs = m2f (set_as_map ((\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M))"
    using \<open>calculate_test_suite_example M m = Test_Suite nodes_with_preambles tps rd_targets atcs\<close>[symmetric]
    unfolding calculate_test_suite_example_def combine_test_suite_def Let_def calculate_test_paths_def  by force+


  have tps_alt_def: "\<And> q . q \<in> fst ` d_reachable_states_with_preambles M \<Longrightarrow> 
          tps q = (fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
  and rd_targets_alt_def: "\<And> q p . q \<in> fst ` d_reachable_states_with_preambles M \<Longrightarrow> 
          rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
  proof -
    fix q p assume "q \<in> fst ` d_reachable_states_with_preambles M"

  

    have scheme0 : "(case set_as_map
             ((\<lambda>(q, p). (q, fst ` p)) `
              (\<lambda>q. (q, m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) `
              fst ` d_reachable_states_with_preambles M)
             q of
       None \<Rightarrow> \<Union> {} | Some x \<Rightarrow> \<Union> x) = image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
    proof -
      have *: "((\<lambda>(q, p). (q, fst ` p)) `
              (\<lambda>q. (q, m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) `
              fst ` d_reachable_states_with_preambles M)
               = (\<lambda> q . (q , image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m))) ` (fst ` d_reachable_states_with_preambles M)"
        by force
      have **: "\<And> f q xs . (case set_as_map
                              ((\<lambda>q. (q, f q)) ` xs)
                              q of
                        None \<Rightarrow> \<Union> {} | Some xs \<Rightarrow> \<Union> xs) = (if q \<in> xs then \<Union> {f q} else \<Union> {})" 
      unfolding set_as_map_def by auto

      show ?thesis
        unfolding * **
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
        by auto
    qed
    
    
    have scheme1 : "\<And> f q xs . (case set_as_map
                              ((\<lambda>q. (q, f q)) ` xs)
                              q of
                        None \<Rightarrow> {} | Some xs \<Rightarrow> xs) = (if q \<in> xs then {f q} else {})" 
      unfolding set_as_map_def by auto        


    have scheme2: "(\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                   \<Union> (prefix_pair_tests q `
                       (if q \<in> fst ` d_reachable_states_with_preambles M
                        then {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m} else {})))
      = (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. (\<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})))"
      unfolding set_as_map_def by auto


    have scheme3: "(\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                   \<Union>mrsps\<in>if q \<in> fst ` d_reachable_states_with_preambles M
                           then {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m} else {}.
                      preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))
      = (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. (\<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m} . preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)))"
      unfolding set_as_map_def by auto

    have scheme4 : "(fst ` (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M)
                    = image fst (r_distinguishable_state_pairs_with_separators M)" 
      by force


    


    have *:"tps q = (fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
      unfolding tps_def 
      unfolding scheme0 scheme1 scheme2 scheme3 scheme4
      unfolding set_as_map_def
      by auto

    



    have **: "{z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}
          = {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}" 
      (is "{z. (q, z) \<in> ?S1} = {z. (q, z) \<in> ?S2}")
    proof -
      have "\<And> z . (q, z) \<in> ?S1 \<Longrightarrow> (q, z) \<in> ?S2"
      proof -
        fix z assume "(q, z) \<in> ?S1"
        then consider "(q, z) \<in> (\<lambda>(q, p, q'). (q, p)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}))"
                    | "(q,z) \<in> (\<lambda>(q, p, q'). (q, p)) `  (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
                    | "(q,z) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
          by blast
        then show "(q, z) \<in> ?S2" proof cases
          case 1
          have scheme: "\<And> f y xs . y \<in> image f xs \<Longrightarrow> \<exists> x . x \<in> xs \<and> f x = y" by auto

          obtain qzq where "qzq \<in> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}))"
                     and   "(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)"
            using scheme[OF 1] by blast
          then obtain q' where "q'\<in>fst ` d_reachable_states_with_preambles M"
                         and   "qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m})"
            by blast
          then have "fst qzq = q'"
            by auto
          then have "q' = q"
            using \<open>(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)\<close>
            by (simp add: prod.case_eq_if) 
          then have "qzq \<in> \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})"
            using \<open>qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m})\<close> 
            by blast
          then have "(\<lambda>(q, p, q'). (q, p)) qzq \<in> ?S2"
            by auto
          then show ?thesis 
            unfolding \<open>(\<lambda>(q, p, q'). (q, p)) qzq = (q,z)\<close> 
            by assumption
        next
          case 2 
          then show ?thesis by blast
        next
          case 3
          then show ?thesis by blast
        qed
      qed
      moreover have "\<And> z . (q, z) \<in> ?S2 \<Longrightarrow> (q, z) \<in> ?S1"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> by blast
      ultimately show ?thesis
        by meson
    qed
        


    show "tps q = (fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<union> 
                  {z. (q, z)
                    \<in> (\<lambda>(q, p, q'). (q, p)) `
                       ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                        (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                        preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
     using * unfolding ** by assumption




    have ***: "rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
      unfolding rd_targets_def
      unfolding scheme1 scheme2 scheme3 scheme4
      unfolding set_as_map_def
      by auto


    have ****: "{z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}
          = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}" 
      (is "{z. ((q, p), z) \<in> ?S1} = {z. ((q, p), z) \<in> ?S2}")
    proof -
      have "\<And> z . ((q, p), z) \<in> ?S1 \<Longrightarrow> ((q, p), z) \<in> ?S2"
      proof -
        fix z assume "((q, p), z) \<in> ?S1"
        then consider "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}))"
                    | "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) `  (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                            \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                               preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))"
                    | "((q, p), z) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
          by blast
        then show "((q, p), z) \<in> ?S2" proof cases
          case 1
          have scheme: "\<And> f y xs . y \<in> image f xs \<Longrightarrow> \<exists> x . x \<in> xs \<and> f x = y" by auto

          obtain qzq where "qzq \<in> (\<Union>q\<in>fst ` d_reachable_states_with_preambles M. \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}))"
                     and   "(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)"
            using scheme[OF 1] by blast
          then obtain q' where "q'\<in>fst ` d_reachable_states_with_preambles M"
                         and   "qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m})"
            by blast
          then have "fst qzq = q'"
            by auto
          then have "q' = q"
            using \<open>(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)\<close>
            by (simp add: prod.case_eq_if) 
          then have "qzq \<in> \<Union> (prefix_pair_tests q ` {m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m})"
            using \<open>qzq \<in> \<Union> (prefix_pair_tests q' ` {m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m})\<close> 
            by blast
          then have "(\<lambda>(q, p, y). ((q, p), y)) qzq \<in> ?S2"
            by auto
          then show ?thesis 
            unfolding \<open>(\<lambda>(q, p, y). ((q, p), y)) qzq = ((q,p),z)\<close> 
            by assumption
        next
          case 2 
          then show ?thesis by blast
        next
          case 3
          then show ?thesis by blast
        qed
      qed
      moreover have "\<And> z . ((q, p), z) \<in> ?S2 \<Longrightarrow> ((q, p), z) \<in> ?S1"
        using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> by blast
      ultimately show ?thesis
        by meson
    qed

    


    show "rd_targets (q,p) = {z. ((q, p), z)
                   \<in> (\<lambda>(q, p, y). ((q, p), y)) `
                      ((prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<union>
                       (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                           \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                              preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M)) \<union>
                       preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))}"
      using ***  unfolding **** by assumption
  qed




  have p1: "(initial M,initial_preamble M) \<in> nodes_with_preambles"
    using fsm_initial[of M]
    unfolding nodes_with_preambles_def d_reachable_states_with_preambles_def calculate_state_preamble_from_input_choices.simps by force

  have p2a: "\<And> q P . (q,P) \<in> nodes_with_preambles \<Longrightarrow> is_preamble P M q"
    using assms(1) d_reachable_states_with_preambles_soundness(1) nodes_with_preambles_def by blast


  have "\<And>q. q \<in> FSM.nodes M \<Longrightarrow> \<exists>d\<in>set (maximal_repetition_sets_from_separators_list M). q \<in> fst d"
  and  "\<And>d. d \<in> set (maximal_repetition_sets_from_separators_list M) \<Longrightarrow> snd d \<subseteq> fst d"
    unfolding maximal_repetition_sets_from_separators_code_alt[symmetric]
              maximal_repetition_sets_from_separators_def
    using maximal_pairwise_r_distinguishable_state_sets_from_separators_cover[of _ M] by force+


  have p2b: "\<And> q P . (q,P) \<in> nodes_with_preambles \<Longrightarrow> (tps q) \<noteq> {}"
  proof -
    fix q P assume "(q,P) \<in> nodes_with_preambles"
    then have "q \<in> (image fst (d_reachable_states_with_preambles M))"
      unfolding nodes_with_preambles_def
      by (simp add: rev_image_eqI) 
    
    have "q \<in> nodes M"
      using \<open>(q, P) \<in> nodes_with_preambles\<close> assms(1) d_reachable_states_with_preambles_soundness(2) nodes_with_preambles_def by blast 


    obtain p' d' where  "(p', d') \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
      using m_traversal_path_exist[OF assms(2) \<open>q \<in> nodes M\<close> assms(3) \<open>\<And>q. q \<in> FSM.nodes M \<Longrightarrow> \<exists>d\<in>set (maximal_repetition_sets_from_separators_list M). q \<in> fst d\<close> \<open>\<And>d. d \<in> set (maximal_repetition_sets_from_separators_list M) \<Longrightarrow> snd d \<subseteq> fst d\<close>]
      by blast
    then have "p' \<in> image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
      using image_iff by fastforce
    
    have "(q, image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<in> (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))"
      using \<open>q \<in> (image fst (d_reachable_states_with_preambles M))\<close> by force
    have "(image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<in> (m2f (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M)))))) q"
      using set_as_map_containment[OF \<open>(q, image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) \<in> (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M))))\<close>]
      by assumption
    then have "p' \<in> (\<Union> ((m2f (set_as_map (image (\<lambda> (q,p) . (q, image fst p)) (image (\<lambda> q . (q,m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)) (image fst (d_reachable_states_with_preambles M)))))) q))"
      using \<open>p' \<in> image fst (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)\<close> by blast

    then show "(tps q) \<noteq> {}"
      unfolding tps_def m2f_by_from_m2f by blast
  qed

  have p2: "(\<forall>q P. (q, P) \<in> nodes_with_preambles \<longrightarrow> is_preamble P M q \<and> tps q \<noteq> {})"
    using p2a p2b by blast



  have "\<And> q1 q2 A d1 d2 . ((A,d1,d2) \<in> atcs (q1,q2)) \<Longrightarrow> ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2"
  proof -
    fix q1 q2 A d1 d2 assume "((A,d1,d2) \<in> atcs (q1,q2))"
    then have "atcs (q1,q2) = {z. ((q1, q2), z) \<in> (\<lambda>((q1, q2), A). ((q1, q2), A, Inr q1, Inr q2)) ` r_distinguishable_state_pairs_with_separators M}"
      unfolding atcs_def set_as_map_def by auto
    then show "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2"
      using \<open>((A,d1,d2) \<in> atcs (q1,q2))\<close> by auto
  qed


  have "\<And> q1 q2 A d1 d2 . (A,d1,d2) \<in> atcs (q1,q2) \<Longrightarrow> (A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
  proof -
    fix q1 q2 A d1 d2 assume "(A,d1,d2) \<in> atcs (q1,q2)"
    then have "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M" and "d1 = Inr q1" and "d2 = Inr q2"
      using \<open>\<And> q1 q2 A d1 d2 . ((A,d1,d2) \<in> atcs (q1,q2)) \<Longrightarrow> ((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M \<and> d1 = Inr q1 \<and> d2 = Inr q2\<close>
      by blast+
    then have "((q2,q1),A) \<in> r_distinguishable_state_pairs_with_separators M"
      unfolding r_distinguishable_state_pairs_with_separators_def
      by auto  
    then have "(A,d2,d1) \<in> atcs (q2,q1)"
      unfolding atcs_def \<open>d1 = Inr q1\<close> \<open>d2 = Inr q2\<close> set_as_map_def by force
    moreover have "is_separator M q1 q2 A d1 d2"
      using r_distinguishable_state_pairs_with_separators_elem_is_separator[OF \<open>((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M\<close> assms(1,2)]
      unfolding \<open>d1 = Inr q1\<close> \<open>d2 = Inr q2\<close>
      by assumption
    ultimately show "(A,d2,d1) \<in> atcs (q2,q1) \<and> is_separator M q1 q2 A d1 d2"
      by simp
  qed
  then have p3 : "(\<forall>q1 q2 A d1 d2. (A, d1, d2) \<in> atcs (q1, q2) \<longrightarrow> (A, d2, d1) \<in> atcs (q2, q1) \<and> is_separator M q1 q2 A d1 d2)"
    by blast


  have p4_witness: " 
        ((\<forall> q . q \<in> nodes M \<longrightarrow> (\<exists>d \<in> set (maximal_repetition_sets_from_separators_list M). q \<in> fst d))
        \<and> (\<forall> d . d \<in> set (maximal_repetition_sets_from_separators_list M) \<longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})))
        \<and> (\<forall> q . q \<in> image fst nodes_with_preambles \<longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m} \<and> fst ` (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<subseteq> tps q) 
        \<and> (\<forall> q p d . q \<in> image fst nodes_with_preambles \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m \<longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst nodes_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))))))"
  proof -
    let ?RepSets = "(maximal_repetition_sets_from_separators_list M)"

    have p4a: "\<And> q . q \<in> nodes M \<Longrightarrow> (\<exists>d \<in> set ?RepSets. q \<in> fst d)"
    proof -
      fix q assume "q \<in> nodes M"

      have *: "image fst (set ?RepSets) = set (maximal_pairwise_r_distinguishable_state_sets_from_separators_list M)"
        unfolding maximal_repetition_sets_from_separators_list_def
        by force
      have "(\<exists>d \<in> image fst (set ?RepSets). q \<in> d)"
        unfolding * maximal_pairwise_r_distinguishable_state_sets_from_separators_code[symmetric]
        using maximal_pairwise_r_distinguishable_state_sets_from_separators_cover[OF \<open>q \<in> nodes M\<close>]
        by assumption
      then show "(\<exists>d \<in> set ?RepSets. q \<in> fst d)"
        by auto
    qed
      
    have p4b: "\<And> d . d \<in> set ?RepSets \<Longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {}))"
    proof -
      fix d assume "d \<in> set ?RepSets"
      then have "d \<in> maximal_repetition_sets_from_separators M"
        unfolding maximal_repetition_sets_from_separators_code_alt[symmetric] 
        by assumption
      


      have "fst d \<subseteq> nodes M" and "(snd d \<subseteq> fst d)" and "\<And> q1 q2 . q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
        using \<open>d \<in> maximal_repetition_sets_from_separators M\<close>
        unfolding maximal_repetition_sets_from_separators_def 
                  maximal_pairwise_r_distinguishable_state_sets_from_separators_def
                  pairwise_r_distinguishable_state_sets_from_separators_def 
        by force+

      moreover have "\<And> q1 q2 . q1 \<in> fst d \<Longrightarrow> q2 \<in> fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1,q2) \<noteq> {}"
      proof -
        fix q1 q2 assume "q1 \<in> fst d" and "q2 \<in> fst d" and "q1 \<noteq> q2"
        then have "(q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M"
          using \<open>\<And> q1 q2 . q1\<in>fst d \<Longrightarrow> q2\<in>fst d \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> (q1, q2) \<in> fst ` r_distinguishable_state_pairs_with_separators M\<close>
          by blast
        then obtain A where "((q1,q2),A) \<in> r_distinguishable_state_pairs_with_separators M"
          by auto
        then have "(A,Inr q1,Inr q2) \<in> atcs (q1,q2)"
          unfolding atcs_def set_as_map_def 
          by force
        then show "atcs (q1,q2) \<noteq> {}"
          by blast
      qed
      ultimately show "((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {}))"
        by blast
    qed


    have p4c : "\<And> q . q \<in> image fst nodes_with_preambles \<Longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m} \<and> fst ` (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<subseteq> tps q"
    proof 
      fix q assume "q \<in> image fst nodes_with_preambles"
      then have "q \<in> fst ` d_reachable_states_with_preambles M"
        unfolding nodes_with_preambles_def by assumption
      then have "q \<in> nodes M"
        by (metis (no_types, lifting) assms(1) d_reachable_states_with_preambles_soundness(2) image_iff prod.collapse)
      show "fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m \<subseteq> tps q"
        unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
        by blast

      show "tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}"
      proof
        fix p assume "p \<in> tps q"


        have * : "(\<And> q . q \<in> nodes M \<Longrightarrow> (\<exists>d \<in> set (maximal_repetition_sets_from_separators_list M). q \<in> fst d))" 
          using p4a by blast

        have  **: "(\<And> d . d \<in> set (maximal_repetition_sets_from_separators_list M) \<Longrightarrow> (snd d \<subseteq> fst d))"
          using p4b by simp


        from \<open>p \<in> tps q\<close> consider 
          (a) "p \<in> fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m" |
          (b) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m))" |
          (c) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
                  \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                     preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))" |
          (d) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"  
          unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] by blast
        then show "p \<in> {p1. \<exists>p2 d. (p1 @ p2, d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}"
        proof cases
          case a
          then obtain d where "(p,d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
            by auto
          then have "\<exists>p2 d. (p @ p2, d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
            by (metis append_eq_append_conv2)
          then show ?thesis 
            by blast
        next
          case b
    
          obtain p1 p2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})"
             and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m.
                (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2"
            using b
            unfolding prefix_pair_tests.simps by blast
    
          
    
          obtain p' d where "(p', d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
                      and   "(p1, p2) \<in> set (prefix_pairs p')"
            using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m.
                (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2\<close>
            by blast
    
          have "\<exists> p'' . p' = p @ p''"
            using \<open>(p1, p2) \<in> set (prefix_pairs p')\<close> unfolding prefix_pairs_set_alt 
            using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})\<close> by auto
          then show ?thesis
            using \<open>(p', d) \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m\<close>  
            by blast
        next
          case c     
    
          obtain q' where "q' \<in> fst ` d_reachable_states_with_preambles M"
                    and   "(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M))"
            using c by blast
    
          obtain p1 q2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})"
             and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m.
                q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2"
            using \<open>(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M))\<close>
            unfolding preamble_prefix_tests_def
            by blast
    
          
    
          obtain p2 d where "(p1@p2, d)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m"
                          and   "q2 \<in> fst ` d_reachable_states_with_preambles M"
            using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m.
                q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2\<close>
            by blast
    
          consider (a) "q = q' \<and> p = p1" | (b) "q = q2 \<and> p = []"
            using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})\<close> by auto
          then show ?thesis proof cases
            case a
            then show ?thesis
              using \<open>(p1 @ p2, d) \<in> m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m\<close> by blast 
    
          next
            case b
    
            then have "q \<in> nodes M" and "p = []"
              using \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close> unfolding d_reachable_states_with_preambles_def by auto
    
            have "\<exists>p' d'. (p', d') \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
              using m_traversal_path_exist[OF assms(2) \<open>q \<in> nodes M\<close> assms(3) * **]
              by blast
            then show ?thesis 
              unfolding \<open>p = []\<close>
              by simp
          qed
        next
          case d 
          then have "q \<in> (fst ` d_reachable_states_with_preambles M)" and "p = []"
            unfolding preamble_pair_tests.simps by auto
          then have "q \<in> nodes M"
            using \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close> unfolding d_reachable_states_with_preambles_def by auto
    
          have "\<exists>p' d'. (p', d') \<in> m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
            using m_traversal_path_exist[OF assms(2) \<open>q \<in> nodes M\<close> assms(3) * **]
            by blast
          then show ?thesis 
            unfolding \<open>p = []\<close>
            by simp
        qed
      qed
    qed


      
    have p4d : "\<And> q p d . q \<in> image fst nodes_with_preambles \<Longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q ?RepSets m \<Longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst nodes_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))))"
    proof -
      fix q p d assume "q \<in> image fst nodes_with_preambles" and "(p,d) \<in> m_traversal_paths_with_witness M q ?RepSets m"
      then have "(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q ?RepSets m" by auto

      have "q \<in> fst ` d_reachable_states_with_preambles M"
        using \<open>q \<in> image fst nodes_with_preambles\<close> unfolding nodes_with_preambles_def by assumption

      have p4c1 : "\<And> p1 p2 p3 . p=p1@p2@p3 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> target q (p1@p2) \<in> fst d \<Longrightarrow> target q p1 \<noteq> target q (p1@p2) \<Longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
      proof -
        fix p1 p2 p3 assume "p=p1@p2@p3" and "p2 \<noteq> []" and "target q p1 \<in> fst d" and "target q (p1@p2) \<in> fst d" and "target q p1 \<noteq> target q (p1@p2)"

        
        
        have "(p1,p1@p2) \<in> set (prefix_pairs p)"
          using \<open>p=p1@p2@p3\<close> \<open>p2 \<noteq> []\<close> unfolding prefix_pairs_set
          by simp 
        then have "(p1,p1@p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))"
          using \<open>target q p1 \<in> fst d\<close> \<open>target q (p1@p2) \<in> fst d\<close> \<open>target q p1 \<noteq> target q (p1@p2)\<close>
          by auto
        have "{(q, p1, target q (p1@p2)), (q, (p1@p2), target q p1)} \<in> ((set (map (\<lambda>(p1, p2). {(q, p1, target q p2), (q, p2, target q p1)})
              (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p)))))"
          using map_set[OF \<open>(p1,p1@p2) \<in> set (filter (\<lambda>(p1, p2). target q p1 \<in> fst d \<and> target q p2 \<in> fst d \<and> target q p1 \<noteq> target q p2) (prefix_pairs p))\<close>, of "(\<lambda>(p1, p2). {(q, p1, target q p2), (q, p2, target q p1)})"] 
          by force
        then have "(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
             and  "(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
          unfolding prefix_pair_tests_code[of q "m_traversal_paths_with_witness M q ?RepSets m"]
          using \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q ?RepSets m\<close>
          by blast+


        
        
          
        have "p1 \<in> tps q"
        proof -
          have "(q, p1) \<in> ((\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)))"
            using \<open>(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)\<close>
            by (simp add: rev_image_eqI)  
          then show ?thesis 
            unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
            by blast
        qed

        moreover have "(p1@p2) \<in> tps q"
        proof -
          have "(q, p1@p2) \<in> ((\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)))"
            using \<open>(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)\<close>
            by (simp add: rev_image_eqI) 
          then show ?thesis 
            unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
            by blast          
        qed

        moreover have "target q p1 \<in> rd_targets (q,(p1@p2))"
        proof -
          have "((q, p1@p2), target q p1) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
            using \<open>(q, p1@p2, target q p1) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)\<close>
            by (simp add: rev_image_eqI)
          then show ?thesis
            unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
            by blast
        qed

        moreover have "target q (p1@p2) \<in> rd_targets (q,p1)"
        proof -
          have "((q, p1), target q (p1@p2)) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)"
            using \<open>(q, p1, target q (p1@p2)) \<in> prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m)\<close>
            by (simp add: rev_image_eqI)
          then show ?thesis
            unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] 
            by blast
        qed
        
        ultimately show "(p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1))"
          by blast
      qed

      moreover have p4c2: "\<And> p1 p2 q' . p=p1@p2 \<Longrightarrow> q' \<in> image fst nodes_with_preambles \<Longrightarrow> target q p1 \<in> fst d \<Longrightarrow> q' \<in> fst d \<Longrightarrow> target q p1 \<noteq> q' \<Longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
      proof -
        fix p1 p2 q' assume "p=p1@p2" and "q' \<in> image fst nodes_with_preambles" and "target q p1 \<in> fst d" and "q' \<in> fst d" and "target q p1 \<noteq> q'"
        then have "q' \<in> fst ` d_reachable_states_with_preambles M"
          unfolding nodes_with_preambles_def by blast
        
        have "p1 \<in> set (prefixes p)"
          using \<open>p=p1@p2\<close> unfolding prefixes_set
          by simp 
        then have "(p1,q') \<in> Set.filter (\<lambda>(p1, q2). target q p1 \<in> fst d \<and> q2 \<in> fst d \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> fst ` d_reachable_states_with_preambles M)"
          using \<open>target q p1 \<in> fst d\<close> \<open>q' \<in> fst d\<close> \<open>q' \<in> image fst nodes_with_preambles\<close> \<open>target q p1 \<noteq> q'\<close> unfolding nodes_with_preambles_def
          by force
        then have "{(q, p1, q'), (q', [], target q p1)} \<subseteq> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)"
          using preamble_prefix_tests_code[of q "m_traversal_paths_with_witness M q ?RepSets m" "(fst ` d_reachable_states_with_preambles M)"]
          using \<open>(p,(fst d, snd d)) \<in> m_traversal_paths_with_witness M q ?RepSets m\<close>
          by blast
        then have "(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)"
             and  "(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)"
          by blast+

        have "p1 \<in> tps q"
          using \<open>(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)\<close>        
                \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
          unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
          by force

        moreover have "[] \<in> tps q'"
          using \<open>(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)\<close>        
                \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
          unfolding tps_alt_def[OF \<open>q' \<in> fst ` d_reachable_states_with_preambles M\<close>]
          by force

        moreover have "target q p1 \<in> rd_targets (q',[])"
          using \<open>(q', [], target q p1) \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)\<close>        
                \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
          unfolding rd_targets_alt_def[OF \<open>q' \<in> fst ` d_reachable_states_with_preambles M\<close>] 
          by force

        moreover have "q' \<in> rd_targets (q,p1)"
          using \<open>(q, p1, q') \<in> preamble_prefix_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M)\<close>        
                \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>
          unfolding rd_targets_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>]
          by force

        ultimately show "(p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))"
          by blast
      qed
      ultimately show "( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst nodes_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))))"
        by blast
    qed


    show ?thesis
      using p4a p4b p4c p4d by blast
  qed
  
  have p4: "(\<exists> RepSets .
        ((\<forall> q . q \<in> nodes M \<longrightarrow> (\<exists>d \<in> set RepSets. q \<in> fst d))
        \<and> (\<forall> d . d \<in> set RepSets \<longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})))
        \<and> (\<forall> q . q \<in> image fst nodes_with_preambles \<longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q RepSets m) \<subseteq> tps q)
        \<and> (\<forall> q p d . q \<in> image fst nodes_with_preambles \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q RepSets m \<longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst nodes_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1)))))))"
  proof 
    let ?RepSets = "(maximal_repetition_sets_from_separators_list M)"
    show "((\<forall> q . q \<in> nodes M \<longrightarrow> (\<exists>d \<in> set ?RepSets. q \<in> fst d))
        \<and> (\<forall> d . d \<in> set ?RepSets \<longrightarrow> ((fst d \<subseteq> nodes M) \<and> (snd d \<subseteq> fst d) \<and> (\<forall> q1 q2 . q1 \<in> fst d \<longrightarrow> q2 \<in> fst d \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {})))
        \<and> (\<forall> q . q \<in> image fst nodes_with_preambles \<longrightarrow> tps q \<subseteq> {p1 . \<exists> p2 d . (p1@p2,d) \<in> m_traversal_paths_with_witness M q ?RepSets m} \<and> fst ` (m_traversal_paths_with_witness M q ?RepSets m) \<subseteq> tps q)
        \<and> (\<forall> q p d . q \<in> image fst nodes_with_preambles \<longrightarrow> (p,d) \<in> m_traversal_paths_with_witness M q ?RepSets m \<longrightarrow> 
              ( (\<forall> p1 p2 p3 . p=p1@p2@p3 \<longrightarrow> p2 \<noteq> [] \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> target q (p1@p2) \<in> fst d \<longrightarrow> target q p1 \<noteq> target q (p1@p2) \<longrightarrow> (p1 \<in> tps q \<and> (p1@p2) \<in> tps q \<and> target q p1 \<in> rd_targets (q,(p1@p2)) \<and> target q (p1@p2) \<in> rd_targets (q,p1)))
              \<and> (\<forall> p1 p2 q' . p=p1@p2 \<longrightarrow> q' \<in> image fst nodes_with_preambles \<longrightarrow> target q p1 \<in> fst d \<longrightarrow> q' \<in> fst d \<longrightarrow> target q p1 \<noteq> q' \<longrightarrow> (p1 \<in> tps q \<and> [] \<in> tps q' \<and> target q p1 \<in> rd_targets (q',[]) \<and> q' \<in> rd_targets (q,p1))))))"
      using p4_witness by blast
  qed


  have "\<And> q1 q2 . q1 \<in> image fst nodes_with_preambles \<Longrightarrow> q2 \<in> image fst nodes_with_preambles \<Longrightarrow> q1 \<noteq> q2 \<Longrightarrow> atcs (q1,q2) \<noteq> {} \<Longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
  proof -
    fix q1 q2 assume "q1 \<in> image fst nodes_with_preambles" and "q2 \<in> image fst nodes_with_preambles" and "q1 \<noteq> q2" and "atcs (q1,q2) \<noteq> {}"
    then have "q1 \<in> fst ` d_reachable_states_with_preambles M"
         and  "q2 \<in> fst ` d_reachable_states_with_preambles M"
      unfolding nodes_with_preambles_def by blast+

    thm preamble_pair_tests.simps
    thm tps_alt_def[OF \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close>]

    (* TODO: extract and reuse *)
    have scheme : "\<And> x zs . m2f (set_as_map zs) x = {y . (x,y) \<in> zs}" 
      unfolding set_as_map_def by auto

    have "(q1,[],q2) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)"
      using \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>atcs (q1,q2) \<noteq> {}\<close>
      unfolding atcs_def scheme preamble_pair_tests.simps by force 

    have "atcs (q2,q1) \<noteq> {}"
      using \<open>atcs (q1,q2) \<noteq> {}\<close> p3 by force
    then have "(q2,[],q1) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)"
      using \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close> \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close> 
      unfolding atcs_def scheme preamble_pair_tests.simps by force

    have "[] \<in> tps q1"
    proof -
      have "(q1,[]) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
        using \<open>(q1,[],q2) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force
      then show ?thesis
        unfolding tps_alt_def[OF \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        by blast
    qed

    moreover have "[] \<in> tps q2"
    proof -
      have "(q2,[]) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
        using \<open>(q2,[],q1) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force
      then show ?thesis
        unfolding tps_alt_def[OF \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        by blast
    qed

    moreover have "q1 \<in> rd_targets (q2,[])"
    proof -
      have "((q2,[]),q1) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
        using \<open>(q2,[],q1) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force
      then show ?thesis
        unfolding rd_targets_alt_def[OF \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        by blast
    qed

    moreover have "q2 \<in> rd_targets (q1,[])"
    proof -
      have "((q1,[]),q2) \<in> (\<lambda>(q, p, y). ((q, p), y)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"
        using \<open>(q1,[],q2) \<in> preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M)\<close>
        by force
      then show ?thesis
        unfolding rd_targets_alt_def[OF \<open>q1 \<in> fst ` d_reachable_states_with_preambles M\<close>] 
        by blast
    qed

    ultimately show "([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[]))"
      by blast
  qed
  then have p5: "(\<forall> q1 q2 . q1 \<in> image fst nodes_with_preambles \<longrightarrow> q2 \<in> image fst nodes_with_preambles \<longrightarrow> q1 \<noteq> q2 \<longrightarrow> atcs (q1,q2) \<noteq> {} \<longrightarrow> ([] \<in> tps q1 \<and> [] \<in> tps q2 \<and> q1 \<in> rd_targets (q2,[]) \<and> q2 \<in> rd_targets (q1,[])))"
    by blast

  have p6: "\<And> q p . q \<in> image fst nodes_with_preambles \<Longrightarrow> p \<in> tps q \<Longrightarrow> path M q p"
  proof -
    fix q p assume "q \<in> image fst nodes_with_preambles" and "p \<in> tps q"

    have "q \<in> fst ` d_reachable_states_with_preambles M"
      using \<open>q \<in> image fst nodes_with_preambles\<close> unfolding nodes_with_preambles_def by assumption
    then have "q \<in> nodes M"
      by (metis (no_types, lifting) assms(1) d_reachable_states_with_preambles_soundness(2) image_iff prod.collapse)


    have * : "(\<And> q . q \<in> nodes M \<Longrightarrow> (\<exists>d \<in> set (maximal_repetition_sets_from_separators_list M). q \<in> fst d))"
    and  **: "(\<And> d . d \<in> set (maximal_repetition_sets_from_separators_list M) \<Longrightarrow> (snd d \<subseteq> fst d))"
      using p4_witness by simp+

    have ***: "\<And> q . q\<in>fst ` d_reachable_states_with_preambles M \<Longrightarrow> fst ` (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<subseteq> {p . path M q p}"
    proof - 
      fix q assume "q \<in> fst ` d_reachable_states_with_preambles M"
      then have "q \<in> nodes M"
        by (metis (no_types, lifting) assms(1) d_reachable_states_with_preambles_soundness(2) image_iff prod.collapse)
      show "fst ` (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m) \<subseteq> {p . path M q p}"
        using m_traversal_paths_with_witness_set[OF * ** \<open>q \<in> nodes M\<close>, of m] by force
    qed



    from \<open>p \<in> tps q\<close> consider 
      (a) "p \<in> fst ` m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m" |
      (b) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (prefix_pair_tests q (m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m))" |
      (c) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (\<Union>q\<in>fst ` d_reachable_states_with_preambles M.
              \<Union>mrsps\<in>{m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m}.
                 preamble_prefix_tests q mrsps (fst ` d_reachable_states_with_preambles M))" |
      (d) "(q, p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_pair_tests (fst ` d_reachable_states_with_preambles M) (fst ` r_distinguishable_state_pairs_with_separators M))"  
      unfolding tps_alt_def[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] by blast
    then show "path M q p"
    proof cases
      case a
      then show ?thesis using m_traversal_paths_with_witness_set[OF * ** \<open>q \<in> nodes M\<close>, of m] 
        by force
    next
      case b

      obtain p1 p2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})"
         and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m.
            (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2"
        using b
        unfolding prefix_pair_tests.simps by blast

      have "p = p1 \<or> p = p2"
        using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q, p1, target q p2), (q, p2, target q p1)})\<close> by auto

      obtain p' rd dr where "(p', rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m"
                      and   "(p1, p2) \<in> set (prefix_pairs p')"
        using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m.
            (p1, p2) \<in> set (prefix_pairs p) \<and> target q p1 \<in> rd \<and> target q p2 \<in> rd \<and> target q p1 \<noteq> target q p2\<close>
        by blast

      have "path M q p'"
        using ***[OF \<open>q \<in> fst ` d_reachable_states_with_preambles M\<close>] \<open>(p', rd, dr)\<in>m_traversal_paths_with_witness M q (maximal_repetition_sets_from_separators_list M) m\<close>
        by auto
      then have "path M q p1" and "path M q p2"
        using prefix_pairs_paths[OF \<open>(p1, p2) \<in> set (prefix_pairs p')\<close>]
        by blast+
      then show ?thesis using \<open>p = p1 \<or> p = p2\<close> 
        by auto
    next
      case c

      

      obtain q' where "q' \<in> fst ` d_reachable_states_with_preambles M"
                and   "(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M))"
        using c by blast

      obtain p1 q2  where "(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})"
         and "\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m.
            q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2"
        using \<open>(q,p) \<in> (\<lambda>(q, p, q'). (q, p)) ` (preamble_prefix_tests q' (m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m) (fst ` d_reachable_states_with_preambles M))\<close>
        unfolding preamble_prefix_tests_def
        by blast

      

      obtain p2 rd dr where "(p1@p2, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m"
                      and   "q2 \<in> fst ` d_reachable_states_with_preambles M"
        using \<open>\<exists>(p, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m.
            q2 \<in> fst ` d_reachable_states_with_preambles M \<and> (\<exists>p2. p = p1 @ p2) \<and> target q' p1 \<in> rd \<and> q2 \<in> rd \<and> target q' p1 \<noteq> q2\<close>
        by blast

      consider (a) "q = q' \<and> p = p1" | (b) "q = q2 \<and> p = []"
        using \<open>(q,p) \<in> ((\<lambda>(q, p, q'). (q, p)) `{(q', p1, q2), (q2, [], target q' p1)})\<close> by auto
      then show ?thesis proof cases
        case a
        then show ?thesis
          using ***[OF \<open>q' \<in> fst ` d_reachable_states_with_preambles M\<close>] \<open>(p1@p2, rd, dr)\<in>m_traversal_paths_with_witness M q' (maximal_repetition_sets_from_separators_list M) m\<close>
          by fastforce
      next
        case b
        then show ?thesis 
          using \<open>q2 \<in> fst ` d_reachable_states_with_preambles M\<close> unfolding d_reachable_states_with_preambles_def by force
      qed
    next
      case d 
      then have "q \<in> (fst ` d_reachable_states_with_preambles M) \<and> p = []"
        unfolding preamble_pair_tests.simps by auto
      then show ?thesis unfolding d_reachable_states_with_preambles_def by force
    qed
  qed

  show ?thesis
    unfolding \<open>calculate_test_suite_example M m = Test_Suite nodes_with_preambles tps rd_targets atcs\<close> is_sufficient_for_reduction_testing.simps
    using p1 p2 p3 p4 p5 p6 by blast
qed


end