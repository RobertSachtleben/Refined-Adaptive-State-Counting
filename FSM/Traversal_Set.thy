theory Traversal_Set
imports R_Distinguishability Helper_Algorithms 
begin

section \<open>Traversal Sets for State Counting\<close>

subsection \<open>Calculating Traversal Paths\<close>


fun m_traversal_paths_up_to_length :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "m_traversal_paths_up_to_length M q D m k = paths_up_to_length_or_condition M q k (\<lambda> p . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) []"

fun m_traversal_paths :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> 'a Transition list list" where
  "m_traversal_paths M q D m = m_traversal_paths_up_to_length M q D m (Suc (size M * m))"

value "m_traversal_paths_up_to_length M_ex_H 1 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 10000"
value "m_traversal_paths_up_to_length M_ex_H 3 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 10000"
value "m_traversal_paths_up_to_length M_ex_H 4 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 10000"

value "m_traversal_paths M_ex_H 1 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 "
value "m_traversal_paths M_ex_H 3 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 "
value "m_traversal_paths M_ex_H 4 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 "

value "m_traversal_paths_up_to_length M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 10000"




  
lemma m_traversal_paths_up_to_length_max_length :
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> D . q \<in> fst d"
  and     "\<forall> d \<in> D . snd d \<subseteq> fst d"
  and     "q \<in> nodes M"
  and     "p \<in> set (m_traversal_paths_up_to_length M q D m k)"
shows "length p \<le> Suc ((size M) * m)"
proof (rule ccontr)
  assume "\<not> length p \<le> Suc (FSM.size M * m)"

  let ?f = "(\<lambda> p . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"

  have "path M q []" using assms(3) by auto
  
  have "path M q p"
        and "length p \<le> k"
        and "?f p"
        and "\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')"
    using paths_up_to_length_or_condition_path_set_nil[OF assms(3), of k ?f] assms(4) by auto
  

  have "\<And> p . path M q p \<Longrightarrow> set (map t_target p) \<subseteq> nodes M"
  proof - 
    fix p assume "path M q p"
    then show "set (map t_target p) \<subseteq> nodes M"
    proof (induction p rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a p)
      then show ?case using path_target_is_node[OF \<open>path M q (p @ [a])\<close>]
        by (metis (mono_tags, lifting) dual_order.trans set_subset_Cons visited_states.elims visited_states_are_nodes)
    qed
  qed
  
  have *: "\<And> p . path M q p \<Longrightarrow> length p = (\<Sum> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) p))"
  proof -
    fix p assume "path M q p"
    then show "length p = (\<Sum> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) p))"
    proof (induction p rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc x xs)
      then have "length xs = (\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) xs))"
        by auto
      
      have *: "t_target x \<in> nodes M"
        using \<open>path M q (xs @ [x])\<close> by auto
      then have **: "length (filter (\<lambda>t. t_target t = t_target x) (xs @ [x])) = Suc (length (filter (\<lambda>t. t_target t = t_target x) xs))"
        by auto
  
      have "\<And> q . q \<in> nodes M \<Longrightarrow> q \<noteq> t_target x \<Longrightarrow> length (filter (\<lambda>t. t_target t = q) (xs @ [x])) = length (filter (\<lambda>t. t_target t = q) xs)"
        by simp
      then have ***: "(\<Sum>q\<in>nodes M - {t_target x}. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) = (\<Sum>q\<in>nodes M - {t_target x}. length (filter (\<lambda>t. t_target t = q) xs))"
        using nodes_finite[of M]
        by (metis (no_types, lifting) DiffE insertCI sum.cong)
  
      have "(\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) = (\<Sum>q\<in>nodes M - {t_target x}. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) + (length (filter (\<lambda>t. t_target t = t_target x) (xs @ [x])))"
        using * nodes_finite[of M]
      proof -
        have "(\<Sum>a\<in>insert (t_target x) (nodes M). length (filter (\<lambda>p. t_target p = a) (xs @ [x]))) = (\<Sum>a\<in>nodes M. length (filter (\<lambda>p. t_target p = a) (xs @ [x])))"
          by (simp add: \<open>t_target x \<in> nodes M\<close> insert_absorb)
        then show ?thesis
          by (simp add: \<open>finite (nodes M)\<close> sum.insert_remove)
      qed  
      moreover have "(\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) xs)) = (\<Sum>q\<in>nodes M - {t_target x}. length (filter (\<lambda>t. t_target t = q) xs)) + (length (filter (\<lambda>t. t_target t = t_target x) xs))"
        using * nodes_finite[of M]
      proof -
        have "(\<Sum>a\<in>insert (t_target x) (nodes M). length (filter (\<lambda>p. t_target p = a) xs)) = (\<Sum>a\<in>nodes M. length (filter (\<lambda>p. t_target p = a) xs))"
          by (simp add: \<open>t_target x \<in> nodes M\<close> insert_absorb)
        then show ?thesis
          by (simp add: \<open>finite (nodes M)\<close> sum.insert_remove)
      qed  
  
      ultimately have "(\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) (xs @ [x]))) = Suc (\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) xs))"
        using ** *** by auto
        
      then show ?case
        by (simp add: \<open>length xs = (\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) xs))\<close>) 
    qed
  qed

  let ?p = "take (Suc (m * size M)) p"
  let ?p' = "drop (Suc (m * size M)) p"
  have "path M q ?p"
    using \<open>path M q p\<close> using path_prefix[of M q ?p "drop (Suc (m * size M)) p"]
    by simp
  have "?p' \<noteq> []"
    using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
    by (simp add: mult.commute) 

  have "\<exists> q \<in> nodes M . length (filter (\<lambda>t . t_target t = q) ?p) \<ge> Suc m"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>nodes M. Suc m \<le> length (filter (\<lambda>t. t_target t = q) ?p))"
    then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) < Suc m"
      by auto
    then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m"
      by auto
    
    have "(\<Sum>q\<in>nodes M. length (filter (\<lambda>t. t_target t = q) ?p)) \<le> (\<Sum>q\<in>nodes M . m)"
      using \<open>\<forall> q \<in> nodes M . length (filter (\<lambda>t. t_target t = q) ?p) \<le> m\<close> by (meson sum_mono) 
    then have "length ?p \<le> m * (size M)"
      using *[OF \<open>path M q ?p\<close>] 
      using nodes_finite[of M] unfolding size_def
      by (simp add: mult.commute)

    then show "False"
      using \<open>\<not> length p \<le> Suc (FSM.size M * m)\<close>
      by (simp add: mult.commute) 
  qed

  then obtain q where "q \<in> nodes M"
                  and "length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m" 
    by blast
  then obtain d where "d \<in> D"
                  and "q \<in> fst d"
    using assms(1) by blast
  then have "\<And> t . t_target t = q \<Longrightarrow> t_target t \<in> fst d" by auto
  then have "length (filter (\<lambda> t . t_target t = q) ?p) \<le> length (filter (\<lambda> t . t_target t \<in> fst d) ?p)"
    using filter_length_weakening[of "\<lambda> t . t_target t = q" "\<lambda> t . t_target t \<in> fst d"] by auto
  then have "Suc m \<le> length (filter (\<lambda>t. t_target t \<in> fst d) ?p)"
    using \<open>length (filter (\<lambda> t . t_target t = q) ?p) \<ge> Suc m\<close> by auto
  then have "?f ?p"
    using assms(2)
    by (meson Suc_le_mono \<open>d \<in> D\<close> diff_le_self le_trans) 

  then have "p = ?p@?p' \<and> ?p' \<noteq> [] \<and> ?f ?p"
    using \<open>?p' \<noteq> []\<close> by auto

  then show "False"
    using \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')\<close> by blast
qed
    


lemma m_traversal_paths_set :
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> D . q \<in> fst d"
    and     "\<forall> d \<in> D . snd d \<subseteq> fst d"
    and     "q \<in> nodes M"
  shows "set (m_traversal_paths M q D m) = {p . path M q p \<and> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))
                                                     \<and> (\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p') \<ge> Suc (m - (card (snd d)))))}"
        (is "?MTP = ?P")
proof -
  let ?f = "\<lambda> p . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))"

  have "path M q []"
    using assms(3) by auto

  have "\<And> p . p \<in> ?MTP \<Longrightarrow> p \<in> ?P"
    using paths_up_to_length_or_condition_path_set_nil[of  q M "(Suc (size M * m))" ?f] assms(3) 
    unfolding m_traversal_paths.simps m_traversal_paths_up_to_length.simps by blast
  moreover have "\<And> p . p \<in> ?P \<Longrightarrow> p \<in> ?MTP"
  proof -
    fix p assume "p \<in> ?P"
    then have "path M q p"
          and "?f p"
          and "\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')"
      by blast+
    then have "p \<in> set (m_traversal_paths_up_to_length M q D m (length p))"
      using paths_up_to_length_or_condition_path_set_nil[of q M "length p" ?f] assms(3) by auto
    then have "length p \<le> Suc (size M * m)"
      using m_traversal_paths_up_to_length_max_length[OF assms] by blast
    
    show "p \<in> ?MTP"
      using \<open>path M q p\<close> \<open>length p \<le> Suc (size M * m)\<close> \<open>?f p\<close> \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')\<close>
      using paths_up_to_length_or_condition_path_set_nil[of q M "(Suc (size M * m))" ?f]  
      unfolding m_traversal_paths.simps m_traversal_paths_up_to_length.simps
      using assms(3) by blast 
  qed
  ultimately show ?thesis
    by (meson subsetI subset_antisym) 
qed




value "maximal_repetition_sets_from_separators M_ex_H"
value "m_traversal_paths M_ex_H  1 (maximal_repetition_sets_from_separators M_ex_H) 4"
value "m_traversal_paths M_ex_H  3 (maximal_repetition_sets_from_separators M_ex_H) 4"
value "m_traversal_paths M_ex_H  4 (maximal_repetition_sets_from_separators M_ex_H) 4"

value "m_traversal_paths M_ex_9  3 (maximal_repetition_sets_from_separators M_ex_9) 4"





lemma maximal_repetition_sets_from_separators_cover :
  assumes "q \<in> nodes M"
  shows "\<exists> d \<in> (maximal_repetition_sets_from_separators M) . q \<in> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  using maximal_pairwise_r_distinguishable_state_sets_from_separators_cover[OF assms] by auto

lemma maximal_repetition_sets_from_separators_d_reachable_subset :
  shows "\<forall> d \<in> (maximal_repetition_sets_from_separators M) . snd d \<subseteq> fst d"
  unfolding maximal_repetition_sets_from_separators_def
  by auto

lemma m_traversal_paths_set_appl : 
  assumes "q \<in> nodes M"
  shows "set (m_traversal_paths M q (maximal_repetition_sets_from_separators M) m) =
          {p. path M q p \<and>
              (\<exists>d\<in>maximal_repetition_sets_from_separators M.
                  Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) \<and>
              (\<forall>p' p''.
                  p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow>
                  \<not> (\<exists>d\<in>maximal_repetition_sets_from_separators M.
                         Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')))}"
  using m_traversal_paths_set[of M "maximal_repetition_sets_from_separators M", OF _ _ assms]
          maximal_repetition_sets_from_separators_d_reachable_subset 
    by (metis (no_types, lifting) maximal_repetition_sets_from_separators_cover)




 


subsection \<open>Calculating Traversal Sets\<close>

(* TODO: decide whether to omit calculations as presented by Petrenko and only use traversal paths *)

(*

fun N :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> Input list list" where
  "N M q D m = add_prefixes (map (\<lambda> p . map t_input p) (m_traversal_paths M q D m))"

value "remdups (N M_ex_H 1 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4)"


fun T :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> (Input \<times> Output) list list" where
  "T M q D m = add_prefixes (map (\<lambda> p . p_io p) (m_traversal_paths M q D m))"

value "remdups (T M_ex_H 1 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4)" 

fun Traces :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "Traces M q D m \<alpha> = filter (\<lambda>io . map fst io \<in> set (prefixes \<alpha>)) (T M q D m)"

value "remdups (Traces M_ex_H 1 {({1,3,4},{1,3,4}),({2,3,4},{3,4})} 4 [1,1])"

value "remdups (T M_ex_9 1 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5)"
value "remdups (Traces M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1])"


definition Traces_not_to_cut :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "Traces_not_to_cut M q D m \<alpha> = (let TR = (Traces M q D m \<alpha>) in filter (\<lambda> \<beta> . \<exists> \<gamma> \<in> set TR . \<beta> \<in> set (prefixes \<gamma>) \<and> length \<gamma> = length \<alpha>) TR)"

definition Traces_to_cut :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "Traces_to_cut M q D m \<alpha> = (let TRTC = set (Traces M q D m \<alpha>) - set (Traces_not_to_cut M q D m \<alpha>) in 
                                filter (\<lambda> \<beta> . (\<exists> \<beta>' \<in> TRTC . \<beta>' \<in> set (prefixes \<beta>) \<and> \<beta>' \<noteq> \<beta> )) (Traces M q D m \<alpha>))"

definition Traces_simplified :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> Input list \<Rightarrow> (Input \<times> Output) list list" where
  "Traces_simplified M q D m \<alpha> = filter (\<lambda> \<beta> . \<beta> \<notin> set (Traces_to_cut M q D m \<alpha>)) (Traces M q D m \<alpha>)"

value "remdups (Traces_to_cut M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1])"
value "remdups (Traces_not_to_cut M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1])"
value "remdups (Traces_simplified M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1])"


(* TODO: move *)
fun insert_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_by f x [] = [x]" |
  "insert_by f x (y#ys) = (if f x y then x#y#ys else y#(insert_by f x ys))"

fun sort_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sort_by f [] = []" | 
  "sort_by f (x#xs) = insert_by f x (sort_by f xs)"

fun lte_io_seq :: "(Input \<times> Output) list \<Rightarrow> (Input \<times> Output) list \<Rightarrow> bool" where
  "lte_io_seq [] [] = True" |
  "lte_io_seq (x#xs) [] = False" |
  "lte_io_seq [] (y#ys) = True" |
  "lte_io_seq (x#xs) (y#ys) = (length xs < length ys 
                              \<or> (length xs = length ys \<and> fst x < fst y) 
                              \<or> (length xs = length ys \<and> fst x = fst y \<and> snd x < snd y) 
                              \<or> (length xs = length ys \<and> fst x = fst y \<and> snd x = snd y \<and> lte_io_seq xs ys))"
                                  
  (*"lte_io_seq (x#xs) (y#ys) = (if x = y then lte_io_seq xs ys else (fst x < fst y \<or> (fst x = fst y \<and> snd x \<le> snd y)))"*)

fun sort_io_seqs :: "(Input \<times> Output) list list \<Rightarrow> (Input \<times> Output) list list" where
  "sort_io_seqs ios = sort_by lte_io_seq ios" 

value "sort_io_seqs (remdups (Traces_not_to_cut M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1]))"
value "sort_io_seqs (remdups (Traces_to_cut M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1]))"
value "sort_io_seqs (remdups (Traces_simplified M_ex_9 0 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 5 [1,1,1,1]))"



lemma N_set : 
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> D . q \<in> fst d"
    and     "\<forall> d \<in> D . snd d \<subseteq> fst d"
    and     "q \<in> nodes M"
  shows "set (N M q D m) = {xs . (\<exists> io \<in> LS M q . xs = map fst io) \<and>
                                       (\<forall> p . (path M q p \<and> xs = map t_input p \<and> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))) \<and>
                                       (\<forall> xs' . (\<exists> xs'' . xs' @ xs'' = xs \<and> xs'' = []) \<longrightarrow> \<not> (\<forall> p . (path M q p \<and> xs' = map t_input p \<and> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))))}" 
proof -
  have "set (N M q D m) = {xs'. \<exists>xs''. xs' @ xs'' \<in> set (map (map t_input) (m_traversal_paths M q D m))}"
    unfolding N.simps
    using add_prefixes_set[of "(map (map t_input) (m_traversal_paths M q D m))"] by assumption
  also have "\<dots> = {xs'. \<exists>xs''. \<exists> p \<in> set (m_traversal_paths M q D m) . xs'@xs'' = map t_input p}"
  proof -
    have "\<And> xs ps . xs \<in> set (map (map t_input) ps) \<longleftrightarrow> (\<exists> p \<in> set ps . xs = map t_input p)"
      by auto
    then show ?thesis by blast
  qed
  also have "\<dots> = {xs'. \<exists>xs''. \<exists> p \<in> {p. path M q p \<and>
      (\<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) \<and>
      (\<forall>p' p''.
          p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow>
          \<not> (\<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p')))} . xs'@xs'' = map t_input p}"
    using m_traversal_paths_set[OF assms, of m] by auto

  (* TODO *)
  also have "\<dots> = {xs . (\<exists> io \<in> LS M q . xs = map fst io) \<and>
                                       (\<forall> p . (path M q p \<and> xs = map t_input p \<and> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))) \<and>
                                       (\<forall> xs' . (\<exists> xs'' . xs' @ xs'' = xs \<and> xs'' = []) \<longrightarrow> \<not> (\<forall> p . (path M q p \<and> xs' = map t_input p \<and> (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))))}"
    sorry
  finally show ?thesis by blast
qed

lemma Traces_set : "set (Traces M q D m \<alpha>) = {io \<in> set (T M q D m) . map fst io \<in> set (prefixes \<alpha>)}"
  sorry

end (*




lemma m_traversal_paths_up_to_length_max_length :
  assumes "\<forall> q \<in> nodes M . \<exists> d \<in> D . q \<in> fst d"
  and     "\<forall> d \<in> D . snd d \<subseteq> fst d"
  and     "q \<in> nodes M"
  and     "p \<in> set (m_traversal_paths_up_to_length M q D m k)"
shows "length p \<le> Suc ((size M) * m)"
proof -
  let ?f = "(\<lambda> p . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"

  have "path M q []" using assms(3) by auto
  
  have "path M q p"
        and "length p \<le> k"
        and "?f p"
        and "\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')"
    using paths_up_to_length_or_condition_path_set_nil[OF \<open>path M q []\<close>, of k ?f] assms(4) by auto

  have "\<forall> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<le> Suc (m - (card (snd d)))"
  proof (rule ccontr)
    assume "\<not> (\<forall>d\<in>D. length (filter (\<lambda>t. t_target t \<in> fst d) p) \<le> Suc (m - card (snd d)))"
    then obtain d where *:  "d \<in> D"
                    and **: "length (filter (\<lambda>t. t_target t \<in> fst d) p) > Suc (m - card (snd d))"
      using leI by blast

    show "False"
    proof (cases p rule: rev_cases)
      case Nil
      then show ?thesis using ** by auto
    next
      case (snoc p' t)
      then have "length (filter (\<lambda>t. t_target t \<in> fst d) p') \<ge> Suc (m - card (snd d))" using **
        by (metis (no_types, lifting) Suc_leI Suc_less_eq2 butlast.simps(2) butlast_append butlast_snoc diff_Suc_1 filter.simps(1) filter.simps(2) filter_append length_butlast less_imp_le_nat)
      then have "?f p'"
        using * by auto
      then have "p = p' @ [t] \<and> [t] \<noteq> [] \<and> ?f p'"
        using snoc by auto
      then show "False" using \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')\<close> by blast
    qed
  qed

  then have "\<forall> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<le> Suc m"
    by auto
  then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t . t_target t = q) p) \<le> Suc m"
    using assms(1)

  then have "\<exists> q . 

  then have "\<forall> q \<in> nodes M . length (filter (\<lambda>t . t_target t = q) p) \<le> Suc (m - (card (snd d))) 

end (*
    have "length (filter (\<lambda>t. t_target t \<in> fst d) (butlast p)) \<ge> Suc (m - card (snd d))"
    proof (cases p rule: rev_cases)
      case Nil
      then show ?thesis using ** by auto
    next
      case (snoc p' t)
      then show ?thesis using **
        by (metis (no_types, lifting) Suc_leI Suc_less_eq2 butlast.simps(2) butlast_append butlast_snoc diff_Suc_1 filter.simps(1) filter.simps(2) filter_append length_butlast less_imp_le_nat)
    qed

    then have "?f (butlast p)"
      
    then have "p \<noteq> []" by auto
    then have "length (filter (\<lambda>t. t_target t \<in> fst d) (butlast p)) \<ge> Suc (m - card (snd d))"
      using ** 
      
    using \<open>\<forall>p' p''. p = p' @ p'' \<and> p'' \<noteq> [] \<longrightarrow> \<not> (?f p')\<close> 

(* calculate maximal sets of pairwise r_distinguishable states and their respective subsets of d-reachable states *)

end (*


(* N - helper *)
(*
fun m_traversal_sequences' :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list set \<Rightarrow> Input list set \<Rightarrow> Input list set" where
  "m_traversal_sequences' M q D m 0 current finished = finished" |
  "m_traversal_sequences' M q D m (Suc k) current finished = 
    m_traversal_sequences' M q D m k
      (image (\<lambda>xsx . (fst xsx)@[snd xsx]) ({xs \<in> current . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<times> (set (inputs M))))
      (finished \<union> {xs \<in> current . \<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))})"

value "m_traversal_sequences' M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 3 {[]} {}"
value "m_traversal_sequences' M_ex_9 2 {({0},{0}),({1},{}),({2},{2}),({3},{3})} 4 100  {[]} {}"*)

fun lists_up_to_length :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list list" where
  "lists_up_to_length xs 0 = [[]]" |
  "lists_up_to_length xs (Suc n) = (lists_up_to_length xs n) @ (lists_of_length xs (Suc n))"

lemma lists_up_to_length_list_set : "set (lists_up_to_length xs k) = {xs' . length xs' \<le> k \<and> set xs' \<subseteq> set xs}"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then show ?case 
    using lists_of_length_list_set[of xs "Suc k"] unfolding lists_up_to_length.simps by auto
qed


(* TODO: extremely slow *)
fun m_traversal_sequences_list :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list list" where
  "m_traversal_sequences_list M q D m k = (filter ((\<lambda> xs . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                          \<not>(\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))))
                                          (lists_up_to_length (inputs M) k))"

lemma m_traversal_sequences_list_set :
  "set (m_traversal_sequences_list M q D m k) = {xs . length xs \<le> k \<and> set xs \<subseteq> set (inputs M) \<and>
                                                  (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                  \<not>(\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
  unfolding m_traversal_sequences_list.simps using lists_up_to_length_list_set[of "inputs M" k] by force

value "m_traversal_sequences_list M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 4"


lemma m_traversal_sequences_bound :
  assumes "\<And> q . q \<in> nodes M \<Longrightarrow> \<exists> d \<in> D . q \<in> fst d"
      and "path M q p"
      and "length p \<ge> Suc ((size M)*m)"
    shows "\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))"
  sorry
  


(* TODO: very awkward, try forward approach similar to distinct path calculation? *)
fun m_traversal_sequences' :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> ('a set \<times> 'a set) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Input list set \<Rightarrow> Input list set \<Rightarrow> Input list set" where
  "m_traversal_sequences' M q D m 0 current finished = finished" |
  "m_traversal_sequences' M q D m (Suc k) current finished = 
    m_traversal_sequences' M q D m k
      ({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (current \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})
      (finished \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (current \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"

value "m_traversal_sequences' M_ex_9 2 {({0,2,3},{0,2,3}),({1,2,3},{2,3})} 4 3 {[]} {}"
(*value "m_traversal_sequences' M_ex_9 2 {({0},{0}),({1},{}),({2},{2}),({3},{3})} 4 100  {[]} {}"*)


lemma m_traversal_sequences'_set_internal : 
  assumes "\<And> xs p . xs \<in> X \<Longrightarrow> \<not> (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"
  shows "m_traversal_sequences' M q D m k X Y = Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> X \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
using assms proof (induction k arbitrary: X Y)
  case 0
  then show ?case unfolding m_traversal_sequences'.simps by force
next
  case (Suc k)

  have *: "(\<And>xs. xs \<in> {xs \<in> (\<lambda>xsx. fst xsx @ [snd xsx]) ` (X \<times> set (inputs M)).
               \<not> (\<forall>p\<in>set (paths_for_input M q xs).
                      \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))} \<Longrightarrow>
         \<not> (\<forall>p\<in>set (paths_for_input M q xs).
                \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)))"
    by blast

  have "m_traversal_sequences' M q D m (Suc k) X Y =
          m_traversal_sequences' M q D m k
            ({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})
            (Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
    (is "?m1 = m_traversal_sequences' M q D m k ?X ?Y")
    by auto

  moreover have "m_traversal_sequences' M q D m k ?X ?Y = 
          ?Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> ?X \<and>
                  (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                  \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
    using Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                     "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"]
    
          *
    by blast
  

  moreover have 
    "{xs' @ xs |xs' xs. set xs \<subseteq> set (inputs M) \<and> length xs \<le> Suc k \<and>  xs' \<in> X \<and>
           (\<forall>p \<in> set (paths_for_input M q (xs' @ xs)). \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p)) \<and>
           \<not>(\<forall>p \<in> set (paths_for_input M q (butlast (xs' @ xs))). \<exists>d\<in>D. Suc (m - card (snd d)) \<le> length (filter (\<lambda>t. t_target t \<in> fst d) p))}
    = {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}
        \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and> xs' \<in> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<and>
            (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
            \<not>(\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
    (is "?S1 = ?S2")
  proof 
    show "?S1 \<subseteq> ?S2"
    
    

end (*
  ultimately show ?case by auto
qed




  note Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                 "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})",
              OF ]

  show ?case unfolding m_traversal_sequences'.simps 
    using Suc.IH[of "({xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"
                 "(Y \<union> {xs \<in> (image (\<lambda>xsx . (fst xsx)@[snd xsx]) (X \<times> set (inputs M))) . (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))})"]
          *  
qed


lemma m_traversal_sequences'_set_internal : 
  (*assumes "q \<in> nodes M"*)
  (*assumes "\<And> xs p . xs \<in> X \<Longrightarrow> \<not> (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))"*)
  assumes "X \<inter> Y = {}"
  shows "m_traversal_sequences' M q D m (Suc k) X Y = Y \<union> {xs'@xs | xs' xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> (Suc k) \<and> xs' \<in> X \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (xs'@xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (butlast (xs'@xs))) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
using assms proof (induction k arbitrary: X Y)
  case 0
  then show ?case unfolding m_traversal_sequences'.simps by forc
next
  case (Suc k)
  note Suc.IH[of "(image (\<lambda>xsx . (fst xsx)@[snd xsx]) ({xs \<in> X . \<not>(\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))} \<times> (set (inputs M))))"
                 "(Y \<union> {xs \<in> X . \<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))})"]
  then show ?case unfolding m_traversal_sequences'.simps 
qed



lemma m_traversal_sequences'_set : 
  (*assumes "q \<in> nodes M"*)
  shows "m_traversal_sequences' M q D m k {[]} {} = {xs . set xs \<subseteq> set (inputs M) \<and> length xs \<le> k \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q xs) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d))))) \<and>
                                                      (\<forall> p \<in> set (paths_for_input M q (butlast xs)) . (\<exists> d \<in> D . length (filter (\<lambda>t . t_target t \<in> fst d) p) \<ge> Suc (m - (card (snd d)))))}"
proof (induction k arbitrary: q)
  case 0
  
  then show ?case unfolding m_traversal_sequences'.simps by force 
next
  case (Suc k)
  then show ?case unfolding m_traversal_sequences'.simps sorry
qed


(* N *)
fun m_traversal_sequences :: "('a,'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> Input list set" where
  "m_traversal_sequences M q D m = m_traversal_sequences' M q D m (Suc ((size M) * m)) {[]} {}"

*)*)*)*)*)

end

