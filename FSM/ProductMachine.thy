theory ProductMachine
imports FSM

begin


subsection \<open>Product Machine\<close>

fun product_transitions :: "('state1, 'b) FSM_scheme \<Rightarrow> ('state2, 'c) FSM_scheme \<Rightarrow> ('state1 \<times> 'state2) Transition list" where
  "product_transitions A B = map (\<lambda> (t1,t2). ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))) (filter (\<lambda> (t1,t2) . t_input t1 = t_input t2 \<and> t_output t1 = t_output t2) (cartesian_product_list (wf_transitions A) (wf_transitions B)))"


value "product_transitions M_ex M_ex'"





    

lemma product_transitions_alt1 : "set (product_transitions A B) = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
proof 
  show "set (product_transitions A B) \<subseteq> {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
  proof 
    fix x assume "x \<in> set (product_transitions A B)"
    then obtain t1 t2 where "x = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
                        and "t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
                        and "(t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B))"
      by force
    then show "x \<in> {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}" by blast
  qed

  show "{((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2} \<subseteq> set (product_transitions A B)"
    by force
qed

lemma product_transitions_alt2 : "set (product_transitions A B) = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . t1 \<in> set (wf_transitions A) \<and> t2 \<in> set (wf_transitions B) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
(is "?P = ?A2")
proof -
  have "?P = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . (t1,t2) \<in> set (cartesian_product_list (wf_transitions A) (wf_transitions B)) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
    using product_transitions_alt1 by assumption
  also have "... = ?A2" by force
  finally show ?thesis by auto
qed

lemma product_transitions_alt3 : "set (product_transitions A B) = {((q1,q2),x,y,(q1',q2')) | q1 q2 x y q1' q2' . (q1,x,y,q1') \<in> set (wf_transitions A) \<and> (q2,x,y,q2') \<in> set (wf_transitions B)}"
(is "?P = ?A3")
proof -
  have "?P = {((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1, t_target t2)) | t1 t2 . t1 \<in> set (wf_transitions A) \<and> t2 \<in> set (wf_transitions B) \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2}"
    using product_transitions_alt2 by assumption
  also have "... = ?A3" by force
  finally show ?thesis by simp
qed


fun product :: "('state1, 'b) FSM_scheme \<Rightarrow> ('state2, 'c) FSM_scheme \<Rightarrow> (('state1 \<times> 'state2), 'b) FSM_scheme" where
  "product A B =
  \<lparr>
    initial = (initial A, initial B),
    inputs = (inputs A) @ (inputs B),
    outputs = (outputs A) @ (outputs B),
    transitions = product_transitions A B,
    \<dots> = FSM.more A    
  \<rparr>"


value "product M_ex M_ex'"

abbreviation(input) "left_path p \<equiv> map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p"
abbreviation(input) "right_path p \<equiv> map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p"
abbreviation(input) "zip_path p1 p2 \<equiv> (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))"


lemma product_simps[simp]:
  "initial (product A B) = (initial A, initial B)"  
  "inputs (product A B) = inputs A @ inputs B"
  "outputs (product A B) = outputs A @ outputs B"
  "transitions (product A B) = product_transitions A B"
unfolding product_def by simp+




lemma product_transitions_io_valid :
  "set (product_transitions A B) = hIO (product A B)"
proof -
  have "\<And> t . t \<in> set (product_transitions A B) \<Longrightarrow> t \<in> hIO (product A B)"
  proof -
    fix t assume *: "t \<in> set (product_transitions A B)"
    then obtain t1 t2 where "t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)"
                        and "t1 \<in> h A \<and> t2 \<in> h B \<and> t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
      using product_transitions_alt2[of A B] by blast
    then have "is_io_valid_transition (product A B) t"
      by auto
    then show "t \<in> hIO (product A B)" using *
      by (metis io_valid_transition_simp product_simps(4))
  qed
  moreover have "\<And> t . t \<in> hIO (product A B) \<Longrightarrow>  t \<in> set (product_transitions A B)"
    by (metis io_valid_transition_simp product_simps(4))
  ultimately show ?thesis by blast
qed
  

lemma product_transition_hIO :
  "((q1,q2),x,y,(q1',q2')) \<in> hIO (product A B) \<longleftrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B"
  using product_transitions_io_valid[of A B] product_transitions_alt3[of A B] by blast





lemma zip_path_last : "length xs = length ys \<Longrightarrow> (zip_path (xs @ [x]) (ys @ [y])) = (zip_path xs ys)@(zip_path [x] [y])"
  by (induction xs ys rule: list_induct2; simp)

lemma product_path_from_paths :
  assumes "path A (initial A) p1"
      and "path B (initial B) p2"
      and "p_io p1 = p_io p2"
    shows "path (product A B) (initial (product A B)) (zip_path p1 p2)"
      and "target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))"
proof -
  have "initial (product A B) = (initial A, initial B)" by auto
  then have "(initial A, initial B) \<in> nodes (product A B)"
    by (metis nodes.initial) 

  have "length p1 = length p2" using assms(3)
    using map_eq_imp_length_eq by blast 
  then have c: "path (product A B) (initial (product A B)) (zip_path p1 p2) \<and> target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))"
    using assms proof (induction p1 p2 rule: rev_induct2)
    case Nil
    
    then have "path (product A B) (initial (product A B)) (zip_path [] [])" 
      using \<open>initial (product A B) = (initial A, initial B)\<close> \<open>(initial A, initial B) \<in> nodes (product A B)\<close>
      by (metis Nil_is_map_conv path.nil zip_Nil)
    moreover have "target (zip_path [] []) (initial (product A B)) = (target [] (initial A), target [] (initial B))"
      using \<open>initial (product A B) = (initial A, initial B)\<close> by auto
    ultimately show ?case by fast
  next
    case (snoc x xs y ys)
    
    have "path A (initial A) xs" using snoc.prems(1) by auto
    moreover have "path B (initial B) ys" using snoc.prems(2) by auto
    moreover have "p_io xs = p_io ys" using snoc.prems(3) by auto
    ultimately have *:"path (product A B) (initial (product A B)) (zip_path xs ys)" 
                and **:"target (zip_path xs ys) (initial (product A B)) = (target xs (initial A), target ys (initial B))" 
      using snoc.IH by blast+
    then have "(target xs (initial A), target ys (initial B)) \<in> nodes (product A B)"
      by (metis (no_types, lifting) path_target_is_node)
    then have "(t_source x, t_source y) \<in> nodes (product A B)"
      using snoc.prems(1-2)  by (metis path_cons_elim path_suffix) 

    have "x \<in> h A" using snoc.prems(1) by auto
    moreover have "y \<in> h B" using snoc.prems(2) by auto
    moreover have "t_input x = t_input y" using snoc.prems(3) by auto
    moreover have "t_output x = t_output y" using snoc.prems(3) by auto
    ultimately have "((t_source x, t_source y), t_input x, t_output x, (t_target x, t_target y)) \<in> hIO (product A B)"
    proof -
      have f1: "{((t_source p, t_source pa), t_input p, t_output p, t_target p, t_target pa) | p pa. p \<in> set (wf_transitions A) \<and> pa \<in> set (wf_transitions B) \<and> t_input p = t_input pa \<and> t_output p = t_output pa} = set (io_valid_transitions (product A B))"
        using product_transitions_alt2[of A B] product_transitions_io_valid by blast
      have "\<exists>p pa. ((t_source x, t_source y), t_input x, t_output x, t_target x, t_target y) = ((t_source p, t_source pa), t_input p, t_output p, t_target p, t_target pa) \<and> p \<in> set (wf_transitions A) \<and> pa \<in> set (wf_transitions B) \<and> t_input p = t_input pa \<and> t_output p = t_output pa"
        using \<open>t_input x = t_input y\<close> \<open>t_output x = t_output y\<close> \<open>x \<in> set (wf_transitions A)\<close> \<open>y \<in> set (wf_transitions B)\<close> by blast
      then show ?thesis
        using f1 by blast
    qed 
    
    moreover have "t_source x = target xs (initial A)" using snoc.prems(1) by auto
    moreover have "t_source y = target ys (initial B)" using snoc.prems(2) by auto
    ultimately have "((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y)) \<in> h (product A B)"
      using \<open>(t_source x, t_source y) \<in> nodes (product A B)\<close>
      by (metis fst_conv io_valid_transition_simp wf_transition_simp)
    then have ***: "path (product A B) (initial (product A B)) ((zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))])"
      using * **
    proof -
      have "\<forall>p f. p \<notin> nodes (f::('a \<times> 'c, 'b) FSM_scheme) \<or> path f p []"
        by blast
      then have "path (product A B) (t_source ((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)) [((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)]"
        by (meson \<open>((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y) \<in> set (wf_transitions (product A B))\<close> cons nodes.step wf_transition_simp)
      then have "path (product A B) (target (map (\<lambda>p. ((t_source (fst p), t_source (snd p)), t_input (fst p), t_output (fst p), t_target (fst p), t_target (snd p))) (zip xs ys)) (initial (product A B))) [((target xs (initial A), target ys (initial B)), t_input x, t_output x, t_target x, t_target y)]"
        by (metis (no_types) "**" fst_conv)
      then show ?thesis
        using "*" by blast
    qed     

    have "t_target x = target (xs@[x]) (initial A)" by auto
    moreover have "t_target y = target (ys@[y]) (initial B)" by auto
    ultimately have ****: "target ((zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]) (initial (product A B)) = (target (xs@[x]) (initial A), target (ys@[y]) (initial B))"
      by fastforce


    have "(zip_path [x] [y]) = [((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]"
      using \<open>t_source x = target xs (initial A)\<close> \<open>t_source y = target ys (initial B)\<close> by auto
    moreover have "(zip_path (xs @ [x]) (ys @ [y])) = (zip_path xs ys)@(zip_path [x] [y])"
      using zip_path_last[of xs ys x y, OF snoc.hyps]  by assumption
    ultimately have *****:"(zip_path (xs@[x]) (ys@[y])) = (zip_path xs ys)@[((target xs (initial A), target ys (initial B)), t_input x, t_output x, (t_target x, t_target y))]"
      by auto
    then have "path (product A B) (initial (product A B)) (zip_path (xs@[x]) (ys@[y]))"
      using *** by presburger 
    moreover have "target (zip_path (xs@[x]) (ys@[y])) (initial (product A B)) = (target (xs@[x]) (initial A), target (ys@[y]) (initial B))"
      using **** ***** by auto
    ultimately show ?case by linarith
  qed

  from c show "path (product A B) (initial (product A B)) (zip_path p1 p2)" by auto
  from c show "target (zip_path p1 p2) (initial (product A B)) = (target p1 (initial A), target p2 (initial B))" by auto
qed


lemma product_transitions_elem :
  assumes "t \<in> set (product_transitions A B)"
  shows "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
    and "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
proof -
  obtain t1 t2 where *:   "t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)" 
                 and **:  "t1 \<in> h A"
                 and ***: "t2 \<in> h B"
                 and ****: "t_input t1 = t_input t2 \<and> t_output t1 = t_output t2"
    using assms product_transitions_alt2[of A B] by blast
 
  from * ** show "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A" by auto
  from * *** **** show "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B" by auto
qed


lemma paths_from_product_path :
  assumes "path (product A B) (initial (product A B)) p"
  shows   "path A (initial A) (left_path p)"
      and "path B (initial B) (right_path p)"
      and "target (left_path p) (initial A) = fst (target p (initial (product A B)))"
      and "target (right_path p) (initial B) = snd (target p (initial (product A B)))"
proof -
  have "path A (initial A) (left_path p)
            \<and> path B (initial B) (right_path p)
            \<and> target (left_path p) (initial A) = fst (target p (initial (product A B)))
            \<and> target (right_path p) (initial B) = snd (target p (initial (product A B)))"
  using assms proof (induction p rule: rev_induct)
    case Nil
    then show ?case by auto
  next
    case (snoc t p)
    then have "path (product A B) (initial (product A B)) p" by fast
    then have "path A (initial A) (left_path p)"
      and "path B (initial B) (right_path p)"
      and "target (left_path p) (initial A) = fst (target p (initial (product A B)))"
      and "target (right_path p) (initial B) = snd (target p (initial (product A B)))" 
      using snoc.IH  by fastforce+

    then have "t_source t = (target (left_path p) (initial A), target (right_path p) (initial B))"
      using snoc.prems by (metis (no_types, lifting) path_cons_elim path_suffix prod.collapse) 


    have ***: "target (left_path (p@[t])) (initial A) = fst (target (p@[t]) (initial (product A B)))"
      by fastforce
    have ****: "target (right_path (p@[t])) (initial B) = snd (target (p@[t]) (initial (product A B)))"
      by fastforce

    have "t \<in> h (product A B)" using snoc.prems
      by (meson path_cons_elim path_suffix wf_transition_simp) 
    then have "t \<in> set (product_transitions A B)" 
      using product_transitions_io_valid[of A B]
      by (metis io_valid_transition_simp wf_transition_simp) 
    
    have "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
      using product_transitions_elem[OF \<open>t \<in> set (product_transitions A B)\<close>] by simp
    moreover have "target (left_path p) (initial A) = fst (t_source t)"
      using \<open>t_source t = (target (left_path p) (initial A), target (right_path p) (initial B))\<close> by auto
    ultimately have "path A (initial A) ((left_path p)@[(fst (t_source t), t_input t, t_output t, fst (t_target t))])"
    proof -
      have "\<forall>a f. a \<notin> nodes (f::('a, 'c) FSM_scheme) \<or> path f a []"
        by blast
      then have "path A (t_source (fst (t_source t), t_input t, t_output t, fst (t_target t))) [(fst (t_source t), t_input t, t_output t, fst (t_target t))]"
        by (meson \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> set (wf_transitions A)\<close> cons nodes.simps wf_transition_simp)
      then have "path A (target (map (\<lambda>p. (fst (t_source p), t_input p, t_output p, fst (t_target p))) p) (initial A)) [(fst (t_source t), t_input t, t_output t, fst (t_target t))]"
        using \<open>target (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p) (initial A) = fst (t_source t)\<close> by auto
      then show ?thesis
        using \<open>path A (initial A) (map (\<lambda>t. (fst (t_source t), t_input t, t_output t, fst (t_target t))) p)\<close> by blast
    qed 
    then have *: "path A (initial A) (left_path (p@[t]))" by auto

    have "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"
      using product_transitions_elem[OF \<open>t \<in> set (product_transitions A B)\<close>] by simp
    moreover have "target (right_path p) (initial B) = snd (t_source t)"
      using \<open>t_source t = (target (left_path p) (initial A), target (right_path p) (initial B))\<close> by auto
    ultimately have "path B (initial B) ((right_path p)@[(snd (t_source t), t_input t, t_output t, snd (t_target t))])"
    proof -
      have "\<forall>b f. b \<notin> nodes (f::('b, 'd) FSM_scheme) \<or> path f b []"
        by blast
      then have "path B (t_source (snd (t_source t), t_input t, t_output t, snd (t_target t))) [(snd (t_source t), t_input t, t_output t, snd (t_target t))]"
        by (meson \<open>(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> set (wf_transitions B)\<close> cons nodes.simps wf_transition_simp)
      then have "path B (target (map (\<lambda>p. (snd (t_source p), t_input p, t_output p, snd (t_target p))) p) (initial B)) [(snd (t_source t), t_input t, t_output t, snd (t_target t))]"
        using \<open>target (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p) (initial B) = snd (t_source t)\<close> by auto
      then show ?thesis
        using \<open>path B (initial B) (map (\<lambda>t. (snd (t_source t), t_input t, t_output t, snd (t_target t))) p)\<close> by blast
    qed
    then have **: "path B (initial B) (right_path (p@[t]))" by auto


    show ?case using * ** *** **** by blast
  qed

  then show "path A (initial A) (left_path p)"
      and "path B (initial B) (right_path p)"
      and "target (left_path p) (initial A) = fst (target p (initial (product A B)))"
      and "target (right_path p) (initial B) = snd (target p (initial (product A B)))" by linarith+
qed

  



lemma product_transition :
  "((q1,q2),x,y,(q1',q2')) \<in> h (product A B) \<longleftrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
proof 
  show "((q1,q2),x,y,(q1',q2')) \<in> h (product A B) \<Longrightarrow> (q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
  proof -
    assume "((q1,q2),x,y,(q1',q2')) \<in> h (product A B)"
    then have "(q1,q2) \<in> nodes (product A B)"
      by (metis fst_conv wf_transition_simp) 
    then obtain p where "path (product A B) (initial (product A B)) p" and "target p (initial (product A B)) = (q1,q2)"
      by (metis path_to_node)

    have "path A (initial A) (left_path p) \<and> path B (initial B) (right_path p) \<and> target (left_path p) (initial A) = q1 \<and> target (right_path p) (initial B) = q2"
      using paths_from_product_path[OF \<open>path (product A B) (initial (product A B)) p\<close>] \<open>target p (initial (product A B)) = (q1,q2)\<close> by auto
    moreover have "p_io (left_path p) = p_io (right_path p)" by auto
    ultimately have "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
      by blast
    moreover have "(q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B"
      using \<open>((q1,q2),x,y,(q1',q2')) \<in> h (product A B)\<close>
      by (metis product_simps(4) product_transition_hIO product_transitions_io_valid wf_transition_simp)
    ultimately show ?thesis by simp
  qed

  show "(q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2) \<Longrightarrow> ((q1,q2),x,y,(q1',q2')) \<in> h (product A B)"
  proof -
    assume assm: "(q1,x,y,q1') \<in> h A \<and> (q2,x,y,q2') \<in> h B \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
    then obtain p1 p2 where pr1: "path A (initial A) p1" 
                        and pr2: "path B (initial B) p2" 
                        and pr3: "target p1 (initial A) = q1" 
                        and pr4: "target p2 (initial B) = q2" 
                        and pr5: "p_io p1 = p_io p2"
      by blast

    have "(q1,x,y,q1') \<in> h A" and "(q2,x,y,q2') \<in> h B"
      using assm by auto

    have "initial (product A B) \<in> nodes (product A B)"
      by blast 
    moreover have "path (product A B) (initial (product A B)) (zip_path p1 p2)"
      using product_path_from_paths(1)[OF pr1 pr2 pr5] by assumption
    moreover have "target (zip_path p1 p2) (initial (product A B)) = (q1,q2)"
      using product_path_from_paths(2)[OF pr1 pr2 pr5] pr3 pr4 by fast
    ultimately have "(q1,q2) \<in> nodes (product A B)" 
      using nodes_path[of "product A B" "initial (product A B)" "zip_path p1 p2"] by metis
    then have "t_source ((q1,q2),x,y,(q1',q2')) \<in> nodes (product A B)"
      by auto

    moreover have "((q1,q2),x,y,(q1',q2')) \<in> hIO (product A B)"
      using product_transitions_alt3[of A B] \<open>(q1,x,y,q1') \<in> h A\<close> \<open>(q2,x,y,q2') \<in> h B\<close> by force
    ultimately show "((q1,q2),x,y,(q1',q2')) \<in> h (product A B)" 
      using hIO_alt_def[of "product A B"] h_alt_def[of "product A B"] by blast
  qed
qed

lemma product_transition_t :
  "t \<in> h (product A B) \<longleftrightarrow> (fst (t_source t),t_input t,t_output t,fst (t_target t)) \<in> h A \<and> (snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = fst (t_source t) \<and> target p2 (initial B) = snd (t_source t) \<and> p_io p1 = p_io p2)"
proof -
  have "t = ((fst (t_source t), snd (t_source t)), t_input t, t_output t, fst (t_target t), snd (t_target t))"
    by auto
  then show ?thesis
    using product_transition[of "fst (t_source t)" "snd (t_source t)" "t_input t" "t_output t" "fst (t_target t)" "snd (t_target t)" A B] by presburger
qed

lemma product_transition_from_transitions :
  assumes "t1 \<in> h A" 
      and "t2 \<in> h B" 
      and "t_input t1 = t_input t2" 
      and "t_output t1 = t_output t2" 
      and "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = t_source t1 \<and> target p2 (initial B) = t_source t2 \<and> p_io p1 = p_io p2)"
  shows "((t_source t1,t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2)) \<in> h (product A B)  "
proof-
  note product_transition[of "t_source t1" "t_source t2" "t_input t1" "t_output t1" "t_target t1" "t_target t2" A B]
  moreover have "(t_source t1, t_input t1, t_output t1, t_target t1) \<in> set (wf_transitions A)"
    using assms(1) by auto
  moreover have "(t_source t2, t_input t1, t_output t1, t_target t2) \<in> set (wf_transitions B)"
    using assms(2-4) by auto
  moreover note assms(5)
  ultimately show ?thesis by presburger
qed
 


lemma product_node_from_path :
  "(q1,q2) \<in> nodes (product A B) \<longleftrightarrow> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
proof 
  show "(q1,q2) \<in> nodes (product A B) \<Longrightarrow> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
  proof -
    assume "(q1,q2) \<in> nodes (product A B)"
    then obtain p where "path (product A B) (initial (product A B)) p" and "target p (initial (product A B)) = (q1,q2)"
      by (metis path_to_node) 
    then have "path A (initial A) (left_path p) \<and> path B (initial B) (right_path p) \<and> target (left_path p) (initial A) = q1 \<and> target (right_path p) (initial B) = q2 \<and> p_io (left_path p) = p_io (right_path p)"
      using paths_from_product_path[OF \<open>path (product A B) (initial (product A B)) p\<close>] by simp
    then show "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
      by blast
  qed

  show "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2) \<Longrightarrow> (q1,q2) \<in> nodes (product A B)"
  proof -
    assume "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
    then obtain p1 p2 where *: "path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2"
      by blast

    have "initial (product A B) \<in> nodes (product A B)"
      by blast 
    moreover have "path (product A B) (initial (product A B)) (zip_path p1 p2)"
      using product_path_from_paths(1)[of A p1 B p2] * by metis
    moreover have "target (zip_path p1 p2) (initial (product A B)) = (q1,q2)"
      using product_path_from_paths(2)[of A p1 B p2] * by metis
    ultimately show "(q1,q2) \<in> nodes (product A B)" 
      using nodes_path[of "product A B" "initial (product A B)" "zip_path p1 p2"] by metis
  qed
qed


lemma left_path_zip : "length p1 = length p2 \<Longrightarrow> left_path (zip_path p1 p2) = p1" 
  by (induction p1 p2 rule: list_induct2; simp)

lemma right_path_zip : "length p1 = length p2 \<Longrightarrow> p_io p1 = p_io p2 \<Longrightarrow> right_path (zip_path p1 p2) = p2" 
  by (induction p1 p2 rule: list_induct2; simp)

lemma zip_path_append_left_right : "length p1 = length p2 \<Longrightarrow> zip_path (p1@(left_path p)) (p2@(right_path p)) = (zip_path p1 p2)@p"
proof (induction p1 p2 rule: list_induct2)
  case Nil
  then show ?case by (induction p; simp)
next
  case (Cons x xs y ys)
  then show ?case by simp
qed
  
    
      

lemma product_path:
  "path (product A B) (q1,q2) p \<longleftrightarrow> (path A q1 (left_path p) \<and> path B q2 (right_path p) \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2))"
proof 
  show "path (product A B) (q1,q2) p \<Longrightarrow> (path A q1 (left_path p) \<and> path B q2 (right_path p) \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2))"
  proof -
    assume "path (product A B) (q1,q2) p"
    then have "(q1,q2) \<in> nodes (product A B)"
      by (meson path_begin_node) 
    then have ex12: "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
      using product_node_from_path[of q1 q2 A B] by blast
    then obtain p1 p2 where *: "path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2"
      by blast
    then have "path (product A B) (initial (product A B)) (zip_path p1 p2)" 
      using product_path_from_paths(1)[of A p1 B p2] by metis

    have "path A (initial A) p1" and "path B (initial B) p2" and "target p1 (initial A) = q1" and "target p2 (initial B) = q2" and "p_io p1 = p_io p2"
      using * by linarith+

    have "target (zip_path p1 p2) (initial (product A B)) = (q1,q2)"
      using product_path_from_paths(2)[of A p1 B p2] * by metis

    have "path (product A B) (initial (product A B)) ((zip_path p1 p2) @ p)" 
      using path_append[OF \<open>path (product A B) (initial (product A B)) (zip_path p1 p2)\<close>, of p]
            \<open>target (zip_path p1 p2) (initial (product A B)) = (q1,q2)\<close>
            \<open>path (product A B) (q1,q2) p\<close> by metis

    have "path A (initial A) (left_path ((zip_path p1 p2) @ p))"
      and "path B (initial B) (right_path ((zip_path p1 p2) @ p))"
      and "target (left_path ((zip_path p1 p2) @ p)) (initial A) = fst (target ((zip_path p1 p2) @ p) (initial (product A B)))"
      and "target (right_path ((zip_path p1 p2) @ p)) (initial B) = snd (target ((zip_path p1 p2) @ p) (initial (product A B)))"
      using paths_from_product_path[OF \<open>path (product A B) (initial (product A B)) ((zip_path p1 p2) @ p)\<close>] by linarith+

    have "length p1 = length p2"
      using \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq by blast 

    have "(left_path ((zip_path p1 p2) @ p)) = p1@(left_path p)"
      using left_path_zip[OF \<open>length p1 = length p2\<close>] by (induction p; simp)
    then have "path A (initial A) (p1@(left_path p))"
      using \<open>path A (initial A) (left_path ((zip_path p1 p2) @ p))\<close> by simp
    have lp: "path A q1 (left_path p)" 
      using path_suffix[OF \<open>path A (initial A) (p1@(left_path p))\<close>] \<open>target p1 (initial A) = q1\<close> by simp

    
    have "(right_path ((zip_path p1 p2) @ p)) = p2@(right_path p)"
      using right_path_zip[OF \<open>length p1 = length p2\<close> \<open>p_io p1 = p_io p2\<close>] by (induction p; simp)  
    then have "path B (initial B) (p2@(right_path p))"
      using \<open>path B (initial B) (right_path ((zip_path p1 p2) @ p))\<close> by simp
    have rp: "path B q2 (right_path p)" 
      using path_suffix[OF \<open>path B (initial B) (p2@(right_path p))\<close>] \<open>target p2 (initial B) = q2\<close> by simp  

    show "(path A q1 (left_path p) \<and> path B q2 (right_path p) \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2))"
      using lp rp ex12 by simp
  qed


  show "(path A q1 (left_path p) \<and> path B q2 (right_path p) \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)) \<Longrightarrow> path (product A B) (q1,q2) p"
  proof-
    assume "(path A q1 (left_path p) \<and> path B q2 (right_path p) \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2))"
    then have "path A q1 (left_path p)" and "path B q2 (right_path p)" and "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
      by auto
    then obtain p1 p2 where *: "path A (initial A) p1" and "path B (initial B) p2" and "target p1 (initial A) = q1" and "target p2 (initial B) = q2" and "p_io p1 = p_io p2"
      by blast 

    have "path A (initial A) (p1@(left_path p))"
      using path_append[OF \<open>path A (initial A) p1\<close>, of "left_path p"] \<open>target p1 (initial A) = q1\<close> \<open>path A q1 (left_path p)\<close> by metis
    have "path B (initial B) (p2@(right_path p))"
      using path_append[OF \<open>path B (initial B) p2\<close>, of "right_path p"] \<open>target p2 (initial B) = q2\<close> \<open>path B q2 (right_path p)\<close> by metis
    have "p_io (p1@(left_path p)) = p_io (p2@(right_path p))"
      using \<open>p_io p1 = p_io p2\<close> by (induction p; simp)
    
    have "path (product A B) (initial (product A B)) ((zip_path p1 p2)@p)"
      using product_path_from_paths(1)[OF \<open>path A (initial A) (p1@(left_path p))\<close> \<open>path B (initial B) (p2@(right_path p))\<close> \<open>p_io (p1@(left_path p)) = p_io (p2@(right_path p))\<close>]
            zip_path_append_left_right[of p1 p2 p]
      by (metis (no_types, lifting) \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq) 

    have "path (product A B) (initial (product A B)) (zip_path p1 p2)"
      using product_path_from_paths(1)[OF \<open>path A (initial A) p1\<close> \<open>path B (initial B) p2\<close> \<open>p_io p1 = p_io p2\<close>] by metis
    moreover have "target (zip_path p1 p2) (initial (product A B)) = (q1,q2)"
      using product_path_from_paths(2)[OF \<open>path A (initial A) p1\<close> \<open>path B (initial B) p2\<close> \<open>p_io p1 = p_io p2\<close>] \<open>target p1 (initial A) = q1\<close> \<open>target p2 (initial B) = q2\<close> by metis
    
    
    ultimately show "path (product A B) (q1,q2) p"
      using path_suffix[OF \<open>path (product A B) (initial (product A B)) ((zip_path p1 p2)@p)\<close>]
      by presburger 
  qed
qed
    
      












lemma product_path_rev:
  assumes "p_io p1 = p_io p2"
  shows "path (product A B) (q1,q2) (zip_path p1 p2)
          \<longleftrightarrow> (path A q1 p1 \<and> path B q2 p2 \<and> (\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2))"
proof -
  have "length p1 = length p2" using assms
    using map_eq_imp_length_eq by blast 
  then have "(map (\<lambda> t . (fst (t_source t), t_input t, t_output t, fst (t_target t))) (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))) = p1"
    by (induction p1 p2 arbitrary: q1 q2 rule: list_induct2; auto)

  moreover have "(map (\<lambda> t . (snd (t_source t), t_input t, t_output t, snd (t_target t))) (map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))) = p2"
    using \<open>length p1 = length p2\<close> assms by (induction p1 p2 arbitrary: q1 q2 rule: list_induct2; auto)

  ultimately show ?thesis using product_path[of A B q1 q2 "(map (\<lambda> t . ((t_source (fst t), t_source (snd t)), t_input (fst t), t_output (fst t), (t_target (fst t), t_target (snd t)))) (zip p1 p2))"]
    by auto
qed
    
    






lemma product_language_state : 
  assumes "(\<exists> p1 p2 . path A (initial A) p1 \<and> path B (initial B) p2 \<and> target p1 (initial A) = q1 \<and> target p2 (initial B) = q2 \<and> p_io p1 = p_io p2)"
  shows "LS (product A B) (q1,q2) = LS A q1 \<inter> LS B q2"
proof 
  show "LS (product A B) (q1, q2) \<subseteq> LS A q1 \<inter> LS B q2"
  proof 
    fix io assume "io \<in> LS (product A B) (q1, q2)"
    then obtain p where "io = p_io p" 
                    and "path (product A B) (q1,q2) p"
      by auto
    then obtain p1 p2 where "path A q1 p1" 
                        and "path B q2 p2"
                        and "io = p_io p1" 
                        and "io = p_io p2"
      using product_path[of A B q1 q2 p] by fastforce
    then show "io \<in> LS A q1 \<inter> LS B q2" 
      unfolding LS.simps by blast
  qed

  show "LS A q1 \<inter> LS B q2 \<subseteq> LS (product A B) (q1, q2)"
  proof
    fix io assume "io \<in> LS A q1 \<inter> LS B q2"
    then obtain p1 p2 where "path A q1 p1" 
                        and "path B q2 p2"
                        and "io = p_io p1" 
                        and "io = p_io p2"
                        and "p_io p1 = p_io p2"
      by auto

    let ?p = "zip_path p1 p2"
    
    
    have "length p1 = length p2"
      using \<open>p_io p1 = p_io p2\<close> map_eq_imp_length_eq by blast 
    moreover have "p_io ?p = p_io (map fst (zip p1 p2))" by auto
    ultimately have "p_io ?p = p_io p1" by auto

    then have "p_io ?p = io" 
      using \<open>io = p_io p1\<close> by auto
    moreover have "path (product A B) (q1, q2) ?p"
      using product_path_rev[OF \<open>p_io p1 = p_io p2\<close>, of A B q1 q2] \<open>path A q1 p1\<close> \<open>path B q2 p2\<close> assms by auto
    ultimately show "io \<in> LS (product A B) (q1, q2)" 
      unfolding LS.simps by blast
  qed
qed


lemma product_language : "L (product A B) = L A \<inter> L B"
proof -
  have "path A (initial A) [] \<and>
         path B (initial B) [] \<and>
         target [] (initial A) = initial A \<and> target [] (initial B) = initial B \<and> p_io [] = p_io []" by auto
  then have "\<exists>p1 p2.
       path A (initial A) p1 \<and>
       path B (initial B) p2 \<and>
       target p1 (initial A) = initial A \<and> target p2 (initial B) = initial B \<and> p_io p1 = p_io p2" by blast
  then show ?thesis
    using product_language_state[of A B "initial A" "initial B"] unfolding product.simps by simp
qed

lemma product_nodes : "nodes (product A B) \<subseteq> (nodes A) \<times> (nodes B)"
proof 
  fix q assume "q \<in> nodes (product A B)"
  then obtain p where "path (product A B) (initial (product A B)) p"
                and   "q = target p (initial (product A B))" 
    by (metis path_to_node)

  let ?p1 = "left_path p"
  let ?p2 = "right_path p"

  have "path A (initial A) ?p1 \<and> path B (initial B) ?p2"
    by (metis \<open>path (product A B) (initial (product A B)) p\<close> product_path[of A B "initial A" "initial B" p] product_simps(1))

  moreover have "target p (initial (product A B)) = (target ?p1 (initial A), target ?p2 (initial B))"
    by (induction p; force)  

  ultimately show "q \<in> (nodes A) \<times> (nodes B)"
    by (metis (no_types, lifting) SigmaI \<open>q = target p (initial (product A B))\<close> nodes_path_initial)
qed

lemma product_transition_split_ob :
  assumes "t \<in> h (product A B)"
  obtains t1 t2 
  where "t1 \<in> h A \<and> t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
    and "t2 \<in> h B \<and> t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)"      
proof -
  have "t \<in> set (transitions (product A B))"
    using assms by blast
  
  then have "t \<in> set (map (\<lambda>(t1, t2).
                      ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2))
               (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)
                 (cartesian_product_list (wf_transitions A) (wf_transitions B))))"
    by (metis product_simps(4) product_transitions.elims) 

  then obtain t1 t2 where "t = ((t_source t1, t_source t2),t_input t1,t_output t1,(t_target t1,t_target t2))"
                 and "(t1,t2) \<in> set (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2)
                                      (cartesian_product_list (wf_transitions A) (wf_transitions B)))"
    by (metis (no_types, lifting) case_prod_beta' imageE prod.collapse set_map)

  then have *: "t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)" 
    by auto
  have **: "t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
    by (simp add: \<open>t = ((t_source t1, t_source t2), t_input t1, t_output t1, t_target t1, t_target t2)\<close>)

  have "(t1,t2) \<in> h A \<times> h B"
    using \<open>(t1,t2) \<in> set (filter (\<lambda>(t1, t2). t_input t1 = t_input t2 \<and> t_output t1 = t_output t2) (cartesian_product_list (wf_transitions A) (wf_transitions B)))\<close> cartesian_product_list_set[of "(wf_transitions A)" "(wf_transitions B)"] by auto
  then have "t1 \<in> h A" and "t2 \<in> h B" by auto

  have "t1 \<in> h A \<and> t_source t1 = fst (t_source t) \<and> t_input t1 = t_input t \<and> t_output t1 = t_output t \<and> t_target t1 = fst (t_target t)"
   and "t2 \<in> h B \<and> t_source t2 = snd (t_source t) \<and> t_input t2 = t_input t \<and> t_output t2 = t_output t \<and> t_target t2 = snd (t_target t)" 
    using \<open>t1 : h A\<close> * \<open>t2 \<in> h B\<close> ** by auto

  then show ?thesis
    using that by blast 
qed

lemma product_transition_split :
  assumes "t \<in> h (product A B)"
  shows "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h A"
    and "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h B"      
  using product_transition_split_ob[OF assms] prod.collapse by metis+



subsection \<open>Other Lemmata\<close>

lemma  product_target_split:
  assumes "target p (q1,q2) = (q1',q2')"
  shows "target (left_path p) q1 = q1'"
    and "target (right_path p) q2 = q2'"
using assms by (induction p arbitrary: q1 q2; force)+





lemma h_from_paths :
  assumes "\<And> p . path A (initial A) p = path B (initial B) p"
  shows "h A = h B"
proof (rule ccontr)
  assume "h A \<noteq> h B"
  then consider  "(\<exists> tA \<in> h A . tA \<notin> h B)" | "(\<exists> tB \<in> h B . tB \<notin> h A)" by blast
  then show "False" proof (cases)
    case 1
    then obtain tA where "tA \<in> h A" and "tA \<notin> h B" by blast
    then have "t_source tA \<in> nodes A" by auto
    then obtain p where "path A (initial A) p" and "target p (initial A) = t_source tA" 
      using path_to_node by metis
    then have "path A (initial A) (p@[tA])" using path_append_last \<open>tA \<in> h A\<close> by metis
    moreover have "\<not> path B (initial B) (p@[tA])" using \<open>tA \<notin> h B\<close> by auto
    ultimately show "False" using assms by metis
  next
    case 2
    then obtain tB where "tB \<in> h B" and "tB \<notin> h A" by blast
    then have "t_source tB \<in> nodes B" by auto
    then obtain p where "path B (initial B) p" and "target p (initial B) = t_source tB" 
      using path_to_node by metis
    then have "path B (initial B) (p@[tB])" using path_append_last \<open>tB \<in> h B\<close> by metis
    moreover have "\<not> path A (initial A) (p@[tB])" using \<open>tB \<notin> h A\<close> by auto
    ultimately show "False" using assms by metis
  qed
qed




lemma single_transitions_path : 
  assumes "(q,x,y,q') \<in> h M" 
  shows "path M q [(q,x,y,q')]" 
  using  path.cons[OF assms path.nil[OF wf_transition_target[OF assms]]] by auto

lemma product_from_next :
  assumes "((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
  shows "h (product (from_FSM M q1') (from_FSM M q2')) = h (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2'))"
proof -
  let ?t = "((q1,q2),x,y,(q1',q2'))"


  have "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
    using wf_transition_target[OF assms] by simp
  then have "q1' \<in> nodes (from_FSM M q1)" and "q2' \<in> nodes (from_FSM M q2)"
    using product_nodes[of "from_FSM M q1" "from_FSM M q2"] by blast+

  have "(q1,x,y,q1') \<in> h (from_FSM M q1)" and "(q2,x,y,q2') \<in> h (from_FSM M q2)"
    using product_transition_split[OF assms] by auto

  have s1 : "initial (product (from_FSM M q1') (from_FSM M q2')) = (q1',q2')"
    by auto
  have s2 : "initial (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) = (q1',q2')"
    by auto


  have *: "\<And> p . path (product (from_FSM M q1') (from_FSM M q2')) (q1',q2') p = path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1',q2') p"
  proof -
    fix p show "path (product (from_FSM M q1') (from_FSM M q2')) (q1',q2') p = path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1',q2') p"
    proof  
      show "path (product (from_FSM M q1') (from_FSM M q2')) (q1', q2') p \<Longrightarrow>
              path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1', q2') p"
      proof -
        assume "path (product (from_FSM M q1') (from_FSM M q2')) (q1', q2') p"
        then have "path (from_FSM M q1') q1' (left_path p)" and "path (from_FSM M q2') q2' (right_path p)"
          using product_path[of "from_FSM M q1'" "from_FSM M q2'" q1' q2' p] by linarith+

        have "path (from_FSM M q1) q1' (left_path p)"
          using from_FSM_path[OF \<open>q1' \<in> nodes (from_FSM M q1)\<close>, of q1' "left_path p"] \<open>path (from_FSM M q1') q1' (left_path p)\<close> by auto
        have "path (from_FSM M q2) q2' (right_path p)"
          using from_FSM_path[OF \<open>q2' \<in> nodes (from_FSM M q2)\<close>, of q2' "right_path p"] \<open>path (from_FSM M q2') q2' (right_path p)\<close> by auto

        have p3: "(\<exists>p1 p2.
                         path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
                         path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
                         target p1 (initial (from_FSM M q1)) = q1' \<and>
                         target p2 (initial (from_FSM M q2)) = q2' \<and> p_io p1 = p_io p2)" 
        proof -
          have "path (from_FSM M q1) (initial (from_FSM M q1)) [(q1, x, y, q1')]"
            using single_transitions_path[OF \<open>(q1,x,y,q1') \<in> h (from_FSM M q1)\<close>] by auto
          moreover have "path (from_FSM M q2) (initial (from_FSM M q2)) [(q2, x, y, q2')]"
            using single_transitions_path[OF \<open>(q2,x,y,q2') \<in> h (from_FSM M q2)\<close>] by auto
          moreover have "(target [(q1,x,y,q1')] (initial (from_FSM M q1)) = q1' \<and>
                          target [(q2,x,y,q2')] (initial (from_FSM M q2)) = q2' \<and> 
                          p_io [(q1,x,y,q1')] = p_io [(q2,x,y,q2')])" 
            by auto
          ultimately show ?thesis by meson
        qed
        
        have "path (product (from_FSM M q1) (from_FSM M q2)) (q1',q2') p"
          using product_path[of "from_FSM M q1" "from_FSM M q2" q1' q2' p] \<open>path (from_FSM M q1) q1' (left_path p)\<close> \<open>path (from_FSM M q2) q2' (right_path p)\<close> p3 by presburger

        then show "path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1',q2') p"
          using from_FSM_path_rev_initial by metis
      qed
      show "path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1', q2') p \<Longrightarrow>
              path (product (from_FSM M q1') (from_FSM M q2')) (q1', q2') p"
      proof -
        assume "path (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) (q1', q2') p"
        then have "path (product (from_FSM M q1) (from_FSM M q2)) (q1',q2') p"
          using from_FSM_path[OF \<open>(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))\<close>] by metis
        then have "path (from_FSM M q1) q1' (left_path p)" 
              and "path (from_FSM M q2) q2' (right_path p)"
              and "(\<exists>p1 p2.
                     path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
                     path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
                     target p1 (initial (from_FSM M q1)) = q1' \<and>
                     target p2 (initial (from_FSM M q2)) = q2' \<and> p_io p1 = p_io p2)"
          using product_path[of "from_FSM M q1" "from_FSM M q2" q1' q2' p] by presburger+

        have "path (from_FSM M q1') q1' (left_path p)"
          using from_FSM_path_rev_initial[OF \<open>path (from_FSM M q1) q1' (left_path p)\<close>] by auto
        moreover have "path (from_FSM M q2') q2' (right_path p)"
          using from_FSM_path_rev_initial[OF \<open>path (from_FSM M q2) q2' (right_path p)\<close>] by auto
        moreover have p3: "(\<exists>p1 p2.
                         path (from_FSM M q1') (initial (from_FSM M q1')) p1 \<and>
                         path (from_FSM M q2') (initial (from_FSM M q2')) p2 \<and>
                         target p1 (initial (from_FSM M q1')) = q1' \<and>
                         target p2 (initial (from_FSM M q2')) = q2' \<and> p_io p1 = p_io p2)" 
        proof -
          have "path (from_FSM M q1') (initial (from_FSM M q1')) []" 
            using path.nil[OF nodes.initial] by metis
          moreover have "path (from_FSM M q2') (initial (from_FSM M q2')) []"
            using path.nil[OF nodes.initial] by metis
          moreover have "(target [] (initial (from_FSM M q1')) = q1' \<and>
                          target [] (initial (from_FSM M q2')) = q2' \<and> 
                          p_io [] = p_io [])" 
            by auto
          ultimately show ?thesis by blast
        qed
        
        ultimately show " path (product (from_FSM M q1') (from_FSM M q2')) (q1', q2') p"
          using product_path[of "from_FSM M q1'" "from_FSM M q2'" q1' q2' p] by presburger        
      qed
    qed
  qed

  show ?thesis using * h_from_paths s1 s2 by metis
qed
   

lemma submachine_transition_product_from :
  assumes "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
      and "((q1,q2),x,y,(q1',q2')) \<in> h S"
 shows "is_submachine (from_FSM S (q1',q2')) (product (from_FSM M q1') (from_FSM M q2'))"
proof -
  have "((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))"
    using submachine_h[OF assms(1)] assms(2) by blast
  have "(q1',q2') \<in> nodes S" using wf_transition_target[OF assms(2)] by auto 
  show ?thesis 
    using product_from_next[OF \<open>((q1,q2),x,y,(q1',q2')) \<in> h (product (from_FSM M q1) (from_FSM M q2))\<close>]
          submachine_from[OF assms(1) \<open>(q1',q2') \<in> nodes S\<close>]
  proof -
    have "initial (from_FSM S (q1', q2')) = initial (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) \<and> set (wf_transitions (from_FSM S (q1', q2'))) \<subseteq> set (wf_transitions (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2'))) \<and> inputs (from_FSM S (q1', q2')) = inputs (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')) \<and> outputs (from_FSM S (q1', q2')) = outputs (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2'))"
      using \<open>is_submachine (from_FSM S (q1', q2')) (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2'))\<close> is_submachine.simps by blast
    then show ?thesis
      by (metis (no_types) \<open>set (wf_transitions (product (from_FSM M q1') (from_FSM M q2'))) = set (wf_transitions (from_FSM (product (from_FSM M q1) (from_FSM M q2)) (q1', q2')))\<close> from_FSM_simps(1) from_FSM_simps(2) from_FSM_simps(3) is_submachine.simps product_simps(1) product_simps(2) product_simps(3))
  qed
qed

lemma submachine_transition_complete_product_from :
  assumes "is_submachine S (product (from_FSM M q1) (from_FSM M q2))"
      and "completely_specified S"
      and "((q1,q2),x,y,(q1',q2')) \<in> h S"
 shows "completely_specified (from_FSM S (q1',q2'))"
proof -
  let ?P = "(product (from_FSM M q1) (from_FSM M q2))"
  let ?P' = "(product (from_FSM M q1') (from_FSM M q2'))"
  let ?F = "(from_FSM S (q1',q2'))"  
  
  have "initial ?P = (q1,q2)"
    by auto
  then have "initial S = (q1,q2)" 
    using assms(1) by (metis is_submachine.simps) 
  then have "(q1',q2') \<in> nodes S"
    using assms(3)
    using wf_transition_target by fastforce 
  then have "nodes ?F \<subseteq> nodes S"
    using from_FSM_nodes by metis
  moreover have "inputs ?F = inputs S"
    by auto
  ultimately show "completely_specified ?F" 
    using assms(2) unfolding completely_specified.simps
    using from_FSM_nodes_transitions[of _ S "(q1',q2')"]
    using contra_subsetD by fastforce
qed


lemma from_FSM_product_inputs :
  "set (inputs (product (from_FSM M q1) (from_FSM M q2))) = set (inputs M)"
  unfolding product.simps from_FSM.simps by auto

lemma from_FSM_product_outputs :
  "set (outputs (product (from_FSM M q1) (from_FSM M q2))) = set (outputs M)"
  unfolding product.simps from_FSM.simps by auto

lemma from_FSM_product_initial : 
  "initial (product (from_FSM M q1) (from_FSM M q2)) = (q1,q2)" by auto

lemma from_FSM_transitions :
  "transitions (from_FSM M q) = transitions M" by auto 

lemma from_from[simp] : "from_FSM (from_FSM M q1) q1' = from_FSM M q1'" by auto

lemma product_from_next' :
  assumes "t \<in> h (product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t))))"
    shows "h (from_FSM (product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t)))) (fst (t_target t),snd (t_target t))) = h (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t))))"
proof -
  have "t = ((fst (t_source t),snd (t_source t)),t_input t, t_output t,(fst (t_target t),snd (t_target t)))"
    by (metis prod.collapse)
  then have *: "((fst (t_source t),snd (t_source t)),t_input t, t_output t,(fst (t_target t),snd (t_target t))) \<in> h (product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t))))"
    using assms by presburger
  
  show ?thesis using product_from_next[OF *] by blast
qed



lemma product_from_next'_path :
  assumes "t \<in> h (product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t))))"
  shows "path (from_FSM (product (from_FSM M (fst (t_source t))) (from_FSM M (snd (t_source t)))) (fst (t_target t),snd (t_target t))) (fst (t_target t),snd (t_target t)) p = path (product (from_FSM M (fst (t_target t))) (from_FSM M (snd (t_target t)))) (fst (t_target t),snd (t_target t)) p" 
    (is "path ?P1 ?q p = path ?P2 ?q p")
proof -
  have i1: "initial ?P1 = ?q" by auto
  have i2: "initial ?P2 = ?q" by auto
  have h12: "h ?P1 = h ?P2" using product_from_next'[OF assms] by assumption
  
  show ?thesis proof (induction p rule: rev_induct)
    case Nil
    then show ?case
      by (metis (full_types) i1 i2 nodes.initial path.nil)
  next
    case (snoc t p)
    show ?case by (meson h12 h_equivalence_path path_begin_node path_prefix snoc.IH)
  qed
qed


lemma product_from_transition_subset:
  assumes "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))" 
  shows "h (product (from_FSM M q1') (from_FSM M q2')) \<subseteq> h (product (from_FSM M q1) (from_FSM M q2))" (is "h ?P' \<subseteq> h ?P")
proof 
  fix t assume "t \<in> h ?P'"
  then have "t_source t \<in> nodes ?P'" by (metis wf_transition_simp)
  then obtain p' where "path ?P' (initial ?P') p'" and "target p' (initial ?P') = t_source t"
    by (metis path_to_node)

  have "path (from_FSM M q1') q1' (left_path p')"
       "path (from_FSM M q2') q2' (right_path p')"
       "(\<exists>p1 p2.
           path (from_FSM M q1') (initial (from_FSM M q1')) p1 \<and>
           path (from_FSM M q2') (initial (from_FSM M q2')) p2 \<and>
           target p1 (initial (from_FSM M q1')) = q1' \<and> target p2 (initial (from_FSM M q2')) = q2' \<and> p_io p1 = p_io p2)"
    using product_path[of "from_FSM M q1'" "from_FSM M q2'" q1' q2' p'] \<open>path ?P' (initial ?P') p'\<close> by auto
  
  have          "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> set (wf_transitions (from_FSM M q1'))"
       and      "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> set (wf_transitions (from_FSM M q2'))"
       and p'': "(\<exists>p1 p2.
                   path (from_FSM M q1') (initial (from_FSM M q1')) p1 \<and>
                   path (from_FSM M q2') (initial (from_FSM M q2')) p2 \<and>
                   target p1 (initial (from_FSM M q1')) = fst (t_source t) \<and>
             target p2 (initial (from_FSM M q2')) = snd (t_source t) \<and> p_io p1 = p_io p2)"
    using product_transition_t[of t "from_FSM M q1'" "from_FSM M q2'"] \<open>t \<in> h ?P'\<close> by presburger+



  obtain p where "path ?P (initial ?P) p" and "target p (initial ?P) = (q1',q2')"
    by (metis assms path_to_node)
  have "path (from_FSM M q1) q1 (left_path p)"
       "path (from_FSM M q2) q2 (right_path p)"
       "(\<exists>p1 p2.
           path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
           path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
           target p1 (initial (from_FSM M q1)) = q1 \<and> target p2 (initial (from_FSM M q2)) = q2 \<and> p_io p1 = p_io p2)"
    using product_path[of "from_FSM M q1" "from_FSM M q2" q1 q2 p] \<open>path ?P (initial ?P) p\<close> by auto

  have "target (left_path p) q1 = q1'" and "target (right_path p) q2 = q2'"
    using product_target_split[of p q1 q2 q1' q2'] \<open>target p (initial ?P) = (q1',q2')\<close> by auto

  have "q1' \<in> nodes (from_FSM M q1)"
    using path_target_is_node[OF \<open>path (from_FSM M q1) q1 (left_path p)\<close>] \<open>target (left_path p) q1 = q1'\<close> by metis
  have "h (from_FSM M q1') \<subseteq> h (from_FSM M q1)"
    using from_FSM_h[OF \<open>q1' \<in> nodes (from_FSM M q1)\<close>] by simp
  then have *: "(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h (from_FSM M q1)"
    using \<open>(fst (t_source t), t_input t, t_output t, fst (t_target t)) \<in> h (from_FSM M q1')\<close> by blast

  have "q2' \<in> nodes (from_FSM M q2)"
    using path_target_is_node[OF \<open>path (from_FSM M q2) q2 (right_path p)\<close>] \<open>target (right_path p) q2 = q2'\<close> by metis
  have "h (from_FSM M q2') \<subseteq> h (from_FSM M q2)"
    using from_FSM_h[OF \<open>q2' \<in> nodes (from_FSM M q2)\<close>] by simp
  then have **: "(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h (from_FSM M q2)"
    using \<open>(snd (t_source t), t_input t, t_output t, snd (t_target t)) \<in> h (from_FSM M q2')\<close> by blast

  have ***: "(\<exists>p1 p2.
               path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
               path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
               target p1 (initial (from_FSM M q1)) = fst (t_source t) \<and>
               target p2 (initial (from_FSM M q2)) = snd (t_source t) \<and> p_io p1 = p_io p2)"
  proof -
    obtain p1' p2' where "path (from_FSM M q1') q1' p1'"
                     and "path (from_FSM M q2') q2' p2'"
                     and "target p1' q1' = fst (t_source t)"
                     and "target p2' q2' = snd (t_source t)" 
                     and "p_io p1' = p_io p2'"
      using p'' by auto

    have "path (from_FSM M q1) q1' p1'"
      using from_FSM_path \<open>q1' \<in> nodes (from_FSM M q1)\<close> \<open>path (from_FSM M q1') q1' p1'\<close> by (metis from_from)
    have "path (from_FSM M q2) q2' p2'"
      using from_FSM_path \<open>q2' \<in> nodes (from_FSM M q2)\<close> \<open>path (from_FSM M q2') q2' p2'\<close> by (metis from_from)

    have "path (from_FSM M q1) (initial (from_FSM M q1)) ((left_path p)@p1')" 
      using path_append[OF \<open>path (from_FSM M q1) q1 (left_path p)\<close>, of p1']  \<open>target (left_path p) q1 = q1'\<close> \<open>path (from_FSM M q1) q1' p1'\<close> by auto
    moreover have "path (from_FSM M q2) (initial (from_FSM M q2)) ((right_path p)@p2')" 
      using path_append[OF \<open>path (from_FSM M q2) q2 (right_path p)\<close>, of p2']  \<open>target (right_path p) q2 = q2'\<close> \<open>path (from_FSM M q2) q2' p2'\<close> by auto
    moreover have "target ((left_path p)@p1') (initial (from_FSM M q1)) = fst (t_source t)"
      using path_target_append[OF \<open>target (left_path p) q1 = q1'\<close> \<open>target p1' q1' = fst (t_source t)\<close>] by auto
    moreover have "target ((right_path p)@p2') (initial (from_FSM M q2)) = snd (t_source t)"
      using path_target_append[OF \<open>target (right_path p) q2 = q2'\<close> \<open>target p2' q2' = snd (t_source t)\<close>] by auto
    moreover have "p_io ((left_path p)@p1') = p_io ((right_path p)@p2')"
      using \<open>p_io p1' = p_io p2'\<close> by auto
    ultimately show ?thesis by blast
  qed

  show "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
    using product_transition_t[of t "from_FSM M q1" "from_FSM M q2"] * ** *** by blast
qed



lemma product_from_path:
  assumes "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))" 
      and "path (product (from_FSM M q1') (from_FSM M q2')) (q1',q2') p" 
    shows "path (product (from_FSM M q1) (from_FSM M q2)) (q1',q2') p"
using h_subset_path[OF product_from_transition_subset[OF assms(1)] assms(2) assms(1)] by assumption


lemma product_from_path_previous :
  assumes "path (product (from_FSM M (fst (t_target t))) 
                         (from_FSM M (snd (t_target t))))
                (t_target t) p"                                           (is "path ?Pt (t_target t) p")
      and "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
    shows "path (product (from_FSM M q1) (from_FSM M q2)) (t_target t) p" (is "path ?P (t_target t) p")
proof -
  have *: "(t_target t) \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
    using wf_transition_target[OF assms(2)] by (metis)
  then have **: "(fst (t_target t), snd (t_target t)) \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
    by (metis prod.collapse)
  have ***: "h ?Pt \<subseteq> h ?P" 
    using product_from_transition_subset[OF **] by assumption
  show ?thesis
    using h_subset_path[OF *** assms(1) *] by assumption
qed


lemma product_from_transition_shared_node :
  assumes "t \<in> h (product (from_FSM M q1') (from_FSM M q2'))"
  and  "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))" 
shows "t \<in> h (product (from_FSM M q1) (from_FSM M q2))"
  by (meson assms(1) assms(2) contra_subsetD product_from_transition_subset)

    

lemma product_from_not_completely_specified :
  assumes "\<not> completely_specified_state (product (from_FSM M q1) (from_FSM M q2)) (q1',q2')"
      and "(q1',q2') \<in> nodes (product (from_FSM M q1) (from_FSM M q2))"
    shows  "\<not> completely_specified_state (product (from_FSM M q1') (from_FSM M q2')) (q1',q2')"
  using assms(1) assms(2) from_FSM_product_inputs[of M q1 q2] from_FSM_product_inputs[of M q1' q2'] product_from_transition_shared_node[OF _ assms(2)] 
  unfolding completely_specified_state.simps by metis

lemma from_product_initial_paths_ex :
  "(\<exists>p1 p2.
         path (from_FSM M q1) (initial (from_FSM M q1)) p1 \<and>
         path (from_FSM M q2) (initial (from_FSM M q2)) p2 \<and>
         target p1 (initial (from_FSM M q1)) = q1 \<and>
         target p2 (initial (from_FSM M q2)) = q2 \<and> p_io p1 = p_io p2)"
proof -
  have "path (from_FSM M q1) (initial (from_FSM M q1)) []" by blast
  moreover have "path (from_FSM M q2) (initial (from_FSM M q2)) []" by blast
  moreover have "
         target [] (initial (from_FSM M q1)) = q1 \<and>
         target [] (initial (from_FSM M q2)) = q2 \<and> p_io [] = p_io []" by auto
  ultimately show ?thesis by blast
qed

end