theory Backwards_Reachability_Analysis
imports FSM
begin



lemma remove1_length : "x \<in> set xs \<Longrightarrow> length (remove1 x xs) < length xs" 
  by (induction xs; auto)


function select_inputs :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "select_inputs f q0 inputList [] nodeSet m = (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> m)" |
  "select_inputs f q0 inputList (n#nL) nodeSet m = 
    (case find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList of 
      Some x \<Rightarrow> m@[(q0,x)] |
      None   \<Rightarrow> (case find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) (n#nL) inputList
          of None            \<Rightarrow> m |
             Some (q',x,nodeList') \<Rightarrow> select_inputs f q0 inputList nodeList' (insert q' nodeSet) (m@[(q',x)])))"
  by pat_completeness auto
termination 
apply (relation "measure (\<lambda> (f,q0,iL,nL,nS,m) . length nL)")
 apply simp
proof -
  fix f :: "(('a \<times> 'b) \<Rightarrow> ('c \<times> 'a) set)"
  fix q0 :: 'a
  fix inputList :: "'b list"
  fix n :: 'a
  fix nL :: "'a list" 
  fix nodeSet :: "'a set"
  fix m :: "('a \<times> 'b) list" 
  fix qynL' q ynL' x nL'
  assume "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None"
     and "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> nodeSet)) (n # nL) inputList = Some qynL'"
     and "(q, ynL') = qynL'"
     and "(x, nL') = ynL'"

  then have *: "find_remove_2 (\<lambda>q' x. f (q', x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q', x). q'' \<in> nodeSet)) (n # nL) inputList = Some (q,x,nL')"
    by auto

  have "q \<in> set (n # nL)"
  and  "nL' = remove1 q (n # nL)"
    using find_remove_2_set(2,6)[OF *] by simp+

  then have "length nL' < length (n # nL)"
    using remove1_length by metis
    

  then show "((f, q0, inputList, nL', insert q nodeSet, m @ [(q, x)]), f, q0, inputList, n # nL, nodeSet, m) \<in> measure (\<lambda>(f, q0, iL, nL, nS, m). length nL)"
    by auto
qed




lemma select_inputs_length :
  "length (select_inputs f q0 inputList nodeList nodeSet m) \<le> (length m) + Suc (length nodeList)"
proof (induction "length nodeList" arbitrary: nodeList nodeSet m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "nodeList = n # nL"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None\<close> unfolding \<open>nodeList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) (n#nL) inputList = Some (q',x,nodeList')"
        unfolding \<open>nodeList = n # nL\<close> by (metis prod_cases3)
      have "k = length nodeList'"
        using find_remove_2_length[OF *] \<open>Suc k = length nodeList\<close> unfolding \<open>nodeList = n # nL\<close>
        by simp
      show ?thesis 
        unfolding \<open>nodeList = n # nL\<close> select_inputs.simps None *
        using Suc.hyps(1)[of nodeList' "insert q' nodeSet" "m@[(q',x)]", OF \<open>k = length nodeList'\<close>] unfolding find_remove_2_length[OF *] by simp
    qed
  next
    case (Some a)
    then show ?thesis unfolding \<open>nodeList = n # nL\<close> by auto
  qed
qed


lemma select_inputs_length_min :
  "length (select_inputs f q0 inputList nodeList nodeSet m) \<ge> (length m)"
proof (induction "length nodeList" arbitrary: nodeList nodeSet m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "nodeList = n # nL"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None\<close> unfolding \<open>nodeList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) (n#nL) inputList = Some (q',x,nodeList')"
        unfolding \<open>nodeList = n # nL\<close> by (metis prod_cases3)
      have "k = length nodeList'"
        using find_remove_2_length[OF *] \<open>Suc k = length nodeList\<close> unfolding \<open>nodeList = n # nL\<close>
        by simp
      show ?thesis 
        unfolding \<open>nodeList = n # nL\<close> select_inputs.simps None *
        using Suc.hyps(1)[of nodeList' "m@[(q',x)]" "insert q' nodeSet" , OF \<open>k = length nodeList'\<close>] unfolding find_remove_2_length[OF *] by simp
    qed
  next
    case (Some a)
    then show ?thesis unfolding \<open>nodeList = n # nL\<close> by auto
  qed
qed



lemma select_inputs_helper1 :
  "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x \<Longrightarrow> (select_inputs f q0 iL nL nS m) = m@[(q0,x)]" 
  by (cases nL; auto)



(*
lemma select_inputs_next :
  "\<exists> m' . (select_inputs f q0 iL nL nS (Suc k) m) = (select_inputs f q0 iL nL nS k m)@m'" 
proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
  case None
  then show ?thesis proof (induction k arbitrary: nL nS m)
    case 0
    show ?case proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      show ?thesis unfolding select_inputs.simps \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
    next
      case (Some a)
      then obtain q' x nodeList' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nodeList')"
          by (metis prod_cases3)
      show ?thesis unfolding select_inputs.simps None **
        by (simp add: option.case_eq_if) 
    qed
  next
    case (Suc k')
    show ?case proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis unfolding select_inputs.simps \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None by auto
    next
      case (Some a)
      then obtain q' x nodeList' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nodeList')"
          by (metis prod_cases3)
      show ?thesis proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>a\<in>f (q0, x). case a of (y, q'') \<Rightarrow> q'' \<in> (insert q' nS))) iL")
        case None
        show ?thesis 
          using Suc.IH[OF None]
          using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> ** by auto
      next
        case (Some x')

        have "select_inputs f q0 iL nL nS (Suc (Suc k')) m = select_inputs f q0 iL nodeList' (insert q' nS) (Suc k') (m@[(q',x)])"
         and "select_inputs f q0 iL nL nS (Suc k') m = select_inputs f q0 iL nodeList' (insert q' nS) k' (m@[(q',x)])"
          using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> ** 
          by auto
        then have "select_inputs f q0 iL nL nS (Suc (Suc k')) m = select_inputs f q0 iL nL nS (Suc k') m"
          unfolding select_inputs_helper1[OF Some] by auto

        then show ?thesis by auto
      qed
    qed
  qed
next
  case (Some a)
  show ?thesis using select_inputs_helper1[OF Some]
    by (metis append_Nil2) 
qed





lemma select_inputs_prefix :
  assumes "i \<le> k"
  shows "take (length (select_inputs f q0 iL nL nS i m)) (select_inputs f q0 iL nL nS k m) = (select_inputs f q0 iL nL nS i m)" 
using assms proof (induction "k - i" arbitrary: nL nS m k i)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "i < k" by auto
  
  show ?case proof (cases d)
    case 0
    then have "k = Suc i" using Suc by auto
    show ?thesis unfolding \<open>k = Suc i\<close> using select_inputs_next[of f q0 iL nL nS i m]
      by auto 
  next
    case (Suc d')
    moreover obtain k' where "k = Suc k'"
      using Suc.hyps by (metis Suc_le_D diff_le_self) 
    ultimately have "Suc d = Suc k' - i" using Suc.hyps(2) by auto 
    then have "d = k' - i" by auto 

    have "i \<le> k'" using \<open>k = Suc k'\<close> \<open>i < k\<close> by auto

    show ?thesis 
      using Suc.hyps(1)[OF \<open>d = k' - i\<close> \<open>i \<le> k'\<close>]
      by (metis \<open>k = Suc k'\<close> append_assoc append_eq_conv_conj append_take_drop_id select_inputs_next) 
  qed
qed


lemma select_inputs_prefix_ex :
  assumes "i \<le> k"
  shows "\<exists> m' . (select_inputs f q0 iL nL nS k m) = (select_inputs f q0 iL nL nS i m) @ m'" 
  using select_inputs_prefix[OF assms] by (metis (no_types) append_take_drop_id)
*)  

lemma select_inputs_take :
  "take (length m) (select_inputs f q0 inputList nodeList nodeSet m) = m"
proof (induction "length nodeList" arbitrary: nodeList nodeSet m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList"; auto)
next
  case (Suc k)
  then obtain n nL where "nodeList = n # nL"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nodeSet))) inputList")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) nodeList inputList")
      case None
      then show ?thesis using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nodeSet)) inputList = None\<close> unfolding \<open>nodeList = n # nL\<close> by auto
    next
      case (Some a)
      then obtain q' x nodeList' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nodeSet))) (n#nL) inputList = Some (q',x,nodeList')"
        unfolding \<open>nodeList = n # nL\<close> by (metis prod_cases3)
      have "k = length nodeList'"
        using find_remove_2_length[OF *] \<open>Suc k = length nodeList\<close> unfolding \<open>nodeList = n # nL\<close>
        by simp

      have **: "(select_inputs f q0 inputList nodeList nodeSet m) = select_inputs f q0 inputList nodeList' (insert q' nodeSet) (m @ [(q', x)])"
        unfolding \<open>nodeList = n # nL\<close> select_inputs.simps None * by simp
      show ?thesis
        unfolding **
        using Suc.hyps(1)[of nodeList' "m@[(q',x)]" "insert q' nodeSet" , OF \<open>k = length nodeList'\<close>] unfolding find_remove_2_length[OF *]
        by (metis butlast_snoc butlast_take diff_Suc_1 length_append_singleton select_inputs_length_min) 
    qed
  next
    case (Some a)
    then show ?thesis unfolding \<open>nodeList = n # nL\<close> by auto
  qed
qed




lemma select_inputs_take' :
  "take (length m) (select_inputs f q0 iL nL nS (m@m')) = m"
  using select_inputs_take
  by (metis (no_types, lifting) add_leE append_eq_append_conv select_inputs_length_min length_append length_take min_absorb2 take_add)



lemma select_inputs_distinct :
  assumes "distinct (map fst m)"
  and     "set (map fst m) \<subseteq> nS"
  and     "q0 \<notin> nS"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
  shows "distinct (map fst (select_inputs f q0 iL nL nS m))" 
using assms proof (induction "length nL" arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL"; auto)
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then have "(select_inputs f q0 iL nL nS m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> unfolding \<open>nL = n # nL''\<close> by auto
      then show ?thesis using Suc.prems by auto
    next
      case (Some a)
      then obtain q' x nL' where *: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      have "k = length nL'"
        using find_remove_2_length[OF *] \<open>Suc k = length nL\<close> by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using *
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto


      have "q' \<in> set nL"
      and  "set nL' = set nL - {q'}"
      and  "distinct nL'"
        using find_remove_2_set[OF * ]  \<open>distinct nL\<close> by auto

      have "distinct (map fst (m@[(q',x)]))" 
        using \<open>(set (map fst m)) \<subseteq> nS\<close> \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
      have "q0 \<notin> insert q' nS"
        using Suc.prems(3) Suc.prems(5) \<open>q' \<in> set nL\<close> by auto
      have "set (map fst (m@[(q',x)])) \<subseteq> insert q' nS" 
        using \<open>(set (map fst m)) \<subseteq> nS\<close> by auto
      have "(set (map fst (m@[(q',x)]))) \<subseteq> insert q' nS"
        using\<open>(set (map fst m)) \<subseteq> nS\<close> by auto
      have "q0 \<notin> set nL'"
        by (simp add: Suc.prems(5) \<open>set nL' = set nL - {q'}\<close>)
      have "set nL' \<inter> insert q' nS = {}"
        using Suc.prems(6) \<open>set nL' = set nL - {q'}\<close> by auto

      show ?thesis 
        unfolding select_inputs.simps None *
        using Suc.hyps(1)[OF \<open>k = length nL'\<close> \<open>distinct (map fst (m@[(q',x)]))\<close>
                               \<open>set (map fst (m@[(q',x)])) \<subseteq> insert q' nS\<close>
                               \<open>q0 \<notin> insert q' nS\<close>
                               \<open>distinct nL'\<close>
                               \<open>q0 \<notin> set nL'\<close>
                               \<open>set nL' \<inter> insert q' nS = {}\<close>]
        unfolding \<open>select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])\<close> by assumption
    qed
  next
    case (Some a)
    then show ?thesis using Suc \<open>nL = n # nL''\<close> by auto
  qed
qed




lemma select_inputs_index_properties : 
  assumes "i < length (select_inputs (h M) q0 iL nL nS m)"
  and     "i \<ge> length m"
  and     "distinct (map fst m)"
  and     "nS = nS0 \<union> set (map fst m)"
  and     "q0 \<notin> nS"
  and     "distinct nL"
  and     "q0 \<notin> set nL"
  and     "set nL \<inter> nS = {}"
shows "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))" 
      "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
      "snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL"
      "(\<forall> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx')"
      "(\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))"
      "(\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"
proof -
  have combined_props : 
    "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))
      \<and> snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL
      \<and> fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0
      \<and> (\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))
      \<and> (\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"    
  using assms proof (induction "length nL" arbitrary: nL nS m)
    case 0
    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      then have "(select_inputs (h M) q0 iL nL nS m) = m" using 0 by auto
      then have "False" using "0.prems"(1,2) by auto
      then show ?thesis by simp
    next
      case (Some x)
      have "(select_inputs (h M) q0 iL nL nS m) = m@[(q0,x)]" using select_inputs_helper1[OF Some] by assumption
      then have "(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)" using "0.prems"(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
      moreover have "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
        using \<open>select_inputs (h M) q0 iL nL nS m ! i = (q0, x)\<close> assms(4) assms(5) by auto
       
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (mono_tags, lifting) case_prod_beta' mem_Collect_eq prod.collapse) 
        then show "t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"
          using \<open>nS = nS0 \<union> set (map fst m)\<close>
          using "0.prems"(1) "0.prems"(2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)\<close> by blast
    qed
  next
    case (Suc k)
    then obtain n nL'' where "nL = n # nL''"
      by (meson Suc_length_conv) 

    show ?case proof (cases "find (\<lambda> x . (h M) (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q0,x) . (q'' \<in> nS))) iL")
      case None
      show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL")
        case None
        then have "(select_inputs (h M) q0 iL nL nS m) = m" using \<open>find (\<lambda>x. h M (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>h M (q0, x). q'' \<in> nS)) iL = None\<close> \<open>nL = n # nL''\<close> by auto
        then have "False" using Suc.prems(1,2) by auto
        then show ?thesis by simp
      next
        case (Some a)
        then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . (h M) (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> (h M) (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)

        have "k = length nL'"
          using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

        have "select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
          using **
          unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
        then have "i < length (select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)]))"
          using Suc.prems(1) by auto

        have "(set (map fst (m @ [(q', x)]))) \<subseteq> insert q' nS"
          using Suc.prems(4) by auto

        have "q' \<in> set nL"
        and  "set nL' = set nL - {q'}"
        and  "distinct nL'"
          using find_remove_2_set[OF ** ]  \<open>distinct nL\<close> by auto
        have "set nL' \<subseteq> set nL"
          using find_remove_2_set(4)[OF ** \<open>distinct nL\<close>] by blast

        have "distinct (map fst (m @ [(q', x)]))" 
          using Suc.prems(4) \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "distinct (map fst (m@[(q',x)]))" 
          using Suc.prems(4) \<open>set nL \<inter> nS = {}\<close> \<open>q' \<in> set nL\<close> \<open>distinct (map fst m)\<close> by auto
        have "q0 \<notin> insert q' nS"
          using Suc.prems(7) Suc.prems(5) \<open>q' \<in> set nL\<close> by auto
        have "insert q' nS = nS0 \<union> set (map fst (m@[(q',x)]))" 
          using Suc.prems(4) by auto
        have "q0 \<notin> set nL'"
          by (metis Suc.prems(7) \<open>set nL' \<subseteq> set nL\<close> subset_code(1))
        have "set nL' \<inter> insert q' nS = {}"
          using Suc.prems(8) \<open>set nL' = set nL - {q'}\<close> by auto


        show ?thesis proof (cases "length (m @ [(q', x)]) \<le> i")
          case True

          show ?thesis
            using Suc.hyps(1)[OF \<open>k = length nL'\<close> \<open>i < length (select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)]))\<close>
                            True
                            \<open>distinct (map fst (m @ [(q', x)]))\<close>
                            \<open>insert q' nS = nS0 \<union> set (map fst (m@[(q',x)]))\<close>
                            \<open>q0 \<notin> insert q' nS\<close>
                            \<open>distinct nL'\<close>
                            \<open>q0 \<notin> set nL'\<close>
                            \<open>set nL' \<inter> insert q' nS = {}\<close> ]
            unfolding \<open>select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> 
            using \<open>set nL' \<subseteq> set nL\<close> by blast
        next
          case False 
          then have "i = length m"
            using Suc.prems(2) by auto
          then have ***: "select_inputs (h M) q0 iL nL nS m ! i = (q',x)"
            unfolding \<open>select_inputs (h M) q0 iL nL nS m = select_inputs (h M) q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> 
            using select_inputs_take
            by (metis length_append_singleton lessI nth_append_length nth_take) 
            
          
          have "q' \<in> insert q0 (set nL)"
            by (simp add: \<open>q' \<in> set nL\<close>) 
          moreover have "x \<in> set iL"
            using find_remove_2_set(3)[OF ** ] by auto
          moreover have "q' \<notin> nS0"
            using Suc.prems(4) Suc.prems(8) \<open>q' \<in> set nL\<close> by blast
          moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x) "
            using find_remove_2_set(1)[OF ** ] unfolding h.simps by force
          moreover have "(\<forall>t\<in>FSM.transitions M. t_source t = q' \<and> t_input t = x \<longrightarrow> t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t))"
            unfolding \<open>i = length m\<close> select_inputs_take 
            using find_remove_2_set(1)[OF ** ] unfolding h.simps \<open>nS = nS0 \<union> (set (map fst m))\<close> by force
          ultimately show ?thesis 
            unfolding *** fst_conv snd_conv by blast
        qed 
      qed
    next
      case (Some x)
      have "(select_inputs (h M) q0 iL nL nS m) = m@[(q0,x)]" using select_inputs_helper1[OF Some] by assumption
      then have "(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)" using Suc.prems(1,2)
        using antisym by fastforce 
  
      have "fst (q0, x) \<in> insert q0 (set nL)" by auto
      moreover have "snd (q0, x) \<in> set iL" using find_set[OF Some] by auto
      moreover have "fst (q0, x) \<notin> nS0"
        using assms(4) assms(5) by auto 
      moreover have "\<And> qx' . qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) - set (take (length m) (select_inputs (h M) q0 iL nL nS m)) \<Longrightarrow> fst (q0, x) \<noteq> fst qx'"
        using Suc.prems(1,2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by auto
      moreover have "(\<exists>t\<in>FSM.transitions M. t_source t = fst (q0, x) \<and> t_input t = snd (q0, x))"
        using find_condition[OF Some] unfolding fst_conv snd_conv h.simps
        by fastforce 
      moreover have "\<And> t . t \<in> FSM.transitions M \<Longrightarrow>
          t_source t = fst (q0, x) \<Longrightarrow> t_input t = snd (q0, x) \<Longrightarrow>
          t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"   
      proof -
        fix t assume "t \<in> FSM.transitions M" "t_source t = fst (q0, x)" "t_input t = snd (q0, x)"
        then have "t_target t \<in> nS"
          using find_condition[OF Some] unfolding h.simps fst_conv snd_conv
          by (metis (mono_tags, lifting) case_prod_beta' mem_Collect_eq prod.collapse) 
        then show "t_target t \<in> nS0 \<or> (\<exists>qx'\<in>set (take i (select_inputs (h M) q0 iL nL nS m)). fst qx' = t_target t)"
          using \<open>nS = nS0 \<union> (set (map fst m))\<close>
          using Suc.prems(1,2) \<open>select_inputs (h M) q0 iL nL nS m = m @ [(q0, x)]\<close> by fastforce    
      qed
        
      ultimately show ?thesis 
        unfolding \<open>(select_inputs (h M) q0 iL nL nS m ! i) = (q0,x)\<close> by blast
    qed
  qed

  then show "fst (select_inputs (h M) q0 iL nL nS m ! i) \<in> (insert q0 (set nL))"
            "snd (select_inputs (h M) q0 iL nL nS m ! i) \<in> set iL"
            "fst (select_inputs (h M) q0 iL nL nS m ! i) \<notin> nS0"
            "(\<exists> t \<in> transitions M . t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i))"
            "(\<forall> t \<in> transitions M . (t_source t = fst (select_inputs (h M) q0 iL nL nS m ! i) \<and> t_input t = snd (select_inputs (h M) q0 iL nL nS m ! i)) \<longrightarrow> (t_target t \<in> nS0 \<or> (\<exists> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst qx' = (t_target t))))"
    by blast+

  show "(\<forall> qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m)) . fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx')" 
  proof 
    fix qx' assume "qx' \<in> set (take i (select_inputs (h M) q0 iL nL nS m))"
    then obtain j where "(take i (select_inputs (h M) q0 iL nL nS m)) ! j = qx'" and "j < length (take i (select_inputs (h M) q0 iL nL nS m))"
      by (meson in_set_conv_nth)
    then have "fst qx' = (map fst (select_inputs (h M) q0 iL nL nS m)) ! j" and "j < length (select_inputs (h M) q0 iL nL nS m)" by auto
      
    moreover have "fst (select_inputs (h M) q0 iL nL nS m ! i) = (map fst (select_inputs (h M) q0 iL nL nS m)) ! i"
      using assms(1) by auto

    moreover have "j \<noteq> i" 
      using \<open>j < length (take i (select_inputs (h M) q0 iL nL nS m))\<close> by auto

    moreover have "set (map fst m) \<subseteq> nS"
      using \<open>nS = nS0 \<union> set (map fst m)\<close> by blast

    ultimately show "fst (select_inputs (h M) q0 iL nL nS m ! i) \<noteq> fst qx'"
      using assms(1)
      using select_inputs_distinct[OF \<open>distinct (map fst m)\<close> _ \<open>q0 \<notin> nS\<close> \<open>distinct nL\<close> \<open>q0 \<notin> set nL\<close> \<open>set nL \<inter> nS = {}\<close>]
      by (metis distinct_Ex1 in_set_conv_nth length_map)
  qed
qed 


(*
lemma select_inputs_Suc_length :
  assumes "(select_inputs f q0 iL nL nS (Suc k) m) \<noteq> (select_inputs f q0 iL nL nS k m)"
  shows "length (select_inputs f q0 iL nL nS k m) = (length m) + k"
using assms proof (induction k arbitrary: nS nL m)
  case 0
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    then show ?thesis by auto
  next
    case (Some x)
    then have "(select_inputs f q0 iL nL nS (Suc 0) m) = (select_inputs f q0 iL nL nS 0 m)"
      unfolding select_inputs_helper1[OF Some] by auto
    then show ?thesis 
      using "0.prems" by simp
  qed
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      have "(select_inputs f q0 iL nL nS (Suc (Suc k)) m) = (select_inputs f q0 iL nL nS (Suc k) m)"
        unfolding select_inputs.simps None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
      then show ?thesis 
        using Suc.prems by simp
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
          by (metis prod_cases3)

      have d1:"(select_inputs f q0 iL nL nS (Suc (Suc k)) m) = select_inputs f q0 iL nL' (insert q' nS) (Suc k) (m@[(q',x)])"
      and  d2:"(select_inputs f q0 iL nL nS (Suc k) m) = select_inputs f q0 iL nL' (insert q' nS) k (m@[(q',x)])"
        using None ** by auto


      show ?thesis proof (cases "select_inputs f q0 iL nL' (insert q' nS) (Suc k) (m@[(q',x)]) \<noteq> select_inputs f q0 iL nL' (insert q' nS) k (m@[(q',x)])")
        case True
        show ?thesis 
          using Suc.IH[OF True] unfolding d2 by auto
      next
        case False
        then have "(select_inputs f q0 iL nL nS (Suc (Suc k)) m) = (select_inputs f q0 iL nL nS (Suc k) m)"
          unfolding d1 d2 by auto
        then show ?thesis using Suc.prems by simp
      qed
    qed

  next
    case (Some x)
    then have "(select_inputs f q0 iL nL nS (Suc (Suc k)) m) = (select_inputs f q0 iL nL nS (Suc k) m)"
      unfolding select_inputs_helper1[OF Some] by auto
    then show ?thesis 
      using Suc.prems by simp
  qed
qed




lemma select_inputs_Suc_eq :
  assumes "(select_inputs f q0 iL nL nS (Suc k) m) = (select_inputs f q0 iL nL nS k m)"
  shows "(select_inputs f q0 iL nL nS (Suc (Suc k)) m) = (select_inputs f q0 iL nL nS k m)" 
using assms proof (induction k arbitrary: nS nL m)
  case 0
  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    then have "(select_inputs f q0 iL nL nS 0 m) = m" using None by auto
    then have "(select_inputs f q0 iL nL nS (Suc 0) m) = m" using 0 by auto
    then have "(select_inputs f q0 iL nL nS (Suc (Suc 0)) m) = m"
      by (metis Zero_not_Suc add_eq_self_zero select_inputs_Suc_length) 
    then show ?thesis using \<open>(select_inputs f q0 iL nL nS 0 m) = m\<close> by auto
  next
    case (Some a)
    show ?thesis using assms unfolding select_inputs_helper1[OF Some] by simp
  qed
next
  case (Suc k)
  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      then show ?thesis unfolding Suc using None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> by auto
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      show ?thesis proof (rule ccontr)
        assume "select_inputs f q0 iL nL nS (Suc (Suc (Suc k))) m \<noteq> select_inputs f q0 iL nL nS (Suc k) m"
        then have "select_inputs f q0 iL nL' (insert q' nS) (Suc (Suc k)) (m@[(q',x)]) \<noteq> select_inputs f q0 iL nL' (insert q' nS) k (m@[(q',x)])"
          using None ** by auto
        then have "select_inputs f q0 iL nL' (insert q' nS) (Suc k) (m @ [(q', x)]) \<noteq> select_inputs f q0 iL nL' (insert q' nS) k (m@[(q',x)])"
          using Suc.IH[of nL' "insert q' nS" "(m@[(q',x)])" ] by blast
        then have "select_inputs f q0 iL nL nS (Suc (Suc k)) m \<noteq> select_inputs f q0 iL nL nS (Suc k) m"
          using None ** by auto
        then show "False"
          using Suc.prems by auto
      qed
    qed
  next
    case (Some a)
    show ?thesis using assms unfolding select_inputs_helper1[OF Some] by simp
  qed
qed


lemma select_inputs_gte_eq :
  assumes "(select_inputs f q0 iL nL nS (Suc i) m) = (select_inputs f q0 iL nL nS i m)"
  and     "i \<le> k"
shows "(select_inputs f q0 iL nL nS k m) = (select_inputs f q0 iL nL nS i m)" 
  using assms proof (induction "k-i" arbitrary: k i)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "d = k - Suc i" and "Suc i \<le> k" by auto

  have "(select_inputs f q0 iL nL nS k m) = (select_inputs f q0 iL nL nS (Suc i) m)"
    using Suc.hyps(1)[OF \<open>d = k - Suc i\<close> _ \<open>Suc i \<le> k\<close>]
    using select_inputs_Suc_eq[OF Suc.prems(1)] Suc.prems(1) by metis
  then show ?case 
    using Suc.prems(1) by simp
qed


lemma select_inputs_prefix_length :
  assumes "i \<le> k"
  and     "(select_inputs f q0 iL nL nS k m) \<noteq> (select_inputs f q0 iL nL nS i m)"
shows "length (select_inputs f q0 iL nL nS i m) = (length m) + i"
  using assms proof (induction "k - i" arbitrary: k i nS nL m)
  case 0
  then show ?case by auto
next
  case (Suc d)
  then have "d = k - Suc i" and "Suc i \<le> k" by auto


  show ?case proof (cases "select_inputs f q0 iL nL nS (Suc i) m = select_inputs f q0 iL nL nS i m")
    case True
    then have "(select_inputs f q0 iL nL nS k m) = (select_inputs f q0 iL nL nS i m)"
      using select_inputs_gte_eq[OF _ \<open>i \<le> k\<close>] by metis
    then have "False"
      using \<open>(select_inputs f q0 iL nL nS k m) \<noteq> (select_inputs f q0 iL nL nS i m)\<close> by simp
    then show ?thesis by simp
  next
    case False
    then show ?thesis using select_inputs_Suc_length by metis
  qed
qed
*)

lemma select_inputs_initial :
  assumes "qx \<in> set (select_inputs f q0 iL nL nS m) - set m"
  and     "fst qx = q0"
  shows "(last (select_inputs f q0 iL nL nS m)) = qx"
using assms(1) proof (induction "length nL" arbitrary: nS nL m)
  case 0
  then have "nL = []" by auto

  have "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL \<noteq> None" 
    using 0 unfolding \<open>nL = []\<close> select_inputs.simps 
    by (metis Diff_cancel empty_iff option.simps(4))
  then obtain x where *: "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = Some x" 
    by auto
  
  have "set (select_inputs f q0 iL nL nS m) - set m = {qx}"
    using "0.prems"(1) unfolding select_inputs_helper1[OF *]
    by auto 
  
  then show ?case unfolding select_inputs_helper1[OF *]
    by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append) 
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      have "(select_inputs f q0 iL nL nS m) = m"
        using \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close> None \<open>nL = n # nL''\<close> by auto
      then have "False" 
        using Suc.prems(1)
        by simp
      then show ?thesis by simp
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)

      have "k = length nL'"
        using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using **
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
      then have "qx \<in> set (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) - set m"
        using Suc.prems by auto
      moreover have "q0 \<noteq> q'"
        using None unfolding find_None_iff
        using find_remove_2_set(1,2,3)[OF **]
        by blast
      ultimately have "qx \<in> set (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) - set (m@[(q',x)])"
        using \<open>fst qx = q0\<close> by auto
      then show ?thesis 
        using Suc.hyps unfolding \<open>(select_inputs f q0 iL nL nS m) = (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)]))\<close>
        using \<open>k = length nL'\<close> by blast 
    qed
  next
    case (Some a)

    have "set (select_inputs f q0 iL nL nS m ) - set m = {qx}"
      using Suc.prems(1) unfolding select_inputs_helper1[OF Some]
      by auto 
    
    then show ?thesis unfolding select_inputs_helper1[OF Some]
      by (metis DiffD1 DiffD2 UnE empty_iff empty_set insert_iff last_snoc list.simps(15) set_append)
  qed 
qed



lemma select_inputs_max_length :
  assumes "distinct nL"
  shows "length (select_inputs f q0 iL nL nS m) \<le> length m + Suc (length nL)" 
using assms proof (induction "length nL" arbitrary: nL nS m)
  case 0
  then show ?case by (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL"; auto)
next
  case (Suc k)
  then obtain n nL'' where "nL = n # nL''"
    by (meson Suc_length_conv) 

  show ?case proof (cases "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL")
    case None
    show ?thesis proof (cases "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL")
      case None
      show ?thesis unfolding \<open>nL = n # nL''\<close> select_inputs.simps None \<open>find (\<lambda>x. f (q0, x) \<noteq> {} \<and> (\<forall>(y, q'')\<in>f (q0, x). q'' \<in> nS)) iL = None\<close>
        using None \<open>nL = n # nL''\<close> by auto 
    next
      case (Some a)
      then obtain q' x nL' where **: "find_remove_2 (\<lambda> q' x . f (q',x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q',x) . (q'' \<in> nS))) nL iL = Some (q',x,nL')"
        by (metis prod_cases3)
      have "k = length nL'"
        using find_remove_2_length[OF **] \<open>Suc k = length nL\<close> by simp

      have "select_inputs f q0 iL nL nS m = select_inputs f q0 iL nL' (insert q' nS) (m @ [(q', x)])" 
        using **
        unfolding  \<open>nL = n # nL''\<close> select_inputs.simps None by auto
      
      have "length nL = Suc (length nL') \<and> distinct nL'"
        using find_remove_2_set(2,4,5)[OF **] \<open>distinct nL\<close>
        by (metis One_nat_def Suc_pred distinct_card distinct_remove1 equals0D length_greater_0_conv length_remove1 set_empty2 set_remove1_eq) 
      then have "length (select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])) \<le> length m + Suc (length nL)"
        using Suc.hyps(1)[OF \<open>k = length nL'\<close>]
        by (metis add_Suc_shift length_append_singleton)
      then show ?thesis 
        using \<open>(select_inputs f q0 iL nL nS m) = select_inputs f q0 iL nL' (insert q' nS) (m@[(q',x)])\<close> by simp
    qed
  next
    case (Some a)
    show ?thesis unfolding select_inputs_helper1[OF Some] by auto 
  qed
qed


(* if q0 can be added, it will be added *)
lemma select_inputs_q0_containment :
  assumes "f (q0,x) \<noteq> {}"
  and     "(\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))"   
  and     "x \<in> set iL"
shows "(\<exists> qx \<in> set (select_inputs f q0 iL nL nS m) . fst qx = q0)" 
proof -
  have "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL \<noteq> None"
    using assms unfolding find_None_iff by blast
  then obtain x' where *: "find (\<lambda> x . f (q0,x) \<noteq> {} \<and> (\<forall> (y,q'') \<in> f (q0,x) . (q'' \<in> nS))) iL = Some x'"
    by auto
  show ?thesis 
    unfolding select_inputs_helper1[OF *] by auto
qed


end