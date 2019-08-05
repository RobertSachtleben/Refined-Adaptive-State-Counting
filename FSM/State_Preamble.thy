theory State_Preamble
imports ProductMachine
begin

section \<open>State Preambles\<close>

subsection \<open>Definitions\<close>

(* TODO: use actual definition
fun definitely_reachable :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<forall> S . completely_specified S \<and> is_submachine S M \<longrightarrow> q \<in> nodes S)"
*)

fun is_preamble :: "('a, 'b) FSM_scheme \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_preamble S M q = (acyclic S \<and> single_input S \<and> is_submachine S M \<and> q \<in> nodes S \<and> deadlock_state S q \<and> (\<forall> q' \<in> nodes S . (q = q' \<or> \<not> deadlock_state S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h S))))"

fun definitely_reachable :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> bool" where
  "definitely_reachable M q = (\<exists> S . is_preamble S M q)"

fun is_preamble_set :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "is_preamble_set M q P = (
    P \<subseteq> L M
    \<and> (\<forall> p . (path M (initial M) p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states (initial M) p))
    \<and> (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)
    \<and> (\<forall> xys xy y . (xys@[xy] \<in> P \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> P)
    \<and> (\<forall> xys \<in> P . ((io_target M xys (initial M) = q 
                     \<and> \<not> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
                   \<or> (\<not> io_target M xys (initial M) = q 
                        \<and> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
    \<and> (\<exists> xys \<in> P . io_target M xys (initial M) = q)
    \<and> (\<forall> xys1 xys2 . xys1@xys2 \<in> P \<longrightarrow> xys1 \<in> P)
  )"   



subsection \<open>Properties\<close>

lemma preamble_set_contains_empty_sequence :
  assumes "is_preamble_set M q P"
  shows "[] \<in> P" 
proof -
  from assms obtain xys where "xys \<in> P \<and> io_target M xys (initial M) = q" unfolding is_preamble_set.simps by blast
  then have "[] @ xys \<in> P" by auto
  then show ?thesis using assms unfolding is_preamble_set.simps by blast
qed

lemma preamble_has_preamble_set :
  assumes "observable M"
  and     "is_preamble S M q"
  shows "is_preamble_set M q (L S)"
proof (rule ccontr)
  assume "\<not> is_preamble_set M q (L S)"
  then consider
    (f1) "\<not> (L S \<subseteq> L M)" |
    (f2) "\<not> (\<forall> p . (path M (initial M) p \<and> p_io p \<in> L S) \<longrightarrow> distinct (visited_states (initial M) p))" |
    (f3) "\<not> (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> L S \<and> xys2@[xy2] \<in> L S \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)" |
    (f4) "\<not> (\<forall> xys xy y . (xys@[xy] \<in> L S \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> L S)" |
    (f5) "\<not> (\<forall> xys \<in> L S . ((io_target M xys (initial M) = q 
                     \<and> \<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))
                   \<or> (\<not> io_target M xys (initial M) = q 
                        \<and> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))" |
    (f6) "\<not> (\<exists> xys \<in> L S . io_target M xys (initial M) = q)" |
    (f7) "\<not> (\<forall> xys1 xys2 . xys1@xys2 \<in> L S \<longrightarrow> xys1 \<in> L S)"
    unfolding is_preamble_set.simps by blast
  then show "False"
  proof cases
    case f1 (* violates submachine property *)
    moreover have "L S \<subseteq> L M"  
      using assms(2) unfolding is_preamble.simps by (metis submachine_language)
    ultimately show "False" by simp 
  next
    case f2 (* violates acyclicness property (for observable M) *)
    then obtain p where "path M (initial M) p" and "p_io p \<in> L S" and "\<not> distinct (visited_states (initial M) p)"
      by blast
    from \<open>p_io p \<in> L S\<close> obtain p' where "path S (initial S) p'" and "p_io p' = p_io p"
      using LS.elims by auto 
    then have "path M (initial M) p'" 
      using assms(2) unfolding is_preamble.simps
      by (metis is_submachine.elims(2) submachine_path) 

    have "observable S"  
      using assms unfolding is_preamble.simps by (metis submachine_observable)
    have "p' = p"
      using observable_path_unique[OF \<open>observable M\<close> \<open>path M (initial M) p\<close> \<open>path M (initial M) p'\<close>] using \<open>p_io p' = p_io p\<close> by auto
    then have "\<not> distinct (visited_states (initial S) p')"
      using \<open>\<not> distinct (visited_states (initial M) p)\<close> assms(2) unfolding is_preamble.simps is_submachine.simps by simp
    then show "False"
      using assms(2) unfolding is_preamble.simps by (meson \<open>path S (initial S) p'\<close> acyclic.elims(2))
  next
    case f3 (* violates single-input property (for observable M) *)
    then obtain xys1 xys2 xy1 xy2 where "xys1@[xy1] \<in> L S" 
                                    and "xys2@[xy2] \<in> L S" 
                                    and "io_target M xys1 (initial M) = io_target M xys2 (initial M)"
                                    and "fst xy1 \<noteq> fst xy2" 
      by blast

    then obtain p1 p2 where "path S (initial S) p1" and "p_io p1 = xys1@[xy1]"
                        and "path S (initial S) p2" and "p_io p2 = xys2@[xy2]" 
      by auto
    let ?hp1 = "butlast p1"
    let ?hp2 = "butlast p2"
    let ?t1 = "last p1"
    let ?t2 = "last p2"

    have "path S (initial S) (?hp1@[?t1])" and "p_io (?hp1@[?t1]) = xys1@[xy1]"
      using \<open>path S (initial S) p1\<close> \<open>p_io p1 = xys1@[xy1]\<close> by (metis (no_types, lifting) Nil_is_map_conv snoc_eq_iff_butlast)+
    then have "path S (initial S) ?hp1" by blast
    then have "path M (initial M) ?hp1"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
    then have "target ?hp1 (initial M) = io_target M xys1 (initial M)"
      by (metis (mono_tags, lifting) \<open>p_io p1 = xys1 @ [xy1]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)
      

    have "path S (initial S) (?hp2@[?t2])" and "p_io (?hp2@[?t2]) = xys2@[xy2]"
      using \<open>path S (initial S) p2\<close> \<open>p_io p2 = xys2@[xy2]\<close> by (metis (no_types, lifting) Nil_is_map_conv snoc_eq_iff_butlast)+
    then have "path S (initial S) ?hp2" by blast
    then have "path M (initial M) ?hp2"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
    then have "target ?hp2 (initial M) = io_target M xys2 (initial M)"
      by (metis (mono_tags, lifting) \<open>p_io p2 = xys2 @ [xy2]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)

    have "target ?hp1 (initial M) = target ?hp2 (initial M)"
      using \<open>io_target M xys1 (initial M) = io_target M xys2 (initial M)\<close> \<open>target (butlast p1) (initial M) = io_target M xys1 (initial M)\<close> \<open>target (butlast p2) (initial M) = io_target M xys2 (initial M)\<close> by presburger
    moreover have "t_source ?t1 = target ?hp1 (initial M)"
      by (metis (no_types) \<open>path S (initial S) (butlast p1 @ [last p1])\<close> assms(2) is_preamble.simps is_submachine.elims(2) path_append_elim path_cons_elim)
    moreover have "t_source ?t2 = target ?hp2 (initial M)"
      by (metis (no_types) \<open>path S (initial S) (butlast p2 @ [last p2])\<close> assms(2) is_preamble.simps is_submachine.elims(2) path_append_elim path_cons_elim)
    ultimately have "t_source ?t1 = t_source ?t2" by auto
    moreover have "?t1 \<in> h S"
      by (metis (no_types, lifting) \<open>path S (initial S) (butlast p1 @ [last p1])\<close> assms(2) contra_subsetD is_preamble.simps is_submachine.elims(2) last_in_set path_h snoc_eq_iff_butlast)
    moreover have "?t2 \<in> h S"
      by (metis (no_types, lifting) \<open>path S (initial S) (butlast p2 @ [last p2])\<close> assms(2) contra_subsetD is_preamble.simps is_submachine.elims(2) last_in_set path_h snoc_eq_iff_butlast)
    moreover have "t_source ?t1 \<in> nodes S"
      by (metis (no_types, hide_lams) \<open>path S (initial S) (butlast p1)\<close> \<open>t_source (last p1) = target (butlast p1) (initial M)\<close> assms(2) is_preamble.simps is_submachine.elims(2) nodes_path)    
    ultimately have "t_input ?t1 = t_input ?t2"
      using assms(2) unfolding is_preamble.simps single_input.simps by blast
      
    then have "fst xy1 = fst xy2"
      using \<open>p_io (butlast p1 @ [last p1]) = xys1 @ [xy1]\<close> \<open>p_io (butlast p2 @ [last p2]) = xys2 @ [xy2]\<close> by auto
    then show "False" using \<open>fst xy1 \<noteq> fst xy2\<close> by simp
  next
    case f4 (* misses transition in M (for observable M) *)
    then obtain xys xy y where "xys@[xy] \<in> L S" and "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))" and  "\<not> xys@[(fst xy,y)] \<in> L S"
      by blast

    then obtain p where "path S (initial S) p" and "p_io p = xys@[xy]" 
      by auto
    let ?hp = "butlast p"
    let ?t = "last p"
    have "path S (initial S) ?hp" 
      using \<open>path S (initial S) p\<close>
      by (metis append_butlast_last_id butlast.simps(1) path_prefix) 
    then have "path M (initial M) ?hp"
      by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)

    have "p_io ?hp = xys"
      using \<open>p_io p = xys@[xy]\<close>
      by (simp add: map_butlast)

    have "?t \<in> h S" 
      by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys @ [xy]\<close> \<open>path S (initial S) p\<close> contra_subsetD last_in_set path_h snoc_eq_iff_butlast) 
    have "fst xy \<in> set (inputs S)" and "t_source ?t = target ?hp (initial S) \<and> t_input ?t = fst xy"
      by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys @ [xy]\<close> \<open>path S (initial S) p\<close> fst_conv last_map path_cons_elim path_suffix snoc_eq_iff_butlast)+
      
    have "target ?hp (initial M) \<in> nodes S"
      by (metis \<open>path S (initial S) (butlast p)\<close> assms(2) is_preamble.simps is_submachine.elims(2) nodes_path_initial) 
      
    have "target ?hp (initial M) = io_target M xys (initial M)"
      using observable_path_io_target[OF assms(1) \<open>path M (initial M) ?hp\<close>] \<open>p_io ?hp = xys\<close> by auto

    obtain tf where "tf \<in> h M" and "t_source tf = io_target M xys (initial M)" and "t_input tf = fst xy" and "t_output tf = y"
      using \<open>[(fst xy, y)] \<in> LS M (io_target M xys (initial M))\<close> by auto
    
    have "\<not> tf \<in> h S"
    proof 
      assume "tf \<in> h S"
      moreover have "t_source tf = target ?hp (initial S)"
        using \<open>t_source tf = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) = io_target M xys (initial M)\<close> assms(2) by auto
      ultimately have "path S (initial S) (?hp@[tf])"
        by (simp add: \<open>path S (initial S) (butlast p)\<close> path_append_last)
      then have "xys@[(fst xy,y)] \<in> L S"
      proof -
        have "xys @ [(fst xy, y)] = p_io (butlast p @ [tf])"
          by (simp add: \<open>p_io (butlast p) = xys\<close> \<open>t_input tf = fst xy\<close> \<open>t_output tf = y\<close>)
        then have "\<exists>ps. xys @ [(fst xy, y)] = p_io ps \<and> path S (initial S) ps"
          by (meson \<open>path S (initial S) (butlast p @ [tf])\<close>)
        then show ?thesis
          by simp
      qed
        
      then show "False" using  \<open>\<not> xys@[(fst xy,y)] \<in> L S\<close> by auto
    qed

    show "False" using assms(2) unfolding is_preamble.simps
      by (metis (no_types, lifting) \<open>fst xy \<in> set (inputs S)\<close> \<open>last p \<in> h S\<close> \<open>t_input tf = fst xy\<close> \<open>t_source (last p) = target (butlast p) (initial S) \<and> t_input (last p) = fst xy\<close> \<open>t_source tf = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) = io_target M xys (initial M)\<close> \<open>target (butlast p) (initial M) \<in> nodes S\<close> \<open>tf \<in> h M\<close> \<open>tf \<notin> h S\<close> is_submachine.elims(2)) 
  next
    case f5 (* violates property that q is the only deadlock state *)
    then consider (f5a) "\<exists> xys \<in> L S . ((io_target M xys (initial M) = q \<and> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)))" |
                  (f5b) "\<exists> xys \<in> L S . (\<not> io_target M xys (initial M) = q \<and> \<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys))" by blast
    then show "False"
    proof (cases)
      case f5a
      then obtain xys xys' where "xys \<in> L S" and "io_target M xys (initial M) = q"
                             and "xys' \<in> L S" and "length xys < length xys'" and "take (length xys) xys' = xys"
        by blast
      then obtain p where "path S (initial S) p" and "p_io p = xys'" by auto
      let ?tp = "take (length xys) p"
      let ?dp = "drop (length xys) p"
      let ?t = "hd ?dp"
      
      have "path S (initial S) ?tp"
        by (metis \<open>path S (initial S) p\<close> append_take_drop_id path_append_elim)
      then have "path M (initial M) ?tp"
        by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
      
      have "p_io ?tp = xys"
        by (metis \<open>p_io p = xys'\<close> \<open>take (length xys) xys' = xys\<close> take_map) 
      then have "io_target M xys (initial M) = target ?tp (initial M)" 
        using observable_path_io_target[OF assms(1) \<open>path M (initial M) ?tp\<close> ] by auto
      then have "target ?tp (initial M) = q" 
        using \<open>io_target M xys (initial M) = q\<close> by auto
      moreover have "initial M = initial S"
        using assms(2) by auto 
      ultimately have "target ?tp (initial S) = q" by auto
      
      have "path S (target ?tp (initial S)) ?dp"
        by (metis \<open>path S (initial S) p\<close> append_take_drop_id path_suffix)
      have "length ?dp > 0"
        using \<open>length xys < length xys'\<close> \<open>p_io p = xys'\<close> by auto
      have "?t \<in> h S"
        by (metis (no_types, lifting) \<open>0 < length (drop (length xys) p)\<close> \<open>path S (target (take (length xys) p) (initial S)) (drop (length xys) p)\<close> contra_subsetD hd_in_set length_greater_0_conv path_h) 
      moreover have "t_source ?t = target ?tp (initial S)"
        by (metis \<open>0 < length (drop (length xys) p)\<close> \<open>path S (target (take (length xys) p) (initial S)) (drop (length xys) p)\<close> hd_Cons_tl length_greater_0_conv path_cons_elim)
      ultimately have "\<not> deadlock_state S q"   
        using \<open>target ?tp (initial S) = q\<close>
        by (metis deadlock_state.elims(2)) 
      then show "False" using assms(2) unfolding is_preamble.simps by blast
    next
      case f5b
      then obtain xys where "xys \<in> L S" and "\<not> io_target M xys (initial M) = q" and "\<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)"
        by blast
      then obtain p where "path S (initial S) p" and "p_io p = xys"
        by auto
      then have "path M (initial M) p"
        by (metis assms(2) is_preamble.simps is_submachine.elims(2) submachine_path)
      then have "io_target M xys (initial M) = target p (initial M)"
        using observable_path_io_target[OF assms(1)] \<open>p_io p = xys\<close> by auto
      moreover have "io_target S xys (initial S) = io_target M xys (initial M)"
        using observable_submachine_io_target[OF assms(1) _ \<open>xys \<in> L S\<close>]
        by (metis assms(2) is_preamble.simps)
      ultimately have "io_target S xys (initial S) = target p (initial S)"
        using assms(2) by auto
        
      
      
      have "deadlock_state S (target p (initial S))"
        unfolding deadlock_state.simps 
      proof 
        show "target p (initial S) \<in> nodes S"
          using \<open>path S (initial S) p\<close> nodes_path_initial by blast 
        show "\<not> (\<exists>t\<in>set (wf_transitions S). t_source t = target p (initial S)) "
        proof 
          assume "\<exists>t\<in>h S. t_source t = target p (initial S)"  
          then obtain t where "t\<in>h S" and "t_source t = target p (initial S)"
            by blast
          then have "path S (initial S) (p@[t])" 
            using \<open>path S (initial S) p\<close> by (simp add: path_append_last) 
          then have "xys@[(t_input t,t_output t)] \<in> L S" 
            using \<open>p_io p = xys\<close>
          proof -
            have "xys @ [(t_input t, t_output t)] = p_io (p @ [t])"
              by (simp add: \<open>p_io p = xys\<close>)
            then have "\<exists>ps. xys @ [(t_input t, t_output t)] = p_io ps \<and> path S (initial S) ps"
              by (meson \<open>path S (initial S) (p @ [t])\<close>)
            then show ?thesis
              by simp
          qed 
          moreover have "length xys < length (xys @ [(t_input t, t_output t)]) \<and> take (length xys) (xys @ [(t_input t, t_output t)]) = xys"
            by simp
            
          ultimately show "False" 
            using \<open>\<not> (\<exists> xys' \<in> L S . length xys < length xys' \<and> take (length xys) xys' = xys)\<close> by blast
        qed
      qed
        
      show "False" using assms(2) unfolding is_preamble.simps
        by (metis \<open>deadlock_state S (target p (initial S))\<close> \<open>io_target M xys (initial M) \<noteq> q\<close> \<open>io_target S xys (initial S) = io_target M xys (initial M)\<close> \<open>io_target S xys (initial S) = target p (initial S)\<close> \<open>path S (initial S) p\<close> nodes_path_initial)
    qed
  next
    case f6 (* violates property that q must be a reachable state *)
    have "\<not> q \<in> nodes S"
    proof 
      assume "q \<in> nodes S"
      then obtain p where "path S (initial S) p" and "target p (initial S) = q"
        by (metis path_to_node)
      then have "p_io p \<in> L S" 
        by auto
      moreover have "io_target M (p_io p) (initial M) = q"
        by (metis (no_types) \<open>path S (initial S) p\<close> \<open>target p (initial S) = q\<close> assms(1) assms(2) is_preamble.simps is_submachine.elims(2) observable_path_io_target submachine_path)
      ultimately show "False" using f6 by blast
    qed
        
    then show "False" using assms(2) unfolding is_preamble.simps by blast
  next
    case f7 (* violates path-prefix properties *)
    then obtain xys1 xys2 where "xys1@xys2 \<in> L S" and "\<not> xys1 \<in> L S" by blast
    then show "False" by (meson language_prefix) 
  qed
qed



end