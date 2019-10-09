theory State_Preamble
imports ProductMachine IO_Sequence_Set
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


subsection \<open>Alternative Definition of Preamble Sets\<close>

(* TODO: use as initial definition *)
lemma is_preamble_set_alt_def :
  "is_preamble_set M q P = (
    P \<subseteq> L M
    \<and> acyclic_sequences M (initial M) P
    \<and> single_input_sequences M P
    \<and> output_complete_for_FSM_sequences_from_state M (initial M) P
    \<and> deadlock_states_sequences M {q} P
    \<and> reachable_states_sequences M {q} P
    \<and> prefix_closed_sequences P)"
  using output_complete_for_FSM_sequences_from_state_alt_def[of M "initial M" P]
  unfolding is_preamble_set.simps 
            acyclic_sequences.simps 
            single_input_sequences.simps
            deadlock_states_sequences.simps
            reachable_states_sequences.simps
            prefix_closed_sequences.simps 
  by blast

lemma is_preamble_set_code[code] :
  "is_preamble_set M q (set P) = (
    ((set P) \<subseteq> (set (map p_io (paths_up_to_length M (initial M) (list_max (map length P))))))
    \<and> acyclic_sequences M (initial M) (set P)
    \<and> single_input_sequences M (set P)
    \<and> output_complete_for_FSM_sequences_from_state M (initial M) (set P)
    \<and> deadlock_states_sequences M {q} (set P)
    \<and> reachable_states_sequences M {q} (set P)
    \<and> prefix_closed_sequences (set P))"
  by (metis (mono_tags, lifting) is_preamble_set_alt_def language_subset_code)


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


lemma preamble_set_shared_suffix :
  assumes "is_preamble_set M q P"
  and     "xys1@[xy] \<in> P"
  and     "xys2 \<in> P"
  and     "io_target M xys1 (initial M) = io_target M xys2 (initial M)"
  and     "observable M"
shows "xys2@[xy] \<in> P"
proof -
  have "xys1 \<in> P" using assms(1,2) unfolding is_preamble_set.simps by blast 
  moreover have "\<exists> xys' \<in> P. length xys1 < length xys' \<and> take (length xys1) xys' = xys1" 
    using assms(2) append_eq_conv_conj by fastforce 
  ultimately have "io_target M xys1 (initial M) \<noteq> q"
    using assms(1) unfolding is_preamble_set.simps by blast
  then have "io_target M xys2 (initial M) \<noteq> q"
    using assms(4) by auto
  then obtain xys2' where "xys2' \<in> P" and "length xys2 < length xys2'" and "take (length xys2) xys2' = xys2"
    using assms(1,3) unfolding is_preamble_set.simps by blast
  let ?xy = "hd (drop (length xys2) xys2')"
  have "xys2@[?xy]@(tl (drop (length xys2) xys2')) \<in> P"
    by (metis \<open>length xys2 < length xys2'\<close> \<open>take (length xys2) xys2' = xys2\<close> \<open>xys2' \<in> P\<close> append_Cons append_self_conv2 append_take_drop_id drop_eq_Nil hd_Cons_tl leD)
  then have "xys2@[?xy] \<in> P"
    using assms(1) unfolding is_preamble_set.simps by (metis (mono_tags, lifting) append_assoc) 
  then have "fst ?xy = fst xy"
    using assms(1,2,4) unfolding is_preamble_set.simps by (metis (no_types, lifting)) 


  have "xys1@[xy] \<in> L M"
    using assms(1,2) by auto
  then obtain p where "path M (initial M) p" and "p_io p = xys1@[xy]" 
    by auto
  let ?hp = "butlast p"
  let ?t = "last p"
  have "path M (initial M) ?hp"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> path_prefix snoc_eq_iff_butlast) 
  moreover have  "p_io ?hp = xys1"
    by (simp add: \<open>p_io p = xys1 @ [xy]\<close> map_butlast)
  ultimately have "target ?hp (initial M) = io_target M xys1 (initial M)"
    using assms(5) by (metis (mono_tags, lifting) observable_path_io_target) 
  then have "t_source ?t = io_target M xys1 (initial M)"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> path_cons_elim path_suffix snoc_eq_iff_butlast) 
  then have "path M (io_target M xys1 (initial M)) [?t]"
    by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = xys1 @ [xy]\<close> \<open>path M (initial M) p\<close> \<open>target (butlast p) (initial M) = io_target M xys1 (initial M)\<close> path_suffix snoc_eq_iff_butlast)
  have "p_io [?t] = [(fst xy, snd xy)]"
    by (metis (mono_tags, lifting) \<open>p_io p = xys1 @ [xy]\<close> last_map list.simps(8) list.simps(9) prod.collapse snoc_eq_iff_butlast)
  
  have "[(fst xy, snd xy)] \<in> LS M (io_target M xys1 (initial M))"
  proof -
    have "\<exists>ps. [(fst xy, snd xy)] = p_io ps \<and> path M (io_target M xys1 (initial M)) ps"
      by (metis (no_types) \<open>p_io [last p] = [(fst xy, snd xy)]\<close> \<open>path M (io_target M xys1 (initial M)) [last p]\<close>)
    then show ?thesis
      by simp
  qed
  then have "[(fst xy, snd xy)] \<in> LS M (io_target M xys2 (initial M))"
    using assms(1) unfolding is_preamble_set.simps by (metis assms(4))

  then have "[(fst ?xy, snd xy)] \<in> LS M (io_target M xys2 (initial M))"
    using \<open>fst ?xy = fst xy\<close> by auto

  then have "xys2@[(fst xy, snd xy)] \<in> P" 
    using \<open>xys2@[?xy] \<in> P\<close> assms(1) unfolding is_preamble_set.simps
    by (metis (no_types, lifting) \<open>fst (hd (drop (length xys2) xys2')) = fst xy\<close>) 
  then show "xys2@[xy] \<in> P"
    by simp
qed



lemma preamble_set_implies_preamble :
  assumes "observable M" and "is_preamble_set M q P"
  (*shows "\<exists> S . is_preamble S M q \<and> L S = P"*)
  shows "is_preamble (M\<lparr> transitions := filter (\<lambda> t . \<exists> xys xy . xys@[xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M) \<rparr>) M q"
    and "L (M\<lparr> transitions := filter (\<lambda> t . \<exists> xys xy . xys@[xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M) \<rparr>) = P"
proof -
  let ?is_preamble_transition = "\<lambda> t . \<exists> xys xy . xys@[xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy"
  let ?S = "M\<lparr> transitions := filter ?is_preamble_transition (transitions M) \<rparr>"

  have "is_submachine ?S M" by (metis transition_filter_submachine)
  then have "L ?S \<subseteq> L M" 
    using submachine_language[of ?S M] by blast

  have "\<And> io . io \<in> L ?S \<longleftrightarrow> io \<in> P"
  proof -
    fix io
    show "io \<in> L ?S \<longleftrightarrow> io \<in> P"
    proof (induction io rule: rev_induct)
      case Nil
      have "[] \<in> P" using preamble_set_contains_empty_sequence[OF assms(2)] by auto
      moreover have "[] \<in> L ?S" by (metis language_contains_empty_sequence)
      ultimately show ?case by blast
    next
      case (snoc xy io)
      have "io@[xy] \<in> L ?S \<Longrightarrow> io@[xy] \<in> P"
      proof -
        assume "io@[xy] \<in> L ?S"
        then have "io \<in> L ?S" using language_prefix[of io] by fastforce
        then have "io \<in> P" using snoc.IH by fastforce

        from \<open>io@[xy] \<in> L ?S\<close> obtain p where "path ?S (initial ?S) p" and "p_io p = io@[xy]" by auto
        let ?hp = "butlast p"
        let ?t = "last p"
        have "?t \<in> h ?S"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path (M\<lparr>transitions := filter ?is_preamble_transition (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter ?is_preamble_transition (transitions M)\<rparr>)) p\<close> append_is_Nil_conv contra_subsetD last_in_set not_Cons_self2 path_h) 
        then have "?is_preamble_transition ?t" 
          by auto
        then obtain xys xy' where "xys @ [xy'] \<in> P" 
                              and "t_source ?t = io_target M xys (initial M)" 
                              and "t_input ?t = fst xy'" 
                              and "t_output (last p) = snd xy'"
          by blast
        then have "xy' = xy"
          by (metis (mono_tags, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> append_is_Nil_conv last_map last_snoc not_Cons_self prod.collapse) 

        have "t_source ?t = target ?hp (initial ?S)"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p\<close> path_append_elim path_cons_elim snoc_eq_iff_butlast) 
        
        
        have "path ?S (initial ?S) ?hp" 
          using \<open>path ?S (initial ?S) p\<close>
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> append_butlast_last_id append_is_Nil_conv not_Cons_self2 path_prefix) 
        then have "path M (initial M) ?hp"
          using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto
        then have "io_target M io (initial M) = target ?hp (initial M)"
          by (metis (mono_tags, lifting) \<open>p_io p = io @ [xy]\<close> assms(1) butlast_snoc map_butlast observable_path_io_target)
          
        then have "io_target M xys (initial M) = io_target M io (initial M)"
          using \<open>t_source (last p) = io_target M xys (initial M)\<close> \<open>t_source (last p) = target (butlast p) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> by auto 
          
        then show "io@[xy] \<in> P"
          using preamble_set_shared_suffix[OF assms(2) \<open>xys @ [xy'] \<in> P\<close> \<open>io \<in> P\<close> _ assms(1)] \<open>xy' = xy\<close> by auto
      qed

      moreover have "io@[xy] \<in> P \<Longrightarrow> io@[xy] \<in> L ?S"
      proof -
        assume "io@[xy] \<in> P"
        then have "io \<in> P" and "io@[xy] \<in> L M" using assms(2) unfolding is_preamble_set.simps by blast+
        then have "io \<in> L ?S" using snoc.IH by auto

        from \<open>io@[xy] \<in> L M\<close> obtain p where "path M (initial M) p" and "p_io p = io@[xy]" by auto
        let ?hp = "butlast p"
        let ?t = "last p"

        have "t_source ?t = io_target M io (initial M) \<and> t_input ?t = fst xy \<and> t_output ?t = snd xy"
        proof - (* TODO: refactor auto-generated code *)
          have f1: "\<forall>ps p psa. (ps @ [p::integer \<times> integer] = psa) = (psa \<noteq> [] \<and> butlast psa = ps \<and> last psa = p)"
            using snoc_eq_iff_butlast by blast
          have f2: "p \<noteq> []"
            using \<open>p_io p = io @ [xy]\<close> by force
          then have f3: "butlast p @ [last p] = p"
            using append_butlast_last_id by blast
          then have f4: "path M (initial M) (butlast p)"
            by (metis (no_types) \<open>path M (initial M) p\<close> path_prefix)
          have f5: "p_io (butlast p) = io"
            by (simp add: \<open>p_io p = io @ [xy]\<close> map_butlast)
          have "\<forall>ps f. ps = [] \<or> last (map f ps) = (f (last ps::'a \<times> integer \<times> integer \<times> 'a)::integer \<times> integer)"
            using last_map by blast
          then have f6: "(t_input (last p), t_output (last p)) = last (p_io p)"
            using f2 by force
          have "io @ [xy] \<noteq> [] \<and> butlast (io @ [xy]) = io \<and> last (io @ [xy]) = xy"
            using f1 by blast
          then show ?thesis
            using f6 f5 f4 f3 by (metis (no_types) \<open>p_io p = io @ [xy]\<close> \<open>path M (initial M) p\<close> assms(1) fst_conv observable_path_io_target path_cons_elim path_suffix snd_conv)
        qed 

        then have "?is_preamble_transition ?t"
          using \<open>io@[xy] \<in> P\<close> by blast
        moreover have "?t \<in> h M"
          by (metis (no_types, lifting) Nil_is_map_conv \<open>p_io p = io @ [xy]\<close> \<open>path M (initial M) p\<close> contra_subsetD last_in_set path_h snoc_eq_iff_butlast)

        have "t_source ?t \<in> nodes ?S"
        proof - (*TODO: refactor auto-generated proof*)
          have f1: "\<forall>f fa ps. (\<not> observable (f::('a, 'b) FSM_scheme) \<or> \<not> is_submachine fa f \<or> ps \<notin> LS fa (initial fa)) \<or> hd (io_targets_list fa ps (initial fa)) = hd (io_targets_list f ps (initial f))"
            using observable_submachine_io_target by blast
          obtain pps :: "(integer \<times> integer) list \<Rightarrow> 'a \<Rightarrow> ('a, 'b) FSM_scheme \<Rightarrow> ('a \<times> integer \<times> integer \<times> 'a) list" where
            "\<forall>x0 x1 x2. (\<exists>v3. x0 = p_io v3 \<and> path x2 x1 v3) = (x0 = p_io (pps x0 x1 x2) \<and> path x2 x1 (pps x0 x1 x2))"
            by moura
          then have f2: "\<forall>f a ps. ((\<nexists>psa. ps = p_io psa \<and> path f a psa) \<or> ps = p_io (pps ps a f) \<and> path f a (pps ps a f)) \<and> ((\<exists>psa. ps = p_io psa \<and> path f a psa) \<or> (\<forall>psa. ps \<noteq> p_io psa \<or> \<not> path f a psa))"
            by blast
          then have f3: "io = p_io (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) \<and> path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))"
            using \<open>io \<in> LS (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> by auto
          have "\<forall>f a ps. \<not> observable (f::('a, 'b) FSM_scheme) \<or> \<not> path f a ps \<or> target ps a = hd (io_targets_list f (p_io ps) a)"
            by (metis (no_types) observable_path_io_target)
          then have f4: "target (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) = hd (io_targets_list (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (p_io (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)))"
            using f3 \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> assms(1) submachine_observable by blast
          have f5: "io = p_io (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) \<and> path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))"
            using f2 \<open>io \<in> LS (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> by auto
          then have "hd (io_targets_list (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (p_io (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))) = hd (io_targets_list M (p_io (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))) (initial M))"
            using f1 \<open>io \<in> LS (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> assms(1) by presburger
          then have "hd (io_targets_list M io (initial M)) = target (pps io (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>))"
            using f5 f4 by force
          then have "\<exists>ps. hd (io_targets_list M io (initial M)) = target ps (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) \<and> path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = hd (io_targets_list M ps (initial M)) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) ps"
            using f3 by blast
          then show ?thesis
            by (simp add: \<open>t_source (last p) = hd (io_targets_list M io (initial M)) \<and> t_input (last p) = fst xy \<and> t_output (last p) = snd xy\<close> nodes_set_alt_def)
        qed

        then have "?t \<in> h ?S"
          using transition_filter_state_transitions[OF _ \<open>?t \<in> h M\<close>, of ?is_preamble_transition, OF _ \<open>?is_preamble_transition ?t\<close>] by blast

        from \<open>io \<in> L ?S\<close> obtain pS where "path ?S (initial ?S) pS" and "p_io pS = io" by auto
        then have "path M (initial M) pS"
          using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto
        then have "target pS (initial M) = io_target M io (initial M)"
          by (metis (mono_tags, lifting) \<open>p_io pS = io\<close> assms(1) observable_path_io_target)
        then have "path ?S (initial ?S) (pS@[?t])"
          by (metis (no_types, lifting) \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> \<open>last p \<in> set (wf_transitions (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>))\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) pS\<close> \<open>t_source (last p) = hd (io_targets_list M io (initial M)) \<and> t_input (last p) = fst xy \<and> t_output (last p) = snd xy\<close> assms(1) io_targets_list.simps(1) language_contains_empty_sequence list.sel(1) observable_submachine_io_target path_append single_transition_path)
        moreover have "p_io (pS@[?t]) = io@[xy]"
          by (simp add: \<open>p_io pS = io\<close> \<open>t_source (last p) = io_target M io (initial M) \<and> t_input (last p) = fst xy \<and> t_output (last p) = snd xy\<close>)  
        ultimately show "io@[xy] \<in> L ?S"
          unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
      qed

      ultimately show ?case by blast
    qed
  qed
  then show "L ?S = P" by auto

  have "acyclic ?S"
  proof (rule ccontr)
    assume "\<not> acyclic ?S"
    then obtain p where "path ?S (initial ?S) p" and "\<not> distinct (visited_states (initial ?S) p)"
      unfolding acyclic.simps by blast
    then have "path M (initial M) p" 
      using submachine_path[OF \<open>is_submachine ?S M\<close>] by auto

    from \<open>path ?S (initial ?S) p\<close> have "p_io p \<in> L ?S" by auto
    then have "p_io p \<in> P" using \<open>L ?S = P\<close> by blast
    
    have "distinct (visited_states (initial M) p)"
      using assms(2) \<open>path M (initial M) p\<close> \<open>p_io p \<in> P\<close> unfolding is_preamble_set.simps by auto
    then show "False" 
      using \<open>\<not> distinct (visited_states (initial ?S) p)\<close> \<open>is_submachine ?S M\<close> by auto
  qed

  moreover have "single_input ?S"  
  proof (rule ccontr)
    assume "\<not> single_input ?S"
    then obtain t1 t2 where "t1 \<in> h ?S" and "t2 \<in> h ?S" and "t_source t1 = t_source t2" and "t_source t1 \<in> nodes ?S" and "t_input t1 \<noteq> t_input t2"
      unfolding single_input.simps by blast
    moreover from \<open>t_source t1 \<in> nodes ?S\<close> obtain p where "path ?S (initial ?S) p" and "target p (initial ?S) = t_source t1"
      by (metis (no_types, lifting) path_to_node)

    ultimately have "path ?S (initial ?S) (p@[t1])" and "path ?S (initial ?S) (p@[t2])"
      by (simp add: path_append_last)+
    let ?xy1 = "(t_input t1, t_output t1)"
    let ?xy2 = "(t_input t2, t_output t2)"

    have "p_io (p@[t1]) = (p_io p)@[?xy1]" by auto
    have "p_io (p@[t2]) = (p_io p)@[?xy2]" by auto

    have "(p_io p)@[?xy1] \<in> L ?S"
      using \<open>path ?S (initial ?S) (p@[t1])\<close> \<open>p_io (p@[t1]) = (p_io p)@[?xy1]\<close> unfolding LS.simps
      by (metis (mono_tags, lifting) mem_Collect_eq) 
    moreover have "(p_io p)@[?xy2] \<in> L ?S"
      using \<open>path ?S (initial ?S) (p@[t2])\<close> \<open>p_io (p@[t2]) = (p_io p)@[?xy2]\<close> unfolding LS.simps
      by (metis (mono_tags, lifting) mem_Collect_eq) 
    ultimately have "(p_io p)@[?xy1] \<in> L ?S \<and> (p_io p)@[?xy2] \<in> L ?S \<and> fst ?xy1 \<noteq> fst ?xy2" 
      using \<open>t_input t1 \<noteq> t_input t2\<close> by auto
    then have "(p_io p)@[?xy1] \<in> L M \<and> (p_io p)@[?xy2] \<in> L M \<and> fst ?xy1 \<noteq> fst ?xy2" 
      using \<open>L ?S \<subseteq> L M\<close> by blast
    then have "\<not> (\<forall> xys xy1 xy2 . (xys@[xy1] \<in> L M \<and> xys@[xy2] \<in> L M) \<longrightarrow> fst xy1 = fst xy2)"
      by blast
    then show "False" using assms(2) unfolding is_preamble_set.simps
      by (metis (no_types, lifting) \<open>\<And>io. (io \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) = (io \<in> P)\<close> \<open>p_io p @ [(t_input t1, t_output t1)] \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) \<and> p_io p @ [(t_input t2, t_output t2)] \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) \<and> fst (t_input t1, t_output t1) \<noteq> fst (t_input t2, t_output t2)\<close>) 
  qed

  moreover have "is_submachine ?S M" by (metis transition_filter_submachine)

  moreover have "q \<in> nodes ?S"
  proof -
    obtain ioq where "ioq \<in> P" and "io_target M ioq (initial M) = q"
      using assms(2) unfolding is_preamble_set.simps by blast
    then have "ioq \<in> L ?S" using \<open>L ?S = P\<close> by auto
    then obtain p where "path ?S (initial ?S) p" and "p_io p = ioq" by auto
    then have "target p (initial ?S) = io_target ?S ioq (initial ?S)"
      by (metis (mono_tags, lifting) assms(1) calculation(3) observable_path_io_target submachine_observable)
    moreover have "io_target ?S ioq (initial ?S) = io_target M ioq (initial M)"
      using \<open>ioq \<in> L (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)\<close> \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> assms(1) observable_submachine_io_target by blast
    finally have "target p (initial ?S) = q"
      using \<open>io_target M ioq (initial M) = q\<close> by auto
    
    then show ?thesis
      using \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p\<close> nodes_path_initial by blast 
  qed

  moreover have "deadlock_state ?S q"
  proof (rule ccontr)
    assume "\<not> deadlock_state ?S q"
    then obtain t where "t \<in> h ?S" and "t_source t = q" 
      unfolding deadlock_state.simps using \<open>q \<in> nodes ?S\<close> by blast
    moreover from \<open>q \<in> nodes ?S\<close> obtain p where "path ?S (initial ?S) p" and "target p (initial ?S) = q"
      by (metis (no_types, lifting) path_to_node)
    ultimately have "path ?S (initial ?S) (p@[t])"
      by (simp add: path_append_last)
    then have "p_io (p@[t]) \<in> L ?S" unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
    then have "p_io (p@[t]) \<in> P" using \<open>L ?S = P\<close> by auto
    then have "p_io p \<in> P" using assms(2) unfolding is_preamble_set.simps
      by (metis (no_types, lifting) map_append) 

    have "path M (initial M) p"
      using submachine_path[OF \<open>is_submachine ?S M\<close>] \<open>path ?S (initial ?S) p\<close> by auto
    moreover have "target p (initial M) = q"
      using \<open>target p (initial ?S) = q\<close> \<open>is_submachine ?S M\<close> by auto
    ultimately have "io_target M (p_io p) (initial M) = q"
      by (metis (mono_tags, lifting) assms(1) observable_path_io_target)
      
    have "p_io (p@[t]) \<in> P \<and> length (p_io p) < length (p_io (p@[t])) \<and> take (length (p_io p)) (p_io (p@[t])) = p_io p"
      using \<open>p_io (p@[t]) \<in> P\<close> by simp

    then show "False" 
      using assms(2) unfolding is_preamble_set.simps 
      using \<open>p_io p \<in> P\<close> \<open>io_target M (p_io p) (initial M) = q\<close>
      by blast
  qed

  moreover have "(\<forall> q' \<in> nodes ?S . (q = q' \<or> \<not> deadlock_state ?S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)))"
  proof 
    fix q' assume "q' \<in> nodes ?S"
    then obtain p' where "path ?S (initial ?S) p'" and "target p' (initial ?S) = q'"
      by (metis (no_types, lifting) path_to_node)
    
    let ?ioq' = "p_io p'"

    have "?ioq' \<in> L ?S" 
      using \<open>path ?S (initial ?S) p'\<close> by auto
    then have "?ioq' \<in> P" using \<open>L ?S = P\<close> by auto

    have "path M (initial M) p'"
      using submachine_path[OF \<open>is_submachine ?S M\<close>] \<open>path ?S (initial ?S) p'\<close> by auto
    moreover have "target p' (initial M) = q'"
      using \<open>target p' (initial ?S) = q'\<close> \<open>is_submachine ?S M\<close> by auto
    ultimately have "io_target M ?ioq' (initial M) = q'"
      by (metis (mono_tags, lifting) assms(1) observable_path_io_target)

    have "(q = q' \<or> \<not> deadlock_state ?S q')"  
    proof (cases "q = q'")
      case True
      then show ?thesis by auto
    next
      case False
      then have "io_target M ?ioq' (initial M) \<noteq> q"
        using \<open>io_target M ?ioq' (initial M) = q'\<close> by auto
      then obtain xys' where "xys'\<in>P" and "length ?ioq' < length xys'" and "take (length ?ioq') xys' = ?ioq'"
        using assms(2) unfolding is_preamble_set.simps using \<open>?ioq' \<in> P\<close> by blast
      let ?xy' = "hd (drop (length ?ioq') xys')"
      have "?ioq'@[?xy']@(tl (drop (length ?ioq') xys')) \<in> P"
        using \<open>xys'\<in>P\<close> \<open>take (length ?ioq') xys' = ?ioq'\<close> \<open>length ?ioq' < length xys'\<close>
        by (metis (no_types, lifting) append_Cons append_Nil append_take_drop_id drop_eq_Nil hd_Cons_tl leD) 
      then have "?ioq'@[?xy'] \<in> P"
        using assms(2) unfolding is_preamble_set.simps by (metis (mono_tags, lifting) append_assoc) 
      then have "?ioq'@[?xy'] \<in> L ?S" using \<open>L ?S = P\<close> by auto
      then obtain p'' where "path ?S (initial ?S) p''" and "p_io p'' = ?ioq'@[?xy']" 
        by auto
      let ?hp'' = "butlast p''"
      let ?t'' = "last p''"
      have "p_io ?hp'' = ?ioq'"
        using \<open>p_io p'' = ?ioq'@[?xy']\<close> by (simp add: map_butlast) 
      then have "?hp'' = p'"
      proof - (* TODO: refactor auto-generated code *)
        have "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial M) p''"
          using \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> by auto
        then have "\<forall>f. path f (initial M) p'' \<or> \<not> is_submachine (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) f"
          by (meson submachine_path)
        then have f1: "path M (initial M) p''"
          using transition_filter_submachine by blast
        have "p'' \<noteq> []"
          using \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close> by force
        then show ?thesis
          using f1 by (metis (no_types) \<open>observable M\<close> \<open>p_io (butlast p'') = p_io p'\<close> \<open>path M (initial M) p'\<close> append_butlast_last_id observable_path_unique path_prefix)
      qed

      obtain t where "t \<in> h ?S" and "t_source t = q'" and "t_input t = fst ?xy'" and "t_output t = snd ?xy'"
      proof -
        assume a1: "\<And>t. \<lbrakk>t \<in> h (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>); t_source t = q'; t_input t = fst (hd (drop (length (p_io p')) xys')); t_output t = snd (hd (drop (length (p_io p')) xys'))\<rbrakk> \<Longrightarrow> thesis"
        have f2: "\<forall>f fa. is_submachine (f::('a, 'b) FSM_scheme) fa = (initial f = initial fa \<and> h f \<subseteq> h fa \<and> inputs f = inputs fa \<and> outputs f = outputs fa)"
          using is_submachine.simps by blast
        have f3: "p'' \<noteq> []"
          using \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close> by force
        then have "p' @ [last p''] = p''"
          using \<open>butlast p'' = p'\<close> append_butlast_last_id by blast
        then have "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial M) (p' @ [last p''])"
          using f2 \<open>is_submachine (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) M\<close> \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> by presburger
        then have f4: "path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) q' [last p'']"
          using \<open>target p' (initial M) = q'\<close> by force
        have "\<forall>f a ps. \<not> path (f::('a, 'b) FSM_scheme) a ps \<or> set ps \<subseteq> h f"
          by (meson path_h)
        then have f5: "last p'' \<in> h (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)"
          using f3 \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) p''\<close> last_in_set by blast
        have f6: "\<forall>ps f. ps = [] \<or> last (map f ps) = (f (last ps::'a \<times> integer \<times> integer \<times> 'a)::integer \<times> integer)"
          by (meson last_map)
        then have "last (p_io p'') = (t_input (last p''), t_output (last p''))"
          using f3 by blast
        then have f7: "t_input (last p'') = fst (hd (drop (length (p_io p')) xys'))"
          by (simp add: \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close>)
        have "(t_input (last p''), t_output (last p'')) = last (p_io p'')"
          using f6 f3 by fastforce
        then have "(t_input (last p''), t_output (last p'')) = hd (drop (length (p_io p')) xys')"
          by (simp add: \<open>p_io p'' = p_io p' @ [hd (drop (length (p_io p')) xys')]\<close>)
        then have "t_output (last p'') = snd (hd (drop (length (p_io p')) xys'))"
          by (metis (no_types) snd_conv)
        then show ?thesis
          using f7 f5 f4 a1 by blast
      qed

      then have "\<not> deadlock_state ?S q'"
        unfolding deadlock_state.simps by blast

      then show ?thesis by auto
    qed

    moreover have "(\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
    proof 
      fix x assume "x \<in> set (inputs M)"
      show "(\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)"
      proof 
        assume "(\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x)"
        then obtain t where "t \<in> h ?S" and "t_source t = q'" and "t_input t = x" by blast
        then have "path ?S (initial ?S) (p'@[t])" 
          using \<open>path ?S (initial ?S) p'\<close> \<open>target p' (initial M) = q'\<close> by fastforce
        moreover have "p_io (p'@[t]) = ?ioq'@[(x,t_output t)]"
          using \<open>t_input t = x\<close> by auto
        ultimately have "?ioq'@[(x,t_output t)] \<in> L ?S"
        proof -
          have "\<exists>ps. p_io (p' @ [t]) = p_io ps \<and> path (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>p. \<exists>ps pa. ps @ [pa] \<in> P \<and> t_source p = io_target M ps (initial M) \<and> t_input p = fst pa \<and> t_output p = snd pa) (transitions M)\<rparr>)) ps"
            by (metis (lifting) \<open>path (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>) (initial (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)) (p' @ [t])\<close>)
          then show ?thesis
            using \<open>p_io (p' @ [t]) = p_io p' @ [(x, t_output t)]\<close> by auto
        qed
        then have "?ioq'@[(x,t_output t)] \<in> P"
          using \<open>L ?S = P\<close> by auto
          
        have "\<And> t' . t' \<in> h M \<Longrightarrow> t_source t' = q' \<Longrightarrow> t_input t' = x \<Longrightarrow> t' \<in> h ?S"
        proof -
          fix t' assume "t' \<in> h M" and "t_source t' = q'" and "t_input t' = x" 
          then have "path M q' [t']" by auto
          then have "[(x, t_output t')] \<in> LS M q'"
            using \<open>t_input t' = x\<close> by force 
          then have "[(fst (x,t_output t), t_output t')] \<in> LS M (io_target M ?ioq' (initial M))"
            using \<open>io_target M ?ioq' (initial M) = q'\<close> by auto
          then have "?ioq'@[(x, t_output t')] \<in> P"
            using \<open>?ioq'@[(x,t_output t)] \<in> P\<close> assms(2) unfolding is_preamble_set.simps
            by (metis (no_types, lifting) fst_conv) 

          have "?is_preamble_transition t'"
            using \<open>io_target M (p_io p') (initial M) = q'\<close> \<open>p_io p' @ [(x, t_output t')] \<in> P\<close> \<open>t_input t' = x\<close> \<open>t_source t' = q'\<close> by auto

          have "t_source t' \<in> nodes ?S"
            using \<open>q' \<in> nodes (M\<lparr>transitions := filter (\<lambda>t. \<exists>xys xy. xys @ [xy] \<in> P \<and> t_source t = hd (io_targets_list M xys (initial M)) \<and> t_input t = fst xy \<and> t_output t = snd xy) (transitions M)\<rparr>)\<close> \<open>t_source t' = q'\<close> by fastforce


          then show "t' \<in> h ?S"
            using transition_filter_state_transitions[OF _ \<open>t' \<in> h M\<close>, of ?is_preamble_transition, OF _ \<open>?is_preamble_transition t'\<close>] by blast
        qed
        then show "(\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S)" by blast
      qed
    qed

    ultimately show "(q = q' \<or> \<not> deadlock_state ?S q') \<and> (\<forall> x \<in> set (inputs M) . (\<exists> t \<in> h ?S . t_source t = q' \<and> t_input t = x) \<longrightarrow> (\<forall> t' \<in> h M . t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> h ?S))"
      by blast
  qed

  ultimately show "is_preamble ?S M q" 
    unfolding is_preamble.simps by blast
qed





lemma is_preamble_set_length :
  assumes "is_preamble_set M q P"
  shows "P \<subseteq> set (language_up_to_length M ( size M - 1 ))" 
proof 
  fix x assume "x \<in> P"
  then have "x \<in> L M" using assms by auto
  then obtain p where "p_io p = x" and "path M (initial M) p" by auto
  then have "distinct (visited_states (initial M) p)" using is_preamble_set_alt_def[of M q P] assms acyclic_sequences.simps
    using \<open>x \<in> P\<close>
    by (metis (mono_tags, lifting)) 
  then have "length p < size M" using distinct_path_length_limit_nodes[OF \<open>path M (initial M) p\<close>] by auto
  then have "p_io p \<in> { io \<in> L M . length io < size M }"
    using \<open>p_io p = x\<close> \<open>x \<in> L M\<close> by fastforce 
  moreover have "size M > 0"
    using \<open>length p < size M\<close> by auto 
  ultimately have "x \<in> { io \<in> L M . length io \<le> size M - 1 }"
    using \<open>p_io p = x\<close> by auto
  then show "x \<in> set (language_up_to_length M ( size M - 1 ))"
    using language_up_to_length_set[of M "size M - 1"]  by auto
qed


subsection \<open>Preamble Set Calculation\<close>

(* TODO: define more efficient variant based on backwards reachability analysis as in d_states *)

definition calculate_preamble_set_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set option" where
  "calculate_preamble_set_naive M q = (let n = size M - 1 in
    (case 
      (find 
        (\<lambda> S . language_up_to_length S (Suc n) = language_up_to_length S n \<and>  is_preamble_set M q (set (language_up_to_length S n))) 
        (generate_submachines M)) of
    None \<Rightarrow> None |
    Some S \<Rightarrow> (Some (set (language_up_to_length S n)))))"



  



lemma calculate_preamble_set_naive_soundness :
  assumes "calculate_preamble_set_naive M q = Some P"
shows "is_preamble_set M q P"
  using assms unfolding calculate_preamble_set_naive_def Let_def
  by (metis (no_types, lifting) find_condition option.case_eq_if option.collapse option.distinct(1) option.sel) 





lemma calculate_preamble_set_naive_exhaustiveness :
  assumes "observable M"
  and     "\<exists> P . is_preamble_set M q P"
  shows "calculate_preamble_set_naive M q \<noteq> None"
proof -

  obtain P where "is_preamble_set M q P"
    using assms(2) by blast

  obtain SP where "is_preamble SP M q" and "L SP = P"
    using preamble_set_implies_preamble[OF assms(1) \<open>is_preamble_set M q P\<close>] by blast
  then have "is_submachine SP M" unfolding is_preamble.simps by presburger

  obtain S where "S \<in> set (generate_submachines M)" and "h S = h SP"
    using generate_submachines_containment[OF \<open>is_submachine SP M\<close>] by blast
  then have "is_submachine S M"
    using generate_submachines_are_submachines by blast 
  then have "L S \<subseteq> L M"
    using submachine_language by blast  

  have "L S = L SP"
    using \<open>is_submachine S M\<close> \<open>is_submachine SP M\<close> \<open>h S = h SP\<close> language_by_same_h_initial[of S SP] by auto
  then have "L S = P"
    using \<open>L SP = P\<close> by simp
  then have "L S \<subseteq> set (language_up_to_length M ( size M - 1) )"
    using is_preamble_set_length[OF \<open>is_preamble_set M q P\<close>] by auto
  then have "L S \<subseteq> {io \<in> L M. length io \<le> size M - 1}"
    using language_up_to_length_set[of M "size M - 1"] by blast
  moreover have "L S \<inter> {io \<in> L M. length io \<le> size M - 1} = {io \<in> L S. length io \<le> size M - 1}"
    using \<open>L S \<subseteq> L M\<close> by blast
  ultimately have "L S \<subseteq> {io \<in> L S. length io \<le> size M - 1}"
    by blast
  then have "L S = {io \<in> L S. length io \<le> size M - 1}"
    by auto
  then have "P = set (language_up_to_length S ( size M - 1) )"
    using language_up_to_length_set[of S "size M - 1"] \<open>L S = P\<close> by blast
  then have "is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))"
    using \<open>is_preamble_set M q P\<close> by metis
  
  have "language_up_to_length S (Suc ( size M - 1 )) = (language_up_to_length S ( size M - 1 )) @ (map p_io (paths_of_length S (initial S) (Suc ( size M - 1 ))))"
  proof -
    have "language_up_to_length S (Suc ( size M - 1)) = map p_io (paths_up_to_length S (initial S) ( size M - 1)) @ map p_io (paths_of_length S (initial S) (Suc ( size M - 1)))"
      by (metis (no_types) language_up_to_length.simps map_append paths_up_to_length.simps(2))
    then show ?thesis
      by (metis (no_types) language_up_to_length.simps)
  qed
  moreover have "map p_io (paths_of_length S (initial S) (Suc ( size M - 1))) = []"
  proof (rule ccontr)
    assume "map p_io (paths_of_length S (initial S) (Suc ( size M - 1))) \<noteq> []"
    then have "(paths_of_length S (initial S) (Suc ( size M - 1))) \<noteq> []"
      by fastforce
    then obtain p where "p \<in> set (paths_of_length S (initial S) (Suc ( size M - 1)))" 
      using hd_in_set[of "paths_of_length S (initial S) (Suc ( size M - 1))"] by blast
    have "path S (initial S) p" and "length p = (Suc ( size M - 1))"
      using paths_of_length_is_path[OF \<open>p \<in> set (paths_of_length S (initial S) (Suc ( size M - 1)))\<close>] by auto
    then have "p_io p \<in> {io \<in> L S. length io = Suc ( size M - 1 )}" unfolding LS.simps by fastforce
    moreover have "{io \<in> L S. length io = Suc ( size M - 1 )} = {}"
    proof -
      have "\<not> length (p_io p) \<le> FSM.size M - 1"
        using calculation by auto
      then show ?thesis
        using \<open>LS S (initial S) = {io \<in> LS S (initial S). length io \<le> FSM.size M - 1}\<close> calculation by blast
    qed  
    ultimately show "False" by blast
  qed
  ultimately have "(language_up_to_length S (Suc ( size M - 1 ))) = (language_up_to_length S ( size M - 1 ))"
    by simp


  let ?f = "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 ))))"

  have "?f S"
    using \<open>(language_up_to_length S (Suc ( size M - 1 ))) = (language_up_to_length S ( size M - 1 ))\<close> \<open>is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))\<close> by metis
  then have "(filter ?f (generate_submachines M)) \<noteq> []"
    using \<open>S \<in> set (generate_submachines M)\<close> filter_empty_conv[of ?f "generate_submachines M"] by blast

  then show "calculate_preamble_set_naive M q \<noteq> None"
    unfolding calculate_preamble_set_naive_def
    by (metis (no_types, lifting) filter_False find_None_iff option.case_eq_if option.distinct(1))  
qed

lemma calculate_preamble_set_naive_correctness : 
  assumes "observable M"
  shows "(\<exists> P . is_preamble_set M q P) = (\<exists> P . calculate_preamble_set_naive M q = Some P \<and> is_preamble_set M q P)"
  using calculate_preamble_set_naive_soundness[of M q] calculate_preamble_set_naive_exhaustiveness[OF assms, of q] by blast 


value[code] "calculate_preamble_set_naive M_ex 2"
value[code] "calculate_preamble_set_naive M_ex 3"
value[code] "calculate_preamble_set_naive M_ex 4"
value[code] "calculate_preamble_set_naive M_ex 5"

value[code] "calculate_preamble_set_naive M_ex_H 1"
value[code] "calculate_preamble_set_naive M_ex_H 2"
value[code] "calculate_preamble_set_naive M_ex_H 3"
value[code] "calculate_preamble_set_naive M_ex_H 4"

value[code] "calculate_preamble_set_naive M_ex_9 3"




subsubsection \<open>Alternative Calculation\<close>

definition "M_ex_DR \<equiv> \<lparr> initial = 0::integer,
                          inputs = [0,1],
                          outputs = [0,1,2],
                          transitions = [(0,0,0,100),
                                         (100,0,0,101), 
                                         (100,0,1,101),
                                         (101,0,0,102),
                                         (101,0,1,102),
                                         (102,0,0,103),
                                         (102,0,1,103),
                                         (103,0,0,104),
                                         (103,0,1,104),
                                         (104,0,0,100),
                                         (104,0,1,100),
                                         (104,1,0,400),
                                         (0,0,2,200),
                                         (200,0,2,201),
                                         (201,0,2,202),
                                         (202,0,2,203),
                                         (203,0,2,200),
                                         (203,1,0,400),
                                         (0,1,0,300),
                                         (100,1,0,300),
                                         (101,1,0,300),
                                         (102,1,0,300),
                                         (103,1,0,300),
                                         (200,1,0,300),
                                         (201,1,0,300),
                                         (202,1,0,300),
                                         (300,0,0,300),
                                         (300,1,0,300),
                                         (400,0,0,300),
                                         (300,1,0,300)] \<rparr>"

                            
(*value "calculate_preamble_set_naive M_ex_DR 400" *)


fun d_states :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> Input) list" where
  "d_states M 0 q = []" |
  "d_states M (Suc k) q =  
    (if length (d_states M k q) < k 
      then (d_states M k q)
      else (case find 
                  (\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set (d_states M k q) . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> h M . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M k q) . fst qx' = (t_target t))))) 
                  (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M)))
            of Some qx \<Rightarrow> (d_states M k q)@[qx] | 
               None \<Rightarrow> (d_states M k q)))"

fun d_states' :: "('a \<times> Input) list \<Rightarrow> 'a Transition set \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> Input) list" where
  "d_states' QX H 0 q = []" |
  "d_states' QX H (Suc k) q = (let Q = d_states' QX H k q in 
    (if length Q < k 
      then Q
      else (case find (\<lambda> qx . (fst qx \<noteq> q) \<and> (\<forall> qx' \<in> set Q . fst qx \<noteq> fst qx') \<and> (\<exists> t \<in> H . t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall> t \<in> H . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set Q . fst qx' = (t_target t))))) QX
            of Some qx \<Rightarrow> Q@[qx] | 
               None \<Rightarrow> Q)))"

(* Slightly more efficient formulation of d_states, avoids some repeated calculations *)
fun d_states_opt :: "('a,'b) FSM_scheme \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a \<times> Input) list" where
  "d_states_opt M k q = d_states' (concat (map (\<lambda> q . map (\<lambda> x . (q,x)) (inputs M)) (nodes_from_distinct_paths M))) (h M) k q"

lemma d_states_code : "d_states M k = d_states_opt M k"  
proof (induction k)
  case 0
  then show ?case 
    unfolding d_states.simps d_states_opt.simps d_states'.simps by blast
next
  case (Suc k)
  then show ?case 
    unfolding d_states.simps d_states_opt.simps d_states'.simps Let_def
    by presburger 
qed


lemma d_states_length :
  "length (d_states M k q) \<le> k"
proof (induction k)
  case 0
  then show ?case by auto 
next
  case (Suc k)
  show ?case
  proof (cases "length (d_states M k q) < k")
    case True
    then show ?thesis unfolding d_states.simps
      by simp 
  next
    case False then show ?thesis using Suc unfolding d_states.simps
      by (simp add: option.case_eq_if)
  qed
qed

lemma d_states_prefix :
  assumes "i \<le> k"
  shows "take i (d_states M k q) = d_states M i q"
  using assms proof (induction k)
  case 0
  then show ?case unfolding d_states.simps
    by (metis le_zero_eq  d_states.simps(1) d_states_length take_all) 
next
  case (Suc k)
  then consider (a) "i \<le> k" | (b) "i = Suc k"
    using le_SucE by blast 
  then show ?case proof cases
    case a
    show ?thesis proof (cases "length (d_states M k q) < k")
      case True
      then show ?thesis using Suc.IH[OF a] unfolding d_states.simps
        by simp 
    next
      case False
      then consider (a1) "(d_states M (Suc k) q = d_states M k q)" |
                    (a2) "\<exists> qx . d_states M (Suc k) q = (d_states M k q)@[qx]"
        unfolding d_states.simps
        by (metis (mono_tags, lifting) option.case_eq_if) 
      then show ?thesis proof cases
        case a1
        then show ?thesis using Suc.IH[OF a] by simp
      next
        case a2
        then show ?thesis using Suc.IH[OF a] using False a by auto
      qed         
    qed      
  next
    case b
    then show ?thesis unfolding d_states.simps
    proof -
      have f1: "\<forall>a f n. take n (d_states (f::('a, 'b) FSM_scheme) n a) = d_states f n a"
        by (simp add: d_states_length)
      then have "d_states M i q = d_states M k q \<longrightarrow> take i (d_states M k q) = d_states M k q"
        by (metis (no_types))
      moreover
      { assume "d_states M i q \<noteq> d_states M k q"
        then have "d_states M i q \<noteq> d_states M k q \<and> take i (d_states M i q) = d_states M i q"
          using f1 by blast
        then have "\<not> length (d_states M k q) < k \<and> take i (if length (d_states M k q) < k then d_states M k q else d_states M i q) = d_states M i q"
          using b by fastforce }
      ultimately have "take i (if length (d_states M k q) < k then d_states M k q else case find (\<lambda>p. (fst p \<noteq> q) \<and> (\<forall>pa\<in>set (d_states M k q). fst p \<noteq> fst pa) \<and> (\<exists>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p\<in>set (d_states M k q). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some p \<Rightarrow> d_states M k q @ [p]) = d_states M i q \<or> \<not> length (d_states M k q) < k \<and> take i (if length (d_states M k q) < k then d_states M k q else d_states M i q) = d_states M i q"
        using f1 by presburger
      then show "take i (if length (d_states M k q) < k then d_states M k q else case find (\<lambda>p. (fst p \<noteq> q) \<and> (\<forall>pa\<in>set (d_states M k q). fst p \<noteq> fst pa) \<and> (\<exists>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa\<in>set (wf_transitions M). t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p\<in>set (d_states M k q). fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some p \<Rightarrow> d_states M k q @ [p]) = d_states M i q"
        using b by force
    qed 
  qed 
qed


lemma d_states_self_length :
  "d_states M k q = d_states M (length (d_states M k q)) q" 
  using d_states_prefix 
  by (metis (no_types) nat_le_linear d_states_length d_states_prefix take_all)

lemma d_states_index_properties : 
  assumes "i < length (d_states M k q)"
shows "fst (d_states M k q ! i) \<in> nodes M" 
      "fst (d_states M k q ! i) \<noteq> q"
      "snd (d_states M k q ! i) \<in> set (inputs M)"
      "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')" 
      "(\<forall> t \<in> h M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
proof -
  have combined_properties: "fst (d_states M k q ! i) \<in> nodes M \<and> fst (d_states M k q ! i) \<noteq> q
       \<and> snd (d_states M k q ! i) \<in> set (inputs M)
       \<and> (\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx') \<and> (\<forall> t \<in> h M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
    using assms proof (induction k)
    case 0
    then have "i = 0" by auto 
    then have "d_states M 0 q \<noteq> []"
      using 0 by auto
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "i < length (d_states M k q)")
      case True
      then have "d_states M k q ! i = d_states M (Suc k) q ! i"
        using d_states_prefix[of i]
      proof -
        have "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
          by (meson Suc_leI)
        then show ?thesis
          by (metis Suc.prems \<open>i < length (d_states M k q)\<close> d_states_prefix d_states_self_length take_last_index)
      qed
      moreover have "take i (d_states M k q) = take i (d_states M (Suc k) q)"
        by (metis Suc.prems Suc_leI less_le_trans nat_less_le not_le d_states_length d_states_prefix)
      ultimately show ?thesis using Suc.IH[OF True] by presburger
    next
      case False
      have "length (d_states M k q) = k"
        by (metis (no_types) False Suc.prems nat_less_le d_states.simps(2) d_states_length)
      then have "i = length (d_states M k q)"
        by (metis (no_types) False Suc.prems Suc_leI leI less_le_trans nat_less_le d_states_length)
      then have "(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)"
        by (metis (no_types, lifting) Suc.prems nat_less_le d_states.simps(2) d_states_code d_states_length take_all take_last_index)
      then have "(d_states M (Suc k) q) = (d_states M k q)@[last (d_states M (Suc k) q)]"
      proof -
        have "i = k"
          by (metis (no_types) Suc.prems \<open>i = length (d_states M k q)\<close> nat_less_le d_states.simps(2) d_states_length)
        then show ?thesis
          by (metis Suc.prems Suc_n_not_le_n \<open>d_states M (Suc k) q ! i = last (d_states M (Suc k) q)\<close> nat_le_linear d_states_prefix take_Suc_conv_app_nth)
      qed 
      then obtain qx where "d_states M (Suc k) q = (d_states M k q)@[qx]"
        by blast
      moreover have "\<not> length (d_states M k q) < k"
        using \<open>length (d_states M k q) = k\<close> by simp
      ultimately have "find
              (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                    (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                    (\<forall>t\<in>set (wf_transitions M).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))
              (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
        unfolding d_states.simps(2)
      proof -
        assume "(if length (d_states M k q) < k then d_states M k q else case find (\<lambda>qx. fst qx \<noteq> q \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and> (\<forall>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow> t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))) (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some qx \<Rightarrow> d_states M k q @ [qx]) = d_states M k q @ [qx]"
        then have f1: "(case find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) of None \<Rightarrow> d_states M k q | Some p \<Rightarrow> d_states M k q @ [p]) = d_states M k q @ [qx]"
          by (simp add: Ball_def_raw Bex_def_raw \<open>\<not> length (d_states M k q) < k\<close>)
        then have f2: "find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
          by (metis (no_types) append_self_conv list.simps(3) option.case_eq_if)
        then have f3: "Some (the (find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M))))) = find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M)))"
          by (meson option.collapse)
        have "the (find (\<lambda>p. fst p \<noteq> q \<and> (\<forall>pa. pa \<in> set (d_states M k q) \<longrightarrow> fst p \<noteq> fst pa) \<and> (\<exists>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p) \<and> (\<forall>pa. pa \<in> set (wf_transitions M) \<and> t_source pa = fst p \<and> t_input pa = snd p \<longrightarrow> t_target pa = q \<or> (\<exists>p. p \<in> set (d_states M k q) \<and> fst p = t_target pa))) (concat (map (\<lambda>a. map (Pair a) (inputs M)) (nodes_from_distinct_paths M)))) = qx"
          using f2 f1 option.case_eq_if by fastforce
        then show ?thesis
          using f3 by (simp add: Ball_def_raw Bex_def_raw)
      qed
      then have *: "find
              (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                    (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                    (\<forall>t\<in>set (wf_transitions M).
                        t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                        t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))
              (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some (last (d_states M (Suc k) q))"
        using \<open>d_states M (Suc k) q = (d_states M k q)@[qx]\<close>
              \<open>(d_states M (Suc k) q) = (d_states M k q)@[last (d_states M (Suc k) q)]\<close> by simp

      
      let ?qx = "last (d_states M (Suc k) q)"
      
      have "(\<lambda>qx. (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
         (\<forall>t\<in>set (wf_transitions M).
             t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
             (t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))) ?qx"
        using find_condition[OF *] \<open>(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)\<close> by force


      

      have "?qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))"
        using find_set[OF *] by assumption
      then have "fst ?qx \<in> nodes M \<and> snd ?qx \<in> set (inputs M)"
        using nodes_code[of M] concat_pair_set[of "inputs M" "nodes_from_distinct_paths M"] by blast
      moreover have "(fst ?qx \<noteq> q) \<and> (\<forall>qx'\<in>set (take i (d_states M (Suc k) q)). fst ?qx \<noteq> fst qx')"
        by (metis find_condition[OF *] \<open>i = length (d_states M k q)\<close> \<open>d_states M (Suc k) q = d_states M k q @ [last (d_states M (Suc k) q)]\<close> append_eq_conv_conj)
      moreover have "(\<forall>t\<in>set (wf_transitions M).
        t_source t = fst (d_states M (Suc k) q ! i) \<and> t_input t = snd (d_states M (Suc k) q ! i) \<longrightarrow>
        (t_target t = q \<or> (\<exists>qx'\<in>set (take i (d_states M (Suc k) q)). fst qx' = t_target t)))"
        using find_condition[OF *] \<open>(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)\<close>
        by (metis \<open>i = length (d_states M k q)\<close> le_imp_less_Suc less_or_eq_imp_le d_states_length d_states_prefix d_states_self_length) 
      ultimately show ?thesis by (presburger add:\<open>(d_states M (Suc k) q) ! i = last (d_states M (Suc k) q)\<close>)
    qed
  qed

  show "fst (d_states M k q ! i) \<in> nodes M" 
       "fst (d_states M k q ! i) \<noteq> q" 
       "snd (d_states M k q ! i) \<in> set (inputs M)"
       "(\<forall> qx' \<in> set (take i (d_states M k q)) . fst (d_states M k q ! i) \<noteq> fst qx')" 
       "(\<forall> t \<in> h M . (t_source t = fst (d_states M k q ! i) \<and> t_input t = snd (d_states M k q ! i)) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (take i (d_states M k q)) . fst qx' = (t_target t))))"
    using combined_properties by presburger+
qed



lemma d_states_distinct_states :
  "distinct (map fst (d_states M k q))" 
proof -
  have "(\<And>i. i < length (map fst (d_states M k q)) \<Longrightarrow>
          map fst (d_states M k q) ! i \<notin> set (take i (map fst (d_states M k q))))"
    using d_states_index_properties(4)[of _ M k]
    by (metis (no_types, lifting) length_map list_map_source_elem nth_map take_map) 
  then show ?thesis
    using list_distinct_prefix[of "map fst (d_states M k q)"] by blast
qed



lemma d_states_nodes : 
  "set (map fst (d_states M k q)) \<subseteq> nodes M"
  using d_states_index_properties(1)[of _ M k]  list_property_from_index_property[of "map fst (d_states M k q)" "\<lambda>q . q \<in> nodes M"]
  by fastforce

lemma d_states_size :
  "length (d_states M k q) \<le> size M"
proof -
  show ?thesis 
    using d_states_nodes[of M k]
          d_states_distinct_states[of M k]
          nodes_finite[of M]
    by (metis card_mono distinct_card length_map size_def) 
qed
  
lemma d_states_max_iterations :
  assumes "k \<ge> size M"
  shows "d_states M k q = d_states M (size M) q"
  using d_states_size[of M k] d_states_prefix[OF assms, of M]
  by simp 



lemma d_states_by_index :
  assumes "i < length (d_states M k q)"
  shows "(d_states M k q) ! i = last (d_states M (Suc i) q)"
  by (metis Suc_leI assms d_states_prefix d_states_self_length take_last_index) 


lemma d_states_subset :
  "set (d_states M k q) \<subseteq> set (d_states M (Suc k) q)"
  unfolding d_states.simps
  by (simp add: option.case_eq_if subsetI) 

lemma d_states_last :
  assumes "d_states M (Suc k) q \<noteq> d_states M k q"
  shows "\<exists> qx . d_states M (Suc k) q = (d_states M k q)@[qx]
                \<and> fst qx \<noteq> q
                \<and> (\<forall> qx' \<in> set (d_states M k q) . fst qx \<noteq> fst qx') 
                \<and> (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) 
                \<and> (\<forall> t \<in> h M . (t_source t = fst qx \<and> t_input t = snd qx) \<longrightarrow> (t_target t = q \<or> (\<exists> qx' \<in> set (d_states M k q) . fst qx' = (t_target t))))
                \<and> fst qx \<in> nodes M
                \<and> snd qx \<in> set (inputs M)"
proof -
  have *: "\<not> (length (d_states M k q) < k)"
    using assms unfolding d_states.simps
    by auto
  have "find
          (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) \<noteq> None"
    using assms unfolding d_states.simps
    by (metis (no_types, lifting) option.simps(4))

  then obtain qx where qx_find: "find
          (\<lambda>qx. (fst qx \<noteq> q) \<and> (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                (\<forall>t\<in>set (wf_transitions M).
                    t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                    (t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))))
          (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M))) = Some qx"
    by blast

  then have "d_states M (Suc k) q = (d_states M k q)@[qx]"
    using * by auto
  moreover note find_condition[OF qx_find] 
  moreover have "fst qx \<in> nodes M
                \<and> snd qx \<in> set (inputs M)"
    using find_set[OF qx_find]
  proof -
    have "fst qx \<in> set (nodes_from_distinct_paths M) \<and> snd qx \<in> set (inputs M)"
      using \<open>qx \<in> set (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))\<close> concat_pair_set by blast
    then show ?thesis
      by (metis (no_types) nodes_code)
  qed 
  ultimately show ?thesis by blast
qed


lemma d_states_transition_target :
  assumes "(t_source t, t_input t) \<in> set (d_states M k q)"
  and     "t \<in> h M"
shows "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))"
  and "t_target t \<noteq> t_source t"
proof -
  have "(t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))) \<and> t_target t \<noteq> t_source t"
    using assms(1) proof (induction k)
    case 0 
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "(t_source t, t_input t) \<in> set (d_states M k q)")
      case True
      then have "(t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))) \<and> t_target t \<noteq> t_source t"
        using Suc.IH by auto
      moreover have "set (d_states M (k - 1) q) \<subseteq> set (d_states M (Suc k - 1) q)"
        using d_states_subset
        by (metis Suc_pred' diff_Suc_1 diff_is_0_eq' nat_less_le order_refl zero_le) 
      ultimately show ?thesis by auto
    next
      case False
      then have "set (d_states M k q) \<noteq> set (d_states M (Suc k) q)"
        using Suc.prems by blast
      then have "d_states M (Suc k) q \<noteq> d_states M k q"
        by auto
      
      obtain qx where    "d_states M (Suc k) q = d_states M k q @ [qx]" 
                  and    "fst qx \<noteq> q"
                  and    "(\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx')"
                  and    "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)"
                  and *: "(\<forall>t\<in>set (wf_transitions M).
                         t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                         t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
                  and    "fst qx \<in> nodes M \<and> snd qx \<in> set (inputs M)"
        using d_states_last[OF \<open>d_states M (Suc k) q \<noteq> d_states M k q\<close>] by blast
      
      have "qx = (t_source t, t_input t)"
        using Suc.prems False \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close>
        by auto
      then have "t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)"
        using assms(2) by (simp add: "*")
      then have "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k-1) q))"
        by (metis diff_Suc_1 in_set_zipE prod.collapse zip_map_fst_snd) 
      moreover have \<open>t_target t \<noteq> t_source t\<close>
        using \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> \<open>fst qx \<noteq> q\<close> \<open>qx = (t_source t, t_input t)\<close> \<open>t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)\<close> by auto        
      ultimately show ?thesis by blast
    qed
  qed
  then show "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (k-1) q))"
        and "t_target t \<noteq> t_source t" by simp+
qed



lemma d_states_last_ex :
  assumes "qx1 \<in> set (d_states M k q)"
  shows "\<exists> k' . k' \<le> k \<and> k' > 0 \<and> qx1 \<in> set (d_states M k' q) \<and> qx1 = last (d_states M k' q) \<and> (\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
proof -

  obtain k' where k'_find: "find_index (\<lambda> qqt . qqt = qx1) (d_states M k q) = Some k'"
    using find_index_exhaustive[of "d_states M k q" "(\<lambda> qqt . qqt = qx1)"] assms
    by blast 

  have "Suc k' \<le> k"
    using find_index_index(1)[OF k'_find] d_states_length[of M k q] by presburger
  moreover have "Suc k' > 0" 
    by auto
  moreover have "qx1 \<in> set (d_states M (Suc k') q)"
    using find_index_index(2)[OF k'_find]
    by (metis Suc_neq_Zero \<open>Suc k' \<le> k\<close> assms find_index_index(1) k'_find last_in_set d_states_by_index d_states_prefix take_eq_Nil) 
  moreover have "qx1 = last (d_states M (Suc k') q)"
    by (metis find_index_index(1,2)[OF k'_find] d_states_by_index)
  moreover have "(\<forall> k'' < Suc k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
  proof -
    have "\<And> k'' . k'' < Suc k' \<Longrightarrow> k'' > 0 \<Longrightarrow> qx1 \<noteq> last (d_states M k'' q)" 
    proof -
      fix k'' assume "k'' < Suc k'" and "k'' > 0"
      then have "k'' \<le> k'" by auto
      
      show "qx1 \<noteq> last (d_states M k'' q)" using find_index_index(3)[OF k'_find] d_states_prefix[OF \<open>k'' \<le> k'\<close>]
      proof -
        have f1: "\<forall>n na. \<not> (n::nat) < na \<or> n \<le> na"
          using less_imp_le_nat by satx
        have f2: "k'' \<noteq> 0"
          using \<open>0 < k''\<close> by blast
        obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
          "\<forall>x0 x1. (\<exists>v2. x1 = Suc v2 \<and> v2 < x0) = (x1 = Suc (nn x0 x1) \<and> nn x0 x1 < x0)"
          by moura
        then have "k'' = Suc (nn k' k'') \<and> nn k' k'' < k'"
          using f2 \<open>k'' < Suc k'\<close> less_Suc_eq_0_disj by force
        then show ?thesis
          using f1 by (metis (no_types) \<open>\<And>j. j < k' \<Longrightarrow> d_states M k q ! j \<noteq> qx1\<close> assms d_states_by_index in_set_conv_nth less_le_trans nat_neq_iff)
      qed
    qed
    then show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed



lemma d_states_last_least : 
  assumes "qx1 \<in> set (d_states M k' q)"
  and "qx1 = last (d_states M k' q)"
  and "(\<forall> k'' < k' . k'' > 0 \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
shows "(k' = (LEAST k' . qx1 \<in> set (d_states M k' q)))" 
proof (rule ccontr)
  assume "k' \<noteq> (LEAST k'. qx1 \<in> set (d_states M k' q))"
  then obtain k'' where "k'' < k'" and "qx1 \<in> set (d_states M k'' q)"
    by (metis (no_types, lifting) LeastI assms(1) nat_neq_iff not_less_Least)

  obtain k''' where "k''' \<le> k''" and "k'''>0" and "qx1 = last (d_states M k''' q)" and "(\<forall>k''<k'''. 0 < k'' \<longrightarrow> qx1 \<noteq> last (d_states M k'' q))"
    using d_states_last_ex[OF \<open>qx1 \<in> set (d_states M k'' q)\<close>] by blast

  have "k''' < k'"
    using \<open>k''' \<le> k''\<close> \<open>k'' < k'\<close> by simp

  show "False"
    using assms(3) \<open>k'''>0\<close> \<open>k''' < k'\<close> \<open>qx1 = last (d_states M k''' q)\<close>  by blast
qed




lemma d_states_distinct_least :
  assumes "t \<in> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  shows "(t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
          \<or> (t_target t = q)"
    and "t_source t \<in> set (map fst (d_states M k q))"
proof -
  have "((t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
          \<or> (t_target t = q))
         \<and> t_source t \<in> set (map fst (d_states M k q))"
  using assms proof (induction k)
    case 0
    then show ?case by auto
  next
    case (Suc k)
    show ?case proof (cases "d_states M (Suc k) q = d_states M k q")
      case True
      then show ?thesis using Suc by auto
    next
      case False
  
      obtain qx where "d_states M (Suc k) q = d_states M k q @ [qx]"
                      "fst qx \<noteq> q"
                      "(\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx')"
                      "(\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx)"
                      "(\<forall>t\<in>set (wf_transitions M).
                          t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                          t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t))"
                      "fst qx \<in> nodes M \<and> snd qx \<in> set (inputs M)"
        using d_states_last[OF False] by blast
  
      
  
      then show ?thesis proof (cases "t_source t = fst qx")
        case True
  
        
        
        have "fst qx \<notin> set (map fst (d_states M k q))"
          using \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> by auto
        then have "\<And> k' . k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (d_states M k' q))"
          using d_states_prefix[of _ k M]
          by (metis \<open>\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx'\<close> in_set_takeD less_Suc_eq_le list_map_source_elem) 
        moreover have "fst qx \<in> set (map fst (d_states M (Suc k) q))"
          using \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by auto
          
        ultimately have "(LEAST k' . fst qx \<in> set (map fst (d_states M k' q))) = Suc k"
        proof -
          have "\<not> (LEAST n. fst qx \<in> set (map fst (d_states M n q))) < Suc k"
            by (meson LeastI_ex \<open>\<And>k'. k' < Suc k \<Longrightarrow> fst qx \<notin> set (map fst (d_states M k' q))\<close> \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close>)
          then show ?thesis
            by (meson \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close> not_less_Least not_less_iff_gr_or_eq)
        qed 
  
  
        have "(t_source t, t_input t) \<in> set (d_states M (Suc k) q) \<and> t \<in> set (wf_transitions M)"
          using Suc.prems by auto 
        then have "t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k - 1) q))"
          using d_states_transition_target(1)[of t M "Suc k" q] by auto
        then have "t_target t = q \<or> ((LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) \<le> k)"
          by (metis Least_le diff_Suc_1)
          
        then have "t_target t = q \<or> ((LEAST k'. t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k'. t_source t \<in> set (map fst (d_states M k' q))))" 
          using \<open>(LEAST k' . fst qx \<in> set (map fst (d_states M k' q))) = Suc k\<close> True by force
        then show ?thesis
          using \<open>fst qx \<in> set (map fst (d_states M (Suc k) q))\<close> True 
                \<open>t_target t = q \<or> t_target t \<in> set (map fst (d_states M (Suc k - 1) q))\<close>
                \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by auto
      next
        case False
        then show ?thesis
          using Suc.IH Suc.prems \<open>d_states M (Suc k) q = d_states M k q @ [qx]\<close> by fastforce 
      qed
    qed
  qed

  then show "(t_target t \<in> set (map fst (d_states M k q)) \<and> (LEAST k' . t_target t \<in> set (map fst (d_states M k' q))) < (LEAST k' . t_source t \<in> set (map fst (d_states M k' q))))
              \<or> (t_target t = q)"
        and "t_source t \<in> set (map fst (d_states M k q))" by simp+
qed



lemma d_states_q_noncontainment :
  shows "\<not>(\<exists> qqx \<in> set (d_states M k q) . fst qqx = q)" 
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  
  show ?case proof (cases "length (d_states M k q) < k")
    case True
    then show ?thesis unfolding d_states.simps using Suc by auto
  next
    case False

    show ?thesis proof (cases "find
                             (\<lambda>qx. fst qx \<noteq> q \<and>
                                   (\<forall>qx'\<in>set (d_states M k q). fst qx \<noteq> fst qx') \<and>
                                   (\<exists>t\<in>set (wf_transitions M). t_source t = fst qx \<and> t_input t = snd qx) \<and>
                                   (\<forall>t\<in>set (wf_transitions M).
                                       t_source t = fst qx \<and> t_input t = snd qx \<longrightarrow>
                                       t_target t = q \<or> (\<exists>qx'\<in>set (d_states M k q). fst qx' = t_target t)))
                             (concat (map (\<lambda>q. map (Pair q) (inputs M)) (nodes_from_distinct_paths M)))")
      case None
      then show ?thesis unfolding d_states.simps using Suc False by auto
    next
      case (Some a)
      then have "(d_states M (Suc k) q) = (d_states M k q)@[a]"
        unfolding d_states.simps using False by auto
      then show ?thesis using Suc find_condition[OF Some] by auto
    qed
  qed  
qed





lemma d_states_induces_state_separator_helper_distinct_pathlikes :
  assumes "\<And> i . (Suc i) < length (t#p) \<Longrightarrow> t_source ((t#p) ! (Suc i)) = t_target ((t#p) ! i)"
  assumes "set (t#p) \<subseteq> set (filter 
                           (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                        (wf_transitions M))"
  
  shows "distinct ((t_source t) # map t_target (t#p))" 
proof - 

  let ?f = "\<lambda> q' . if q' = q then 0 else LEAST k' . q' \<in> set (map fst (d_states M k' q))"
  let ?p = "(t_source t) # map t_target (t#p)"

  have "\<And> t' . t' \<in> set (t#p) \<Longrightarrow> t_source t' \<noteq> q"
    using d_states_q_noncontainment[of M k q] assms(2)
  proof -
    fix t' :: "'a \<times> integer \<times> integer \<times> 'a"
    assume "t' \<in> set (t # p)"
    then have "\<And>P. \<not> set (t # p) \<subseteq> P \<or> t' \<in> P"
      by (metis subset_code(1))
    then have "t' \<in> set (filter (\<lambda>p. \<exists>pa. pa \<in> set (d_states M k q) \<and> t_source p = fst pa \<and> t_input p = snd pa) (wf_transitions M))"
      by (metis (no_types, lifting) assms(2))
    then show "t_source t' \<noteq> q"
      using \<open>\<not> (\<exists>qqx\<in>set (d_states M k q). fst qqx = q)\<close> by auto
  qed 

  have f1: "\<And> i . (Suc i) < length ?p \<Longrightarrow> ?f (?p ! i) > ?f (?p ! (Suc i))"
  proof -
    fix i assume "Suc i < length ?p"
    
    
    let ?t1 = "(t#t#p) ! i"
    let ?t2 = "(t#t#p) ! (Suc i)"

    have "length (t#t#p) = length ?p" by auto
    



    show "?f (?p ! i) > ?f (?p ! (Suc i))" proof (cases i)
      case 0
      then have "?t1 = ?t2"
        by auto

      have "?t1 \<in> h M"
        using assms(2) 
        by (metis (no_types, lifting) Suc_lessD \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>length (t # t # p) = length (t_source t # map t_target (t # p))\<close> filter_is_subset list.set_intros(1) nth_mem set_ConsD subsetD)  
      have "?t1 \<in> set (t#t#p)"
        using \<open>length (t#t#p) = length ?p\<close>
              \<open>Suc i < length ?p\<close>
        by (metis Suc_lessD nth_mem)
      have "?t1 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t1 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then consider
          (a) "t_target ?t1 \<in> set (map fst (d_states M k q)) \<and>
                      (LEAST k'. t_target ?t1 \<in> set (map fst (d_states M k' q)))
                      < (LEAST k'. t_source ?t1 \<in> set (map fst (d_states M k' q)))" |
          (b) "t_target ?t1 = q"
          using d_states_distinct_least(1)[of ?t1 M k q] by presburger

      then show ?thesis proof cases
        case a
        moreover have "(t_source t # map t_target (t # p)) ! Suc i \<noteq> q" 
          using 0 assms(2) d_states_q_noncontainment
          using a by fastforce 
        moreover have "(t_source t # map t_target (t # p)) !i \<noteq> q" 
          using 0 assms(2) d_states_q_noncontainment
          using a by fastforce 
        ultimately show ?thesis using \<open>?t1 = ?t2\<close> 0
          by (simp add: "0") 
      next
        case b
        then have "t_target t = q"
          using 0 by auto
        then have "?f (?p ! (Suc i)) = 0" using 0 by auto
        
        have "?p ! i \<in> set (map fst (d_states M k q))"
          using assms(2) 0 by auto
        have "?p ! i \<notin> set (map fst (d_states M 0 q))"
          by auto
        have "(LEAST k'. ?p ! i \<in> set (map fst (d_states M k' q))) > 0"
          by (metis (no_types) LeastI_ex \<open>(t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k q))\<close> \<open>(t_source t # map t_target (t # p)) ! i \<notin> set (map fst (d_states M 0 q))\<close> neq0_conv)
        moreover have "?p ! i \<noteq> q"
          using assms(2) d_states_q_noncontainment 0 by force
        ultimately have "?f (?p ! i) > 0" by auto
          

        then show ?thesis 
          using \<open>?f (?p ! (Suc i)) = 0\<close> by auto 
      qed 
        
    next
      case (Suc m)

      have "?t2 \<in> set (t#t#p)"
        using \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (metis nth_mem) 
      
      have "?t2 \<in> h M"
        using assms(2) using \<open>(t#t#p) ! (Suc i) \<in> set (t#t#p)\<close> by auto 
  
      have "?t2 \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))"
        using \<open>?t2 \<in> set (t#t#p)\<close> assms(2)
        by (metis (no_types, lifting) list.set_intros(1) set_ConsD subsetD) 
      then consider
        (a) "t_target ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k q)) \<and> 
              (LEAST k'. t_target ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k' q)))
                < (LEAST k'. t_source ((t # t # p) ! Suc i) \<in> set (map fst (d_states M k' q)))" |
        (b) "t_target ((t # t # p) ! Suc i) = q"
        using d_states_distinct_least(1)[of ?t2 M k q] by presburger

      then show ?thesis proof cases
        case a

        have "t_source ?t2 = t_target ?t1"
        using assms(1) \<open>Suc i < length ?p\<close> \<open>length (t#t#p) = length ?p\<close>
        by (simp add: Suc) 

        then have " t_target ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! Suc i"
          by (metis Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> length_Cons length_map nth_Cons_Suc nth_map)
        moreover have "t_source ((t # t # p) ! Suc i) = (t_source t # map t_target (t # p)) ! i"
          by (metis Suc Suc_lessD Suc_less_eq \<open>Suc i < length (t_source t # map t_target (t # p))\<close> \<open>t_source ((t # t # p) ! Suc i) = t_target ((t # t # p) ! i)\<close> length_Cons length_map nth_Cons_Suc nth_map)  
        moreover have "(t_source t # map t_target (t # p)) ! Suc i \<noteq> q"
          using a d_states_q_noncontainment
          using calculation(1) by fastforce 
        moreover have "(t_source t # map t_target (t # p)) ! i \<noteq> q"
          by (metis \<open>(t # t # p) ! Suc i \<in> set (t # t # p)\<close> \<open>\<And>t'. t' \<in> set (t # p) \<Longrightarrow> t_source t' \<noteq> q\<close> calculation(2) list.set_intros(1) set_ConsD)
        ultimately show "?f (?p ! i) > ?f (?p ! (Suc i))" 
          using a by simp
      next
        case b 


        then have "?f (?p ! (Suc i)) = 0" using Suc
          using \<open>Suc i < length (t_source t # map t_target (t # p))\<close> by auto 

        have "?p ! i = t_target ((t#p) ! (i - 1))"
          using Suc \<open>Suc i < length ?p\<close>
          by (metis Suc_lessD Suc_less_eq diff_Suc_1 length_Cons length_map nth_Cons_Suc nth_map) 
        then have "?p ! i = t_source ((t#p) ! i)"
          using Suc assms(1)
          using \<open>Suc i < length (t_source t # map t_target (t # p))\<close> by auto 
        then have "?p ! i \<in> set (map fst (d_states M k q))"
          using assms(2)
          using \<open>(t # t # p) ! Suc i \<in> set (filter (\<lambda>t. \<exists>qqx\<in>set (d_states M k q). t_source t = fst qqx \<and> t_input t = snd qqx) (wf_transitions M))\<close> by auto 
        have "?p ! i \<notin> set (map fst (d_states M 0 q))"
          by auto
        have "(LEAST k'. ?p ! i \<in> set (map fst (d_states M k' q))) > 0"
          by (metis (no_types) LeastI_ex \<open>(t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k q))\<close> \<open>(t_source t # map t_target (t # p)) ! i \<notin> set (map fst (d_states M 0 q))\<close> neq0_conv)
        moreover have "?p ! i \<noteq> q"
          using \<open>(t # t # p) ! Suc i \<in> set (t # t # p)\<close> \<open>(t_source t # map t_target (t # p)) ! i = t_source ((t # p) ! i)\<close> \<open>\<And>t'. t' \<in> set (t # p) \<Longrightarrow> t_source t' \<noteq> q\<close> by auto 
        ultimately have "?f (?p ! i) > 0" by auto

        then show ?thesis 
          using \<open>?f (?p ! (Suc i)) = 0\<close> by auto 
      qed 
    qed
  qed


  moreover have f2: "\<And> i . i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! i = (if (t_source t # map t_target (t # p)) ! i = q then 0 else LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k' q)))"
  proof -
    fix i assume "i < length (map ?f ?p)"
    have map_index : "\<And> xs f i . i < length (map f xs) \<Longrightarrow> (map f xs) ! i = f (xs ! i)"
      by simp
    show "map ?f ?p ! i = (if (t_source t # map t_target (t # p)) ! i = q then 0 else LEAST k'. (t_source t # map t_target (t # p)) ! i \<in> set (map fst (d_states M k' q)))"
      using map_index[OF \<open>i < length (map ?f ?p)\<close>] by assumption
  qed

  ultimately have "(\<And>i. Suc i < length (map ?f ?p) \<Longrightarrow> map ?f ?p ! Suc i < map ?f ?p ! i)"
  proof -
    fix i assume "Suc i < length (map ?f ?p)"
    then have "Suc i < length ?p" 
              "i < length (map ?f ?p)"
              "i < length ?p"
       by auto

    note f2[OF \<open>Suc i < length (map ?f ?p)\<close>] 
    moreover note f2[OF \<open>i < length (map ?f ?p)\<close>]
    moreover note f1[OF \<open>Suc i < length ?p\<close>]
    ultimately show "map ?f ?p ! Suc i < map ?f ?p ! i"
      by linarith
  qed

  then have "distinct (map ?f ?p)"
    using ordered_list_distinct_rev[of "map ?f ?p"] by blast

  then show "distinct ?p"
    using distinct_map[of ?f ?p] by linarith
qed

lemma d_states_last_ex_k :
  assumes "qqx \<in> set (d_states M k q)"  
  shows "\<exists> k' . d_states M (Suc k') q = (d_states M k' q) @ [qqx]"
proof -
  obtain k' where "k'\<le>k" and "0 < k'" and "qqx = last (d_states M k' q)" 
                  "(\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (d_states M k'' q))"
    using d_states_last_ex[OF assms] by blast

  have "k' = (LEAST k' . qqx \<in> set (d_states M k' q))"
    by (metis \<open>0 < k'\<close> \<open>\<forall>k''<k'. 0 < k'' \<longrightarrow> qqx \<noteq> last (d_states M k'' q)\<close> \<open>qqx = last (d_states M k' q)\<close> assms nat_neq_iff d_states_last_ex d_states_last_least)

  from \<open>0 < k'\<close> obtain k'' where Suc: "k' = Suc k''"
    using gr0_conv_Suc by blast 

  then have "qqx = last (d_states M (Suc k'') q)"
    using \<open>qqx = last (d_states M k' q)\<close> by auto
  have "Suc k'' = (LEAST k' . qqx \<in> set (d_states M k' q))"
    using \<open>k' = (LEAST k' . qqx \<in> set (d_states M k' q))\<close> Suc by auto
  then have "qqx \<notin> set (d_states M k'' q)"
    by (metis lessI not_less_Least)
  then have "(d_states M (Suc k'') q) \<noteq> (d_states M k'' q)"
    using \<open>Suc k'' = (LEAST k' . qqx \<in> set (d_states M k' q))\<close>
    by (metis Suc Suc_neq_Zero \<open>k' \<le> k\<close> \<open>qqx = last (d_states M (Suc k'') q)\<close> assms last_in_set d_states_prefix take_eq_Nil)

  have "d_states M (Suc k'') q = d_states M k'' q @ [qqx]"
    by (metis \<open>qqx = last (d_states M (Suc k'') q)\<close> \<open>d_states M (Suc k'') q \<noteq> d_states M k'' q\<close> last_snoc d_states_last)
  then show ?thesis by blast
qed











thm is_preamble.simps


lemma d_states_induces_state_preamble :
  assumes "(d_states M k q) \<noteq> []"
  and     "q \<noteq> initial M" (* TODO: add special case in final function, as *)
  and     "S = \<lparr> initial = initial M,
                 inputs = inputs M,
                 outputs = outputs M,
                 transitions = 
                       filter 
                         (\<lambda>t . \<exists> qqx \<in> set (d_states M k q) . t_source t = fst qqx \<and> t_input t = snd qqx) 
                    (wf_transitions M),
                 \<dots> = more M \<rparr>"
shows "is_preamble S M q" 
proof -

  have is_acyclic: "acyclic S" sorry
  have is_single_input: "single_input S" sorry
  have is_sub: "is_submachine S M" sorry
  have contains_q : "q \<in> nodes S" sorry
  have has_deadlock_q : "deadlock_state S q" sorry
  have has_nodes_prop : "(\<forall>q'\<in>nodes S.
        (q = q' \<or> \<not> deadlock_state S q') \<and>
        (\<forall>x\<in>set (inputs M).
            (\<exists>t\<in>set (wf_transitions S). t_source t = q' \<and> t_input t = x) \<longrightarrow>
            (\<forall>t'\<in>set (wf_transitions M). t_source t' = q' \<and> t_input t' = x \<longrightarrow> t' \<in> set (wf_transitions S))))" sorry

  show ?thesis
    unfolding is_preamble.simps
    using is_acyclic 
          is_single_input 
          is_sub
          contains_q
          has_deadlock_q
          has_nodes_prop
    by presburger
qed


end