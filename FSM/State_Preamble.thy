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

definition calculate_preamble_set_naive :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set option" where
  "calculate_preamble_set_naive M q = (let n = size M - 1 in
    (case 
      (filter 
        (\<lambda> S . language_up_to_length S (Suc n) = language_up_to_length S n \<and>  is_preamble_set M q (set (language_up_to_length S n))) 
        (generate_submachines M)) of
    [] \<Rightarrow> None |
    SS \<Rightarrow> (Some (set (language_up_to_length (hd SS) n)))))" 



lemma calculate_preamble_set_naive_soundness :
  assumes "calculate_preamble_set_naive M q = Some P"
  shows "is_preamble_set M q P"
proof -
  have P_prop : "P = set (language_up_to_length (hd 
              (filter 
                (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
                (generate_submachines M))
              ) ( size M - 1 ))"
    using assms unfolding calculate_preamble_set_naive_def
    by (metis (no_types, lifting) hd_Cons_tl list.case_eq_if option.discI option.inject)

  have *: "filter 
        (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
        (generate_submachines M) \<noteq> []"
    by (metis (mono_tags, lifting) assms calculate_preamble_set_naive_def list.case_eq_if option.discI)

  let ?S = "hd (filter 
        (\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and>  is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) 
        (generate_submachines M))"

  have "?S \<in> set (generate_submachines M)"
    using * by (metis (no_types, lifting) filter_set hd_in_set member_filter) 
  then have "is_submachine ?S M"
    using generate_submachines_are_submachines[of ?S M] by fastforce
  
  have "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and> is_preamble_set M q (set (language_up_to_length S ( size M - 1 )))) ?S"
    using filter_list_set_not_contained[OF \<open>?S \<in> set (generate_submachines M)\<close>, of "(\<lambda> S . language_up_to_length S (Suc ( size M - 1 )) = language_up_to_length S ( size M - 1 ) \<and> is_preamble_set M q (set (language_up_to_length S ( size M - 1 ))))"] hd_in_set[OF *] by fastforce
  then have "language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )" and "is_preamble_set M q (set (language_up_to_length ?S ( size M - 1 )))"
    by fastforce+
  
  have "set (language_up_to_length ?S ( size M - 1 )) = L ?S"
    using sym[OF language_up_to_length_finite_language_fixpoint[OF \<open>language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )\<close>]] by assumption
  moreover have "P = set (language_up_to_length ?S ( size M - 1 ))"
    using P_prop by fastforce
  ultimately have "P = L ?S"
    by metis
  moreover have "is_preamble_set M q (L ?S)"
    using \<open>is_preamble_set M q (set (language_up_to_length ?S ( size M - 1 )))\<close> sym[OF language_up_to_length_finite_language_fixpoint[OF \<open>language_up_to_length ?S (Suc ( size M - 1 )) = language_up_to_length ?S ( size M - 1 )\<close>]] by metis
  ultimately show ?thesis by metis
qed

(* TODO: move *)
lemma nodes_paths_by_same_h_initial :
  assumes "initial A = initial B"
      and "h A = h B"
    shows "nodes A = nodes B"
      and "path A q p = path B q p"
proof -
  show "nodes A = nodes B"
  proof -
    have "insert (initial A) {t_target p |p. p \<in> set (wf_transitions B)} = nodes B"
      using assms(1) h_nodes by force
    then show ?thesis
      by (metis (no_types) assms(2) h_nodes)
  qed 

  then show "path A q p = path B q p" using assms by (induction p arbitrary: q; fast)
qed

lemma language_by_same_h_initial :
  assumes "initial A = initial B"
      and "h A = h B"
    shows "L A = L B"
  unfolding LS.simps using nodes_paths_by_same_h_initial(2)[OF assms]
  using assms(1) by auto 




lemma calculate_preamble_set_naive_exhaustiveness :
  assumes "observable M"
  and     "is_preamble_set M q P"
  shows "calculate_preamble_set_naive M q \<noteq> None"
proof -

  obtain SP where "is_preamble SP M q" and "L SP = P"
    using preamble_set_implies_preamble[OF assms] by blast
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
    using is_preamble_set_length[OF assms(2)] by auto
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
    using assms(2) by metis
  
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
    by (metis (mono_tags, lifting) list.case_eq_if option.distinct(1))   
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



end