theory IO_Sequence_Set
imports FSM
begin


section \<open>Properties of Sets of IO Sequences\<close>

fun output_completion :: "(Input \<times> Output) list set \<Rightarrow> Output set \<Rightarrow> (Input \<times> Output) list set" where
  "output_completion P Out = P \<union> {io@[(fst xy, y)] | io xy y . y \<in> Out \<and> io@[xy] \<in> P \<and> io@[(fst xy, y)] \<notin> P}"


fun output_complete_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_sequences M P = (\<forall> io \<in> P . io = [] \<or> (\<forall> y \<in> set (outputs M) . (butlast io)@[(fst (last io), y)] \<in> P))"

value "output_complete_sequences M_ex {}"  
value "output_complete_sequences M_ex {[]}"
value "output_complete_sequences M_ex {[],[(1,10)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,10),(1,20)],[(1,10),(1,30)]}"



fun acyclic_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences M q P = (\<forall> p . (path M q p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states q p))"

fun acyclic_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences' M q P = (\<forall> io \<in> P . \<forall> p \<in> set (paths_of_length M q (length io)) . (p_io p = io) \<longrightarrow> distinct (visited_states q p))"

lemma acyclic_sequences_alt_def[code] : "acyclic_sequences M P = acyclic_sequences' M P"
  unfolding acyclic_sequences'.simps acyclic_sequences.simps
  by (metis (no_types, lifting) length_map paths_of_length_containment paths_of_length_is_path(1))
  
value "acyclic_sequences M_ex (initial M_ex) {}"  
value "acyclic_sequences M_ex (initial M_ex) {[]}"
value "acyclic_sequences M_ex (initial M_ex) {[(1,30)]}"
value "acyclic_sequences M_ex (initial M_ex) {[(1,30),(2,20)]}"





fun single_input_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "single_input_sequences M P = (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)"

fun single_input_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "single_input_sequences' M P = (\<forall> io1 \<in> P . \<forall> io2 \<in> P . io1 = [] \<or> io2 = [] \<or> ((io_target M (butlast io1) (initial M) = io_target M (butlast io2) (initial M)) \<longrightarrow> fst (last io1) = fst (last io2)))"

lemma single_input_sequences_alt_def[code] : "single_input_sequences M P = single_input_sequences' M P"
  unfolding single_input_sequences.simps single_input_sequences'.simps
  by (metis append_butlast_last_id append_is_Nil_conv butlast_snoc last_snoc not_Cons_self)

value "single_input_sequences M_ex {}"
value "single_input_sequences M_ex {[]}"
value "single_input_sequences M_ex {[(1,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(2,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,20)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(1,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(2,30)]}"
value "single_input_sequences M_ex {[(1,30)],[(1,30),(1,30)],[(1,30),(2,30)]}"

fun output_complete_for_FSM_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences M P = (\<forall> io xy t . io@[xy] \<in> P \<and> t \<in> h M \<and> t_source t = io_target M io (initial M) \<and> t_input t = fst xy \<longrightarrow> io@[(fst xy, t_output t)] \<in> P)"

lemma output_complete_for_FSM_sequences_alt_def :
  shows "output_complete_for_FSM_sequences M P = (\<forall> xys xy y . (xys@[xy] \<in> P \<and> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))) \<longrightarrow> xys@[(fst xy,y)] \<in> P)"
proof -
  have "\<And> xys (xy :: (Input \<times> Output)) y .[(fst xy,y)] \<in> LS M (io_target M xys (initial M)) \<Longrightarrow> \<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
    then obtain p where "path M (io_target M xys (initial M)) p" and "p_io p = [(fst xy,y)]"
      unfolding LS.simps mem_Collect_eq by (metis (no_types, lifting)) 
    let ?t = "hd p"
    have "?t \<in> h M \<and> t_source ?t = io_target M xys (initial M) \<and> t_input ?t = fst xy \<and> t_output ?t = y"
      using \<open>p_io p = [(fst xy, y)]\<close> \<open>path M (io_target M xys (initial M)) p\<close> by auto
    
    then show "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
  qed
  have "\<And> xys (xy :: (Input \<times> Output)) y . \<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
    then obtain t where "t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
    then have "path M (io_target M xys (initial M)) [t] \<and> p_io [t] = [(fst xy, y)]"
      by (metis (no_types, lifting) list.simps(8) list.simps(9) single_transition_path)
      

    then show "[(fst xy,y)] \<in> LS M (io_target M xys (initial M))"
      unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
  qed

  show ?thesis
  proof -
    have "\<forall>f P. output_complete_for_FSM_sequences f P = (\<forall>ps p pa. (ps @ [p] \<notin> P \<or> pa \<notin> h f \<or> (t_source pa::'a) \<noteq> io_target f ps (initial f) \<or> t_input pa \<noteq> fst p) \<or> ps @ [(fst p, t_output pa)] \<in> P)"
      by (meson output_complete_for_FSM_sequences.simps)
  then have "(\<not> output_complete_for_FSM_sequences M P) \<noteq> (\<forall>ps p n. (ps @ [p] \<notin> P \<or> [(fst p, n)] \<notin> LS M (io_target M ps (initial M))) \<or> ps @ [(fst p, n)] \<in> P)"
  by (metis (full_types) \<open>\<And>y xys xy. [(fst xy, y)] \<in> LS M (io_target M xys (initial M)) \<Longrightarrow> \<exists>t. t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y\<close> \<open>\<And>y xys xy. \<exists>t. t \<in> h M \<and> t_source t = io_target M xys (initial M) \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy, y)] \<in> LS M (io_target M xys (initial M))\<close>)
    then show ?thesis
      by blast
  qed 
qed

fun output_complete_for_FSM_sequences' :: "('a, 'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences' M P = (\<forall> io\<in>P . \<forall> t \<in> h M . io = [] \<or> (t_source t = io_target M (butlast io) (initial M) \<and> t_input t = fst (last io) \<longrightarrow> (butlast io)@[(fst (last io), t_output t)] \<in> P))"

lemma output_complete_for_FSM_sequences_alt_def'[code] : "output_complete_for_FSM_sequences M P = output_complete_for_FSM_sequences' M P"
  unfolding output_complete_for_FSM_sequences.simps output_complete_for_FSM_sequences'.simps
  by (metis last_snoc snoc_eq_iff_butlast)
  

value "output_complete_for_FSM_sequences M_ex {}"
value "output_complete_for_FSM_sequences M_ex {[]}"
value "output_complete_for_FSM_sequences M_ex {[(1,20)]}"
value "output_complete_for_FSM_sequences M_ex {[(1,10)],[(1,20)]}"
value "output_complete_for_FSM_sequences M_ex {[(1,20)],[(1,30)]}"


fun deadlock_states_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "deadlock_states_sequences M Q P = (\<forall> xys \<in> P . 
                                        ((io_target M xys (initial M) \<in> Q 
                                          \<and> \<not> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))
                                      \<or> (\<not> io_target M xys (initial M) \<in> Q 
                                          \<and> (\<exists> xys' \<in> P . length xys < length xys' \<and> take (length xys) xys' = xys)))" 

value "deadlock_states_sequences M_ex {} {}"
value "deadlock_states_sequences M_ex {} {[]}"
value "deadlock_states_sequences M_ex {2} {[]}" 
value "deadlock_states_sequences M_ex {3} {[]}"
value "deadlock_states_sequences M_ex {3} {[(1,20)]}"
value "deadlock_states_sequences M_ex {2,3} {[(1,20)]}"
value "deadlock_states_sequences M_ex {2,3} {[(1,30)]}"
value "deadlock_states_sequences M_ex {2,4} {[],[(1,30)]}"
value "deadlock_states_sequences M_ex {2,4} {[(1,20)],[(1,30)]}"
value "deadlock_states_sequences M_ex {3,4} {[(1,20)],[(1,30)]}"



fun reachable_states_sequences :: "('a, 'b) FSM_scheme \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "reachable_states_sequences M Q P = (\<forall> q \<in> Q . \<exists> xys \<in> P . io_target M xys (initial M) = q)"


value "reachable_states_sequences M_ex {} {}"
value "reachable_states_sequences M_ex {} {[]}"
value "reachable_states_sequences M_ex {2} {}"
value "reachable_states_sequences M_ex {2} {[]}"
value "reachable_states_sequences M_ex {3,4} {[(1,20)],[(1,30),(2,20)]}"
value "reachable_states_sequences M_ex {3,4} {[(1,20)],[(1,30)]}"
value "reachable_states_sequences M_ex {3,4,5} {[(1,20)],[(1,30)]}"


fun prefix_closed_sequences :: "(Input \<times> Output) list set \<Rightarrow> bool" where
  "prefix_closed_sequences P = (\<forall> xys1 xys2 . xys1@xys2 \<in> P \<longrightarrow> xys1 \<in> P)"

fun prefix_closed_sequences' :: "(Input \<times> Output) list set \<Rightarrow> bool" where
  "prefix_closed_sequences' P = (\<forall> io \<in> P . io = [] \<or> (butlast io) \<in> P)"

lemma prefix_closed_sequences_alt_def[code] : "prefix_closed_sequences P = prefix_closed_sequences' P"
proof 
  show "prefix_closed_sequences P \<Longrightarrow> prefix_closed_sequences' P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps
    by (metis append_butlast_last_id) 

  have "\<And>xys1 xys2. \<forall>io\<in>P. io = [] \<or> butlast io \<in> P \<Longrightarrow> xys1 @ xys2 \<in> P \<Longrightarrow> xys1 \<in> P"
  proof -
    fix xys1 xys2 assume "\<forall>io\<in>P. io = [] \<or> butlast io \<in> P" and "xys1 @ xys2 \<in> P"
    then show "xys1 \<in> P"
    proof (induction xys2 rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc a xys2)
      then show ?case
        by (metis append.assoc snoc_eq_iff_butlast) 
    qed
  qed

  then show "prefix_closed_sequences' P \<Longrightarrow> prefix_closed_sequences P"
    unfolding prefix_closed_sequences.simps prefix_closed_sequences'.simps by blast 
qed

value "prefix_closed_sequences {}"
value "prefix_closed_sequences {[]}"
value "prefix_closed_sequences {[(1,20)]}"
value "prefix_closed_sequences {[],[(1,20)]}"

end