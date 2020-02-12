theory IO_Sequence_Set
imports FSM
begin


section \<open>Properties of Sets of IO Sequences\<close>

fun output_completion :: "(Input \<times> Output) list set \<Rightarrow> Output set \<Rightarrow> (Input \<times> Output) list set" where
  "output_completion P Out = P \<union> {io@[(fst xy, y)] | io xy y . y \<in> Out \<and> io@[xy] \<in> P \<and> io@[(fst xy, y)] \<notin> P}"


fun output_complete_sequences :: "'a FSM \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_sequences M P = (\<forall> io \<in> P . io = [] \<or> (\<forall> y \<in> set (outputs M) . (butlast io)@[(fst (last io), y)] \<in> P))"

value "output_complete_sequences M_ex {}"  
value "output_complete_sequences M_ex {[]}"
value "output_complete_sequences M_ex {[],[(1,10)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)]}"
value "output_complete_sequences M_ex {[],[(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,20)],[(1,30)]}"
value "output_complete_sequences M_ex {[],[(1,10),(1,10)],[(1,10),(1,20)],[(1,10),(1,30)]}"



fun acyclic_sequences :: "'a FSM \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences M q P = (\<forall> p . (path M q p \<and> p_io p \<in> P) \<longrightarrow> distinct (visited_states q p))"

fun acyclic_sequences' :: "'a FSM \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "acyclic_sequences' M q P = (\<forall> io \<in> P . \<forall> p \<in> set (paths_of_length M q (length io)) . (p_io p = io) \<longrightarrow> distinct (visited_states q p))"

lemma acyclic_sequences_alt_def[code] : "acyclic_sequences M P = acyclic_sequences' M P"
  unfolding acyclic_sequences'.simps acyclic_sequences.simps
  by (metis (no_types, lifting) length_map paths_of_length_containment paths_of_length_is_path(1))
  
value "acyclic_sequences M_ex (initial M_ex) {}"  
value "acyclic_sequences M_ex (initial M_ex) {[]}"
value "acyclic_sequences M_ex (initial M_ex) {[(1,30)]}"
value "acyclic_sequences M_ex (initial M_ex) {[(1,30),(2,20)]}"





fun single_input_sequences :: "'a FSM \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "single_input_sequences M P = (\<forall> xys1 xys2 xy1 xy2 . (xys1@[xy1] \<in> P \<and> xys2@[xy2] \<in> P \<and> io_target M xys1 (initial M) = io_target M xys2 (initial M)) \<longrightarrow> fst xy1 = fst xy2)"

fun single_input_sequences' :: "'a FSM \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
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

fun output_complete_for_FSM_sequences_from_state :: "'a FSM \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences_from_state M q P = (\<forall> io xy t . io@[xy] \<in> P \<and> t \<in> h M \<and> t_source t = io_target M io q \<and> t_input t = fst xy \<longrightarrow> io@[(fst xy, t_output t)] \<in> P)"

lemma output_complete_for_FSM_sequences_from_state_alt_def :
  shows "output_complete_for_FSM_sequences_from_state M q P = (\<forall> xys xy y . (xys@[xy] \<in> P \<and> [(fst xy,y)] \<in> LS M (io_target M xys q)) \<longrightarrow> xys@[(fst xy,y)] \<in> P)"
proof -
  have "\<And> xys (xy :: (Input \<times> Output)) y .[(fst xy,y)] \<in> LS M (io_target M xys q) \<Longrightarrow> \<exists> t . t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "[(fst xy,y)] \<in> LS M (io_target M xys q)"
    then obtain p where "path M (io_target M xys q) p" and "p_io p = [(fst xy,y)]"
      unfolding LS.simps mem_Collect_eq by (metis (no_types, lifting)) 
    let ?t = "hd p"
    have "?t \<in> h M \<and> t_source ?t = io_target M xys q \<and> t_input ?t = fst xy \<and> t_output ?t = y"
      using \<open>p_io p = [(fst xy, y)]\<close> \<open>path M (io_target M xys q) p\<close> by auto
    
    then show "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
  qed
  have "\<And> xys (xy :: (Input \<times> Output)) y . \<exists> t . t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy,y)] \<in> LS M (io_target M xys q)"
  proof -
    fix xys y 
    fix xy :: "(Input \<times> Output)"
    assume "\<exists> t . t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y"
    then obtain t where "t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y"
      by blast
    then have "path M (io_target M xys q) [t] \<and> p_io [t] = [(fst xy, y)]"
      by (metis (no_types, lifting) list.simps(8) list.simps(9) single_transition_path)
      

    then show "[(fst xy,y)] \<in> LS M (io_target M xys q)"
      unfolding LS.simps by (metis (mono_tags, lifting) mem_Collect_eq) 
  qed

  show ?thesis
  proof -
    have *: "\<forall>f q P. output_complete_for_FSM_sequences_from_state f q P = (\<forall>ps p pa. (ps @ [p] \<notin> P \<or> pa \<notin> h f \<or> (t_source pa::'a) \<noteq> io_target f ps q \<or> t_input pa \<noteq> fst p) \<or> ps @ [(fst p, t_output pa)] \<in> P)"
      by (meson output_complete_for_FSM_sequences_from_state.simps)
  then have "(\<not> output_complete_for_FSM_sequences_from_state M q P) \<noteq> (\<forall>ps p n. (ps @ [p] \<notin> P \<or> [(fst p, n)] \<notin> LS M (io_target M ps q)) \<or> ps @ [(fst p, n)] \<in> P)"
  by (metis (full_types) \<open>\<And>y xys xy. [(fst xy, y)] \<in> LS M (io_target M xys q) \<Longrightarrow> \<exists>t. t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y\<close> \<open>\<And>y xys xy. \<exists>t. t \<in> h M \<and> t_source t = io_target M xys q \<and> t_input t = fst xy \<and> t_output t = y \<Longrightarrow> [(fst xy, y)] \<in> LS M (io_target M xys q)\<close>)
    then show ?thesis
      by blast
  qed 
qed

fun output_complete_for_FSM_sequences_from_state' :: "'a FSM \<Rightarrow> 'a \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
  "output_complete_for_FSM_sequences_from_state' M q P = (\<forall> io\<in>P . \<forall> t \<in> h M . io = [] \<or> (t_source t = io_target M (butlast io) q \<and> t_input t = fst (last io) \<longrightarrow> (butlast io)@[(fst (last io), t_output t)] \<in> P))"

lemma output_complete_for_FSM_sequences_alt_def'[code] : "output_complete_for_FSM_sequences_from_state M q P = output_complete_for_FSM_sequences_from_state' M q P"
  unfolding output_complete_for_FSM_sequences_from_state.simps output_complete_for_FSM_sequences_from_state'.simps
  by (metis last_snoc snoc_eq_iff_butlast)
  

value "output_complete_for_FSM_sequences_from_state M_ex (initial M_ex) {}"
value "output_complete_for_FSM_sequences_from_state M_ex (initial M_ex) {[]}"
value "output_complete_for_FSM_sequences_from_state M_ex (initial M_ex) {[(1,20)]}"
value "output_complete_for_FSM_sequences_from_state M_ex (initial M_ex) {[(1,10)],[(1,20)]}"
value "output_complete_for_FSM_sequences_from_state M_ex (initial M_ex) {[(1,20)],[(1,30)]}"


fun deadlock_states_sequences :: "'a FSM \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
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



fun reachable_states_sequences :: "'a FSM \<Rightarrow> 'a set \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> bool" where
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



subsection \<open>Completions\<close>

definition prefix_completion :: "'a list set \<Rightarrow> 'a list set" where
  "prefix_completion P = {xs . \<exists> ys . xs@ys \<in> P}"

lemma prefix_completion_closed :
  "prefix_closed_sequences (prefix_completion P)"
  unfolding prefix_closed_sequences.simps prefix_completion_def
  by auto 

lemma prefix_completion_source_subset :
  "P \<subseteq> prefix_completion P" 
  unfolding prefix_completion_def
  by (metis (no_types, lifting) append_Nil2 mem_Collect_eq subsetI) 


definition output_completion_for_FSM :: "('a,'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list set \<Rightarrow> (Input \<times> Output) list set" where
  "output_completion_for_FSM M P = P \<union> { io@[(x,y')] | io x y' . (y' \<in> set (outputs M)) \<and> (\<exists> y . io@[(x,y)] \<in> P)}"

lemma output_completion_for_FSM_complete :
  shows "output_complete_sequences M (output_completion_for_FSM M P)"
  unfolding output_completion_for_FSM_def output_complete_sequences.simps 
proof 
  fix io assume *: "io \<in> P \<union> {io @ [(x, y')] |io x y'. y' \<in> set (outputs M) \<and> (\<exists>y. io @ [(x, y)] \<in> P)}"
  show   "io = [] \<or>
          (\<forall>y\<in>set (outputs M).
              butlast io @ [(fst (last io), y)]
              \<in> P \<union> {io @ [(x, y')] |io x y'. y' \<in> set (outputs M) \<and> (\<exists>y. io @ [(x, y)] \<in> P)})"
  proof (cases io rule: rev_cases)
    case Nil
    then show ?thesis by blast
  next
    case (snoc ys y)
    then show ?thesis proof (cases "io \<in> P")
      case True  
      then have "butlast io @ [(fst (last io), (snd (last io)))] \<in> P" using snoc by auto
      then show ?thesis using snoc by blast
    next
      case False
      then show ?thesis
        using "*" by auto 
    qed 
  qed
qed

lemma output_completion_for_FSM_length :
  assumes "\<forall> io \<in> P . length io \<le> k"
  shows   "\<forall> io \<in> output_completion_for_FSM M P. length io \<le> k" 
  using assms unfolding output_completion_for_FSM_def
  by auto 

fun output_completion_for_FSM_list :: "('a,'b) FSM_scheme \<Rightarrow> (Input \<times> Output) list list \<Rightarrow> (Input \<times> Output) list list" where
  "output_completion_for_FSM_list M [] = []" |
  "output_completion_for_FSM_list M (io#ios) = (case length io of
    0 \<Rightarrow> [] # (output_completion_for_FSM_list M ios) |
    Suc k \<Rightarrow> io # (map (\<lambda>y . (butlast io @ [(fst (last io), y)])) (outputs M))) @ (output_completion_for_FSM_list M ios)"



lemma output_completion_for_FSM_code[code] :
  "output_completion_for_FSM M (set xs) = set (remdups (output_completion_for_FSM_list M xs))"
proof (induction xs)
  case Nil
  then show ?case unfolding output_completion_for_FSM_def by auto
next
  case (Cons x xs)

  have *: "output_completion_for_FSM M (set (x # xs)) = output_completion_for_FSM M {x} \<union> output_completion_for_FSM M (set xs)"
    unfolding output_completion_for_FSM_def by force

  show ?case proof (cases "length x")
    case 0
    then have "set (output_completion_for_FSM_list M (x#xs)) = {[]} \<union> set (output_completion_for_FSM_list M xs)"
      by auto
    moreover have "output_completion_for_FSM M {x} = {[]}"
      using 0 unfolding output_completion_for_FSM_def by auto
    ultimately show ?thesis using * Cons.IH by force
  next
    case (Suc nat)
    then have **: "set (output_completion_for_FSM_list M (x#xs)) = (set (x # map (\<lambda>y . (butlast x @ [(fst (last x), y)])) (outputs M))) \<union> set (output_completion_for_FSM_list M xs)"
      by auto

    have "{(butlast x @ [(fst (last x), snd (last x))])} = {x}"
      using Suc snoc_eq_iff_butlast by fastforce 
    then have "set (map (\<lambda>y. butlast x @ [(fst (last x), y)]) (outputs M)) = {butlast x @[(fst (last x),y)] | y . y \<in> set (outputs M)}"
      by auto
    moreover have "{io @ [(xa, y')] |io xa y'. y' \<in> set (outputs M) \<and> (\<exists>y. io @ [(xa, y)] \<in> {x})} = {butlast x @[(fst (last x),y)] | y . y \<in> set (outputs M)}"
      using \<open>{(butlast x @ [(fst (last x), snd (last x))])} = {x}\<close>
      by (metis (no_types, lifting) butlast_snoc fst_conv insertI1 last_snoc singletonD) 
    ultimately have "(set (map (\<lambda>y . (butlast x @ [(fst (last x), y)])) (outputs M))) = {io @ [(xa, y')] |io xa y'. y' \<in> set (outputs M) \<and> (\<exists>y. io @ [(xa, y)] \<in> {x})}"
      by auto
    then have "(set (x # map (\<lambda>y . (butlast x @ [(fst (last x), y)])) (outputs M))) = output_completion_for_FSM M {x}"
      unfolding output_completion_for_FSM_def by auto 
    then show ?thesis 
      using * ** Cons.IH by auto
  qed
qed


value "output_completion_for_FSM_list M_ex_H [[(0,0)],[(0,0),(1,1)]]"
value "output_completion_for_FSM M_ex_H {[(0,0)],[(0,0),(1,1)]}"

end