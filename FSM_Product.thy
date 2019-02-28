theory FSM_Product
imports FSM2
begin


fun productF :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('state1 \<times> 'state2)  
  \<Rightarrow> ('in, 'out, 'state1 \<times>'state2) FSM \<Rightarrow> bool" where
  "productF A B FAIL AB = ( 
    (inputs A = inputs B) 
  \<and> (fst FAIL \<notin> nodes A) 
  \<and> (snd FAIL \<notin> nodes B)
  \<and> AB =  \<lparr>
            succ = (\<lambda> a (p1,p2) . (if (p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst a \<in> inputs A) \<and> (snd a \<in> outputs A \<union> outputs B))
                                    then (if (succ A a p1 = {} \<and> succ B a p2 \<noteq> {})
                                      then {FAIL} 
                                      else (succ A a p1 \<times> succ B a p2))
                                    else {})),
            inputs = inputs A,
            outputs = outputs A \<union> outputs B,
            initial = (initial A, initial B)
          \<rparr> )"

lemma productF_simps[simp]:
  "productF A B FAIL AB \<Longrightarrow> succ AB a (p1,p2) = (if (p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst a \<in> inputs A) \<and> (snd a \<in> outputs A \<union> outputs B))
                                    then (if (succ A a p1 = {} \<and> succ B a p2 \<noteq> {})
                                      then {FAIL} 
                                      else (succ A a p1 \<times> succ B a p2))
                                    else {})"
  "productF A B FAIL AB \<Longrightarrow> inputs AB = inputs A"
  "productF A B FAIL AB \<Longrightarrow> outputs AB = outputs A \<union> outputs B"
  "productF A B FAIL AB \<Longrightarrow> initial AB = (initial A, initial B)"
  unfolding productF.simps by simp+




lemma succ_nodes :
  fixes A :: "('a,'b,'c) FSM"
  and   w :: "('a \<times> 'b)"
  assumes "q2 \<in> succ A w q1"
  and     "q1 \<in> nodes A"
shows "q2 \<in> nodes A"
proof -
  obtain x y where "w = (x,y)" by (meson surj_pair)
  then have "q2 \<in> successors A q1" using assms  by auto
  then have "q2 \<in> reachable A q1" by blast 
  then have "q2 \<in> reachable A (initial A)" using assms by blast 
  then show "q2 \<in> nodes A" by blast
qed

lemma productF_path :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "path A (w || r1) p1 \<and> path B (w || r2) p2"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "path (AB) (w || r1 || r2) (p1, p2)"
using assms  proof (induction w r1 r2 arbitrary: p1 p2 rule: list_induct3)
  case Nil
  then show ?case by auto
next
  case (Cons w ws r1 r1s r2 r2s) 
  then have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" by auto
  then have succs : "r1 \<in> succ A w p1 \<and> r2 \<in> succ B w p2" by auto
  then have "succ A w p1 \<noteq> {}" by force
  then have w_elem : "fst w \<in> inputs A \<and> snd w \<in> outputs A " using Cons by (metis assms(4) prod.collapse well_formed.elims(2))
  then have "(r1,r2) \<in> succ AB w (p1,p2)" using Cons succs by auto 
  then have path_head : "path AB ([w] || [(r1,r2)]) (p1,p2)" by auto
  
  have "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2" using Cons by auto
  moreover have "r1 \<in> nodes A \<and> r2 \<in> nodes B" using succs Cons.prems succ_nodes[of r1 A w p1] succ_nodes[of r2 B w p2] by auto
  ultimately have "path AB (ws || r1s || r2s) (r1,r2)" using Cons by blast 

  then show ?case using path_head by auto
qed






lemma fail_next_productF : 
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "productF M2 M1 FAIL PM"
shows "succ PM a FAIL = {}" 
proof (cases "((fst FAIL) \<in> nodes M2 \<and> (snd FAIL) \<in> nodes M1)")
  case True
  then show ?thesis using assms by auto
next
  case False
  then show ?thesis using assms by (cases "(succ M2 a (fst FAIL) = {} \<and> (fst a \<in> inputs M2) \<and> (snd a \<in> outputs M2))"; auto)
qed




lemma nodes_productF : 
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "productF M2 M1 FAIL PM"
shows "nodes PM \<subseteq> insert FAIL (nodes M2 \<times> nodes M1)"
proof 
  fix q assume q_assm : "q \<in> nodes PM"
  then show "q \<in> insert FAIL (nodes M2 \<times> nodes M1)"
  using assms proof (cases)
    case initial
    then show ?thesis using assms by auto
  next
    case (execute p a)
    then obtain p1 p2 x y q1 q2  where p_a_split[simp] : "p = (p1,p2)" "a = ((x,y),q)" "q = (q1,q2)" by (metis eq_snd_iff)
    have subnodes : "p1 \<in> nodes M2 \<and> p2 \<in> nodes M1 \<and> (x \<in> inputs M2) \<and> (y \<in> outputs M2 \<union> outputs M1)"  
    proof (rule ccontr)
      assume "\<not> (p1 \<in> nodes M2 \<and> p2 \<in> nodes M1  \<and> (x \<in> inputs M2) \<and> (y \<in> outputs M2 \<union> outputs M1))"
      then have "succ PM (x,y) (p1,p2) = {}" using assms(3) by auto
      then show "False" using execute by auto
    qed
      
    show ?thesis proof (cases "(succ M2 (x,y) p1 = {} \<and> succ M1 (x,y) p2 \<noteq> {})")
      case True 
      then have "q = FAIL" using subnodes assms(3) execute by auto
      then show ?thesis by auto
    next
      case False 
      then have "succ PM (fst a) p = succ M2 (x,y) p1 \<times> succ M1 (x,y) p2" using subnodes assms(3) execute by auto
      then have "q \<in> (succ M2 (x,y) p1 \<times> succ M1 (x,y) p2)" using execute by blast
      then have q_succ : "(q1,q2) \<in> (succ M2 (x,y) p1 \<times> succ M1 (x,y) p2)" by simp

      have "q1 \<in> succ M2 (x,y) p1" using q_succ by simp
      then have "q1 \<in> successors M2 p1" by auto
      then have "q1 \<in> reachable M2 p1" by blast 
      then have "q1 \<in> reachable M2 (initial M2)" using subnodes by blast 
      then have nodes1 : "q1 \<in> nodes M2" by blast

      have "q2 \<in> succ M1 (x,y) p2" using q_succ by simp
      then have "q2 \<in> successors M1 p2" by auto
      then have "q2 \<in> reachable M1 p2" by blast 
      then have "q2 \<in> reachable M1 (initial M1)" using subnodes by blast 
      then have nodes2 : "q2 \<in> nodes M1" by blast

      show ?thesis using nodes1 nodes2 by auto
    qed
  qed
qed




lemma well_formed_productF :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "productF M2 M1 FAIL PM"
shows "well_formed PM"
unfolding well_formed.simps proof
  have "finite (nodes M1)" "finite (nodes M2)" using assms by auto
  then have "finite (insert FAIL (nodes M2 \<times> nodes M1))" by simp
  moreover have "nodes PM \<subseteq> insert FAIL (nodes M2 \<times> nodes M1)" using nodes_productF assms by blast
  ultimately show "finite_FSM PM" using infinite_subset by auto  
next
  have "inputs PM = inputs M2" "outputs PM = outputs M2 \<union> outputs M1" using assms by auto
  then show "\<forall>s1 x y. x \<notin> inputs PM \<or> y \<notin> outputs PM \<longrightarrow> succ PM (x, y) s1 = {}" using assms by auto
qed
  


lemma fail_reachable :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"
  and     "observable M1"
  and     "observable M2"
  and "productF M2 M1 FAIL PM"
shows "FAIL \<in> reachable PM (initial PM)"
proof -
  let ?diff = "{ io . io \<in> language_state M1 (initial M1) \<and> io \<notin> language_state M2 (initial M2)}"
  have "?diff \<noteq> empty" using assms by auto
  moreover  obtain io where io_def[simp] : "io = arg_min length (\<lambda> io . io \<in> ?diff)" using assms by auto
  ultimately have io_diff : "io \<in> ?diff" using assms by (meson all_not_in_conv arg_min_natI) 

  then have "io \<noteq> []" using assms io_def using language_state by auto 
  then obtain io_init io_last where io_split[simp] : "io = io_init @ [io_last]" using list.exhaust by blast 

  have io_init_inclusion : "io_init \<in> language_state M1 (initial M1) \<and> io_init \<in> language_state M2 (initial M2)"
  proof (rule ccontr)
    assume assm : "\<not> (io_init \<in> language_state M1 (initial M1) \<and> io_init \<in> language_state M2 (initial M2))"

    have "io_init @ [io_last] \<in> language_state M1 (initial M1)" using io_diff io_split by auto
    then have "io_init \<in> language_state M1 (initial M1)" by (meson language_state language_state_split) 
    moreover have "io_init \<notin> language_state M2 (initial M2)" using assm calculation by auto
    ultimately have "io_init \<in> ?diff" by auto 
    moreover have "length io_init < length io" using io_split by auto 
    ultimately have "io \<noteq> arg_min length (\<lambda> io . io \<in> ?diff)"
    proof -
      have "\<exists>ps. ps \<in> {ps \<in> language_state M1 (initial M1). ps \<notin> language_state M2 (initial M2)} \<and> \<not> length io \<le> length ps"
        using \<open>io_init \<in> {io \<in> language_state M1 (initial M1). io \<notin> language_state M2 (initial M2)}\<close> \<open>length io_init < length io\<close> linorder_not_less by blast
      then show ?thesis
        by (meson arg_min_nat_le)
    qed
    then show "False" using io_def by simp
  qed

  then obtain tr1 tr2 where tr_def : "path M1 (io_init || tr1) (initial M1)" "length tr1 = length io_init"
                                     "path M2 (io_init || tr2) (initial M2)" "length tr2 = length io_init" by fastforce  
  then have paths_init : "path PM (io_init || tr2 || tr1) (initial PM)" using productF_path[of io_init tr2 tr1 M2 M1 FAIL PM "initial M2" "initial M1"] assms by auto
  let ?t1 = "target (io_init || tr1) (initial M1)"
  let ?t2 = "target (io_init || tr2) (initial M2)"
  have targets_init : "(?t2,?t1) = target (io_init || tr2 || tr1) (initial PM)" using assms(6) tr_def(2) tr_def(4) by force 

  have succ_last_2 : "succ M2 io_last ?t2 = {}" 
  proof (rule ccontr)
    assume "succ M2 io_last ?t2 \<noteq> {}"
    then obtain t2x where t1x_def : "t2x \<in> succ M2 io_last ?t2" by auto
    then have path2x : "path M2 (io_init @ [io_last] || tr2 @ [t2x]) (initial M2)"
    proof -
      have "initial PM = (initial M2, initial M1)" using assms(6) productF_simps(4) by blast
      moreover have "length tr2 = length tr1" by (metis tr_def(2) tr_def(4))
      moreover have "path M2 ([io_last] || [t2x]) ?t2" using t1x_def by auto
      ultimately show ?thesis by (metis (no_types) FSM.path_append tr_def(3) tr_def(4) zip_append)
    qed 
    then have "io_init @ [io_last] \<in> language_state M2 (initial M2)" unfolding language_state_def
    proof -
      have "length [io_last] = length [t2x]" by auto
      then have "\<exists>ps. io_init @ [io_last] = map fst ps \<and> path M2 ps (initial M2)" by (metis (no_types) path2x map_append map_fst_zip tr_def(4) zip_append)
      then show "io_init @ [io_last] \<in> {map fst ps |ps. path M2 ps (initial M2)}" by blast
    qed 
    then show "False" using io_split io_diff by auto 
  qed

  have succ_last_1 : "succ M1 io_last ?t1 \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> (succ M1 io_last ?t1 \<noteq> {})"
    then have assm : "succ M1 io_last ?t1 = {}" by simp
    then have no_trans : "\<not> (\<exists> tr1_last . path M1 ([io_last] || [tr1_last]) ?t1)" by auto
    

    have "io_init @ [io_last] \<in> language_state M1 (initial M1)" using io_diff io_split by auto
    then obtain tr1' tr1_last where tr1_last_def : "path M1 (io_init @ [io_last] || tr1' @ [tr1_last]) (initial M1)" "length (tr1' @ [tr1_last]) = length (io_init @ [io_last])"
      by (metis append_Nil append_butlast_last_id append_is_Nil_conv language_state_elim language_state_split not_Cons_self2 zip.simps(1) zip_Nil zip_eq)
    then have "tr1' = tr1" using assms(4) io_init_inclusion tr1_last_def(1) tr1_last_def(2) tr_def(1) tr_def(2) by auto
    then have "path M1 (io_init @ [io_last] || tr1 @ [tr1_last]) (initial M1)" using tr1_last_def by auto
    then have "path M1 ([io_last] || [tr1_last]) ?t1" using targets_init using tr_def by auto 
    then show "False" using no_trans by simp
  qed

  then have "fst io_last \<in> inputs M1 \<and> snd io_last \<in> outputs M1" by (metis assms(2) prod.exhaust_sel well_formed.simps) 
  then have "fst io_last \<in> inputs M2 \<and> snd io_last \<in> outputs M1" using assms by auto
  moreover have "?t2 \<in> nodes M2" "?t1 \<in> nodes M1" using tr_def by auto

  ultimately have "FAIL \<in> succ PM io_last (?t2,?t1)" using assms succ_last_2 succ_last_1 by auto

  then show ?thesis
    by (metis FSM.nodes.initial FSM.nodes_target FSM.nodes_target_elim FSM.reachable.reflexive FSM.reachable_target paths_init succ_nodes targets_init) 
qed

lemma fail_reachable_ob :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"
  and     "observable M1"
  and     "observable M2"
  and "productF M2 M1 FAIL PM"
obtains p
where "path PM p (initial PM)" "target p (initial PM) = FAIL"
using assms fail_reachable by (metis FSM.reachable_target_elim) 




lemma no_transition_after_FAIL :
  assumes "productF A B FAIL AB"
  shows "succ AB io FAIL = {}"
  using assms by auto

lemma no_prefix_targets_FAIL :
  assumes "productF M2 M1 FAIL PM"
  and     "path PM p q"
  and     "k < length p"
shows "target (take k p) q \<noteq> FAIL"
proof 
  assume assm : "target (take k p) q = FAIL"
  have "path PM (take k p @ drop k p) q" using assms by auto
  then have "path PM (drop k p) (target (take k p) q)" by blast
  then have path_from_FAIL : "path PM (drop k p) FAIL" using assm by auto
  
  have "length (drop k p) \<noteq> 0" using assms by auto
  then obtain io q where "drop k p = (io,q) # (drop (Suc k) p)" by (metis Cons_nth_drop_Suc assms(3) prod_cases3) 
  then have "succ PM io FAIL \<noteq> {}" using path_from_FAIL by auto 

  then show "False" using no_transition_after_FAIL assms by auto
qed




lemma productF_path_rev :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "path AB (w || r1 || r2) (p1, p2)"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "target (w || r1 || r2) (p1, p2) = FAIL \<or> path A (w || r1) p1 \<and> path B (w || r2) p2"
using assms  proof (induction w r1 r2 arbitrary: p1 p2 rule: list_induct3)
  case Nil
  then show ?case by auto
next
  case (Cons w ws r1 r1s r2 r2s) 
  show ?case proof (cases "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL")
    case True
    then show ?thesis by auto
  next
    case False

    then have path_head : "path AB ([w] || [(r1,r2)]) (p1,p2)" using Cons by auto
    then have succ_nonempty : "succ AB w (p1,p2) \<noteq> {}" by force
    then have succ_if_1 : "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B)" using Cons by auto

    have no_FAIL_next : "(r1,r2) \<noteq> FAIL"
    proof (cases "length ws")
      case 0
      show ?thesis 
      proof (rule ccontr)
        assume "\<not> ((r1,r2) \<noteq> FAIL)"
        then show "False" using False 0 by auto
      qed
    next
      case (Suc nat)
      then have "1 < length (w # ws || r1 # r1s || r2 # r2s)" using Cons by auto
      then have "target (take 1 (w # ws || r1 # r1s || r2 # r2s)) (p1,p2) \<noteq> FAIL" using no_prefix_targets_FAIL[of A B FAIL AB "(w # ws || r1 # r1s || r2 # r2s)" "(p1,p2)" 1 ] Cons.prems(1) Cons.prems(4) by auto
      then show ?thesis by auto
    qed
    moreover have "(r1,r2) \<in> succ AB w (p1,p2)" using path_head by auto

    ultimately have succ_not_fail : "succ AB w (p1,p2) \<noteq> {FAIL}" using succ_nonempty by auto

    have "\<not> (succ A w p1 = {} \<and> succ B w p2 \<noteq> {})" 
    proof (rule ccontr)
      assume "\<not> \<not> (succ A w p1 = {} \<and> succ B w p2 \<noteq> {})"
      then have "succ AB w (p1,p2) = {FAIL}" using succ_if_1 Cons by auto
      then show "False" using succ_not_fail by simp
    qed

    then have "succ AB w (p1,p2) = (succ A w p1 \<times> succ B w p2)" using succ_if_1 Cons by auto
    then have "(r1,r2) \<in> (succ A w p1 \<times> succ B w p2)" using Cons by auto
    then have succs_next : "r1 \<in> succ A w p1 \<and> r2 \<in> succ B w p2" by auto
    
    then have nodes_next : "r1 \<in> nodes A \<and> r2 \<in> nodes B" using Cons succ_nodes by metis
    moreover have path_tail : "path AB (ws || r1s || r2s) (r1,r2)" using Cons by auto
    ultimately have "target (ws || r1s || r2s) (r1, r2) = FAIL \<or> path A (ws || r1s) r1 \<and> path B (ws || r2s) r2" using Cons.IH Cons.prems by auto

    moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
    ultimately show ?thesis using path_head path_tail by auto  
  qed
qed

lemma butlast_zip_cons : "length ws = length r1s \<Longrightarrow> ws \<noteq> [] \<Longrightarrow> butlast (w # ws || r1 # r1s) = ((w,r1) # (butlast (ws || r1s)))"
proof -
assume a1: "length ws = length r1s"
assume a2: "ws \<noteq> []"
  have "length (w # ws) = length r1s + Suc 0"
    using a1 by (metis list.size(4))
  then have f3: "length (w # ws) = length (r1 # r1s)"
    by (metis list.size(4))
  have f4: "ws @ w # ws \<noteq> w # ws"
    using a2 by (meson append_self_conv2)
  have "length (ws @ w # ws) = length (r1s @ r1 # r1s)"
    using a1 by auto
  then have "ws @ w # ws || r1s @ r1 # r1s \<noteq> w # ws || r1 # r1s"
    using f4 f3 by (meson zip_eq)
  then show ?thesis
    using a1 by simp
qed
  

lemma productF_path_rev :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "path AB (w || r1 || r2) (p1, p2)"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "(path A (w || r1) p1 \<and> path B (w || r2) p2) 
           \<or> ((\<exists> r2' . (path B (w || r2') p2) \<and> length w = length r2') 
              \<and> target (w || r1 || r2) (p1, p2) = FAIL 
              \<and> (length w > 0 \<longrightarrow> path A (butlast (w || r1)) p1))"
using assms  proof (induction w r1 r2 arbitrary: p1 p2 rule: list_induct3)
  case Nil
  then show ?case by auto
next
  case (Cons w ws r1 r1s r2 r2s) 

  have path_head : "path AB ([w] || [(r1,r2)]) (p1,p2)" using Cons by auto
  then have succ_nonempty : "succ AB w (p1,p2) \<noteq> {}" by force
  then have succ_if_1 : "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B)" using Cons by auto

  show ?case proof (cases "(r1,r2) = FAIL")
    case False

    have "(r1,r2) \<in> succ AB w (p1,p2)" using path_head by auto
    then have succ_not_fail : "succ AB w (p1,p2) \<noteq> {FAIL}" using succ_nonempty False by auto

    have "\<not> (succ A w p1 = {} \<and> succ B w p2 \<noteq> {})" 
    proof (rule ccontr)
      assume "\<not> \<not> (succ A w p1 = {} \<and> succ B w p2 \<noteq> {})"
      then have "succ AB w (p1,p2) = {FAIL}" using succ_if_1 Cons by auto
      then show "False" using succ_not_fail by simp
    qed

    then have "succ AB w (p1,p2) = (succ A w p1 \<times> succ B w p2)" using succ_if_1 Cons by auto
    then have "(r1,r2) \<in> (succ A w p1 \<times> succ B w p2)" using Cons by auto
    then have succs_next : "r1 \<in> succ A w p1 \<and> r2 \<in> succ B w p2" by auto
    then have nodes_next : "r1 \<in> nodes A \<and> r2 \<in> nodes B" using Cons succ_nodes by metis     

    moreover have path_tail : "path AB (ws || r1s || r2s) (r1,r2)" using Cons by auto
    ultimately have prop_tail : "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2 \<or>
        ((\<exists> r2s' . (path B (ws || r2s') r2) \<and> length ws = length r2s')  \<and> target (ws || r1s || r2s) (r1, r2) = FAIL \<and> (length ws > 0 \<longrightarrow> path A (butlast (ws || r1s)) r1))" using Cons.IH Cons.prems by auto

    moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
    then show ?thesis
    proof (cases "(\<exists> r2s' . (path B (ws || r2s') r2) \<and> length ws = length r2s')  \<and> target (ws || r1s || r2s) (r1, r2) = FAIL \<and> (length ws > 0 \<longrightarrow> path A (butlast (ws || r1s)) r1)")
      case True 
      then obtain r2s' where "(path B (ws || r2s') r2) \<and> length ws = length r2s'" by auto
      moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
      moreover have "length ws = length r1s" using Cons by auto
      moreover have "length ws > 0 \<longrightarrow> butlast (w # ws || r1 # r1s) = ((w,r1) # (butlast (ws || r1s)))" by (metis (no_types) butlast_zip_cons calculation(3) less_nat_zero_code list.size(3))
      ultimately have "(path B (w # ws || r2 # r2s') p2 \<and> length (w # ws) = length (r2 # r2s')) \<and>
          target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL \<and>
          (0 < length (w # ws) \<longrightarrow> path A (butlast (w # ws || r1 # r1s)) p1)" using True by auto

      then show ?thesis by blast 
    next
      case False
      then have "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2" using prop_tail by auto
      moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
      ultimately show ?thesis by auto
    qed

  next
    case True
    then show ?thesis 
    proof (cases "length ws")
      case 0
      then have empty[simp] : "ws = []" "r1s = []" "r2s = []" using Cons.hyps by auto
      then have tgt_fail : "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL" using True Cons by auto
      moreover have path_AB : "path AB (w # ws || r1 # r1s || r2 # r2s) (p1, p2)" using Cons by simp
      moreover have "(r1,r2) = FAIL" using calculation by auto
      moreover have "(r1,r2) \<in> succ AB w (p1,p2)" using calculation by auto
      ultimately have "FAIL \<in> succ AB w (p1,p2)" by auto

   
      then have "succ B w p2 \<noteq> {}" using Cons succ_if_1 by auto
      then obtain r2' where r2'_def : "r2' \<in> succ B w p2" by auto
      then have "path B (w # ws || r2' # r2s) p2" using empty path_AB by auto
      then show ?thesis by (metis FSM.nil butlast.simps(2) empty(1) length_Cons list.size(3) tgt_fail zip_Cons_Cons zip_Nil)      
    next
      case (Suc nat)
      then have "target (take 1 (w # ws || r1 # r1s || r2 # r2s)) (p1, p2) \<noteq> FAIL" using Cons no_prefix_targets_FAIL[of A B FAIL AB "(w # ws || r1 # r1s || r2 # r2s)" "(p1,p2)" 1] by auto
      moreover have "(r1,r2) = target (take 1 (w # ws || r1 # r1s || r2 # r2s)) (p1, p2)" by auto
      ultimately show ?thesis by (simp add: True)
    qed
  qed
qed













  show ?case proof (cases "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL")
    case False

    have path_head : "path AB ([w] || [(r1,r2)]) (p1,p2)" using Cons by auto
    then have "succ AB w (p1,p2) \<noteq> {}" by force
    then have succ_if_1 : "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B)" using Cons by auto

    moreover have no_FAIL_next : "(r1,r2) \<noteq> FAIL"
    proof (cases "length ws")
      case 0
      show ?thesis 
      proof (rule ccontr)
        assume "\<not> ((r1,r2) \<noteq> FAIL)"
        then show "False" using False 0 by auto
      qed
    next
      case (Suc nat)
      then have "1 < length (w # ws || r1 # r1s || r2 # r2s)" using Cons by auto
      then have "target (take 1 (w # ws || r1 # r1s || r2 # r2s)) (p1,p2) \<noteq> FAIL" using no_prefix_targets_FAIL[of A B FAIL AB "(w # ws || r1 # r1s || r2 # r2s)" "(p1,p2)" 1 ] Cons.prems(1) Cons.prems(4) by auto
      then show ?thesis by auto
    qed

    ultimately have succ_if_2 : "succ A w p1 \<noteq> {}" using Cons by auto

    then have "succ AB w (p1,p2) = (succ A w p1 \<times> succ B w p2)" using succ_if_1 Cons by auto
    then have "(r1,r2) \<in> (succ A w p1 \<times> succ B w p2)" using Cons by auto
    then have succs_next : "r1 \<in> succ A w p1 \<and> r2 \<in> succ B w p2" by auto
    then have nodes_next : "r1 \<in> nodes A \<and> r2 \<in> nodes B" using Cons succ_nodes by metis 
    

    moreover have path_tail : "path AB (ws || r1s || r2s) (r1,r2)" using Cons by auto
    ultimately have prop_tail : "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2 \<or>
        path B (ws || r2s) r2 \<and> target (ws || r1s || r2s) (r1, r2) = FAIL \<and> path A (butlast (ws || r1s)) r1" using Cons.IH Cons.prems by auto

    moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
    then show ?thesis
    proof (cases "path B (ws || r2s) r2 \<and> target (ws || r1s || r2s) (r1, r2) = FAIL \<and> path A (butlast (ws || r1s)) r1")
      case True 
      moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
      moreover have "length ws = length r1s" using Cons by auto
      moreover have "ws \<noteq> [] \<Longrightarrow> butlast (w # ws || r1 # r1s) = ((w,r1) # (butlast (ws || r1s)))" using Cons calculation butlast_zip_cons by metis
      ultimately show ?thesis by auto
    next
      case False
      then have "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2" using prop_tail by auto
      moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
      ultimately show ?thesis by auto
    qed

  next
    case True
    then show ?thesis using Cons.IH



end (*


lemma productF_path_impl :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "path AB (w || r1 || r2) (p1, p2) \<longleftrightarrow> (   
           (path A (w || r1) p1 \<and> path B (w || r2) p2) 
           \<or> (path B (w || r2) p2 
              \<and> target (w || r1 || r2) (p1, p2) = FAIL 
              \<and> path A (take (length w - 1) (w || r1)) p1))"

lemma productF_path :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "target (w || r1 || r2) (p1, p2) = FAIL"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "path (AB) (w || r1 || r2) (p1, p2)"

(*
lemma product_target[simp]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "target (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) = (target (w || r\<^sub>1) p\<^sub>1, target (w || r\<^sub>2) p\<^sub>2)"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)

lemma product_path[iff]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "path (product A B) (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) \<longleftrightarrow> path A (w || r\<^sub>1) p\<^sub>1 \<and> path B (w || r\<^sub>2) p\<^sub>2"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)

lemma product_language_state[simp]: "language_state (product A B) (q1,q2) = language_state A q1 \<inter> language_state B q2"
  by (fastforce iff: split_zip)
*)


lemma productF_language_state_dist:  
  assumes "(io_init @ [io_tail]) \<in> language_state AB (q1,q2)"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "observable A"
  and     "observable B"
shows "io_init \<in> (language_state A q1 \<inter> language_state B q2)" 


end