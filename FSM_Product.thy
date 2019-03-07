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




lemma well_formed_productF[simp] :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "productF M2 M1 FAIL PM"
shows "well_formed PM"
unfolding well_formed.simps proof
  have "finite (nodes M1)" "finite (nodes M2)" using assms by auto
  then have "finite (insert FAIL (nodes M2 \<times> nodes M1))" by simp
  moreover have "nodes PM \<subseteq> insert FAIL (nodes M2 \<times> nodes M1)" using nodes_productF assms by blast
  moreover have "inputs PM = inputs M2" "outputs PM = outputs M2 \<union> outputs M1" using assms by auto
  ultimately show "finite_FSM PM" using infinite_subset assms by auto  
next
  have "inputs PM = inputs M2" "outputs PM = outputs M2 \<union> outputs M1" using assms by auto
  then show "\<forall>s1 x y. x \<notin> inputs PM \<or> y \<notin> outputs PM \<longrightarrow> succ PM (x, y) s1 = {}" using assms by auto
qed

lemma observable_productF[simp] : 
  assumes "observable M1"
  and     "observable M2"
  and     "productF M2 M1 FAIL PM"
shows "observable PM"
  unfolding observable.simps
proof -
  have "\<forall> t s . succ M1 t (fst s) = {} \<or> (\<exists>s2. succ M1 t (fst s) = {s2})" using assms by auto
  moreover have "\<forall> t s . succ M2 t (snd s) = {} \<or> (\<exists>s2. succ M2 t (snd s) = {s2})" using assms by auto
  ultimately have sub_succs : "\<forall> t s . succ M2 t (fst s) \<times> succ M1 t (snd s) = {} \<or> (\<exists> s2 . succ M2 t (fst s) \<times> succ M1 t (snd s) = {s2})" by fastforce
  moreover have succ_split : "\<forall> t s . succ PM t s = {} \<or> succ PM t s = {FAIL} \<or> succ PM t s = succ M2 t (fst s) \<times> succ M1 t (snd s)" using assms by auto
  ultimately show "\<forall>t s. succ PM t s = {} \<or> (\<exists>s2. succ PM t s = {s2})" by metis 
qed
  





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


lemma productF_path_inclusion :
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

lemma productF_path_forward :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "(path A (w || r1) p1 \<and> path B (w || r2) p2) 
            \<or> (target (w || r1 || r2) (p1, p2) = FAIL
              \<and> length w > 0
              \<and> path A (butlast (w || r1)) p1
              \<and> path B (butlast (w || r2)) p2
              \<and> succ A (last w) (target (butlast (w || r1)) p1) = {}
              \<and> succ B (last w) (target (butlast (w || r2)) p2) \<noteq> {})"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "path (AB) (w || r1 || r2) (p1, p2)"
using assms  proof (induction w r1 r2 arbitrary: p1 p2 rule: list_induct3)
  case Nil
  then show ?case by auto
next
  case (Cons w ws r1 r1s r2 r2s) 
  then show ?case
  proof (cases "(path A (w # ws || r1 # r1s) p1 \<and> path B (w # ws || r2 # r2s) p2)")
    case True
    then show ?thesis using Cons productF_path_inclusion[of "w # ws" "r1 # r1s" "r2 # r2s" A B FAIL AB p1 p2] by auto 
  next
    case False
    then have fail_prop : "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL \<and>
                0 < length (w # ws) \<and>
                path A (butlast (w # ws || r1 # r1s)) p1 \<and>
                path B (butlast (w # ws || r2 # r2s)) p2 \<and>
                succ A (last (w # ws)) (target (butlast (w # ws || r1 # r1s)) p1) = {} \<and>
                succ B (last (w # ws)) (target (butlast (w # ws || r2 # r2s)) p2) \<noteq> {}" using Cons.prems by fastforce
    

    then show ?thesis 
    proof (cases "length ws")
      case 0
      then have empty[simp] : "ws = []" "r1s = []" "r2s = []" using Cons.hyps by auto
      then have fail_prop_0 : "target ( [w] || [r1] || [r2]) (p1, p2) = FAIL \<and>
                0 < length ([w]) \<and>
                path A [] p1 \<and>
                path B [] p2 \<and>
                succ A w p1 = {} \<and>
                succ B w p2 \<noteq> {}" using fail_prop by auto
      then have "fst w \<in> inputs B \<and> snd w \<in> outputs B" using Cons.prems by (metis prod.collapse well_formed.elims(2))
      then have inputs_0 : "fst w \<in> inputs A \<and> snd w \<in> outputs B" using Cons.prems by auto
      
      moreover have fail_elems_0 : "(r1,r2) = FAIL" using fail_prop by auto
      ultimately have "succ AB w (p1,p2) = {FAIL}" using fail_prop_0 Cons.prems by auto

      then have "path AB ( [w] || [r1] || [r2]) (p1, p2)" using Cons.prems fail_elems_0 by auto
      then show ?thesis by auto
    next
      case (Suc nat)
      
      then have path_r1 : "path A ([w] || [r1]) p1" using fail_prop by (metis Cons.hyps(1) FSM.nil FSM.path.intros(2) FSM.path_cons_elim Suc_neq_Zero butlast.simps(2) length_0_conv zip_Cons_Cons zip_Nil zip_eq)
      then have path_r1s : "path A (butlast (ws || r1s)) r1" using Suc
        by (metis (no_types, lifting) Cons.hyps(1) FSM.path_cons_elim Suc_neq_Zero butlast.simps(2) fail_prop length_0_conv snd_conv zip.simps(1) zip_Cons_Cons zip_eq) 
      
      have path_r2 : "path B ([w] || [r2]) p2" using Suc fail_prop by (metis Cons.hyps(1) Cons.hyps(2) FSM.nil FSM.path.intros(2) FSM.path_cons_elim Suc_neq_Zero butlast.simps(2) length_0_conv zip_Cons_Cons zip_Nil zip_eq)
      then have path_r2s : "path B (butlast (ws || r2s)) r2" using Suc
        by (metis (no_types, lifting) Cons.hyps(1) Cons.hyps(2) FSM.path_cons_elim Suc_neq_Zero butlast.simps(2) fail_prop length_0_conv snd_conv zip.simps(1) zip_Cons_Cons zip_eq)

      have "target (ws || r1s || r2s) (r1, r2) = FAIL" using fail_prop by auto
      moreover have "r1 \<in> nodes A" using Cons.prems path_r1 by (metis FSM.path_cons_elim snd_conv succ_nodes zip_Cons_Cons)
      moreover have "r2 \<in> nodes B" using Cons.prems path_r2 by (metis FSM.path_cons_elim snd_conv succ_nodes zip_Cons_Cons)
      moreover have "succ A (last ws) (target (butlast (ws || r1s)) r1) = {}" by (metis (no_types, lifting) Cons.hyps(1) Suc Suc_neq_Zero butlast.simps(2) fail_prop fold_simps(2) last_ConsR list.size(3) snd_conv zip_Cons_Cons zip_Nil zip_eq) 
      moreover have "succ B (last ws) (target (butlast (ws || r2s)) r2) \<noteq> {}" by (metis (no_types, lifting) Cons.hyps(1) Cons.hyps(2) Suc Suc_neq_Zero butlast.simps(2) fail_prop fold_simps(2) last_ConsR list.size(3) snd_conv zip_Cons_Cons zip_Nil zip_eq)

      ultimately have "path AB (ws || r1s || r2s) (r1, r2)" using Suc \<open>\<lbrakk>productF A B FAIL AB; well_formed A; well_formed B; path A (ws || r1s) r1 \<and> path B (ws || r2s) r2 \<or> target (ws || r1s || r2s) (r1, r2) = FAIL \<and> 0 < length ws \<and> path A (butlast (ws || r1s)) r1 \<and> path B (butlast (ws || r2s)) r2 \<and> succ A (last ws) (target (butlast (ws || r1s)) r1) = {} \<and> succ B (last ws) (target (butlast (ws || r2s)) r2) \<noteq> {}; r1 \<in> nodes A; r2 \<in> nodes B\<rbrakk> \<Longrightarrow> path AB (ws || r1s || r2s) (r1, r2)\<close> \<open>r1 \<in> nodes A\<close> \<open>r2 \<in> nodes B\<close> \<open>succ A (last ws) (target (butlast (ws || r1s)) r1) = {}\<close> \<open>succ B (last ws) (target (butlast (ws || r2s)) r2) \<noteq> {}\<close> \<open>target (ws || r1s || r2s) (r1, r2) = FAIL\<close> assms(3) assms(4) assms(5) path_r1s path_r2s by linarith
      moreover have "path AB ([w] || [r1] || [r2]) (p1,p2)" using path_r1 path_r2 productF_path_inclusion[of "[w]" "[r1]" "[r2]" A B FAIL AB p1 p2] Cons.prems by auto
      ultimately show ?thesis by auto 
    qed 
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


lemma productF_succ_fail_imp : 
  assumes "productF A B FAIL AB"
  and     "FAIL \<in> succ AB w (p1,p2)"
  and     "well_formed A"
  and     "well_formed B"
shows "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B) \<and> succ AB w (p1,p2) = {FAIL} \<and> succ A w p1 = {} \<and> succ B w p2 \<noteq> {}" 
proof -
  have path_head : "path AB ([w] || [FAIL]) (p1,p2)" using assms by auto
  then have succ_nonempty : "succ AB w (p1,p2) \<noteq> {}" by force
  then have succ_if_1 : "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B)" using assms by auto
  then have "(p1,p2) \<noteq> FAIL" using assms by auto

 have "succ A w p1 \<subseteq> nodes A" using assms succ_if_1 by (simp add: subsetI succ_nodes) 
  moreover have "succ B w p2 \<subseteq> nodes B" using assms succ_if_1 by (simp add: subsetI succ_nodes)
  ultimately have "FAIL \<notin> (succ A w p1 \<times> succ B w p2)" using assms by auto
  then have succ_no_inclusion : "succ AB w (p1,p2) \<noteq> (succ A w p1 \<times> succ B w p2)" using assms succ_if_1 by blast 
  moreover have "succ AB w (p1,p2) = {} \<or> succ AB w (p1,p2) = {FAIL} \<or> succ AB w (p1,p2) = (succ A w p1 \<times> succ B w p2)" using assms by simp
  ultimately have succ_fail : "succ AB w (p1,p2) = {FAIL}" using succ_nonempty by simp

  have "succ A w p1 = {} \<and> succ B w p2 \<noteq> {}"
  proof (rule ccontr)
    assume "\<not> (succ A w p1 = {} \<and> succ B w p2 \<noteq> {})"
    then have "succ AB w (p1,p2) = (succ A w p1 \<times> succ B w p2)" using assms by auto
    then show "False" using succ_no_inclusion by simp
  qed
  
  then show ?thesis using succ_if_1 succ_fail by simp
qed
  


lemma productF_path_reverse :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "path AB (w || r1 || r2) (p1, p2)"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "(path A (w || r1) p1 \<and> path B (w || r2) p2) 
            \<or> (target (w || r1 || r2) (p1, p2) = FAIL
              \<and> length w > 0
              \<and> path A (butlast (w || r1)) p1
              \<and> path B (butlast (w || r2)) p2
              \<and> succ A (last w) (target (butlast (w || r1)) p1) = {}
              \<and> succ B (last w) (target (butlast (w || r2)) p2) \<noteq> {})"
using assms  proof (induction w r1 r2 arbitrary: p1 p2 rule: list_induct3)
  case Nil
  then show ?case by auto
next
  case (Cons w ws r1 r1s r2 r2s) 

  have path_head : "path AB ([w] || [(r1,r2)]) (p1,p2)" using Cons by auto
  then have succ_nonempty : "succ AB w (p1,p2) \<noteq> {}" by force
  then have succ_if_1 : "p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst w \<in> inputs A) \<and> (snd w \<in> outputs A \<union> outputs B)" using Cons by auto
  then have "(p1,p2) \<noteq> FAIL" using Cons by auto

  have path_tail : "path AB (ws || r1s || r2s) (r1,r2)" using path_head Cons  by auto
  
  show ?case 
  proof (cases "(r1,r2) = FAIL")
    case True
    have "r1s = []"
    proof (rule ccontr)
      assume "\<not> (r1s = [])"
      then have "(\<not> (ws = [])) \<and> (\<not> (r1s = [])) \<and> (\<not> (r2s = []))" using Cons.hyps by auto
      moreover have "path AB (ws || r1s || r2s) FAIL" using True path_tail by simp
      ultimately have "path AB ([hd ws] @ tl ws || [hd r1s] @ tl r1s || [hd r2s] @ tl r2s) FAIL" by simp
      then have "path AB ([hd ws] || [hd r1s] || [hd r2s]) FAIL" by auto
      then have "succ AB (hd ws) FAIL \<noteq> {}" by auto
      then show "False" using no_transition_after_FAIL using Cons.prems by auto
    qed
    then have tail_nil : "ws = [] \<and> r1s = [] \<and> r2s = []" using Cons.hyps by simp

    have succ_fail : "FAIL \<in> succ AB w (p1,p2)" using path_head True by auto

    then have succs : "succ A w p1 = {} \<and> succ B w p2 \<noteq> {}" using Cons.prems by (meson productF_succ_fail_imp)

    have  "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL" using True tail_nil by simp
    moreover have "0 < length (w # ws)" by simp
    moreover have "path A (butlast (w # ws || r1 # r1s)) p1" using tail_nil by auto
    moreover have "path B (butlast (w # ws || r2 # r2s)) p2" using tail_nil by auto
    moreover have "succ A (last (w # ws)) (target (butlast (w # ws || r1 # r1s)) p1) = {}" using succs tail_nil by simp 
    moreover have "succ B (last (w # ws)) (target (butlast (w # ws || r2 # r2s)) p2) \<noteq> {}" using succs tail_nil by simp

    ultimately show ?thesis by simp
  next
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
    ultimately have prop_tail : 
        "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2 \<or>
            target (ws || r1s || r2s) (r1, r2) = FAIL \<and>
            0 < length ws \<and>
            path A (butlast (ws || r1s)) r1 \<and>
            path B (butlast (ws || r2s)) r2 \<and>
            succ A (last ws) (target (butlast (ws || r1s)) r1) = {} \<and>
            succ B (last ws) (target (butlast (ws || r2s)) r2) \<noteq> {}" using Cons.IH[of r1 r2] Cons.prems by auto

    moreover have "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
    then show ?thesis
    proof (cases "path A (ws || r1s) r1 \<and> path B (ws || r2s) r2")
      case True
      moreover have paths_head : "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto
      ultimately show ?thesis by (metis (no_types) FSM.path.simps FSM.path_cons_elim True eq_snd_iff paths_head zip_Cons_Cons)
    next
      case False

      then have fail_prop : "target (ws || r1s || r2s) (r1, r2) = FAIL \<and>
            0 < length ws \<and>
            path A (butlast (ws || r1s)) r1 \<and>
            path B (butlast (ws || r2s)) r2 \<and>
            succ A (last ws) (target (butlast (ws || r1s)) r1) = {} \<and>
            succ B (last ws) (target (butlast (ws || r2s)) r2) \<noteq> {}" using prop_tail by auto

      then have paths_head : "path A ([w] || [r1]) p1 \<and> path B ([w] || [r2]) p2" using succs_next by auto

      have "(last (w # ws)) = last ws" using fail_prop by simp
      moreover have "(target (butlast (w # ws || r1 # r1s)) p1) = (target (butlast (ws || r1s)) r1)" using fail_prop Cons.hyps(1) butlast_zip_cons by fastforce 
      moreover have "(target (butlast (w # ws || r2 # r2s)) p2) = (target (butlast (ws || r2s)) r2)" using fail_prop Cons.hyps(1) Cons.hyps(2) butlast_zip_cons by fastforce
      ultimately have "succ A (last (w # ws)) (target (butlast (w # ws || r1 # r1s)) p1) = {} \<and> succ B (last (w # ws)) (target (butlast (w # ws || r2 # r2s)) p2) \<noteq> {}" using fail_prop by auto
      moreover have "path A (butlast (w # ws || r1 # r1s)) p1" using fail_prop paths_head by auto
      moreover have "path B (butlast (w # ws || r2 # r2s)) p2" using fail_prop paths_head by auto
      moreover have "target (w # ws || r1 # r1s || r2 # r2s) (p1, p2) = FAIL" using fail_prop paths_head by auto
      ultimately show ?thesis by simp
    qed

  qed
qed

lemma butlast_zip[simp] :
  assumes "length xs = length ys"
  shows "butlast (xs || ys) = (butlast xs || butlast ys)"
  using assms by (metis (no_types, lifting) map_butlast map_fst_zip map_snd_zip zip_map_fst_snd) 



lemma productF_path_reverse_ob : 
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "path AB (w || r1 || r2) (p1, p2)"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
obtains r2' 
where "path B (w || r2') p2 \<and> length w = length r2'"
proof -
  have path_prop : "(path A (w || r1) p1 \<and> path B (w || r2) p2) 
                    \<or> (target (w || r1 || r2) (p1, p2) = FAIL
                      \<and> length w > 0
                      \<and> path A (butlast (w || r1)) p1
                      \<and> path B (butlast (w || r2)) p2
                      \<and> succ A (last w) (target (butlast (w || r1)) p1) = {}
                      \<and> succ B (last w) (target (butlast (w || r2)) p2) \<noteq> {})" using assms productF_path_reverse[of w r1 r2 A B FAIL AB p1 p2] by simp
  have "\<exists> r1' . path B (w || r1') p2 \<and> length w = length r1'"
  proof (cases "path A (w || r1) p1 \<and> path B (w || r2) p2")
    case True
    then show ?thesis using assms by auto
  next
    case False 
    then have B_prop : "length w > 0
                \<and> path B (butlast (w || r2)) p2
                \<and> succ B (last w) (target (butlast (w || r2)) p2) \<noteq> {}" using path_prop by auto
    then obtain rx where "rx \<in> succ B (last w) (target (butlast (w || r2)) p2)" by auto
    
    then have "path B ([last w] || [rx]) (target (butlast (w || r2)) p2)" using B_prop by auto
    then have "path B ((butlast (w || r2)) @ ([last w] || [rx])) p2" using B_prop by auto
    moreover have "butlast (w || r2) = (butlast w || butlast r2)" using assms by simp 
    
    ultimately have "path B ((butlast w) @ [last w] || (butlast r2) @ [rx]) p2" using assms B_prop by auto
    moreover have "(butlast w) @ [last w] = w" using B_prop by simp
    moreover have "length ((butlast r2) @ [rx]) = length w" using assms B_prop by auto
    ultimately show ?thesis by auto
  qed
  then obtain r1' where "path B (w || r1') p2 \<and> length w = length r1'" by blast
  then show ?thesis using that by blast
qed
  



lemma productF_path[iff] :
  assumes "length w = length r1" "length r1 = length r2"
  and     "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "p1 \<in> nodes A"
  and     "p2 \<in> nodes B"
shows "path AB (w || r1 || r2) (p1, p2) \<longleftrightarrow> ((path A (w || r1) p1 \<and> path B (w || r2) p2) 
            \<or> (target (w || r1 || r2) (p1, p2) = FAIL
              \<and> length w > 0
              \<and> path A (butlast (w || r1)) p1
              \<and> path B (butlast (w || r2)) p2
              \<and> succ A (last w) (target (butlast (w || r1)) p1) = {}
              \<and> succ B (last w) (target (butlast (w || r2)) p2) \<noteq> {}))" (is "?path \<longleftrightarrow> ?paths")
proof 
  assume ?path
  then show ?paths using assms productF_path_reverse[of w r1 r2 A B FAIL AB p1 p2] by simp
next 
  assume ?paths
  then show ?path using assms productF_path_forward[of w r1 r2 A B FAIL AB p1 p2] by simp
qed





fun sequence_to_failure :: "('in,'out,'state) FSM \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "sequence_to_failure M1 M2 xs = (
    (butlast xs) \<in> (language_state M2 (initial M2) \<inter> language_state M1 (initial M1))
    \<and> xs \<in> (language_state M1 (initial M1) - language_state M2 (initial M2)))"

lemma fail_reachable_by_sequence_to_failure :
  assumes "sequence_to_failure M1 M2 io"
  and     "well_formed M1"
  and     "well_formed M2"
  and "productF M2 M1 FAIL PM"
obtains p
where "path PM (io || p) (initial PM) \<and> length p = length io \<and> target (io || p) (initial PM) = FAIL"
proof -
  have "io \<noteq> []" using assms by auto 
  then obtain io_init io_last where io_split[simp] : "io = io_init @ [io_last]" by (metis append_butlast_last_id) 
  have io_init_inclusion : "io_init \<in> language_state M1 (initial M1) \<and> io_init \<in> language_state M2 (initial M2)" using assms by auto

  have "io_init @ [io_last] \<in> language_state M1 (initial M1)" using assms by auto
  then obtain tr1_init tr1_last where tr1_def : "path M1 (io_init @ [io_last] || tr1_init @ [tr1_last]) (initial M1) \<and> length (tr1_init @ [tr1_last]) = length (io_init @ [io_last])"
    by (metis append_butlast_last_id language_state_elim length_0_conv length_append_singleton nat.simps(3)) 
  
  then have path_init_1 : "path M1 (io_init || tr1_init) (initial M1) \<and> length tr1_init = length io_init" by auto
  then have "path M1 ([io_last] || [tr1_last]) (target (io_init || tr1_init) (initial M1))" using tr1_def by auto
  then have succ_1 : "succ M1 io_last (target (io_init || tr1_init) (initial M1)) \<noteq> {}" by auto

  obtain tr2 where tr2_def : "path M2 (io_init || tr2) (initial M2) \<and> length tr2 = length io_init" using io_init_inclusion by auto
  have succ_2 : "succ M2 io_last (target (io_init || tr2) (initial M2)) = {}" 
  proof (rule ccontr)
    assume "succ M2 io_last (target (io_init || tr2) (initial M2)) \<noteq> {}"
    then obtain tr2_last where "tr2_last \<in> succ M2 io_last (target (io_init || tr2) (initial M2))" by auto
    then have "path M2 ([io_last] || [tr2_last]) (target (io_init || tr2) (initial M2))" by auto
    then have "io_init @ [io_last] \<in> language_state M2 (initial M2)" by (metis FSM.path_append language_state length_Cons length_append list.size(3) tr2_def zip_append) 
    then show "False" using assms io_split by simp
  qed

  have fail_lengths : "length (io_init @ [io_last]) = length (tr2 @ [fst FAIL]) \<and> length (tr2 @ [fst FAIL]) = length (tr1_init @ [snd FAIL])" using assms tr2_def tr1_def by auto
  then have fail_tgt : "target (io_init @ [io_last] || tr2 @ [fst FAIL] || tr1_init @ [snd FAIL]) (initial M2, initial M1) = FAIL" by auto

  have fail_butlast_simp[simp] : "butlast (io_init @ [io_last] || tr2 @ [fst FAIL]) = io_init || tr2" "butlast (io_init @ [io_last] || tr1_init @ [snd FAIL]) = io_init || tr1_init" using fail_lengths by simp+

  have "path M2 (butlast (io_init @ [io_last] || tr2 @ [fst FAIL])) (initial M2) \<and>
    path M1 (butlast (io_init @ [io_last] || tr1_init @ [snd FAIL])) (initial M1)" using tr1_def tr2_def by auto
  moreover have "succ M2 (last (io_init @ [io_last])) (target (butlast (io_init @ [io_last] || tr2 @ [fst FAIL])) (initial M2)) = {}" using succ_2 by simp
  moreover have "succ M1 (last (io_init @ [io_last])) (target (butlast (io_init @ [io_last] || tr1_init @ [snd FAIL])) (initial M1)) \<noteq> {}" using succ_1 by simp
  moreover have "initial M2 \<in> nodes M2 \<and> initial M1 \<in> nodes M1" by auto
  ultimately have "path PM (io_init @ [io_last] || tr2 @ [fst FAIL] || tr1_init @ [snd FAIL]) (initial M2, initial M1)" using fail_lengths fail_tgt assms path_init_1 tr2_def productF_path_forward[of "io_init @ [io_last]" "tr2 @ [fst FAIL]" "tr1_init @ [snd FAIL]" M2 M1 FAIL PM "initial M2" "initial M1" ] by simp

  moreover have "initial PM = (initial M2, initial M1)" using assms(4) productF_simps(4) by blast
 
  ultimately have "path PM (io_init @ [io_last] || tr2 @ [fst FAIL] || tr1_init @ [snd FAIL]) (initial PM)
   \<and> length (tr2 @ [fst FAIL] || tr1_init @ [snd FAIL]) = length (io_init @ [io_last])
   \<and> target (io_init @ [io_last] || tr2 @ [fst FAIL] || tr1_init @ [snd FAIL]) (initial PM) = FAIL" using fail_lengths fail_tgt by auto
  then show ?thesis using that using io_split by blast 
qed



lemma sequence_to_failure_ob :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"
  and "productF M2 M1 FAIL PM"
obtains io
where "sequence_to_failure M1 M2 io"
proof -
  let ?diff = "{ io . io \<in> language_state M1 (initial M1) \<and> io \<notin> language_state M2 (initial M2)}"
  have "?diff \<noteq> empty" using assms by auto
  moreover  obtain io where io_def[simp] : "io = arg_min length (\<lambda> io . io \<in> ?diff)" using assms by auto
  ultimately have io_diff : "io \<in> ?diff" using assms by (meson all_not_in_conv arg_min_natI) 

  then have "io \<noteq> []" using assms io_def using language_state by auto 
  then obtain io_init io_last where io_split[simp] : "io = io_init @ [io_last]" by (metis append_butlast_last_id) 

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

  then have "sequence_to_failure M1 M2 io" using io_split io_diff by auto
  then show ?thesis using that by auto  
qed





lemma fail_reachable :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"
  and "productF M2 M1 FAIL PM"
shows "FAIL \<in> reachable PM (initial PM)"
proof -
  obtain io where "sequence_to_failure M1 M2 io" using sequence_to_failure_ob assms by blast
  then show ?thesis using assms fail_reachable_by_sequence_to_failure[of M1 M2 io FAIL PM] by (metis FSM.reachable.reflexive FSM.reachable_target)  
qed


lemma fail_reachable_ob :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"
  and     "observable M2"
  and "productF M2 M1 FAIL PM"
obtains p
where "path PM p (initial PM)" "target p (initial PM) = FAIL"
using assms fail_reachable by (metis FSM.reachable_target_elim) 




lemma fail_reachable_reverse : 
  assumes "well_formed M1"
  and     "well_formed M2" 
  and     "productF M2 M1 FAIL PM"
  and     "FAIL \<in> reachable PM (initial PM)"
  and     "observable M2"
shows "\<not> M1 \<preceq> M2" 
proof -
  obtain pathF where pathF_def : "path PM pathF (initial PM) \<and> target pathF (initial PM) = FAIL" using assms by auto
  let ?io = "map fst pathF"
  let ?tr2 = "map fst (map snd pathF)"
  let ?tr1 = "map snd (map snd pathF)" 

  have "initial PM \<noteq> FAIL" using assms by auto
  then have "pathF \<noteq> []" using pathF_def by auto
  moreover have "initial PM = (initial M2, initial M1)" using assms by simp
  ultimately have "path M2 (?io || ?tr2) (initial M2) \<and> path M1 (?io || ?tr1) (initial M1) \<or>
    target (?io || ?tr2 || ?tr1) (initial M2, initial M1) = FAIL \<and>
    0 < length (?io) \<and>
    path M2 (butlast (?io || ?tr2)) (initial M2) \<and>
    path M1 (butlast (?io || ?tr1)) (initial M1) \<and>
    succ M2 (last (?io)) (target (butlast (?io || ?tr2)) (initial M2)) = {} \<and>
    succ M1 (last (?io)) (target (butlast (?io || ?tr1)) (initial M1)) \<noteq> {}" using productF_path_reverse[of ?io ?tr2 ?tr1 M2 M1 FAIL PM "initial M2" "initial M1"] using assms pathF_def
  proof -
    have f1: "path PM (?io || ?tr2 || ?tr1) (initial M2, initial M1)" by (metis (no_types) \<open>initial PM = (initial M2, initial M1)\<close> pathF_def zip_map_fst_snd)
    have f2: "length (?io) = length pathF \<longrightarrow> length (?io) = length (?tr2)" by auto
    have "length (?io) = length pathF \<and> length (?tr2) = length (?tr1)" by auto
    then show ?thesis using f2 f1 \<open>productF M2 M1 FAIL PM\<close> \<open>well_formed M1\<close> \<open>well_formed M2\<close> by blast
  qed
    
  moreover have "\<not> (path M2 (?io || ?tr2) (initial M2) \<and> path M1 (?io || ?tr1) (initial M1))" 
  proof (rule ccontr)
    assume " \<not> \<not> (path M2 (?io || ?tr2) (initial M2) \<and>
          path M1 (?io || ?tr1) (initial M1))"
    then have "path M2 (?io || ?tr2) (initial M2)" by simp
    then have "target (?io || ?tr2) (initial M2) \<in> nodes M2" by auto
    then have "target (?io || ?tr2) (initial M2) \<noteq> fst FAIL" using assms by auto
    then show "False" using pathF_def
    proof -
      have "FAIL = target (map fst pathF || map fst (map snd pathF) || map snd (map snd pathF)) (initial M2, initial M1)"
        by (metis (no_types) \<open>initial PM = (initial M2, initial M1)\<close> \<open>path PM pathF (initial PM) \<and> target pathF (initial PM) = FAIL\<close> zip_map_fst_snd)
      then show ?thesis
        using \<open>target (map fst pathF || map fst (map snd pathF)) (initial M2) \<noteq> fst FAIL\<close> by auto
    qed 
  qed

  ultimately have fail_prop : "target (?io || ?tr2 || ?tr1) (initial M2, initial M1) = FAIL \<and>
        0 < length (?io) \<and>
        path M2 (butlast (?io || ?tr2)) (initial M2) \<and>
        path M1 (butlast (?io || ?tr1)) (initial M1) \<and>
        succ M2 (last (?io)) (target (butlast (?io || ?tr2)) (initial M2)) = {} \<and>
        succ M1 (last (?io)) (target (butlast (?io || ?tr1)) (initial M1)) \<noteq> {}" by auto

  then have "?io \<in> language_state M1 (initial M1)"
  proof -
    have f1: "path PM (map fst pathF || map fst (map snd pathF) || map snd (map snd pathF)) (initial M2, initial M1)"
      by (metis (no_types) \<open>initial PM = (initial M2, initial M1)\<close> pathF_def zip_map_fst_snd)
    have "\<forall>c f. c \<noteq> initial (f::('a, 'b, 'c) FSM) \<or> c \<in> nodes f"
      by blast
    then show ?thesis
      using f1 by (metis (no_types) assms(1) assms(2) assms(3) language_state length_map productF_path_reverse_ob)
  qed 

  moreover have "?io \<notin> language_state M2 (initial M2)"
  proof (rule ccontr)
    assume "\<not> ?io \<notin> language_state M2 (initial M2)"
    then have assm : "?io \<in> language_state M2 (initial M2)" by simp
    then obtain tr2' where tr2'_def : "path M2 (?io || tr2') (initial M2) \<and> length ?io = length tr2'" by auto
    then obtain tr2'_init tr2'_last where tr2'_split : "tr2' = tr2'_init @ [tr2'_last]" using fail_prop by (metis \<open>pathF \<noteq> []\<close> append_butlast_last_id length_0_conv map_is_Nil_conv) 

    have "butlast ?io \<in> language_state M2 (initial M2)" using fail_prop by auto
    then have "{t. path M2 (butlast ?io || t) (initial M2) \<and> length (butlast ?io) = length t} = {butlast ?tr2}" 
      using assms(5) observable_path_unique[of "butlast ?io" M2 "initial M2" "butlast ?tr2"] fail_prop by fastforce
    then have "\<forall> t ts . path M2 ((butlast ?io) @ [last ?io] || ts @ [t]) (initial M2) \<and> length ((butlast ?io) @ [last ?io]) = length (ts @ [t]) \<longrightarrow> ts = butlast ?tr2"
      by (metis (no_types, lifting) FSM.path_append_elim \<open>butlast (map fst pathF) \<in> language_state M2 (initial M2)\<close> assms(5) butlast_snoc butlast_zip fail_prop length_butlast length_map observable_path_unique zip_append)
    
    then have "tr2'_init = butlast ?tr2" using tr2'_def tr2'_split using \<open>pathF \<noteq> []\<close> by auto
    then have "path M2 ((butlast ?io) @ [last ?io] || (butlast ?tr2) @ [tr2'_last]) (initial M2) \<and> length ((butlast ?io) @ [last ?io]) = length ((butlast ?tr2) @ [tr2'_last])" using tr2'_def fail_prop tr2'_split by auto
    then have "path M2 ([last ?io] || [tr2'_last]) (target (butlast ?io || butlast ?tr2) (initial M2)) \<and> length [last ?io] = length [tr2'_last]" by auto
    then have "tr2'_last \<in> succ M2 (last (?io)) (target (butlast (?io || ?tr2)) (initial M2))" by auto
    then show "False" using fail_prop by auto
  qed

  ultimately show ?thesis by auto
qed



lemma fail_reachable_iff[iff] : 
  assumes "well_formed M1"
  and     "well_formed M2" 
  and     "productF M2 M1 FAIL PM"
  and     "observable M2"
shows "FAIL \<in> reachable PM (initial PM) \<longleftrightarrow> \<not> M1 \<preceq> M2"
proof
  show "FAIL \<in> reachable PM (initial PM) \<Longrightarrow> \<not> M1 \<preceq> M2" using assms fail_reachable_reverse by blast 
  show "\<not> M1 \<preceq> M2 \<Longrightarrow> FAIL \<in> reachable PM (initial PM)" using assms fail_reachable by blast
qed






lemma non_distinct_duplicate_indices :
  assumes "\<not> distinct xs"
shows "\<exists> i1 i2 . i1 \<noteq> i2 \<and> xs ! i1 = xs ! i2 \<and> i1 \<le> length xs \<and> i2 \<le> length xs"
  using assms by (meson distinct_conv_nth less_imp_le) 

lemma set_of_succs_finite :
  assumes "well_formed M"
  and     "q \<in> nodes M"
shows "finite (succ M io q)"
proof (rule ccontr)
  assume "infinite (succ M io q)"
  moreover have "succ M io q \<subseteq> nodes M" using assms by (simp add: subsetI succ_nodes) 
  ultimately have "infinite (nodes M)" using infinite_super by blast 
  then show "False" using assms by auto
qed

lemma well_formed_path_io_containment : 
  assumes "well_formed M"
  and     "path M p q"
shows "set (map fst p) \<subseteq> (inputs M \<times> outputs M)"
using assms proof (induction p arbitrary: q)
case Nil
  then show ?case by auto
next
  case (Cons a p)
  have "fst a \<in> (inputs M \<times> outputs M)"
  proof (rule ccontr)
    assume "fst a \<notin> inputs M \<times> outputs M"
    then have "fst (fst a) \<notin> inputs M \<or> snd (fst a) \<notin> outputs M" by (metis SigmaI prod.collapse) 
    then have "succ M (fst a) q = {}" using Cons by (metis prod.collapse well_formed.elims(2)) 
    moreover have "(snd a) \<in> succ M (fst a) q" using Cons by auto
    ultimately show "False" by auto
  qed
  moreover have "set (map fst p) \<subseteq> (inputs M \<times> outputs M)" using Cons by blast 
  ultimately show ?case by auto
qed

lemma path_state_containment :
  assumes "path M p q"
  and     "q \<in> nodes M"
shows "set (map snd p) \<subseteq> nodes M"
  using assms by (metis FSM.nodes_states states_alt_def) 




lemma set_of_paths_finite : 
  assumes "well_formed M"
  and     "q1 \<in> nodes M"
shows "finite { p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
proof -

  let ?trs = "{ tr . set tr \<subseteq> nodes M \<and> length tr \<le> k }"
  let ?ios = "{ io . set io \<subseteq> inputs M \<times> outputs M \<and> length io \<le> k }"
  let ?iotrs = "image (\<lambda> (io,tr) . io || tr) (?ios \<times> ?trs)"

  let ?paths = "{ p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
  
  have "finite (inputs M \<times> outputs M)" using assms by auto
  then have "finite ?ios" using assms by (simp add: finite_lists_length_le) 
  moreover have "finite ?trs" using assms by (simp add: finite_lists_length_le)
  ultimately have "finite ?iotrs" by auto

  moreover have "?paths \<subseteq> ?iotrs" 
  proof 
    fix p assume p_assm : "p \<in> { p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
    then obtain io tr where p_split : "p = io || tr \<and> length io = length tr" using that by (metis (no_types) length_map zip_map_fst_snd)
    then have "io \<in> ?ios" using well_formed_path_io_containment
    proof -
      have f1: "path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k"
        using p_assm by force
      then have "set io \<subseteq> inputs M \<times> outputs M"
        by (metis (no_types) assms(1) map_fst_zip p_split well_formed_path_io_containment)
      then show ?thesis
        using f1 by (simp add: p_split)
    qed 

    moreover have "tr \<in> ?trs" using p_split
    proof -
      have f1: "path M (io || tr) q1 \<and> target (io || tr) q1 = q2 \<and> length (io || tr) \<le> k" using \<open>p \<in> {p. path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k}\<close> p_split by force
      then have f2: "length tr \<le> k" by (simp add: p_split)
      have "set tr \<subseteq> nodes M" using f1 by (metis (no_types) assms(2) length_map p_split path_state_containment zip_eq zip_map_fst_snd)
      then show ?thesis using f2 by blast
    qed 
    ultimately show "p \<in> ?iotrs" using p_split by auto
  qed

  ultimately show ?thesis using Finite_Set.finite_subset by blast
qed 




lemma reaching_path_without_repetition :
  assumes "well_formed M"
  and     "q2 \<in> reachable M q1"
  and     "q1 \<in> nodes M"
shows "\<exists> p . path M p q1 \<and> target p q1 = q2 \<and> distinct (q1 # states p q1)"
proof -
  have shorten_nondistinct : "\<forall> p . (path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)) 
               \<longrightarrow> (\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
  proof 
    fix p 
    show "(path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)) 
               \<longrightarrow> (\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
    proof 
      assume assm : "path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)"
      then show "(\<exists>p'. path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
      proof (cases "q1 \<in> set (states p q1)")
        case True
        have "\<exists> i1 . target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0"
        proof (rule ccontr)
          assume "\<nexists>i1. target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0"
          then have "\<not> (\<exists> i1 . (states p q1) ! i1 = q1 \<and> i1 \<le> length (states p q1))" by (metis True in_set_conv_nth less_eq_Suc_le scan_length scan_nth zero_less_Suc)
          then have "q1 \<notin> set (states p q1)" by (meson in_set_conv_nth less_imp_le)  
          then show "False" using True by auto
        qed
        then obtain i1 where i1_def : "target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0" by auto

        then have "path M (take i1 p) q1" using assm by (metis FSM.path_append_elim append_take_drop_id)  
        moreover have "path M (drop i1 p) q1" using i1_def by (metis FSM.path_append_elim append_take_drop_id assm) 
        ultimately have "path M (drop i1 p) q1 \<and> (target (drop i1 p) q1 = q2)" using i1_def by (metis (no_types) append_take_drop_id assm fold_append o_apply)
        
        moreover have "length (drop i1 p) < length p" using i1_def by auto
        ultimately show ?thesis using assms by blast
      
     next
        case False
        then have assm' : "path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (states p q1)" using assm by auto

        have "\<exists> i1 i2 . i1 \<noteq> i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 \<and> i1 \<le> length p \<and> i2 \<le> length p"
        proof (rule ccontr)
          assume "\<not> (\<exists> i1 i2 . i1 \<noteq> i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 \<and> i1 \<le> length p \<and> i2 \<le> length p)"
          then have "\<not> (\<exists> i1 i2 . i1 \<noteq> i2 \<and> (states p q1) ! i1 = (states p q1) ! i2 \<and> i1 \<le> length (states p q1) \<and> i2 \<le> length (states p q1))"
            by (metis (no_types, lifting) Suc_leI assm' distinct_conv_nth nat.inject scan_length scan_nth) 
    
          then have "distinct (states p q1)" using non_distinct_duplicate_indices by blast 
          then show "False" using assm' by auto
        qed
        then obtain i1 i2 where i_def : "i1 < i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 \<and> i1 \<le> length p \<and> i2 \<le> length p" by (metis nat_neq_iff)
    
        then have "path M (take i1 p) q1" using assm by (metis FSM.path_append_elim append_take_drop_id)  
        moreover have "path M (drop i2 p) (target (take i2 p) q1)" by (metis FSM.path_append_elim append_take_drop_id assm) 
        ultimately have "path M ((take i1 p) @ (drop i2 p)) q1 \<and> (target ((take i1 p) @ (drop i2 p)) q1 = q2)" using i_def assm
          by (metis FSM.path_append append_take_drop_id fold_append o_apply) 
    
        moreover have "length ((take i1 p) @ (drop i2 p)) < length p" using i_def by auto
    
        ultimately have "path M ((take i1 p) @ (drop i2 p)) q1 \<and> target ((take i1 p) @ (drop i2 p)) q1 = q2 \<and> length ((take i1 p) @ (drop i2 p)) < length p" by simp
      
        then show ?thesis using assms by blast
      qed


      
    qed
  qed



  obtain p where p_def : "path M p q1 \<and> target p q1 = q2" using assms by auto

  let ?paths = "{p' . (path M p' q1 \<and> target p' q1 = q2 \<and> length p' \<le> length p)}"
  let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
  have "?paths \<noteq> empty" using p_def by auto
  moreover have "finite ?paths" using assms by (simp add: set_of_paths_finite) 
  ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" by (meson arg_min_nat_lemma equals0I) 
  
  moreover have "distinct (q1 # states ?minPath q1)"
  proof (rule ccontr)
    assume "\<not> distinct (q1 # states ?minPath q1)"
    then have "\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length ?minPath" using shorten_nondistinct minPath_def by blast 
    then show "False" using minPath_def using arg_min_nat_le dual_order.strict_trans1 by auto 
  qed

  ultimately show ?thesis by auto
qed
  




lemma states_target_index :
  assumes "i < length p"
  shows "(states p q1) ! i = target (take (Suc i) p) q1"
  using assms by auto 


lemma reaching_path_length :
  assumes "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "q2 \<in> reachable AB q1"
  and     "q2 \<noteq> FAIL"
  and     "q1 \<in> nodes AB"
shows "\<exists> p . path AB p q1 \<and> target p q1 = q2 \<and> length p < card (nodes A) * card (nodes B)"
proof -
  obtain p where p_def : "path AB p q1 \<and> target p q1 = q2 \<and> distinct (q1 # states p q1)" using assms reaching_path_without_repetition by (metis well_formed_productF) 

  have "FAIL \<notin> set (q1 # states p q1)"
  proof(cases p)
    case Nil
    then have "q1 = q2" using p_def by auto
    then have "q1 \<noteq> FAIL" using assms by auto
    then show ?thesis using Nil by auto
  next
    case (Cons a list)
    have "FAIL \<notin> set (butlast (q1 # states p q1))" 
    proof (rule ccontr)
      assume assm : "\<not> FAIL \<notin> set (butlast (q1 # states p q1))"
      then obtain i where i_def : "i < length (butlast (q1 # states p q1)) \<and> butlast (q1 # states p q1) ! i = FAIL" by (metis distinct_Ex1 distinct_butlast p_def) 
      then have "i < Suc (length (butlast p))" using local.Cons by fastforce 
      then have "i < length p" by (metis append_butlast_last_id length_append_singleton list.simps(3) local.Cons) 
  
      then have "butlast (q1 # states p q1) ! i = target (take i p) q1" 
      using i_def assm proof (induction i)
        case 0
        then show ?case by auto
      next
        case (Suc i)
        then show ?case by (metis Suc_lessD nth_Cons_Suc nth_butlast states_target_index)  
      qed

      then have "target (take i p) q1 = FAIL" using i_def by auto
      moreover have "\<forall> k . k < length p \<longrightarrow> target (take k p) q1 \<noteq> FAIL" using no_prefix_targets_FAIL[of A B FAIL AB p q1] assms p_def by auto
      ultimately show "False" by (metis assms(5) linorder_neqE_nat nat_less_le order_refl p_def take_all) 
    qed

    moreover have "last (q1 # states p q1) \<noteq> FAIL" using assms(5) local.Cons p_def transition_system_universal.target_alt_def by force 
    ultimately show ?thesis by (metis (no_types, lifting) UnE append_butlast_last_id list.set(1) list.set(2) list.simps(3) set_append singletonD) 
  qed

  moreover have "set (q1 # states p q1) \<subseteq> nodes AB" using assms by (metis FSM.nodes_states insert_subset list.simps(15) p_def) 
  ultimately have states_subset : "set (q1 # states p q1) \<subseteq> nodes A \<times> nodes B" using nodes_productF assms by blast 

  have finite_nodes : "finite (nodes A \<times> nodes B)" using assms(2) assms(3) by auto 
  have "length p \<le> length (states p q1)" by simp
  then have "length p < card (nodes A) * card (nodes B)"  by (metis (no_types) finite_nodes states_subset card_cartesian_product card_mono distinct_card impossible_Cons less_le_trans not_less p_def)

  then show ?thesis using p_def by blast    
qed 
  

lemma reaching_path_fail_length :
  assumes "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "q2 \<in> reachable AB q1"
  and     "q1 \<in> nodes AB"
shows "\<exists> p . path AB p q1 \<and> target p q1 = q2 \<and> length p \<le> card (nodes A) * card (nodes B)"
proof (cases "q2 = FAIL")
  case True

  then have q2_def : "q2 = FAIL" by simp
  then show ?thesis 
  proof (cases "q1 = q2")
    case True
    then show ?thesis by auto
  next
    case False
    then obtain px where px_def : "path AB px q1 \<and> target px q1 = q2" using assms by auto
    then have px_nonempty : "px \<noteq> []" using q2_def using False by auto 
    let ?qx = "target (butlast px) q1"
    have "?qx \<in> reachable AB q1" using px_def px_nonempty
      by (metis FSM.path_append_elim FSM.reachable.reflexive FSM.reachable_target append_butlast_last_id) 
    moreover have "?qx \<noteq> FAIL" using False q2_def assms by (metis One_nat_def Suc_pred butlast_conv_take length_greater_0_conv lessI no_prefix_targets_FAIL px_def px_nonempty) 
    ultimately obtain px' where px'_def : "path AB px' q1 \<and> target px' q1 = ?qx \<and> length px' < card (nodes A) * card (nodes B)" using assms reaching_path_length[of A B FAIL AB ?qx q1] by blast  

    have px_split : "path AB ((butlast px) @ [last px]) q1 \<and> target ((butlast px) @ [last px]) q1 = q2" using px_def px_nonempty by auto
    then have "path AB [last px] ?qx \<and> target [last px] ?qx = q2" using px_nonempty
    proof -
      have "target [last px] (target (butlast px) q1) = q2" using px_split by force
      then show ?thesis using px_split by blast
    qed 

    then have "path AB (px' @ [last px]) q1 \<and> target (px' @ [last px]) q1 = q2" using px'_def by auto
    moreover have "length (px' @ [last px]) \<le> card (nodes A) * card (nodes B)" using px'_def by auto
    ultimately show ?thesis by blast 
  qed  
next
  case False
  then show ?thesis using assms reaching_path_length by (metis less_imp_le) 
qed










fun minimal_sequence_to_failure_extending :: "'in list set \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "minimal_sequence_to_failure_extending V M1 M2 io = (
   \<exists> v \<in> V . \<exists> v' \<in> language_state_in M1 (initial M1) V .sequence_to_failure M1 M2 (v' @ io) 
              \<and> \<not> (\<exists> io' . \<exists> w' \<in> language_state_in M1 (initial M1) V . sequence_to_failure M1 M2 (w' @ io') \<and> length io' < length io))"

lemma minimal_sequence_to_failure_extending_det_state_cover_ob :
  assumes "productF M2 M1 FAIL PM"
  and     "well_formed M1"
  and     "well_formed M2"
  and     "observable M2"
  and     "is_det_state_cover M2 V"
  and     "\<not> M1 \<preceq> M2"
obtains io
where "minimal_sequence_to_failure_extending V M1 M2 io" 
proof
  let ?seqs = "{seq . \<exists> v' \<in> language_state_in M1 (initial M1) V .sequence_to_failure M1 M2 (v' @ seq)}"
  obtain seq where "sequence_to_failure M1 M2 seq" using assms sequence_to_failure_ob by blast
  then have "sequence_to_failure M1 M2 ([] @ seq)" by simp
  moreover have "[] \<in> language_state_in M1 (initial M1) V" using assms det_state_cover_empty language_state_in_empty by metis
  ultimately have "seq \<in> ?seqs" using assms(5) by blast
  then have seqs_nonempty : "?seqs \<noteq> {}" by auto

  let ?minSeq = "arg_min length (\<lambda> io . io \<in> ?seqs)"
  have minSeq_def : "?minSeq \<in> ?seqs \<and> (\<forall> seq' \<in> ?seqs . length  ?minSeq \<le> length seq')" using seqs_nonempty by (meson all_not_in_conv arg_min_nat_lemma) 
  moreover have "\<not> (\<exists> io' . \<exists> w' \<in> language_state_in M1 (initial M1) V . sequence_to_failure M1 M2 (w' @ io') \<and> length io' < length ?minSeq)"
  proof (rule ccontr)
    assume "\<not> (\<nexists>io'. \<exists>w'\<in>language_state_in M1 (initial M1) V. sequence_to_failure M1 M2 (w' @ io') \<and> length io' < length ?minSeq)"
    then obtain seq' where seq'_def : "\<exists>w' \<in> language_state_in M1 (initial M1) V. sequence_to_failure M1 M2 (w' @ seq') \<and> length seq' < length ?minSeq" by auto
    then have "seq' \<in> ?seqs \<and> length seq' < length ?minSeq " by auto
    then show "False" using minSeq_def using leD by blast  
  qed
  ultimately show "minimal_sequence_to_failure_extending V M1 M2 ?minSeq" by auto
qed
  




lemma productF_language :
  assumes "productF A B FAIL AB"
  and     "well_formed A"
  and     "well_formed B"
  and     "io \<in> L A \<inter> L B"
shows "io \<in> L AB"
proof -
  obtain trA trB where tr_def : "path A (io || trA) (initial A) \<and> length io = length trA" 
                                "path B (io || trB) (initial B) \<and> length io = length trB" using assms by blast 
  then have "path AB (io || trA || trB) (initial A, initial B)" using assms by (metis FSM.nodes.initial productF_path_inclusion)
  then show ?thesis using tr_def by (metis assms(1) language_state length_zip min.idem productF_simps(4)) 
qed

end