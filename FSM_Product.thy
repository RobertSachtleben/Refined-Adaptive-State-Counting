theory FSM_Product
imports FSM2
begin

(*

definition productF :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> 'out 
  \<Rightarrow> ('in, 'out, 'state1 \<times>'state2) FSM \<Rightarrow> bool" where
  "productF A B FAIL fail AB \<equiv> 
    (inputs A = inputs B) 
  \<and> (fst FAIL \<notin> nodes A) 
  \<and> (snd FAIL \<notin> nodes B) 
  \<and> (fail \<notin> outputs A) 
  \<and> (fail \<notin> outputs B) 
  \<and> AB =  \<lparr>
            succ = (
              \<lambda> a (p1,p2) . (if (((p1,p2) = FAIL) \<and> (snd a = fail) \<and> (fst a \<in> inputs A))
                then {FAIL}
                else (if (succ A a p1 = {} \<and> (fst a \<in> inputs A))
                  then {FAIL} 
                  else (succ A a p1 \<times> succ B a p2)
                )
              )
            ),
            inputs = inputs A \<union> inputs B,
            outputs = outputs A \<union> outputs B,
            initial = (initial A, initial B)
          \<rparr> "

*)

fun productF :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> ('state1 \<times> 'state2)  
  \<Rightarrow> ('in, 'out, 'state1 \<times>'state2) FSM \<Rightarrow> bool" where
  "productF A B FAIL AB = ( 
    (inputs A = inputs B) 
  \<and> (fst FAIL \<notin> nodes A) 
  \<and> (snd FAIL \<notin> nodes B)
  \<and> AB =  \<lparr>
            succ = (\<lambda> a (p1,p2) . (if (p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst a \<in> inputs A) \<and> (snd a \<in> outputs A \<union> outputs B))
                                    then (if (succ A a p1 = {})
                                      then {FAIL} 
                                      else (succ A a p1 \<times> succ B a p2))
                                    else {})),
            inputs = inputs A,
            outputs = outputs A \<union> outputs B,
            initial = (initial A, initial B)
          \<rparr> )"

lemma productF_simps[simp]:
  "productF A B FAIL AB \<Longrightarrow> succ AB a (p1,p2) = (if (p1 \<in> nodes A \<and> p2 \<in> nodes B \<and> (fst a \<in> inputs A) \<and> (snd a \<in> outputs A \<union> outputs B))
                                    then (if (succ A a p1 = {})
                                      then {FAIL} 
                                      else (succ A a p1 \<times> succ B a p2))
                                    else {})"
  "productF A B FAIL AB \<Longrightarrow> inputs AB = inputs A"
  "productF A B FAIL AB \<Longrightarrow> outputs AB = outputs A \<union> outputs B"
  "productF A B FAIL AB \<Longrightarrow> initial AB = (initial A, initial B)"
  unfolding productF.simps by simp+

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
  then have "succ A w p1 \<noteq> {}" using succs by force
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
      
    show ?thesis proof (cases "(succ M2 (x,y) p1 = {})")
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
  and "productF M2 M1 FAIL PM"
shows "FAIL \<in> reachable PM (initial PM)"
proof -
  let ?diff = "{ io . io \<in> language_state M1 (initial M1) \<and> io \<notin> language_state M2 (initial M2)}"
  have "?diff \<noteq> empty" using assms by auto
  moreover  obtain io where io_def[simp] : "io = arg_min length (\<lambda> io . io \<in> ?diff)" using assms by auto
  ultimately have io_diff : "io \<in> ?diff" using assms by (meson all_not_in_conv arg_min_natI) 

  then have "io \<noteq> []" using assms io_def using language_state by auto 
  then obtain io_init io_last where io_split[simp] : "io = io_init @ [io_last]" using list.exhaust by blast 

  
  
  
  have "io_init \<in> language_state M1 (initial M1) \<and> io_init \<in> language_state M2 (initial M2)"
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
  then have "path PM (io_init || tr2 || tr1) (initial PM)" using productF_path[of io_init tr2 tr1 M2 M1 FAIL PM "initial M2" "initial M1"] assms by auto
  then have "io_init \<in> language_state PM (initial PM)" using tr_def by auto

  

end