theory ATC
  imports Main FSM "~~/src/HOL/Library/Finite_Set" "~~/src/HOL/Library/Finite_Map"
begin


datatype ('in, 'out) ATC = Leaf | Node 'in "('out , (('in, 'out) ATC)) fmap"

fun is_atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list \<Rightarrow> bool" where
"is_atc_reaction M s1 Leaf [] = True" |
"is_atc_reaction M s1 Leaf io = False" |
"is_atc_reaction M s1 (Node x f) [] = (\<not>(\<exists> y s2 . (s1,x,y,s2) \<in> transitions M))" | (*only relevant if M not completely specified *)
"is_atc_reaction M s1 (Node x f) ((xi,yi)#io) = (case (fmlookup f yi) of
  Some t \<Rightarrow> (x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 t io)) |
  None \<Rightarrow> (io = [] \<and> x = xi \<and> (\<exists> s2 . (s1,xi,yi,s2) \<in> transitions M)))"

fun has_height_gte :: "('in, 'out) ATC \<Rightarrow> nat \<Rightarrow> bool" where
"has_height_gte Leaf n = True" |
"has_height_gte (Node x f) 0 = False" |
"has_height_gte (Node x f) (Suc n) = (\<forall> t \<in> fmran' f .  has_height_gte t n)"
(*"has_height_gte (Node x f) (Suc n) = Ball (ran f) (\<lambda> t . has_height_gte t n)"*)




definition has_height :: "('in, 'out) ATC \<Rightarrow> nat \<Rightarrow> bool" where
"has_height T n \<equiv> has_height_gte T n \<and> (\<forall> i < n . \<not> has_height_gte T i)"

definition height_the :: "('in, 'out) ATC \<Rightarrow> nat" where
"height_the T = (THE n . has_height T n)"


lemma height_inc : "has_height_gte t n1 \<Longrightarrow> n2 > n1 \<Longrightarrow> has_height_gte t n2"
proof (induction t  arbitrary: n1 n2)
  case Leaf
  then show ?case by simp
next
  case (Node x f)
  have gtz : "n1 > 0"
  proof (rule ccontr)
    assume "\<not> (n1 > 0)"
    then have "t = Leaf" using has_height_gte.elims(2) using Node.prems by blast
    then show "False" using Node \<open>\<not> 0 < n1\<close> by auto
  qed
  have "\<forall> t1 \<in> fmran' f . has_height_gte t1 (n2-1)"
  proof 
    fix t1 
    show "t1 \<in> fmran' f \<Longrightarrow> has_height_gte t1 (n2-1)"
    proof (rule Node.IH[of "t1" "n1-1" "n2-1"])
      assume el: "t1 \<in> fmran' f"
      show "has_height_gte t1 (n1-1)" using Node.prems(1) gtz el gr0_conv_Suc by auto
      show "(n2-1) > (n1-1)" using Node.prems(2) gtz by linarith
    qed
  qed
  then show "has_height_gte (Node x f) n2" using Node.prems(2) diff_Suc_1 has_height_gte.elims(3) less_numeral_extra(3) by fastforce
qed



lemma upper_bound : 
  fixes n1 :: nat
  and S :: "'a set"
  and P :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  assumes el: "\<forall> a \<in> S . \<exists> n1 . P a (n1 a)"
  and fn: "finite S"
  shows 
  "\<exists> n2 . \<forall> a \<in> S . \<exists> n1 . P a (n1 a) \<and> n2 > (n1 a)"
proof -
  have sized_subset_f : "\<forall> n . \<forall> S1. ((S1 \<subseteq> S \<and> card S1 = n) \<longrightarrow> (\<exists> nf . \<forall> a \<in> S1 . P a (nf a)))" 
  proof
    fix n
    show "\<forall> S1. ((S1 \<subseteq> S \<and> card S1 = n) \<longrightarrow> (\<exists> nf . \<forall> a \<in> S1 . P a (nf a)))" 
    proof (induction "n")
      case 0
      then show ?case
      proof
        fix S1
        show "S1 \<subseteq> S \<and> card S1 = 0 \<longrightarrow> (\<exists> nf . \<forall>a\<in>S1. P a (nf a))"
        proof 
          assume S1_assm : "S1 \<subseteq> S \<and> card S1 = 0" 
          have "finite S1" using S1_assm fn finite_subset by blast
          then have "S1 = {}" using fn S1_assm card_0_eq by blast
          then show "\<exists>nf. \<forall>a\<in>S1. P a (nf a)" by simp
        qed
      qed
    next
      case (Suc k)
      show ?case
      proof 
        fix S1
        show "S1 \<subseteq> S \<and> card S1 = Suc k \<longrightarrow> (\<exists> nf . \<forall>a\<in>S1. P a (nf a))"
        proof 
          assume S1_assm : "S1 \<subseteq> S \<and> card S1 = Suc k"
          have "finite S1" using S1_assm fn finite_subset by blast
          then obtain x S2 where x_def : "S1 = {x} \<union> S2 \<and> x \<notin> S2" using fn S1_assm by (metis card_le_Suc_iff dual_order.refl insert_is_Un)
          then have "card S2 = k" using S1_assm \<open>finite S1\<close> by auto
          moreover have "S2 \<subseteq> S1" using x_def by auto
          then obtain nf2 where nf2_def : "\<forall>a\<in>S2. P a (nf2 a)" using Suc.IH S1_assm calculation by fastforce
          have "x \<in> S" using x_def S1_assm by auto
          then obtain nfx where nfx_def : "P x (nfx x)" using el by auto
          show "\<exists> nf . \<forall> a \<in> S1 . P a (nf a)"
          proof 
            let ?nf = "nf2(x := nfx x)"
            show "\<forall> a \<in> S1 . P a (?nf a)"
            proof
              fix a
              show "a \<in> S1 \<Longrightarrow> P a (?nf a)"
              proof (cases "a = x")
              case True
                then show ?thesis using nfx_def by auto
              next
                case False
                assume "a \<in> S1"
                then have "a \<in> S2" using x_def False by blast
                then show ?thesis using nf2_def False by auto 
              qed
            qed
          qed
        qed
      qed
    qed
  qed   

  
  
  
  have "S \<subseteq> S" by auto
  moreover have "card S = card S" by simp
  print_theorems
  then obtain nfS where nfS_def : "\<forall> a \<in> S . P a (nfS a)" using sized_subset_f by auto
  let ?nf_set = "image nfS S"
  have "finite ?nf_set" using fn by simp
  let ?ub = "Max ?nf_set"
  have n2_gt : "\<forall> a \<in> ?nf_set . a < Suc ?ub" using finite_nat_set_iff_bounded by (meson Max_ge \<open>finite (nfS ` S)\<close> le_imp_less_Suc)
  let ?n2 = "Suc ?ub"

  have n2_ub : "\<forall>a\<in>S. \<exists> n1 . P a (n1 a) \<and> n1 a < ?n2"
  proof 
    fix a
    show "a \<in> S \<Longrightarrow>\<exists> n1 . P a (n1 a) \<and> n1 a < ?n2"
    proof
      show "a \<in> S \<Longrightarrow> P a (nfS a) \<and> nfS a < ?n2"
      proof
        show "a \<in> S \<Longrightarrow> P a (nfS a)" using nfS_def by blast
        show "a \<in> S \<Longrightarrow> nfS a < ?n2" using n2_gt by blast
      qed
    qed
  qed

  show ?thesis 
  proof -
    obtain ubF where ubF_def : "\<forall>a\<in>S. \<exists> n1 . P a (n1 a) \<and> n1 a < ubF" using n2_ub by auto
    then show ?thesis by auto
  qed
qed


lemma upper_bound_f : 
  fixes S :: "'a set"
  and   P :: "'a \<Rightarrow> nat \<Rightarrow> bool"
  and   f :: "'a \<Rightarrow> nat"
  assumes el: "\<forall> a \<in> S . P a (f a)"
  and     fn: "finite S"
  shows 
  "\<exists> n2 . \<forall> a \<in> S . n2 > (f a)"
proof -
  let ?f_set = "image f S"
  have "finite ?f_set" using fn by simp
  let ?ub = "Max ?f_set"
  have gtv : "\<forall> a \<in> ?f_set . a < Suc ?ub" using finite_nat_set_iff_bounded by (meson Max_ge \<open>finite (f ` S)\<close> le_imp_less_Suc)
  
  then obtain hv where hv_def : "\<forall> a \<in> S . hv > f a" by simp
  then show ?thesis by auto
qed

lemma upper_bound_height :
  fixes S :: "('in, 'out) ATC set"
  and   f :: "('in, 'out) ATC \<Rightarrow> nat"
  assumes el: "\<forall> a \<in> S . has_height_gte a (f a)"
  and     fn: "finite S"
  shows 
  "\<exists> ub . \<forall> a \<in> S . ub > (f a)"
  using upper_bound_f assms by blast

lemma h_map_ex :
  assumes "\<forall> x \<in> X . \<exists> y . P x y"
  shows "\<exists> f . \<forall> x \<in> X . P x (f x)"
  using assms by (rule Hilbert_Choice.bchoice)

lemma range_domain_finite : 
  fixes f :: "'a \<Rightarrow> 'b option"
  assumes fd : "finite (dom m)"
  shows "finite (ran m)"
  using assms by (rule Map.finite_ran)


lemma fmran'_finite :
  fixes m :: "('a, 'b) fmap"
  shows "finite (fmran' m)"
proof -
  have "finite (fset (fmran m))" by simp
  show ?thesis by (simp add: fmran'_alt_def)
qed    

lemma height_ex : "\<exists> n . has_height_gte t n"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node x f)
  
  have height_ex : "\<forall> t1 \<in> fmran' f . \<exists> n1 . has_height_gte t1 n1" 
    by (smt Node.IH UNIV_I image_eqI mem_Collect_eq option.set_intros ran_def)
  then obtain hf where hc_def : "\<forall> t1 \<in> fmran' f . has_height_gte t1 (hf t1)" using Hilbert_Choice.bchoice by blast
  moreover have "finite (fmran' f)" using fmran'_finite by auto
  ultimately obtain ub where ub_def : "\<forall> t1 \<in> fmran' f . ub > hf t1" 
    using upper_bound_height[of "fmran' f" "hf"] by blast
  then have ub_valid : "\<forall> t1 \<in> fmran' f . has_height_gte t1 ub"
    using height_inc[of _ _ "ub"] hc_def by blast
  have "has_height_gte (Node x f) (Suc ub)" using ub_valid by auto
  then show ?case by blast
qed

lemma max_elem :
  fixes S :: "nat set"
  assumes fn: "finite S"
  assumes ne: "S \<noteq> {}"
  shows "\<exists> y1 \<in> S . \<forall> y2 \<in> S . y2 \<le> y1"
  using assms Max_ge Max_in by blast

lemma max_elem_f :
  fixes S :: "'a set"
    and f :: "'a \<Rightarrow> nat"
  assumes fn: "finite S"
  assumes ne: "S \<noteq> {}"
  shows "\<exists> x1 \<in> S . \<forall> x2 \<in> S . f x2 \<le> f x1"
proof -
  obtain maxV where maxV_def : "maxV \<in> (image f S) \<and> (\<forall> y \<in> (image f S) . y \<le> maxV)" 
    using max_elem assms by (metis empty_is_image finite_imageI)
  then obtain maxE where maxE_def : "maxE \<in> S \<and> f maxE = maxV" by blast
  then have "maxE \<in> S \<and> (\<forall> x \<in> S . f x \<le> f maxE)" using maxV_def by blast
  then show ?thesis by blast
qed

lemma height_min_ex : "\<exists> n . has_height_gte t n \<and> (\<forall> m . (has_height_gte t m) \<longrightarrow> (n \<le> m))"
proof (induction t)
  case Leaf
  then show ?case by auto
next
  case (Node x f)

  then show ?case
  proof (cases "fmran' f = {}")
    case True
    then show ?thesis by (metis empty_iff has_height_gte.simps(2) has_height_gte.simps(3) le_0_eq not_less_eq_eq)
  next
    case False
    
    (* collect childrens minimal heights and show that this node has minimal height: 1 + largest mininmal height *)

    let ?ch_set = "{ (t1,ch) | t1 ch . t1 \<in> fmran' f \<and> has_height_gte t1 ch \<and> (\<forall> m . (has_height_gte t1 m) \<longrightarrow> (ch \<le> m)) }"
    have "\<forall> t1 \<in> fmran' f . \<exists> ch . (t1,ch) \<in> ?ch_set" using Node.IH by blast
    moreover have "\<forall> t1 ch1 ch2 . ((t1,ch1) \<in> ?ch_set \<and> (t1,ch2) \<in> ?ch_set) \<longrightarrow> ch1 = ch2" by (simp add: le_antisym)
    moreover have "Domain ?ch_set \<subseteq> fmran' f" by blast
    moreover have "fmran' f \<subseteq> Domain ?ch_set" using calculation by (simp add: subsetI)
    moreover have "Domain ?ch_set = fmran' f" using calculation by blast
    moreover have "\<forall> t1 \<in> fmran' f . (?ch_set `` {t1}) = {ch . has_height_gte t1 ch \<and> (\<forall> m . (has_height_gte t1 m) \<longrightarrow> (ch \<le> m))}" using calculation by blast
    moreover have "\<forall> t1 \<in> fmran' f . \<exists> ch . (?ch_set `` {t1} = {ch})"
      proof (rule ccontr)
        assume "\<not>(\<forall> t1 \<in> fmran' f . \<exists> ch . (?ch_set `` {t1} = {ch}))"
        then obtain tm where tm_def : "tm \<in> fmran' f \<and> \<not>(\<exists> ch . (?ch_set `` {tm} = {ch}))" by blast
        then have "\<exists> ch . (tm,ch) \<in> ?ch_set" using Node.IH by simp
        then obtain chm where chm_def : "chm \<in> (?ch_set `` {tm})" by blast 
        have "\<forall> ch1 ch2 . ((tm,ch1) \<in> ?ch_set \<and> (tm,ch2) \<in> ?ch_set) \<longrightarrow> ch1 = ch2" using calculation by blast
        then have "\<forall> ch1 ch2 . (ch1 \<in> (?ch_set `` {tm}) \<and> ch2 \<in> (?ch_set `` {tm})) \<longrightarrow> ch1 = ch2" by blast
        moreover have "?ch_set `` {tm} \<noteq> {}" using chm_def by blast
        ultimately have "(?ch_set `` {tm}) = {chm}" using chm_def by auto
        then show "False" using tm_def by blast
      qed
    moreover have "\<forall> t1 \<in> Domain ?ch_set . finite (?ch_set `` {t1})" using calculation by auto
    moreover have "finite (Domain ?ch_set)" using calculation fmran'_finite by simp
    moreover have "finite (Range ?ch_set)" using calculation by simp
    moreover have "finite (Domain ?ch_set \<times> Range ?ch_set)" using calculation by simp
    moreover have "?ch_set \<subseteq> (Domain ?ch_set \<times> Range ?ch_set)" using calculation by blast
    moreover have "finite ?ch_set" using calculation by (meson infinite_super)
    moreover have "?ch_set \<noteq> {}" using calculation by (metis False all_not_in_conv)
    ultimately obtain max_t max_ch where max_el_def : "(max_t,max_ch) \<in> ?ch_set \<and> (\<forall> (t2,ch2) \<in> ?ch_set . snd (t2,ch2) \<le> snd (max_t,max_ch))"
      using max_elem_f[of "?ch_set" "snd"] by (smt SigmaE case_prodI2 subsetCE)

    

    have no_smaller :"\<forall> k . (k < (Suc max_ch) \<longrightarrow> \<not> (has_height_gte (Node x f) k))" 
    proof (rule ccontr)
      assume "\<not>(\<forall> k . (k < (Suc max_ch) \<longrightarrow> \<not> (has_height_gte (Node x f) k)))"

      then obtain lk where lk_def : "(lk < (Suc max_ch) \<and> has_height_gte (Node x f) lk)" by blast
      then have "\<forall> t1 \<in> fmran' f . has_height_gte t1 lk" by (meson has_height_gte.simps(3) height_inc lessI)
      then have "has_height_gte max_t lk" using max_el_def by blast
      moreover have "\<forall> k . (k < max_ch \<longrightarrow> \<not> (has_height_gte max_t k))" using max_el_def
        by (metis (no_types, lifting) Domain.DomainI Image_singleton_iff \<open>Domain {(t1, ch) |t1 ch. t1 \<in> fmran' f \<and> has_height_gte t1 ch \<and> (\<forall>m. has_height_gte t1 m \<longrightarrow> ch \<le> m)} = fmran' f\<close> \<open>\<forall>t1\<in>fmran' f. {(t1, ch) |t1 ch. t1 \<in> fmran' f \<and> has_height_gte t1 ch \<and> (\<forall>m. has_height_gte t1 m \<longrightarrow> ch \<le> m)} `` {t1} = {ch. has_height_gte t1 ch \<and> (\<forall>m. has_height_gte t1 m \<longrightarrow> ch \<le> m)}\<close> has_height_def linorder_not_less mem_Collect_eq)
      ultimately show "False" using lk_def
        by (metis (no_types, lifting) ATC.distinct(1) Domain.DomainI \<open>Domain {(t1, ch) |t1 ch. t1 \<in> fmran' f \<and> has_height_gte t1 ch \<and> (\<forall>m. has_height_gte t1 m \<longrightarrow> ch \<le> m)} = fmran' f\<close> has_height_gte.elims(2) has_height_gte.simps(3) less_Suc_eq_0_disj less_antisym max_el_def)
    qed

    then have "\<forall> t1 \<in> fmran' f . has_height_gte t1 max_ch" using max_el_def height_inc 
      by (smt \<open>\<forall>t1\<in>fmran' f. \<exists>ch. (t1, ch) \<in> {(t1, ch) |t1 ch. t1 \<in> fmran' f \<and> has_height_gte t1 ch \<and> (\<forall>m. has_height_gte t1 m \<longrightarrow> ch \<le> m)}\<close> fst_conv le_eq_less_or_eq mem_Collect_eq old.prod.case snd_conv)

    then have "has_height_gte (Node x f) (Suc max_ch)" by simp

    then show ?thesis using no_smaller using leI by blast
  qed
qed





lemma height_unique_the : 
  assumes hh: "has_height T m"
  shows "height_the T = m"
  using height_min_ex by (metis (no_types, hide_lams) has_height_def height_the_def hh le_eq_less_or_eq theI_unique)

lemma has_height_subtest :
  assumes st: "t \<in> fmran' f"
  assumes h1: "has_height t h1" 
  assumes h2: "has_height (Node x f) h2"
  shows "h2 > h1"
  using assms height_min_ex by (smt One_nat_def add.right_neutral add_Suc_right ex_least_nat_less has_height_def has_height_gte.simps(2) has_height_gte.simps(3) less_trans linorder_neqE_nat)

lemma has_height_the_subtest :
  assumes st: "t \<in> fmran' f"
  shows "height_the (Node x f) > height_the t"
  using has_height_subtest height_unique_the by (metis has_height_def height_min_ex not_less st)



function size :: "('in, 'out) ATC \<Rightarrow> nat" where
"size Leaf = 0" |
"size (Node x f) = (if (fmdom f = fempty) 
  then 1
  else 1 + Max ( image size (fmran' f) ))"
  by pat_completeness auto
termination 
proof (relation "measure height_the")
  show "wf (measure height_the)" by simp
  show "\<And>x f xa.
       xa \<in> fmran' f \<Longrightarrow>
       (xa, Node x f)
       \<in> measure height_the " by (simp add: has_height_the_subtest)
qed




definition atc_io :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in * 'out) list set"
  where "atc_io M s t = { io . is_atc_reaction M s t io }"

definition atc_io_set :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in * 'out) list set" where
"atc_io_set M s T = \<Union> { atc_io M s t | t . t \<in> T }"
  

lemma io_dist_ineq :
  assumes io_diff : "atc_io M s1 t \<noteq> atc_io M s2 t"
  shows "s1 \<noteq> s2"
  using io_diff by auto

lemma io_dist_set_ineq :
  assumes io_diff_set : "atc_io_set M s1 T \<noteq> atc_io_set M s2 T"
  shows "s1 \<noteq> s2"
  using io_diff_set by auto

definition atc_dist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_dist M t s1 s2 \<equiv> atc_io M s1 t \<noteq> atc_io M s2 t"

definition atc_rdist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_rdist M t s1 s2 \<equiv> atc_io M s1 t \<inter> atc_io M s2 t = {}"

definition atc_dist_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_dist_set M T s1 s2 \<equiv> (\<exists> t \<in> T . atc_dist M t s1 s2)"

definition atc_rdist_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_rdist_set M T s1 s2 \<equiv> (\<exists> t \<in> T . atc_rdist M t s1 s2)"



definition atc_reduction_state :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"atc_reduction_state M2 s2 M1 s1 T \<equiv> (\<forall> t \<in> T . atc_io M2 s2 t \<subseteq> atc_io M1 s1 t)"
(*"atc_reduction_state M2 s2 M1 s1 T \<equiv> atc_io_set M2 s2 T \<subseteq> atc_io_set M1 s1 T" *)

definition atc_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"atc_reduction M2 M1 T \<equiv> atc_reduction_state M2 (initial M2) M1 (initial M1) T" 





function atc_inputs :: "('in,'out) ATC \<Rightarrow> 'in set" where
"atc_inputs Leaf = {}" |
"atc_inputs (Node x f) = insert x (\<Union>  (image atc_inputs (fmran' f)))"
  by pat_completeness auto
termination
proof (relation "measure height_the")
  show "wf (measure height_the)" by simp
  show "\<And>x f xa.
       xa \<in> fmran' f \<Longrightarrow>
       (xa, Node x f)
       \<in> measure height_the " by (simp add: fmran'_alt_def has_height_the_subtest)
qed


definition atc_applicable :: "('in,'out,'state) FSM \<Rightarrow> ('in,'out) ATC \<Rightarrow> bool" where
"atc_applicable M t \<equiv> atc_inputs t \<subseteq> inputs M"

definition atc_applicable_set :: "('in,'out,'state) FSM \<Rightarrow> ('in,'out) ATC set \<Rightarrow> bool" where
"atc_applicable_set M T \<equiv> \<forall> t \<in> T . atc_applicable M t"

lemma subtest_inputs :
  assumes el: "t2 \<in> fmran' f"
  shows "atc_inputs t2 \<subseteq> atc_inputs (Node x f)"
proof 
  fix i
  assume "i \<in> atc_inputs t2"
  then obtain i_s where i_s_def : "i_s \<in>  image atc_inputs {t2} \<and> i \<in> i_s" by blast
  then have "i_s \<in> image atc_inputs (fmran' f)" using el by blast
  then have "i \<in> \<Union>  (image atc_inputs (fmran' f))" using i_s_def by blast
  then show "i \<in> atc_inputs (Node x f)" by simp
qed

lemma applicable_subtest :
  assumes el: "t2 \<in> fmran' f"
  and     ap: "atc_applicable M (Node x f)"
  shows "atc_applicable M t2"
  by (metis (mono_tags, lifting) subtest_inputs ap atc_applicable_def dual_order.trans el)

lemma atc_reaction_exists :
  assumes cs : "completely_specified M"
  and     wf : "well_formed M"
  and     ap : "atc_applicable M t"
  and     el : "s \<in> states M"
  shows "\<exists> io . io \<in> atc_io M s t"
using assms proof (induction t arbitrary: s)
  case Leaf
  then show ?case by (metis atc_io_def is_atc_reaction.simps(1) mem_Collect_eq)
next
  case (Node x f)
  have "x \<in> atc_inputs (Node x f)" using atc_inputs.simps(2) by simp
  then have "x \<in> inputs M" using Node.prems(3) by (simp add: atc_applicable_def)
  then obtain y s2 where trans_def : "(s,x,y,s2) \<in> transitions M" by (meson Node.prems completely_specified_def el)
  show "\<exists> io . io \<in> atc_io M s (Node x f)" 
  proof (cases "fmlookup f y")
    case None
    then have "is_atc_reaction M s (Node x f) [(x,y)]" using trans_def is_atc_reaction.simps(4)[of "M" "s" "x" "f" "x" "y" "[]"] None by auto
    then show ?thesis by (metis atc_io_def mem_Collect_eq)
  next
    case (Some t2)
    then have ap2: "atc_applicable M t2" using applicable_subtest Node.prems(3) fmran'I by fastforce
    have "s2 \<in> states M" using wf trans_def transition_contents by fastforce
    then obtain io2 where r2_def : "is_atc_reaction M s2 t2 io2" using Node.IH[of "t2" "s2"] Some ap2 atc_io_def cs fmran'I local.wf by fastforce
    then have "is_atc_reaction M s (Node x f) ((x,y)#io2)"
      using is_atc_reaction.simps(4)[of "M" "s" "x" "f" "x" "y" "io2" ] Some local.trans_def by auto
    then have "((x,y)#io2) \<in> atc_io M s (Node x f)" by (simp add: atc_io_def)
    then show ?thesis by blast
  qed
qed

 
(* Lemma 5.3.7 *)  
lemma atc_rdist_dist :
  assumes wf2   : "well_formed M2"
  and     cs2   : "completely_specified M2"
  and     ap2   : "atc_applicable_set M2 T"
  and     el_t1 : "t1 \<in> states M2"
  and     red1  : "atc_reduction_state M2 t1 M1 s1 T"
  and     red2  : "atc_reduction_state M2 t2 M1 s2 T"
  and     rdist : "atc_rdist_set M1 T s1 s2"
  shows "atc_dist_set M2 T t1 t2"
proof -
  obtain td where td_def : "td \<in> T \<and> atc_rdist M1 td s1 s2" by (meson rdist atc_rdist_set_def)
  then have "atc_io M1 s1 td \<inter> atc_io M1 s2 td = {}" using td_def by (simp add: atc_rdist_def)
  moreover have "atc_io M2 t1 td \<subseteq> atc_io M1 s1 td" by (meson atc_reduction_state_def red1 td_def)
  moreover have "atc_io M2 t2 td \<subseteq> atc_io M1 s2 td" by (meson atc_reduction_state_def red2 td_def)
  ultimately have no_inter : "atc_io M2 t1 td \<inter> atc_io M2 t2 td = {}" by blast
  
  have "td \<noteq> Leaf" using td_def by (metis Int_iff atc_rdist_def atc_io_def equals0D is_atc_reaction.simps(1) mem_Collect_eq)
  then have "atc_io M2 t1 td \<noteq> {}" using atc_reaction_exists ap2 atc_applicable_set_def cs2 el_t1 td_def wf2 by fastforce

  then have "atc_dist M2 td t1 t2" using atc_dist_def no_inter by fastforce
  then show ?thesis by (meson td_def atc_dist_set_def)
qed

(* explicitly requires the ATC set to be applicable to the FSN *)
definition characterizing_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"characterizing_set M T \<equiv> atc_applicable_set M T \<and> (\<forall> s1 \<in> (states M) . \<forall> s2 \<in> (states M) . 
    (\<exists> td . atc_rdist M td s1 s2) \<longrightarrow> (\<exists> tt \<in> T . atc_rdist M tt s1 s2))"


definition B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in * 'out) list set" where
"B M io T = \<Union> (image (\<lambda> s . atc_io_set M s T) (h_y_seq M (initial M) io))"

(* Proposition 5.4.2 *)
lemma B_dist :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     ln1: "io1 \<in> language M"
  and     ln2: "io2 \<in> language M"
  and     df: "B M io1 T \<noteq> B M io2 T"
  shows   "(h_y_seq M (initial M) io1) \<noteq> (h_y_seq M (initial M) io2)"
proof -
  obtain q1 where q1_def : "h_y_seq M (initial M) io1 = {q1}" by (metis h_y_seq_observable language_def ln1 local.wf ob well_formed_def)
  then have B1 : "B M io1 T = atc_io_set M q1 T" by (simp add: B_def)
  obtain q2 where q2_def : "h_y_seq M (initial M) io2 = {q2}" by (metis h_y_seq_observable language_def ln2 local.wf ob well_formed_def)
  then have B2 : "B M io2 T = atc_io_set M q2 T" by (simp add: B_def)
  have "q1 \<noteq> q2" using B1 B2 df by blast
  then show ?thesis using q1_def q2_def by blast
qed



definition D :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'in list set \<Rightarrow> ('in * 'out) list set set" where
"D M T ISeqs \<equiv> { B M io T | io . \<exists> iseq \<in> ISeqs . io \<in> language_state_in M (initial M) iseq }"


lemma set_of_lists_finite:
  assumes f1 : "finite S1"
  assumes ne : "S1 \<noteq> {}" 
  shows "finite { xs . (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs = k }"
proof (induction k)
  case 0
  have "{ xs . (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs = 0 } = {Nil}" using assms by fastforce
  then show ?case by simp
next
  case (Suc k)
  then have "{xs.(\<forall>x\<in>set xs. x \<in> S1) \<and> length xs = Suc k} = { (a#xs) | a xs . a \<in> S1 \<and> (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs = k }" 
    by (smt Collect_cong insert_iff length_Suc_conv list.simps(15))
  then show ?case using assms by (simp add: Suc.IH finite_image_set2)
qed

lemma set_of_lists_finite_lte:
  assumes f1 : "finite S1"
  assumes ne : "S1 \<noteq> {}" 
  shows "finite { xs . (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs \<le> k }"
proof (induction k)
  case 0
  have "{ xs . (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs = 0 } = {Nil}" using assms by fastforce
  then show ?case by simp
next
  case (Suc k)
  let ?orig = "{xs.(\<forall>x\<in>set xs. x \<in> S1) \<and> length xs \<le> Suc k}"
  let ?splt = "{[]} \<union> { (a#xs) | a xs . a \<in> S1 \<and> (\<forall> x \<in> set xs . x \<in> S1) \<and> length xs \<le> k }"
  have "?orig = ?splt" 
  proof 
    show "?orig \<subseteq> ?splt"
    proof   
      fix xs
      assume xs_assm : "xs \<in> ?orig"
      then show "xs \<in> ?splt"
      proof (cases xs)
        case Nil
        then show ?thesis by simp
      next
        case (Cons a list)
        then have "a \<in> S1 \<and> (\<forall> x \<in> set list . x \<in> S1) \<and> length list \<le> k" using xs_assm by auto
        then show ?thesis using Cons xs_assm by auto 
      qed
    qed
    show "?splt \<subseteq> ?orig"
    proof   
      fix xs
      assume xs_assm : "xs \<in> ?splt"
      then show "xs \<in> ?orig"
      proof (cases xs)
        case Nil
        then show ?thesis by simp
      next
        case (Cons a list)
        then have "(\<forall> x \<in> set (Cons a list) . x \<in> S1) \<and> length (Cons a list) \<le> (Suc k)" using xs_assm by auto
        then show ?thesis using Cons xs_assm by auto 
      qed
    qed
  qed
  then show ?case using assms by (simp add: Suc.IH finite_image_set2)
qed

lemma sequence_elem :
  assumes sq: "is_sequence M seq"
  and     wf: "well_formed M"
  shows "\<forall> x \<in> set seq . x \<in> (states M \<times> inputs M \<times> outputs M \<times> states M)"
using assms proof (induction seq rule: is_sequence.induct)
  case (1 M)
  then show ?case by simp
next
  case (2 M a)
  then show ?case using contra_subsetD well_formed_def by fastforce
next
  case (3 M a b seq)
  then show ?case using contra_subsetD well_formed_def by fastforce
qed

lemma transitions_finite : 
  assumes wf : "well_formed M"
  shows "finite (states M \<times> inputs M \<times> outputs M \<times> states M) \<and> (states M \<times> inputs M \<times> outputs M \<times> states M) \<noteq> {}"
  using well_formed_def wf by (simp add: well_formed_def)

lemma ios_finite : 
  assumes wf : "well_formed M"
  shows "finite (inputs M \<times> outputs M) \<and> (inputs M \<times> outputs M) \<noteq> {}"
  using well_formed_def wf by (simp add: well_formed_def)

lemma sequences_length_finite :
  assumes wf: "well_formed M"
shows "finite {seq . is_sequence M seq \<and> length seq = k}"
proof -
  let ?seqSet = "{seq . is_sequence M seq \<and> length seq = k}"
  let ?transSet = "{seq . (\<forall> x \<in> set seq . x \<in> (states M \<times> inputs M \<times> outputs M \<times> states M)) \<and> length seq = k}"
  have "?seqSet \<subseteq> ?transSet" using assms sequence_elem by blast
  moreover have "finite ?transSet"
    using 
      assms
      transitions_finite
      set_of_lists_finite
    by blast
  ultimately show "finite ?seqSet" using finite_subset by auto
qed

lemma io_in_seq_alphabets :
  assumes sq: "\<forall> x \<in> set seq . x \<in> (states M \<times> inputs M \<times> outputs M \<times> states M)"
  and     io: "io = get_io seq"
  shows "\<forall> x \<in> set io . x \<in> (inputs M \<times> outputs M)"
using assms proof (induction seq arbitrary: io)
  case Nil
  then show ?case by (simp add: get_io_def)
next
  case (Cons a seq2)
  obtain xy io2 where io_split : "io = xy # io2" using get_io_length by (metis Cons.prems(2) length_Suc_conv)
  then have "io2 = get_io seq2" using Cons.prems(2) by (simp add: get_io_def)
  then have el2 : "\<forall> x \<in> set io2 . x \<in> (inputs M \<times> outputs M)" using Cons.IH by (simp add: Cons.prems(1))

  
  obtain s1 x y s2 where a_def : "a = (s1,x,y,s2)" using local.Cons(2) by auto
  then have "xy = (x,y)" using io_split Cons a_def by (simp add: get_io_def)
  moreover have "(s1,x,y,s2) \<in> (states M \<times> inputs M \<times> outputs M \<times> states M)" using Cons sq a_def by simp
  ultimately have el_xy : "xy \<in> (inputs M \<times> outputs M)" by blast

  have "set io = insert xy (set io2)" using io_split by simp
  
  then show ?case using el2 el_xy by simp
qed

lemma language_state_in_alphabets :
  assumes wf : "well_formed M"
  and     ln : "io \<in> language_state M s"
shows "(\<forall> x \<in> set io . x \<in> (inputs M \<times> outputs M))"
proof -
  obtain seq where seq_def : "is_enabled_sequence M s seq \<and> io = get_io seq" by (metis language_state_sequence_ex ln)
  have "is_sequence M seq" by (metis is_enabled_sequence.elims(2) is_sequence.simps(1) seq_def)
  then have "\<forall> x \<in> set seq . x \<in> (states M \<times> inputs M \<times> outputs M \<times> states M)" using assms sequence_elem by blast
  then show "\<forall> x \<in> set io . x \<in> (inputs M \<times> outputs M)" using seq_def io_in_seq_alphabets by blast
qed



lemma language_state_in_finite :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     el: "s \<in> states M"
shows "finite (language_state_in M s iseq)"
proof -
  let ?ioS = "{ io . (\<forall> x \<in> set io . x \<in> (inputs M \<times> outputs M)) \<and> length io = length iseq }"
  have "finite (inputs M \<times> outputs M) \<and> (inputs M \<times> outputs M) \<noteq> {}" using wf by (simp add: well_formed_def)
  then have "finite ?ioS" using set_of_lists_finite[of "inputs M \<times> outputs M"] by simp
  moreover have "language_state_in M s iseq \<subseteq> ?ioS" 
  proof 
    fix io
    assume io_assm : "io \<in> language_state_in M s iseq"
    then have "io \<in> language_state M s" using language_state_in_def by fastforce
    then have io_el : "(\<forall> x \<in> set io . x \<in> (inputs M \<times> outputs M))" using language_state_in_alphabets wf by fastforce
    have "length io = length iseq" using io_assm language_state_in_def language_state_i_length by fastforce
    then show "io \<in> ?ioS" using io_el by blast
  qed
  ultimately show ?thesis using finite_subset by auto
qed
      

(*
"B M io T = \<Union> (image (\<lambda> s . atc_io_set M s T) (h_y_seq M (initial M) io))"

lemma atc_io_alt_def : "atc_io M s (Node x f) = 
  { ((x,y)#io) | y io . \<exists> t2 . (fmlookup f y = Some t2) \<and> (\<exists> s2 \<in> states M . (s,x,y,s2) \<in> transitions M \<and> io \<in> atc_io M s2 t2)}
  \<union> { [(x,y)] | y . (fmlookup f y = None) \<and> (\<exists> s2 \<in> states M . (s,x,y,s2) \<in> transitions M) }"
*)

lemma atc_reaction_length :
  assumes ir: "is_atc_reaction M s t io"
  and     ht: "has_height t k"
  shows "length io \<le> k"
using assms proof (induction t arbitrary: s io k)
  case Leaf
  have "\<forall> io . is_atc_reaction M s Leaf io \<longrightarrow> io = []" by (metis is_atc_reaction.simps(2) neq_Nil_conv)
  then have "io = []" using Leaf.prems by blast
  moreover have "k = 0" using Leaf.prems has_height_def has_height_gte.simps(1) by blast
  ultimately show ?case by simp
next
  case (Node x f)
  then show ?case 
  proof (cases io)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a io2)
    then obtain ax ay where a_def : "a = (ax,ay)" by (meson surj_pair)
    show ?thesis 
    proof (cases "(fmlookup f ay)")
      case None
      then have "io2 = []" using Node.prems(1) a_def local.Cons by auto
      moreover have "k \<noteq> 0" using has_height_gte.simps(2) Node by (metis has_height_def)
      ultimately show ?thesis using local.Cons by auto
    next
      case (Some t2)
      have "is_atc_reaction M s (Node x f) ((ax,ay)#io2)" using Node Cons a_def by blast
      then have t2_r : "(x = ax \<and> (\<exists> s2 . (s,ax,ay,s2) \<in> transitions M \<and> is_atc_reaction M s2 t2 io2))"
        using Some is_atc_reaction.simps(4)[of "M" "s" "x" "f" "ax" "ay" "io2"]
        by simp
      
      obtain k2 where k2_def : "has_height t2 k2" by (meson has_height_def height_min_ex not_less)
      then have "length io2 \<le> k2" using Node.IH Some t2_r k2_def by (meson fmran'I)
      moreover have "k2 < k" using Node.prems(2) Some has_height_def k2_def by (meson fmran'I has_height_subtest)
      ultimately show ?thesis using Cons by simp
    qed
  qed
qed


lemma atc_reaction_alphabets :
  assumes wf: "well_formed M"
  and     ir: "is_atc_reaction M s t io"
  shows "\<forall> xy \<in> set io . xy \<in> (inputs M \<times> outputs M)"
using assms proof (induction t arbitrary: s io)
  case Leaf
  have "\<forall> io . is_atc_reaction M s Leaf io \<longrightarrow> io = []" by (metis is_atc_reaction.simps(2) neq_Nil_conv)
  then have "io = []" using Leaf.prems by blast
  then show ?case by simp
next
  case (Node x f)
  then show ?case 
  proof (cases io)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a io2)
    then obtain ax ay where a_def : "a = (ax,ay)" by (meson surj_pair)
    have "is_atc_reaction M s (Node x f) ((ax,ay)#io2)" using Node Cons a_def by blast
    then have "\<exists> s2 . (s,ax,ay,s2) \<in> transitions M"
      using is_atc_reaction.simps(4)[of "M" "s" "x" "f" "ax" "ay" "io2"]
            disjE_realizer2 not_less 
      by fastforce
    then have a_el : "a \<in> (inputs M \<times> outputs M)" using wf a_def transition_contents by fastforce
    show ?thesis 
    proof (cases "(fmlookup f ay)")
      case None
      then have "io2 = []" using a_def Cons Node.prems(2) by auto
      then show ?thesis using a_def a_el Cons by auto
    next
      case (Some t2)
      have "is_atc_reaction M s (Node x f) ((ax,ay)#io2)" using Node Cons a_def by blast
      then have t2_r : "(x = ax \<and> (\<exists> s2 . (s,ax,ay,s2) \<in> transitions M \<and> is_atc_reaction M s2 t2 io2))"
        using Some is_atc_reaction.simps(4)[of "M" "s" "x" "f" "ax" "ay" "io2"]
        by simp
      then have "\<forall> xy \<in> set io2 . xy \<in> (inputs M \<times> outputs M)" using Node.IH Some wf by (meson fmran'I)
      then show ?thesis using a_def a_el Cons by auto
    qed
  qed
qed


lemma atc_io_finite :
  assumes wf: "well_formed M"
  shows "finite (atc_io M s t)"
proof -
  obtain k where k_def : "has_height t k" by (meson has_height_def height_min_ex not_less)
  then have io_k : "\<forall> io . is_atc_reaction M s t io \<longrightarrow> length io \<le> k" using atc_reaction_length by auto
  moreover have io_el : "\<forall> io . is_atc_reaction M s t io \<longrightarrow> (\<forall> xy \<in> set io . xy \<in> (inputs M \<times> outputs M))" 
    by (simp add: wf atc_reaction_alphabets)
  ultimately have sup : "atc_io M s t \<subseteq> { io . (\<forall> xy \<in> set io . xy \<in> (inputs M \<times> outputs M)) \<and> length io \<le> k }"
    using atc_io_def by fastforce
  moreover have "finite (inputs M \<times> outputs M)" using wf by (simp add: ios_finite)
  moreover have "(inputs M \<times> outputs M) \<noteq> {}" using wf ios_finite by auto
  ultimately have "finite { io . (\<forall> xy \<in> set io . xy \<in> (inputs M \<times> outputs M)) \<and> length io \<le> k }" 
    using set_of_lists_finite_lte[of "inputs M \<times> outputs M" "k"] by blast
  then show ?thesis using io_el infinite_super sup by blast
qed

lemma B_finite : 
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     ft: "finite T"
  and     io: "io \<in> language M"
  shows "finite (B M io T)" 
proof -
  obtain q where q_def : "h_y_seq M (initial M) io = {q}" using language_def h_y_seq_observable assms well_formed_def by metis
  then have Beq: "B M io T = atc_io_set M q T" by (simp add: B_def)
  
  have fs: "\<forall> t \<in> T . finite (atc_io M q t)" using wf by (simp add: atc_io_finite)
  then have "finite { atc_io M q t | t . t \<in> T }" 
    using ft by simp
  then have "finite (\<Union> { atc_io M q t | t . t \<in> T })"
    using fs by blast
  moreover have "atc_io_set M q T = \<Union>{ atc_io M q t | t . t \<in> T }" 
    by (simp add: atc_io_set_def)
  ultimately show ?thesis using B_def Beq by simp
qed

lemma D_alt_def :
  "D M T ISeqs = image (\<lambda> io . B M io T) (\<Union> (image (language_state_in M (initial M)) ISeqs))"
proof -
  let ?orig = "{ io . \<exists> iseq \<in> ISeqs . io \<in> language_state_in M (initial M) iseq }"
  let ?alt = "\<Union> (image (language_state_in M (initial M)) ISeqs)"
  have alt_def : "?orig = ?alt" by (simp add: UNION_eq)
  have "D M T ISeqs = image (\<lambda> io . B M io T) ?orig" by (simp add: D_def setcompr_eq_image)
  then show "D M T ISeqs = image (\<lambda> io . B M io T) ?alt" using alt_def by auto
qed

lemma D_finite : 
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     fi: "finite ISeqs"
  shows "finite (D M T ISeqs)" 
proof -
  let ?orig = "{ io . \<exists> iseq \<in> ISeqs . io \<in> language_state_in M (initial M) iseq }"
  let ?alt = "\<Union> (image (language_state_in M (initial M)) ISeqs)"
  
  have "\<forall> iseq \<in> ISeqs . finite (language_state_in M (initial M) iseq)" 
    using language_state_in_finite[of "M" "initial M"] wf ob by (simp add: well_formed_def) 
  then have fa: "finite ?alt" using fi by blast
   
  have alt_def : "?orig = ?alt" by (simp add: UNION_eq)

  have "D M T ISeqs = image (\<lambda> io . B M io T) ?orig" by (simp add: D_def setcompr_eq_image)
  then have "D M T ISeqs = image (\<lambda> io . B M io T) ?alt" using alt_def by auto
  moreover have "finite (image (\<lambda> io . B M io T) ?alt)" using fa by blast
  ultimately show ?thesis by simp
qed

lemma singleton_image_card :
  assumes "S = {s}"
  shows "card (image f S) = 1"
  using assms by simp

lemma D_bound :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     fi: "finite ISeqs"
  shows "card (D M T ISeqs) \<le> card (states M)" 
proof -
  (* 
  Idea: 
    D produces only responses of states in M to T, 
    thus it is sufficient to show that D produces
    a subset of the set of reactions of all states 
    in M to T
  *)
  let ?dom = "{ io . \<exists> iseq \<in> ISeqs . io \<in> language_state_in M (initial M) iseq }" 
  let ?dom2 = "{ io . \<exists> iseq . io \<in> language_state_in M (initial M) iseq }"
  let ?dm_sub = "image (\<lambda> io . B M io T) (language_state M (initial M))"
  have "?dom \<subseteq> ?dom2" by blast
  moreover have "?dom2 \<subseteq> language_state M (initial M)" by (simp add: language_state_in_def)
  ultimately have "?dom \<subseteq> language_state M (initial M)" by blast
  then have dm_sub : "D M T ISeqs \<subseteq> ?dm_sub" 
    by (smt D_def Setcompr_eq_image mem_Collect_eq subset_iff)

  have io_s :"\<forall> io \<in> language_state M (initial M) . \<exists> s \<in> states M .  h_y_seq M (initial M) io = {s}"
  proof 
    fix io
    assume io_assm : "io \<in> language_state M (initial M)"
    then show "\<exists> s \<in> states M .  h_y_seq M (initial M) io = {s}" 
      by (meson wf ob well_formed_def h_y_seq_observable)
  qed

  let ?dm_sub2 = "image (\<lambda> s . atc_io_set M s T) (states M)"
  have "?dm_sub \<subseteq> ?dm_sub2"
  proof
    fix resp
    assume resp_assm : "resp \<in> (\<lambda>io. B M io T) ` language_state M (initial M)"
    show "resp \<in> image (\<lambda> s . atc_io_set M s T) (states M)"
    proof -
      obtain io where io_def : "io \<in> language_state M (initial M) \<and> B M io T = resp" using resp_assm by auto
      then obtain q where q_def : "q \<in> states M \<and>  h_y_seq M (initial M) io = {q}" using io_s resp_assm by auto
      then have "resp = \<Union> (image (\<lambda> s . atc_io_set M s T) {q})" by (metis B_def io_def)
      then have "resp = atc_io_set M q T" by blast
      then show "resp \<in> image (\<lambda> s . atc_io_set M s T) (states M)" using q_def by auto
    qed
  qed
  then have "D M T ISeqs \<subseteq> ?dm_sub2" using dm_sub by blast
  moreover have "card ?dm_sub2 \<le> card (states M)" using card_image_le  wf well_formed_def by blast
  ultimately show "card (D M T ISeqs) \<le> card (states M)" by (meson card_mono dual_order.trans finite_imageI local.wf well_formed_def)
qed

lemma D_bound_subset :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     fi: "finite ISeqs"
  and     sb: "S \<subseteq> D M T ISeqs"
shows "card S \<le> card (states M)" 
  by (metis (no_types, lifting) assms D_bound D_finite card_mono dual_order.trans)





  
definition append_io_B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in * 'out) list set" where
"append_io_B M io \<Omega> \<equiv> { io@res | res . res \<in> B M io \<Omega> }"

definition is_reduction_on :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'in list \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"is_reduction_on M1 M2 iseq \<Omega> \<equiv> 
  language_in M1 iseq \<subseteq> language_in M2 iseq 
  \<and> (\<forall> io \<in> language_in M1 iseq . append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>)"

definition is_reduction_on_sets :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"is_reduction_on_sets M1 M2 TS \<Omega> \<equiv> \<forall> iseq \<in> TS . is_reduction_on M1 M2 iseq \<Omega>"


lemma language_state_alt_def :
  "language_state M q =  image get_io {seq . is_enabled_sequence M q seq }"
  using language_state_def by (metis setcompr_eq_image)

lemma language_state_nil :
  "[] \<in> language_state M q"
proof -
  have "is_enabled_sequence M q []"
    using is_enabled_sequence.simps(1) by auto
  moreover have "get_io [] = []" by (simp add: get_io_def)
  ultimately have "[] \<in> image get_io {seq . is_enabled_sequence M q seq }"
    by (metis CollectI image_eqI)
  then show ?thesis using language_state_alt_def[of "M" "q"] by auto
qed


lemma atc_reaction_el :
  assumes "is_atc_reaction M q t io"
  shows "io \<in> language_state M q"
using assms proof (induction t arbitrary: q io)
  case Leaf
  then have "io = []" using is_atc_reaction.simps(2) by (metis list.exhaust)
  then show ?case using language_state_nil by auto  
next
  case (Node x f)
  
  then show ?case
  proof (cases io)
    case Nil
    then show ?thesis using language_state_nil by auto
  next
    case (Cons xy io2)
    then obtain xi yi where head_split : "xy = (xi,yi)" by fastforce
    then show ?thesis 
    proof (cases "fmlookup f yi")
      case None
      then have reaction : "io2 = [] \<and> (\<exists> s2 . (q,xi,yi,s2) \<in> transitions M)"
        using 
          is_atc_reaction.simps(4) 
          Cons Node.prems trans_def head_split
        by simp
      then have io_eq : "io = [(xi,yi)]" using Cons head_split by simp
      obtain s2 where s2_def : "(q,xi,yi,s2) \<in> transitions M" using reaction by auto
      then have "is_enabled_sequence M q [(q,xi,yi,s2)]" using is_enabled_sequence.simps by auto
      moreover have "get_io [(q,xi,yi,s2)] = io" using io_eq by (simp add: get_io_def)
      ultimately show ?thesis using Cons language_state_def
        by fastforce
    next
      case (Some t)
      then have reaction : "\<exists> s2 . (q,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 t io2"
        using 
          is_atc_reaction.simps(4) 
          Cons Node.prems trans_def head_split
        by simp
      then obtain s2 where s2_def : "(q,xi,yi,s2) \<in> transitions M \<and> is_atc_reaction M s2 t io2"
        by auto
      then have "io2 \<in> language_state M s2" using Node.IH Some 
        by (meson fmran'I)
      then obtain seq2 where seq2_def : "get_io seq2 = io2 \<and> is_enabled_sequence M s2 seq2"
        unfolding language_state_def by auto
      then have "is_sequence M ((q,xi,yi,s2)#seq2)"
      proof (cases seq2)
        case Nil
        then show ?thesis using is_sequence.simps s2_def by auto
      next
        case (Cons a seq3)
        then have "t_source a = s2" 
          using seq2_def s2_def is_enabled_sequence.simps(2)[of "M" "s2" "a" "seq3"]
          by auto
        moreover have "t_target (q,xi,yi,s2) = s2" by auto
        ultimately show ?thesis 
          using seq2_def s2_def Cons is_enabled_sequence.simps(2)[of "M" "s2" "a" "seq3"] is_sequence.simps(3)[of "M" "(q,xi,yi,s2)" "a" "seq3"]
          by auto
      qed  
      then have "is_enabled_sequence M q ((q,xi,yi,s2)#seq2)" by auto
      moreover have "get_io ((q,xi,yi,s2)#seq2) = (xi,yi)#io2"
        using seq2_def Cons by (simp add: get_io_def)
      moreover have "get_io ((q,xi,yi,s2)#seq2) = io"
        using Cons head_split calculation by auto
      ultimately show ?thesis 
        using language_state_def[of "M" "q"] by blast
    qed
  qed
qed


lemma atc_io_subset :
  "atc_io M q t \<subseteq> language_state M q"
  using atc_reaction_el atc_io_def by fastforce

lemma union_of_subsets :
  assumes "\<forall> s \<in> S . s \<subseteq> T"
  shows "\<Union> S \<subseteq> T"
  using assms by (simp add: Union_least)



lemma atc_io_set_subset :
  "atc_io_set M q T \<subseteq> language_state M q"
  unfolding atc_io_set_def
  using atc_io_subset union_of_subsets by fastforce

lemma B_language_in :
  assumes "h_y_seq M (initial M) io = {q}"
  shows "B M io \<Omega> \<subseteq> language_state M q"
proof -
  have "B M io \<Omega> = \<Union> (image (\<lambda> s . atc_io_set M s \<Omega>) {q})"
    using assms by (simp add: B_def)
  then have "B M io \<Omega> = atc_io_set M q \<Omega>"
    by auto
  moreover have "atc_io_set M q \<Omega> \<subseteq> language_state M q"
    using atc_io_set_subset by fastforce
  ultimately show ?thesis by auto
qed

lemma enabled_subsequence :
  assumes "is_enabled_sequence M s1 (Cons a seq1)"
shows "is_enabled_sequence M (t_target a) seq1"
using assms proof (induction seq1)
  case Nil
  then show ?case by auto
next
  case (Cons b seq1)
  then have is_seq1 : "is_sequence M (Cons a (Cons b seq1))" using Cons 
    by (metis is_enabled_sequence.elims(2) is_sequence.simps(1))
  then have is_seq2 : "is_sequence M (Cons b seq1)" using Cons 
    by (metis is_sequence.simps(3))

  have "t_target a = t_source b" 
    using Cons is_seq1 is_seq2 is_enabled_sequence.simps 
    by auto
    
  then show ?case using is_seq2 by auto
qed

lemma reaches_subsequence : 
  assumes "reaches M s1 (Cons a seq) s2"
shows "reaches M (t_target a) seq s2"
proof - (* auto-gen *)
  obtain pp :: "('c \<times> 'a \<times> 'b \<times> 'c) list \<Rightarrow> 'c \<times> 'a \<times> 'b \<times> 'c" and pps :: "('c \<times> 'a \<times> 'b \<times> 'c) list \<Rightarrow> ('c \<times> 'a \<times> 'b \<times> 'c) list" where
    f1: "(seq = [] \<or> seq = pp seq # pps seq) \<and> (seq \<noteq> [] \<or> (\<forall>p ps. seq \<noteq> p # ps))"
    by (metis (no_types) neq_Nil_conv)
  { assume "reaches M (t_target (last (a # seq))) [] (t_target (last (a # seq))) \<noteq> reaches M (t_target a) seq s2"
    then have "seq \<noteq> []"
      using assms by force
    then have ?thesis
      using f1 by (metis (no_types) assms enabled_subsequence last.simps reaches.simps(2)) }
  then show ?thesis
    by fastforce
qed

lemma enabled_sequences_append :
  assumes "is_enabled_sequence M s1 seq1"
  and     "reaches M s1 seq1 s2"
  and     "is_enabled_sequence M s2 seq2"
shows "is_enabled_sequence M s1 (seq1@seq2)"
using assms proof (induction seq1 arbitrary: s1)
  case Nil
  then have "s1 = s2" using reaches.simps(1) by auto
  then show ?case using Nil by auto
next
  case (Cons a seq1)
  then have "is_enabled_sequence M s1 [a]" 
    using is_sequence.elims(2) by auto
  then have a_el : "a \<in> transitions M" 
    using is_enabled_sequence.simps is_sequence.simps
    by auto
  
  have "is_enabled_sequence M (t_target a) seq1"
    using Cons enabled_subsequence[of "M" "s1" "a" "seq1"]
    by auto
  moreover have "reaches M (t_target a) seq1 s2"
    using Cons reaches_subsequence[of "M" "s1" "a" "seq1" "s2"] 
    by auto
  ultimately have en12 : "is_enabled_sequence M (t_target a) (seq1@seq2)"
    using Cons.IH[of "(t_target a)"] Cons 
    by auto
  
  have "is_sequence M (Cons a (seq1@seq2))"
  proof (cases "seq1@seq2")
    case Nil
    then show ?thesis using a_el by auto
  next
    case (Cons b list)
    have seq12 : "is_sequence M (seq1@seq2)"
      using en12
      by (metis is_enabled_sequence.elims(2) is_sequence.simps(1))
    moreover have "t_source b = t_target a"
      using en12 is_sequence.simps Cons
      by simp
    ultimately show ?thesis using is_sequence.simps Cons a_el by auto
  qed
  moreover have "t_source a = s1"
    using Cons by auto
  ultimately show ?case by auto
qed






lemma append_io_B_subset :
  assumes "io \<in> language M"
  shows "append_io_B M io \<Omega> \<subseteq> language M"
proof 
  fix iores
  assume res_assm : "iores \<in> append_io_B M io \<Omega>"
  then obtain res where res_def : "iores = io@res \<and> res \<in> B M io \<Omega>"
    unfolding append_io_B_def
    by auto
  then obtain s2 where s2_def : "s2 \<in> h_y_seq M (initial M) io \<and> res \<in> atc_io_set M s2 \<Omega>"
    unfolding B_def
    by auto
  then have res_el : "res \<in> language_state M s2"
    using atc_io_set_subset[of "M" "s2" "\<Omega>"]
    by auto
  then obtain seqRES where seqRES_def : "is_enabled_sequence M s2 seqRES \<and> get_io seqRES = res"
    using language_state_def[of "M" "s2"]
    by auto

  moreover obtain seqIO where seqIO_def : "is_enabled_sequence M (initial M) seqIO \<and>
      reaches M (initial M) seqIO s2 \<and> get_io seqIO = io"
    using s2_def h_y_seq.simps[of "M" "(initial M)" "io"] 
    by auto

  ultimately have en: "is_enabled_sequence M (initial M) (seqIO@seqRES)"
    using enabled_sequences_append[of "M" "initial M" "seqIO" "s2" "seqRES"]
    by auto

  have "get_io (seqIO@seqRES) = (get_io seqIO)@(get_io seqRES)"
    by (simp add: get_io_def)
  then have "get_io (seqIO@seqRES) = iores"
    using seqRES_def seqIO_def res_def by auto

  then have "iores \<in>  image get_io {seq . is_enabled_sequence M (initial M) seq }"
    using en by auto
  then show "iores \<in> language M" 
    using language_state_alt_def[of "M" "initial M"] language_def[of "M"]  by auto 
qed


lemma enabled_sequence_prefix : 
  assumes "is_enabled_sequence M s (seq1@seq2)"
  shows "is_enabled_sequence M s seq1"
using assms proof (induction seq1 arbitrary: seq2)
  case Nil
  then show ?case by auto
next
  case (Cons a seq1)
  then show ?case sorry (* TODO *)
qed

lemma language_reached_state :
  assumes "h_y_seq M (initial M) io = {q}"
  and     "io@ext \<in> language M"
shows     "ext \<in> language_state M q"
proof -
  obtain seqIO where seqIO_def : "is_enabled_sequence M (initial M) seqIO \<and> reaches M (initial M) seqIO q \<and> get_io seqIO = io" 
    using assms h_y_seq.simps[of "M" "initial M" "io"] by auto
  obtain seqIOExt where seqIOExt_def : "is_enabled_sequence M (initial M) seqIOExt \<and> get_io seqIOExt = io@ext"
    using assms(2) language_def[of "M"] language_state_def[of "M" "initial M"] by auto

  have "length (io@ext) \<ge> length io"
    by auto
  moreover have ln_io : "length seqIO = length (io)"
    using seqIO_def by (simp add: get_io_length)
  moreover have "length seqIOExt = length (io@ext)"
    using seqIOExt_def by (simp add: get_io_length)
  ultimately have ln: "length seqIOExt \<ge> length seqIO"
    by auto

  let ?seqIO2 = "take (length seqIO) seqIOExt"
  have "length seqIO = length ?seqIO2"
    using ln by auto
  moreover have "get_io ?seqIO2 = take (length seqIO) (io@ext)"
    using ln seqIOExt_def get_io_def by (metis (no_types, lifting) take_map)
  ultimately have io2 : "get_io ?seqIO2 = io"
    using ln ln_io by auto


  then have "is_enabled_sequence M (initial M) ?seqIO2"
    using seqIOExt_def is_enabled_sequence.simps by sledgehamme
  then have "reaches M (initial M) ?seqIO2 q"

end (*
lemma test :
  assumes "h_y_seq M1 (initial M1) io = {q1}"
  and     "h_y_seq M2 (initial M2) io = {q2}"
  and     "M1 \<preceq> M2"
shows "language_state M1 q1 \<subseteq> language_state M2 q2"
proof 
  obtain seq1 where seq1_def : "is_enabled_sequence M1 (initial M1) seq1 \<and> reaches M1 (initial M1) seq1 q1 \<and> get_io seq1 = io" 
    using assms h_y_seq.simps[of "M1" "initial M1" "io"] by auto
  obtain seq2 where seq2_def : "is_enabled_sequence M2 (initial M2) seq2 \<and> reaches M2 (initial M2) seq2 q2 \<and> get_io seq2 = io" 
    using assms h_y_seq.simps[of "M2" "initial M2" "io"] by auto
  
  fix ext
  assume ext_assm : "ext \<in> language_state M1 q1"

  then obtain suf1 where suf1_def : "is_enabled_sequence M1 q1 suf1 \<and> get_io suf1 = ext"
    using language_state_def[of "M1" "q1"] by auto
  moreover have "reaches M1 (initial M1) seq1 q1"
    using seq1_def by auto
  ultimately have "is_enabled_sequence M1 (initial M1) (seq1@suf1)"
    using seq1_def enabled_sequences_append[of "M1" "initial M1" "seq1" "q1" "suf1"] by auto
  moreover have "get_io (seq1@suf1) = io@ext"
    using seq1_def suf1_def by (simp add: get_io_def)
  ultimately have "io@ext \<in>  image get_io {seq . is_enabled_sequence M1 (initial M1) seq }"
    by (metis CollectI image_eqI)
  then have lang1_el : "io@ext \<in> language M1" 
    using language_state_alt_def[of "M1" "initial M1"] language_def[of "M1"]  by auto

  show "ext \<in> language_state M2 q2"
  proof (rule ccontr)
    assume ext_assm_c : "ext \<notin> language_state M2 q2"
    then have "io@ext \<notin> language M2"  

end (*
lemma is_reduction_on_reverse : 
  assumes rd: "M1 \<preceq> M2"
  shows "is_reduction_on M1 M2 t \<Omega>"
proof -
  have lr : "language_in M1 t \<subseteq> language_in M2 t"
    using rd reduction_in_subset by auto
  (*moreover have "(\<forall> io \<in> language_in M1 t . append_io_B M1 io \<Omega> \<subseteq> language M1)"
    using append_io_B_subset language_in_subset by blast 
  moreover have "(\<forall> io \<in> language_in M2 t . append_io_B M2 io \<Omega> \<subseteq> language M2)"
    using append_io_B_subset language_in_subset by blast 
  ultimately *)
  have "(\<forall> io \<in> language_in M1 t . append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>)"
  proof 
    fix io
    assume io_assm : "io \<in> language_in M1 t"
    show "append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>"
    

lemma is_reduction_reverse :
  assumes rd: "M1 \<preceq> M2"
  shows "is_reduction_on_sets M1 M2 TS \<Omega>"

end