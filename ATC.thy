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
  then show ?case by auto
next
  case (Cons a seq2)
  obtain xy io2 where io_split : "io = xy # io2" using get_io_length by (metis Cons.prems(2) length_Suc_conv)
  then have "io2 = get_io seq2" using Cons.prems(2) get_io.elims by auto
  then have el2 : "\<forall> x \<in> set io2 . x \<in> (inputs M \<times> outputs M)" using Cons.IH by (simp add: Cons.prems(1))

  
  obtain s1 x y s2 where a_def : "a = (s1,x,y,s2)" using local.Cons(2) by auto
  then have "xy = (x,y)" using io_split Cons a_def by simp
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
      

lemma D_finite : 
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     ft: "finite T"
  and     fi: "finite ISeqs"
  shows "finite (D M T ISeqs)" 
proof -
  
  

lemma D_bound :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     ft: "finite T"
  and     fi: "finite ISeqs"
  shows "card (D M T ISeqs) \<le> card (states M)" 
proof -  

(* ************************* Input Seq to ATC ******************************

fun restrict_fset :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> 'b option)"  where
"restrict_fset m xs = restrict_map m (fset xs)"

fun map_of_fset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> 'b option)"  where
"map_of_fset f xs = restrict_fset (\<lambda> x . Some (f x)) xs"

lemma finite_restrict_fset : "finite (dom (restrict_fset m xs))"
proof -
  have "finite (fset xs)" by simp
  then show ?thesis by simp
qed

lemma finite_map_of_fset : "finite (dom (map_of_fset f xs))"
  using finite_restrict_fset by simp

fun fmap_of_fset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a, 'b) fmap"  where
"fmap_of_fset f xs = Abs_fmap (map_of_fset f xs)"

fun to_atc :: "'in list \<Rightarrow> 'out fset \<Rightarrow> ('in, 'out) ATC" where
"to_atc [] _ = Leaf" |
"to_atc (x#xs) os = (Node x (fmap_of_fset (\<lambda> _ . to_atc xs os) os))"


fun map_of_fset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> 'b option)"  where
"map_of_fset f xs = (\<lambda> x . (if (x \<in> fset xs)
                      then Some (f x)
                      else None))"

fun fmap_of_fset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> ('a, 'b) fmap"  where
"fmap_of_fset f xs = Abs_fmap (map_of_fset f xs)"

fun to_atc :: "'in list \<Rightarrow> 'out fset \<Rightarrow> ('in, 'out) ATC" where
"to_atc [] _ = Leaf" |
"to_atc (x#xs) os = Node x (Abs_fmap (map_of (image (\<lambda> y . (y,to_atc xs os)) (fset os))))"



lemma test : "finite xs \<Longrightarrow> \<exists> fxs . xs = fset fxs"
  using fset_to_fset by auto

lemma test2 : "\<exists> fxs . xs = fset fxs \<Longrightarrow> finite xs"
  using finite_fset by blast


fun apply_io_atc :: "('in,'out) ATC \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in,'out) ATC option" where
"apply_io_atc Leaf [] = Some Leaf" |
"apply_io_atc Leaf io = None" |
"apply_io_atc (Node x f) [] = None" |
"apply_io_atc (Node x f) ((x1,y1)#io) = (if (x = x1)
  then (case (fmlookup f y1) of 
    Some a \<Rightarrow> apply_io_atc a io |
    None   \<Rightarrow> apply_io_atc Leaf io) 
  else None)"

lemma reached_atc :
  assumes io: "io \<in> atc_io M s t"
  shows "apply_io_atc t io = Some t2 \<and> t2 


lemma to_atc_nil : "atc_io M s Leaf = {Nil}"
proof -
  have "\<forall> seq . is_atc_reaction M s Leaf seq \<longrightarrow> length seq = 0" by (metis is_atc_reaction.simps(2) list.size(3) neq_Nil_conv)
  then have "\<forall> seq \<in> atc_io M s Leaf . length seq = 0" by (simp add: atc_io_def)
  moreover have "{Nil} \<subseteq> atc_io M s Leaf" by (simp add: atc_io_def)
  ultimately show ?thesis by blast
qed


lemma language_seq_atc :
  assumes io: "io \<in> atc_io M s (to_atc iseq fouts)"
  and     fo: "fset fouts = outputs M"
shows "io \<in> language_state_i M s iseq"
using assms proof (induction iseq arbitrary: io s)
  case Nil
  then have "to_atc Nil fouts = Leaf" by simp
  then have nil_atc : "{Nil} = atc_io M s (to_atc Nil fouts)" by (simp add: to_atc_nil)
  moreover have "{Nil} \<subseteq> language_state_i M s []" by (simp add: language_state_i_nil)
  ultimately show ?case using Nil.prems(1) by auto 
next
  case (Cons a iseq)
  then show ?case sorry
qed



lemma language_seq_atc :
  assumes ln: "io \<in> language_state_i M s iseq"
  and     fo: "fset fouts = outputs M"
  and     tc: "t = to_atc iseq fouts"
  shows "io \<in> atc_io M s t"
using assms proof (induction iseq)
  case Nil
  then have "to_atc Nil fouts = Leaf" by simp
  then have "t = Leaf" by (simp add: Nil.prems(3))
  then have nil_atc : "Nil \<in> atc_io M s t" by (simp add: atc_io_def)
  have "{Nil} \<subseteq> language_state_i M s []" by (simp add: language_state_i_nil)
  then have "io = Nil" using Nil.prems(1) language_state_i_nil by fastforce
  then show ?case using nil_atc by simp
next
  case (Cons a iseq)
  then show ?case sorry
qed
  

*)


















(*
TODO:
- concat ATCs (for alphabet Y)
- input list \<rightarrow> ATC (for alphabet Y)
*)

end