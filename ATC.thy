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
"size (Node x f) = Max ( image size (fmran' f) )"
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
where "atc_io M s T = { io . is_atc_reaction M s T io }"
  

lemma io_dist :
  assumes io_diff : "act_io M s1 \<noteq> act_io M s2"
  shows "s1 \<noteq> s2"
  using io_diff by auto

definition atc_dist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_dist M T s1 s2 \<equiv> atc_io M s1 T \<noteq> atc_io M s2 T"

definition atc_rdist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"atc_rdist M T s1 s2 \<equiv> atc_io M s1 T \<inter> atc_io M s2 T = {}"


lemma atc_rdist_dist :
  assumes wf1 : "well_formed M1"
  assumes wf2 : "well_formed M2"
  assumes ob1 : "observable M1"
  assumes ob2 : "observable M2"
  assumes el_s1 : "s1 \<in> states M1"
  assumes el_s2 : "s2 \<in> states M1"
  assumes el_t1 : "t1 \<in> states M2"
  assumes el_t2 : "t2 \<in> states M2"
  assumes red1 : "io_reduction_state M2 t1 M1 s1"
  assumes red2 : "io_reduction_state M2 t2 M1 s2"
  assumes rdist: "atc_rdist M1 T s1 s2"
  shows "atc_dist M2 T t1 t2"
  oops






(*
TODO:
- concat ATCs (for alphabet Y)
- input list \<rightarrow> ATC (for alphabet Y)
*)

end