theory Test_Suite_Calculation_Refined
  imports Test_Suite_Calculation 
          "HOL-Library.Product_Lexorder"
          HOL.Record
          Deriving.Compare
          Containers.Containers
          Containers.Card_Datatype
begin

subsection \<open>New Instances\<close>


(*

(* TODO: linear order on FSMs can be created using set_less_aux or similar functions, as all
         contained sets are finite - but this is probably not that efficient/necessary,
         as sets of FSMs only occur at one point in the algorithm (collecting ATCs to append
         after the same path), after which the FSMs are translated to path sets anyway.
         Still, the instantiation can be made later to profile whether it has any positive
         effect on performance.
*)
instantiation fsm :: (ord,ord,ord) ord
begin

fun less_eq_fsm ::  "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "less_eq_fsm M1 M2 = 
    (if initial M1 < initial M2 
      then True
      else ((initial M1 = initial M2) \<and> (if set_less_aux (nodes M1)  (nodes M2)
        then True
        else ((nodes M1 = nodes M2) \<and> (if set_less_aux (inputs M1) (inputs M2)
          then True
          else ((inputs M1 = inputs M2) \<and> (if set_less_aux (outputs M1) (outputs M2)
            then True
            else ((outputs M1 = outputs M2) \<and> (set_less_aux (transitions M1) (transitions M2) \<or> (transitions M1) = (transitions M2))))))))))"

fun less_fsm ::  "('a,'b,'c) fsm \<Rightarrow> ('a,'b,'c) fsm \<Rightarrow> bool" where
  "less_fsm a b = (a \<le> b \<and> a \<noteq> b)"

instance by (intro_classes)
end


instantiation fsm :: (linorder,linorder,linorder) linorder
begin



lemma less_le_not_le_FSM :
  fixes x :: "('a,'b,'c) fsm"
  and   y :: "('a,'b,'c) fsm"
shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
proof 
  show "x < y \<Longrightarrow> x \<le> y \<and> \<not> y \<le> x" 
    
   
  proof -
    assume "x < y"
    then show "x \<le> y \<and> \<not> y \<le> x"
    proof (cases "FSM.initial x < FSM.initial y")
      case True
      then show ?thesis unfolding less_fsm.simps less_eq_fsm.simps by auto
    next
      case False
      then have *: "FSM.initial x = FSM.initial y"
        using \<open>x < y\<close> unfolding less_fsm.simps less_eq_fsm.simps by auto
      
      show ?thesis proof (cases "set_less_aux (FSM.nodes x) (FSM.nodes y)")
        case True
        then show ?thesis 
          unfolding less_fsm.simps less_eq_fsm.simps 
          using * set_less_aux_antisym by fastforce
      next
        case False
        then have **: "FSM.nodes x = FSM.nodes y"
          using \<open>x < y\<close> * unfolding less_fsm.simps less_eq_fsm.simps by auto
        
        show ?thesis proof (cases "set_less_aux (FSM.inputs x) (FSM.inputs y)")
          case True
          then show ?thesis 
            unfolding less_fsm.simps less_eq_fsm.simps 
            using * ** set_less_aux_antisym by fastforce
        next
          case False
          then have ***: "FSM.inputs x = FSM.inputs y"
            using \<open>x < y\<close> * ** unfolding less_fsm.simps less_eq_fsm.simps by (simp add: set_less_def)
          
          show ?thesis proof (cases "set_less_aux (FSM.outputs x) (FSM.outputs y)")
            case True
            then show ?thesis 
              unfolding less_fsm.simps less_eq_fsm.simps 
              using * ** *** set_less_aux_antisym by fastforce
          next
            case False
            then have ****: "FSM.outputs x = FSM.outputs y"
              using \<open>x < y\<close> * ** *** unfolding less_fsm.simps less_eq_fsm.simps by (simp add: set_less_def)


            have "x \<noteq> y" using \<open>x < y\<close> by auto
            then have "FSM.transitions x \<noteq> FSM.transitions y"
              using * ** *** **** by (transfer; auto)
            then have *****: "set_less_aux (FSM.transitions x) (FSM.transitions y)"
              using \<open>x < y\<close> * ** *** **** unfolding less_fsm.simps less_eq_fsm.simps by (simp add: set_less_aux_def)

            then have "\<not>(set_less_aux (FSM.transitions y) (FSM.transitions x) \<or> transitions y = transitions x)"
              using \<open>FSM.transitions x \<noteq> FSM.transitions y\<close> fsm_transitions_finite set_less_aux_antisym by auto
            then have "\<not> y \<le> x"
              using * ** *** **** unfolding less_fsm.simps less_eq_fsm.simps 
              by (simp add: set_less_def)
            then show ?thesis using \<open>x < y\<close> 
              using less_fsm.elims(2) by blast
          qed
        qed
      qed
    qed
  qed

  show "x \<le> y \<and> \<not> y \<le> x \<Longrightarrow> x < y"
    using less_fsm.elims(3) by blast
qed

    
lemma order_refl_FSM :
  fixes x :: "('a,'b,'c) fsm"
  shows "x \<le> x" 
  by auto

lemma order_trans_FSM :
  fixes x :: "('a,'b,'c) fsm"
  fixes y :: "('a,'b,'c) fsm"
  fixes z :: "('a,'b,'c) fsm"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  unfolding less_eq_fsm.simps 
  using less_trans[of "initial x" "initial y" "initial z"]
        set_less_aux_trans[of "nodes x" "nodes y" "nodes z"]
        set_less_aux_trans[of "inputs x" "inputs y" "inputs z"]
        set_less_aux_trans[of "outputs x" "outputs y" "outputs z"]
        set_less_aux_trans[of "transitions x" "transitions y" "transitions z"]
  by metis

lemma antisym_FSM :
  fixes x :: "('a,'b,'c) fsm"
  fixes y :: "('a,'b,'c) fsm"
shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  unfolding less_eq_fsm.simps
  using equal_fsm_def[of x y] 
  unfolding equal_class.equal
  by (metis order.asym set_less_aux_antisym)

lemma linear_FSM :
  fixes x :: "('a,'b,'c) fsm"
  fixes y :: "('a,'b,'c) fsm"
shows "x \<le> y \<or> y \<le> x"
  unfolding less_eq_fsm.simps 
  by (metis fsm_inputs_finite fsm_nodes_finite fsm_outputs_finite fsm_transitions_finite neq_iff set_less_aux_finite_total) 


instance 
  using less_le_not_le_FSM order_refl_FSM order_trans_FSM antisym_FSM linear_FSM 
  by (intro_classes; metis+)
end




instantiation fsm :: (linorder,linorder,linorder) compare
begin 
fun compare_fsm :: "('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> order" where
  "compare_fsm x y = comparator_of x y"

instance   
  using comparator_of compare_fsm.elims
  by (intro_classes; simp add: comparator_def)
end


instantiation fsm :: (linorder,linorder,linorder) ccompare
begin
definition ccompare_fsm :: "(('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> order) option" where
  "ccompare_fsm = Some compare"

instance by (intro_classes; simp add: ccompare_fsm_def comparator_compare)
end
*)


subsubsection \<open>Derived Instances\<close>

(* TODO: experiment with different set-impls for fsms *)
derive (eq) ceq fsm

derive (dlist) set_impl fsm
derive (assoclist) mapping_impl fsm

derive (no) cenum fsm

print_derives
derive (no) ccompare fsm
(*derive (rbt) set_impl sum*)

(*derive (no) cproper_interval sum*)

thm finite_UNIV_axioms




subsection \<open>Finiteness and Cardinality Instantiations for FSMs\<close>


(* class to encode the constraint that the types used for FSM elements in the following sections are to be infinite to reduce the
   effort required for instance proofs *)
(* this is not the best idea, see for example https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-July/msg00104.html *)
class infinite_UNIV =
  assumes infinite_UNIV: "infinite (UNIV :: 'a set)"
begin
end

instantiation integer :: infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV_char_0) 
end

(* too restrictive *)
instantiation sum :: (infinite_UNIV,infinite_UNIV) infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV)
end

(* too restrictive *)
instantiation prod :: (infinite_UNIV,infinite_UNIV) infinite_UNIV begin
instance apply intro_classes
  by (simp add: finite_prod infinite_UNIV)  
end



instantiation fsm :: (infinite_UNIV,type,type) finite_UNIV begin
definition "finite_UNIV = Phantom(('a::infinite_UNIV,'b,'c)fsm) False"


lemma finite_UNIV_fsm : 
  shows "infinite (UNIV :: ('a :: infinite_UNIV,'b,'c) fsm set)"
proof -
  (* if infinitely many states exist, then infinitely many distinct singleton fsms can be created *)
  define f :: "'a \<Rightarrow> ('a,'b,'c) fsm" where f_def: "f = (\<lambda> q . fsm_from_list q [])"
  have "inj f" 
  proof 
    fix x y assume "x \<in> (UNIV :: 'a set)" and "y \<in> UNIV" and "f x = f y" 
    then show "x = y" unfolding f_def by (transfer; auto)
  qed
  moreover have "infinite (UNIV :: 'a set)"
    using infinite_UNIV by auto
  ultimately show ?thesis
    by (meson finite_imageD infinite_iff_countable_subset top_greatest) 
qed

instance by (intro_classes)
            (simp add: finite_UNIV_fsm_def finite_UNIV_fsm) 
end



(* in each case: use singletons for the remaining sets and exploit that isabelle types are nonempty *)
lemma f1: 
  assumes "finite (UNIV :: ('a :: infinite_UNIV) set)"
  shows "\<not> finite (UNIV :: ('a,'b,'c) fsm set)"
  sorry (* TODO: show that (\<lambda> <node> \<rightarrow> <FSM using that node as initial state>) is inj on the UNIV of FSMs *)

lemma f2: 
  assumes "finite (UNIV :: 'b set)"
  shows "\<not> finite (UNIV :: ('a,'b,'c) fsm set)"
  sorry (* TODO: show that (\<lambda> <input> \<rightarrow> <FSM using that input in a single transition from initial as nodes>) is inj on the UNIV of FSMs *)

lemma f3: 
  assumes "finite (UNIV :: 'c set)"
  shows "\<not> finite (UNIV :: ('a,'b,'c) fsm set)"
  sorry (* TODO: show that (\<lambda> <output> \<rightarrow> <FSM using that output in a single transition from initial as nodes>) is inj on the UNIV of FSMs *)

lemma f4:
  assumes "finite (UNIV :: ('a::infinite_UNIV,'b,'c) fsm set)"
  shows "False"         
proof -
  have "finite (UNIV :: 'a set)"
    using f1 assms 
  using f1 infinite_UNIV unfolding finite_UNIV

instance 
  apply intro_classes unfolding finite_UNIV_fsm_def  finite_UNIV  using f1 f2 f3 infinite_UNIV 
proof -
have "Phantom(('a, 'b, 'c) fsm) (of_phantom (finite_UNIV::('a, bool) phantom) \<and> of_phantom (finite_UNIV::('b, bool) phantom) \<and> of_phantom (finite_UNIV::('c, bool) phantom)) = (Phantom(('a, 'b, 'c) fsm) (finite (UNIV::('a, 'b, 'c) fsm set))::(('a, 'b, 'c) fsm, bool) phantom)"
  using f1 f2 f3 f4(1) by blast
  then show "Phantom(('a, 'b, 'c) fsm) (of_phantom (Phantom('a) (finite (UNIV::'a set))::('a, bool) phantom) \<and> of_phantom (Phantom('b) (finite (UNIV::'b set))::('b, bool) phantom) \<and> of_phantom (Phantom('c) (finite (UNIV::'c set))::('c, bool) phantom)) = (Phantom(('a, 'b, 'c) fsm) (finite (UNIV::('a, 'b, 'c) fsm set))::(('a, 'b, 'c) fsm, bool) phantom)"
    by (simp add: finite_UNIV_class.finite_UNIV)
  qed 
end



print_classes 

instantiation prod :: (card_UNIV, card_UNIV) card_UNIV begin
definition "card_UNIV = Phantom('a \<times> 'b) 
  (of_phantom (card_UNIV :: 'a card_UNIV) * of_phantom (card_UNIV :: 'b card_UNIV))"
instance by intro_classes (simp add: card_UNIV_prod_def card_UNIV)
end

instantiation fsm :: (card_UNIV,card_UNIV,card_UNIV) card_UNIV begin
definition "finite_UNIV = Phantom(('a,'b,'c)fsm) ((of_phantom (finite_UNIV :: 'a finite_UNIV)) \<and> of_phantom (finite_UNIV :: 'b finite_UNIV) \<and> of_phantom (finite_UNIV :: 'c finite_UNIV))"
definition "card_UNIV = Phantom(XY) 1"

lemma card_univ_XY_props: shows "finite (UNIV :: XY set)" and "card (UNIV :: XY set) = 1"
proof -
  have "UNIV = {X}"
    by (metis (full_types) UNIV_eq_I XY.exhaust insertI1) 
  then show "finite (UNIV :: XY set)"
    using finite.simps by auto 
  show "card (UNIV :: XY set) = 1"
    using \<open>UNIV = {X}\<close>
    using card_eq_1_iff by auto
    
qed

instance 
  by intro_classes 
  (simp_all add: card_univ_XY_props finite_UNIV_XY_def card_UNIV_XY_def)
end


instantiation XY :: cproper_interval begin
definition cproper_interval_XY :: "XY proper_interval"
  where "cproper_interval_XY _ _ = False"

instance apply intro_classes unfolding cproper_interval_XY_def
  by (simp add: ID_None ccompare_XY_def)
end




subsection \<open>Updating Code Equations\<close>

subsubsection \<open>New Code Generation for set_as_map\<close>

declare [[code drop: set_as_map]]

lemma set_as_map_code_refined[code] :
  fixes t :: "('a :: ccompare \<times> 'c :: ccompare) set_rbt" 
  shows "set_as_map (RBT_set t) = (case ID CCOMPARE(('a \<times> 'c)) of
           Some _ \<Rightarrow> Mapping.lookup (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (RBT_set t)))"
proof (cases "ID CCOMPARE(('a \<times> 'c))")
  case None
  then show ?thesis by auto
next
  case (Some a)
  
  let ?f' = "(\<lambda> t' . (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                None \<Rightarrow> Mapping.update x {z} m |
                                                Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                           t'
                           Mapping.empty))"
 
  let ?f = "\<lambda> xs . (fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                None \<Rightarrow> Mapping.update x {z} m |
                                                Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                          xs Mapping.empty)"
  have "\<And> xs :: ('a \<times> 'c) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
  proof - 
    fix xs :: "('a \<times> 'c) list"
    show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case 
        by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq)
    next
      case (snoc xz xs)
      then obtain x z where "xz = (x,z)" 
        by (metis (mono_tags, hide_lams) surj_pair)
  
      have *: "(?f (xs@[(x,z)])) = (case Mapping.lookup (?f xs) x of
                                  None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
        by auto
  
      then show ?case proof (cases "Mapping.lookup (?f xs) x")
        case None
        then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
  
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
  
        have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
          unfolding ** 
          unfolding scheme by force
  
        have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = None"
        using None snoc by auto
        then have "\<not>(\<exists> z . (x,z) \<in> set xs)"
          by (metis (mono_tags, lifting) option.distinct(1))
        then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" and "{z' . (x,z') \<in> set (xs@[(x,z)])} = {z}"
          by fastforce+
        then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                     = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
          by force
        
        show ?thesis using m1 m2 snoc
          using \<open>xz = (x, z)\<close> by presburger
      next
        case (Some zs)
        then have **: "Mapping.lookup (?f (xs@[(x,z)])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
        have m1: "Mapping.lookup (?f (xs@[(x,z)])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
          unfolding ** 
          unfolding scheme by force
  
  
        have "(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs"
          using Some snoc by auto
        then have "(\<exists> z' . (x,z') \<in> set xs)"
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))" by fastforce
  
        have "{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs"
        proof -
          have "Some {z . (x,z) \<in> set xs} = Some zs"
            using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x = Some zs\<close>
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "{z . (x,z) \<in> set xs} = zs" by auto
          then show ?thesis by auto
        qed
  
        have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                   = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a" 
        proof -
          fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x') a"
          using \<open>{z' . (x,z') \<in> set (xs@[(x,z)])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> set (xs@[(x,z)]))\<close>
          by (cases "a = x"; auto)
        qed

        then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> set (xs@[(x,z)])) then Some {z' . (x',z') \<in> set (xs@[(x,z)])} else None)
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None) x')"
          by auto
  
  
        show ?thesis using m1 m2 snoc
          using \<open>xz = (x, z)\<close> by presburger
      qed
    qed
  qed
  then have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set (RBT_Set2.keys t)) then Some {z . (x,z) \<in> set (RBT_Set2.keys t)} else None)"
    unfolding fold_conv_fold_keys by metis
  moreover have "set (RBT_Set2.keys t) = (RBT_set t)" 
    using Some by (simp add: RBT_set_conv_keys) 
  ultimately have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (RBT_set t)) then Some {z . (x,z) \<in> (RBT_set t)} else None)"
    by force
    

  then show ?thesis 
    using Some unfolding set_as_map_def by simp
qed



subsubsection \<open>New Code Generation for remove_proper_prefixes\<close>

declare [[code drop: remove_proper_prefixes]]


lemma remove_proper_prefixes_refined[code] :
  fixes t :: "('a :: ccompare) list set_rbt" 
shows "remove_proper_prefixes (RBT_set t) = (case ID CCOMPARE(('a list)) of
  Some _ \<Rightarrow> (if (is_empty t) then {} else set (paths (from_list (RBT_Set2.keys t)))) |
  None   \<Rightarrow> Code.abort (STR ''remove_proper_prefixes RBT_set: ccompare = None'') (\<lambda>_. remove_proper_prefixes (RBT_set t)))"
  (is "?v1 = ?v2")
proof (cases "ID CCOMPARE(('a list))")
  case None
  then show ?thesis by simp
next
  case (Some a)
  then have *:"ID ccompare \<noteq> (None :: ('a::ccompare list \<Rightarrow> 'a::ccompare list \<Rightarrow> order) option)" by auto
  
  show ?thesis proof (cases "is_empty t")
    case True
    then show ?thesis unfolding Some remove_proper_prefixes_def by auto
  next
    case False
    then have "?v2 = set (paths (from_list (RBT_Set2.keys t)))" using Some by auto
    moreover have "?v1 = set (paths (from_list (RBT_Set2.keys t)))"
      using False unfolding RBT_set_conv_keys[OF *, of t] remove_proper_prefixes_code  by (cases "RBT_Set2.keys t"; auto)
    ultimately show ?thesis by simp
  qed
qed


subsubsection \<open>New Code Generation for r_distinguishable_state_pairs_with_separators\<close>

(*
declare [[show_types]]
  declare [[show_sorts]]
  declare [[show_consts]]
*)

declare [[code drop: r_distinguishable_state_pairs_with_separators]]

value "{(Inr (1::integer,2::integer), Some m_ex_H),(Inr (1,2),Some m_ex_H)} \<union> {(Inl (1::integer,2::integer), Some m_ex_H),(Inr (1,2),Some m_ex_H)}"

lemma r_distinguishable_state_pairs_with_separators_refined[code] :
  fixes M :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  shows  "r_distinguishable_state_pairs_with_separators M = (\<Union> q \<in> {True} . {}::(('a \<times> 'a) \<times> (('a \<times> 'a) + 'a,'b,'c) fsm) set)"
  sorry

code_deps r_distinguishable_state_pairs_with_separators



definition test_ccompare :: "'a::ccompare \<Rightarrow> bool" where 
  "test_ccompare x = (case ID CCOMPARE('a) of Some _ \<Rightarrow> True | None \<Rightarrow> False)"
definition test_cenum :: "'a::cenum \<Rightarrow> bool" where 
  "test_cenum x = (case ID CENUM('a) of Some _ \<Rightarrow> True | None \<Rightarrow> False)"
definition test_ceq :: "'a::ceq \<Rightarrow> bool" where 
  "test_ceq x = (case ID CEQ('a) of Some _ \<Rightarrow> True | None \<Rightarrow> False)"

value "test_ccompare m_ex_H"
value "test_cenum m_ex_H"
value "test_ceq m_ex_H"



definition m_X :: "((integer\<times>integer)+integer,integer,integer) fsm" where
  "m_X = fsm_from_list (Inl (1,1)) [(Inl (1,1), 2, 3, Inr 4)]"


value "test_ccompare m_X"
value "test_cenum m_X"
value "test_ceq m_X"

declare pretty_sets[code_post del]
value "{((1::integer,1::integer), m_X)}"
value "{((1::integer,1::integer), m_X)} \<union> {((1::integer,1::integer), m_X)}"

value "(1::integer,2::integer) < (2::integer,1::integer)"



datatype XY = X

print_derives 
derive (eq) equality XY
derive (eq) ceq XY
derive (no) cenum XY
derive (linorder) comparator XY
derive (linorder) linorder XY
derive (compare) ccompare XY
derive (dlist) set_impl XY
derive (assoclist) mapping_impl XY




instantiation XY :: card_UNIV begin
definition "finite_UNIV = Phantom(XY) True"
definition "card_UNIV = Phantom(XY) 1"

lemma card_univ_XY_props: shows "finite (UNIV :: XY set)" and "card (UNIV :: XY set) = 1"
proof -
  have "UNIV = {X}"
    by (metis (full_types) UNIV_eq_I XY.exhaust insertI1) 
  then show "finite (UNIV :: XY set)"
    using finite.simps by auto 
  show "card (UNIV :: XY set) = 1"
    using \<open>UNIV = {X}\<close>
    using card_eq_1_iff by auto
    
qed

instance 
  by intro_classes 
  (simp_all add: card_univ_XY_props finite_UNIV_XY_def card_UNIV_XY_def)
end


instantiation XY :: cproper_interval begin
definition cproper_interval_XY :: "XY proper_interval"
  where "cproper_interval_XY _ _ = False"

instance apply intro_classes unfolding cproper_interval_XY_def
  by (simp add: ID_None ccompare_XY_def)
end


definition x where "x = finite {X}"

code_deps x
code_thms x

value "{X}"
value "finite ({} :: XY set)


value "(\<lambda> q . {m_ex_H}) {True}"
value "{m_ex_H}"

fun test_dlist :: "'a set \<Rightarrow> nat" where "test_dlist n = 0"
lemma[code] : "test_dlist (DList_set k) = 1" sorry
lemma[code] : "test_dlist (RBT_set k) = 2" sorry

value "test_dlist {m_ex_H}"
value "test_dlist {1::integer}"



value "finite {m_ex_H}"

(* seems to use Collect_set version of finite ? *)
value "\<Union> {{m_ex_H}}"
value "\<Union> q \<in> {True} . {m_ex_H}"

end (*

print_classes

declare pretty_sets[code_post del]
value "\<Union> q \<in> nodes m_ex_H . nodes m_ex_H"
value "state_separator_from_s_states m_ex_H 1 3"
value "{state_separator_from_s_states m_ex_H 1 3, state_separator_from_s_states m_ex_H 1 3}"
value "{state_separator_from_s_states m_ex_H 1 3, state_separator_from_s_states m_ex_H 1 3} \<union> {state_separator_from_s_states m_ex_H 1 3, state_separator_from_s_states m_ex_H 1 3}"
value "\<Union> q \<in> {True} . {1::nat}"
value "\<Union> q \<in> {True} . {m_ex_H}"
value "\<Union> q \<in> {True} . {state_separator_from_s_states m_ex_H 1 3, state_separator_from_s_states m_ex_H 1 3}"
value "(\<lambda> q . {state_separator_from_s_states m_ex_H 1 3, state_separator_from_s_states m_ex_H 1 3}) ` {True}"
value "r_distinguishable_state_pairs_with_separators m_ex_H"

value "{1::integer}"

(*
lemma r_distinguishable_state_pairs_with_separators_code[code] :
  "r_distinguishable_state_pairs_with_separators M = 
    \<Union> (image (\<lambda> ((q1,q2),A) . {((q1,q2),the A),((q2,q1),the A)}) (Set.filter (\<lambda> (qq,A) . A \<noteq> None) (image (\<lambda> (q1,q2) . ((q1,q2),state_separator_from_s_states M q1 q2)) (Set.filter (\<lambda> (q1,q2) . q1 < q2) (nodes M \<times> nodes M)))))"
  (is "?P1 = ?P2")
*)

definition ex07 where "ex07 = calculate_test_suite_example_as_io_sequences m_ex_H 4"



value "calculate_test_suite_example_as_io_sequences m_ex_H 0"

end (*
export_code ex07 in Haskell module_name FSM2


end