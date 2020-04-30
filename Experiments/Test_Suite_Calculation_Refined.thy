theory Test_Suite_Calculation_Refined
  imports Test_Suite_Calculation 
          "HOL-Library.Product_Lexorder"
          HOL.Record
          Deriving.Compare
          Containers.Containers
          "HOL-Library.Code_Target_Nat"
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
derive (no) ccompare fsm
print_derives




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
definition "finite_UNIV = Phantom(('a,'b,'c)fsm) False"


lemma infinite_UNIV_fsm : 
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
            (simp add: finite_UNIV_fsm_def infinite_UNIV_fsm) 
end


instantiation fsm :: (infinite_UNIV,type,type) card_UNIV begin
definition "card_UNIV = Phantom(('a,'b,'c) fsm) 0" 

instance by (intro_classes) (simp add: infinite_UNIV_fsm card_UNIV_fsm_def)
end



instantiation fsm :: (infinite_UNIV,type,type) cproper_interval begin
definition cproper_interval_fsm :: "(('a,'b,'c) fsm) proper_interval" 
  where "cproper_interval_fsm _ _ = undefined"
instance by(intro_classes)(simp add: infinite_UNIV_fsm)
end










subsection \<open>Updating Code Equations\<close>

subsubsection \<open>New Code Generation for set_as_map\<close>

declare [[code drop: set_as_map]]

lemma set_as_map_code_refined[code] :
  fixes t :: "('a :: ccompare \<times> 'c :: ccompare) set_rbt" 
  and   xs:: "('b :: ceq \<times> 'd :: ceq) set_dlist"
  shows "set_as_map (RBT_set t) = (case ID CCOMPARE(('a \<times> 'c)) of
           Some _ \<Rightarrow> Mapping.lookup (RBT_Set2.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (RBT_set t)))"
    (is "?C1")
  and   "set_as_map (DList_set xs) = (case ID CEQ(('b \<times> 'd)) of
            Some _ \<Rightarrow> Mapping.lookup (DList_Set.fold (\<lambda> (x,z) m . case Mapping.lookup m (x) of
                        None \<Rightarrow> Mapping.update (x) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)
                      xs
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (DList_set xs)))"
    (is "?C2")
proof -
  show ?C1
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

  show ?C2
  proof (cases "ID CEQ(('b \<times> 'd))")
    case None
    then show ?thesis by auto
  next
    case (Some a)
    
    let ?f' = "(\<lambda> t' . (DList_Set.fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                             t'
                             Mapping.empty))"
   
    let ?f = "\<lambda> xs . (fold (\<lambda> (x,z) m . case Mapping.lookup m x of
                                                  None \<Rightarrow> Mapping.update x {z} m |
                                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) m)
                            xs Mapping.empty)"
    have *: "\<And> xs :: ('b \<times> 'd) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> set xs) then Some {z . (x,z) \<in> set xs} else None)"
    proof - 
      fix xs :: "('b \<times> 'd) list"
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

    have "ID CEQ('b \<times> 'd) \<noteq> None"
      using Some by auto
    then have **: "\<And> x . x \<in> set (list_of_dlist xs) = (x \<in> (DList_set xs))" 
      using DList_Set.member.rep_eq[of xs]
      using Set_member_code(2) ceq_class.ID_ceq in_set_member by fastforce 
    
    have "Mapping.lookup (?f' xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> (DList_set xs)) then Some {z . (x,z) \<in> (DList_set xs)} else None)"
      using *[of "(list_of_dlist xs)"] 
      unfolding DList_Set.fold.rep_eq ** by assumption
    then show ?thesis unfolding set_as_map_def using Some by simp
  qed
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






subsection \<open>Some Manual Common Subexpression Elimination\<close>

lemma[code] :
  fixes M :: "('a::linorder,'b::linorder,'c::linorder) fsm"
  shows 
  "calculate_test_suite_example M m = undefined"


  unfolding calculate_test_suite_example_def 
            Let_def 
            combine_test_suite_def
            d_reachable_states_with_preambles_def
            calculate_state_preamble_from_input_choices.simps
            calculate_test_paths_def
            m_traversal_paths_with_witness_def
            m_traversal_paths_with_witness_up_to_length_def
            paths_up_to_length_or_condition_with_witness_code
            d_states.simps
            maximal_repetition_sets_from_separators_list_def
            reachable_nodes_as_list.simps
            reachable_nodes_code
            acyclic_paths_up_to_length_code
maximal_pairwise_r_distinguishable_state_sets_from_separators_code
maximal_pairwise_r_distinguishable_state_sets_from_separators_list_def
pairwise_r_distinguishable_state_sets_from_separators_list_def
preamble_pair_tests.simps
preamble_prefix_tests_code
prefix_pair_tests_code

end (*


subsection \<open>Exports\<close>

definition generate_test_suite :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list set" where
  "generate_test_suite M m = calculate_test_suite_example_as_io_sequences M (nat_of_integer m)"


export_code generate_test_suite m_ex_H m_ex_9 m_ex_DR in Haskell module_name FSM
(*
definition generate_test_suite :: "(integer,integer,integer) fsm \<Rightarrow> integer \<Rightarrow> (integer\<times>integer) list set" where
  "generate_test_suite M m = 
   (let m' = (if m > 0 then Nat m else 0)
    in calculate_test_suite_example_as_io_sequences M m')"
*)




end