section \<open>Refined Test Suite Calculation\<close>

text \<open>This theory refines some of the algorithms defined in @{text "Test_Suite_Calculation"}
      using containser from the Containers framework.\<close>

theory Test_Suite_Calculation_Refined
  imports Test_Suite_Calculation 
          Deriving.Compare
          Containers.Containers
begin



subsection \<open>New Instances\<close>

subsubsection \<open>Order on FSMs\<close>

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
            using \<open>x < y\<close> * ** 
            unfolding less_fsm.simps less_eq_fsm.simps 
            by (simp add: set_less_def)
          
          show ?thesis proof (cases "set_less_aux (FSM.outputs x) (FSM.outputs y)")
            case True
            then show ?thesis 
              unfolding less_fsm.simps less_eq_fsm.simps 
              using * ** *** set_less_aux_antisym 
              by fastforce
          next
            case False
            then have ****: "FSM.outputs x = FSM.outputs y"
              using \<open>x < y\<close> * ** *** 
              unfolding less_fsm.simps less_eq_fsm.simps 
              by (simp add: set_less_def)


            have "x \<noteq> y" using \<open>x < y\<close> by auto
            then have "FSM.transitions x \<noteq> FSM.transitions y"
              using * ** *** **** by (transfer; auto)
            then have *****: "set_less_aux (FSM.transitions x) (FSM.transitions y)"
              using \<open>x < y\<close> * ** *** **** 
              unfolding less_fsm.simps less_eq_fsm.simps 
              by (simp add: set_less_aux_def)

            then have "\<not>(set_less_aux (FSM.transitions y) (FSM.transitions x) \<or> transitions y = transitions x)"
              using \<open>FSM.transitions x \<noteq> FSM.transitions y\<close> fsm_transitions_finite set_less_aux_antisym 
              by auto
            then have "\<not> y \<le> x"
              using * ** *** **** 
              unfolding less_fsm.simps less_eq_fsm.simps 
              by (simp add: set_less_def)
            then show ?thesis using \<open>x < y\<close> 
              using less_fsm.elims(2) 
              by blast
          qed
        qed
      qed
    qed
  qed

  show "x \<le> y \<and> \<not> y \<le> x \<Longrightarrow> x < y"
    using less_fsm.elims(3) 
    by blast
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

(* The above order on FSMs is currently not used in code generation,
   as there are few sets of FSMs and hence on evaluated examples it is
   more efficient to simply store FSMs using d-lists.*)
(*
instantiation fsm :: (linorder,linorder,linorder) ccompare
begin
definition ccompare_fsm :: "(('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> order) option" where
  "ccompare_fsm = Some compare"

instance by (intro_classes; simp add: ccompare_fsm_def comparator_compare)
end
*)


subsubsection \<open>Derived Instances\<close>

derive (eq) ceq fsm

derive (dlist) set_impl fsm
derive (assoclist) mapping_impl fsm

derive (no) cenum fsm
derive (no) ccompare fsm


subsubsection \<open>Finiteness and Cardinality Instantiations for FSMs\<close>

text \<open>The following type class partially encodes infinity of a type.
      This is done as later instantiations assume the universe of FSMs to be infinite, as this
      reduces the effort required to instantiate proper intervals over FSMs.
      This class is not a good idea for any general usage, as many types (e.g. pairs) have
      conflicting instantiations (see for example https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-July/msg00104.html).\<close>
class infinite_UNIV =
  assumes infinite_UNIV: "infinite (UNIV :: 'a set)"
begin
end

instantiation integer :: infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV_char_0) 
end

instantiation nat :: infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV_char_0) 
end

instantiation int :: infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV_char_0) 
end

(* too restrictive *)
instantiation sum :: (infinite_UNIV,type) infinite_UNIV begin
instance apply intro_classes
  by (simp add: infinite_UNIV)
end

(* too restrictive *)
instantiation prod :: (infinite_UNIV,type) infinite_UNIV begin
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




subsection \<open>Updated Code Equations\<close>

subsubsection \<open>New Code Equations for @{text "set_as_map"}\<close>

declare [[code drop: set_as_map]]

lemma set_as_map_refined[code] :
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







subsubsection \<open>New Code Equations for @{text "remove_proper_prefixes"}\<close>

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
      using False unfolding RBT_set_conv_keys[OF *, of t] remove_proper_prefixes_code_trie 
      by (cases "RBT_Set2.keys t"; auto)
    ultimately show ?thesis by simp
  qed
qed












subsubsection \<open>Special Handling for @{text "set_as_map"} on @{text "image"}\<close>


text \<open>Avoid creating an intermediate set for @{text "(image f xs)"} when evaluating @{text "(set_as_map (image f xs))"}.\<close>

definition set_as_map_image :: "('a1 \<times> 'a2) set \<Rightarrow> (('a1 \<times> 'a2) \<Rightarrow> ('b1 \<times> 'b2)) \<Rightarrow> ('b1 \<Rightarrow> 'b2 set option)" where 
  "set_as_map_image xs f = (set_as_map (image f xs))"

(* combine two separate set_as_map_image calls on the same set *)
definition dual_set_as_map_image :: "('a1 \<times> 'a2) set \<Rightarrow> (('a1 \<times> 'a2) \<Rightarrow> ('b1 \<times> 'b2)) \<Rightarrow> (('a1 \<times> 'a2) \<Rightarrow> ('c1 \<times> 'c2)) \<Rightarrow> (('b1 \<Rightarrow> 'b2 set option) \<times> ('c1 \<Rightarrow> 'c2 set option))" where 
  "dual_set_as_map_image xs f1 f2 = (set_as_map (image f1 xs), set_as_map (image f2 xs))"


lemma set_as_map_image_code[code]  :
  fixes t :: "('a1 ::ccompare \<times> 'a2 :: ccompare) set_rbt" 
  and   f1 :: "('a1 \<times> 'a2) \<Rightarrow> ('b1 :: ccompare \<times> 'b2 ::ccompare)"
shows "set_as_map_image (RBT_set t) f1 = (case ID CCOMPARE(('a1 \<times> 'a2)) of
           Some _ \<Rightarrow> Mapping.lookup 
                      (RBT_Set2.fold (\<lambda> kv m1 .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map_image RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map_image (RBT_set t) f1))"
proof (cases "ID CCOMPARE(('a1 \<times> 'a2))")
  case None
  then show ?thesis by auto
next
  case (Some a)

  let ?f' = "\<lambda> t . (RBT_Set2.fold (\<lambda> kv m1 .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)))
                      t
                      Mapping.empty)"

  let ?f = "\<lambda> xs . (fold (\<lambda> kv m1 . case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1))
                            xs Mapping.empty)"
  have "\<And> xs :: ('a1 \<times> 'a2) list . Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None)"
  proof -
    fix xs :: "('a1 \<times> 'a2) list"
    show "Mapping.lookup (?f xs) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case 
        by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq) 
    next
      case (snoc xz xs)
      then obtain x z where "f1  xz = (x,z)" 
        by (metis (mono_tags, hide_lams) surj_pair)
  
      then have *: "(?f (xs@[xz])) = (case Mapping.lookup (?f xs) x of
                                  None \<Rightarrow> Mapping.update x {z} (?f xs) |
                                  Some zs \<Rightarrow> Mapping.update x (Set.insert z zs) (?f xs))"
        by auto
  
      then show ?case proof (cases "Mapping.lookup (?f xs) x")
        case None
        then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x {z} (?f xs))" using * by auto
  
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
  
        have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some {z} else Mapping.lookup (?f xs) x')"
          unfolding ** 
          unfolding scheme by force
  
        have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = None"
        using None snoc by auto
        then have "\<not>(\<exists> z . (x,z) \<in> f1 ` set xs)"
          by (metis (mono_tags, lifting) option.distinct(1))
        then have "(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))" and "{z' . (x,z') \<in> f1 ` set (xs@[xz])} = {z}"
          using \<open>f1  xz = (x,z)\<close> by fastforce+
        then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None)
                     = (\<lambda> x' . if x' = x then Some {z} else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x')"
          using \<open>f1  xz = (x,z)\<close> by fastforce
        
        show ?thesis using m1 m2 snoc
          using \<open>f1 xz = (x, z)\<close> by presburger
      next
        case (Some zs)
        then have **: "Mapping.lookup (?f (xs@[xz])) = Mapping.lookup (Mapping.update x (Set.insert z zs) (?f xs))" using * by auto
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
        have m1: "Mapping.lookup (?f (xs@[xz])) = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else Mapping.lookup (?f xs) x')"
          unfolding ** 
          unfolding scheme by force
  
  
        have "(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = Some zs"
          using Some snoc by auto
        then have "(\<exists> z' . (x,z') \<in> f1 ` set xs)"
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))" by fastforce
  
        have "{z' . (x,z') \<in> f1 ` set (xs@[xz])} = Set.insert z zs"
        proof -
          have "Some {z . (x,z) \<in> f1 ` set xs} = Some zs"
            using \<open>(\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x = Some zs\<close>
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "{z . (x,z) \<in> f1 ` set xs} = zs" by auto
          then show ?thesis 
            using \<open>f1 xz = (x, z)\<close> by auto
        qed
  
        have "\<And> a  . (\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None) a
                   = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x') a" 
        proof -
          fix a show "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None) a
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x') a"
          using \<open>{z' . (x,z') \<in> f1 ` set (xs@[xz])} = Set.insert z zs\<close> \<open>(\<exists> z' . (x,z') \<in> f1 ` set (xs@[xz]))\<close> \<open>f1 xz = (x, z)\<close>
          by (cases "a = x"; auto)
        qed

        then have m2: "(\<lambda> x' . if (\<exists> z' . (x',z') \<in> f1 ` set (xs@[xz])) then Some {z' . (x',z') \<in> f1 ` set (xs@[xz])} else None)
                     = (\<lambda> x' . if x' = x then Some (Set.insert z zs) else (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set xs) then Some {z . (x,z) \<in> f1 ` set xs} else None) x')"
          by auto
  
  
        show ?thesis using m1 m2 snoc
          using \<open>f1 xz = (x, z)\<close> by presburger
      qed
    qed
  qed


  
  then have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` set (RBT_Set2.keys t)) then Some {z . (x,z) \<in> f1 ` set (RBT_Set2.keys t)} else None)"
    unfolding fold_conv_fold_keys by metis
  moreover have "set (RBT_Set2.keys t) = (RBT_set t)" 
    using Some by (simp add: RBT_set_conv_keys) 
  ultimately have "Mapping.lookup (?f' t) = (\<lambda> x . if (\<exists> z . (x,z) \<in> f1 ` (RBT_set t)) then Some {z . (x,z) \<in> f1 ` (RBT_set t)} else None)"
    by force
  then show ?thesis 
    using Some unfolding set_as_map_image_def set_as_map_def by simp
qed


lemma dual_set_as_map_image_code[code] :
  fixes t :: "('a1 ::ccompare \<times> 'a2 :: ccompare) set_rbt" 
  and   f1 :: "('a1 \<times> 'a2) \<Rightarrow> ('b1 :: ccompare \<times> 'b2 ::ccompare)"
  and   f2 :: "('a1 \<times> 'a2) \<Rightarrow> ('c1 :: ccompare \<times> 'c2 ::ccompare)"
  shows "dual_set_as_map_image (RBT_set t) f1 f2 = (case ID CCOMPARE(('a1 \<times> 'a2)) of
           Some _ \<Rightarrow> let mm = (RBT_Set2.fold (\<lambda> kv (m1,m2) .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)
                        , case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m2 (x) of None \<Rightarrow> Mapping.update (x) {z} m2 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m2)))
                      t
                      (Mapping.empty,Mapping.empty))
                     in (Mapping.lookup (fst mm), Mapping.lookup (snd mm)) |
           None   \<Rightarrow> Code.abort (STR ''dual_set_as_map_image RBT_set: ccompare = None'') 
                                (\<lambda>_. (dual_set_as_map_image (RBT_set t) f1 f2)))"
proof (cases "ID CCOMPARE(('a1 \<times> 'a2))")
  case None
  then show ?thesis by auto
next
  case (Some a)

  let ?f1 = "\<lambda> xs . (fold (\<lambda> kv m . case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m (x) of None \<Rightarrow> Mapping.update (x) {z} m | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)) xs Mapping.empty)"
  let ?f2 = "\<lambda> xs . (fold (\<lambda> kv m . case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m (x) of None \<Rightarrow> Mapping.update (x) {z} m | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)) xs Mapping.empty)"

  let ?f12 = "\<lambda> xs . fold (\<lambda> kv (m1,m2) .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)
                        , case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m2 (x) of None \<Rightarrow> Mapping.update (x) {z} m2 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m2)))
                      xs
                      (Mapping.empty,Mapping.empty)"

  let ?f1' = "\<lambda> t . (RBT_Set2.fold (\<lambda> kv m . case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m (x) of None \<Rightarrow> Mapping.update (x) {z} m | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)) t Mapping.empty)"
  let ?f2' = "\<lambda> t . (RBT_Set2.fold (\<lambda> kv m . case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m (x) of None \<Rightarrow> Mapping.update (x) {z} m | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m)) t Mapping.empty)"

  let ?f12' = "\<lambda> t . RBT_Set2.fold (\<lambda> kv (m1,m2) .
                        ( case f1 kv of (x,z) \<Rightarrow> (case Mapping.lookup m1 (x) of None \<Rightarrow> Mapping.update (x) {z} m1 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m1)
                        , case f2 kv of (x,z) \<Rightarrow> (case Mapping.lookup m2 (x) of None \<Rightarrow> Mapping.update (x) {z} m2 | Some zs \<Rightarrow> Mapping.update (x) (Set.insert z zs) m2)))
                      t
                      (Mapping.empty,Mapping.empty)"

  have "\<And>xs . ?f12 xs = (?f1 xs, ?f2 xs)"
    unfolding fold_dual[symmetric] by simp
  then have "?f12 (RBT_Set2.keys t) = (?f1 (RBT_Set2.keys t), ?f2 (RBT_Set2.keys t))"
    by simp
  then have "?f12' t = (?f1' t, ?f2' t)"
    unfolding fold_conv_fold_keys by metis

  have "Mapping.lookup (fst (?f12' t)) = set_as_map (f1 ` (RBT_set t))" 
    unfolding \<open>?f12' t = (?f1' t, ?f2' t)\<close> fst_conv set_as_map_image_def[symmetric]
    using set_as_map_image_code[of t f1] Some by simp
  moreover have "Mapping.lookup (snd (?f12' t)) = set_as_map (f2 ` (RBT_set t))" 
    unfolding \<open>?f12' t = (?f1' t, ?f2' t)\<close> snd_conv set_as_map_image_def[symmetric]
    using set_as_map_image_code[of t f2] Some by simp
  ultimately show ?thesis
    unfolding dual_set_as_map_image_def Let_def using Some by simp
qed



subsubsection \<open>New Code Equations for @{text "h"}\<close>

declare [[code drop: h]]
lemma h_refined[code] : "h M (q,x) 
  = (let m = set_as_map_image (transitions M) (\<lambda>(q,x,y,q') . ((q,x),y,q')) 
      in (case m (q,x) of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}))"
  unfolding h_code set_as_map_image_def by simp



subsubsection \<open>New Code Equations for @{text "canonical_separator'"}\<close>

lemma canonical_separator'_refined[code] : 
  fixes M :: "('a,'b,'c) fsm_impl"
  shows
"FSM_Impl.canonical_separator' M P q1 q2 = (if FSM_Impl.fsm_impl.initial P = (q1,q2) 
  then
    (let f'  = set_as_map_image (FSM_Impl.fsm_impl.transitions M) (\<lambda>(q,x,y,q') . ((q,x),y));
         f   = (\<lambda>qx . (case f' qx of Some yqs \<Rightarrow> yqs | None \<Rightarrow> {}));
         shifted_transitions' = shifted_transitions (FSM_Impl.fsm_impl.transitions P);
         distinguishing_transitions_lr = distinguishing_transitions f q1 q2 (FSM_Impl.fsm_impl.nodes P) (FSM_Impl.fsm_impl.inputs P);
         ts = shifted_transitions' \<union> distinguishing_transitions_lr
     in 
  
      \<lparr> FSM_Impl.fsm_impl.initial = Inl (q1,q2)
      , FSM_Impl.fsm_impl.nodes = (image Inl (FSM_Impl.fsm_impl.nodes P)) \<union> {Inr q1, Inr q2}
      , FSM_Impl.fsm_impl.inputs = FSM_Impl.fsm_impl.inputs M \<union> FSM_Impl.fsm_impl.inputs P
      , FSM_Impl.fsm_impl.outputs = FSM_Impl.fsm_impl.outputs M \<union> FSM_Impl.fsm_impl.outputs P
      , FSM_Impl.fsm_impl.transitions = ts \<rparr>)
  else \<lparr> FSM_Impl.fsm_impl.initial = Inl (q1,q2), FSM_Impl.fsm_impl.nodes = {Inl (q1,q2)}, FSM_Impl.fsm_impl.inputs = {}, FSM_Impl.fsm_impl.outputs = {}, FSM_Impl.fsm_impl.transitions = {}\<rparr>)"
  unfolding set_as_map_image_def by simp


subsubsection \<open>New Code Equations for @{text "calculate_test_paths"}\<close>

lemma calculate_test_paths_refined[code] : 
  "calculate_test_paths M m d_reachable_nodes r_distinguishable_pairs repetition_sets =
    (let
         paths_with_witnesses 
              = (image (\<lambda> q . (q,m_traversal_paths_with_witness M q repetition_sets m)) d_reachable_nodes);
         get_paths                        
              = m2f (set_as_map paths_with_witnesses);
         PrefixPairTests                    
              = \<Union> q \<in> d_reachable_nodes . \<Union> mrsps \<in> get_paths q . prefix_pair_tests q mrsps;
         PreamblePrefixTests
              = \<Union> q \<in> d_reachable_nodes . \<Union> mrsps \<in> get_paths q . preamble_prefix_tests q mrsps d_reachable_nodes;
         PreamblePairTests
              = preamble_pair_tests (\<Union> (q,pw) \<in> paths_with_witnesses . ((\<lambda> (p,(rd,dr)) . dr) ` pw)) r_distinguishable_pairs;
         tests
              = PrefixPairTests \<union> PreamblePrefixTests \<union> PreamblePairTests; 
         tps'  
              = m2f_by \<Union> (set_as_map_image paths_with_witnesses (\<lambda> (q,p) . (q, image fst p)));
         dual_maps 
              =  dual_set_as_map_image tests (\<lambda> (q,p,q') . (q,p)) (\<lambda> (q,p,q') . ((q,p),q'));
         tps''  
              = m2f (fst dual_maps);
         tps  
              = (\<lambda> q . tps' q \<union> tps'' q);
         rd_targets 
              = m2f (snd dual_maps)     
    in ( tps, rd_targets))"

  unfolding calculate_test_paths_def Let_def dual_set_as_map_image_def fst_conv snd_conv set_as_map_image_def 
  by simp


subsubsection \<open>New Code Equations for @{text "prefix_pair_tests"}\<close>

fun target' :: "'state \<Rightarrow> ('state, 'input, 'output) path \<Rightarrow> 'state" where
  "target' q [] = q" |
  "target' q p = t_target (last p)"

lemma target_refined[code] :
  "target q p = target' q p" 
proof (cases p rule: rev_cases)
  case Nil
  then show ?thesis by auto
next
  case (snoc p' t)
  then have "p \<noteq> []" by auto
  then show ?thesis unfolding snoc target.simps visited_nodes.simps
    by (metis (no_types, lifting) last_ConsR last_map list.map_disc_iff target'.elims) 
qed

declare [[code drop: prefix_pair_tests]]
lemma prefix_pair_tests_refined[code] :
fixes t :: "(('a ::ccompare,'b::ccompare,'c::ccompare) traversal_Path \<times> ('a set \<times> 'a set)) set_rbt" 
shows "prefix_pair_tests q (RBT_set t) = (case ID CCOMPARE((('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set))) of
  Some _ \<Rightarrow> set 
    (concat (map (\<lambda> (p,(rd,dr)) . 
                      (concat (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))])
                                    (filter (\<lambda> (p1,p2) . (target q p1) \<noteq> (target q p2) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd) (prefix_pairs p)))))
                 (RBT_Set2.keys t))) |
  None   \<Rightarrow> Code.abort (STR ''prefix_pair_tests RBT_set: ccompare = None'') 
                                  (\<lambda>_. (prefix_pair_tests q (RBT_set t))))"
  (is "prefix_pair_tests q (RBT_set t) = ?C")
proof (cases "ID CCOMPARE((('a ::ccompare,'b::ccompare,'c::ccompare) traversal_Path \<times> ('a set \<times> 'a set)))")
  case None
  then show ?thesis by auto
next
  case (Some a)   

  have *: "?C = (\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) (set (RBT_Set2.keys t))))"
  proof -
    let ?S1 = "set (concat (map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) (RBT_Set2.keys t)))"
    let ?S2 = "(\<Union>(image (\<lambda> (p,(rd,dr)) . \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) (set (RBT_Set2.keys t))))"

    have *: "?C = ?S1"
    proof -
      have *: "\<And> rd p . (filter (\<lambda> (p1,p2) . (target q p1) \<noteq> (target q p2) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd) (prefix_pairs p)) = (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))"
        by meson
      have "?C = set (concat (map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (filter (\<lambda> (p1,p2) . (target q p1) \<noteq> (target q p2) \<and> (target q p1) \<in> rd \<and> (target q p2) \<in> rd) (prefix_pairs p))))) (RBT_Set2.keys t)))"
        using Some by auto
      then show ?thesis 
        unfolding * by presburger
    qed

    have union_filter_helper: "\<And> xs f x1 x2  y . y \<in> f (x1,x2) \<Longrightarrow> (x1,x2) \<in> set xs \<Longrightarrow> y \<in> \<Union> (set (map f xs))"
      by auto 
    have concat_set_helper : "\<And> xss xs x . x \<in> set xs \<Longrightarrow> xs \<in> set xss \<Longrightarrow> x \<in> set (concat xss)" 
      by auto

    have "\<And> x . x \<in> ?S1 \<Longrightarrow> x \<in> ?S2" 
    proof -
      fix x assume "x \<in> ?S1"
      then obtain p rd dr p1 p2 where "(p,(rd,dr)) \<in> set (RBT_Set2.keys t)"
                                and   "(p1,p2) \<in> set ((filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))"
                                and   "x \<in> set [(q,p1,(target q p2)), (q,p2,(target q p1))]"
        by auto
      then have "x \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}"
        by auto
      then have "x \<in> \<Union> (set (map (\<lambda> (p1,p2) . {(q,p1,(target q p2)), (q,p2,(target q p1))}) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))"
        using union_filter_helper[OF _ \<open>(p1,p2) \<in> set ((filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))\<close>, of x "(\<lambda>(p1, p2). {(q, p1, target q p2), (q, p2, target q p1)})"] by simp
      then show "x \<in> ?S2"
        using \<open>(p,(rd,dr)) \<in> set (RBT_Set2.keys t)\<close> by blast
    qed

    moreover have "\<And> x . x \<in> ?S2 \<Longrightarrow> x \<in> ?S1" 
    proof -
      fix x assume "x \<in> ?S2"
      then obtain p rd dr p1 p2 where "(p,(rd,dr)) \<in> set (RBT_Set2.keys t)"
                                and   "(p1,p2) \<in> set ((filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))"
                                and   "x \<in> {(q,p1,(target q p2)), (q,p2,(target q p1))}"
        by auto
      
      then have *: "x \<in> set [(q,p1,(target q p2)), (q,p2,(target q p1))]" by auto
      have **: "[(q,p1,(target q p2)), (q,p2,(target q p1))] \<in> set (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))"
        using \<open>(p1,p2) \<in> set ((filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))\<close> by force
      have ***: "(concat (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p)))) \<in> set ((map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,p2) . [(q,p1,(target q p2)), (q,p2,(target q p1))]) (filter (\<lambda> (p1,p2) . (target q p1) \<in> rd \<and> (target q p2) \<in> rd \<and> (target q p1) \<noteq> (target q p2)) (prefix_pairs p))))) (RBT_Set2.keys t)))"
        using \<open>(p,(rd,dr)) \<in> set (RBT_Set2.keys t)\<close> by force
      
      show "x \<in> ?S1"
        using concat_set_helper[OF concat_set_helper[OF * **] ***] by assumption
    qed
  
    ultimately show ?thesis unfolding * by blast
  qed

  show ?thesis
    unfolding * unfolding prefix_pair_tests_code 
    using Some by (simp add: RBT_set_conv_keys)
qed


subsubsection \<open>New Code Equations for @{text "preamble_prefix_tests"}\<close>

declare [[code drop: preamble_prefix_tests]]
lemma preamble_prefix_tests_refined[code] :
  fixes t1 :: "(('a ::ccompare,'b::ccompare,'c::ccompare) traversal_Path \<times> ('a set \<times> 'a set)) set_rbt"  
  and   t2 :: "'a set_rbt"
shows "preamble_prefix_tests q (RBT_set t1) (RBT_set t2) = (case ID CCOMPARE((('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set))) of
Some _ \<Rightarrow> (case ID CCOMPARE('a) of
  Some _ \<Rightarrow> set (concat (map (\<lambda> (p,(rd,dr)) . 
                 (concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))])     
                             (filter (\<lambda> (p1,q2) . (target q p1) \<noteq> q2 \<and> (target q p1) \<in> rd \<and> q2 \<in> rd) 
                                     (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))))))
                 (RBT_Set2.keys t1))) |
  None \<Rightarrow> Code.abort (STR ''prefix_pair_tests RBT_set: ccompare = None'') (\<lambda>_. (preamble_prefix_tests q (RBT_set t1) (RBT_set t2)))) |
None \<Rightarrow> Code.abort (STR ''prefix_pair_tests RBT_set: ccompare = None'') (\<lambda>_. (preamble_prefix_tests q (RBT_set t1) (RBT_set t2))))"
  (is "preamble_prefix_tests q (RBT_set t1) (RBT_set t2) = ?C")
proof (cases "ID CCOMPARE((('a,'b,'c) traversal_Path \<times> ('a set \<times> 'a set)))")
  case None
  then show ?thesis by auto
next
  case (Some a)
  then have k1: "(RBT_set t1) = set (RBT_Set2.keys t1)" 
    by (simp add: RBT_set_conv_keys)
  
  show ?thesis proof (cases "ID CCOMPARE('a)")
    case None
    then show ?thesis using Some by auto
  next
    case (Some b)
    then have k2: "(RBT_set t2) = set (RBT_Set2.keys t2)" 
      by (simp add: RBT_set_conv_keys)

    have "preamble_prefix_tests q (RBT_set t1) (RBT_set t2) = (\<Union>(p, rd, dr)\<in> set (RBT_Set2.keys t1). \<Union>(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2))). {(q, p1, q2), (q2, [], target q p1)})"
      unfolding preamble_prefix_tests_code  k1 k2 by simp
      

    moreover have "?C = (\<Union>(p, rd, dr)\<in> set (RBT_Set2.keys t1). \<Union>(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2))). {(q, p1, q2), (q2, [], target q p1)})"
    proof -
      let ?S1 = "set (concat (map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))) (RBT_Set2.keys t1)))"
      let ?S2 = "(\<Union>(p, rd, dr)\<in> set (RBT_Set2.keys t1). \<Union>(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2))). {(q, p1, q2), (q2, [], target q p1)})"
  
      have *: "?C = ?S1" 
      proof -
        have *: "\<And> rd p . (filter (\<lambda> (p1,q2) . (target q p1) \<noteq> q2 \<and> (target q p1) \<in> rd \<and> q2 \<in> rd) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))) = (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))"
          by meson
        have "?C = set (concat (map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<noteq> q2 \<and> (target q p1) \<in> rd \<and> q2 \<in> rd) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))) (RBT_Set2.keys t1)))"
          using Some \<open>ID ccompare = Some a\<close> by auto
        then show ?thesis 
          unfolding * by presburger
      qed
  
      have union_filter_helper: "\<And> xs f x1 x2  y . y \<in> f (x1,x2) \<Longrightarrow> (x1,x2) \<in> set xs \<Longrightarrow> y \<in> \<Union> (set (map f xs))"
        by auto 
      have concat_set_helper : "\<And> xss xs x . x \<in> set xs \<Longrightarrow> xs \<in> set xss \<Longrightarrow> x \<in> set (concat xss)" 
        by auto
  
      have "\<And> x . x \<in> ?S1 \<Longrightarrow> x \<in> ?S2" 
      proof -
        fix x assume "x \<in> ?S1"
        
        obtain prddr where "prddr \<in> set (RBT_Set2.keys t1)"
                            and   "x \<in> set ((\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))) prddr)"
          using concat_map_elem[OF \<open>x \<in> ?S1\<close>] by blast

        moreover obtain p rd dr where "prddr = (p,(rd,dr))"
          using prod_cases3 by blast 
        
        ultimately have "(p,(rd,dr)) \<in> set (RBT_Set2.keys t1)"
                   and  "x \<in> set ((concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))))))"
          by auto
        then obtain p1 q2 where "(p1,q2) \<in> set ((filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))))"
                          and   "x \<in> set [(q,p1,q2), (q2,[],(target q p1))]"
          by auto

        then have "x \<in> {(q,p1,q2), (q2,[],(target q p1))}"
          by auto
        then have "x \<in> \<Union> (set (map (\<lambda>(p1, q2). {(q, p1, q2), (q2, [], target q p1)}) (filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))"
          using union_filter_helper[OF _ \<open>(p1,q2) \<in> set ((filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))))\<close>, of x "(\<lambda> (p1,q2) . {(q,p1,q2), (q2,[],(target q p1))})"] by simp
        then have "x \<in> (\<Union>(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2))). {(q, p1, q2), (q2, [], target q p1)})"
          by auto
        then show "x \<in> ?S2"
          using \<open>(p,(rd,dr)) \<in> set (RBT_Set2.keys t1)\<close> by blast
      qed

      moreover have "\<And> x . x \<in> ?S2 \<Longrightarrow> x \<in> ?S1"
      proof -
        fix x assume "x \<in> ?S2"
        then obtain p rd dr p1 q2 where "(p, rd, dr)\<in> set (RBT_Set2.keys t1)"
                                  and   "(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2)))"
                                  and   "x \<in> {(q, p1, q2), (q2, [], target q p1)}"
          by blast

        then have *:"x \<in> set [(q, p1, q2), (q2, [], target q p1)]"
          by auto

        have "(p1,q2) \<in> set (filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))"
          using \<open>(p1, q2)\<in>Set.filter (\<lambda>(p1, q2). target q p1 \<in> rd \<and> q2 \<in> rd \<and> target q p1 \<noteq> q2) (set (prefixes p) \<times> (set (RBT_Set2.keys t2)))\<close>
          using cartesian_product_list_set
          by auto 
        then have **:"[(q, p1, q2), (q2, [], target q p1)] \<in> set ((map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))"
          by force
        
          
        have ***: "(concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2))))) \<in> set (map (\<lambda> (p,(rd,dr)) . (concat (map (\<lambda> (p1,q2) . [(q,p1,q2), (q2,[],(target q p1))]) (filter (\<lambda> (p1,q2) . (target q p1) \<in> rd \<and> q2 \<in> rd \<and> (target q p1) \<noteq> q2) (cartesian_product_list (prefixes p) (RBT_Set2.keys t2)))))) (RBT_Set2.keys t1))"
          using \<open>(p, rd, dr)\<in> set (RBT_Set2.keys t1)\<close> by force

        
        show "x \<in> ?S1"
          using concat_set_helper[OF concat_set_helper[OF * **] ***] by assumption
      qed

      ultimately show ?thesis unfolding * by blast
    qed

    ultimately show ?thesis by simp
  qed
qed

end