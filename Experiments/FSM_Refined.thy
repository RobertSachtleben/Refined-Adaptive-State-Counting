theory FSM_Refined
  imports FSM 
          "HOL-Library.Product_Lexorder"
          HOL.Record
          Deriving.Compare
          Containers.Containers
begin

(* TODO:
  - experiment with common-subexpression elimination
  - read up on AFP entries / userguides for
    - Containers
    - (maybe) Lifting/Transfer    
*)

value[code] "{1::nat}"

(* TODO:
  - instantiations for type fsm
    - ceq, ccompare, ...
*)




instantiation fsm :: (equal,equal,equal) equal
begin
definition equal_fsm :: "('a, 'b, 'c) fsm \<Rightarrow> ('a, 'b, 'c) fsm \<Rightarrow> bool" where
  "equal_fsm x y = (initial x = initial y \<and> nodes x = nodes y \<and> inputs x = inputs y \<and> outputs x = outputs y \<and> transitions x = transitions y)"

instance
  apply (intro_classes)
  unfolding equal_fsm_def 
  by (simp add: fsm_eq)
end 








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
  by (metis fsm_eq order.asym set_less_aux_antisym)

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


subsection \<open>Derive\<close>

derive (eq) ceq fsm
derive (rbt) set_impl fsm
derive (rbt) mapping_impl fsm



value "{m_ex_H,m_ex_H}"
value "{m_ex_H,m_ex_H,m_ex_H}"
value[code] "compare m_ex_H m_ex_H"






subsection \<open>Revisiting h\<close>

subsubsection \<open>New Code Generation for set_as_map\<close>

declare [[code drop: set_as_map]]

lemma set_as_map_code[code] :
  fixes t :: "('a :: ccompare \<times> 'b :: ccompare \<times> 'c :: ccompare) set_rbt" 
  shows "set_as_map (RBT_set t) = (case ID CCOMPARE(('a \<times> 'b \<times> 'c)) of
           Some _ \<Rightarrow> Mapping.lookup (RBT_Set2.fold (\<lambda> (x,y,z) m . case Mapping.lookup m (x,y) of
                        None \<Rightarrow> Mapping.update (x,y) {z} m |
                        Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
                      t
                      Mapping.empty) |
           None   \<Rightarrow> Code.abort (STR ''set_as_map RBT_set: ccompare = None'') 
                                (\<lambda>_. set_as_map (RBT_set t)))"
proof (cases "ID CCOMPARE(('a \<times> 'b \<times> 'c))")
  case None
  then show ?thesis by auto
next
  case (Some a)
  
  let ?f' = "(\<lambda> t' . (RBT_Set2.fold (\<lambda> (x,y,z) m . case Mapping.lookup m (x,y) of
                                                None \<Rightarrow> Mapping.update (x,y) {z} m |
                                                Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
                           t'
                           Mapping.empty))"
 
  let ?f = "\<lambda> xs . (fold (\<lambda> (x,y,z) m . case Mapping.lookup m (x,y) of
                                                None \<Rightarrow> Mapping.update (x,y) {z} m |
                                                Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) m)
                          xs Mapping.empty)"
  have "\<And> xs :: ('a \<times> 'b \<times> 'c) list . Mapping.lookup (?f xs) = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None)"
  proof - 
    fix xs :: "('a \<times> 'b \<times> 'c) list"
    show "Mapping.lookup (?f xs) = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None)"
    proof (induction xs rule: rev_induct)
      case Nil
      then show ?case 
        by (simp add: Mapping.empty.abs_eq Mapping.lookup.abs_eq)
    next
      case (snoc xyz xs)
      then obtain x y z where "xyz = (x,y,z)" 
        by (metis (mono_tags, hide_lams) surj_pair)
  
      have *: "(?f (xs@[(x,y,z)])) = (case Mapping.lookup (?f xs) (x,y) of
                                  None \<Rightarrow> Mapping.update (x,y) {z} (?f xs) |
                                  Some zs \<Rightarrow> Mapping.update (x,y) (insert z zs) (?f xs))"
        by auto
  
      then show ?case proof (cases "Mapping.lookup (?f xs) (x,y)")
        case None
        then have **: "Mapping.lookup (?f (xs@[(x,y,z)])) = Mapping.lookup (Mapping.update (x,y) {z} (?f xs))" using * by auto
  
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
  
        have m1: "Mapping.lookup (?f (xs@[(x,y,z)])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else Mapping.lookup (?f xs) (x',y'))"
          unfolding ** 
          unfolding scheme by force
  
        have "(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = None"
          using None snoc by auto
        then have "\<not>(\<exists> z . (x,y,z) \<in> set xs)"
          by (metis (mono_tags, lifting) case_prod_conv option.distinct(1))
        then have "(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))" and "{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = {z}"
          by auto
        then have m2: "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some {z} else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y'))"
          by auto
  
        show ?thesis using m1 m2 snoc
          using \<open>xyz = (x, y, z)\<close> by presburger
      next
        case (Some zs)
        then have **: "Mapping.lookup (?f (xs@[(x,y,z)])) = Mapping.lookup (Mapping.update (x,y) (insert z zs) (?f xs))" using * by auto
        have scheme: "\<And> m k v . Mapping.lookup (Mapping.update k v m) = (\<lambda>k' . if k' = k then Some v else Mapping.lookup m k')"
          by (metis lookup_update')
  
        have m1: "Mapping.lookup (?f (xs@[(x,y,z)])) = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else Mapping.lookup (?f xs) (x',y'))"
          unfolding ** 
          unfolding scheme by force
  
  
        have "(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = Some zs"
          using Some snoc by auto
        then have "(\<exists> z . (x,y,z) \<in> set xs)"
          unfolding case_prod_conv using  option.distinct(2) by metis
        then have "(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))" by simp
  
        have "{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = insert z zs"
        proof -
          have "Some {z . (x,y,z) \<in> set xs} = Some zs"
            using \<open>(\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x,y) = Some zs\<close>
            unfolding case_prod_conv using  option.distinct(2) by metis
          then have "{z . (x,y,z) \<in> set xs} = zs" by auto
          then show ?thesis by auto
        qed
  
        have "\<And> a b . (\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None) (a,b)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y')) (a,b)"
        proof -
          fix a b show "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None) (a,b)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y')) (a,b)"
          using \<open>{z' . (x,y,z') \<in> set (xs@[(x,y,z)])} = insert z zs\<close> \<open>(\<exists> z . (x,y,z) \<in> set (xs@[(x,y,z)]))\<close>
          by (cases "(a,b) = (x,y)"; auto)
        qed
  
        then have m2: "(\<lambda> (x',y') . if (\<exists> z' . (x',y',z') \<in> set (xs@[(x,y,z)])) then Some {z' . (x',y',z') \<in> set (xs@[(x,y,z)])} else None)
                     = (\<lambda> (x',y') . if (x',y') = (x,y) then Some (insert z zs) else (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set xs) then Some {z . (x,y,z) \<in> set xs} else None) (x',y'))"
          by auto
  
  
        show ?thesis using m1 m2 snoc
          using \<open>xyz = (x, y, z)\<close> by presburger
      qed
    qed
  qed
  then have "Mapping.lookup (?f' t) = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> set (RBT_Set2.keys t)) then Some {z . (x,y,z) \<in> set (RBT_Set2.keys t)} else None)"
    unfolding fold_conv_fold_keys by force
  moreover have "set (RBT_Set2.keys t) = (RBT_set t)" 
    using Some by (simp add: RBT_set_conv_keys) 
  ultimately have "Mapping.lookup (?f' t) = (\<lambda> (x,y) . if (\<exists> z . (x,y,z) \<in> (RBT_set t)) then Some {z . (x,y,z) \<in> (RBT_set t)} else None)"
    by force
    

  then show ?thesis 
    using Some unfolding set_as_map_def by simp
qed

declare pretty_sets[code_post del]
value[code] "h (m_ex_H) (1,1)"
declare pretty_sets[code_post]
value[code] "h (m_ex_H) (1,1)"
value[code] "h (m_ex_H) (1,2)"
value[code] "h (m_ex_H) (1,4)"

(*code_printing class_instance integer :: mapping_impl \<rightharpoonup> (Haskell)*)
code_deps h
definition xy :: "(integer \<times> integer) \<Rightarrow> (integer \<times> integer) set" where "xy = h m_ex_H"
export_code open h m_ex_H FSM.initial mapping_impl xy in Haskell module_name H4

end