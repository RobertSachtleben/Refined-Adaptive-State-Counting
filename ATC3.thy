theory ATC3
imports FSM2
begin

abbreviation single_input :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "single_input M \<equiv> (\<forall> q1 \<in> nodes M . \<exists> x1 . \<forall> x2 . \<forall> y \<in> outputs M . x1 \<noteq> x2 \<longrightarrow> succ M (x2,y) q1 = {})"

abbreviation output_complete :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "output_complete M \<equiv> (\<forall> q1 \<in> nodes M. \<exists> x . \<forall> y \<in> outputs M . \<exists> q2 . q2 \<in> succ M (x,y) q1)"

definition is_ATC :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "is_ATC M \<equiv> single_input M \<and> output_complete M"

typedef ('in,'out,'state) ATC = "{ M :: ('in, 'out, 'state) FSM . single_input M \<and> output_complete M }"
proof -
  obtain M :: "('in,'out,'state) FSM" where M_def : "outputs M = {}"
    by (meson select_convs(3)) 
  then have "single_input M" "output_complete M" by auto
  then show ?thesis by auto
qed

setup_lifting type_definition_ATC



end