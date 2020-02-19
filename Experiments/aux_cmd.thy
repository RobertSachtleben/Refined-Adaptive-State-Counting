(* copied from https://stackoverflow.com/a/57064672 *)

theory aux_cmd
  imports Complex_Main Containers.Containers
  keywords "find_instantiations" :: thy_decl  
begin
section \<open>Auxiliary commands\<close>
subsection \<open>Commands\<close>

ML \<open>

fun find_instantiations ctxt c =
  let
    val {classes, ...} = ctxt |> Proof_Context.tsig_of |> Type.rep_tsig;
    val algebra = classes |> #2 
    val arities = algebra |> Sorts.arities_of;
  in  
    Symtab.lookup arities c
    |> the
    |> map #1
    |> Sorts.minimize_sort algebra
  end

fun find_instantiations_cmd tc st = 
  let
    val ctxt = Toplevel.context_of st;
    val _ = tc 
      |> Syntax.parse_typ ctxt 
      |> dest_Type 
      |> fst 
      |> find_instantiations ctxt 
      |> map Pretty.str 
      |> Pretty.writeln_chunks
  in () end

val q = Outer_Syntax.command
  \<^command_keyword>\<open>find_instantiations\<close> 
  "find all instantiations of a given type constructor"
  (Parse.type_const >> (fn tc => Toplevel.keep (find_instantiations_cmd tc)));

\<close>


subsection \<open>Examples\<close>

find_instantiations filter
find_instantiations nat
find_instantiations real
find_instantiations integer
find_instantiations prod

end