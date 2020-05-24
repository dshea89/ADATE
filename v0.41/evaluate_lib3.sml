(* File: evaluate_lib3.sml.
   Created 1999-11-02.
   Modified 1999-11-03
*)

functor IDPEF_fn(
  Eval :
    sig
      type program_eval_type
      type quick (* Same as quick_eval_value_type *)
      val program_eval_fun' : ('a,'b)Ast.d -> program_eval_type
      val program_eval_type_to_quick : 
        program_eval_type -> quick
      val Weighted_pe_cmps : ( real * ( quick * quick -> order ) )list
      val Max_time_distribution : int list
      val set_max_time : int -> unit
    end ) :
sig

(* Identifiers listed in the order they are supposed to be used: *)
val initialize : unit -> unit
val First_cutoffs_list : Eval.quick list option list
val set_initial_idpef_arg : Eval.quick list option list -> unit
val program_eval_fun : ('a,'b)Ast.d -> Eval.program_eval_type
val next_cutoffs_list : unit -> Eval.quick list option list
val print_PEF_statistics : unit -> unit
end =
struct
open Lib List1 Ast Ast_lib Eval_selection Eval

val Pe_cmps = map( #2, Weighted_pe_cmps )

fun to_move_on( Eval : 'a, Pe_cmps : ( 'a * 'a -> order )list,
      Cutoffs : 'a list ) : bool =
  case ( Pe_cmps, Cutoffs ) of
    ( [], [] ) => false
  | ( Pe_cmp :: Pe_cmps, Cutoff :: Cutoffs ) =>
  case Pe_cmp( Eval, Cutoff ) of
    GREATER => to_move_on( Eval, Pe_cmps, Cutoffs )
  | _ => true


val PEF_statistics = 
  Array.fromList( map( fn _ => 0.0, Max_time_distribution ) )

local

fun p S = output( !std_err, S )

in

fun print_PEF_statistics() = (
  p"\n\nPEF_statistics = ";
  real_list_out( !std_err,
     map( fn I => Array.sub( PEF_statistics, I ),
          fromto( 0, Array.length PEF_statistics - 1 ) ) );
  p"\n\n";
  flush_out( !std_err ) )

end (* local *)

(* Iterative-deepening program evaluation function. *)
fun idpef( 
      D : ('a,'b)d, 
      Current_eval : program_eval_type,
      Max_times : int list,
      Selection_data_list : quick selection_data list,
      Cutoffs_list : quick list list
      ) : program_eval_type =
  case Selection_data_list of
    [] => Current_eval
  | S :: Selection_data_list =>
let
  val Quick = program_eval_type_to_quick Current_eval
in
  receive( S, Quick ); 
  case Cutoffs_list of
    [] => Current_eval
  | Cutoffs :: Cutoffs_list =>
  if not( to_move_on( Quick, Pe_cmps, Cutoffs ) ) then
    Current_eval
  else
let
  val Max_time :: Max_times = Max_times
  val I = index( Max_time, Max_time_distribution )
in
  Array.update( PEF_statistics, I, Array.sub( PEF_statistics, I ) + 1.0 );
  set_max_time Max_time;
  idpef( D, program_eval_fun' D, Max_times, Selection_data_list, Cutoffs_list )
end
end
  
(*
Assume Max_time_distribution = [ 5000, 50000, 500000 ].
Examples of initial calls to idpef:

Cost_limit  Initial call to idpef

10000       idpef( D, Eval_for_5000, [50000,500000], [S5000], [] )

20000       idpef( D, Eval_for_5000, [50000,500000], [S5000,S50000],
              [ Cutoffs5000 ] )

40000       idpef( D, Eval_for_5000, [50000,500000], [S5000,S50000],
              [ Cutoffs5000, Cutoffs50000 ] )
*)

val Selection_data_list_ref : quick selection_data list option ref =
  ref NONE

val Cutoffs_list_ref : quick list list option ref = ref NONE

fun set_initial_idpef_arg( Cutoffs_list : quick list option list ) : unit =
let
  val N = length Cutoffs_list
  val N_somes = length( takewhile( is_SOME, Cutoffs_list ) )

  val Selection_data_list : quick selection_data list = map( fn _ =>
    initial_selection_data Weighted_pe_cmps,
    fromto( 1, if N = N_somes then N else N_somes+1 ) )

  val Cutoffs_list : quick list list =
    map( fn SOME Es => Es, takewhile( is_SOME, Cutoffs_list ) )
in
  Selection_data_list_ref := SOME Selection_data_list;
  Cutoffs_list_ref := SOME Cutoffs_list
end

val First_cutoffs_list : quick list option list =
      map( fn _ => NONE, 
        fromto( 1, length Max_time_distribution - 1 ) )

fun initialize() =
  if length Max_time_distribution = 1 then 
    set_max_time( hd Max_time_distribution )
  else
    ()
    

fun next_cutoffs_list() =
let
  val SOME Selection_data_list = !Selection_data_list_ref
  val Cutoffs_list : quick list option list = 
    map( SOME o cutoffs, Selection_data_list )
in
  Selection_data_list_ref := NONE;
  Cutoffs_list_ref := NONE;
  Cutoffs_list @ map( fn _ => NONE,
    fromto( 1, length First_cutoffs_list - length Cutoffs_list ) )
end
  
fun program_eval_fun( D : ('a,'b)d ) : program_eval_type = 
  if length Max_time_distribution = 1 then 
    program_eval_fun' D
  else (
  set_max_time( hd Max_time_distribution );
  Array.update( PEF_statistics, 0, Array.sub( PEF_statistics, 0 ) + 1.0 );
  idpef( D, program_eval_fun' D, tl Max_time_distribution,
    case !Selection_data_list_ref of SOME X => X, 
    case !Cutoffs_list_ref of SOME X => X )
  )
  
end (* functor IDPEF_fn *)
