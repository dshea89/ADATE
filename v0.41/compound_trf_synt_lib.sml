(* File: compound_trf_synt_lib.sml.
   Created: 1998-12-07.
   Modified: 1998-12-07.
*)

functor Compound_trf_synt_lib( Synt_lib : SYNT_LIB ) :
sig

datatype atomic_trf_type = CASE_DIST_trf | ABSTR_trf | EMB_trf | 
  R_trf | REQ_trf | DUPL_trf | MULTIR_trf

type coupling_rule_type = { Is_start : bool, Is_end : bool, Is_strong : bool,
  Is_open : bool, Atomic_trfs : atomic_trf_type list, 
  Rule_id : string }

type atomic_emit_type = 
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list ) * 
  Ast_lib2.atomic_trf_record list 
  -> unit

datatype rule_proc_type = 
    REQ_proc of 
      Ast.dec * Ast_lib2.atomic_trf_record list * real list * real list * 
      REQ_lib.req_match_error_data * atomic_emit_type -> 
      unit
  | other_proc of 
      Ast.dec * Ast_lib2.atomic_trf_record list * real list * atomic_emit_type 
      -> unit

type rule_type = coupling_rule_type * rule_proc_type * real

val rule_eq : rule_type * rule_type -> bool


type form_type = int * rule_type list

val print_form : form_type -> unit

val set_wanted_decs : ( string * Ast.dec ) list -> unit

val wanted_check : 
    Ast.dec * Ast_lib2.atomic_trf_record list * ( form_type * real ) list -> 
    unit

end =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Print



(* Types: *)


datatype atomic_trf_type = CASE_DIST_trf | ABSTR_trf | EMB_trf | 
  R_trf | REQ_trf | DUPL_trf | MULTIR_trf

type coupling_rule_type = { Is_start : bool, Is_end : bool, Is_strong : bool,
  Is_open : bool, Atomic_trfs : atomic_trf_type list, Rule_id : string }

type atomic_emit_type = 
  (dec * atomic_trf_record list * real option list) * atomic_trf_record list 
  -> unit

datatype rule_proc_type = 
    REQ_proc of 
      dec * atomic_trf_record list * real list * real list * 
       REQ_lib.req_match_error_data * atomic_emit_type 
      -> unit
  | other_proc of 
      dec * atomic_trf_record list * real list * atomic_emit_type 
      -> unit

type rule_type = coupling_rule_type * rule_proc_type * real

fun rule_eq( ( { Rule_id = X, ... }, _ ,_ ) : rule_type, 
             ( { Rule_id = Y, ... }, _, _ ) : rule_type) = X=Y 


type form_type = int * rule_type list


fun print_form( ( Form_id, Form ) : form_type ) : unit = (
  map(fn ({Rule_id,...},_,_) => output(!std_out,Rule_id^" "), Form);
  ()
  )


structure H = Real_HashTable

exception Wanted_decs_exn

val Wanted_decs : string H.hash_table ref = 
  ref( H.mkTable( 10, Wanted_decs_exn ) )

fun set_wanted_decs( Xs : ( string * dec ) list ) : unit = (
  Wanted_decs := H.mkTable( 10, Wanted_decs_exn );
  loop( fn ( S, D ) => 
    H.insert (!Wanted_decs) ( Synt_lib.Evaluate.syntactic_fingerprint D, S ),
    Xs ) )


fun wanted_check( D : dec, Trf_history : atomic_trf_record list,
      Forms_and_cost_limits : ( form_type * real ) list ) : unit =
let
  val F = Synt_lib.Evaluate.syntactic_fingerprint D
in
  case H.find (!Wanted_decs) F of
    NONE => ()
  | SOME S => (
      p( "\nWanted " ^ S ^ " input found.\n" );
      p"Trf_history =\n"; loop( print_atomic_trf_record, Trf_history );
      p"\n\nForms_and_cost_limits =\n";
      loop( fn( Form, Cost_limit ) => (
        print_form Form; p"   "; p( Real.toString Cost_limit ); nl() ),
        Forms_and_cost_limits );
      nl() )
       
     
end
    






end (* functor Compound_trf_synt_lib *)
