(* File: dupl_lib1.sml.
   Created 1999-07-03.
   Modified 1999-07-07.
*)

functor DUPL_lib1_fn( R_lib : R_lib_sig ) :
sig

type DUPL_record = { 
  synted_exp : Ast.exp, 
  top_pos : Ast_lib.pos, 
  rhs_size : int,
  fingerprint : real,
  synted_syntactic_complexity : real }

val find_dupls : real * Ast.dec * real * ( DUPL_record -> unit ) -> unit

val apply_dupl : Ast.dec * DUPL_record -> Ast.dec * Ast_lib.pos list
  
val print_DUPL_record : DUPL_record -> unit
(* Only used for debugging/testing. *)

end =
struct

open Lib List1 Ast Ast_lib Ast_lib2 Ast_lib6 Print

structure Exp_synt = R_lib.Exp_synt

fun dupl_top_poses( E : ('a,'b)e ) : pos list =
(* A dupl top pos is either a case-rhs, a fun-rhs or an in-exp. The reason
   that these poses are chosen is that new identifiers may be introduced by
   the parent which disables case-lifting i.e. the inserted case
   cannot occur higher. 
*)
  flat_map( fn Pos =>
    case pos_to_sub( E, Pos ) of
      case_exp{ rules, ... } => flat_map( fn( { exp, ... }, I ) =>
        if is_not_activated_exp exp then
          []
        else
          [ snoc( Pos, I ) ],
        indexize( rules, 1 ) )

    | let_exp{ dec_list, exp, ... } =>
        snoc( Pos, length dec_list ) ::
        map( fn( _, I ) => snoc( Pos, I ), indexize( dec_list, 0 ) )

    | app_exp{ ... } => [],

    all_poses_in_preorder E )

exception Dupl_min_once_exn
fun dupl_min_once_opt( E, Top_pos ) : symbol list option =
(* Returns NONE if the parent of Top_pos doesn't introduce any new
   identifiers which means that Top_pos should be ignored.
*)
if null Top_pos then SOME [] else
let
  val Parent_pos = lt Top_pos
  val I = dh Top_pos
in
  case pos_to_sub( E, Parent_pos ) of
    case_exp{ rules, ... } => (
      if I = 0 then raise Dupl_min_once_exn else
      case nth( rules, I-1 ) of { pat, ... } =>
      case vars_in_pat pat of
        [] => NONE
      | Xs as _::_ => SOME Xs )

  | let_exp{ dec_list, exp, ... } =>
      if I < length dec_list then
        case nth( dec_list, I ) of { func, pat, ... } =>
          SOME( map( fn{ func, ... } => func, dec_list ) @ vars_in_pat pat )
      else
        SOME( map( fn{ func, ... } => func, dec_list ) )
end
local

fun analyzed_exps_below_pos( E, Pos ) =
  map( fn case_exp{ exp, ... } =>exp,
    exp_filter( is_case_exp, pos_to_sub( E, Pos ) ) )

structure H = Real_HashTable

exception Analyzed_exp_ok_fun_exn 

in (* local *)

fun analyzed_exp_ok_fun( E : ('a,'b)e, Pos : pos ) : ('a,'b)e -> bool =
let
  val Prohibited = analyzed_exps_below_pos( E, Pos )
  val T = H.mkTable( 2 * length Prohibited, Analyzed_exp_ok_fun_exn )
in
  loop( fn A => H.insert T ( exp_hash A, A ), Prohibited );
  fn A => 
    case H.find T (exp_hash A) of 
      NONE => true 
    | SOME A' => not( exp_eq( A, A' ) )
end

end (* local *)



type DUPL_record = { synted_exp : exp, top_pos : pos, rhs_size : int,
                      fingerprint : real, synted_syntactic_complexity : real }

fun print_DUPL_record{ synted_exp : exp, top_pos : pos, rhs_size : int,
                       fingerprint, synted_syntactic_complexity : real } = (
  p"\nsynted_exp = "; Print.print_exp' synted_exp;
  p"\ntop_pos = "; print_pos top_pos;
  p"\nrhs_size = "; print_int rhs_size;
  p"\nfingerprint = "; print_real fingerprint;
  p"\nsynted_syntactic_complexity = "; print_real synted_syntactic_complexity
  )



fun find_dupls( Synt_and_eval_time_per_exp : real,
      D : dec, REQ_cost_limit : real, emit :  DUPL_record -> unit )
    : unit =
let
  val Top_poses = [] :: dupl_top_poses( #exp D )
  val REQ_cost_limit = REQ_cost_limit / real( length Top_poses )
in
  loop( fn Top_pos =>
    case dupl_min_once_opt( #exp D, Top_pos ) of
      NONE => ()
    | SOME( Min_once : symbol list ) =>
    let
      fun emit_synted_exp( E, _, _ ) =
      let
        val RHS_poses = selected_rhs_poses E @ other_rhs_poses E

        val E = poses_replace( E, RHS_poses, fn Sub => 
          gen_dont_know_exp( get_exp_info Sub ) )
      in
        case E of 
          case_exp{ ... } => 
            let 
              val Record = { synted_exp = E, top_pos = Top_pos,
                rhs_size = exp_size( pos_to_sub( #exp D, Top_pos ) ),
                fingerprint = (exp_hash( rename( E, true ) ) + 0.00001) * (
                  normrealhash(
                    Real.fromInt( Word.toIntX( pos_hash Top_pos ) ) 
                    ) + 
                   0.0000031 ),
                synted_syntactic_complexity = 
                  R_lib.pos_syntactic_complexity( D, E, [], Top_pos ) } 
            in
              emit Record
            end
        | _ => ()
      end
    in
      Exp_synt.synt_n( Synt_and_eval_time_per_exp,
        Constants.Default_no_of_cases_distribution, false,
        SOME( analyzed_exp_ok_fun( #exp D, Top_pos ) ),
        type_of_exp( pos_to_sub( #exp D, Top_pos ) ),
        R_lib.comps_at_pos( D, Top_pos ), fn Sub => Sub, D, Top_pos, [],
        if null Min_once then [] else [ Min_once ], true, emit_synted_exp, 
        REQ_cost_limit )
    end,
    Top_poses )
end (* fun find_dupls *)




fun apply_dupl( D : dec, { synted_exp, top_pos, ... } : DUPL_record ) 
    : dec * pos list =
let
  val Selected_rhs_poses = selected_rhs_poses synted_exp
  val RHS_poses = Selected_rhs_poses @ other_rhs_poses synted_exp
  val RHS = pos_to_sub( #exp D, top_pos )

  val D = pos_replace_dec( D, top_pos, fn _ => 
    poses_replace( synted_exp, RHS_poses, fn _ => rename( RHS, false ) ) )
  val Selected_rhs_poses = map( fn Pos => top_pos @ Pos, Selected_rhs_poses )
in
  ( R_lib.add_not_activated_exps_dec D, Selected_rhs_poses )
end



end (* functor DUPL_fn *)
