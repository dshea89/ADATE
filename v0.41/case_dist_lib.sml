(* File: case_dist_lib.sml
   Created 1998-10-27.
   Modified 1998-12-11.
*)

structure Case_dist_lib :
sig
  val schema5a :
    ( 'a, 'b )Ast.e * ( 'a -> bool ) * ( 'a -> 'a ) *
    ( bool * ( 'a, 'b )Ast.e -> unit )
    ->
    unit

  val schema6a :
    ( 'a, 'b )Ast.e * ( 'a -> bool ) * ( 'a -> 'a ) *
    ( bool * ( 'a, 'b )Ast.e -> unit )
    ->
    unit

  val schema5b :
    ( 'a, 'b )Ast.e * ( 'a -> bool ) * ( 'a -> 'a ) *
    ( ( 'a, 'b )Ast.e -> unit )
    ->
    unit

  val schema6b :
    ( 'a, 'b )Ast.e * ( 'a -> bool ) * ( 'a -> 'a ) *
    ( ( 'a, 'b )Ast.e -> unit )
    ->
    unit

val pre_process : ( 'a, 'b )Ast.d -> ( Ast_lib.pos option * 'a, 'b )Ast.d

val post_process : ( Ast_lib.pos option * 'a, 'b )Ast.d ->
      ( 'a, 'b )Ast.d * ( Ast_lib.pos -> Ast_lib.pos list )
end =
struct

open Lib List1 Ast Ast_lib 

fun schema5a(
      let_exp{
        dec_list,
        exp = app_exp{ func, args, exp_info = Exp_info_child },
        exp_info = Exp_info } : ( 'a, 'b )e,
      is_marked : 'a -> bool,
      mark : 'a -> 'a,
      emit : bool * ( 'a, 'b )e -> unit
      ) : unit =
  if not( is_marked Exp_info_child orelse is_marked Exp_info ) then () else
  let
    fun mk_let A =
      if exists( fn{ func, ... } => sym_exp_member( func, A ), dec_list ) then
        rename(
          let_exp{ dec_list = dec_list, exp = A, 
                   exp_info = mark( get_exp_info A ) },
          false )
      else
        A
  in
    emit(
      false,
      app_exp{ func = func, args = map( mk_let, args ), 
               exp_info = mark Exp_info_child } )
  end (* fun schema5a *)




fun schema6a(
      let_exp{
        dec_list = Decs,
        exp = let_exp{ dec_list, exp, exp_info = Exp_info_child },
        exp_info = Exp_info } : ( 'a, 'b )e,
      is_marked : 'a -> bool,
      mark : 'a -> 'a,
      emit : bool * ( 'a, 'b )e -> unit
      ) : unit =
  if not( is_marked Exp_info_child orelse is_marked Exp_info ) then () else
  let
    fun mk_let A =
      if exists( fn{ func, ... } => sym_exp_member( func, A ), Decs ) then
        rename(
          let_exp{ dec_list = Decs, exp = A, 
                   exp_info = mark( get_exp_info A ) },
          false )
      else
        A
  in
    emit(
      false,
      let_exp{
        dec_list = map( fn D => set_exp( D, mk_let( #exp D ) ), dec_list ),
        exp = mk_let exp,
        exp_info = mark Exp_info_child } )
  end (* fun schema6a *)


exception Schema5b_exn
fun schema5b(
      app_exp{ func, args, exp_info = Exp_info },
      is_marked : 'a -> bool,
      mark : 'a -> 'a,
      emit : ( 'a, 'b )e -> unit
      ) : unit =
  if not( is_marked Exp_info  orelse
          exists( is_marked o get_exp_info, args ) )
  then 
    () 
  else if exists( is_q_exp, args ) then
    raise Schema5b_exn
  else
  let
    val Let_nos =
      filter( fn No => is_let_exp( nth( args, No ) ),
        fromto( 0, length args - 1 ) )
  in
  loop( fn Let_no =>
    let
      val let_exp{ dec_list, exp, exp_info } = nth( args, Let_no )
    in
      emit(
        let_exp{
          dec_list = dec_list,
          exp = app_exp{ func = func,
                         args = list_replace( args, Let_no, exp ),
                         exp_info = mark Exp_info },
          exp_info = mark Exp_info } )
    end,
    Let_nos )
  end (* fun schema5b *)



exception Schema6b_exn
fun schema6b(
      let_exp{ dec_list = Decs, exp = E, exp_info = Exp_info },
      is_marked : 'a -> bool,
      mark : 'a -> 'a,
      emit : ( 'a, 'b )e -> unit
      ) : unit =
  if not( is_marked Exp_info  orelse
          exists( is_marked o get_exp_info o #exp, Decs ) )
  then 
    () 
  else
  let
    val Let_nos =
      filter( fn No => is_let_exp( #exp( nth( Decs, No ) ) ),
        fromto( 0, length Decs - 1 ) )
  in
  loop( fn Let_no =>
    let
      val Dec = nth( Decs, Let_no )
      val let_exp{ dec_list, exp = A, exp_info } = #exp Dec
    in
      emit(
        let_exp{
          dec_list = dec_list,
          exp = let_exp{
            dec_list = list_replace( Decs, Let_no, set_exp( Dec, A ) ),
            exp = E,
            exp_info = mark Exp_info },
          exp_info = mark Exp_info } )
    end,
    Let_nos )
  end (* fun schema6b *)

fun pre_process( D : ( 'a, 'b )d ) : ( pos option * 'a, 'b )d =
  info_map_dec_pos( fn( Exp_info, Pos_opt ) => ( Pos_opt, Exp_info ),
                     fn( Dec_info, _ ) => Dec_info,
                     D )

local

structure H = Pos_hash
exception Post_process_exn

in

fun post_process( D : ( pos option * 'a, 'b )d ) 
    : ( 'a, 'b )d * ( pos -> pos list ) =
let
  val Table : pos list H.hash_table = H.mkTable( 100, Post_process_exn )

  fun f( ( Old_pos_opt, Exp_info ), New_pos_opt ) =
    case ( Old_pos_opt, New_pos_opt ) of
      ( NONE, NONE ) => Exp_info
    | ( SOME Old_pos, SOME New_pos ) => (
      H.insert Table 
        ( Old_pos,
          case H.find Table Old_pos of
            NONE => [ New_pos ]
          | SOME New_poses => New_pos :: New_poses
          );
      Exp_info )

  val D = info_map_dec_pos( f, fn( Dec_info, _ ) => Dec_info, D )

  fun pos_transform Old_pos =
    case H.find Table Old_pos of
      NONE => []
    | SOME New_poses => New_poses
in
  ( D, pos_transform )
end (* fun post_process *)

end (* local *)

  














end (* structure case_dist_lib *)
