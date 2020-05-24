(*
  File: rconst.sml
  Created: 2000-03-31.
  Modified: 2000-03-31.

A form of replacement specialized for real constants.
*)


structure Rconst :
sig

type rconst = int * real * real

val rand_rconst : unit -> rconst

val rconst_synt : rconst * real * (rconst -> unit ) -> unit

val is_rconst_exp : ('a,'b)Ast.e -> bool

val rconst_trfs : Ast.dec * Ast_lib.pos list list * real list *
  ( Ast.dec * Ast_lib2.atomic_trf_record list * real option list -> unit )
  ->
  unit


val rconst_trfs_size : Ast.dec * Ast_lib.pos list * int *
  ( Ast.dec * Ast_lib2.atomic_trf_record -> unit )
  ->
  unit

val rconst_split : 
  Ast.dec * real list * Ast_lib.pos list list * 
  ( ( Ast_lib.pos * Ast_lib.pos list ) list -> bool ) *
  Ast.symbol list list
   ->
 {
  rconst_cost_limits :  real list,
  other_cost_limits  :  real list,
  rconst_alts : Ast_lib.pos list list,
  other_alts : Ast_lib.pos list list,
  rconst_post_adjust : real option list -> real option list,
  other_post_adjust : real option list -> real option list
  }


(* Function used by exp_synt.sml: *)

val is_rconst_type : Ast.ty_exp -> bool
val synt_rconst : int * Ast.ty_env * Ast.symbol list * 
      ( Ast.exp * int * Ast.ty_env -> unit ) * 
      ( unit -> bool ) -> unit

end =
struct
open Lib List1 Ast Ast_lib Ast_lib2

fun is_rconst_exp( app_exp{ func, ... } ) = func = RCONST
  | is_rconst_exp _ = false

fun is_rconst_pos( E, Pos ) = is_rconst_exp( pos_to_sub( E, Pos ) )

exception Is_rconst_alt_exn

fun is_rconst_alt( E : ('a,'b)e, Alt : pos list ) : bool =
  if exists( fn P => is_rconst_pos( E, P ), Alt ) then
    if forall( fn P => is_rconst_pos( E, P ), Alt ) then
      true
    else
      raise Is_rconst_alt_exn
  else
    false

fun is_rconst_type( ty_con_exp( Ty_con, nil ) ) = Ty_con = RCONST_TYPE
  | is_rconst_type _ = false



type rconst = int * real * real

local

datatype lr = lnil | rnil | l of lr | r of lr

fun lr_length Xs =
  case Xs of
    lnil => 1
  | rnil => 1
  | l Xs => 1 + lr_length Xs
  | r Xs => 1 + lr_length Xs

fun apply_lr( ( Complexity, Stepsize, Current ) : rconst, lnil ) = 
      ( Complexity+1, Stepsize / 2.0, Current - Stepsize )
  | apply_lr( ( Complexity, Stepsize, Current ), rnil ) =
      ( Complexity+1, Stepsize / 2.0, Current + Stepsize )
  | apply_lr( ( Complexity, Stepsize, Current ), l Xs ) =
      apply_lr( ( Complexity+1, Stepsize / 2.0, Current - Stepsize ), Xs )
  | apply_lr( ( Complexity, Stepsize, Current ), r Xs ) =
      apply_lr( ( Complexity+1, Stepsize / 2.0, Current + Stepsize ), Xs )

fun lr_synt( Size_left : int, Sofar : lr, emit : lr -> unit,
      continue : unit -> bool ) : unit =
  if not( continue() ) then () else
  if Size_left = 1 then emit Sofar else (
    emit Sofar;
    lr_synt( Size_left-1, l Sofar, emit, continue );
    lr_synt( Size_left-1, r Sofar, emit, continue )
    )


fun synt( Max_size : int, emit : lr * real * int -> unit, 
       continue : unit -> bool ) : unit =
(* N_emitted = 2*2^Max_size - 2*Max_size-2. emit( LR, Stepsize_factor) *)
for( 1, Max_size-1, fn I => 
  let
    fun emit' LR = emit( LR, 2.01 * real_pow( 2.5, real( I - 1 ) ), I )
  in
    lr_synt( Max_size-I, lnil, emit', continue );
    lr_synt( Max_size-I, rnil, emit', continue )
  end )

in (* local *)

fun rconst_synt( ( Complexity, Stepsize, Current ) : rconst, Cost_limit : real, 
      emit : rconst -> unit ) : unit =
  if Cost_limit < 1.0 then () else
let
  fun n Max_size = 
    real_pow( 2.0, Max_size + 1.0 ) - 2.0*Max_size -2.0

  fun find_max_size S =
    if n( real S ) > Cost_limit then
      S-1
    else
      find_max_size( S + 1 )

  val Max_size = find_max_size 1

    fun emit'( LR : lr, Stepsize_factor : real, _ : int ) = 
      emit( apply_lr( ( Complexity, Stepsize * Stepsize_factor, Current ), LR ) )
  in
    synt( Max_size, emit', fn () => true )
  end


fun rconst_synt_size( ( Complexity, Stepsize, Current ) : rconst,
      Max_size : int, emit : rconst -> unit ) : unit =
let
  val true = Max_size >= 1
    fun emit'( LR : lr, Stepsize_factor : real, _ : int ) = 
      emit( 
        apply_lr( ( Complexity, Stepsize * Stepsize_factor, Current ), LR )) 
  in
    synt( Max_size, emit', fn () => true )
  end

(* Function used by exp_synt.sml: *)

fun rand_weight() = randReal() / 10.0 - 0.05

fun rand_rconst() = ( 0, 0.1, rand_weight() )

fun synt_rconst( S_max : int, Components : ty_env, Max_once : symbol list,
      emit : exp * int * ty_env -> unit, continue : unit -> bool ) :  unit =
if S_max < 1 then () else
let
  val ( Complexity, Stepsize, Current ) = rand_rconst()
  fun emit'( LR : lr, Stepsize_factor : real, I : int ) = 
    case apply_lr( ( Complexity, Stepsize * Stepsize_factor, Current ), LR ) 
    of RC =>
    emit( mk_rconst_exp RC, lr_length LR + I, Components )
  val RC_components = 
    filter( fn( _, { ty_exp, ... } ) => is_rconst_type ty_exp, Components )
in
  loop( fn Comp as ( V, { ty_exp, ... } ) =>
    emit( app_exp{ func = V, args = nil, exp_info = mk_exp_info ty_exp }, 1,
      if member( V, Max_once ) then
        filter( fn( V', _ ) => V <> V', Components )
      else
        Components ),
    RC_components );
  synt( S_max, emit', continue )
end




end (* local *)


exception R_const_trfs_exn'

fun rconst_trfs'( D : dec, Alt as Pos::_ : pos list,
      [ Cost_limit ] : real list,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
  if not( is_rconst_alt( #exp D, Alt ) ) then raise R_const_trfs_exn' else
let
  val app_exp{ args = [ Complexity, Stepsize, Current ], ... } = 
    pos_to_sub( #exp D, Pos )
  val Old = ( int_exp_to_int Complexity, real_exp_to_real Stepsize, 
              real_exp_to_real Current )
  val K = REQ_lib.K_bis( Cost_limit, 1 )
  val N = ref 0

  fun emit'( Complexity, Stepsize, Current ) = 
    case mk_rconst_exp( Complexity, Stepsize, Current ) of New => (
    inc N;
    emit(
      poses_replace_dec( D, Alt, fn _ => New ),
      [ R( { r_top_poses = ( Alt, NONE ),
             bottom_poses = [],
             bottom_labels = [],
             synted_exp = New,
             not_activated_syms = [] },
          [] ) ],

       [ 
         if K * ( real( !N ) + real REQ_lib.Offset ) < Cost_limit then
           SOME( K * ( real( !N ) + real REQ_lib.Offset ) )
         else
           NONE
         ] ) )
in
  rconst_synt( Old, Cost_limit, emit' )
end


fun rconst_trfs( D : dec, Alts : pos list list,
      [ Cost_limit ] : real list,
      emit : dec * atomic_trf_record list * real option list -> unit
      ) : unit =
if null Alts then () else
let
  val N = real( length Alts )
  
  fun emit'( D, Record, [ Cost_opt ] ) : unit =
    emit( D, Record, [
      case Cost_opt of
        NONE => NONE
      | SOME Cost =>
      case Cost * N of Cost =>
        if Cost < Cost_limit then SOME Cost else NONE ] )

  fun g Alts =
    case Alts of
      [] => ()
    | Alt :: Alts => (
        rconst_trfs'( D, Alt, [ Cost_limit / N ], emit' );
        g Alts )
in
  g Alts
end
       

exception Rconst_split_exn
fun rconst_split( D : dec, Cost_limits : real list, Alts : pos list list,
      poses_ok : ( pos * pos list ) list -> bool,
      Min_once : symbol list list ) =
if not( null Min_once ) then {
  rconst_cost_limits = map( fn _ => 0.0, Cost_limits ),
  other_cost_limits = Cost_limits,
  rconst_alts = [],
  other_alts = Alts,
  rconst_post_adjust = fn _ => raise Rconst_split_exn,
  other_post_adjust = fn X => X
  }
else
let
  fun ok( Alt : pos list ) = poses_ok( map( fn P => ( P, [] ), Alt ) )
  val ( Rconst_alts, Other_alts ) =
    pfilter( fn Alt => is_rconst_alt( #exp D, Alt ) andalso ok Alt, Alts )

  val IW = real( length Rconst_alts ) / real( length Alts )
in {
  rconst_cost_limits = map( fn L => L * IW, Cost_limits ),
  other_cost_limits = map( fn L => L * ( 1.0 - IW ), Cost_limits ),
  rconst_alts = Rconst_alts,
  other_alts = Other_alts,
  rconst_post_adjust = fn Cost_opts =>
    map( fn( Cost_limit, Cost_opt ) =>
      case Cost_opt of NONE => NONE | SOME Cost =>
      case Cost / IW of Cost =>
      if Cost > Cost_limit then NONE else SOME Cost,
      combine( Cost_limits, Cost_opts ) ),
  other_post_adjust = fn Cost_opts =>
    map( fn( Cost_limit, Cost_opt ) =>
      case Cost_opt of NONE => NONE | SOME Cost =>
      case Cost / ( 1.0 - IW ) of Cost =>
      if Cost > Cost_limit then NONE else SOME Cost,
      combine( Cost_limits, Cost_opts ) )
  }
end
     







fun rconst_trfs_size( D : dec, Alt as Pos::_ : pos list,
      Max_size : int,
      emit : dec * atomic_trf_record -> unit
      ) : unit =
let
  val true = is_rconst_alt( #exp D, Alt )
  val app_exp{ args = [ Complexity, Stepsize, Current ], ... } = 
    pos_to_sub( #exp D, Pos )
  val Old = ( int_exp_to_int Complexity, real_exp_to_real Stepsize, 
              real_exp_to_real Current )

  fun emit'( Complexity, Stepsize, Current ) = 
    case mk_rconst_exp( Complexity, Stepsize, Current ) of New =>
    emit(
      poses_replace_dec( D, Alt, fn _ => New ),
      R( { r_top_poses = ( Alt, NONE ),
             bottom_poses = [],
             bottom_labels = [],
             synted_exp = New,
             not_activated_syms = [] },
          [] ) )
         

in
  rconst_synt_size( Old, Max_size, emit' )
end









end (* structure Rconst *)






