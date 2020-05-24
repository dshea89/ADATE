(* File: req_lib5.sml.
   Created 1998-10-01.
   Modified 1999-07-20.
*)

signature SO_FAR =
sig
  type so_far = Ast_lib2.so_far
  val original_records : so_far -> Ast_lib2.simple_R_record list
  val maintained_records : so_far -> Ast_lib2.simple_R_record list
  val d_so_far : so_far -> Ast.dec
  val independent : 
    Ast_lib2.simple_R_record * Ast_lib2.simple_R_record list -> bool
  val independent' : 
    Ast_lib.pos * Ast_lib.pos list * Ast_lib2.simple_R_record list -> bool
  val initial_so_far : Ast.dec -> so_far
  val new_so_far : Ast_lib2.simple_R_record * so_far -> so_far option
  val new_so_far' : Ast_lib2.simple_R_record list * so_far -> so_far option

val make_emittable :
      ( Ast.dec * Ast_lib.pos list -> 
        Ast.dec * Ast_lib2.CSE_record list ) *
      so_far
      ->
      Ast.dec * Ast_lib2.Simple_R_and_CSE_records

end 

functor So_far_fn( Synt_lib : SYNT_LIB ) : SO_FAR =
struct
open Lib List1 Ast Ast_lib Ast_lib2 Print

type so_far = Ast_lib2.so_far

fun original_records( ( Original, D_so_far, _, Maintained ) : so_far ) =
  Original

fun d_so_far( ( Original, D_so_far, _, Maintained ) : so_far ) =
  D_so_far

fun maintained_records( ( Original, D_so_far, _, Maintained ) : so_far ) =
  Maintained


exception Not_independent
fun mk_pos_transform( 
      { top_pos, 
        rel_bottom_poses, 
        synted_exp_bottom_poses, 
        ... } : simple_R_record ) =
(* The following function is applied to possible future top poses. *)
  fn( Pos : pos ) =>
    if not( is_prefix( top_pos, Pos ) ) then
      Pos
    else if top_pos = Pos andalso
          ( null rel_bottom_poses orelse not( null( hd rel_bottom_poses ) ) )
    then
      Pos
    else
    let
      val Pos = drop( length top_pos, Pos )
      val Rbs = filter( fn( Rb, _ ) => is_prefix( Rb, Pos ),
                  combine( rel_bottom_poses, synted_exp_bottom_poses ) )
    in
      case Rbs of
        [] => raise Not_independent
      | [ ( Rb, Sb ) ] => top_pos @ Sb @ drop( length Rb, Pos )
    end


(* The following function is used to maintain top poses for already applied
   simple R records. The second argument ia a new simple R record that may
  change Top_pos. *)
exception Not_independent_update_applied_top_pos
fun update_applied_top_pos(
      Top_pos : pos,
      New as { top_pos, rel_bottom_poses, synted_exp_bottom_poses, 
        ... } : simple_R_record
      ) : pos =
    if not( is_prefix( top_pos, Top_pos ) ) then
      Top_pos
    else
    let
      val Pos = drop( length top_pos, Top_pos )
      val Rbs = filter( fn( Rb, _ ) => is_prefix( Rb, Pos ),
                  combine( rel_bottom_poses, synted_exp_bottom_poses ) )
    in
      case Rbs of
        [] => Top_pos (* Tricky special case! *)
      | [ ( Rb, Sb ) ] => top_pos @ Sb @ drop( length Rb, Pos )
    end

fun maintain_simple_R_record( Old : simple_R_record, New : simple_R_record )
    : simple_R_record =
  set_top_pos( Old, update_applied_top_pos( #top_pos Old, New ) )
 



fun transform_simple_R_record(
      { top_pos,
        rel_bottom_poses,
        synted_exp,
        synted_exp_bottom_poses } : simple_R_record,
      pos_transform : pos -> pos ) : simple_R_record =
  { top_pos = pos_transform top_pos,
    rel_bottom_poses = rel_bottom_poses,
    synted_exp = synted_exp,
    synted_exp_bottom_poses = synted_exp_bottom_poses } 




fun is_inside_a_bottom( Ty, Tx, Bxs ) =
  exists( fn Pos => is_prefix( Pos, Ty ), map( fn Bx => Tx @ Bx, Bxs ) )

fun pair_independent( 
      { top_pos = Tx, rel_bottom_poses = Bxs, ... } : simple_R_record,
      { top_pos = Ty, rel_bottom_poses = Bys, ... } : simple_R_record
      ) : bool =
  not( prefix_related( Tx, Ty ) ) orelse
  is_inside_a_bottom( Ty, Tx, Bxs ) orelse
  is_inside_a_bottom( Tx, Ty, Bys )

fun independent( New : simple_R_record, Olds : simple_R_record list ) : bool =
  forall( fn Old => pair_independent( New, Old ), Olds )

fun independent'( Top_pos, Rel_bottom_poses, Olds ) : bool =
let
  val New : simple_R_record = {
    top_pos = Top_pos,
    rel_bottom_poses = Rel_bottom_poses,
    synted_exp = Dummy_exp,
    synted_exp_bottom_poses = [ [Max_int], [Max_int], [Max_int] ] }
in
  independent( New, Olds )
end

fun initial_so_far D = ( [], D, fn X => X, [] ) : so_far

exception New_so_far_exn
fun new_so_far(
      New : simple_R_record,
      So_far as ( Original, D_so_far, pos_transform, Maintained ) : so_far 
      ) : so_far option =
  if not( independent( New, Original ) ) then
    NONE
  else
  let
    val Original = New :: Original
    val New = transform_simple_R_record( New, pos_transform )
    val D_so_far = apply_simple_R_record( D_so_far, New )
    val pos_transform = mk_pos_transform New o pos_transform
    val Maintained = New ::
      map( fn Old => maintain_simple_R_record( Old, New ), Maintained ) 
     val _ =
       if synted_exp_match( #exp D_so_far, map( #top_pos, Maintained ), Original ) then
         ()
       else
         raise New_so_far_exn
  in
    if Synt_lib.scope_check_dec D_so_far then
      SOME( Original, D_so_far, pos_transform, Maintained )
    else
      NONE
  end
handle Ex => (
      p"\nnew_so_far:\n New = \n";
      print_simple_R_record New; 
      p"\nSo_far =\n";
      print_so_far So_far;
      p"\n-----------------------------------------------";
      raise Ex
      )



fun new_so_far'( Simples, So_far ) =
  case Simples of
    [] => SOME So_far
  | Simple :: Simples =>
  case new_so_far( Simple, So_far ) of
    NONE => NONE
  | SOME So_far => new_so_far'( Simples, So_far )
  



fun make_emittable( 
      cse : dec * pos list -> dec * CSE_record list,
      ( _, D_so_far as { exp, ... }, _, Maintained : simple_R_record list ) 
      : so_far
      ) : dec * Simple_R_and_CSE_records =
let
(*
  val () = (
    p"\n\nmake_emittable:\n";
    Print.print_dec' D_so_far; nl() )
*)
  val Top_poses = map( #top_pos, Maintained )
  val Top_poses_and_subs =
    map( fn Top_pos => ( Top_pos, pos_to_sub( exp, Top_pos ) ), Top_poses )
  fun eq( ( _, E1 ), ( _, E2 ) ) = exp_eq( E1, E2 )
  val Eq_classes = mk_eq_classes( eq, Top_poses_and_subs )
(* Big first is best when all small are entirely contained in the big 
   occurrences. Small first will in this case result in redundant CSE
   for the small exps.
*)
  val Eq_classes : ( int * pos list ) list = 
    map( fn Class as ( Pos, E ) :: _ => ( exp_size E, map( #1, Class ) ),
      Eq_classes )

  val Common_poses_list : pos list list =
    map( #2, sort (fn( (S1,_), (S2,_) ) => S1 > S2) Eq_classes )

  val ( D_so_far, CSE_records_so_far, New_maintained ) =
    apply_cses( cse, D_so_far, [], Maintained, Common_poses_list )

  val ( New_maintained, D_so_far ) = 
    emit_rename( New_maintained, D_so_far )
in
  ( D_so_far,
    { just_before_cse = Maintained,
      cse_records = CSE_records_so_far,
      after_cse = New_maintained } )
end (* fun make_emittable *)

end (* structure So_far *)

