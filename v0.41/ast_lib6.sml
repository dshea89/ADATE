(* File: ast_lib6.sml
   Lifted out from ast_lib.sml 2000-03-30.
*)

structure Ast_lib6 =
struct
open Lib List1 Ast Ast_lib

fun is_abstract_con_exp( app_exp{ func, ... } ) = 
      Predefined.is_abstract_constructor func
  | is_abstract_con_exp _ = false

fun all_poses_in_preorder( E : ('a,'b)e ) : pos list =
  if is_not_activated_exp E then nil else
  if is_abstract_con_exp E then [ [] ] else
  let val Subs =
    map( all_poses_in_preorder,
      case E of
        app_exp{func,args,...} => ( if is_q func then nil else args)
      | case_exp{exp,rules,...} => exp::map(#exp,rules)
      | let_exp{dec_list,exp,...} => snoc(map(#exp,dec_list),exp)
      )
  in 
    [] ::
    flat_map( fn(Order_no,Sub_pos_list) =>
      map( fn Sub_pos => Order_no::Sub_pos, Sub_pos_list ),
      combine( fromto(0,length(Subs)-1), Subs )
      )
  end



fun all_poses_in_postorder( E : ('a,'b)e ) : pos list =
  if is_not_activated_exp E then nil else
  if is_abstract_con_exp E then [ [] ] else
  let val Subs =
    map( all_poses_in_postorder,
      case E of
        app_exp{func,args,...} => ( if is_q func then nil else args)
      | case_exp{exp,rules,...} => exp::map(#exp,rules)
      | let_exp{dec_list,exp,...} => snoc(map(#exp,dec_list),exp)
      )
  in 
    snoc(
    flat_map( fn(Order_no,Sub_pos_list) =>
      map( fn Sub_pos => Order_no::Sub_pos, Sub_pos_list ),
      combine( fromto(0,length(Subs)-1), Subs )
      ),
    [] )
  end


fun absolutely_all_poses_in_postorder( E : ('a,'b)e ) : pos list =
  if is_abstract_con_exp E then [ [] ] else
  let val Subs =
    map( absolutely_all_poses_in_postorder,
      case E of
        app_exp{func,args,...} =>  args
      | case_exp{exp,rules,...} => exp::map(#exp,rules)
      | let_exp{dec_list,exp,...} => snoc(map(#exp,dec_list),exp)
      )
  in 
    snoc(
    flat_map( fn(Order_no,Sub_pos_list) =>
      map( fn Sub_pos => Order_no::Sub_pos, Sub_pos_list ),
      combine( fromto(0,length(Subs)-1), Subs )
      ),
    [] )
  end

fun descendants(Pos,E) : pos list =
  let val All_sub_poses = all_poses_in_preorder(pos_to_sub(E,Pos))
  in
    map( fn Sub_pos => Pos@Sub_pos, All_sub_poses )
  end

exception Proper_descendants
fun proper_descendants( Pos, E ) = 
  case descendants( Pos, E ) of
    [] => (
      p"\n\nproper_descendants: \n";
      p"\n  Pos = "; print_pos Pos;
      p"\n  E = "; Print.print_exp' E;
      raise Proper_descendants
      )
  | _ :: Xs => Xs

fun children( Pos, E ) : pos list =
  case pos_to_sub( E, Pos ) of Sub =>
  if is_abstract_con_exp Sub then [] else
  map( fn P => snoc( Pos, P ),
    case Sub of
      app_exp{func,args,...} => fromto( 0, length args - 1 )
      | case_exp{exp,rules,...} => fromto( 0, length rules )
      | let_exp{dec_list,exp,...} => fromto( 0, length dec_list )
      )

exception All_poses_filter
fun all_poses_filter( f : ('a,'b)e->bool, E : ('a,'b)e ) : pos list =
  let
    val So_far : pos list ref = ref []
    fun ins Pos = So_far := rev Pos :: !So_far
    fun g( E, Pos ) =
      if is_not_activated_exp E then
        ()
      else if is_abstract_con_exp E then
             if f E then ins Pos else () 
      else (
      case E of
        app_exp{ args, ... } =>
          loop( fn( N, E ) => g( E, N :: Pos ), 
            combine( fromto( 0, length args - 1 ), args ) )
      | case_exp{ exp, rules, ... } => (
          g( exp, 0 :: Pos );
          loop( fn( N, { exp, ... } ) => g( exp, N :: Pos ), 
            combine( fromto( 1, length rules ),  rules ) ) )
      | let_exp{ dec_list, exp, ... } => (
          loop( fn( N, { exp, ... } ) => g( exp, N :: Pos ), 
            combine( fromto( 0, length dec_list - 1 ),  dec_list ) );
          g( exp, length dec_list :: Pos ) );
      if f E then ins Pos else () )
  in
    g( E, [] );
    rev( !So_far )
  end
  handle Ex => (
    output( !std_out, "\nall_poses_filter:\n\n" );
    Print.print_exp' E;
    nl();
    re_raise( Ex, "all_poses_filter" )
    )
         


exception Absolutely_all_poses_filter
fun absolutely_all_poses_filter( f : ('a,'b)e->bool, E : ('a,'b)e ) : pos list =
  filter( fn Pos => f(pos_to_sub(E,Pos)), absolutely_all_poses_in_postorder E )
  handle Ex => re_raise(Ex,"Absolutely_all_poses_filter")




(*
 Code related to finding the common subexpressions for each subexpression
of a given expression.

Output: A list of ( Position, Common sub exp ) pairs.

This output is intended to be used in the REQ and the R transformations
as follows.

Given E( Sub, Sub ), transform to case Sub of V => E( V, V ) and replace
Sub with a synthesized expression Synt yielding case Synt of V => E( V, V ).
*)

local

exception Common_sub_exps_exn
structure H = Exp_HashTable

fun common_sub_exps'( E : exp, Pos : pos )
    : ( pos * exp) list * unit H.hash_table =
  if is_abstract_con_exp E then cse'( E, nil, Pos ) else
  case E of
    app_exp{ args, ... } => cse'( E, args, Pos )
  | case_exp{ exp, rules, ... } => cse'( E, exp :: map( #exp, rules ), Pos )
  | let_exp{ dec_list, exp, ... } =>
      cse'( E, map( #exp, dec_list ) @ [ exp ], Pos )

and cse'( E : exp, Es : exp list, Pos : pos ) =
  let
    val Xs = map( common_sub_exps',
      combine( Es, map( fn N => Pos @ [ N ], fromto( 0, length Es - 1 ) ) ) 
      )
    val ( Xss, Tables ) = split Xs
    val All_subs = 
      exp_hash_make_set( map( #1, flat_map( H.listItemsi, Tables ) ) )
    val Common_subs = filter( fn Sub =>
      length( filter( fn Table =>
        case H.find Table Sub of NONE => false | SOME _ => true,
        Tables ) ) >= 2,
      All_subs )
    val Xs = map( fn Common_sub => ( Pos,  Common_sub ), Common_subs ) @
      flatten Xss
    val Table = H.mkTable( length All_subs, Common_sub_exps_exn )
  in
    H.insert Table ( E,  () );
    loop( fn Sub => H.insert Table ( Sub, () ), All_subs );
    ( Xs, Table )
  end (* cse'  *)

in (* local *)

fun common_sub_exps( E : exp ) : ( pos * exp ) list =
  #1( common_sub_exps'( E, [] ) )

end (* local *)


local

fun common_poses_list( E : exp, Top_pos : pos ) : pos list list =
  map( fn( Pos, Common ) =>
      map( fn Common_pos => Pos @ Common_pos,
        absolutely_all_poses_filter( fn Sub => exp_eq( Sub, Common ), 
          pos_to_sub( E, Pos ) ) ),
    filter( fn( Pos, _ ) => is_prefix( Top_pos, Pos ),
      common_sub_exps E ) )

in

exception Produce_bottom_posess_list

fun produce_bottom_posess_list( E : exp, Top_pos : pos, N_bottoms : int,
      Time_limit : real, Approximate_synt_time_per_exp : real )
    : pos list list list =
  if is_not_activated_exp E then [] else
  let 
    val Delta_posess = 
      map( fn Pos => Pos::nil, proper_descendants(Top_pos,E) ) @ (
(*
      if real(exp_size E) / 20.0 * Approximate_synt_time_per_exp / 0.004 >
         Time_limit
      then
        []
      else
*)
        common_poses_list( E, Top_pos ) )

    fun p_list N_bottoms =
    if N_bottoms <= 0 then
      raise Produce_bottom_posess_list
    else if N_bottoms = 1 then
      map( fn Poses => Poses::nil, Delta_posess )
    else
      let val Bottom_posess_list = p_list(N_bottoms-1)
      in
        map( fn( Poses, Bottom_posess ) => Poses :: Bottom_posess,
          filter( fn( Poses, Bottom_posess ) =>
            pos_list_less( Poses, hd Bottom_posess ) andalso
            forall( fn Pos =>
              not( exists( fn Bottom_pos => 
                is_prefix( Pos, Bottom_pos ) orelse 
                is_prefix( Bottom_pos, Pos ),
                flatten Bottom_posess ) ),
              Poses ),
            cart_prod( Delta_posess, Bottom_posess_list )
            ))
      end
  in
    if N_bottoms=0 then nil else p_list N_bottoms
  end

end (* local *)


end (* structure Ast_lib6 *)
