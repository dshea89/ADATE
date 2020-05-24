(* File: exp_synt_lib.sml.
   Created 1999-02-22.
   Modified 1999-03-26.
*)


structure TGI :
sig
val mk_exp_list : Ast.exp -> Ast.exp list
val mk_ty_exp_list : Ast.ty_exp -> Ast.ty_exp list

type TGI_args_type = (Ast.symbol * (Ast.exp*Ast.exp list) list) list 
val fill_in_tgi_args : Ast.exp * TGI_args_type * Ast_lib.pos -> TGI_args_type
val tgi_args : Ast.dec * Ast_lib.pos -> TGI_args_type

val make_tgi_choices :
  'a list list * ( 'a option list -> unit ) -> unit

val remove_somed : 'a list * 'b option list -> 'a list
val add_somed : 'a list * 'a option list -> 'a list

end =
struct
open Lib List1 Ast Ast_lib

fun mk_exp_list(E:exp) : exp list =
  case E of
    app_exp{func,args,...} => if func = TUPLE then args else E::nil
  | _ => E::nil

fun mk_ty_exp_list(E:ty_exp) : ty_exp list =
  case E of
    ty_con_exp(Ty_con,args) => 
      if Ty_con = TUPLE_TY_CON then args else E::nil
  | _ => E::nil



type TGI_args_type = (symbol * (exp*exp list) list) list 

  fun update_par_subs(E,Pat,(Par,Subs)) =
    if exp_eq(E,Par) orelse member'(exp_eq,E,Subs) then
       ( Par, var_exps_in_pat Pat @ Subs )
    else
      ( Par, Subs )

  fun update_tgi_args(E,Pat,TGI_args : TGI_args_type ) =
    (* Example. TGI_args = [ ( "sort", [ (`Xs,[`Xs1]) ] ), ... ]. 
       Updates TGI_args given E and Pat in case E of ... Pat=>Exp..., where
       Pat is on the chosen path.
       *)
    map( fn(F,Par_subs_list) => 
     (F, map(fn Par_subs => update_par_subs(E,Pat,Par_subs), Par_subs_list) ),
     TGI_args)

exception Fill_in_tgi_args
fun fill_in_tgi_args(E,TGI_args,Pos) =
(
  case Pos of
    nil => TGI_args
  | P::Ps =>
  case E of
    app_exp{args,...} => fill_in_tgi_args(nth(args,P),TGI_args,Ps)
  | case_exp{exp,rules,...} =>
      if P = 0 then
        fill_in_tgi_args(exp,TGI_args,Ps)
      else
        let val { pat, exp=Rhs, ... } = nth(rules,P-1) in
          fill_in_tgi_args(Rhs,update_tgi_args(exp,pat,TGI_args),Ps)
        end
  | let_exp{dec_list,exp,...} =>
      if P < length dec_list then
        fill_in_tgi_args(#exp(nth(dec_list,P)),TGI_args,Ps)
      else
        fill_in_tgi_args(exp,TGI_args,Ps)
) handle Ex => re_raise(Ex,"Fill_in_tgi_args")

fun type_filter( TGI_args : TGI_args_type ) : TGI_args_type =
  map( fn( F, Par_subs_list ) =>
    ( F,
      map( fn( Par, Subs ) =>
        ( Par,
          case type_of_exp Par of T =>
          filter( fn Sub => type_of_exp Sub = T, Subs )
          ),
        Par_subs_list )
      ),
    TGI_args )
       
val fill_in_tgi_args = type_filter o fill_in_tgi_args

exception Tgi_args
fun tgi_args( {func,pat,exp,...} : dec, Pos : pos ) =
  let 
    fun init_tgi_arg(Func,Pat) =
      ( Func,
        map( fn as_exp{ var, pat, exp_info } =>
                  let
                    val V_exp = app_exp{ func =  var, args = [],
                                  exp_info = exp_info }
                  in
                    update_par_subs( V_exp, pat, ( V_exp, [] ) )
                  end
              | V_exp as app_exp{ func, args = [], ... } => ( V_exp, [] ),
          mk_exp_list Pat )
        )
    fun g _ = nil

    fun f(Func_pats,E,P::Ps) =
      case E of
        let_exp{dec_list,exp,...} =>
          if P < length dec_list then
            let val {func,pat,...} = nth(dec_list,P) in
              (func,pat)::Func_pats
            end
          else
            Func_pats
      | _ => Func_pats

    val Func_pats = (func,pat) :: pos_fold(f,g,Pos,exp)
  in
    fill_in_tgi_args( exp, map(init_tgi_arg,Func_pats), Pos )
  end
  handle Ex => re_raise(Ex,"Tgi_args")



local

fun mtc( Argss, So_far, emit ) =
  case Argss of
    [] => emit( rev So_far )
  | Args :: Argss => (
      mtc( Argss, NONE :: So_far, emit );
      loop( fn Arg =>
        mtc( Argss, SOME Arg :: So_far, emit ),
        Args ) )
in

fun make_tgi_choices( 
      Argss : 'a list list,
      emit : 'a option list -> unit
      ) : unit =
  (* 'a is intended to be exp. *)
  mtc( Argss, [], emit )

(*
Ex. Argss = [ [Xs1,Xs2], [Ys1], [Zs1,Zs2] ]
Examples of TGI choices:
  [ SOME Xs1, NONE, SOME Zs1 ]
  [ SOME Xs1, NONE, SOME Zs2 ]
  [ NONE, NONE, NONE ]

where the last choice is discarded iff TGI is required.
*)

end
  
exception Remove_somed_exn
fun remove_somed( Xs : 'a list, Ys : 'b option list ) : 'a list =  
  if length Xs <> length Ys then raise Remove_somed_exn else
  flat_map( fn( X, NONE ) => [ X ] | ( X, SOME _ ) => [],
    combine( Xs, Ys ) )

fun add_somed( Xs : 'a list, Ys : 'a option list ) : 'a list =
  case ( Xs, Ys ) of
    ( [], [] ) => []
  | ( [], SOME Y :: Ys ) => Y :: add_somed( [], Ys )
  | ( X :: Xs, NONE :: Ys ) => X :: add_somed( Xs, Ys )
  | ( Xs as _::_, SOME Y :: Ys ) => Y :: add_somed( Xs, Ys )




end (* structure TGI *)


