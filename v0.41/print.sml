(*
  File: print.sml
  Created 1999-12-07
  Modified 1999-12-09

Pretty printing of expressions and declarations. Hard-coded to enhance 
portability, particularly to the MLton compiler.
*)

structure Print  :
sig
val print_ty_exp : Ast.ty_exp -> unit
val print_exp : Ast.exp -> unit
val print_dec : Ast.dec -> unit
val print_decs : Ast.dec list -> unit
val print_exp' : ('a,'b)Ast.e-> unit
val print_dec' : ('a,'b)Ast.d -> unit
val print_decs' : ('a,'b)Ast.d list -> unit
val print_dec_act_info : ('a,'b)Ast.d -> unit
val print_ty_schema : Ast.ty_schema -> unit
val print_ty_env : Ast.ty_env -> unit
end =

struct
open Lib List1 Ast

val LW = 72
exception LW_to_small_exn

val () = if LW <= 30 then raise LW_to_small_exn else ()
(* Check motivated by emergency line-break criterion. *)

(*
  LW = Line width, typically 72 characters.
  Ci = Current indentation
 *) 

fun spaces( N : int ) =
  for( 1, N, fn _ => p" " )

fun is_bin_op F =
  F = SEMICOLON orelse
  F = CONS orelse
  F = APPEND orelse
  F = EQ orelse
  F = LESS' orelse
  F = PLUS orelse
  F = MUL orelse
  F = DIV orelse
  F = MINUS orelse

  F = EQR orelse
  F = LESSR orelse
  F = PLUSR orelse
  F = MULR orelse
  F = DIVR orelse
  F = MINUSR

fun symbol_to_string( S : symbol ) : string =
  if S = EQR then "=" else
  if S = LESSR then "<" else
  if S = PLUSR then "+" else
  if S = MULR then "*" else
  if S = DIVR then "/" else
  if S = MINUSR then "-" else
  if S = UMINUSR then "~" else
  Ast.symbol_to_string S


fun list_to_string( 
      elem_to_string : 'a * int * bool -> string option, 
      Es : 'a list, Max_len : int, Sep : string ) 
    : string option =
  if Max_len <= 0 then
    NONE
  else
  case Es of
    [] => SOME ""
  | [ E ] => elem_to_string( E, Max_len, true )
  | E::Es => 
  case elem_to_string( E, Max_len, false ) of
    NONE => NONE
  | SOME SE =>
  case SE ^ Sep of SE =>
  case list_to_string( elem_to_string, Es, 
         Max_len - String.size SE, Sep ) of
    NONE => NONE
  | SOME S => SOME( SE ^ S )

fun exp_to_string( E :  ('a,'b)e, Max_len : int, 
      sexp_info : ('a,'b)e -> string,
      srule_info : ('a,'b)rule_type -> string,
      sdec_info : ('a,'b)d -> string
      ) : string option =
let
  val exp_to_string = fn( X,Y ) =>
    exp_to_string( X,Y, sexp_info, srule_info, sdec_info )
  val alt_to_string = fn( X,Y,Z ) =>
    alt_to_string( X,Y,Z, sexp_info, srule_info, sdec_info )
  val S_opt =
  if Max_len <= 0 then
    NONE
  else
  case E of
    app_exp{ func, args, ... } =>
      if null args then
        case symbol_to_string func of Sfunc =>
        if String.size Sfunc > Max_len then NONE else SOME Sfunc
      else
    let
      val Is_bin_op = is_bin_op func
      val [_,_] = if Is_bin_op then args else [E,E]
      val Sfunc = symbol_to_string func
      val Sfunc = if func = TUPLE orelse Is_bin_op then "" else Sfunc
      val Sargs = 
        list_to_string( fn( E, Max_len, Last ) => exp_to_string( E, Max_len ), 
          args,
          Max_len - String.size Sfunc - 4 - 
            ( if Is_bin_op then 4 else 2*( length args - 1 ) ),
          if Is_bin_op then " " ^ symbol_to_string func ^ " " else ", " 
          )
    in
      case Sargs of
        NONE => NONE
      | SOME Sargs => SOME( Sfunc ^ "( " ^ Sargs ^ " )" )
    end

  | case_exp{ exp, rules, ... } => (
      case exp_to_string( exp, Max_len - 9 ) of
        NONE => NONE
      | SOME Sexp =>
      case "case " ^ Sexp ^ " of " of Sexp =>
      case list_to_string( alt_to_string, rules, 
              Max_len - String.size Sexp, " | " ) 
      of Srules =>
      case Srules of
        NONE => NONE
      | SOME Srules => SOME( Sexp ^ Srules )
      )

  | as_exp{ var, pat, ... } => (
      case symbol_to_string var of Svar =>
      case Svar ^ " as " of Svar =>
      if String.size Svar > Max_len then
        NONE
      else
      case exp_to_string( pat, Max_len - String.size Svar ) of
        NONE => NONE
      | SOME Spat => SOME( Svar ^ Spat )
      )

  | let_exp{ ... } => NONE
in
  case S_opt of
    NONE => NONE
  | SOME S => SOME( S ^ sexp_info E )
end (* fun exp_to_string *)
      

and alt_to_string( Rule as { pat, exp, ... }, 
      Max_len, 
      Last,
      sexp_info : ('a,'b)e -> string,
      srule_info : ('a,'b)rule_type -> string,
      sdec_info : ('a,'b)d -> string
      ) : string option =
let
  val exp_to_string = fn( X,Y ) =>
    exp_to_string( X,Y, sexp_info, srule_info, sdec_info )
in
  case exp_to_string( pat, Max_len - 4 ) of
    NONE => NONE
  | SOME Spat =>
  case Spat ^ srule_info Rule ^ " => " of Spat =>
  let
    val N_internal = if not Last andalso is_case_exp exp then 4 else 0
  in
  case exp_to_string( exp, Max_len - String.size Spat - N_internal ) of
    NONE => NONE
  | SOME Sexp => 
  case if not Last andalso is_case_exp exp then "( " ^ Sexp ^ " )" else Sexp of
    Sexp => SOME( Spat ^ Sexp )
  end
end (* fun alt_to_string *)
    

fun print_exp( Indented : bool, Ci : int, E : ('a,'b)e,
      sexp_info : ('a,'b)e -> string,
      srule_info : ('a,'b)rule_type -> string,
      sdec_info : ('a,'b)d -> string
      ) : unit =
let
  val exp_to_string = fn( X,Y ) =>
    exp_to_string( X,Y, sexp_info, srule_info, sdec_info )
  val alt_to_string = fn( X,Y,Z ) =>
    alt_to_string( X,Y,Z, sexp_info, srule_info, sdec_info )
  val print_exp = fn( X,Y,Z ) =>
    print_exp( X,Y,Z, sexp_info, srule_info, sdec_info )
  val print_dec = fn( X,Y,Z ) =>
    print_dec( X,Y,Z, sexp_info, srule_info, sdec_info )
in
  if Indented then () else spaces Ci;
  if Ci > LW - 20 then (
    (* Emergency line break *)
    p"\n";
    print_exp( false, 0, E );
    p"\n" )
  else
  case exp_to_string( E, LW - Ci ) of
    SOME S => p S
  | NONE =>
  case E of
    app_exp{ func, args, ... } => 
    let
      val Is_bin_op = is_bin_op func
    in
      if func = TUPLE orelse Is_bin_op then () else p( symbol_to_string func );
      if null args then
        () 
      else (
        p"(\n";
        loop( fn Arg => ( 
          print_exp( false, Ci+2, Arg ); 
          if Is_bin_op then 
            p( " " ^ symbol_to_string func ^ "\n" ) 
          else 
            p",\n" ), 
          lt args );
        print_exp( false, Ci+2, dh args ); p"\n";
        spaces( Ci+2 );  p")"
        )
    end
  | case_exp{ exp, rules, ... } => (
      case exp_to_string( exp, LW - Ci - 8 ) of
        NONE => (
          p"case\n";
          print_exp( false, Ci+2, exp );
          spaces Ci; p"of\n"
          )
      | SOME Sexp => ( p"case "; p Sexp; p" of\n" );

      spaces( Ci + 2 );

      loop( fn Alt as { pat, exp, ... } =>
        case alt_to_string( Alt, LW - Ci - 2, false ) of
          SOME S => ( p S; p"\n"; spaces Ci; p"| " )
        | NONE => (
            print_exp( true, Ci+2, pat ); p( srule_info Alt );
            if is_case_exp exp then p" => (\n" else p" =>\n";
            print_exp( false, Ci+4, exp );
            if is_case_exp exp then (
              p"\n";
              spaces( Ci+4 ); p")" )
            else 
              ();
            p"\n"; spaces Ci; p"| "
            ),
        lt rules );

      case dh rules of Alt as { pat, exp, ... } =>
      case alt_to_string( Alt, LW - Ci - 2, true ) of
        SOME S => p S
      | NONE => (
          print_exp( true, Ci+2, pat ); p( srule_info Alt ); p" =>\n";
          print_exp( 
            false, 
            case exp of app_exp{ ... } => Ci+4 | _ => Ci, 
            exp )
          )
    ) (* case_exp{ ... } *)

  | as_exp{ var, pat, ... } => (
      p( symbol_to_string var ); p" as\n";
      print_exp( false, Ci+2, pat )
      )

  | let_exp{ dec_list, exp, ... } => (
      p"let\n";
      loop( fn( D, Order_no ) => ( print_dec( Order_no, Ci+2, D ); p"\n" ),
        indexize( dec_list, 0 ) );
      spaces Ci; p"in\n";
      print_exp( false, Ci+2, exp ); p"\n";
      spaces Ci; p"end"
      );

  p( sexp_info E )

end (* fun print_exp *)
           
and print_dec( Order_no, Ci, D as { func, pat, exp, ... } : ('a,'b)d,
      sexp_info : ('a,'b)e -> string,
      srule_info : ('a,'b)rule_type -> string,
      sdec_info : ('a,'b)d -> string
      ) =
let
  val exp_to_string = fn( X,Y ) =>
    exp_to_string( X,Y, sexp_info, srule_info, sdec_info )
  val print_exp = fn( X,Y,Z ) =>
    print_exp( X,Y,Z, sexp_info, srule_info, sdec_info )
  val Extra_left =
    case pat of
      app_exp{ func, args = [], ... } => " "
    | as_exp{ ... } => "( "
    | _ => ""

  val Extra_right =
    case pat of
      as_exp{ ... } => " )"
    | _ => ""
  val FunAnd = if Order_no > 0 then "and " else "fun "
in
  spaces Ci;
  case symbol_to_string func ^ sdec_info D of Sfunc =>
  case exp_to_string( pat, LW - Ci - 10 - String.size Sfunc ) of
    SOME Spat => (
      p FunAnd; p Sfunc; p Extra_left; p Spat; p Extra_right; p" =\n";
      print_exp( false, Ci+2, exp )
      )
  | NONE => (
      p FunAnd; p Sfunc; p Extra_left; p"\n";
      print_exp( false, Ci+6, pat ); p Extra_right; p" = \n";
      print_exp( false, Ci+2, exp )
      )
end (* fun print_dec *)
 

fun ty_exp_to_string( E : ty_exp ) : string =
  case E of
    ty_var_exp V => symbol_to_string V
  | ty_con_exp( F, Es ) =>
  let 
    val Sep = 
      if F = TUPLE_TY_CON then 
        " * " 
      else if F = THIN_ARROW then
        " -> "
      else 
        ", "
    val SF = 
      if F = TUPLE_TY_CON orelse F = THIN_ARROW then 
        "" 
      else 
        symbol_to_string F
    val SOME SES = list_to_string(
      fn( E, _, _ ) => SOME( ty_exp_to_string E ),
      Es, Max_int, Sep  )
  in
    SF ^( if null Es then "" else "( " ^ SES ^ " )" )
  end

fun ty_schema_to_string( { schematic_vars, ty_exp } : ty_schema ) : string =
  "{ " ^ 
  ( case list_to_string( fn( V, _, _ ) => SOME( symbol_to_string V ), 
           schematic_vars, Max_int, ","  ) of
      SOME S => S ) ^ " ; " ^
  ty_exp_to_string ty_exp ^ " }\n"


fun sexp_info( E : exp ) : string =
  " : " ^ ty_exp_to_string( type_of_exp E )

fun srule_info( { act_index, act_count, activated, ... } : ('a,'b)rule_type )
    : string =
  " : " ^ Int.toString( !act_index ) ^ " " ^ Int.toString( !act_count ) ^ " " ^
  Bool.toString( !activated )


fun sdec_info( { dec_info, ... } : dec ) : string =
  " " ^ ty_schema_to_string dec_info

fun e _ = ""

fun print_list( print_elem : 'a -> unit, Xs : 'a list, Sep : string ) : unit =
  case Xs of
    [] => ()
  | [ X ] => print_elem X
  | X::Xs => (
      print_elem X;
      p Sep;
      print_list( print_elem, Xs, Sep )
      )

(* Functions to be exported: *)

fun print_ty_exp E = p( ty_exp_to_string E )
fun print_ty_schema E = p( ty_schema_to_string E )
fun print_ty_env Xs = 
  print_list( 
    fn( Sym, Sch ) => ( p"( "; p( symbol_to_string Sym ); p", ";
      print_ty_schema Sch; p" ) " ), 
    Xs, 
    "\n" )

fun print_exp' E = print_exp( false, 0, E, e,e,e )

fun print_dec' D = print_dec( 0, 0, D, e,e,e )
fun print_decs' Ds = print_list( print_dec', Ds, "\n\n" )

fun print_dec_act_info D = print_dec( 0, 0, D, e, srule_info, e )

val print_exp = fn E => print_exp( false, 0, E, sexp_info, e, sdec_info )
val print_dec = fn D => print_dec( 0, 0, D, sexp_info, e, sdec_info )

fun print_decs Ds = print_list( print_dec, Ds, "\n\n" )


end (* structure Print *)
