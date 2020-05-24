(* 
  File: predefined.sml
  Created: 1996-06-14.
  Modified: 1996-10-09.
*)

signature PREDEFINED =
sig

val initialize : string * string list -> unit
val fun_decs : unit -> Ast.dec list
val ty_env : unit -> Ast.ty_env
val input_type : unit -> Ast.ty_exp
val output_type : unit -> Ast.ty_exp
val datatype_decs : unit -> Ast.datatype_dec list 
val rec_types : unit -> Ast.ty_exp list
val initial_program : unit -> Ast.dec

val proper_dummy_exp : Ast.ty_exp -> Ast.exp

val find_datatype_dec : Ast.symbol -> Ast.datatype_dec
val is_in_Ddec_table : Ast.symbol -> bool
val is_constructor : Ast.symbol -> bool
val is_abstract_constructor : Ast.symbol -> bool
val is_abstract_type : Ast.symbol -> bool
val constructors : unit -> Ast.symbol list

val mk_pattern : Ast.ty_exp -> Ast.exp
val mk_dec : string * string -> Ast.dec
val mk_f_dec : string -> Ast.dec
val retype_f_dec : Ast.dec -> Ast.dec
end


structure Predefined : PREDEFINED =
struct
open Lib List1 Ast Ast_lib


fun extract_ty_env( Ds : datatype_dec list ) : ty_env =
  flat_map( fn { ty_con, ty_pars, alts } =>
  let
    val Ty_par_exps = map( ty_var_exp, ty_pars ) 
  in
    map( fn { constr, domain } =>
      ( constr, 
        { schematic_vars = ty_pars, 
          ty_exp =
            case domain of
              NONE => ty_con_exp( ty_con, Ty_par_exps )
            | SOME TE => ty_con_exp(
                           THIN_ARROW,
                           [ TE, ty_con_exp( ty_con, Ty_par_exps ) ]
                           )
          } ),
      alts )
  end,
    Ds
    )
      


val Fun_decs : dec list ref = ref []
fun fun_decs() = !Fun_decs

val Ty_env : ty_env ref = ref []
fun ty_env() = !Ty_env

val Input_type : ty_exp ref = ref( Dummy_ty_exp )
fun input_type() = !Input_type

val Output_type : ty_exp ref = ref( Dummy_ty_exp )
fun output_type() = !Output_type

val Datatype_decs : datatype_dec list ref = ref []
fun datatype_decs() = !Datatype_decs

val Rec_types : ty_exp list ref = ref []
fun rec_types() = !Rec_types

val Pre_ty_env = [
  ( DUMMY_FUNC, Dummy_ty_schema ),
  ( SEMICOLON, Dummy_ty_schema ),
  ( EQ, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int * int -> bool" } ),
  ( LESS', { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int * int -> bool" } ),
  ( UMINUS, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int -> int" } ),
  ( PLUS, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int * int -> int" } ),
  ( MINUS, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int * int -> int" } ),
  ( MUL, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int * int -> int" } ),

  ( TCOUNT, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "int" } ),

  ( EQR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> bool" } ),
  ( LESSR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> bool" } ),
  ( UMINUSR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real -> real" } ),
  ( SIGMOID, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real -> real" } ),
  ( PLUSR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> real" } ),
  ( MINUSR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> real" } ),
  ( DIVR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> real" } ),
  ( MULR, { schematic_vars = [], ty_exp = Parse.parse_ty_exp
    "real * real -> real" } )
  ]


local

structure H = Symbol_HashTable

exception Proper_dummy_table_exn
val Proper_dummy_exp_table : exp H.hash_table = 
  H.mkTable( 2, Proper_dummy_table_exn )

exception Find_dummy_exp_exn
fun find_dummy_exp( Ty_con : symbol, Ds : datatype_dec list ) 
    : exp option =
  case H.find Proper_dummy_exp_table Ty_con of
    SOME E => SOME E
  | NONE =>
  case filter( fn{ ty_con, ... } => ty_con = Ty_con, Ds ) of
    nil => NONE
  | [ D as { ty_pars=[], alts, ... } ] =>
  let
    fun g Alts =
      case Alts of
        nil => NONE
      | Alt as { constr, domain } :: Alts =>
      case domain of
        NONE => SOME( app_exp{ func = constr, args = nil, 
          exp_info = ty_con_exp(Ty_con,[]) } )
      | SOME( T as ty_con_exp(Con,Args) ) =>
      if Con <> TUPLE_TY_CON andalso not(null Args) then
        raise Find_dummy_exp_exn
      else
        let
          val Args = case Args of [] => [ T ] | _::_ => Args
          val Xs = map( fn ty_con_exp( Con, nil ) =>
            find_dummy_exp( Con, filter( fn{ ty_con, ... } =>
              ty_con <> Ty_con,
              Ds )),
            Args )
        in
          if member( NONE, Xs ) then
            g Alts
          else
            SOME( app_exp{ func = constr, args = map( fn SOME X => X, Xs ),
              exp_info = ty_con_exp( Ty_con, nil ) } )
        end
  in
    case g alts of
      NONE => NONE
    | SOME E => (
        H.insert Proper_dummy_exp_table (Ty_con,E);
        SOME E )
  end (* find_dummy_exp *)

in (* local *)
            
exception Proper_dummy_exp_table_init_exn
fun proper_dummy_exp_table_init( Ds : datatype_dec list ) = (
  H.insert Proper_dummy_exp_table ( INT,
    app_exp{ func = int_to_symbol 0, args = nil, exp_info =
      ty_con_exp(INT,nil) } );
  H.insert Proper_dummy_exp_table ( REAL,
    app_exp{ func = real_to_symbol 0.0, args = nil, exp_info =
      ty_con_exp(REAL,nil) } );
  loop( fn{ ty_con, ... } =>
    case find_dummy_exp( ty_con, Ds ) of
      NONE => raise Proper_dummy_exp_table_init_exn
    | SOME _ => (),
    Ds )
  )

exception Proper_dummy_exp_exn
fun proper_dummy_exp( T as ty_con_exp( Con, Args ) ) =
  case Args of
    nil => H.lookup Proper_dummy_exp_table Con
  | _ =>
  if Con <> TUPLE_TY_CON then
    raise Proper_dummy_exp_exn
  else
    app_exp{ func = TUPLE, args = map( proper_dummy_exp, Args ),
      exp_info = T }

end (* local *)




exception Ddec_table_exn
val Ddec_table : datatype_dec Symbol_HashTable.hash_table =
  Symbol_HashTable.mkTable( 10, Ddec_table_exn )

exception Abstract_type_table_exn
val Abstract_type_table : unit Symbol_HashTable.hash_table =
  Symbol_HashTable.mkTable( 20, Abstract_type_table_exn )

exception Constr_table_exn
val Constr_table : unit Symbol_HashTable.hash_table =
  Symbol_HashTable.mkTable( 20, Constr_table_exn )


exception Abstract_constr_table_exn
val Abstract_constr_table : unit Symbol_HashTable.hash_table =
  Symbol_HashTable.mkTable( 20, Abstract_constr_table_exn )

fun find_datatype_dec Ty_con =
  Symbol_HashTable.lookup Ddec_table Ty_con
  handle Ex => (
    output( !std_err, symbol_to_string Ty_con );
    flush_out( !std_err );
    raise Ex
    )

fun is_in_Ddec_table Ty_con =
  case Symbol_HashTable.find Ddec_table Ty_con of
    NONE => false
  | _ => true

fun is_constructor F =
  case Symbol_HashTable.find Constr_table F of
    NONE => false
  | _ => true


fun is_abstract_constructor F =
  case Symbol_HashTable.find Abstract_constr_table F of
    NONE => false
  | _ => true

fun constructors() = map( #1, Symbol_HashTable.listItemsi Constr_table )

fun is_abstract_type Ty_con =
  case Symbol_HashTable.find Abstract_type_table Ty_con of
    NONE => false
  | SOME _  => true

local

fun extract_ty_args( TE as ty_con_exp( Ty_con, Ty_args ) ) =
  if Ty_con = TUPLE_TY_CON then
    Ty_args
  else
    case Ty_args of nil => [ TE ]

in

exception Single_rule_constant_datatype_not_allowed
exception Mk_pattern
fun mk_pattern( T : ty_exp ) : exp =
(* Example. mk_pattern `int*(int*int) = 
     `V1 as (V2,V3 as (V4,V5)). 
*)
  case T of
    ty_con_exp(Ty_con,Args) =>
      if Ty_con = TUPLE_TY_CON then
        as_exp{ 
          var=gen_var_sym(),
          pat=app_exp{ func=TUPLE, args=map(mk_pattern,Args),
                             exp_info=mk_exp_info T },
                exp_info=mk_exp_info T }
      else if Ty_con = INT orelse Ty_con = REAL orelse 
              is_abstract_type Ty_con 
          then
            gen_var_exp T
      else (
        case find_datatype_dec Ty_con of { alts, ... } =>
        case alts of
          nil => raise Mk_pattern
        | [ { constr, domain } ] => (
            case domain of 
              NONE => 
                raise Single_rule_constant_datatype_not_allowed
            | SOME DT => as_exp{
                var = gen_var_sym(),
                pat = app_exp{ func=constr, 
                  args = map( mk_pattern, extract_ty_args DT ),
                  exp_info = T },
                exp_info = T } )
        | _ => gen_var_exp T
        )
  | _ => gen_var_exp T

end (* local *)



fun is_rec_datatype( { ty_con, alts, ... } : datatype_dec ) : bool =
  member( ty_con, flat_map( fn{ domain, ... } =>
    case domain of
      NONE => []
    | SOME TE => ty_cons_in_ty_exp TE,
    alts ) )


val Initial_program = ref Dummy_dec

fun initialize( Spec_file : string, Abstract_types : string list ) : unit =
  let
    val () = C_interface.GCmessages false
    (* val () = Make_spec.make_spec Spec_file *)
    val ( Ddecs, Inp_type, Out_type, Fdecs ) =
      Make_spec.extract_decs Spec_file
    fun find_ty_env() =
      extract_ty_env( !Datatype_decs ) @
      flat_map( fn { func, dec_info=Sch, ... } =>
        if is_no_dec_info Sch then
          []
        else
          [ (func,Sch) ],
        Fdecs )
  in
    Input_type := Inp_type;
    Output_type := Out_type;
    Datatype_decs := Ddecs;
    Rec_types := map( fn { ty_con, ty_pars = [], ...  } =>
        ty_con_exp( ty_con, [] ),
      filter( is_rec_datatype, Ddecs ) );
    Ty_env := Pre_ty_env @ find_ty_env();
    Fun_decs := Type.infer_types_of_decs( Fdecs, !Ty_env );
    proper_dummy_exp_table_init( !Datatype_decs );

    loop(fn Ddec as { ty_con, alts, ... } => (
      if member( symbol_to_string ty_con, Abstract_types ) then
        Symbol_HashTable.insert Abstract_type_table ( ty_con, () )
      else
         ();
      Symbol_HashTable.insert Ddec_table ( ty_con, Ddec );
      map( fn{ constr, ... } => (
        if member( symbol_to_string ty_con, Abstract_types ) then
          Symbol_HashTable.insert Abstract_constr_table ( constr, () )
        else
          ();
        Symbol_HashTable.insert Constr_table ( constr, () ) ),
        alts ) ),
      datatype_decs() );
    Initial_program :=
{ 
  func = Ast.F, 
  pat = case input_type() of T as ty_con_exp( Ty_con, _ ) =>
        if Ty_con <> TUPLE_TY_CON then
          mk_pattern T
        else
          case mk_pattern T of as_exp{ pat, ... } => pat,
  exp = gen_dont_know_exp( output_type() ), 
  dec_info = { schematic_vars = nil, ty_exp = ty_con_exp( THIN_ARROW,
    [ input_type(), output_type() ] ) }
  }


  end

fun mk_dec( Tstr, Dstr ) = Type.parse_dec_t( Dstr, Tstr, ty_env() )

fun mk_f_dec Dstr = 
  let
    val Sch : ty_schema = { schematic_vars = [], ty_exp =
      ty_con_exp( THIN_ARROW, [ input_type(), output_type() ] ) }
  in
    Type.infer_types_of_dec_using_schema( Parse.parse_dec Dstr, Sch, ty_env() )
  end


fun retype_f_dec( D : dec ) : dec =
  let
    val Sch : ty_schema = { schematic_vars = [], ty_exp =
      ty_con_exp( THIN_ARROW, [ input_type(), output_type() ] ) }
  in
    Type.infer_types_of_dec_using_schema( D, Sch, ty_env() )
  end

fun initial_program() = !Initial_program

end (* structure Predefined *)
