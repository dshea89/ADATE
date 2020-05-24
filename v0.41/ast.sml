(* File: ast.sml
   Created: 1993-05-21
   Modified: 2000-03-24
*)

signature AST =
sig


datatype symbol_category = 
    func_sym | var_sym | emb_sym | not_activated_sym | dont_know_sym 
  | ty_var_sym | ty_con_sym | int_sym | real_sym

val symbol_category_to_string : symbol_category -> string
val string_to_symbol_category : string -> symbol_category 
type symbol = symbol_category*Word32.word*Word32.word
val symbol_pack : symbol -> string
val symbol_unpack : string -> symbol
val symbol_hash : symbol -> Word.word
val real_symbol_hash : symbol -> real
val string_to_symbol : symbol_category * string -> symbol
val string_to_symbol' : string -> symbol
val string_to_qsymbol : string -> symbol
val symbol_to_string : symbol -> string
val get_predefined_syms : unit -> symbol list
val symbol_less : symbol * symbol -> bool
val int_to_symbol : int -> symbol
val int_sym_to_int : symbol -> int
val real_to_symbol : real -> symbol
val real_sym_to_real : symbol -> real
structure Symbol_hash_key : HASH_KEY
structure Symbol_HashTable : MONO_HASH_TABLE
structure Symbol_dyn : MONO_DYNAMIC_ARRAY

type ty_var = symbol

datatype ty_exp =
  ty_var_exp of ty_var
| ty_con_exp of symbol * ty_exp list

type ty_schema = { schematic_vars : ty_var list, ty_exp :  ty_exp }
(* See Peyton-Jones book for documentation of this type *)

type ty_env = (symbol * ty_schema) list

datatype ('a,'b)e =
  app_exp of { func : symbol, args : ('a,'b)e list, exp_info : 'a }
| case_exp of { 
    exp : ('a,'b)e, 
    rules : {
      pat:('a,'b)e,
      exp:('a,'b)e,
      act_index : int ref,
      act_count : int ref,
      activated : bool ref
      } list,
    exp_info : 'a 
    }
| let_exp of { 
    dec_list : { 
      func : symbol, 
      pat : ('a,'b)e, 
      exp:('a,'b)e,
      dec_info : 'b
      } list,
    exp : ('a,'b)e,
    exp_info : 'a 
    }
| as_exp of { var : symbol, pat : ('a,'b)e, exp_info : 'a }

type ('a,'b)rule_type = {
      pat:('a,'b)e,
      exp:('a,'b)e,
      act_index : int ref,
      act_count : int ref,
      activated : bool ref
      } 



type ('a,'b)d = { 
  func : symbol, 
  pat : ('a,'b)e, 
  exp : ('a,'b)e, 
  dec_info : 'b 
  }

val set_exp : ('a,'b)d * ('a,'b)e -> ('a,'b)d

type exp_info_type = ty_exp
type dec_info_type = ty_schema

val no_exp_info : unit -> exp_info_type
val no_dec_info : unit -> ty_schema

val is_no_exp_info : exp_info_type -> bool
val is_no_dec_info : dec_info_type -> bool

val mk_exp_info : ty_exp -> exp_info_type
val get_ty_exp : exp_info_type -> ty_exp
val set_ty_exp : exp_info_type * ty_exp -> exp_info_type


val mk_rule : ('a,'b)rule_type * ('c,'d)e * ('c,'d)e -> ('c,'d)rule_type
val mk_new_rule : ('a,'b)e * ('a,'b)e -> ('a,'b)rule_type

type exp = ( exp_info_type, dec_info_type )e
type pat=exp
type dec = ( exp_info_type, dec_info_type )d

type datatype_dec = {
  ty_con : symbol,
  ty_pars : ty_var list,
  alts : { constr : symbol, domain : ty_exp option } list
  }

type type_dec = {
  ty_con : symbol,
  ty_pars : ty_var list,
  ty_exp : ty_exp 
  }

datatype parse_result =
  parsed_fun of dec list
| parsed_type of type_dec
| parsed_datatype of datatype_dec list


val TUPLE : symbol
val TUPLE_TY_CON : symbol
val OUTPUT : symbol
val OUTPUT_TY_CON : symbol
val INT : symbol
val REAL : symbol
val RCONST_TYPE : symbol
val LINCOMB_TYPE : symbol
val BOOL : symbol
val INPUT_TYPE : symbol
val OUTPUT_TYPE : symbol
val THIN_ARROW : symbol
val PREDEFINED_NOT_ACTIVATED_SYMBOL : symbol
val SEMICOLON : symbol

val EQ : symbol
val LESS' : symbol
val PLUS : symbol
val MUL : symbol
val DIV : symbol
val MINUS : symbol
val UMINUS : symbol

val TCOUNT : symbol (* Time complexity count read from register EDX. *)


val EQR : symbol
val LESSR : symbol
val PLUSR : symbol
val MULR : symbol
val DIVR : symbol
val MINUSR : symbol
val UMINUSR : symbol
val SIGMOID : symbol

val RCONST : symbol
val CONST : symbol
val LIN : symbol
val PHI : symbol

val CONS : symbol
val APPEND : symbol
val FALSE : symbol
val TRUE : symbol
val F : symbol
val ANON : symbol
val DUMMY_FUNC : symbol
val DUMMY_TY_CON : symbol
val DUMMY_SYMBOL : symbol
val dummy_exp : 'a -> ('a,'b)e
val Dummy_exp : exp
val Dummy_dec : dec
val Dummy_ty_exp : ty_exp
val Dummy_ty_schema : ty_schema

val type_of_exp : exp -> ty_exp

val is_predefined_sym : symbol -> bool
val is_generated_sym : symbol -> bool
val is_int : symbol -> bool
val is_int_exp : ('a,'b)e -> bool
val is_real : symbol -> bool
val is_real_exp : ('a,'b)e -> bool
val is_variable : symbol -> bool
val is_ty_var : symbol -> bool
val is_variable_exp : ('a,'b)e -> bool
val is_function : symbol -> bool
val is_q : symbol -> bool
val is_q_exp : ('a,'b)e -> bool
val is_not_activated_sym : symbol -> bool
val is_not_activated_exp : ('a,'b)e -> bool
val is_not_activated_rule : ('a,'b)rule_type -> bool
val is_emb_exp : ('a,'b)e -> bool
val is_dont_know_exp : ('a,'b)e -> bool
val is_app_exp : ('a,'b)e -> bool
val is_case_exp : ('a,'b)e -> bool
val is_let_exp : ('a,'b)e -> bool
val is_leaf : ('a,'b)e -> bool
val is_tuple_exp : ('a,'b)e -> bool
val is_anon_sym : symbol -> bool
val is_anon_exp : ('a,'b)e -> bool
val is_fun_type : ty_exp -> bool
val is_tuple_type : ty_exp -> bool

val sym_is_overloaded : symbol -> bool
val get_real_overloaded_sym : symbol -> symbol


val sym_no : unit -> Word32.word * Word32.word
val set_sym_no : Word32.word * Word32.word -> unit
val gen_func_sym : unit -> symbol
val gen_ty_var_sym : unit -> symbol
val gen_var_sym : unit -> symbol
val gen_var_exp : 'a -> ('a,'b) e
val gen_emb_sym : unit -> symbol
val gen_emb_exp : 'a -> ('a,'b) e
val gen_not_activated_sym  : unit -> symbol
val gen_not_activated_exp : 'a -> ('a,'b) e
val gen_dont_know_sym : unit -> symbol
val gen_dont_know_exp : 'a -> ('a,'b) e

val mk_anon_exp : 'a -> ('a,'b)e

val vars_in_ty_exp : ty_exp -> ty_var list
val ty_cons_in_ty_exp : ty_exp -> symbol list
val vars_in_pure_tuple_pat : ('a,'b)e -> symbol list
val vars_in_pat : ('a,'b)e -> symbol list
val var_exps_in_pat : ('a,'b)e -> ('a,'b)e list 

val get_exp_info : ('a,'b)e -> 'a
val set_exp_info : ('a,'b)e * 'a -> ('a,'b)e

val exp_size : ('a,'b)e -> int
val rename :  ('a,'b)e * bool -> ('a,'b)e 
val rename_decs :  ('a,'b)d list * bool -> ('a,'b)d list

val int_exp_to_int : ('a,'b)e -> int
val real_exp_to_real : ('a,'b)e -> real
val rconst_exp_to_real : ('a,'b)e -> real
val mk_int_exp : int -> exp
val mk_real_exp : real -> exp
val mk_rconst_exp : int * real * real -> exp

val Debug : bool ref

val print_syms : symbol list -> unit

end (* sig AST *)


structure Ast : AST =
struct

open Lib
open List1

datatype symbol_category = 
    func_sym | var_sym | emb_sym | not_activated_sym | dont_know_sym 
  | ty_var_sym | ty_con_sym | int_sym | real_sym



fun symbol_category_to_string( X :  symbol_category ) =
  case X of
    func_sym => "func_sym"
  | var_sym => "var_sym"
  | emb_sym => "emb_sym"
  | not_activated_sym => "not_activated_sym"
  | dont_know_sym => "dont_know_sym"
  | ty_var_sym => "ty_var_sym"
  | ty_con_sym => "ty_con_sym" 
  | int_sym => "int_sym"
  | real_sym => "real_sym"

fun string_to_symbol_category( X : string ) =
  case X of
    "func_sym" => func_sym
  | "var_sym" => var_sym
  | "emb_sym" => emb_sym
  | "not_activated_sym" => not_activated_sym
  | "dont_know_sym" => dont_know_sym
  | "ty_var_sym" => ty_var_sym
  | "ty_con_sym" => ty_con_sym
  | "int_sym" => int_sym
  | "real_sym" => real_sym

type symbol = symbol_category*Word32.word*Word32.word
(* 
  A symbol (Cat,0,N) represents a predefined identifier.
  A symbol of the form (Cat,1,N) is used for canonization.
  A symbol (Cat,M,N) with M>=2 represents a generated identifier.
*)

fun is_predefined_sym(Cat,M,N) = Cat <> real_sym andalso M = Word32.fromInt 0
fun is_generated_sym(Cat,M,N) = Cat <> real_sym andalso M >= Word32.fromInt 2


exception Symbol_HashTable_exn
structure H = Lib.String_HashTable
val Symbol_table : symbol H.hash_table = 
(* 
  Maps a string (predefined identifier) to the corresponding 
   symbol. 
*)
  H.mkTable(1000,Symbol_HashTable_exn)


fun get_predefined_syms() : symbol list =
  map( #2, H.listItemsi Symbol_table )

structure String_dyn = DynamicArrayFn(
  struct
    open Array
    type elem = string
  type vector = elem Vector.vector
    type array = string array
    structure Vector = 
struct
  open Vector
  type elem = string
  type vector = elem Vector.vector
end
  end 
  )


val String_table: String_dyn.array = 
  String_dyn.array(2,"UNDEFINED SYMBOL")
val Top : int ref = ref 0

fun string_to_symbol( Cat : symbol_category, S : string ) : symbol =
(*
  Inserts S in the next free entry in array of predefined symbols
  if S is an unseen symbol.
*)
  case H.find Symbol_table S of
    SOME Sym => Sym
  | NONE => (
      String_dyn.update( String_table, !Top, S );
      let val Sym = ( Cat, Word32.fromInt 0, Word32.fromInt(!Top) ) in
        H.insert Symbol_table (S,Sym);
        inc Top;
        Sym
      end
      )


fun string_to_symbol'( S : string ) : symbol =
  case String.explode S of
    #"?" :: #"_" :: #"E" :: #"M" :: #"B" :: _ =>
      string_to_symbol( emb_sym, S )
  | #"?" :: #"_" :: #"D" :: _ =>
      string_to_symbol( dont_know_sym, S )
  | #"?" :: #"_" :: #"N" :: #"A" :: _ =>
      string_to_symbol( not_activated_sym, S )
  | _ => string_to_symbol( func_sym, S )

exception String_to_qsymbol_exn
fun string_to_qsymbol( S : string ) : symbol =
  case String.explode S of
    #"E" :: #"M" :: #"B" :: _ =>
      string_to_symbol( emb_sym, S )
  | #"D" :: _ =>
      string_to_symbol( dont_know_sym, S )
  | #"N" :: #"A" :: _ =>
      string_to_symbol( not_activated_sym, S )
  | #"?" :: #"_" :: #"E" :: #"M" :: #"B" :: _ =>
      string_to_symbol( emb_sym, S )
  | #"?" :: #"_" :: #"D" :: _ =>
      string_to_symbol( dont_know_sym, S )
  | #"?" :: #"_" :: #"N" :: #"A" :: _ =>
      string_to_symbol( not_activated_sym, S )
  | _ => (
      output( !std_err, "\nIllegal exception name:" ^ S ^
        "\nExceptions must start with EMB, D or NA.\n\n");
      raise String_to_qsymbol_exn
      )


fun is_q(Cat,_,_) =
  case Cat of 
    emb_sym => true
  | not_activated_sym => true
  | dont_know_sym  => true
  | _ => false 
  

fun int_to_symbol( N : int ) :  symbol =
  ( int_sym, Word32.fromInt(~1), Word32.fromInt N )

fun int_sym_to_int( (int_sym,_,N) : symbol ) : int =
  Word32.toIntX N

fun real_to_symbol( X : real ) : symbol =
  case C_interface.real_to_doubleword X of ( W1, W2 ) =>
    ( real_sym, W1, W2 )

fun real_sym_to_real( ( real_sym, W1, W2 ) : symbol ) : real =
  C_interface.doubleword_to_real( W1, W2 )

fun symbol_to_string( Sym as (Cat,M,N) : symbol ) : string =
  if is_predefined_sym Sym then
    (if is_q Sym then "(raise " else "") ^
    String_dyn.sub( String_table, Word32.toInt N) ^
    (if is_q Sym then ")" else "")
  else
  let 
    val Suffix = 
      if M = 0w2 then
        Word32.toString N
      else
        Word32.toString M ^ "_" ^ Word32.toString N 
  in
    case Cat of
      func_sym => "g" ^ Suffix
    | var_sym => "V" ^ Suffix
    | not_activated_sym => "(raise NA_" ^ Suffix ^ ")"
    | emb_sym => "(raise EMB_" ^ Suffix ^ ")"
    | dont_know_sym => "(raise D_" ^ Suffix ^ ")"
    | ty_var_sym => "'" ^ Suffix
    | ty_con_sym => "c" ^ Suffix
    | int_sym => Int.toString( int_sym_to_int Sym )
    | real_sym => Real.toString( real_sym_to_real Sym )
  end

fun symbol_less( (_,M1,N1) : symbol, (_,M2,N2) : symbol ) : bool =
  Word32.<(M1,M2) orelse M1=M2 andalso Word32.<(N1,N2)
 
type ty_var = symbol

datatype ty_exp =
  ty_var_exp of ty_var
| ty_con_exp of symbol * ty_exp list

type ty_schema = { schematic_vars : ty_var list, ty_exp :  ty_exp }
(* See Peyton-Jones book for documentation of this type *)

type ty_env = (symbol * ty_schema) list


datatype ('a,'b)e =
  app_exp of { func : symbol, args : ('a,'b)e list, exp_info : 'a }
| case_exp of { 
    exp : ('a,'b)e, 
    rules : {
      pat:('a,'b)e,
      exp:('a,'b)e,
      act_index : int ref,
      act_count : int ref,
      activated : bool ref
      } list,
    exp_info : 'a 
    }
| let_exp of { 
    dec_list : { 
      func : symbol, 
      pat : ('a,'b)e, 
      exp:('a,'b)e,
      dec_info : 'b
      } list,
    exp : ('a,'b)e,
    exp_info : 'a 
    }
| as_exp of { var : symbol, pat : ('a,'b)e, exp_info : 'a }


type ('a,'b)rule_type = {
      pat:('a,'b)e,
      exp:('a,'b)e,
      act_index : int ref,
      act_count : int ref,
      activated : bool ref
      } 


type ('a,'b)d = { 
  func : symbol, 
  pat : ('a,'b)e, 
  exp : ('a,'b)e, 
  dec_info : 'b 
  }

fun set_exp( { func, pat, exp, dec_info } : ('a,'b)d, E : ('a,'b)e )
    : ('a,'b)d =
  { func = func, pat = pat, exp = E, dec_info = dec_info }

type exp_info_type = ty_exp
type dec_info_type = ty_schema

fun get_ty_exp TE = TE

fun set_ty_exp( _, TE ) = TE 


fun mk_rule( { act_index, act_count, activated, ... } : ('a,'b)rule_type,
      Pat : ('c,'d)e, E : ('c,'d)e ) = {
  pat = Pat,
  exp = E,
  act_index = ref( !act_index ),
  act_count = ref( !act_count ),
  activated = ref( !activated )
  }


fun mk_new_rule( Pat : ('a,'b)e, E : ('a,'b)e ) = {
  pat = Pat,
  exp = E,
  act_index = ref 0,
  act_count = ref 0,
  activated = ref false
  }


type exp = ( exp_info_type, dec_info_type )e
type pat=exp
type dec = ( exp_info_type, dec_info_type )d


type datatype_dec = {
  ty_con : symbol,
  ty_pars : ty_var list,
  alts : { constr : symbol, domain : ty_exp option } list
  }

type type_dec = {
  ty_con : symbol,
  ty_pars : ty_var list,
  ty_exp : ty_exp 
  }

datatype parse_result =
  parsed_fun of dec list
| parsed_type of type_dec
| parsed_datatype of datatype_dec list

val TUPLE = string_to_symbol( func_sym, "___tuple" )
val TUPLE_TY_CON = string_to_symbol( ty_con_sym, "___tuple" )
val OUTPUT = string_to_symbol( func_sym, "output" )
val OUTPUT_TY_CON = string_to_symbol( ty_con_sym, "output" )
val INT = string_to_symbol( ty_con_sym, "int" )
val REAL = string_to_symbol( ty_con_sym, "real" )
val BOOL = string_to_symbol( ty_con_sym, "bool" )
val RCONST_TYPE = string_to_symbol( ty_con_sym, "rconst" )
val LINCOMB_TYPE = string_to_symbol( ty_con_sym, "lincomb" )
val INPUT_TYPE = string_to_symbol( ty_con_sym, "input_type" )
val OUTPUT_TYPE = string_to_symbol( ty_con_sym, "output_type" )
val THIN_ARROW = string_to_symbol( ty_con_sym, "->" )
val PREDEFINED_NOT_ACTIVATED_SYMBOL = string_to_symbol( not_activated_sym, "?_NA_PREDEFINED" )
val SEMICOLON = string_to_symbol( func_sym, ";" )

val EQ = string_to_symbol( func_sym, "=" )
val LESS' = string_to_symbol( func_sym, "<" )
val PLUS = string_to_symbol( func_sym, "+" )
val MUL = string_to_symbol( func_sym, "*" )
val DIV = string_to_symbol( func_sym, "/" )
val MINUS = string_to_symbol( func_sym, "-" )
val UMINUS = string_to_symbol( func_sym, "~" )

val TCOUNT = string_to_symbol( func_sym, "TCOUNT" )

val EQR = string_to_symbol( func_sym, "=R" )
val LESSR = string_to_symbol( func_sym, "<R" )
val PLUSR = string_to_symbol( func_sym, "+R" )
val MULR = string_to_symbol( func_sym, "*R" )
val DIVR = string_to_symbol( func_sym, "/R" )
val MINUSR = string_to_symbol( func_sym, "-R" )
val UMINUSR = string_to_symbol( func_sym, "~R" )
val SIGMOID = string_to_symbol( func_sym, "sigmoid" )


val RCONST = string_to_symbol( func_sym, "rconst" )
val CONST = string_to_symbol( func_sym, "const" )
val LIN = string_to_symbol( func_sym, "lin" )
val PHI = string_to_symbol( func_sym, "phi" )

val CONS = string_to_symbol( func_sym, "::" )
val APPEND = string_to_symbol( func_sym, "@" )
val FALSE = string_to_symbol( func_sym, "false" )
val TRUE = string_to_symbol( func_sym, "true" )
val ANON = string_to_symbol( func_sym, "_" )
val F = string_to_symbol( func_sym, "f" )


val DUMMY_FUNC = string_to_symbol( func_sym, "___dummy" )
val DUMMY_SYMBOL = DUMMY_FUNC
val DUMMY_TY_CON = string_to_symbol( ty_con_sym, "___dummy_ty_con" )

val Dummy_ty_exp = ty_con_exp( DUMMY_TY_CON, [] )

fun dummy_exp(Exp_info : 'a) : ('a,'b)e = 
  app_exp{
    func=DUMMY_FUNC,
    args=nil,
    exp_info=Exp_info
    }

val Dummy_exp : exp = dummy_exp Dummy_ty_exp

val Dummy_ty_schema = { schematic_vars = [], ty_exp = Dummy_ty_exp }


val Dummy_dec : dec = {
  func=DUMMY_FUNC,
  pat=Dummy_exp,
  exp=Dummy_exp,
  dec_info=Dummy_ty_schema
  }

fun no_exp_info() = Dummy_ty_exp
fun no_dec_info() = Dummy_ty_schema

fun is_no_exp_info TE = TE = no_exp_info()
fun is_no_dec_info Sch = Sch = no_dec_info()

fun mk_exp_info TE = TE

fun is_int(int_sym,_,_) = true
  | is_int _ = false

fun is_int_exp( app_exp{ func, ... } : ('a,'b)e ) = is_int func
  | is_int_exp _ = false


fun is_real(real_sym,_,_) = true
  | is_real _ = false

fun is_real_exp( app_exp{ func, ... } : ('a,'b)e ) = is_real func
  | is_real_exp _ = false

fun is_variable(var_sym,_,_) = true
  | is_variable _ = false

fun is_ty_var(ty_var_sym,_,_) = true
  | is_ty_var(_,_,_) = false

fun is_variable_exp( app_exp{ func, ... } ) = is_variable func
  | is_variable_exp _ = false

fun is_function(func_sym,_,_) = true
  | is_function _ = false

fun is_q_exp( app_exp{ func, ... } : ('a,'b)e ) = is_q func
  | is_q_exp _ = false

fun is_emb_exp( 
      app_exp{ func=(emb_sym,_,_), ... } : ('a,'b)e ) = 
        true
  | is_emb_exp _ = false

fun is_not_activated_sym( (not_activated_sym,_,_) ) = true
  | is_not_activated_sym _ = false

fun is_not_activated_exp( 
      app_exp{ func=(not_activated_sym,_,_), ... } : ('a,'b)e ) = 
        true
  | is_not_activated_exp _ = false

fun is_not_activated_rule( { exp, ... } : ('a,'b) rule_type ) =
  is_not_activated_exp exp

fun is_dont_know_exp( 
      app_exp{ func=(dont_know_sym,_,_), ... } : ('a,'b)e ) = true
  | is_dont_know_exp _ = false

fun is_app_exp( app_exp{...} ) = true
  | is_app_exp _ = false

fun is_case_exp(case_exp{...}) = true
  | is_case_exp _ = false

fun is_let_exp(let_exp{...}) = true
  | is_let_exp _ = false

fun is_leaf( app_exp{args=nil,...}:('a,'b)e ) = true
  | is_leaf E = is_q_exp E

fun is_tuple_exp( app_exp{ func, ... } : ('a,'b)e ) = func=TUPLE
  | is_tuple_exp _ = false

fun is_anon_sym S = S = ANON

exception Is_anon_exp_exn
fun is_anon_exp( app_exp{ func, args, ... } :('a,'b)e ) = 
      if null args then
        is_anon_sym func
      else
        raise Is_anon_exp_exn
  | is_anon_exp _ = false


fun is_fun_type( ty_con_exp( Ty_con, _ ) ) = Ty_con = THIN_ARROW
  | is_fun_type _ = false

fun is_tuple_type( ty_con_exp( Ty_con, _ ) ) = Ty_con = TUPLE_TY_CON
  | is_tuple_type _ = false

fun sym_is_overloaded( F : symbol ) =
  F = EQ orelse F = LESS' orelse F = PLUS orelse F = MUL orelse F = DIV orelse
  F = MINUS orelse F = UMINUS

exception Real_overloaded_sym_exn
fun get_real_overloaded_sym( F : symbol ) : symbol =
  if F = EQ then EQR else
  if F = LESS' then LESSR else
  if F = PLUS then PLUSR else
  if F = MUL then MULR else
  if F = DIV then DIVR else
  if F = MINUS then MINUSR else
  if F = UMINUS then UMINUSR else raise Real_overloaded_sym_exn
  

local

val Current_sym_no = ref( Word32.fromInt 0 ) 
val Current_sym_no' = ref( Word32.fromInt 2 )

in

exception Sym_no
fun sym_no() =   ( 
  word32_inc Current_sym_no;
  if Word32.>=( !Current_sym_no, Lib.Max_word32 ) then (
    Current_sym_no := Word32.fromInt 1;
    word32_inc Current_sym_no';
    if Word32.>=( !Current_sym_no', Lib.Max_word32 ) then 
      raise Sym_no 
    else 
      ()
    )
  else
    ();
  ( !Current_sym_no', !Current_sym_no )
  )

fun set_sym_no( No', No ) = (
  Current_sym_no := No;
  Current_sym_no' := No'
  )

fun less_eq_current( _, W1, W2 ) =
  Word32.<( W1, !Current_sym_no' ) orelse
   W1 = !Current_sym_no' andalso Word32.<=( W2, !Current_sym_no )

end (* local *)

fun gen_var_sym() = 
  case sym_no() of (M,N) => (var_sym,M,N)

fun gen_ty_var_sym() = 
  case sym_no() of (M,N) => (ty_var_sym,M,N)

fun gen_func_sym() = 
  case sym_no() of (M,N) => (func_sym,M,N)

fun gen_emb_sym() = 
  case sym_no() of (M,N) => (emb_sym,M,N)

fun gen_not_activated_sym() = 
  case sym_no() of (M,N) => (not_activated_sym,M,N)

fun gen_dont_know_sym() = 
  case sym_no() of (M,N) => (dont_know_sym,M,N)

fun gen_var_exp(Exp_info) =
  app_exp{func=gen_var_sym(),args=nil,exp_info=Exp_info }

fun mk_anon_exp(Exp_info) =
  app_exp{func=ANON,args=nil,exp_info=Exp_info }

fun gen_not_activated_exp(Exp_info) =
  app_exp{func=gen_not_activated_sym(),args=nil,exp_info=Exp_info }

fun gen_dont_know_exp(Exp_info) =
  app_exp{func=gen_dont_know_sym(),args=nil,exp_info=Exp_info }


fun gen_emb_exp(Exp_info) =
  app_exp{func=gen_emb_sym(),args=nil,exp_info=Exp_info }



fun vars_in_ty_exp TE =
let fun vars_in_ty_exp1 TE =
  case TE of ty_var_exp N => N::nil
  | ty_con_exp(F,TEs) => flat_map( vars_in_ty_exp1, TEs )
in
  make_set(vars_in_ty_exp1 TE)
end


fun ty_cons_in_ty_exp TE =
let fun ty_cons_in_ty_exp1 TE =
  case TE of  
    ty_var_exp _ => nil
  | ty_con_exp(F,TEs) => F :: flat_map( ty_cons_in_ty_exp1, TEs )
in
  make_set(ty_cons_in_ty_exp1 TE)
end

exception Vars_in_pure_tuple_pat_exn
fun vars_in_pure_tuple_pat P = (
  case P of
    app_exp{func,args=nil,...} =>
    if is_variable func then
      func::nil
    else
      raise Vars_in_pure_tuple_pat_exn
  | app_exp{func,args,...} => 
      if func = TUPLE then (
        loop( fn app_exp{ func = V, args=[], ... } =>
          if is_variable V then () else raise Vars_in_pure_tuple_pat_exn
               | _ => raise Vars_in_pure_tuple_pat_exn,
          args );
        map( fn app_exp{ func, ... } => func, args )
        )
      else
        raise Vars_in_pure_tuple_pat_exn )
  


fun vars_in_pat P =
  case P of
    app_exp{func,args=nil,...} =>
    if is_variable func then
      func::nil
    else
      nil
  | app_exp{func,args,...} => flat_map(vars_in_pat,args)
  | as_exp{var,pat,...} => var::vars_in_pat(pat)



fun var_exps_in_pat P =
  case P of
    app_exp{func,args=nil,...} =>
    if is_variable func then
      P::nil
    else
      nil
  | app_exp{func,args,...} => flat_map(var_exps_in_pat,args)
  | as_exp{var,pat,exp_info} => 
      app_exp{func=var,args=nil,exp_info=exp_info}::
      var_exps_in_pat pat 



fun symbol_hash( (Cat,M,N) : symbol ) = 
  Word.fromLargeWord(
  Word32.xorb(
    case Cat of func_sym => 0w1 | var_sym => 0w2 | _ => 0w4,
    Word32.xorb(M,N) ) )


fun real_symbol_hash( (Cat,M,N) : symbol ) : real = 
    ( case Cat of 
        func_sym => 0.456343233453663769848 
      | var_sym => 0.8349187367352156128437628 
      | _ => 0.92764352345272984378327
      ) 
    * 
    normrealhash( Real.fromLargeInt( Word32.toLargeIntX( Word32.xorb( M, N ))))

structure Symbol_hash_key =
struct
  type hash_key=symbol
  val hashVal = symbol_hash
  fun sameKey(X,Y:symbol)= X=Y
end

structure Symbol_HashTable = HashTableFn(Symbol_hash_key)



structure Symbol_dyn = DynamicArrayFn(
  struct
    open Array
    type elem = symbol
  type vector = symbol Vector.vector
    type array = symbol array
    structure Vector =
struct
  open Vector
  type elem = symbol
  type vector = symbol Vector.vector
end

  end 
  )




fun get_exp_info E =
  case E of
    app_exp {exp_info,...} => exp_info
  | case_exp {exp_info,...} => exp_info
  | let_exp {exp_info,...} => exp_info
  | as_exp {exp_info,...} => exp_info


fun set_exp_info( E, Info ) =
  case E of
    app_exp { func, args, ... } => 
      app_exp{ func = func, args = args, exp_info = Info }
  | case_exp { exp, rules, ... } =>
      case_exp{ exp = exp, rules = rules, exp_info = Info }
  | let_exp { dec_list, exp, ... } =>
      let_exp{ dec_list = dec_list, exp = exp, exp_info = Info }
  | as_exp { var, pat, ... } => 
      as_exp{ var = var, pat = pat, exp_info = Info }

fun type_of_exp E = get_ty_exp(get_exp_info E)

fun exp_size( E : ('a,'b)e ) = 
  case E of
    app_exp{ args, ... } => 1 + int_sum(map(exp_size,args))
  | case_exp{ exp, rules, ... } =>
      1 + exp_size exp + int_sum(map(exp_size o #exp,rules))
  | let_exp { dec_list, exp, ... } =>
      1 + exp_size exp + int_sum(map(exp_size o #exp,dec_list))
  | as_exp{ pat, ... } => 1 + exp_size pat

local

exception Rename
exception Rename_hash
structure H = Symbol_HashTable

in

fun rename( E : ('a,'b)e, Canonize : bool ) : ('a,'b)e =
let
  val Curr_no = ref(Word32.fromInt 0)
  fun sym_no() = (word32_inc Curr_no; (Word32.fromInt 1,!Curr_no) )

  val gen_var_sym = 
    if Canonize then 
      fn() => case sym_no() of (M,N) => (var_sym,M,N)
    else 
      gen_var_sym

  val gen_func_sym = 
    if Canonize then 
      fn() => case sym_no() of (M,N) => (func_sym,M,N)
    else 
      gen_func_sym

  val gen_not_activated_sym = 
    if Canonize then 
      fn() => case sym_no() of (M,N) => (not_activated_sym,M,N)
    else 
      gen_not_activated_sym

  val gen_dont_know_sym = 
    if Canonize then 
      fn() => case sym_no() of (M,N) => (dont_know_sym,M,N)
    else 
      gen_dont_know_sym

  val gen_var_exp =
    if Canonize then 
      fn Exp_info => 
        app_exp{func=gen_var_sym(),args=nil,exp_info=Exp_info }
    else
      gen_var_exp

  val gen_not_activated_exp = 
    if Canonize then 
      fn Exp_info => 
        app_exp{func=gen_not_activated_sym(),
          args=nil,exp_info=Exp_info }
    else
      gen_not_activated_exp

  val gen_dont_know_exp =
    if Canonize then 
      fn Exp_info => 
        app_exp{func=gen_dont_know_sym(),
          args=nil,exp_info=Exp_info }
    else
      gen_dont_know_exp
  
  val Table : symbol list H.hash_table = 
    H.mkTable( 3 * exp_size E, Rename_hash )

  fun insert S = 
    let 
      val Sym =
        if is_variable S then gen_var_sym() else gen_func_sym() 
    in
      case H.find Table S of
        NONE => H.insert Table ( S, [Sym] )
      | SOME Xs => H.insert Table ( S, Sym::Xs )
    end

  fun delete( S : symbol ) : unit =
    let 
      val Sym::Xs = H.lookup Table S
    in
      case Xs of
        [] => ( H.remove Table S; () )
      | _ => H.insert Table ( S, Xs )
    end

  fun replace( S : symbol) : symbol = 
    case H.find Table S of NONE => S | SOME( S :: _ ) => S
  
  fun insert_pat Pat = ( map(insert,vars_in_pat Pat); () )

  fun delete_pat Pat = ( map(delete,vars_in_pat Pat); () )

  fun rename E =
  case E of
    app_exp{func,args,exp_info} =>
      if is_q_exp E then
        if is_dont_know_exp E then
          gen_dont_know_exp exp_info
        else if is_not_activated_exp E then
          gen_not_activated_exp exp_info
        else
          raise Rename
      else
        app_exp{ func=replace func, args=map(rename,args), exp_info=exp_info }
  | case_exp{exp,rules,exp_info} => case_exp{ exp=rename exp, rules=
      map( fn Rule as {pat,exp,...} =>
        let 
          val _ = insert_pat pat;
          val X = mk_rule(Rule,rename pat,rename exp)
        in
          delete_pat pat;
          X
        end,
        rules ),
      exp_info=exp_info }
  | let_exp{ dec_list, exp, exp_info } => 
    let
      val _ = map( fn { func, ... } => insert func, dec_list )
      val Ds = map( fn { func, pat, exp, dec_info } => 
        let
          val _ = insert_pat pat
          val D = {
            func = replace func,
            pat = rename pat,
            exp = rename exp,
            dec_info = dec_info
            }
        in
          delete_pat pat;
          D
        end,
        dec_list )

      val LE = let_exp{ dec_list = Ds, exp = rename exp,
        exp_info = exp_info }
    in
      map( fn { func, ... } => delete func, dec_list );
      LE
    end

  | as_exp{var,pat,exp_info} => 
      as_exp{ var=replace var, pat=rename pat, exp_info=exp_info }
in
  rename E
end

end (* local *)


fun rename_decs( Ds : ('a,'b)d list, Canonize : bool ) 
    : ('a,'b)d list =
  case Ds of
    [] => []
  | D::_ =>
  let
    val Dummy_e = #exp D
  in
  case rename( 
    let_exp{
      dec_list = Ds,
      exp = Dummy_e,
      exp_info = get_exp_info Dummy_e 
      },
    Canonize ) of
    let_exp{ dec_list, ... } => dec_list
  end




fun int_exp_to_int( app_exp{ func, args=nil, ... } ) =
  int_sym_to_int func


fun real_exp_to_real( app_exp{ func, args=nil, ... } ) =
  real_sym_to_real func


fun mk_int_exp( X : int ) : exp =
  app_exp{ func = int_to_symbol X, args=nil,
    exp_info = ty_con_exp( INT, nil ) }


fun mk_real_exp( X : real ) : exp =
  app_exp{ func = real_to_symbol X, args=nil,
    exp_info = ty_con_exp( REAL, nil ) }

fun mk_rconst_exp( Complexity : int, Stepsize : real, Current : real ) : exp =
  app_exp{ func = RCONST, 
    args = [ mk_int_exp Complexity, mk_real_exp Stepsize, mk_real_exp Current ],
    exp_info = ty_con_exp( RCONST_TYPE, [] ) }

fun rconst_exp_to_real( app_exp{ func, args = [ _, _, Current ], ... } ) 
    : real =
  case func = RCONST of true => real_exp_to_real Current



val Debug = ref false


fun print_syms Syms = list_out(
      !std_out,
      fn (Str,Sym) => output( Str, symbol_to_string Sym ),
      Syms )


fun symbol_pack( Cat, W1, W2 ) : string =
  pack[ symbol_category_to_string Cat, Word32.toString W1, Word32.toString W2 ]

exception Symbol_unpack_exn

fun symbol_unpack( S : string ) : symbol =
let
  val [ Cat, W1, W2 ] = unpack S
  val Sym = 
    ( string_to_symbol_category Cat, word32_from_string W1, word32_from_string W2 )
in
  if less_eq_current Sym then () else raise Symbol_unpack_exn;
  Sym
end


end (* structure Ast *)

