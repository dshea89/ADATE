(*
  File: make_spec.sml.
  Created: 1996-06-07.
  Modified: 1997-05-06.
*)

signature GRADE =
sig

type grade
val zero : grade
val + : grade * grade -> grade
val toRealOpt : ( grade -> real )option
val post_process : grade -> grade
val comparisons : ( grade * grade -> order ) list
val toString : grade -> string
val pack : grade -> string
val unpack : string -> grade

end

signature SPEC =
sig

val clear : unit -> unit
val get : unit -> real

val Output_type_is_unboxed : bool
val Spec_file_name : string
type input_type
type output_type
val input_type_to_dynarr : Word32.word * input_type -> unit
val vector_to_output_type : Word32.word * int -> output_type


val Inputs : input_type list

(* Only used if Grade.toRealOpt is not NONE which implies neural net usage: *)
(*
val Input_arrays : real Array.array Array.array
val Output_arrays : real Array.array Array.array
*)
(* val real_outputs : output_type -> real Vector.vector *)


val Validation_inputs : input_type list
val Abstract_types : string list
val Funs_to_use : string list
val Reject_funs : ( ('a,'b)Ast.e -> bool ) list
val restore_transform : ('a,'b)Ast.d -> ('a,'b)Ast.d
structure Grade : GRADE
val Initial_program : string option
val output_eval_fun : int * input_type * output_type ->
  Ast_lib.output_eval_type * Grade.grade


val Max_lcs_class_card : int
val LCS_class_synt_compl_ratio : real
val Max_output_class_card : int
val Time_class_card : int
val Max_scm_class_card : int
val Scm_class_synt_compl_ratio : real

val Max_time_distribution :  int list
val Pe_survival_weights : real list
end (* signature SPEC *)

signature MAKE_SPEC =
sig

val make_spec : string -> unit
val extract_decs : string -> Ast.datatype_dec list * Ast.ty_exp *
      Ast.ty_exp * Ast.dec list

val sigmoid : real -> real

datatype rconst = rconst of int * real * real

val square_dist :  real Array.array * real Array.array -> real
val indexofmax :  real Array.array -> int

structure Random : RANDOM

val Dynarr : Lib.Word32_dyn.array 
val Dynarr_top : int ref
val reserve : int -> unit
val store : Word32.word * int -> unit
val int_to_word : int -> Word32.word

val Vector_to_call_count : int ref
val Max_vector_to_call_count : int

exception Heap_overflow_exn 


end


structure Make_spec : MAKE_SPEC =
struct
open Lib List1 Ast Ast_lib

structure Random = Random

val Output_type_is_unboxed = ref false

(* Definitions to be used by the <EXAMPLE NAME>.spec.sml file: *)

fun sigmoid( X : real ) :  real = 1.0 / ( 1.0 + Math.exp( ~X ) )

datatype rconst = rconst of int * real * real

fun square_dist( Xs : real Array.array, Ys : real Array.array ) : real =
let
  val S = ref 0.0
  fun sqr X = X * X
in
  for( 0, Array.length Xs - 1, fn I =>
    S := !S + sqr( Array.sub(Xs,I) - Array.sub(Ys,I) ) );
  !S
end

fun indexofmax( Xs : real Array.array ) : int =
let
  val I' = ref 0
  val M' = ref( Array.sub( Xs, 0 ) )
in
  for( 1, Array.length Xs - 1, fn I =>
    case Array.sub( Xs, I ) of M =>
    if M > !M' then ( M' := M; I' := I ) else () );
  !I'
end


val Dynarr : Word32_dyn.array = Word32_dyn.array( 2, 0wx0 )

val Dynarr_top = ref 0

fun reserve N = ( Dynarr_top := !Dynarr_top + N )
fun store( X, Addr ) = Word32_dyn.update( Dynarr, Addr, X )

val int_to_word = Word32.fromInt

val Vector_to_call_count = ref 0
val Max_vector_to_call_count = 
  Constants.Heap_size div 10

exception Heap_overflow_exn


fun find_ddec( Ty_con : symbol, Ds : datatype_dec list ) =
  case filter( fn{ty_con,...} => ty_con=Ty_con, Ds ) of
    D::nil => D

fun concat_list [] = ""
  | concat_list( X::Xs ) = X ^ concat_list Xs

fun convert_domain( 
      TE : ty_exp, 
      convert_par_type : symbol * int -> string ) : string =
  let
    val I = ref 0
    fun mk( ty_con_exp( Ty_con, [] ) ) = 
          ( inc I; convert_par_type(Ty_con,!I) )
      | mk( ty_con_exp( Ty_con, Args ) ) =
          "(" ^ 
          concat_list(map( fn Arg => mk Arg ^ ",", lt Args )) ^
          mk(dh Args) ^ ")"
  in
    mk TE
  end





fun datatypes_to_dynarray( Ds : datatype_dec list ) : string =
(*
  The returned string contains defs of functions that translate from
  an expression represented using the datatypes in Ds to a dynamic 
  array of ints.
*)
  case Ds of [] => "" | _ =>
let
exception Not_implemented_alt_to_dynarray
fun alt_to_dynarray( 
      Code : int,
      { constr : symbol, domain : ty_exp option }
      ) : string =
  case domain of
    NONE =>
      symbol_to_string constr ^ " => ( reserve 1; store( Word32.fromInt " ^
      Int.toString Code ^ ", N ); N )\n"
  | SOME DT =>
  let
    fun mk_var I = "X" ^ Int.toString I
    val Ty_syms = tuple_ty_syms DT
    val Arity = length Ty_syms
  in
    symbol_to_string constr ^ "(" ^
    convert_domain( DT, fn(_,I) => mk_var I ) ^
    ") => (\n" ^
    "    reserve " ^ Int.toString( Arity+1 ) ^ ";\n" ^
    "    store( Word32.fromInt " ^ Int.toString Code ^ ", N );\n" ^
    foldright(
      "",
      fn( (Ty_sym,I), So_far ) =>
        let
          val Unboxed = Ty_sym=INT orelse Ty_sym<>REAL andalso
            is_unboxed(find_ddec(Ty_sym,Ds))
        in
        "    store( " ^ 
        (if Unboxed then "" else "Word32.+(Word32.fromInt( 4 * ") ^
        symbol_to_string Ty_sym ^
        (if Unboxed then
           "_to_word "
         else
           "_to_dynarr( Start_addr, "
         ) ^ mk_var I ^ 
        (if Unboxed then "" else ")), Start_addr) ") ^
        ", N+" ^ Int.toString I ^
        " );\n" ^ So_far
        end,
      combine( Ty_syms, fromto(1,Arity) )
      ) ^
    "    N\n" ^
    "    )\n"
  end (* fun alt_to_dynarray *)
         
exception Not_implemented_to_dynarray
fun to_dynarray( D as { ty_con, ty_pars, alts } : datatype_dec )
    : string =
  case ty_pars of
    _::_ => raise Not_implemented_to_dynarray
  | _ =>
  if is_unboxed D then
  let
    val Fun_name = symbol_to_string ty_con ^ "_to_word"
  in
    foldright(
      "",
      fn( ( {constr,...}, N ), So_far ) =>
        Fun_name ^ " " ^ symbol_to_string constr ^
        " = Word32.fromInt " ^ Int.toString N ^
        (if So_far="" then "\n" else "\n  | ") ^ So_far,
        combine( alts, fromto( 0, length alts -1 ) )
        )
  end
  else
  let 
    val BT = symbol_to_string ty_con
    val Fun_name = BT ^ "_to_dynarr"
  in
    Fun_name ^ "( Start_addr : Word32.word, Xs : " ^ BT ^ " ) : int =\n" ^
    "let val N = !Dynarr_top in\n" ^
    "case Xs of\n" ^
    "  " ^
    foldright(
      "",
      fn( (Alt,N), So_far ) =>
        alt_to_dynarray(N,Alt) ^
        (if So_far="" then "\n" else "\n| ") ^ So_far,
        combine( alts, fromto( 0, length alts-1 ) )
        ) ^
    "end\n"
  end (* fun to_dyn_array *)

in
  "fun " ^
  foldright(
    "",
    fn(D,So_far) => to_dynarray D ^
      (if So_far="" then "\n" else "\nand ") ^ So_far,
    Ds
    )
end (* fun datatypes_to_dynarray *)
 
  

fun datatypes_vector_to( Ds : datatype_dec list, Ds' : datatype_dec list ) 
  : string =
(*
  The returned string contains defs of functions that translate from
  a vector of ints to an expression represented using the datatypes
  in Ds.
*)
  case Ds of [] => "" | _ =>
let

exception Not_implemented_alt_vector_to
fun alt_vector_to( 
      Code : int,
      { constr : symbol, domain : ty_exp option }
      ) : string =
  case domain of
    NONE =>
      Int.toString Code ^ " => " ^ symbol_to_string constr 
  | SOME DT =>
  let
    val Ty_syms = tuple_ty_syms DT
    val Arity = length Ty_syms
    fun convert_par_type( Ty_sym,I) =
      let
        val Unboxed = Ty_sym=INT orelse 
          Ty_sym<>REAL andalso is_unboxed(find_ddec(Ty_sym,Ds@Ds')) 
      in
      "\n      " ^
      (if Unboxed then
         "word_to_" ^ symbol_to_string Ty_sym ^
         "( " ^ C_interface.mk_heap_sub_call( "Xs+" ^ Int.toString I ) ^ ")"
       else
         "vector_to_" ^ symbol_to_string Ty_sym ^ 
         "( Start_addr, Word32.toIntX(Word32.-(" ^
         C_interface.mk_heap_sub_call( "Xs+" ^ Int.toString I ) ^
         ", Start_addr ) ) div 4 )"
      )
      end
  in
    Int.toString Code ^ " => " ^ "\n" ^
    "    " ^ symbol_to_string constr ^ "(" ^
    convert_domain( DT, convert_par_type ) ^ ")"
  end (* fun alt_vector_to *)
         
exception Not_implemented_vector_to
fun vector_to( D as { ty_con, ty_pars, alts } : datatype_dec )
    : string =
  case ty_pars of
    _::_ => raise Not_implemented_vector_to
  | _ =>
  if is_unboxed D then
  let
    val Fun_name = "word_to_" ^ symbol_to_string ty_con
  in
    foldright(
      "",
      fn( ( {constr,...}, N ), So_far ) =>
        Fun_name ^ "( 0wx" ^ Word32.toString(Word32.fromInt N) ^ 
        " : Word32.word ) = ( output_hash " ^ Int.toString N ^ "; " ^
        symbol_to_string constr ^ " )" ^
        (if So_far="" then "\n" else "\n  | ") ^ So_far,
        combine( alts, fromto( 0, length alts -1 ) )
        )
  end
  else
  let 
    val BT = symbol_to_string ty_con
    val Fun_name = "vector_to_" ^ BT
  in
    Fun_name ^ "( Start_addr : Word32.word, Xs : int ) : " 
    ^ BT ^ " =\n" ^
    "if ( Vector_to_call_count := !Vector_to_call_count + 1;\n" ^
    "     !Vector_to_call_count) > Max_vector_to_call_count then\n" ^
    "  raise Heap_overflow_exn\n" ^
    "else\n" ^
    "let val X = Word32.toIntX " ^ 
    C_interface.mk_heap_sub_call "Xs" ^ "\n" ^
    "in\n" ^
    "output_hash X;\n" ^
    "case X of\n" ^
    "  " ^
    foldright(
      "",
      fn( (Alt,N), So_far ) =>
        alt_vector_to(N,Alt) ^
        (if So_far="" then "\n" else "\n| ") ^ So_far,
        combine( alts, fromto( 0, length alts-1 ) )
        ) ^ "\n" ^
    "end\n"
  end (* fun vector_to *)

in
  "fun " ^
  foldright(
    "",
    fn(D,So_far) => vector_to D ^
      (if So_far="" then "\n" else "\nand ") ^ So_far,
    Ds
    )
end (* fun datatypes_vector_to *)
 


exception Not_implemented_input_type_to_dynarray

fun input_type_to_dynarray( 
      Input_type : ty_exp,
      Ds : datatype_dec list
      ) : string =
  let
    val Ty_syms = tuple_ty_syms Input_type
    val Arity = length Ty_syms
    fun mk_var I = "X" ^ Int.toString I
  in
    "fun input_type_to_dynarr( Start_addr : Word32.word, " ^
    convert_domain( Input_type, fn(_,I) => mk_var I ) ^
    ") = \n" ^
    "let val N = !Dynarr_top in\n" ^
    "  reserve " ^ Int.toString Arity ^ ";\n" ^
    foldright(
      "",
      fn( (Ty_sym,I), So_far ) =>
        (if Ty_sym=INT orelse 
            Ty_sym<>REAL andalso is_unboxed( find_ddec(Ty_sym,Ds) ) then
           "  store( " ^ symbol_to_string Ty_sym ^
           "_to_word " ^ mk_var I ^ ", N+" ^ Int.toString(I-1) 
         else
           "  store( Word32.+(Word32.fromInt( 4 * " ^
           symbol_to_string Ty_sym ^
           "_to_dynarr( Start_addr, " ^ mk_var I ^ ")), Start_addr) , N+" ^ 
           Int.toString(I-1)
         ) ^
        " )" ^
        (if So_far="" then "\n" else ";\n") ^ So_far,
      combine( Ty_syms, fromto(1,Arity) ) 
      ) ^
    "end"
  end (* fun input_type_to_dynarray *)




exception Not_implemented_output_type_vector_to

fun output_type_vector_to( 
      Output_type : ty_exp,
      Ds : datatype_dec list
      ) : string =
    "fun vector_to_output_type( Start_addr : Word32.word, Xs : int )\n" ^
    "    : output_type = ( Vector_to_call_count := 0;\n" ^ (
  case tuple_ty_syms Output_type of Ty_syms =>
  case Ty_syms of
    [ Ty_sym ] =>
      if Ty_sym=INT orelse 
           Ty_sym<>REAL andalso is_unboxed( find_ddec(Ty_sym,Ds) ) then (
        Output_type_is_unboxed := true;
        "word_to_" ^ symbol_to_string Ty_sym ^ "( Word32.fromInt Xs )"
        )
      else
         "vector_to_" ^ symbol_to_string Ty_sym ^ 
         "( Start_addr, Xs )"
  | _ :: _ =>
      "\nlet\n" ^
      datatypes_vector_to( [ { ty_con = OUTPUT_TYPE, ty_pars=[], alts = [
        { constr = string_to_symbol( func_sym, "" ), 
          domain = SOME Output_type } ] } ], Ds ) ^
      "\nin\n" ^
      "vector_to_output_type( Start_addr, Xs )\n" ^
      "\nend\n"
  ) ^
  ")\n"


exception Read_file

fun read_file( File : string ) 
    : string * parse_result list * string =
  let
    val Stream = TextIO.openIn File
    val Std_in_string = TextIO.inputAll Stream
    fun find_pos I =
      if String.sub( Std_in_string, I ) = #"%" andalso
         String.sub( Std_in_string,  I+1 ) = #"%"
      then
        I
      else
        find_pos( I+1 )
    val N = CharVector.length Std_in_string
    val Pos = find_pos 0
    val First = 
      Substring.string(
        Substring.substring( Std_in_string, 0, Pos )
        )
    val Last = 
      Substring.string(
        Substring.substring( Std_in_string, Pos+2, N-Pos-2 )
        )
    val () = TextIO.closeIn Stream
  in
    ( First, Parse.parse_declarations First, Last )
  end (* fun read_file *)
  handle Ex => (
    output(!std_err,
      "\nERROR : Something went wrong when trying to open or parse the\n" ^ 
      "specification file " ^ File ^ ".\n" ^
      "Make sure that the syntax of this file is ok, for example that\n" ^
      "the %% separator is in the right position.\n"
      );
    raise Ex
    )



exception Make_spec' 
exception Do_not_redefine_bool
exception Do_not_redefine_rconst

fun make_spec'( Spec_file : string, Write : bool ) 
    : ( datatype_dec list * ty_exp * ty_exp * dec list ) option =
  let
    val ( First, Parse_result, Last ) = read_file Spec_file
    val Ddecs = 
      flat_map( 
        fn parsed_datatype Decs => Decs
         | _ => [],
        Parse_result 
        )

    val _ = map( fn{ ty_con, ... } =>
      if ty_con = BOOL then
        raise Do_not_redefine_bool
      else if ty_con = RCONST_TYPE then
        raise Do_not_redefine_rconst
      else
        (),
      Ddecs )
    val Datatype_dec_bool = {
      ty_con = BOOL,
      ty_pars = [],
      alts = [
        { constr = FALSE, domain = NONE },
        { constr = TRUE,  domain = NONE }
        ]
      }
    val Datatype_dec_rconst = {
      ty_con = RCONST_TYPE,
      ty_pars = [],
      alts = [
        { constr = RCONST,  
          domain = SOME( ty_con_exp( TUPLE_TY_CON, [
            ty_con_exp( INT, nil ),
            ty_con_exp( REAL, nil ),
            ty_con_exp( REAL, nil ) ] ) ) } 
        ]
      }
    val Ddecs = Datatype_dec_bool :: Datatype_dec_rconst :: Ddecs
    val Parse_result = 
      filter( 
        fn parsed_datatype _ => false | _ => true, 
        Parse_result
        )
    val Fun_decs =
      flat_map( 
        fn parsed_fun Decs => Decs
         | _ => [],
        Parse_result 
        )
    val Parse_result = 
      filter( 
        fn parsed_fun _ => false  | _ => true, 
        Parse_result
        )
    fun inp_out_type_error() = (
      output( !std_err,
        "\nERROR : The specification file should contain exactly two type\n" ^
        "declarations, namely first one of the form\n\n" ^
        "type input_type = <TUPLE TYPE DEFINITION>\n\n" ^
        "and then one of the form\n\n" ^
        "type output_type = <TYPE NAME>\n"
        );
      raise Make_spec'
      )
    val ( Input_type, Output_type ) =
      case Parse_result of
        [ parsed_type { ty_con = Con1, ty_pars = [], ty_exp = TE1 },
          parsed_type { ty_con = Con2, ty_pars = [], 
            ty_exp = TE2 as ty_con_exp( _, [] ) }
        ]   =>
          if Con1 = INPUT_TYPE andalso Con2 = OUTPUT_TYPE then
            ( TE1, TE2 )
          else
            inp_out_type_error()
      | _ => inp_out_type_error()

  in
  if not Write then
    SOME( Ddecs, Input_type, Output_type, Fun_decs )
  else 
    case TextIO.openOut( Spec_file ^ ".sml" ) of Ostrm => (
    output( Ostrm,
"structure spec : SPEC = \n" ^
"struct\n" ^
"\n" ^
"open Lib List1 Ast Ast_lib C_interface Make_spec\n" ^
"local \n\
\ \n\
\val Output_hash_val : real ref = ref ~0.1435 \n\
\ \n\
\val N_rands = 20000 \n\
\ \n\
\local \n\
\  val Rand = Random.rand( 776354, ~487346 ) \n\
\in \n\
\ \n\
\val Rand_vector : real vector = \n\
\  Vector.tabulate( N_rands, fn I => Random.randReal Rand - 0.5 ) \n\
\end \n\
\ \n\
\val Rand_vector_index = ref ~1 \n\
\ \n\
\fun next_random() = ( \n\
\  Rand_vector_index := !Rand_vector_index + 1; \n\
\  Vector.sub( Rand_vector, !Rand_vector_index ) \n\
\  ) \n\
\  handle Subscript => ( \n\
\    Rand_vector_index := ~1; \n\
\    next_random() \n\
\    ) \n\
\ \n\
\val M = real Big_prime \n\
\ \n\
\in \n\
\ \n\
\fun clear() = ( \n\
\  Rand_vector_index := ~1; \n\
\  Output_hash_val := ~0.1435 \n\
\  ) \n\
\   \n\
\fun output_hash( X : int ) : unit = \n\
\  Output_hash_val := ( real X + 2.0 ) * next_random() + !Output_hash_val \n\
\     \n\
\fun output_hash_real( X : real ) : unit = \n\
\  Output_hash_val := ( X + 2.0 ) * next_random() + !Output_hash_val \n\
\     \n\
\ \n\
\ \n\
\fun get() = !Output_hash_val \n\
\ \n\
\end (* local *) \n\n\n \
\fun word_to_int( X : Word32.word ) : int =  \n\
\  case Word32.toIntX X of X => (output_hash X; X )  \n\
\ \n\
\fun real_to_dynarr( Start_addr : Word32.word, X : real ) : int = \n\
\let \n\
\  val N = !Dynarr_top \n\
\  val ( W2, W1 ) = C_interface.real_to_doubleword X \n\
\in \n\
\  reserve 2; \n\
\  store( W1, N ); \n\
\  store( W2, N+1 ); \n\
\  N \n\
\end \n\
\ \n\
\fun vector_to_real( Start_addr : Word32.word, Xs : int ) : real = \n\
\let \n\
\  val XXX = Heap_addr_int + 4*Xs \n\
\  val X = C_interface.read_double XXX \n\
\in \n\
\  output_hash_real X; \n\
\  X \n\
\end \n\
\" ^ "\n\n" ^
"val TCOUNT = 0\n\n" ^
"val Spec_file_name = \"" ^ Spec_file ^ "\"\n\n"
);
    output( Ostrm, First );
    output( Ostrm, "\n\n" ^ datatypes_to_dynarray Ddecs );
    output( Ostrm, "\n\n" ^ datatypes_vector_to( Ddecs, [] ) );
    output( 
      Ostrm, 
      "\n\n" ^ input_type_to_dynarray( Input_type, Ddecs ) 
      );
    output( 
      Ostrm, 
      "\n\n" ^output_type_vector_to( Output_type, Ddecs ) 
      );
    output( Ostrm, "\n\n" ^ Last );
    output( Ostrm, 
"val Output_type_is_unboxed =" ^ Bool.toString( !Output_type_is_unboxed ) ^
"\n\n"  );
    output( Ostrm, "\nend (* structure spec *)" );
    TextIO.closeOut Ostrm;
    NONE
    )
  end (* fun make_spec' *)
          
local

structure H = Symbol_HashTable

exception Change_names
fun change_names( Ds : ('a,'b)d list ) : ('a,'b)d list =
  let
    val Saved_names = map( fn{ func, ... } => func, Ds )
    val Ds = rename_decs( Ds, false )
    val New_names = map( fn{ func, ... } => func, Ds )
    val Subst : sym_subst = 
      H.mkTable( length New_names, Change_names )
  in
    map( fn( New, Old ) => H.insert Subst (New,Old),
      combine( New_names, Saved_names ) );
    map( fn D => apply_sym_subst( D, Subst ), Ds )
  end

    

in

fun extract_decs( Spec_file : string ) =
  case make_spec'( Spec_file, false ) of 
    SOME( TDs, Inp, Out, Ds ) => 
      ( TDs, Inp, Out, change_names Ds )

end (* local *)

fun make_spec( Spec_file : string ) : unit = (
  make_spec'( Spec_file, true );
  ()
  )




end (* structure Make_spec *)
