(* File: dec_cvt.sml
   Created: 1997-03-26
   Modified: 1997-03-26
*)


structure Dec_cvt :
  sig
    val exp_to_vector : Ast.exp -> Word32.word Vector.vector
    val vector_to_exp : Ast.symbol Ast.Symbol_HashTable.hash_table option * 
      Word32.word Vector.vector -> Ast.exp
    val dec_to_vector : Ast.dec -> Word32.word Vector.vector
    val vector_to_dec : Ast.symbol Ast.Symbol_HashTable.hash_table option * 
      Word32.word Vector.vector -> Ast.dec
  end = 
struct

open Lib List1 Ast

datatype ty_var_list = 
  ty_var_list_nil
| ty_var_list_cons of symbol * ty_var_list

datatype ty_exp' =
  ty_var_exp' of symbol
| ty_con_exp' of symbol * ty_exp_list

and ty_exp_list = 
  ty_exp_list_nil 
| ty_exp_list_cons of ty_exp' * ty_exp_list

datatype ty_schema' = ty_schema of ty_var_list * ty_exp'

datatype exp' =
  app_exp' of symbol * exp_list * ty_exp'
| case_exp' of exp' * rule_list * ty_exp'
| let_exp' of dec_list * exp' * ty_exp'
| as_exp' of symbol * exp' * ty_exp'

and exp_list =
  exp_list_nil
| exp_list_cons of exp' * exp_list

and rule_list =
  rule_list_nil
| rule_list_cons of exp' * exp' * rule_list

and dec' = dec of symbol * exp' * exp' * ty_schema'

and dec_list = dec_list_nil | dec_list_cons of dec' * dec_list

fun to_ty_var_list( Xs : ty_var list ) =
  case Xs of
    [] => ty_var_list_nil
  | X :: Xs => ty_var_list_cons( X, to_ty_var_list Xs )

fun to_ty_exp'( TE : ty_exp ) =
  case TE of
    ty_var_exp V => ty_var_exp'( V )
  | ty_con_exp( Con, Args ) => 
      ty_con_exp'( Con, to_ty_exp_list Args )

and to_ty_exp_list( Xs : ty_exp list ) =
  case Xs of
    [] =>  ty_exp_list_nil
  | X :: Xs => ty_exp_list_cons( to_ty_exp' X, to_ty_exp_list Xs )


fun to_ty_schema'( { schematic_vars, ty_exp } : ty_schema ) =
  ty_schema( to_ty_var_list schematic_vars, to_ty_exp' ty_exp )

fun to_exp'( E : exp ) =
  case E of
    app_exp{ func, args, exp_info } =>
      app_exp'( func, to_exp_list args, to_ty_exp' exp_info )
  | case_exp{ exp, rules, exp_info } =>
      case_exp'( to_exp' exp, to_rule_list rules, to_ty_exp' exp_info )
  | let_exp{ dec_list, exp, exp_info } =>
      let_exp'( to_dec_list dec_list, to_exp' exp, to_ty_exp' exp_info )
  | as_exp{ var, pat, exp_info } =>
      as_exp'( var, to_exp' pat, to_ty_exp' exp_info )
       
and to_exp_list( Es : exp list ) =
  case Es of
    [] => exp_list_nil
  | X :: Xs => exp_list_cons( to_exp' X, to_exp_list Xs )

and to_rule_list( Xs : ( exp_info_type, dec_info_type ) rule_type list ) =
  case Xs of
    [] => rule_list_nil
  | { pat, exp, ... } :: Xs  => 
      rule_list_cons( to_exp' pat, to_exp' exp, to_rule_list Xs )

and to_dec'( { func, pat, exp, dec_info } : dec ) =
  dec( func, to_exp' pat, to_exp' exp, to_ty_schema' dec_info )

and to_dec_list( Ds : dec list ) =
  case Ds of
    [] => dec_list_nil
  | X :: Xs => dec_list_cons( to_dec' X, to_dec_list Xs )



structure H = Symbol_HashTable
exception Sym_mapping_ref_exn
val Sym_mapping_ref : symbol H.hash_table option ref = ref NONE

fun from_symbol( Sym : symbol ) =
  case !Sym_mapping_ref of
    NONE => Sym
  | SOME Sym_mapping =>
      if is_predefined_sym Sym then
        H.lookup Sym_mapping Sym
      else
        Sym

fun from_ty_var_list Xs =
  case Xs of
    ty_var_list_nil => []
  | ty_var_list_cons( X, Xs ) => from_symbol X :: from_ty_var_list Xs

fun from_ty_exp' TE =
  case TE of
    ty_var_exp' V => ty_var_exp( from_symbol V )
  | ty_con_exp'( Con, Args ) => 
      ty_con_exp( from_symbol Con, from_ty_exp_list Args )

and from_ty_exp_list Xs =
  case Xs of
    ty_exp_list_nil => []
  | ty_exp_list_cons( X, Xs ) =>
      from_ty_exp' X :: from_ty_exp_list Xs

fun from_ty_schema'( ty_schema( Vars, TE ) ) : ty_schema =
  { schematic_vars = from_ty_var_list Vars,
    ty_exp = from_ty_exp' TE }

fun from_exp' E =
  case E of
    app_exp'( func, args, exp_info ) =>
      app_exp{ func = from_symbol func,
        args = from_exp_list args,
        exp_info = from_ty_exp' exp_info }
  | case_exp'( exp, rules, exp_info ) =>
      case_exp{ exp = from_exp' exp,
        rules = from_rule_list rules,
        exp_info = from_ty_exp' exp_info }
  | let_exp'( dec_list, exp, exp_info ) =>
      let_exp{ dec_list = from_dec_list dec_list,
        exp = from_exp' exp,
        exp_info = from_ty_exp' exp_info }
  | as_exp'( var, pat, exp_info ) =>
      as_exp{ var = from_symbol var,
        pat = from_exp' pat,
        exp_info = from_ty_exp' exp_info }
        
and from_exp_list Xs =
  case Xs of
    exp_list_nil => []
  | exp_list_cons( X, Xs ) => from_exp' X :: from_exp_list Xs

and from_rule_list Xs =
  case Xs of
    rule_list_nil =>  []
  | rule_list_cons( pat, exp, Xs ) => 
      mk_new_rule( from_exp' pat, from_exp' exp ) :: from_rule_list Xs

and from_dec'( dec( func, pat, exp, dec_info ) ) : dec =
  { func = from_symbol func, pat = from_exp' pat,
    exp = from_exp' exp, dec_info = from_ty_schema' dec_info }

and from_dec_list Xs =
  case Xs of
    dec_list_nil => []
  | dec_list_cons( X, Xs ) => from_dec' X :: from_dec_list Xs

  
(* Copied from make_spec.sml: *)

val Dynarr : Word32_dyn.array = Word32_dyn.array( 2, 0wx0 )

val Dynarr_top = ref 0

fun reserve N = ( Dynarr_top := !Dynarr_top + N )
fun store( X, Addr ) = Word32_dyn.update( Dynarr, Addr, X )

val Vector_to_call_count = ref 0
val Max_vector_to_call_count = Lib.Max_int
exception Heap_overflow_exn



fun output_hash _ = ()


fun symbol_category_to_word func_sym = Word32.fromInt 0
  | symbol_category_to_word var_sym = Word32.fromInt 1
  | symbol_category_to_word emb_sym = Word32.fromInt 2
  | symbol_category_to_word not_activated_sym = Word32.fromInt 3
  | symbol_category_to_word dont_know_sym = Word32.fromInt 4
  | symbol_category_to_word ty_var_sym = Word32.fromInt 5
  | symbol_category_to_word ty_con_sym = Word32.fromInt 6
  | symbol_category_to_word int_sym = Word32.fromInt 7
  | symbol_category_to_word real_sym = Word32.fromInt 8

and symbol_to_dynarr( Start_addr : Word32.word, Xs : symbol ) : int =
let val N = !Dynarr_top in
case Xs of
  ((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 0, N );
    store( symbol_category_to_word X1, N+1 );
    store( X2, N+2 );
    store( X3, N+3 );
    N
    )

end

and ty_var_list_to_dynarr( Start_addr : Word32.word, Xs : ty_var_list ) : int =
let val N = !Dynarr_top in
case Xs of
  ty_var_list_nil => ( reserve 1; store( Word32.fromInt 0, N ); N )

| ty_var_list_cons((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * ty_var_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end

and ty_exp'_to_dynarr( Start_addr : Word32.word, Xs : ty_exp' ) : int =
let val N = !Dynarr_top in
case Xs of
  ty_var_exp'(X1) => (
    reserve 2;
    store( Word32.fromInt 0, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    N
    )

| ty_con_exp'((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end

and ty_exp_list_to_dynarr( Start_addr : Word32.word, Xs : ty_exp_list ) : int =
let val N = !Dynarr_top in
case Xs of
  ty_exp_list_nil => ( reserve 1; store( Word32.fromInt 0, N ); N )

| ty_exp_list_cons((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end

and ty_schema'_to_dynarr( Start_addr : Word32.word, Xs : ty_schema' ) : int =
let val N = !Dynarr_top in
case Xs of
  ty_schema((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 0, N );
    store( Word32.+(Word32.fromInt( 4 * ty_var_list_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end

and exp'_to_dynarr( Start_addr : Word32.word, Xs : exp' ) : int =
let val N = !Dynarr_top in
case Xs of
  app_exp'((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 0, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    N
    )

| case_exp'((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * rule_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    N
    )

| let_exp'((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 2, N );
    store( Word32.+(Word32.fromInt( 4 * dec_list_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    N
    )

| as_exp'((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 3, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * ty_exp'_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    N
    )

end

and exp_list_to_dynarr( Start_addr : Word32.word, Xs : exp_list ) : int =
let val N = !Dynarr_top in
case Xs of
  exp_list_nil => ( reserve 1; store( Word32.fromInt 0, N ); N )

| exp_list_cons((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end

and rule_list_to_dynarr( Start_addr : Word32.word, Xs : rule_list ) : int =
let val N = !Dynarr_top in
case Xs of
  rule_list_nil => ( reserve 1; store( Word32.fromInt 0, N ); N )

| rule_list_cons((X1,X2,X3)) => (
    reserve 4;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * rule_list_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    N
    )

end

and dec'_to_dynarr( Start_addr : Word32.word, Xs : dec' ) : int =
let val N = !Dynarr_top in
case Xs of
  dec((X1,X2,X3,X4)) => (
    reserve 5;
    store( Word32.fromInt 0, N );
    store( Word32.+(Word32.fromInt( 4 * symbol_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    store( Word32.+(Word32.fromInt( 4 * exp'_to_dynarr( Start_addr, X3)), Start_addr) , N+3 );
    store( Word32.+(Word32.fromInt( 4 * ty_schema'_to_dynarr( Start_addr, X4)), Start_addr) , N+4 );
    N
    )

end

and dec_list_to_dynarr( Start_addr : Word32.word, Xs : dec_list ) : int =
let val N = !Dynarr_top in
case Xs of
  dec_list_nil => ( reserve 1; store( Word32.fromInt 0, N ); N )

| dec_list_cons((X1,X2)) => (
    reserve 3;
    store( Word32.fromInt 1, N );
    store( Word32.+(Word32.fromInt( 4 * dec'_to_dynarr( Start_addr, X1)), Start_addr) , N+1 );
    store( Word32.+(Word32.fromInt( 4 * dec_list_to_dynarr( Start_addr, X2)), Start_addr) , N+2 );
    N
    )

end


val V_ref = ref( Vector.fromList( [] : Word32.word list ) )

fun persistence_sub( I : int ) = Vector.sub( !V_ref, I )


fun word_to_symbol_category( 0wx0 : Word32.word ) = ( output_hash 0; func_sym )
  | word_to_symbol_category( 0wx1 : Word32.word ) = ( output_hash 1; var_sym )
  | word_to_symbol_category( 0wx2 : Word32.word ) = ( output_hash 2; emb_sym )
  | word_to_symbol_category( 0wx3 : Word32.word ) = ( output_hash 3; not_activated_sym )
  | word_to_symbol_category( 0wx4 : Word32.word ) = ( output_hash 4; dont_know_sym )
  | word_to_symbol_category( 0wx5 : Word32.word ) = ( output_hash 5; ty_var_sym )
  | word_to_symbol_category( 0wx6 : Word32.word ) = ( output_hash 6; ty_con_sym )
  | word_to_symbol_category( 0wx7 : Word32.word ) = ( output_hash 7; int_sym )
  | word_to_symbol_category( 0wx8 : Word32.word ) = ( output_hash 8; real_sym )

and vector_to_symbol( Start_addr : Word32.word, Xs : int ) : symbol =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => 
    ((
      word_to_symbol_category(  persistence_sub( Xs+1 )),
      (  persistence_sub( Xs+2 )),
      (  persistence_sub( Xs+3 ))))

end

and vector_to_ty_var_list( Start_addr : Word32.word, Xs : int ) : ty_var_list =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => ty_var_list_nil
| 1 => 
    ty_var_list_cons((
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_ty_var_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end

and vector_to_ty_exp'( Start_addr : Word32.word, Xs : int ) : ty_exp' =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => 
    ty_var_exp'(
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ))
| 1 => 
    ty_con_exp'((
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end

and vector_to_ty_exp_list( Start_addr : Word32.word, Xs : int ) : ty_exp_list =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => ty_exp_list_nil
| 1 => 
    ty_exp_list_cons((
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end

and vector_to_ty_schema'( Start_addr : Word32.word, Xs : int ) : ty_schema' =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => 
    ty_schema((
      vector_to_ty_var_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end

and vector_to_exp'( Start_addr : Word32.word, Xs : int ) : exp' =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => 
    app_exp'((
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 )))
| 1 => 
    case_exp'((
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_rule_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 )))
| 2 => 
    let_exp'((
      vector_to_dec_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 )))
| 3 => 
    as_exp'((
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_ty_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 )))

end

and vector_to_exp_list( Start_addr : Word32.word, Xs : int ) : exp_list =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => exp_list_nil
| 1 => 
    exp_list_cons((
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end

and vector_to_rule_list( Start_addr : Word32.word, Xs : int ) : rule_list =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => rule_list_nil
| 1 => 
    rule_list_cons((
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_rule_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 )))

end

and vector_to_dec'( Start_addr : Word32.word, Xs : int ) : dec' =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => 
    dec((
      vector_to_symbol( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 ),
      vector_to_exp'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+3 ), Start_addr ) ) div 4 ),
      vector_to_ty_schema'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+4 ), Start_addr ) ) div 4 )))

end

and vector_to_dec_list( Start_addr : Word32.word, Xs : int ) : dec_list =
if ( Vector_to_call_count := !Vector_to_call_count + 1;
     !Vector_to_call_count) > Max_vector_to_call_count then
  raise Heap_overflow_exn
else
let val X = Word32.toInt(  persistence_sub( Xs ) )
in
output_hash X;
case X of
  0 => dec_list_nil
| 1 => 
    dec_list_cons((
      vector_to_dec'( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+1 ), Start_addr ) ) div 4 ),
      vector_to_dec_list( Start_addr, Word32.toInt(Word32.-( persistence_sub( Xs+2 ), Start_addr ) ) div 4 )))

end





fun exp_to_vector( E : exp ) = (
  Dynarr_top := 0;
  exp'_to_dynarr( 0w0, to_exp' E );
  Vector.tabulate( !Dynarr_top, 
    fn I => Word32_dyn.sub( Dynarr, I ) )
  )

fun vector_to_exp( Sym_mapping, V : Word32.word Vector.vector ) : exp = (
  Sym_mapping_ref := Sym_mapping;
  V_ref := V;
  from_exp'( vector_to_exp'( 0w0, 0 ) )
  )
  


fun dec_to_vector( D : dec ) = (
  Dynarr_top := 0;
  dec'_to_dynarr( 0w0, to_dec' D );
  Vector.tabulate( !Dynarr_top, 
    fn I => Word32_dyn.sub( Dynarr, I ) )
  )

fun vector_to_dec( Sym_mapping, V : Word32.word Vector.vector ) : dec = (
  Sym_mapping_ref := Sym_mapping;
  V_ref := V;
  from_dec'( vector_to_dec'( 0w0, 0 ) )
  )
  


end (* structure Dec_cvt *)
