(*
  File: compile.sml.
  Created: 1996-06-17.
  Modified: 2000-03-01.

Changed 2000-03-01 to use esp-based stack frames instead of ebp-based frames.

Tail recursion optimization added 2000-03-08.

Changed 2000-03-26 to enable calling of floating-point functions.

Example.

Consider compiling

fun append( Xs, Ys ) =
  case Xs of
    nil => Ys
  | cons( X1, Xs1 ) => cons( X1, append( Xs1, Ys ) )

During execution, the stack just before the recursive call to append is:

Offset Contents  Address based on esp

-16    Xs1       esp 
-12    Ys        esp+4
 -8    X1        esp+8
 -4    Xs1       esp+12
  0    ret addr  esp+16
  4    Xs        esp+20
  8    Ys        esp+24

The address of a variable on the stack is esp + 4*Push_count + Offset,
where esp + 4*Push_count is the absolute address to ret addr.
Offset is stored in Var_entry_table.

Register usage:
Scratch: eax, ecx
Result: ebx
Call count: edx



*)

signature COMPILE  =
sig


datatype mnemonic = push | pop | pusha | popa | call | ret | mov 
  | add | sub | neg
  | mul | dec | inc' | cmp | test | xor | jmp | jz | jg 
  | setl | sete | cmovle | cmove | nop | align

datatype reg = eax | ebx | ecx | edx | edi | esi | ebp | esp

datatype operand =
    none
  | immediate of Word32.word
  | register of reg
  | direct of Word32.word
  | indirect of reg 
  | indexed of reg * Word32.word
  | label of Ast.symbol

type instruction = mnemonic * operand * operand


val Q_sym_handler_sym : Ast.symbol
val Call_count_overflow_handler_sym : Ast.symbol
val Heap_overflow_handler_sym : Ast.symbol

val assembly_to_string : instruction Array.array * int * int -> string


val  compile_supers : ( '1a, '1b )Ast.d list option * 
  int Ast.Symbol_HashTable.hash_table * 
  (Ast.symbol -> int) * ('1a,'1b)Ast.d list * int * 
  instruction Array.array * bool * Word32.word -> int * Word32.word

val initialize : string * string list -> unit

end (* signature COMPILE *)


structure Compile : COMPILE =
struct
open Lib List1 Ast Ast_lib


(* 
Function used for inlining. Tested by compile_test2.sml.
Example. Convert append( Xs, cons( X1, Ys ) ) to
case cons( X1, Ys ) of V1 => append( Xs, V1 )
*)

fun build_case_defs( app_exp{ func, args, exp_info } : ( 'a, 'b )e ) 
    : ( 'a, 'b )e =
let
  fun g( Args, New_args ) =
    case Args of
      nil => app_exp{ func = func, args = rev New_args, exp_info = exp_info }
    | Arg :: Args =>
    if is_variable_exp Arg then
      g( Args, Arg :: New_args )
    else
    case gen_var_exp( get_exp_info Arg ) of V_exp =>
      case_exp{
        exp = Arg,
        rules = [ mk_new_rule(
          V_exp,
          g( Args, V_exp :: New_args )
          ) ],
        exp_info = exp_info }
in
  g( args, [] )
end (* fun build_case_defs *)









datatype mnemonic = push | pop | pusha | popa | call | ret | mov 
  | add | sub | neg
  | mul | dec | inc' | cmp | test | xor | jmp | jz | jg 
  | setl | sete | cmovle | cmove | nop | align

datatype reg = eax | ebx | ecx | edx | edi | esi | ebp | esp

datatype operand =
    none
  | immediate of Word32.word
  | register of reg
  | direct of Word32.word
  | indirect of reg 
  | indexed of reg * Word32.word
  | label of symbol

type instruction = mnemonic * operand * operand


val Q_sym_handler_sym = string_to_symbol( func_sym, "_Q_sym_handler" )
val Call_count_overflow_handler_sym = 
  string_to_symbol( func_sym, "_Call_count_overflow_handler" )
val Heap_overflow_handler_sym = 
  string_to_symbol( func_sym, "_Heap_overflow_handler" )


fun mnemonic_to_string X = 
  case X of
    push => "push" 
  | pop => "pop" 
  | pusha => "pusha" 
  | popa => "popa" 
  | call => "call" 
  | ret => "ret" 
  | mov => "mov" 
  | add => "add"
  | sub => "sub"
  | neg => "neg"
  | mul => "mul"
  | dec => "dec"
  | inc' => "inc"
  | cmp => "cmp"
  | test => "test"
  | xor => "xor"
  | jmp => "jmp"
  | jz => "jz"
  | jg => "jg"
  | setl => "setl"
  | sete => "sete"
  | cmovle => "cmovle"
  | cmove => "cmove"
  | nop => "nop"
  | align => "align"

fun reg_to_string X =
  case X of
    eax => "eax"
  | ebx => "ebx" 
  | ecx => "ecx"
  | edx => "edx"
  | edi => "edi"
  | esi => "esi"
  | ebp => "ebp"
  | esp => "esp"

fun operand_to_string X = 
  case X of
    none => ""
  | immediate N => Word32.toString N
  | register Reg => reg_to_string Reg
  | direct N => Word32.toString N
  | indirect Reg => "[" ^ reg_to_string Reg ^ "]"
  | indexed(Reg,N) => 
      "[" ^ reg_to_string Reg ^ "+" ^ Word32.toString N ^ "]"
  | label S => symbol_to_string S

fun instruction_to_string( Mnem, Op1, Op2 ) =
  case Op1 of
    none => mnemonic_to_string Mnem
  | _ =>
  case Op2 of
    none => mnemonic_to_string Mnem ^ " " ^ operand_to_string Op1
  | _ =>
    mnemonic_to_string Mnem ^ " " ^ operand_to_string Op1 ^ ", " ^
    operand_to_string Op2
    
    

structure H = Symbol_HashTable


fun assembly_to_string( Assembly : instruction Array.array, Start : int, 
      End : int ) : string =
  foldright(
    "",
    fn(I,Str) =>
      Word32.toString(Word32.fromInt I) ^ " " ^ 
      instruction_to_string( Array.sub(Assembly,I) ) ^
      "\n" ^
      Str,
    fromto(Start,End))


exception Unboxed_constant_table_exn
val Unboxed_constant_table : unit H.hash_table =
  H.mkTable( 10, Unboxed_constant_table_exn )

exception Constructor_table_exn
val Constructor_table: int H.hash_table =
  H.mkTable( 10, Constructor_table_exn )
(* Maps each constructor to its code. Includes TUPLE. *)

exception Normal_fun_name_table_exn
val Normal_fun_name_table : int H.hash_table =
  H.mkTable( 10, Normal_fun_name_table_exn )
(* Stores the arity of a function.
   Is initialized with the functions in the specification.
   For each call to compile_supers, the argument functions are
   added and then deleted.
*)

fun is_unboxed_constant( S : symbol ) =
  is_int S orelse (
  case H.find Unboxed_constant_table S of
    NONE => false
  | SOME _ => true
  )

fun unboxed_constant_to_int( S : symbol ) : int =
  if is_int S then
    int_sym_to_int S
  else
    H.lookup Constructor_table S
    

fun is_simple_arg( app_exp{ func, args=[], ... } ) =
      is_unboxed_constant func orelse is_variable func
  | is_simple_arg _ = false


exception Compile_super
exception Compile_exp
exception Compile_case_alt_exn
exception Update_next_q_sym
exception Function_call_exn
fun compile_super( 
      inlining : symbol -> ( '1a, '1b )d option,
      Fun_entry_table : int H.hash_table,
      Heap_size : int,
      Heap_addr : Word32.word,
      next_q_sym :  symbol -> int,
      Q_sym_code_addr,
      Act_array_addr: Word32.word,
      D : ('1a,'1b)d,
      Start_index : int,
      Assembly_code : instruction Array.array,
      Top_of_heap : Word32.word
      ) : int * Word32.word =
(* Returns index of next free entry in Assembly_code. *)
let
(*
  val _ = (
    p"\ncompile_super:\n";
    Print.print_dec_act_info D;
    nl(); flush_out( !std_out )
    )
*)
  val _ = H.insert Fun_entry_table (#func D, Start_index )
  val Current_addr =  ref Start_index
  val Current_top_of_heap = ref Top_of_heap
  fun update_next( Instr : instruction ) : unit = (
    Array.update( Assembly_code, !Current_addr, Instr );
    inc Current_addr
    )
  val _ = (
    update_next( add,  register edx, immediate( Word32.fromInt 2 ) );
    update_next( jg, label Call_count_overflow_handler_sym, none )
    )

  fun return( Return : bool, Push_count : int,
        Finish_functions : ( unit -> unit ) list ) : int -> unit =
    let
      val F = fn() => loop( fn G => G(), Finish_functions )
    in
      if Return then (
        if Push_count > 0 then
          update_next( add, register esp, 
            immediate( Word32.fromInt(4 * Push_count) ) )
        else
          ();
        update_next( ret,  none, none );
        update_next( align, immediate(Word32.fromInt 16), none );
        F();
        fn _ => ()
        )
      else
        fn _ => ( F(); () )
    end

  fun case_return( Return : bool, Case_push_count : int ) : unit =
    if Return orelse Case_push_count = 0 then
      ()
    else
      update_next( add,  register esp, 
        immediate( Word32.fromInt( 4 * Case_push_count ) ) )

  fun function_call( F : symbol, Arity : int ) : unit = (
    case H.find Normal_fun_name_table F of SOME N =>
      if N = Arity then () else raise Function_call_exn;
    update_next( call, label F, none );
    update_next( add, register esp, immediate( Word32.fromInt( 4 * Arity ) ) ) 
    )

  fun loop_args( f : 'c -> unit, Args : 'c list ) : unit =
    case Args of
      [] => ()
    | Arg :: Args => ( loop_args( f, Args ); f Arg )

  fun pass_constr_args( Args : ('1a,'1b)e list, Push_count : int, 
        Var_entry_table, Inline )
      : ( ('1a,'1b)e * int option ) list * ( unit -> unit ) list * int =
    let
      val Tagged_args =
        let
          val Counter = ref 0
        in
          map( fn Arg =>
            if is_simple_arg Arg then
              ( Arg, NONE )
            else
              let
                val X = ( Arg, SOME( !Counter ) )
              in
                inc Counter;
                X
              end,
            Args )
        end
      val M = ref 0
      val Finish_functions = flat_map( fn( Arg, Tag ) =>
        case Tag of
          NONE => []
        | SOME N =>
            let
              val F = compile_exp'( Arg, false, Push_count + !M, 0, false, 
                Var_entry_table, Inline )
              val A = !Current_addr
              val Finish = fn() => F A
            in
              if N > 0 then (
                update_next( push, register ebx, none );
                inc M
                )
              else
                ();
              [Finish]
            end,
          rev Tagged_args )
    in
      ( Tagged_args, Finish_functions, !M ) 
    end (* fun pass_constr_args *)

  and compile_exp'( E : ('1a,'1b)e, Return : bool, Push_count : int,
        Case_push_count : int, TR_context : bool, 
        Var_entry_table : int H.hash_table, Inline : bool ) : int -> unit = 
  let
(*
    val () = (
      p"\nCompile_exp: E =\n";
      Print.print_exp' E;
      nl() )
*)
    fun compile_exp( E, Return, Push_count, Case_push_count, TR_context ) =
      compile_exp'( E, Return, Push_count, Case_push_count, TR_context,
        Var_entry_table, Inline )
    exception Compile_exn_inline
  in
    case E of
      app_exp{ func, args, ... }  => (
      case H.find Normal_fun_name_table func of
        SOME _ => (
        case ( Inline, inlining func ) of
          ( true, SOME D_to_inline ) =>
            if func <> #func D_to_inline then raise Compile_exn_inline else
            if exists( not o is_variable_exp, args ) then
              compile_exp( build_case_defs E, Return, Push_count,
                Case_push_count, TR_context )
            else
            let
              exception New_var_entry_table_exn
              val New_var_entry_table : int H.hash_table =
                H.mkTable( 10, New_var_entry_table_exn )
              
              val Pars_vars = combine(
                vars_in_pure_tuple_pat( #pat D_to_inline ),
                map( fn app_exp{ func, ... } => func, args ) )
            in
              loop( fn( Par, Var ) =>
                H.insert New_var_entry_table 
                  ( Par, H.lookup Var_entry_table Var ),
                Pars_vars );
              compile_exp'( #exp D_to_inline, Return, Push_count, 
                Case_push_count, TR_context, New_var_entry_table, false )
            end

        | ( _ : bool, _ : ('1a,'1b)d option ) =>

        let val Finish_functions =
          map( fn( Arg, I ) =>
            case Arg of
              app_exp{ func, args=nil, ... } =>
                if is_unboxed_constant func then (
                  update_next( push, 
                    immediate( Word32.fromInt(unboxed_constant_to_int func) ),
                    none );
                  fn _ => ()
                  )
                else if is_variable func then (
                  update_next( push,
                    indexed( esp, Word32.fromInt(
                      4*(Push_count+I) + H.lookup Var_entry_table func )),
                    none );
                  fn _ => ()
                  )
                else
                  let
                    val F = compile_exp( Arg, false, Push_count+I, 0, false )
                    val A = !Current_addr
                    val Finish = fn _ => F A
                  in
                    update_next( push, register ebx, none );
                    Finish
                  end
            | _ =>
                  let
                    val F = compile_exp( Arg, false, Push_count+I, 0, false )
                    val A = !Current_addr
                    val Finish = fn _ => F A
                  in
                    update_next( push, register ebx, none );
                    Finish
                  end,
            combine( rev args, fromto( 0,  length args - 1 ) ) )
        
          val N = length args
          val Push_count' = Push_count + N
        in    
          if null args then raise Compile_exp else ();
          if TR_context andalso func = #func D then (
            (* Tail recursive call. *)
            for( 0, N-1, fn I => (
              update_next( mov, register eax, 
                indexed( esp, Word32.fromInt( 4*I ) ) );
              update_next( mov, 
                indexed( esp, Word32.fromInt( 4*Push_count'+4*I+4 ) ),
                register eax ) ) );
            update_next( add, register esp, 
              immediate( Word32.fromInt( 4*Push_count' ) ) );
            update_next( jmp, label func, none );
            update_next( align, immediate(Word32.fromInt 16), none );
            loop( fn G => G(), Finish_functions );
            fn _ => () )
          else (
          function_call( func, length args );
          case_return( Return, Case_push_count );
          return( Return, Push_count, Finish_functions )
          )
        end
        ) 
      | NONE =>
      if is_q func then (
        update_next( mov,  direct Q_sym_code_addr,
          immediate( Word32.fromInt(next_q_sym func) ) );
        update_next( jmp, label Q_sym_handler_sym, none );
        fn _ => ()
        )
      else
        (* func is a variable, constructor or built_in function. *)
      if is_unboxed_constant func then (
        update_next( mov, register ebx,
          immediate( Word32.fromInt( unboxed_constant_to_int func ) ) );
        case_return( Return, Case_push_count );
        return( Return, Push_count, [ fn _ => () ] )
        )
      else if is_variable func then (
          update_next( mov, register ebx,
            indexed( esp, Word32.fromInt(
              4 * Push_count + H.lookup Var_entry_table func ) ));
        case_return( Return, Case_push_count );
        return( Return, Push_count, [ fn _ => () ] )
        )
      else if is_real func then (
        C_interface.write_double( Word32.toInt( !Current_top_of_heap ),
          real_sym_to_real func );
        update_next( mov, register ebx, immediate( !Current_top_of_heap ) );
        Current_top_of_heap := Word32.+( !Current_top_of_heap, 0w8 );
        case_return( Return, Case_push_count );
        return( Return, Push_count, [ fn _ => () ] ) )
      else
      case H.find Constructor_table func of
        SOME Code =>
        let
          val ( Tagged_args, Finish_functions, M ) =
            pass_constr_args( args, Push_count, Var_entry_table, Inline )
          val _ = (
            update_next( cmp, register edi, 
              immediate( Word32.+(
                Word32.fromInt(4*Heap_size-4000),
                Heap_addr ) ) );
            update_next( jg, label Heap_overflow_handler_sym, none )
            )
        in
          loop_args( fn( I, ( Arg, Tag ) ) =>
            case Tag of
              SOME N =>
                if N = 0 then
                  update_next( mov, indexed( edi, Word32.fromInt(4*I) ),
                    register ebx )
                else (
                  update_next( mov, register eax,
                    indexed( esp, Word32.fromInt( 4*N - 4 ) ) );
                  update_next( mov, indexed( edi, Word32.fromInt(4*I) ),
                    register eax )
                  )
            | NONE =>
            case Arg of app_exp{ func, args=[], ... } =>
            if is_unboxed_constant func then
              update_next( mov, indexed( edi, Word32.fromInt(4*I) ),
                immediate( Word32.fromInt( unboxed_constant_to_int func ) ) )
            else if is_variable func then (
              update_next( mov, register eax,
                indexed( esp, Word32.fromInt(
                  4*(Push_count+M) + H.lookup Var_entry_table func ) ) );
              update_next( mov, indexed( edi, Word32.fromInt(4*I) ), 
                register eax )
              )
            else
              raise Compile_exp,
            combine( fromto(1,length args), Tagged_args )
            );
          update_next( mov, indirect edi, immediate(Word32.fromInt Code) );
          update_next( mov, register ebx, register edi );
          update_next( add, register edi, 
            immediate(  Word32.fromInt(4*(length args + 1)) ) );
          update_next( add, register edx, 
            immediate( Word32.fromInt( length args + 2 ) ) );
          if M = 0 then (
            case_return( Return, Case_push_count );
            return( Return, Push_count, Finish_functions )
            )
          else if Return then
            return( Return, Push_count + M, Finish_functions )
          else (
            update_next( add, register esp, 
              immediate( Word32.fromInt(4*M) ) );
            case_return( Return, Case_push_count );
            return( Return, Push_count, Finish_functions )
            )
        end (* func is constructor *)

      | NONE => (* func is a built-in function *)
      (* Note that all built-in functions have arity <=2.
         func is DUMMY_FUNC, SEMICOLON, EQ, LESS', PLUS, MUL, MINUS or 
         UMINUS.  DIV is not implemented.
      *)
(*
      if func = DUMMY_FUNC then (
        case_return( Return, Case_push_count );
        return( Return, Push_count, [ fn _ => () ] )
        )
      else 
*) 
      if func = TCOUNT then (
        update_next( mov, register ebx, register edx );
        case_return( Return, Case_push_count );
        return( Return, Push_count, [ fn _ => () ] )
        )
      else if func = SEMICOLON then
        case args of [ Arg1, Arg2 ] =>
        let
          val F1 = compile_exp( Arg1, false, Push_count, 0, false )
          val A1 = !Current_addr
          val Finish1 = fn _ => F1 A1
          val F2 = compile_exp( Arg2, false, Push_count, 0, TR_context )
          val A2 = !Current_addr
          val Finish2 = fn _ => F2 A2
        in
          case_return( Return, Case_push_count );
          return( Return, Push_count, [ Finish1, Finish2 ] )
        end
      else if func = UMINUS orelse func = SIGMOID then
        case args of [ Arg ] =>
        let
          val F = compile_exp( Arg, false, Push_count, 0, false )
          val A = !Current_addr
          val Finish = fn _ => F A
        in
          if func = SIGMOID then (
            update_next(mov, register esi, register edx );
            update_next( cmp, register edi, 
              immediate( Word32.+(
                Word32.fromInt(4*Heap_size-4000),
                Heap_addr ) ) );
            update_next( jg, label Heap_overflow_handler_sym, none );
            update_next( push, register ebx, none );
            update_next( push, register edi, none );
            update_next( call, immediate C_interface.Sigmoid_addr, none );
            update_next( mov, register ebx, register edi );
            update_next( add, register edi, immediate 0w8 );
            update_next( add, register esp, immediate 0w8 );
            update_next(mov, register edx, register esi )
            )
          else
            update_next( neg, register ebx, none );
          case_return( Return, Case_push_count );
          return( Return, Push_count, [ Finish ] )
        end
      else
        case args of [ Arg1, Arg2 ] =>
        let
          val Arg2_offset = ~4*Push_count - 4
          val F1 = compile_exp( Arg2, false, Push_count, 0, false )
          val A1 = !Current_addr
          val Finish1 = fn _ => F1 A1
          val _ = update_next( push, register ebx, none )
          val F2 = compile_exp( Arg1, false, Push_count+1, 0, false )
          val A2 = !Current_addr
          val Finish2 = fn _ => F2 A2
          exception Compile_exn_real_operator
        in
          if func = PLUSR orelse func = MULR orelse func = MINUSR orelse
             func = DIVR then (
          (* Save edx since it is modified by the C code. *)
            update_next(mov, register esi, register edx );
            update_next( cmp, register edi, 
              immediate( Word32.+(
                Word32.fromInt(4*Heap_size-4000),
                Heap_addr ) ) );
            update_next( jg, label Heap_overflow_handler_sym, none );
            update_next( push, register ebx, none );
            update_next( push, register edi, none );
            update_next( call, 
              if func = PLUSR then
                immediate C_interface.Add_addr
              else if func = MINUSR then
                immediate C_interface.Sub_addr
              else if func = MULR then
                immediate C_interface.Mul_addr
              else if func = DIVR then
                immediate C_interface.Div_addr
              else
                raise Compile_exn_real_operator,
               none );
            update_next( mov, register ebx, register edi );
            update_next( add, register edi, immediate 0w8 );
            update_next( add, register esp, immediate 0w8 );
            update_next(mov, register edx, register esi )
            )
          else if func = EQR orelse func = LESSR then (
          (* Save edx since it is modified by the C code. *)
            update_next(mov, register esi, register edx );
            update_next( push, register ebx, none );
            update_next( call, 
              if func = EQR then
                immediate C_interface.Equal_addr
              else if func = LESSR then
                immediate C_interface.Less_addr
              else
                raise Compile_exn_real_operator,
               none );
            update_next( mov, register ebx, register eax );
            update_next( add, register esp, immediate 0w4 );
            update_next(mov, register edx, register esi )
            )
          else if func = EQ orelse func = LESS' then (
            update_next( cmp, register ebx, 
              indexed( esp, Word32.fromInt( 4*(Push_count+1) + Arg2_offset )));
            update_next( mov, register ebx, immediate 0w0 );
            update_next( if func = EQ then sete else setl,
              register ebx, none )
            )
          else
            update_next(
              if func = PLUS then
                add
              else if func = MINUS then 
                sub
              else if func = MUL then
                mul
              else (
                output( !std_err, "Unknown function: " ^ symbol_to_string func );
                flush_out( !std_err );
                raise Compile_exp),
              register ebx, 
              indexed( esp, Word32.fromInt( 4*(Push_count+1) + Arg2_offset )));
          if Return then
            return( Return, Push_count+1, [ Finish1, Finish2 ] )
          else (
            case_return( Return, Case_push_count+1 );
            return( Return, Push_count, [ Finish1, Finish2 ] )
            )
        end
      ) (* app_exp{ func, args, ... } *)
              
    | case_exp{ exp, rules, ... } =>     
    if case rules of [ { pat = app_exp{ func, ... }, ... } ] => 
         is_variable func 
       | _ => false 
    then
    let
      val F = compile_exp( exp, false, Push_count, 0, false )
      val A = !Current_addr
      val Finish1 = fn() => F A
      val ( Act_index, V, E ) =
        case rules of [{ pat = app_exp{ func, ... }, 
                        exp, act_index, ... }] =>
            ( !act_index, func, exp )
    in
      update_next( inc', 
        direct( Word32.+( Act_array_addr, Word32.fromInt(4*Act_index) ) ),
        none );
      update_next( inc', register edx,  none );
      H.insert Var_entry_table ( V, ~4 * Push_count - 4 );
      update_next( push, register ebx, none );
      case compile_exp( E, Return, Push_count+1, Case_push_count+1, TR_context )
      of
        Finish2 => ( fn Continue_addr => 
          ( Finish1(); Finish2 Continue_addr ) )
    end
    else
    let
      fun less( 
        { act_count = A1, ... } : ('c,'d)rule_type, 
        { act_count = A2, ... } : ('c,'d)rule_type ) =
        !A1 < !A2
      val rules = rev rules
      val Sorted_rules =
        if is_sorted( less, rules ) then
          rules
        else
          sort less rules
      val X::Xs = map( 
        fn{ pat = app_exp{ func, args, ... }, exp, act_index, ... } =>
          case indexize( args, 1 ) of args =>
          case filter( not o is_anon_exp o #1, args ) of args =>
          ( H.lookup Constructor_table func, !act_index, 
            func, length args, args, exp ),
          Sorted_rules )
      val F = compile_exp( exp, false, Push_count, 0, false )
      val A = !Current_addr
      val Finish1 = fn() => F A
      val Patch_addresses = 
        map( fn( Code, _, Func, _, _, _ ) => (
          update_next( cmp, 
            if is_unboxed_constant Func then
               register ebx
            else
              indirect ebx, 
            immediate(Word32.fromInt Code) );
        let val Addr = !Current_addr
        in
          inc Current_addr;
          Addr
        end
        ),
        rev Xs )
      fun compile_case_alt( Code, Act_index, _, Arity, Args, E ) = (
        update_next( inc', 
          direct( Word32.+(
            Act_array_addr, 
            Word32.fromInt(4*Act_index) ) ),
          none );
        update_next( inc', register edx, none );
        loop_args( fn( N, ( app_exp{ func, args=[], ... }, I ) ) => 
          if is_anon_sym func then raise Compile_case_alt_exn else (
          H.insert Var_entry_table
            ( func, ~4*Push_count - 4*(Arity+1) + 4*N );
          update_next( push, indexed( ebx, Word32.fromInt(4*I) ), none )
          ),
          combine( fromto(1,Arity), Args ) );
        compile_exp( E, Return, Push_count + Arity,
          Case_push_count + Arity, TR_context )
        )
      val Finish2 = compile_case_alt X
    in
      fn Continue_addr => (
        Finish1();
        Finish2 Continue_addr;
        loop_args( fn( Patch_addr, X ) => 
          let
            val _ =
              Array.update( Assembly_code, Patch_addr,
                ( jz, immediate( Word32.fromInt(!Current_addr) ), none ) );
            val F = compile_case_alt X
            val _ =
              if Return then
                ()
              else (
                update_next( jmp, immediate(Word32.fromInt Continue_addr), 
                  none );
                update_next( align, immediate(Word32.fromInt 16), none )
                )
          in
            F Continue_addr
          end,
          combine( rev Patch_addresses, Xs ) ) )
    end (* case_exp{ exp, rules, ... } *)
  end (* and compile_exp' *)

  val Pars = vars_in_pure_tuple_pat( #pat D )
  val Arity = length Pars
  val Var_entry_table : int H.hash_table =
    (* Maps a variable to its offset within a stack frame. *)
    H.mkTable( 10, Compile_super )
  val _ = loop( fn( I, Par ) =>
    H.insert Var_entry_table ( Par, 4*I ),
    combine( fromto(1,Arity), Pars ) )
  in
   (compile_exp'( #exp D, true, 0, 0, Constants.Tail_recursion_opt, 
      Var_entry_table, true )) Max_int;
   ( !Current_addr, !Current_top_of_heap )
  end (* fun compile_super *)

local

exception Produce_fun_frequency_fun_exn
fun produce_fun_frequency_fun( Ds : ( 'a, 'b )d list ) : symbol -> int =
let
  val T : int ref H.hash_table = H.mkTable( 10, Produce_fun_frequency_fun_exn )
  fun ins Sym = 
    if is_function Sym then
      case H.find T Sym of
        NONE => H.insert T ( Sym, ref 1 )
      | SOME N_ref => inc N_ref
    else
      ()
          
  fun l( app_exp{ func, args, ... } ) = ( ins func; loop( l, args ) )
    | l( case_exp{ exp, rules, ... } ) = 
        ( l exp; loop( fn{ exp, ... } => l exp, rules ) )
in
  loop( l, map( #exp, Ds ) );
  fn Sym =>
    case H.find T Sym of
      NONE => 0
    | SOME N_ref => !N_ref
end

fun decs_to_inline'( 
      Xs : { d : ( '1a, '1b )d, size : int, freq : int } list,
      (* Sorted in order of increasing size *)
      Extra_size_so_far : int,
      Max_extra_size : int
      ) :  ( '1a, '1b )d list =
  case Xs of
    nil => nil
  | { d, size, freq } :: Xs =>
  case Extra_size_so_far + size * freq of Extra_size_so_far =>
  if Extra_size_so_far > Max_extra_size then
    nil
  else
    d :: decs_to_inline'( Xs, Extra_size_so_far, Max_extra_size )

exception Decs_to_inline_exn

in (* local *)

fun decs_to_inline( 
      Spec_supers : ( '1a, '1b )d list option,
      Ds : ('1a,'1b)d list
      ) : symbol -> ( '1a, '1b )d option =
let
  fun size( D : ( 'a, 'b )d ) :  int = exp_size( #exp D )
  val Ds_sizes = map( size, Ds )
  val Max_extra_size = int_sum Ds_sizes + 200
  val Xs =
    ( case Spec_supers of NONE => nil | SOME Ds =>
      case produce_fun_frequency_fun Ds of f =>
        map( fn D => { d = D, size = size D, freq = f( #func D ) }, Ds ) ) @ (
    case produce_fun_frequency_fun Ds of f =>
      map( fn( D, S ) => { d = D, size = S, freq = f( #func D ) },
        combine( Ds, Ds_sizes ) ) )

  val Xs = sort (fn( X1, X2 ) => #size X1 < #size X2) Xs
        
  val Decs_to_inline = decs_to_inline'( Xs, 0, Max_extra_size )
  val T : ( '1a, '1b )d H.hash_table = H.mkTable( 16, Decs_to_inline_exn )
in
  loop( fn D => H.insert T ( #func D, D ), Decs_to_inline );
  fn Sym => H.find T Sym
end (* decs_to_inline *)

end (* local *)

val Initialized = ref false

exception Compile_supers
fun compile_supers( 
      Spec_supers : ( '1a, '1b )d list option,
      Fun_entry_table : int H.hash_table,
      next_q_sym :  symbol -> int,
      Ds : ('1a,'1b)d list, 
      Start_index : int,
      Assembly_code : instruction Array.array,
      Inline : bool,
      Top_of_heap : Word32.word ) : int * Word32.word =
  (* Note that Fun_entry_table is modified by compile_supers. *)
  case Ds of nil => ( Start_index, Top_of_heap ) | _ =>
  let
    val _ = if !Initialized then () else raise Compile_supers
    val _ = loop( fn{ func, pat, ... } =>
      H.insert Normal_fun_name_table 
        ( func, length(vars_in_pure_tuple_pat pat) ),
      Ds )
    fun compile( D, Start_index, Top_of_heap ) =
      compile_super(
        if Inline then
          decs_to_inline( Spec_supers, Ds )
        else
          fn _ => NONE,
        Fun_entry_table,
        Constants.Heap_size,
        C_interface.Heap_addr,
        next_q_sym,
        C_interface.Q_sym_code_addr,
        C_interface.Act_array_addr,
        D,
        Start_index,
        Assembly_code,
        Top_of_heap )
    fun g( ( Start_index, Top_of_heap ), [D] ) = 
          compile( D, Start_index, Top_of_heap )
      | g( ( Start_index, Top_of_heap ), D::Ds ) = 
          g( compile( D, Start_index, Top_of_heap ), Ds )
    val ( Next_free_addr, Top_of_heap ) = g( ( Start_index, Top_of_heap ), Ds )
    val _ = 
      if is_NONE Spec_supers then 
      (* Spec_supers is NONE iff spec supers are being compiled actually. 
         The spec supers are then stored in Ds. *)
        ()
      else
        loop( fn{ func, ... } =>
          H.remove Normal_fun_name_table func,
          Ds )
  in
    ( Next_free_addr, Top_of_heap )
  end
handle Ex => (
  output(!std_err, "\ncompile_supers :\n" );
  flush_out( !std_err );
  re_raise( Ex, "compile_supers" )
  )

exception Compile_initialize
fun initialize( Spec_file : string, Abstract_types : string list ) : unit = (
  if !Initialized then raise Compile_initialize else ();
  Predefined.initialize( Spec_file, Abstract_types );
  H.insert Constructor_table ( TUPLE, 0 );
  loop( fn{ alts, ... } => 
    loop( fn( I, { constr, ... } ) =>
      H.insert Constructor_table ( constr, I ),
      combine( fromto( 0, length alts - 1 ), alts ) ),
    Predefined.datatype_decs() );
  loop( fn( Dt as { alts, ... } ) =>
    if is_unboxed Dt then (
      loop( fn{ constr, ... } => 
        H.insert Unboxed_constant_table ( constr, () ),
        alts );
      ()
      )
    else
      (),
    Predefined.datatype_decs() );
  loop( fn {  func, pat, ... } =>
    H.insert Normal_fun_name_table 
      ( func, length( vars_in_pure_tuple_pat pat ) ),
    Predefined.fun_decs() );
  Initialized := true
  )
      


      


end (* functor Compile_functor *)


