(* File: evaluate.sml.
   Created 1993-06-08.
   Modified 2000-05-16.

Modified 1999-12-01 to handle Spec.Validation_inputs.
Added program_eval_fun_validate.

Modified 2000-03-22 to include entropy in program_eval_type.

Function program_to_real_outputs added 2000-05-16. Intended do be used
together with Levenberg-Marquardt rconst optimization.
*)

signature EVALUATE =
sig

val initialize : string -> unit
val reinitialize : string -> unit

val set_max_time : int -> unit

structure Spec : SPEC 

type program_eval_type  = {
   output_eval : (Ast_lib.output_eval_type * Spec.Grade.grade) list,
   n_c_n_w_n_o : int*int*int,
   extra_quality : Spec.Grade.grade,
   n_c' : int, entropy : real, call_count : real, time_complexity : real,
   match_errors : Ast.symbol list,
(* match_errors is for example [ "Dont_know", "V157", "V157" ] 
   if ?(Dont_know) was returned for one input and ?(V157) was returned for 
   two inputs.
*)
   fingerprint : real,
   no_globals : unit Ast.Symbol_HashTable.hash_table
  }


type eval_value_type =
 {
  n_c : int, n_w : int, n_o : int, extra_quality : Spec.Grade.grade,
  n_c' : int, entropy : real,
  call_count : real, time_complexity : real,
  syntactic_fingerprint : real,
  syntactic_complexities : real list,
  fingerprint : real
  }


type quick_eval_value_type = {
  n_c : int, n_w : int, n_o : int, extra_quality : Spec.Grade.grade,
  n_c' : int, entropy : real
  }



val eval_value_type_pack : eval_value_type -> string
val eval_value_type_unpack : string -> eval_value_type
val quick_eval_value_type_pack : quick_eval_value_type -> string
val quick_eval_value_type_unpack : string -> quick_eval_value_type


val sc_of_exp : (real*real*real*real) * (real*real*real*real) *
  int * int * bool * (real*real*real*real) * ('a,'b)Ast.e *
  unit Ast.Symbol_HashTable.hash_table -> real
val syntactic_complexities 
    : ('a,'b)Ast.d * unit Ast.Symbol_HashTable.hash_table -> real list
val Comps_to_use : Ast.ty_env ref
val Semi_abstract_constructors : Ast_lib.Symbol_set.set ref
(* Can occur in patterns but not in applications. *)

val no_of_evaluations : unit -> real
val cum_eval_time : unit -> real
val syntactic_fingerprint_time : unit -> real
val syntactic_complexity_time : unit -> real
val execute_time : unit -> real
val total_execute_time : unit -> real
val finish_time : unit -> real
val act_array_time : unit -> real
val execute_aux_time : unit -> real
val vector_to_output_time : unit -> real
val compile_etc_time : unit -> real

val output_eval_type_cmp : 
      Ast_lib.output_eval_type * Ast_lib.output_eval_type -> order
val Dummy_quick_eval_value : quick_eval_value_type
val normal_to_quick 
    : eval_value_type -> quick_eval_value_type
val program_eval_type_to_quick 
    : program_eval_type -> quick_eval_value_type
val program_eval_to_eval_value 
    : Ast.dec * program_eval_type -> eval_value_type
val quick_to_normal' : quick_eval_value_type -> eval_value_type
val quick_to_normal : quick_eval_value_type * real list * real * 
      real * real * real -> eval_value_type
val pe1_cmp : (Spec.Grade.grade * Spec.Grade.grade -> order) * 
      eval_value_type * eval_value_type -> order
val pe2_cmp : (Spec.Grade.grade * Spec.Grade.grade -> order) * 
      eval_value_type * eval_value_type -> order
val pe3_cmp : (Spec.Grade.grade * Spec.Grade.grade -> order) * 
      eval_value_type * eval_value_type -> order
val pe4_cmp 
    : eval_value_type * eval_value_type -> order
val pe5_cmp 
    : eval_value_type * eval_value_type -> order

val pe1_listing : eval_value_type -> real list * Spec.Grade.grade * real list
val pe2_listing : eval_value_type -> real list * Spec.Grade.grade * real list
val pe3_listing : eval_value_type -> real list * Spec.Grade.grade * real list

val main_grade_cmp : Spec.Grade.grade * Spec.Grade.grade -> order
val main_syntactic_complexity : eval_value_type -> real

val quick_pe5_cmp 
    : quick_eval_value_type * quick_eval_value_type 
       -> order
val better_or_equal : eval_value_type * eval_value_type -> bool
val better : eval_value_type * eval_value_type -> bool

val quick_eval_value_out : 
  Lib.outstream * quick_eval_value_type -> unit
val print_quick_eval_value : quick_eval_value_type -> unit

val output_eval_to_string : 
  (Ast_lib.output_eval_type * Spec.Grade.grade) list -> string
val eval_value_out : Lib.outstream * eval_value_type -> unit
val print_eval_value : eval_value_type -> unit
val pre : ( '1a, '1b )Ast.d -> unit
val pre_with_time : ( '1a, '1b )Ast.d * int -> unit
val pre_validate : ( '1a, '1b )Ast.d -> unit
val mk_eval_value : ( '1a, '1b )Ast.d -> eval_value_type
val mk_eval_value_with_time : ( '1a, '1b )Ast.d * int -> eval_value_type
val mk_eval_value_max : ( '1a, '1b )Ast.d -> eval_value_type

(*
val program_to_real_outputs 
  : ('1a,'1b)Ast.d -> real Vector.vector Vector.vector
*)

val program_eval_fun_with_time : ('1a,'1b)Ast.d * int -> program_eval_type
val program_eval_fun_max : ('1a,'1b)Ast.d -> program_eval_type
val program_eval_fun_validate : ('1a,'1b)Ast.d -> program_eval_type

val  syntactic_fingerprint : ( 'a, 'b )Ast.d -> real

val truncate_syntactic_complexities : eval_value_type -> eval_value_type


val First_cutoffs_list : quick_eval_value_type list option list
val set_initial_idpef_arg : quick_eval_value_type list option list -> unit
val program_eval_fun : ('1a,'1b)Ast.d -> program_eval_type
val next_cutoffs_list : unit -> quick_eval_value_type list option list
val print_cutoffs_list : quick_eval_value_type list option list -> unit
val print_PEF_statistics : unit -> unit

end (* signature EVALUATE *)

functor Evaluate_functor( structure Spec : SPEC ) : EVALUATE =
struct
open Lib Ast Ast_lib Spec

structure Spec = Spec


type program_eval_type =
  {output_eval : (output_eval_type * Grade.grade) list,
   n_c_n_w_n_o : int*int*int,
   extra_quality : Grade.grade,
   n_c' : int, entropy : real, call_count : real, 
   time_complexity : real,
   match_errors : Ast.symbol list,
(* match_errors is for example [ "Dont_know", "V157", "V157" ] 
   if ?(Dont_know) was returned for one input and ?(V157) was returned for 
   two inputs.
*)
   fingerprint : real,
   no_globals : unit Ast.Symbol_HashTable.hash_table
  }

fun no_globals( { no_globals, ... } : program_eval_type ) = no_globals

type eval_value_type = {
  n_c : int, n_w : int, n_o : int, extra_quality : Grade.grade,
  n_c' : int, entropy : real,
  call_count : real, time_complexity : real,
  syntactic_fingerprint : real,
  syntactic_complexities : real list,
  fingerprint : real
  }

fun eval_value_type_pack( { n_c, n_w, n_o, extra_quality, n_c', entropy,
      call_count, time_complexity, 
      syntactic_fingerprint, syntactic_complexities,
      fingerprint } : eval_value_type ) : string =
  pack [
    Int.toString n_c,
    Int.toString n_w,
    Int.toString n_o,
    Grade.pack extra_quality,
    Int.toString n_c',
    real_pack entropy, 
    real_pack call_count,
    real_pack time_complexity,
    real_pack syntactic_fingerprint,
    pack( map( real_pack, syntactic_complexities ) ),
    real_pack fingerprint
    ]


fun eval_value_type_unpack( S : string ) : eval_value_type =
  case unpack S of
    [ N_c, N_w, N_o, Extra_quality, N_c', Entropy, Call_count, Time_complexity,
      Syntactic_fingerprint, Syntactic_complexities, Fingerprint ] =>
  {
    n_c = int_from_string N_c,
    n_w = int_from_string N_w,
    n_o = int_from_string N_o,
    extra_quality = Grade.unpack Extra_quality,
    n_c' = int_from_string N_c',
    entropy = real_unpack Entropy,
    call_count = real_unpack Call_count,
    time_complexity = real_unpack Time_complexity,
    syntactic_fingerprint = real_unpack Syntactic_fingerprint,
    syntactic_complexities = 
      map( real_unpack, unpack Syntactic_complexities ),
    fingerprint = real_unpack Fingerprint
  }
  


type quick_eval_value_type = {
  n_c : int, n_w : int, n_o : int, extra_quality : Grade.grade,
  n_c' : int, entropy : real
  }



fun quick_eval_value_type_pack( { n_c, n_w, n_o, extra_quality, n_c', entropy }
       : quick_eval_value_type ) : string =
  pack [
    Int.toString n_c,
    Int.toString n_w,
    Int.toString n_o,
    Grade.pack extra_quality,
    Int.toString n_c',
    real_pack entropy
    ]


fun quick_eval_value_type_unpack( S : string ) : quick_eval_value_type =
  case unpack S of
    [ N_c, N_w, N_o, Extra_quality, N_c', Entropy ] =>
  {
    n_c = int_from_string N_c,
    n_w =  int_from_string N_w,
    n_o = int_from_string N_o,
    extra_quality = Grade.unpack Extra_quality,
    n_c' = int_from_string N_c',
    entropy = real_unpack Entropy
  }
  

(* Canonizing hashing for dec: *)

local

local

val Hash_val : real ref = ref 0.0

val N_rands = 10000

local 
  val Rand = Random.rand( 819462154, ~92361654 )
in 

val Rand_vector : real vector =
  Vector.tabulate( N_rands, fn I => Random.randReal Rand - 0.5 )

end

val Rand_vector_index = ref ~1

fun next_random() = (
  Rand_vector_index := !Rand_vector_index + 1;
  Vector.sub( Rand_vector, !Rand_vector_index )
  )
  handle Subscript => (
    Rand_vector_index := ~1;
    next_random()
    )

in

fun hash_val_clear() = (
  Rand_vector_index := ~1;
  Hash_val := 0.0
  )
  
fun hash( X : real ) : unit =
  Hash_val := normrealhash( X * next_random() ) + normrealhash( !Hash_val )

fun hash_val_get() = !Hash_val

end (* local *)

structure H = Symbol_HashTable

exception Predef_table_exn
val Predef_table : real H.hash_table = H.mkTable( 10, Predef_table_exn )

val Current_sym_no = ref 16
val Init_sym_no = ref 0

fun next_sym_no() : real = (
  Current_sym_no := !Current_sym_no + 1;
  real( !Current_sym_no )
  )

val Syntactic_fingerprint_timer = mk_timer "Syntactic_fingerprint_timer"


in

fun syntactic_fingerprint_time() = check_timer Syntactic_fingerprint_timer

fun syntactic_fingerprint_init() = (
  loop( fn( Sym, _ ) => H.insert Predef_table ( Sym, next_sym_no() ),
    Predefined.ty_env() );
  Init_sym_no := !Current_sym_no
  )

fun syntactic_fingerprint( { func, pat, exp, ... } : ( 'a, 'b )d ) : real =
  let
    val () = start_timer Syntactic_fingerprint_timer
    val T = H.copy Predef_table
    fun ins Sym =
      case H.find T Sym of
        NONE =>
          let
            val X = next_sym_no()
          in
            H.insert T ( Sym, X );
            hash X
          end
      | SOME X => hash X
    
    fun s( app_exp{ func, args, ... } ) =
          if is_not_activated_sym func then
            hash 8.643534654
          else if is_q func then
            hash 3.45465393453
          else if is_int func then 
            ( hash 9.7352942; hash( real( int_sym_to_int func ) ) )
          else if is_real func then
            ( hash 2.73619825; hash( real_sym_to_real func ) )
          else
            ( hash 7.56435465; ins func; loop( s, args ) )
      | s( case_exp{ exp, rules, ... } ) =
          ( hash 8.746635463; s exp; 
            loop( fn{ pat, exp, ... } => (s pat; s exp), rules ) )
      | s( let_exp{ dec_list, exp, ... } ) =
          ( hash 9.35654653; 
            loop( fn{ func, pat, exp, ... } => 
              ( ins func; s pat; s exp), 
            dec_list );
            s exp )
      | s( as_exp{ var, pat, ... } ) = ( ins var; s pat )
    val _ = (
      Current_sym_no := !Init_sym_no;
      hash_val_clear();
      ins func;
      s pat;
      s exp 
      )
    val X = hash_val_get()
  in
    stop_timer Syntactic_fingerprint_timer;
    X
  end

end (* local *)
  


structure Execute = Execute_functor( structure Spec = Spec )
val compile_etc_time = Execute.compile_etc_time
val execute_time = Execute.execute_time
val act_array_time = Execute.act_array_time
val execute_aux_time = Execute.execute_aux_time
val vector_to_output_time = Execute.vector_to_output_time
val total_execute_time = Execute.total_execute_time
val finish_time = Execute.finish_time

val set_max_time = Execute.set_max_time

local

fun isInt( S : string ) = 
  case Int.fromString S of NONE => false | SOME N =>
    String.size( Int.toString N ) = String.size S
   
fun isReal( S : string ) = 
  case Real.fromString S of NONE => false | SOME N =>
    String.size( Real.toString N ) = String.size S

in (* local *)

val Funs_to_use = map( fn Sym => 
      if isInt Sym orelse isReal Sym then
       case Parse.parse_exp Sym of app_exp{ func, ... } => func
      else
        string_to_symbol( func_sym, Sym ),
  Spec.Funs_to_use )

end (* local *)

val Comps_to_use : ty_env ref = ref []
val Semi_abstract_constructors : Symbol_set.set ref = ref( Symbol_set.empty() )
val Arity_zero_funs : symbol list ref = ref []
val Initial_N_leaves = ref Max_int
(* 
Simplified syntactic_complexity estimate
---------------------------

The syntactic_complexity of a program, such as insertion sort, needs to be estimated in less
than 1 ms. It therefore takes too much time to do an "exact" syntactic_complexity 
calculation, which takes type constraints into consideration.
Type constraints are thus not considered below to make estimate computation
fast and simple.
Note that only the relative values of syntactic_complexity estimates matter i.e. if
h_1 and h_2 are exact values such that h_1 < h_2 then 
estimate(h_1) < estimate(h_2).

First consider the syntactic_complexity of an expression A that only contains function
applications. A very simple syntactic_complexity estimate is the size of A, i.e. the
number of nodes in A's expression tree representation.
Consider two expressions A_1 and A_2 such that each node in A_1, as a result
of scoping, can have 2 different values whereas each node in A_2 can have
4 different values. Let s_i be the size of A_i.
Better "relative" syntactic_complexity estimates than s_1 and s_2 are then
2^s_1 and 4^s_2 or alternatively s_1 * log 2 and s_2 * log 4.

The estimate actually used is in principle as follows:
The increase in syntactic_complexity due to a node N is
fn N =>
  if N is a leaf then
    log( No of leaf symbols whose scope include N )
  else
    log( No of function symbols whose scope include N ).
The syntactic complexity estimate is thus in principle the sum of this 
function applied to all nodes.

The execution time of the call syntactic_complexity( Def for insertion sort ) is
0.76 ms.

*)


fun sc_of_exp( Argument_lengths : (real*real*real*real), 
  Analyzed_lengths : (real*real*real*real), N_internals, N_leaves, 
  Analyzed : bool, 
  Lengths as (Let,Case,Internal,Leaf) : (real*real*real*real), 
  E : ('a,'b)e,
  No_globals ) : real =
  let
    fun contains_no_globals F =
      case Symbol_HashTable.find No_globals F of
        NONE => false
      | SOME() => true
    val sc_of_exp = fn( N_internals, N_leaves, Analyzed, Lengths, E ) =>
      sc_of_exp( Argument_lengths, Analyzed_lengths, N_internals,
        N_leaves, Analyzed, Lengths, E, No_globals )
  in 
  case E of
    app_exp{func,args,...} => 
      if func = RCONST then
        case args of [ Complexity, _, _ ] =>
          2.0*(Leaf + ln(real N_leaves)) 
(* Assume that the number of rconsts is the square of the number of 
   variables as it is in a standard MLP. *)
      else if is_q func then
        if is_not_activated_exp E then
          0.0
        else
         Leaf + ln(real N_leaves)   
      else if null(args) then
        Leaf + ln(real N_leaves)
      else
        Internal + ln(real N_internals)  +
        real_sum(
          map( fn A => sc_of_exp(N_internals,N_leaves, Analyzed,
              if Analyzed then Lengths else Argument_lengths ,A), 
            args )) + 0.0
(* Commented out 1999-07-30.
        (if null(tl args) orelse func=TUPLE then
           0.0
         else
           Internal + ln 2.0
           (* Accounts for the "implicit" tuple constructor. *)
         )
*) 
  | case_exp{ exp, rules, ... } =>
      Case +
      sc_of_exp( N_internals, N_leaves, 
        case rules of _::nil => Analyzed | _ => true,
        case  rules of _::nil => Lengths | _ => Analyzed_lengths,
        exp) +
      real_sum(map( fn{ pat, exp, ... } => 
            sc_of_exp( N_internals, N_leaves+length(vars_in_pat pat), 
              Analyzed, Lengths, exp ),
            rules))
  | let_exp{ dec_list, exp, ...} =>
      Let+
      real_sum(map( fn D => 
        sc_of_dec( Argument_lengths, Analyzed_lengths,
           N_internals+length dec_list, 
           if contains_no_globals( #func D ) then
             !Initial_N_leaves
           else
             N_leaves, 
           Analyzed, Lengths, D, No_globals), 
          dec_list ))+
      sc_of_exp( N_internals+length dec_list, N_leaves, 
        Analyzed, Lengths, exp )
  end

and sc_of_dec( Argument_lengths, Analyzed_lengths, N_internals, N_leaves, 
  Analyzed, Lengths, {pat,exp,...} : ('a,'b)d,  No_globals ) =
  sc_of_exp( Argument_lengths, Analyzed_lengths, N_internals, 
    N_leaves+length(vars_in_pat pat), Analyzed, Lengths, exp, No_globals )


val Normal_lengths = ( ~(ln 0.025), ~(ln 0.15), ~(ln 0.325), ~(ln 0.5) )
val Argument_lengths = ( ~(ln 5.0E~3), ~(ln 3.0E~2), ~(ln 0.380151515151516),
  ~(ln 0.584848484848485) )
val Analyzed_lengths = ( ~(ln 2.5E~3), ~(ln 1.5E~2), ~(ln 0.387045454545455), 
  ~(ln 0.595454545454546) )

fun syntactic_complexity(Normal_lengths, Argument_lengths, Analyzed_lengths,
  D : ('a,'b)d, No_globals ) : real =
  case !Initial_N_leaves < Max_int of true =>
  sc_of_dec( Argument_lengths, Analyzed_lengths, 
    2 + length Spec.Funs_to_use - length(!Arity_zero_funs),
    !Initial_N_leaves, false, Normal_lengths, D, No_globals ) / ln 2.0

local

  val Syntactic_complexity_timer = mk_timer "Syntactic_complexity_timer"
in

fun syntactic_complexity_time() = check_timer Syntactic_complexity_timer

fun syntactic_complexities( D, No_globals ) =
  let
    val () = start_timer Syntactic_complexity_timer
    val X = [
      syntactic_complexity( Normal_lengths, Argument_lengths, Analyzed_lengths,
        D, No_globals ),
      syntactic_complexity( Normal_lengths, Normal_lengths, Normal_lengths,
        D, No_globals )
      ]
  in
    stop_timer Syntactic_complexity_timer;
    X
  end

end (* local *)

val No_of_evaluations = ref 0.0
val Eval_timer = mk_timer "Eval_timer"
fun no_of_evaluations() = !No_of_evaluations
fun cum_eval_time() = check_timer Eval_timer

fun program_eval_fun_validate( D : ('1a,'1b)d ) =
let 
  val () = set_max_time( dh Spec.Max_time_distribution )
  val _ = Spec.clear()
  val ( No_globals, _ ) = Execute.compile_f_dec D
  val Lower = length Spec.Inputs
  val Upper = Lower + length Spec.Validation_inputs - 1  
  val Results = map( fn Problem_no => 
    Execute.execute Problem_no,
    fromto( Lower, Upper ) )
  val Call_count = real_sum(map(real o #2,Results))
  val Allocation_count = real_sum( map( real o #3, Results ) )
  val Output_eval = map( fn( (Xs,I), (Res,_,_) ) =>
    case Res of
      Execute.ok_status Ys => Spec.output_eval_fun(I,Xs,Ys)
    | Execute.q_sym_status _ => ( dont_know, Spec.Grade.zero )
    | _ => ( overflow, Spec.Grade.zero ),
    combine( 
      combine( Spec.Validation_inputs, fromto( Lower, Upper ) ), 
      Results ) )

  val (N_c,N_w,N_o) =
    ( count(correct,map(#1,Output_eval)), 
      count(wrong,map(#1,Output_eval)),
      count(overflow,map(#1,Output_eval))
      )
in { 
    output_eval = Output_eval,
    extra_quality = Grade.post_process(
      foldright( Spec.Grade.zero, Spec.Grade.+, map(#2,Output_eval)) ),
    n_c_n_w_n_o = (N_c,N_w,N_o),
    n_c' = 0, entropy = 0.0,
    call_count = 0.0, (* Call count is now time complexity! *)
    time_complexity = Call_count,
    match_errors = flat_map( fn( Res, _, _ ) =>
      case Res of
        Execute.q_sym_status Sym => 
          if Sym = PREDEFINED_NOT_ACTIVATED_SYMBOL then [] else [ Sym ]
      | _ => [],
      Results ),
    fingerprint = Spec.get(),
    no_globals = No_globals
    }
end
handle Ex => (
  output(!std_err, "\nprogram_eval_fun_validate :\n" );
  Print.print_dec' D;
  flush_out( !std_err );
  re_raise( Ex, "program_eval_fun_validate" )
  )

  

fun error_locality_quality(Counts : (int*int) list) : int*int =
(* See page 1994-01-03.2. *)
  let
    val Max_wrong_true_count =  #1(max(fn((X1,Y1),(X2,Y2)) => X1<X2,Counts))
    val Max_counts = filter(fn(Wrong_true_count,Correct_true_count) =>
      Wrong_true_count = Max_wrong_true_count,
      Counts)
  in
    min(fn((X1,Y1),(X2,Y2)) => Y1<Y2, Max_counts)
  end


fun program_eval_fun'( D : ('1a,'1b)d ) =
let 

  val _ = (
    No_of_evaluations := !No_of_evaluations + 1.0;
    start_timer Eval_timer
    )
  (* val D = set_exp( D, rename( #exp D, false ) )
     Error: Gives wrong activation counting
   *)
  val _ = Spec.clear()

(*
  val _ =  
    if !Ast.Debug then (
      output(!std_out, "\nprogram_eval_fun' :\n" );
      Print.print_dec' D;
      flush_out( !std_out )
      )
    else
      ()
*)


  val ( No_globals, Act_count_so_far ) = Execute.compile_f_dec D
(*
  val _ = 
    if !Ast.Debug then (
      output(!std_out, "\nCompilation finished \n" );
      flush_out( !std_out )
      )
    else
      ()
*)
  val Max_problem_no = length Spec.Inputs - 1
  val Results = map( fn Problem_no => (
(*
    if !Ast.Debug then (
      output(!std_out, " " ^ Int.toString Problem_no );
      flush_out( !std_out )
      )
    else
      ();
*)
    Execute.execute Problem_no
    ),
    fromto( 0, Max_problem_no ) )
  val Call_count = real_sum(map(real o #2,Results))
  val Allocation_count = real_sum( map( real o #3, Results ) )
  val ( Problem_act_matrix, Act_count ) = Execute.finish D
  val Act_count : real = Act_count - Act_count_so_far
  val Max_rhs_no = Vector.length( Array.sub( Problem_act_matrix, 0 ) ) - 1
  val Output_eval = map( fn( (Xs,I), (Res,_,_) ) =>
    case Res of
      Execute.ok_status Ys => Spec.output_eval_fun(I,Xs,Ys)
    | Execute.q_sym_status _ => ( dont_know, Spec.Grade.zero )
    | _ => ( overflow, Spec.Grade.zero ),
    combine( 
      combine( Spec.Inputs, fromto( 0, Max_problem_no ) ) , 
      Results ) )

  val Output_eval' = map( #1, Output_eval )
  
  fun counts Rhs_no =
    let fun g(Problem_no,cwd_res,Wrong_true_count,Correct_true_count) =
      case cwd_res of
        nil =>  (Wrong_true_count,Correct_true_count)
      | Res::cwd_res =>
      case Vector.sub( Array.sub( Problem_act_matrix, Problem_no ),
                       Rhs_no ) of
        0 => g(Problem_no+1,cwd_res,Wrong_true_count,Correct_true_count)
      | _ => 
          g(Problem_no+1, cwd_res,
            case Res of 
              wrong =>  Wrong_true_count+1 
            | overflow =>  Wrong_true_count+1 
            | _ => Wrong_true_count,
            case Res of 
              correct => Correct_true_count+1 
            | _ => Correct_true_count )
    in
      if Rhs_no>Max_rhs_no then 
        nil
      else
        g( 0, Output_eval', 0, 0 ) :: counts(Rhs_no+1)
    end
  val (N_c,N_w,N_o) =
    ( count(correct,Output_eval'), 
      count(wrong,Output_eval'),
      count(overflow,Output_eval')
      )
  val  (Loc_n_w,Loc_n_c) =
        if N_w+N_o=0 then
          (0,0)
        else if Max_rhs_no = ~1 then 
          (N_w+N_o,N_c) 
        else 
          error_locality_quality(counts 0)
(*
  val _ = 
    if !Ast.Debug then (
      output(!std_out, "\nvals in program_eval_fun' computed\n" );
      flush_out( !std_out )
      )
    else
      ()
*)


  val Y =
  { output_eval = Output_eval,
    extra_quality = Grade.post_process(
      foldright( Spec.Grade.zero, Spec.Grade.+, map(#2,Output_eval)) ),
    n_c_n_w_n_o = (N_c,N_w,N_o),
    n_c' = if N_w+N_o-Loc_n_w = 0 then N_c-Loc_n_c else 0,
    entropy = 0.0 (* if N_c = 0 andalso N_w = 0 then 1.0 else
      Evaluate_lib4.entropy_measure(
        Output_eval', Problem_act_matrix, Max_rhs_no, Max_problem_no ) *),
    call_count = 0.0, (* Call count is now time complexity! *)
    time_complexity = Call_count,
    match_errors = flat_map( fn( Res, _, _ ) =>
      case Res of
        Execute.q_sym_status Sym => 
          if Sym = PREDEFINED_NOT_ACTIVATED_SYMBOL then [] else [ Sym ]
      | _ => [],
      Results ),
    fingerprint = Spec.get(),
    no_globals = No_globals
    }
in
  stop_timer Eval_timer;
  Y
end
handle Ex => (
  output(!std_err, "\nprogram_eval_fun' :\n" );
  Print.print_dec' D;
  flush_out( !std_err );
  re_raise( Ex, "program_eval_fun'" )
  )

  
val program_eval_fun' = fn( D : ('a,'b)d ) => (
(*
  Evaluate_lib.save_d D;
*)
  program_eval_fun' D
  )


val Epsilon = 1.0E~6

local
  fun to_int correct = 0
    | to_int dont_know = 1
    | to_int wrong = 2
    | to_int overflow = 3
in
  fun output_eval_type_cmp(X,Y) =
    let
      val X = to_int X
      val Y = to_int Y
    in
      if X < Y then
        LESS
      else if X > Y then
        GREATER
      else 
        EQUAL
    end
end

val Dummy_quick_eval_value =
  { n_c=0, n_w=0, n_o=0, extra_quality=Grade.zero, n_c'=0, entropy = 0.0 }

fun main_syntactic_complexity( 
      { syntactic_complexities = S :: _, ... } : eval_value_type ) = S

val main_grade_cmp = case Grade.comparisons of X::_ => X

fun normal_to_quick( { n_c, n_w, n_o, extra_quality, n_c', entropy,
      ... } : eval_value_type ) 
    : quick_eval_value_type =
  { n_c=n_c, n_w=n_w, n_o=n_o, extra_quality=extra_quality,
    n_c'=n_c', entropy = entropy }

fun program_eval_type_to_quick( { n_c_n_w_n_o=(N_c,N_w,N_o), 
      extra_quality, n_c', entropy,... } : program_eval_type ) 
    : quick_eval_value_type =
  { n_c=N_c, n_w=N_w, n_o=N_o, extra_quality=extra_quality,
    n_c'=n_c', entropy = entropy }

fun quick_to_normal'( { n_c, n_w, n_o, extra_quality, n_c', entropy} 
    : quick_eval_value_type ) : eval_value_type =
  {  n_c=n_c, n_w=n_w, n_o=n_o, extra_quality=extra_quality,
    n_c'=n_c', entropy = entropy,
    call_count=0.0, time_complexity = 0.0,
    syntactic_complexities= [0.0,0.0], fingerprint = 0.0,
    syntactic_fingerprint = 0.0 }

fun quick_to_normal( { n_c, n_w, n_o, extra_quality, n_c', entropy } 
      : quick_eval_value_type, Syntactic_complexities : real list, 
      Syntactic_fingerprint : real,
      Call_count : real, Time_complexity : real,
      Fingerprint : real ) : eval_value_type =
  { n_c=n_c, n_w=n_w, n_o=n_o, extra_quality=extra_quality,
    n_c'=n_c', entropy = entropy, syntactic_fingerprint = Syntactic_fingerprint,
    call_count=Call_count, time_complexity = Time_complexity,
    syntactic_complexities=Syntactic_complexities,
    fingerprint = Fingerprint }



fun program_eval_to_eval_value( 
      Program : dec,
      Program_eval_value as { call_count, time_complexity,
        fingerprint, ... } : 
        program_eval_type ) : eval_value_type =
  let
    val Quick : quick_eval_value_type =
      program_eval_type_to_quick Program_eval_value
    val No_globals = #2( Produce_super_combs.make_super_combs[ Program ] )
(* The no_globals in Program_eval_value shouldn't be trusted due to a
   combination of unwrapping and simplification in compound_trf-synt.sml. *)

    val S = syntactic_complexities( Program, No_globals )
    val SF = syntactic_fingerprint Program
  in
    quick_to_normal( Quick, S, SF, call_count, time_complexity, fingerprint)
  end

fun pe1_cmp( Less : Grade.grade*Grade.grade -> order,
      { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1', 
        (* entropy = En1, *) ...} 
      : eval_value_type,
      { n_c=N_c2, n_w=N_w2, n_o=N_o2,  extra_quality=E2, n_c'=N_c2', 
        (* entropy = En2, *) ...} 
      : eval_value_type 
      ) : order =
  if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else
    case Less( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
(*
  else if En1 < En2 then
    LESS
  else if En1 > En2 then
    GREATER
*)
  else if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
  else
    EQUAL

fun pe1_listing( 
      { n_c, n_w, n_o, extra_quality, n_c', (* entropy, *) ... } : eval_value_type ) =
  ( [ real n_c ], extra_quality, 
    [ real(n_o + n_w), real n_o, (* entropy, *) real n_c' ] )


fun pe2_cmp( Less : Grade.grade*Grade.grade -> order,
      { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1', 
        (* entropy = En1, *) ...} 
      : eval_value_type,
      { n_c=N_c2, n_w=N_w2, n_o=N_o2,  extra_quality=E2, n_c'=N_c2', 
        (* entropy = En2, *) ...} 
      : eval_value_type 
      ) : order =
  if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
(*
  else if En1 < En2 then
    LESS
  else if En1 > En2 then
    GREATER
*)
  else if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else
    case Less( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
  else
    EQUAL


fun pe2_listing( 
      { n_c, n_w, n_o, extra_quality, n_c', (* entropy, *) ... } : eval_value_type ) =
  ( [ real n_c', (* entropy, *) real n_c ], extra_quality, 
    [ real(n_o + n_w), real n_o ] )


fun pe3_cmp( Less : Grade.grade*Grade.grade -> order,
      { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1', 
        (* entropy = En1, *) ...} 
      : eval_value_type,
      { n_c=N_c2, n_w=N_w2, n_o=N_o2, extra_quality=E2, n_c'=N_c2', 
        (* entropy = En2, *) ...} 
      : eval_value_type 
      ) : order =
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
  else if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else 
    case Less( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
(*
  if En1 < En2 then
    LESS
  else if En1 > En2 then
    GREATER
  else *) if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
  else
    EQUAL

fun pe3_listing( 
      { n_c, n_w, n_o, extra_quality, n_c', (* entropy, *) ... } : eval_value_type ) =
  ( [ real(n_o + n_w), real n_o, real n_c ], extra_quality, 
    [ (* entropy, *) real n_c' ] )


fun pe4_cmp( { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1',
      time_complexity=T1, syntactic_complexities=S1::_,...} : eval_value_type,
              { n_c=N_c2, n_w=N_w2, n_o=N_o2, extra_quality=E2, n_c'=N_c2',
      time_complexity=T2, syntactic_complexities=S2::_,...} : eval_value_type 
      ) : order =
  if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else 
    case main_grade_cmp( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
  else if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
  else if T1 < T2 then
    LESS
  else if T1 > T2 then
    GREATER
  else if S1 < S2 - Epsilon then
    LESS
  else if S2 <  S1 - Epsilon then
    GREATER
  else
    EQUAL


fun pe5_cmp( { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1',
      time_complexity=T1, syntactic_complexities=S1::_,...} : eval_value_type,
              { n_c=N_c2, n_w=N_w2, n_o=N_o2, extra_quality=E2, n_c'=N_c2',
      time_complexity=T2, syntactic_complexities=S2::_,...} : eval_value_type 
      ) : order =
  if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else 
    case main_grade_cmp( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
  else if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
  else if S1 < S2 - Epsilon then
    LESS
  else if S2 <  S1 - Epsilon then
    GREATER
  else if T1 < T2 then
    LESS
  else if T1 > T2 then
    GREATER
  else
    EQUAL


fun quick_pe5_cmp( 
      { n_c=N_c1, n_w=N_w1, n_o=N_o1, extra_quality=E1, n_c'=N_c1', ...} 
      : quick_eval_value_type,
      { n_c=N_c2, n_w=N_w2, n_o=N_o2, extra_quality=E2, n_c'=N_c2', ...} 
      : quick_eval_value_type 
      ) : order =
  if N_c1 > N_c2 then
    LESS
  else if N_c1 < N_c2 then
    GREATER
  else 
    case main_grade_cmp( E1, E2 ) of
      LESS => LESS
    | GREATER => GREATER
    | EQUAL =>
  if N_o1+N_w1 < N_o2+N_w2 then
    LESS
  else if N_o1+N_w1 > N_o2+N_w2 then
    GREATER
  else if N_o1 < N_o2 then
    LESS
  else if N_o1 > N_o2 then
    GREATER
  else if N_c1' > N_c2' then
    LESS
  else if N_c1' < N_c2' then
    GREATER
  else
    EQUAL


local

val Pe_cmps = flat_map( fn Pei_cmp => map( fn Cmp =>
        fn(X,Y) => Pei_cmp(Cmp,X,Y), Grade.comparisons ),
      [pe1_cmp, pe2_cmp, pe3_cmp ] )
in

fun better_or_equal( X : eval_value_type, Y ) : bool =
  forall( fn pe_cmp =>
    case pe_cmp( X, Y ) of
      LESS => true
    | EQUAL => true
    | GREATER => false,
    Pe_cmps )


fun better( X : eval_value_type, Y ) : bool =
  better_or_equal( X, Y ) andalso
  exists( fn pe_cmp =>
    case pe_cmp( X, Y ) of
      LESS => true
    | EQUAL => false
    | GREATER => false,
    Pe_cmps )

end


fun output_eval_to_string( Xs : (output_eval_type * Grade.grade) list )
    : string =
  foldright( 
    "",
    fn((Oe,G),S) =>
      ( case Oe of 
          correct => "c" 
        | wrong => "w" 
        | dont_know => "d" 
        | overflow => "o" ) ^
      " " ^
      Grade.toString G ^
      " " ^ S, 
    Xs)

fun eval_value_out( out, 
      { n_c, n_w, n_o, extra_quality, n_c', (* entropy, *)
        call_count, time_complexity, syntactic_complexities, fingerprint, 
        syntactic_fingerprint,... } 
      : eval_value_type ) = (
  output(out, 
    Int.toString n_c ^ " " ^
    Int.toString n_o ^ "  " ^
    Int.toString n_w ^ " " ^
    Grade.toString extra_quality ^ " " ^
    (* Real.toString entropy ^ " " ^ *)
    Int.toString n_c' ^ " " ^
    Real.toString time_complexity ^ " "
    );
  real_list_out(out, syntactic_complexities);
  output( out, " " ^ Real.toString fingerprint ^ " " ^
    Real.toString syntactic_fingerprint ^ "\n") 
  )

fun print_eval_value E = eval_value_out(!std_out,E)
    





fun quick_eval_value_out(out, { n_c, n_w, n_o, extra_quality, n_c', ...
   (* entropy *) } 
    : quick_eval_value_type ) = 
  output(out, " :  "^
    Int.toString n_c ^ " " ^
    Int.toString n_o ^ " " ^
    Int.toString n_w ^ "  " ^
    Grade.toString extra_quality ^ "  " ^
    (* Real.toString entropy ^ "  " ^ *)
    Int.toString n_c'
  )
    
fun print_quick_eval_value X = quick_eval_value_out(!std_out,X)

structure IDPEF = IDPEF_fn(
struct

type program_eval_type = program_eval_type
type quick = quick_eval_value_type
val program_eval_fun' = program_eval_fun'
val program_eval_type_to_quick = program_eval_type_to_quick
val set_max_time = set_max_time

local

val Pe_cmps = map( fn Pei_cmp => map( fn Cmp =>
        fn(X,Y) => Pei_cmp(Cmp,X,Y), Grade.comparisons ),
      [pe3_cmp, pe2_cmp, pe1_cmp] )
(* Note that the order 3, 2, 1 is important. *)

val N = real( length Grade.comparisons )

val Weighted_pe_cmps = flat_map( fn( W, Cmps ) =>
  map( fn Cmp => ( W / N, Cmp ), Cmps ),
  combine( Spec.Pe_survival_weights, Pe_cmps ) )

in (* local *)

val Weighted_pe_cmps = map( fn( W, Pe_cmp ) => ( W,
  fn( X : quick_eval_value_type, Y : quick_eval_value_type ) =>
    Pe_cmp( quick_to_normal' X, quick_to_normal' Y ) ),
  Weighted_pe_cmps )

end (* local *)

val Max_time_distribution = Spec.Max_time_distribution

end )

fun pqo( Xs_opt : quick_eval_value_type list option ) : unit =
  case Xs_opt of
    NONE => p"NONE"
  | SOME Xs => print_list( print_quick_eval_value, Xs )

fun print_cutoffs_list( 
      Cutoffs_list : quick_eval_value_type list option list ) =
  print_list( pqo, Cutoffs_list )

open IDPEF


fun pre_with_time( D, Max_time ) =
let 
  val () = set_max_time Max_time
  val Program_eval_value as { call_count, time_complexity,
        fingerprint, no_globals, ... } = 
    program_eval_fun' D
  val Eval_value = program_eval_type_to_quick Program_eval_value
  val S = syntactic_complexities( D, no_globals )
  val SF = syntactic_fingerprint D
in
  print_eval_value(
    quick_to_normal( Eval_value, S, SF, call_count, time_complexity,
      fingerprint ) )
end

fun pre D = pre_with_time( D, dh Spec.Max_time_distribution )


fun pre_validate D =
let 
  val () = set_max_time( dh Spec.Max_time_distribution )
  val Program_eval_value as { call_count, time_complexity,
        fingerprint, no_globals, ... } = 
    program_eval_fun_validate D
  val Eval_value = program_eval_type_to_quick Program_eval_value
  val S = syntactic_complexities( D, no_globals )
  val SF = syntactic_fingerprint D
in
  print_eval_value(
    quick_to_normal( Eval_value, S, SF, call_count, time_complexity,
      fingerprint ) )
end

fun mk_eval_value Program =
  let 
    val X = program_eval_fun Program
    val Quick = program_eval_type_to_quick X
  in
    quick_to_normal( Quick, 
      syntactic_complexities( Program, #no_globals X ),
      syntactic_fingerprint Program, #call_count X, #time_complexity X,
      #fingerprint X )
  end

fun mk_eval_value_with_time( Program, Max_time ) =
  let 
    val () = set_max_time Max_time
    val X = program_eval_fun' Program
    val Quick = program_eval_type_to_quick X
  in
    quick_to_normal( Quick, 
      syntactic_complexities( Program, #no_globals X ),
      syntactic_fingerprint Program, #call_count X, #time_complexity X,
      #fingerprint X )
  end

fun mk_eval_value_max Program = 
  mk_eval_value_with_time( Program, dh Spec.Max_time_distribution )

fun program_eval_fun_with_time( Program, Max_time ) =
  let 
    val () = set_max_time Max_time
  in
    program_eval_fun' Program
  end

(*
fun program_to_real_outputs( D : ('1a,'1b)d ) 
    : real Vector.vector Vector.vector =
let 
  val () = set_max_time( hd Spec.Max_time_distribution )
  val _ = Spec.clear()
  val ( No_globals, _ ) = Execute.compile_f_dec D

  val Max_problem_no = length Spec.Inputs - 1
  val Output_arity = Array.length( Array.sub( Spec.Output_arrays, 0 ) )
  val Zero = case Spec.Grade.toRealOpt of SOME toReal =>
    toReal( Spec.Grade.zero )
in
  Vector.tabulate( Max_problem_no+1, fn Problem_no => 
    case Execute.execute Problem_no of
      ( Execute.ok_status Ys, _, _ ) => Spec.real_outputs Ys
    | _ => Vector.tabulate( Output_arity, fn _ => Zero ) )
end
*)





exception Wrong_max_time_distribution
val () = 
  if is_sorted( op<, Spec.Max_time_distribution ) then 
    () 
  else
    raise Wrong_max_time_distribution

fun program_eval_fun_max D = 
  program_eval_fun_with_time( D, dh Spec.Max_time_distribution )

fun truncate_syntactic_complexities( {
  n_c, n_w, n_o, extra_quality, n_c', entropy, call_count, time_complexity,
  syntactic_fingerprint,
  syntactic_complexities, fingerprint } : eval_value_type 
  ) : eval_value_type = {
  n_c = n_c, n_w = n_w, n_o = n_o, extra_quality = extra_quality,
  n_c' = n_c', entropy = entropy,
  call_count = call_count, time_complexity = time_complexity,
  syntactic_fingerprint = syntactic_fingerprint,
  syntactic_complexities = 
    map( fn X => real( Real.trunc X ), syntactic_complexities ),
  fingerprint = fingerprint }
    
exception Unknown_fun_to_use

exception Attempt_to_use_abstract_constructor
fun initialize Spec_file_name = (
  Execute.initialize Spec_file_name;
  IDPEF.initialize();
  syntactic_fingerprint_init();
  case map( #1, Predefined.ty_env() ) of Xs =>
    if forall( fn Sym => member( Sym, Xs ) orelse
      is_int Sym orelse is_real Sym,
      Funs_to_use )
    then
      ()
    else
      raise Unknown_fun_to_use;
  Comps_to_use := filter( fn(Sym,_) => member(Sym,Funs_to_use),
                           Predefined.ty_env() ) @
    map( fn Sym => ( Sym, { schematic_vars = [],
                            ty_exp = ty_con_exp( INT, [] ) } ),
      filter( is_int, Funs_to_use ) ) @
    map( fn Sym => ( Sym, { schematic_vars = [],
                            ty_exp = ty_con_exp( REAL, [] ) } ),
      filter( is_real, Funs_to_use ) );
  Arity_zero_funs := map(#1, filter( fn( _, { ty_exp, ... } ) => (
    case ty_exp of
      ty_con_exp(Ty_con,_) =>Ty_con <> THIN_ARROW 
    | _ => true ),
    !Comps_to_use ));

  Semi_abstract_constructors := Symbol_set.list_to_set(
  filter( fn Con => not( exists( fn( Sym, _ ) => Sym = Con, !Comps_to_use ) ),
    Predefined.constructors() ) );

  if exists( fn( F, _ ) => Predefined.is_abstract_constructor F, 
       !Comps_to_use ) 
  then
    raise Attempt_to_use_abstract_constructor
  else
    ();

  Initial_N_leaves := length( !Arity_zero_funs ) + 1
  )

fun reinitialize Spec_file_name = (
  IDPEF.initialize();
  Execute.reinitialize Spec_file_name
  )



end (* functor Evaluate_functor *)

