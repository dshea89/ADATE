(*
  File: population.sml
  Created: 1997-04-01.
  Modified: 2001-11-12.
*)

signature POPULATION =
sig

structure Indis : INDIS

type population

val pop_out : TextIO.outstream * population -> unit
val init_lcss : population * 
      Indis.Evaluate.quick_eval_value_type list -> unit
val end_lcss : population -> unit
val bests_insert : Indis.individual * population ->
      Indis.individual list list * population
val bests_insert_check : Indis.individual * population -> bool
val all_class_insert : Indis.individual * population -> population
val all_class_insert_check : Indis.individual * population -> bool
val knocked_out_all_class_insert : Indis.individual * population -> 
      population
val all_indis : population -> Indis.individual list
val screened_all_indis : population -> Indis.individual list
val used_check : Indis.individual * real -> bool
val store_indi_state : Indis.individual -> unit
val update_sigmas : Indis.individual * real -> unit
val synt_compl : Indis.individual -> real
val time_compl : Indis.individual -> real
val Initial_population : population
val restored_insert : Indis.individual * population -> population
val save : population * string * real * real * real list -> unit
val restore : string -> real * real * real list * population
(* val restore_old : string -> real * real * real list * population *)

end






functor Population_functor( structure Indis : INDIS (* structure NN_opt : NN_OPT  *) ) : POPULATION =
struct
open Lib SplayTree List1 Ast Ast_lib Genealogical_search_lib 
  Genealogical_search_lib2 Indis Indis.Evaluate Indis.Evaluate.Spec

structure Indis = Indis

type class = individual * individual lcs_class option * 
  individual output_class option * individual time_class option *
  individual synt_compl_matches ref option
(* ( Base, LCS_class, Output_class, Time class, Scm_class ) *)

type population = class splay list







local

type indi_state = {
  max_cost_limit_used : real,
  last_match_error_cost_limit_sum : real,
  req_match_error_data : REQ_lib.req_match_error_data,
  cutoffs_list : Evaluate.quick_eval_value_type list option list
  }


fun indi_state_pack( { max_cost_limit_used, last_match_error_cost_limit_sum, 
        req_match_error_data,  cutoffs_list } : indi_state ) : string =
  pack[
    real_pack( max_cost_limit_used ), 
    real_pack( last_match_error_cost_limit_sum ), 
    REQ_lib.req_match_error_data_pack( req_match_error_data ), 
    list_pack( fn X => 
      option_pack( fn Ys => list_pack( quick_eval_value_type_pack, Ys ), X ),
      cutoffs_list )
     ]

fun indi_state_unpack( S : string ) : indi_state = (
  case unpack S of [ MC, LM, RMD, CL ] => { 
      max_cost_limit_used = real_unpack MC
        handle Ex => re_raise( Ex, "indi_state_unpack:5" ), 
      last_match_error_cost_limit_sum = real_unpack LM
        handle Ex => re_raise( Ex, "indi_state_unpack:6" ), 
      req_match_error_data = REQ_lib.req_match_error_data_unpack RMD
        handle Ex => re_raise( Ex, "indi_state_unpack:7" ),
      cutoffs_list = list_unpack( fn S1 =>
        option_unpack( fn S2 => 
          list_unpack( quick_eval_value_type_unpack, S2 ),
          S1 ),
        CL  )
        handle Ex => re_raise( Ex, "indi_state_unpack:9" )
      } )
  handle Ex => re_raise( Ex, "indi_state_unpack" )


structure H  = Real_HashTable

exception Cost_limit_used_table_exn
val Cost_limit_used_table : indi_state H.hash_table =
   H.mkTable( 2, Cost_limit_used_table_exn )


fun used_peek( Indi : individual ) : indi_state option =
  H.find Cost_limit_used_table 
    ( syntactic_fingerprint( #program Indi ) ) 

in (* local *)

fun store_indi_state( Indi : individual ) : unit =
let
  val X : indi_state = {
    max_cost_limit_used = !(#max_cost_limit_used Indi ),
    last_match_error_cost_limit_sum = !(#last_match_error_cost_limit_sum Indi),
    req_match_error_data = !(#req_match_error_data Indi ),
    cutoffs_list = !(#cutoffs_list Indi )
    }
in
  H.insert Cost_limit_used_table
    ( syntactic_fingerprint( #program Indi ), X )
end


fun cost_limit_used_table_pack() : string = 
let
  val Xs = H.listItemsi Cost_limit_used_table
  val ( Fingerprints, Indi_states ) = unzip Xs
in
  pack[
    list_pack( real_pack, Fingerprints ),
    list_pack( indi_state_pack, Indi_states )
    ]
end

fun cost_limit_used_table_unpack( S : string ) : unit = 
let
  val [ FI, IS ] = unpack S
  val Fingerprints = list_unpack( real_unpack, FI )
  val Indi_states = list_unpack( indi_state_unpack, IS )
in
  H.clear Cost_limit_used_table;
  loop( fn X => H.insert Cost_limit_used_table X,
    zip( Fingerprints, Indi_states ) )
end

fun used_check( Indi : individual, Cost_limit : real ) : bool =
  case used_peek Indi of
    NONE => ( #max_cost_limit_used Indi := Cost_limit;
              store_indi_state Indi; 
              true )
  | SOME( X as { max_cost_limit_used, ... } ) =>
      if max_cost_limit_used < 0.9999999 * Cost_limit then (
        #max_cost_limit_used Indi := Cost_limit;
        store_indi_state Indi; 
        true )
      else (
        #max_cost_limit_used Indi := max_cost_limit_used;
        #last_match_error_cost_limit_sum Indi := 
          #last_match_error_cost_limit_sum X;
        #req_match_error_data Indi := #req_match_error_data X;
        #cutoffs_list Indi := #cutoffs_list X;
        false
        )

end (* local *)



local

val Sigma_time = ref 0.0
(* Sum of all cost limits used to expand indis from a time class. *)
val Sigma_lcs = ref 0.0
val Sigma_scm = ref 0.0
val Sigma_out = ref 0.0
val Sigma_base = ref 0.0

fun too_big X = !X >= !Sigma_base

in

fun sigmas_pack() : string = list_pack( real_pack, [
  !Sigma_time, !Sigma_lcs, !Sigma_scm, !Sigma_out, !Sigma_base
  ] )
  
fun sigmas_unpack( S : string ) : unit =
let
  val [ T, L, S, O, B ] = list_unpack( real_unpack, S )
in
  Sigma_time := T;
  Sigma_lcs := L;
  Sigma_scm := S;
  Sigma_out := O;
  Sigma_base :=  B
end
  


fun update_sigmas( Indi : individual, Cost_limit : real ) : unit =
  case #trace_info Indi of SOME{ class, ... } =>
  case
  case class of
    time_class => Sigma_time
  | lcs_class => Sigma_lcs
  | scm_class => Sigma_scm
  | out_class => Sigma_out
  | base => Sigma_base
  of
    X => X := !X + Cost_limit

fun  l f = fn Opt => case Opt of NONE => [] | SOME X => f X

fun v( SOME X ) = X

val scm_class_indis = fn Scm_class => scm_indis( !Scm_class )

fun screened_class_indis( 
      Base, LCS_class, Output_class, Time_class, Scm_class ) =
      Base :: 
      ( if too_big Sigma_lcs then [] else l lcs_class_indis LCS_class ) @
      ( if too_big Sigma_out then [] else l output_class_indis Output_class ) @ 
      ( if too_big Sigma_time then [] else l time_class_indis Time_class ) @
      ( if too_big Sigma_scm then [] else l scm_class_indis Scm_class )

end (* local *)


fun class_indis( Base, LCS_class, Output_class, Time_class, Scm_class ) =
      Base :: l lcs_class_indis LCS_class @
      l output_class_indis Output_class @ l time_class_indis Time_class @
      l scm_class_indis Scm_class

fun all_class_indis( Base, LCS_class, Output_class, Time_class, Scm_class ) =
      Base :: l all_lcs_class_indis LCS_class @ 
      l output_class_indis Output_class @ l time_class_indis Time_class @
      l scm_class_indis Scm_class 


fun synt_compl( X : individual ) =
  (hd Syntactic_complexity_selectors)(#eval_value X)

fun synt_compl'( X : individual ) = synt_compl X + 50.0

fun time_compl( X : individual ) =
  #time_complexity( #eval_value X )

fun fingerprint( X : individual ) =
  #fingerprint( #eval_value X )

fun syntactic_fingerprint( X : individual ) =
  #syntactic_fingerprint( #eval_value X )



fun class_out( out : outstream, indi_out : outstream*individual->unit,
      ( Base, LCS_class, Output_class, Time_class, Scm_class ) : class ) =
  let
    fun p S = output(out,S)
  in
    p "CLASS\n\n";
    indi_out(out,Base);
    if Max_lcs_class_card > 0 then (
      p "\n\nLCS class:\n";
      lcs_class_out( out, indi_out, v LCS_class ) )
    else
      ();
    if Max_output_class_card > 0 then (
      p "\n\nOutput class:\n";
      output_class_out( fingerprint, synt_compl, out, 
        indi_out, v Output_class ) )
    else
      ();
    if Time_class_card > 0 then (
      p "\n\nTime class:\n";
      time_class_out( out, indi_out, v Time_class ) )
    else
      ();
    if Max_scm_class_card > 0 then (
      p "\n\nScm class:\n";
      scm_out( out, indi_out, !( v Scm_class ) ) )
    else
      ()
  end



(* Instantiation of lcs, output and scm class functions: *)

fun find_id( X : individual ) = #individual_id X

val create_output_class = fn( Base : individual ) =>
  if Max_output_class_card = 0 then NONE else
  SOME(create_output_class( Base, Max_output_class_card ))

val update_output_class = fn( Output_class, Indi : individual ) => 
  case Output_class of NONE => SOME Indi | SOME Output_class =>
  case output_class_base Output_class of Base =>
  case set_trace_info( Indi,
      SOME{ base_id = #individual_id Base, class = out_class } )
  of Indi =>
  update_output_class( fingerprint, synt_compl, Output_class, Indi )
  : individual option

val update_output_class_check = fn( Output_class, Indi ) =>
  case Output_class of NONE => false | SOME Output_class =>
  update_output_class_check( find_id, fingerprint, synt_compl, 
    Output_class, Indi )



val create_time_class = fn( Base : individual ) =>
  if Time_class_card = 0 then NONE else
  SOME(create_time_class( Time_class_card, time_compl, synt_compl, Base ))

val update_time_class = fn( Time_class : individual time_class option, Indi ) =>
  case Time_class of NONE => [Indi] | SOME Time_class =>
  case time_class_base Time_class of Base =>
  case set_trace_info( Indi,
      SOME{ base_id = #individual_id Base, class = time_class } )
  of Indi =>
  update_time_class( Time_class, Indi )

val update_time_class_check = fn( Time_class, Indi ) =>
  case Time_class of NONE => false | SOME Time_class =>
  update_time_class_check( find_id, Time_class, Indi )



val create_scm_class = fn( Base : individual ) => 
  if Max_scm_class_card = 0 then NONE else SOME(
  create_scm_class( Base, synt_compl', Max_scm_class_card, 
    Scm_class_synt_compl_ratio ) )

fun update_scm_class( Base : individual, Scm_class, Indi : individual ) 
    : individual option = 
  case Scm_class of NONE => SOME Indi | SOME Scm_class =>
  case set_trace_info( Indi,
    SOME{ base_id = #individual_id Base, class = scm_class } )
  of
    Indi =>
  case scm_update( synt_compl Indi, Indi, !Scm_class ) of
    ( NONE, Knocked_out_opt ) => Knocked_out_opt
  | ( SOME New_scm_class, Knocked_out_opt ) => (
      Scm_class := New_scm_class;
      Knocked_out_opt
      )


fun update_scm_class_check( Scm_class, Indi ) : bool =
   case Scm_class of NONE => false | SOME Scm_class =>
   scm_update_check( synt_compl Indi, Indi, !Scm_class )

fun dist { ancestor_evals : quick_eval_value_type list, other : individual } =
  case Max_lcs_class_card >=1 of true =>
  ~(LCS.llcs(quick_pe5_cmp, ancestor_evals, tl(#ancestor_evals other) ))

val create_lcs_class = fn( Base : individual ) =>
  if Max_lcs_class_card = 0 then NONE else SOME(
  create_lcs_class( Base, synt_compl', Max_lcs_class_card, 
    LCS_class_synt_compl_ratio ) )

fun create_class Base : class = ( Base, create_lcs_class Base,
      create_output_class Base, create_time_class Base, 
      create_scm_class Base )

exception Init_lcs_class_Duplicates
val init_lcs_class = 
  fn( Base, LCS_class, Ancestor_evals : quick_eval_value_type list ) =>
    if Max_lcs_class_card = 0 then () else
    case LCS_class of SOME LCS_class =>
    let
      val Xs = Base :: lcs_class_indis LCS_class
      val Ys = fast_make_set( fn( A : individual, B : individual ) => 
        Id.<( #individual_id A, #individual_id B ),
        Xs )
    in
      if length Xs <> length Ys then (
        output( !std_out, "\n\n\nDuplicates found in lcs class:\n");
        indi_out(!std_out,Base);
        lcs_class_out( !std_out, indi_out, LCS_class );
        raise Init_lcs_class_Duplicates
        )
      else
        init_lcs_class( find_id, 
          fn( X : individual) => !(#max_cost_limit_used X) > 0.01,
          dist, Base, Ancestor_evals, LCS_class )
    end

val end_lcs_class = fn LCS_class => 
  if Max_lcs_class_card = 0 then NONE else
  case LCS_class of SOME LCS_class => end_lcs_class( find_id, LCS_class )

val update_lcs_class = 
  fn( Base : individual, LCS_class, Indi : individual ) => 
  case LCS_class of NONE => SOME Indi | SOME LCS_class =>
  case set_trace_info( Indi,
    SOME{ base_id = #individual_id Base, class = lcs_class } )
  of Indi =>
  update_lcs_class( find_id, synt_compl, LCS_class, Indi ) 

val update_lcs_class_check = fn( LCS_class, Indi ) =>
  case LCS_class of NONE => false | SOME LCS_class =>
  update_lcs_class_check( find_id, synt_compl, LCS_class, Indi )


fun all_indis ( Pop : population ) : individual list =
  flat_map( fn T =>
     flat_map( class_indis, Splay_lib.inorder T ),
    Pop )


fun screened_all_indis ( Pop : population ) : individual list =
  flat_map( fn T =>
     flat_map( screened_class_indis, Splay_lib.inorder T ),
    Pop )


(* Hack to avoid MLton bug: *)
(*

fun split Xs =
  case length Xs of N =>
  case N div 2 of Middle =>
  case drop( Middle, Xs ) of Y::Ys =>
    ( take( Middle, Xs ), Y, Ys )


fun fromList  Xs =
  case Xs of
    [] => SplayNil
  | _ => 
  case split Xs of ( Left, M, Right ) =>
    SplayObj{ value = M, left = fromList Left, right = fromList Right }

fun sfilter( p, Xs ) = fromList( filter( p, Splay_lib.inorder Xs ) )
*)

fun create_dummy_class Base : class = 
  ( Base, NONE, NONE, NONE, NONE )


local

val Pe_cmps = flat_map( fn Pei_cmp => map( fn Cmp =>
        fn(X,Y) => Pei_cmp(Cmp,X,Y), Grade.comparisons ),
      [pe1_cmp, pe2_cmp, pe3_cmp ] )

fun mk_synt_compl_cmp( Synt_compl_sel : eval_value_type -> real )
    : individual * individual -> order =
  let
    fun s( X : individual ) = Synt_compl_sel( #eval_value X )
  in
    fn( X, Y ) =>
      let
        val SX = s X
        val SY = s Y
      in
        if SX < SY - Epsilon then
          LESS
        else if SY < SX - Epsilon then
          GREATER
        else
          EQUAL
      end
  end

val Class_synt_compl_cmps : ( class * class -> order ) list =
  map( fn Sel => fn( X, Y ) => (mk_synt_compl_cmp Sel)( #1 X, #1 Y ),
    Syntactic_complexity_selectors )

val Class_pe_cmps : ( class * class -> order ) list =
  map( fn Pe_cmp => fn( X, Y ) => 
    Pe_cmp( #eval_value( #1 X ), #eval_value( #1 Y ) ),
    Pe_cmps )

in (* local *)

val Class_pe_synt_compl_cmps =
  cart_prod( Class_pe_cmps, Class_synt_compl_cmps )

end (* local *)



fun pop_out(out : outstream, Pop : population )
    : unit =
  let
    fun p S = output(out,S)
    fun tree_out Xs = (
      p "\n\nTREE\n\n\n";
      Splay_lib.splay_out( out, 
        fn( out, Class ) => class_out( out, indi_out, Class ), Xs )
      )
  in
    p
"++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
    loop( tree_out, Pop );
    ()
  end



fun init_lcss( Pop : population, 
      Ancestor_evals : quick_eval_value_type list ) : unit =
  if Max_lcs_class_card = 0 then () else
  loop( fn Xs =>
    Splay_lib.loop( fn( Base, LCS_class, _, _, _ ) =>
      init_lcs_class( Base, LCS_class, Ancestor_evals ),
      Xs ),
    Pop )
  


fun end_lcss( Pop : population ) : unit =
  if Max_lcs_class_card = 0 then () else
  loop( fn Xs =>
    Splay_lib.loop( 
      fn( Base, LCS_class, Output_class, Time_class, Scm_class ) =>
        case end_lcs_class LCS_class of
          NONE => ()
        | SOME Y => 
        case update_output_class( Output_class, Y ) of
          NONE => ()
        | SOME Y => 
        case update_time_class( Time_class, Y ) of Time_knocked_out => 
          loop( fn Y => update_scm_class( Base, Scm_class, Y ), 
            Time_knocked_out ),
      Xs ),
    Pop )




fun bests_insert( X : individual, Pop : population )
    : individual list list * population =
    (* Returns ( Knocked out indis, New Pop ) *)
  let
    val X = 
      set_trace_info( X, 
        SOME{ base_id = #individual_id X, class = base } )
    val Anc_evals = tl( #ancestor_evals X )
    fun dummy_class_to_class( Base, _, _, _, _ ) = 
      case create_class Base of
        Class as ( Base, LCS_class, _, _, _ ) => (
          init_lcs_class( Base, LCS_class, Anc_evals );
          Class 
          )
    val Yss = map( fn( ( eval_cmp, synt_compl_cmp ), Xs ) =>
        update_bests( eval_cmp, synt_compl_cmp, dummy_class_to_class, 
          create_dummy_class X, Xs ),
      combine( Class_pe_synt_compl_cmps, Pop ) )
  in
    ( map( fn Classes => flat_map( class_indis, Classes ), 
        map( #1, Yss ) ),
      map( #2, Yss ) )
  end

fun bests_insert_check( X : individual, Pop : population ) : bool =
  exists( fn( ( eval_cmp, synt_compl_cmp ), Xs ) =>
        update_bests_check( eval_cmp, synt_compl_cmp, 
          create_dummy_class X, Xs ),
      combine( Class_pe_synt_compl_cmps, Pop ) )





local

fun find_class( eval_cmp : class * class -> order,
      X : individual, Xs : class splay ) : class option * class splay =
  let
    val X_class = create_dummy_class X
  in
    case Splay_lib.lub( eval_cmp, X_class, Xs ) of
      ( NONE, Xs ) => ( NONE, Xs )
    | ( SOME( Class as ( Base, _, _, _, _ ) ), Xs ) =>
        case filter( fn Indi =>
          real_rep_eq( syntactic_fingerprint X, syntactic_fingerprint Indi ),
          all_class_indis Class )
        of
          _ :: _ => ( NONE, Xs )
        | nil =>
        if #individual_id X = #individual_id Base then
          ( NONE, Xs )
        else
          ( SOME Class, Xs )
  end

fun all_class_insert'( eval_cmp : class * class -> order,
      X : individual, Xs : class splay ) : class splay =
  case find_class( eval_cmp, X, Xs ) of
    ( NONE, Xs ) => Xs
  | ( SOME( Base, LCS_class, Output_class, Time_class, Scm_class ), Xs ) =>
  case update_lcs_class( Base, LCS_class, X ) of
    NONE => Xs
  | SOME Y => 
  case update_output_class( Output_class, Y ) of
    NONE => Xs
  | SOME Y => 
  case update_time_class( Time_class, Y ) of Time_knocked_out => (
  loop( fn Y => update_scm_class( Base, Scm_class, Y ), Time_knocked_out ); 
  Xs )

fun all_class_insert_check'( eval_cmp : class * class -> order,
      X : individual, Xs : class splay ) : bool =
  if Max_lcs_class_card = 0 andalso Max_output_class_card = 0 andalso
     Time_class_card = 0 andalso Max_scm_class_card = 0 then false else
  case find_class( eval_cmp, X, Xs ) of
    ( NONE, Xs ) => false
  | ( SOME( _, LCS_class, Output_class, Time_class, Scm_class ), _ ) =>
      update_lcs_class_check( LCS_class, X ) orelse
      update_output_class_check( Output_class, X ) orelse
      update_time_class_check( Time_class, X ) orelse
      update_scm_class_check( Scm_class, X )


in (* local *)

fun all_class_insert( X, Pop ) =
  map( fn( ( eval_cmp, _ ), Xs ) => all_class_insert'( eval_cmp, X, Xs ),
    combine( Class_pe_synt_compl_cmps, Pop ) )

fun all_class_insert_check( X, Pop ) =
  exists( fn( ( eval_cmp, _ ), Xs ) => 
    all_class_insert_check'( eval_cmp, X, Xs ),
    combine( Class_pe_synt_compl_cmps, Pop ) )

end (* local *)


local

fun knocked_out_all_class_insert'( eval_cmp : class * class -> order,
      X : individual, Xs : class splay ) : class splay =
  let
    val X_class = create_dummy_class X
    val Anc_evals = tl( #ancestor_evals X )
  in
    case Splay_lib.lub( eval_cmp, X_class, Xs ) of
      ( NONE, Xs ) => Xs
    | ( SOME( Class as 
             ( Base, LCS_class, Output_class, Time_class, Scm_class ) ), 
        Xs ) => 
    case filter( fn Indi =>
      real_rep_eq( syntactic_fingerprint X, syntactic_fingerprint Indi ),
      all_class_indis Class )
    of
      _ :: _ => Xs
    | nil => (
    init_lcs_class( Base, LCS_class, Anc_evals );
    case update_lcs_class( Base, LCS_class, X ) of
      NONE => ()
    | SOME Y => 
    case update_output_class( Output_class, Y ) of
      NONE => ()
    | SOME Y => 
    case update_time_class( Time_class, Y ) of Time_knocked_out =>
      loop( fn Y => update_scm_class( Base, Scm_class, Y ), Time_knocked_out );
    case end_lcs_class LCS_class of
      NONE => Xs
    | SOME Y =>
    case update_output_class( Output_class, Y ) of
      NONE => Xs
    | SOME Y => 
    case update_time_class( Time_class, Y ) of Time_knocked_out => (
      loop( fn Y => update_scm_class( Base, Scm_class, Y ), Time_knocked_out ); 
      Xs )
    )
  end

in (* local *)

fun knocked_out_all_class_insert( X, Pop ) =
  map( fn( ( eval_cmp, _ ), Xs ) => 
      knocked_out_all_class_insert'( eval_cmp, X, Xs ),
    combine( Class_pe_synt_compl_cmps, Pop ) )
(*
  handle Ex => (
    output( !std_out, "\n\nknocked_out_all_class_insert:\n\n");
    print_individual X;
    pop_out( !std_out, Pop );
    raise Ex
    )
*)
  

end (* local *)



fun restored_insert( X : individual, Pop : population ) 
    : population =
  let
    val () = best_update X
    val _ = used_check( X, !(#max_cost_limit_used X) )
    val ( Xss, Pop ) = bests_insert( X, Pop )
    fun g( [], Ps ) = Ps
      | g( Y::Ys, Ps ) = g( Ys, knocked_out_all_class_insert( Y, Ps ) )
  in
    g( X :: flatten Xss, Pop )
  end



val Initial_population : population =
  let
    fun g _ = SplayObj{
      value = create_class( set_trace_info( Initial_individual,
        SOME{ base_id = #individual_id Initial_individual, class = base } ) ),
      left = SplayNil,
      right = SplayNil }
  in
    map( g, Class_pe_synt_compl_cmps )
  end

(*
val Initial_population =
let
  fun g Xs = 
    case Xs of 
      nil => Initial_population 
    | X::Xs => 
    case mk_indi( X, [], Evaluate.mk_eval_value X, Initial_individual ) 
    of Indi => (
(*
      p"\n.....................................................\n";
      print_individual Indi;
*)
      restored_insert( Indi, g Xs ) )
in
  g( NN_opt.initial_net_programs( #program Initial_individual ) )
end
*)

val Empty_population : population =
  let
    fun g _ = SplayNil
  in
    map( g, Class_pe_synt_compl_cmps )
  end


local

fun predef_sym_to_string( Cat, 0w0 : Word32.word, N ) =
  pack[ symbol_category_to_string Cat, Word32.toString N ]

fun predef_syms_to_string( Syms : symbol list ) : string =
  pack( flat_map( fn Sym => 
    [ predef_sym_to_string Sym, symbol_to_string Sym ],
    Syms ) )

fun indis_to_save( Pop : population ) : individual list =
  let
    val Base_indis = flat_map( fn T => map( #1, Splay_lib.inorder T ), Pop )
    val LCS_class_indis =
      flat_map( fn T =>
        flat_map( fn( _, LCS_class, _, _, _ ) => 
          l all_lcs_class_indis LCS_class,
          Splay_lib.inorder T ),
        Pop )
    val Output_class_indis =
      flat_map( fn T =>
        flat_map( fn( _, _, Output_class, _, _ ) => 
          l output_class_indis Output_class,
          Splay_lib.inorder T ),
        Pop )
    val Time_class_indis =
      flat_map( fn T =>
        flat_map( fn( _, _, _, Time_class, _ ) => 
          l time_class_indis Time_class,
          Splay_lib.inorder T ),
        Pop )
    val Scm_class_indis =
      flat_map( fn T =>
        flat_map( fn( _, _, _, _, Scm_class ) => 
          l scm_class_indis Scm_class,
          Splay_lib.inorder T ),
        Pop )
  in
    hash_make_set( Base_indis @ LCS_class_indis @ Output_class_indis @
      Time_class_indis @ Scm_class_indis )
  end

in (* local *)

fun save( Pop, File_name, Genealogical_search_time, Global_time,
      Consumption ) : unit =
  let
    val ( No', No ) = Ast.sym_no()
    val Ostr = TextIO.openOut File_name
    val Statistics = pack( [
      real_pack Genealogical_search_time,
      real_pack Global_time,
      Word32.toString No',
      Word32.toString No,
      Id.toString( Id.current_id() ),
      predef_syms_to_string( Ast.get_predefined_syms() ),
      cost_limit_used_table_pack(),
      sigmas_pack()
      ] @ map( real_pack, Consumption ) )
    fun p S = output( Ostr, S )
    val Indis = indis_to_save Pop
    val N = length Indis
  in
    p( Int.toString( String.size Statistics ) ); p "\n";
    p Statistics;
    p( Int.toString N ); p "\n";
    loop( fn Indi => indi_save( Ostr, Indi ), Indis );
    TextIO.closeOut Ostr
  end
  handle _ =>
    output(  !std_err, "\n\nWARNING: Couldn't save population in " ^
      File_name ^ "\n\n" )

end (* local *)

  
local

fun string_to_predef_sym( S : string ) : symbol =
  case unpack S of [ Cat, N ] => 
    ( string_to_symbol_category Cat, 0w0, 
      case Word32.fromString N of SOME X => X )

structure H = Symbol_HashTable

exception String_to_sym_mapping_exn
fun string_to_sym_mapping( S : string ) : symbol H.hash_table =
  let
    val T : symbol H.hash_table = H.mkTable( 2, String_to_sym_mapping_exn )
    fun g [] = T
      | g( Sym :: Str :: Xs ) =
          case string_to_predef_sym Sym of
            Sym as ( Cat, _, _ ) => (
              H.insert T ( Sym, string_to_symbol( Cat, Str ) );
              g Xs )
  in
    g( unpack S )
  end

  
in (* local *)

fun restore( File_name : string ) : real * real * real list * population =
  let
    val Istr = TextIO.openIn File_name
    val N = int_from_string( TextIO.inputLine Istr )
    val Genealogical_search_time :: Global_time :: No' :: No :: Max_used_id ::
        Sym_mapping :: Cost_limit_used_table :: Sigmas :: Consumption =
      unpack( TextIO.inputN( Istr, N ) )
    val SOME No' = Word32.fromString No'
    val SOME No = Word32.fromString No
    val () = Ast.set_sym_no( No', No )
    val Sym_mapping = string_to_sym_mapping Sym_mapping
    val () = cost_limit_used_table_unpack Cost_limit_used_table
    val () = sigmas_unpack Sigmas
    val () = Id.set_id( case Id.fromString Max_used_id of SOME X => X )
    val SOME N = Int.fromString( TextIO.inputLine Istr )
    fun g( 0, Pop ) = Pop
      | g( N, Pop ) = 
          g( N-1, 
             restored_insert( indi_restore( Sym_mapping, Istr), Pop ) )
    val Pop = g( N, Empty_population );
  in
    TextIO.closeIn Istr;
    ( real_unpack Genealogical_search_time,
      real_unpack Global_time,
      map( real_unpack, Consumption ),
      Pop )
  end
  handle Ex => re_raise( Ex, "restore" )

(*
fun restore_old( File_name : string ) : real * real * real list * population =
  let
    val Istr = TextIO.openIn File_name
    val N = valOf( Int.fromString( TextIO.inputLine Istr ) )
    val Genealogical_search_time :: Global_time :: No' :: No :: Max_used_id ::
        Sym_mapping :: Consumption =
      unpack( TextIO.inputN( Istr, N ) )
    val SOME No' = Word32.fromString No'
    val SOME No = Word32.fromString No
    val () = Ast.set_sym_no( No', No )
    val Sym_mapping = string_to_sym_mapping Sym_mapping
    val () = Id.set_id( valOf( Id.fromString Max_used_id ) )
    val SOME N = Int.fromString( TextIO.inputLine Istr )
    fun g( 0, Pop ) = Pop
      | g( N, Pop ) = 
          g( N-1, 
             restored_insert( old_indi_restore( Sym_mapping, Istr), Pop ) )
    val Pop = g( N, Empty_population );
  in
    TextIO.closeIn Istr;
    ( valOf( Real.fromString Genealogical_search_time ),
      valOf( Real.fromString Global_time ),
      map( valOf o Real.fromString, Consumption ),
      Pop )
  end
*)

end (* local *)
  

        
        




end (* functor Population_functor *)
