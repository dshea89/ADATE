(* File: ast_lib4.sml.
   Created: 2000-02-10.
   Modified: 2000-02-11.
*)


structure Ast_lib4 :
sig

val dec_pack : Ast.dec -> string
val dec_unpack : string -> Ast.dec

val atomic_trf_record_pack : Ast_lib2.atomic_trf_record -> string
val atomic_trf_record_unpack : string -> Ast_lib2.atomic_trf_record

end =
struct

open Lib List1 Ast Ast_lib Ast_lib2 Dec_cvt

fun exp_pack( E : exp ) : string =
  list_pack( Word32.toString, vector_to_list( exp_to_vector E ) )

fun exp_unpack( S : string ) : exp =
  vector_to_exp( NONE, Vector.fromList(
    list_unpack( word32_from_string, S ) ) )


fun dec_pack( D : dec ) : string =
  list_pack( Word32.toString, vector_to_list( dec_to_vector D ) )

fun dec_unpack( S : string ) : dec =
  vector_to_dec( NONE, Vector.fromList(
    list_unpack( word32_from_string, S ) ) )

val abstr_kind_pack = abstr_kind_to_string

fun abstr_kind_unpack( S : string ) : abstr_kind =
  case S of
    "abstre" => abstre
  | "rec_arg_type_exists" => rec_arg_type_exists
  | "other_abstr" => other_abstr

fun r_top_poses_pack( ( Top_poses, Bottom_poses ) : r_top_poses ) : string =
  pack[
    pos_list_pack Top_poses,
    option_pack( fn( E, P ) => pack[ exp_pack E, pos_pack P ], Bottom_poses ) 
    ]

fun r_top_poses_unpack( S : string ) : r_top_poses =
let
  val [ T, Bs ] = unpack S
in
  ( pos_list_unpack T,
    option_unpack( fn S => 
      case unpack S of [ E, P ] => ( exp_unpack E, pos_unpack P ),
      Bs ) )
end

fun CSE_record_pack( { case_pos, common_poses_before, v_poses } : CSE_record )
    : string =
  pack[
    pos_pack case_pos,
    pos_list_pack common_poses_before,
    pos_list_pack v_poses ]

fun CSE_record_unpack( S : string ) : CSE_record =
  case unpack S of [ CA, CO, VP ] =>
  { case_pos = pos_unpack CA, common_poses_before = pos_list_unpack CO,
    v_poses = pos_list_unpack VP }


fun R_record_pack( { r_top_poses, bottom_poses, bottom_labels, synted_exp,
                   not_activated_syms } : R_record ) : string =
  pack[
    r_top_poses_pack r_top_poses,
    pos_list_pack bottom_poses,
    list_pack( exp_pack, bottom_labels ),
    exp_pack synted_exp,
    list_pack( symbol_pack, not_activated_syms )
    ]

fun R_record_unpack( S : string ) : R_record =
  case unpack S of [ RT, BP, BL, SE, NAS ] => {
    r_top_poses = r_top_poses_unpack RT,
    bottom_poses = pos_list_unpack BP,
    bottom_labels = list_unpack( exp_unpack, BL ),
    synted_exp = exp_unpack SE,
    not_activated_syms = list_unpack( symbol_unpack, NAS )
    }

val REQ_record_pack = R_record_pack
val REQ_record_unpack = R_record_unpack

fun simple_R_record_pack( { top_pos, rel_bottom_poses, synted_exp,
      synted_exp_bottom_poses } : simple_R_record ) : string =
  pack[
    pos_pack top_pos,
    pos_list_pack rel_bottom_poses,
    exp_pack synted_exp,
    pos_list_pack synted_exp_bottom_poses
    ]

fun simple_R_record_unpack( S : string ) : simple_R_record =
  case unpack S of [ TP, RBP, SE, SEBP ] => {
    top_pos = pos_unpack TP,
    rel_bottom_poses = pos_list_unpack RBP,
    synted_exp = exp_unpack SE,
    synted_exp_bottom_poses = pos_list_unpack SEBP
    }


fun Simple_R_and_CSE_records_pack( { just_before_cse,
      cse_records, after_cse } : Simple_R_and_CSE_records ) : string =
  pack[
    list_pack( simple_R_record_pack, just_before_cse ),
    list_pack( CSE_record_pack, cse_records ),
    list_pack( simple_R_record_pack, after_cse )
    ]


fun Simple_R_and_CSE_records_unpack( S : string ) : Simple_R_and_CSE_records =
  case unpack S of [ JB, CR, A ] => {
    just_before_cse = list_unpack( simple_R_record_unpack, JB ),
    cse_records = list_unpack( CSE_record_unpack, CR ),
    after_cse = list_unpack( simple_R_record_unpack, A )
    }


fun atomic_trf_record_pack( X : atomic_trf_record ) : string =
  case X of
    ABSTR{ let_exp_pos, func, parameters_added, abstr_kind } => 
      pack[ 
        "ABSTR", 
        pos_pack let_exp_pos,
        symbol_pack func,
        list_pack( exp_pack, parameters_added ),
        abstr_kind_pack abstr_kind 
        ]

  | REQ( Records, CSE_records ) =>
      pack[
        "REQ",
        list_pack( REQ_record_pack, Records ),
        Simple_R_and_CSE_records_pack CSE_records
        ]

  | BLASTABLE_MULTIR Records => 
      pack[ "BLASTABLE_MULTIR", list_pack( R_record_pack, Records ) ]

  | DUPL{ top_pos, synted_exp, selected_rhs_poses } =>
      pack[
        "DUPL",
        pos_pack top_pos,
        exp_pack synted_exp,
        pos_list_pack selected_rhs_poses
        ]

  | R( Record, CSE_records ) =>
      pack[
        "R",
        R_record_pack Record,
        list_pack( CSE_record_pack, CSE_records )
        ]

  | BLASTABLE_CASE_DIST Poses =>
      pack[
        "BLASTABLE_CASE_DIST",
        pos_list_pack Poses
        ]

  | match_errors Symbols =>
      pack[
        "match_errors",
        list_pack( symbol_pack, Symbols )
        ]


fun atomic_trf_record_unpack( S : string ) : atomic_trf_record =
  case unpack S of
    [ "ABSTR", LP, F, PA, AK ] =>
      ABSTR{ 
        let_exp_pos = pos_unpack LP,
        func = symbol_unpack F,
        parameters_added = list_unpack( exp_unpack, PA ),
        abstr_kind = abstr_kind_unpack AK
        }

  | [ "REQ", Rec, S ] =>
      REQ( list_unpack( REQ_record_unpack, Rec ), 
           Simple_R_and_CSE_records_unpack S )
        
  | [ "BLASTABLE_MULTIR", Rs ] =>
      BLASTABLE_MULTIR( list_unpack( R_record_unpack, Rs ) )

  | [ "DUPL", TP, SE, SRP ] =>
      DUPL{
        top_pos = pos_unpack TP,
        synted_exp = exp_unpack SE,
        selected_rhs_poses = pos_list_unpack SRP
        }

  | [ "R", REC, CSE ] =>
      R( R_record_unpack REC, list_unpack( CSE_record_unpack, CSE ) )

  | [ "BLASTABLE_CASE_DIST", PS ] =>
      BLASTABLE_CASE_DIST( pos_list_unpack PS )

  | [ "match_errors", S ] =>
      match_errors( list_unpack( symbol_unpack, S ) )
        
  


end (* struct Ast_lib4 *)
