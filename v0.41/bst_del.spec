datatype bin_tree = bt_nil | bt_cons of int * bin_tree * bin_tree

type input_type = int * bin_tree
type output_type = bin_tree

%%

val Inputs = 
  let 
    fun l X = bt_cons(X,bt_nil,bt_nil)
    val b = bt_cons
  in [
  (5,bt_nil),

  (5, b(5,bt_nil,b(17,b(10,l 9,l 11),l 28)) ),

  (5, b(2,bt_nil,b(20,b(16,b(5,bt_nil,b(8,l 7,l 9)),l 17),l 30)) ),

  (2, b(5,bt_nil,b(20,b(16,b(6,bt_nil,b(8,l 7,l 9)),l 17),l 30)) ),

  (15, b(40,b(20,b(15,bt_nil,b(18,l 17,l 19)),bt_nil),b(60,l 50,l 70)) ),
   
  (35, 
b(20,b(10,l 5,l 12),
     b(40,b(30,l 25,b(35,b(32,l 31,l 33),bt_nil)),l 50)) ),

  (350,
b(200,b(100,l 50,l 120),
     b(400,b(300,l 250,
     b(350,b(320,b(310,b(305,l 303,l 307), b(315,l 313,l 317)), 
                 b(330,b(325,l 323,l 327), b(335,l 333,l 337))),
           b(370,b(360,b(355,l 353,l 357), b(365,l 363,l 367)), 
                 b(380,b(375,l 373,l 377), b(385,l 383,l 387))))),
     l 500)) ),

  (30,
b(20, b(10,l 5,l 12),
      b(40,b(30,b(25,l 22,l 28),b(35,bt_nil,b(37,l 36,l 38))),l 50)) )

  ]
  end

val Validation_inputs = []

val Abstract_types = []



val Funs_to_use = [ "<", "bt_nil", "bt_cons", "false", "true" ]

val Initial_program = NONE

val Reject_funs = []
fun restore_transform D = D


structure Grade : GRADE =
struct

type grade = unit
val zero = ()
val op+ = fn _ => ()
val comparisons = [ fn _ => EQUAL ]
val toString = fn _ =>""
val pack = fn _ => ""
val unpack = fn _ =>()

val post_process = fn _ => ()

val toRealOpt = NONE

end



local

fun inorder bt_nil = nil
  | inorder(bt_cons(RoXs,LeXs,RiXs)) = inorder LeXs @ RoXs::inorder RiXs

fun depth bt_nil = 0
  | depth(bt_cons(_,LeXs,RiXs)) = 1+max2(op<,depth LeXs,depth RiXs)

fun delete_one(_,nil) = nil
  | delete_one(X,Y::Ys) = if X=Y then Ys else Y :: delete_one(X,Ys)

fun is_correct((X,Xs),Ys) =
  inorder Ys = delete_one(X,inorder Xs) andalso depth Ys <= depth Xs

in

fun output_eval_fun( _, Xs : input_type, Ys : output_type )
  : output_eval_type * Grade.grade =
  if is_correct(Xs,Ys) then (correct,()) else (wrong,())
   
end (* local *)


(* Uses 1.35s as upper limit for an scm class and 2s for a lcs class.  *)

val N = 0
val Theta = 0.25
val Max_lcs_class_card = N
val LCS_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 2.0, 1.0/real(N) )
val Max_output_class_card = N
val Time_class_card = N
val Max_scm_class_card = N
val Scm_class_synt_compl_ratio = 
  if N = 0 then 1.0 else real_pow( 1.35, 1.0/real(N) )


val Max_time_distribution = [ 
  10000, 
  50000, 
  250000 ]

val Pe_survival_weights = [ 0.05, 0.05, 0.1 ]
(* For pe3_cmp, pe2_cmp and pe1_cmp respectively. *)

