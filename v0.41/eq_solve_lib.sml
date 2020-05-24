(*
  File: eq_solve_lib.sml
  Taken out from lib.sml 1998-09-14
  Modified 1998-09-14
*)


structure Eq_solve_lib :
sig

  val eq_solve : ( real -> real ) * real * real * real * real * real -> real
  val eq_solve_is' : ( ( real * real ) -> bool ) * 
    ( real -> real ) * real * real * real * real * real -> real option
  val eq_solve_is_start' : ( real -> bool ) * ( ( real * real ) -> bool ) * 
    bool *
    ( real -> real ) * real * real -> real option
  val eq_solve_is_start_list' : ( ( real * real ) -> bool ) * bool *
    ( real option list -> real option list ) * real * real list -> 
    real option list

end =
struct
open Lib List1


exception Eq_solve
fun eq_solve( F : real->real, Epsilon : real, Lower : real, F_Lower : real,
      Upper : real, F_Upper : real ) : real =
(* Finds X such that Lower<=X<=Upper and such that abs(F X) < Epsilon.
   Uses linear interpolation.
*)
if not(F_Lower<=0.0 andalso F_Upper>=0.0) orelse real_rep_eq(F_Lower,F_Upper) 
then
  raise Eq_solve
else
  let val New_X = Lower - F_Lower/(F_Upper-F_Lower)*(Upper-Lower)
      val New_F = F New_X
  in
    if abs New_F < Epsilon then
      New_X
    else if New_F<=0.0 then
      eq_solve(F,Epsilon,New_X,New_F,Upper,F_Upper)
    else
      eq_solve(F,Epsilon,Lower,F_Lower,New_X,New_F)
  end

exception Eq_solve_is
fun eq_solve_is'( stop : real * real -> bool,
      F : real->real, Epsilon : real, Lower : real, F_Lower : real,
      Upper : real, F_Upper : real ) : real option =
(* Finds X such that Lower<=X<=Upper and such that abs(F X) < Epsilon.
   Uses interval halving.
*)
if not(F_Lower<=0.0 andalso F_Upper>=0.0) orelse real_rep_eq(F_Lower,F_Upper) 
then
  raise Eq_solve_is
else if stop( Lower, Upper ) then
  NONE
else
  let val New_X = (Upper+Lower)/2.0
      val New_F = F New_X
  in
    if abs New_F < Epsilon then
      SOME New_X
    else if New_F<=0.0 then
      eq_solve_is'(stop,F,Epsilon,New_X,New_F,Upper,F_Upper)
    else
      eq_solve_is'(stop,F,Epsilon,Lower,F_Lower,New_X,New_F)
  end

fun eq_solve_is(  F : real->real, Epsilon : real, Lower : real, F_Lower : real,
      Upper : real, F_Upper : real ) : real =
  case eq_solve_is'( fn _ => false, 
         F, Epsilon, Lower, F_Lower, Upper, F_Upper )
  of
    SOME X => X

exception Eq_solve_is_start_exn
fun eq_solve_is_start'( stop1 : real -> bool, stop : real * real -> bool,
      Increasing : bool, f : real -> real, Epsilon : real,
      Start : real ) : real option =
  if Start <= 0.0 then raise Eq_solve_is_start_exn else
  case f Start of F_Start =>
  if abs F_Start < Epsilon then SOME Start else
let
  fun ok F_X = abs F_X < Epsilon orelse
    F_Start <= 0.0 andalso F_X >= 0.0 orelse
    F_Start >= 0.0 andalso F_X <= 0.0
  val Alpha = 1.1
  fun g X =
    if stop1 X then
      NONE
    else
    case f X of F_X =>
    if ok F_X then
      SOME( X, F_X )
    else
    case ( Increasing, F_Start < 0.0 ) of
      ( true, true ) => g( X * Alpha )
    | ( true, false ) => g( X / Alpha )
    | ( false, true ) => g( X / Alpha )
    | ( false, false ) => g( X * Alpha )
in
  case g Start of
    NONE => NONE
  | SOME G_Start =>
let
  val ( Lower,  F_Lower ) =
    if F_Start < 0.0 then ( Start, F_Start ) else G_Start
  val ( Upper, F_Upper ) =
    if F_Start < 0.0 then G_Start else ( Start, F_Start )
in
  if abs F_Lower < Epsilon then
    SOME Lower
  else if abs F_Upper < Epsilon then
    SOME Upper
  else
    eq_solve_is'( stop, f, Epsilon, Lower, F_Lower, Upper, F_Upper )
end
end
  
 









datatype so_far = 
    none 
  | some of real
  | data of { lower : real, f_lower : real, upper : real, f_upper : real }

exception Eq_solve_is_list
fun eq_solve_is_list'( 
      stop : real * real -> bool,
      f : real option list -> real option list,
      Epsilon : real, 
      So_far : so_far list
      ) : real option list =
if exists( 
     fn data { lower, f_lower, upper, f_upper } => 
          not(f_lower<=0.0 andalso f_upper>=0.0) orelse 
              real_rep_eq(f_lower,f_upper) 
      | _ => false,
     So_far )
then
  raise Eq_solve_is_list
else
let
  val So_far = map(
          fn( Z as data{ lower, upper, ... } ) => 
               if stop( lower, upper ) then none else Z
           | Z => Z,
          So_far )
in
if forall( fn none => true | some _ => true | data _ => false, So_far ) then
  map( fn none => NONE | some X => SOME X, So_far )
else
let
  val Args = map(
    fn data { lower, f_lower, upper, f_upper } => 
         SOME( ( upper + lower ) / 2.0 )
     | _ => NONE,
     So_far )
  val Result = f Args
  val So_far = map( fn( ( New_f_opt, A ), Z ) =>
    case New_f_opt of
      NONE => Z
    | SOME New_f => 
        case A of SOME X =>
        case Z of data{ lower, f_lower, upper, f_upper } =>
        if abs New_f < Epsilon then 
          some X
        else if New_f <= 0.0 then
          data{ lower = X, f_lower = New_f, upper = upper, f_upper = f_upper }
        else
          data{ lower = lower, f_lower = f_lower, upper = X, f_upper = New_f },
    combine( combine( Result, Args ), So_far ) )
in
  eq_solve_is_list'( stop, f, Epsilon, So_far )
end
end (* fun eq_solve_is_list' *)
  

datatype fin_unfin = finished of ( real * real ) option | unfinished of real

exception Eq_solve_is_start_list_exn
fun eq_solve_is_start_list'( 
      stop : real * real -> bool,
      Increasing : bool, 
      f : real option list -> real option list, 
      Epsilon : real,
      Starts : real list ) : real option list =
  if exists( fn Start => Start <= 0.0, Starts ) then
    raise Eq_solve_is_start_list_exn
  else
  let
    val F_Starts = f( map( fn X => SOME X, Starts ) )
    val F_Starts : real list = map( fn SOME Y => Y, F_Starts )

    fun ok( F_Start, F_X ) = 
    abs F_X < Epsilon orelse
    F_Start <= 0.0 andalso F_X >= 0.0 orelse
    F_Start >= 0.0 andalso F_X <= 0.0

  val Alpha = 1.1

  fun g( Xs : fin_unfin list ) : ( real * real ) option list =
  let
    val F_Xs = f( map( fn unfinished X => SOME X | _ => NONE, Xs ) )
    val Xs = map(
      fn( ( unfinished X, SOME F_X ), F_Start ) =>
          if ok( F_Start, F_X ) then
            finished( SOME( X, F_X ) )
          else unfinished(
            case ( Increasing, F_Start < 0.0 ) of
              ( true, true ) => X * Alpha
            | ( true, false ) => X / Alpha
            | ( false, true ) => X / Alpha
            | ( false, false ) => X * Alpha
            )
      | ( ( Z as finished _, NONE ), _ ) => Z
      | ( ( unfinished _, NONE ), _ ) => finished NONE,
      combine( combine( Xs, F_Xs ), F_Starts ) )
  in
    if forall( fn finished _ => true | _ => false, Xs ) then
      map( fn finished Z => Z, Xs )
    else
      g Xs
  end

  val G_Starts : ( real * real ) option list =
    g(
      map( fn( Start, F_Start ) =>
        if abs F_Start < Epsilon then
          finished( SOME( Start, F_Start ) )
        else
          unfinished Start,
        combine( Starts, F_Starts ) ) 
      )
         

  val So_far : so_far list =
    map( fn( ( Start, F_Start ), G_Start_opt ) =>
      case G_Start_opt of
        NONE => none
      | SOME G_Start =>
      if abs F_Start < Epsilon then
        some Start
      else if abs( #2 G_Start ) < Epsilon then
        some( #1 G_Start )
      else if F_Start < 0.0 then
        data{ lower = Start, f_lower = F_Start, 
              upper = #1 G_Start, f_upper = #2 G_Start }
      else
        data{ lower = #1 G_Start, f_lower = #2 G_Start,
              upper = Start, f_upper = F_Start },
      combine( combine( Starts, F_Starts ), G_Starts ) )

  in
    eq_solve_is_list'( stop, f, Epsilon, So_far )
  end (* fun eq_solve_is_start_list' *)
  
 

    




















end (* structure Eq_solve_lib *)
