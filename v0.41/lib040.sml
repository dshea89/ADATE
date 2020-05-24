(* File: lib40.sml
   Created 1993-06-01
   Modified 1998-09-14.
*)

structure Lib =
struct
open Math


fun for( L, U, f ) =
  if L>U then
    ()
  else (
    f L;
    for( L+1, U, f )
    )

fun real_for( L, U, f ) =
  if L>U then
    ()
  else (
    f L;
    real_for( L+1.0, U, f )
    )

type outstream = TextIO.outstream
val std_err = ref TextIO.stdErr
val std_out = ref TextIO.stdOut
fun output( stream : outstream, S : string ) = 
  TextIO.output(stream, S)
fun flush_out( stream : outstream ) = TextIO.flushOut stream
fun flush_output( stream : outstream, S : string ) = (
  flush_out stream;
  output(stream, S)
  )

fun p S = ( output( !std_out, S ); flush_out( !std_out ) )

fun nl() = output(!std_out,"\n");

fun print_int N = p(Int.toString N)
fun print_word32 N = p(Word32.toString N)
fun print_real N = p(Real.toString N)
fun print_bool N = p(Bool.toString N)

fun print_option(print : 'a -> unit, X : 'a option ) =
  case X of NONE => p"NONE" | SOME X => ( p"SOME( "; print X; p" )" )

fun print_int_option X = print_option( print_int, X )
fun print_real_option X = print_option( print_real, X )
fun print_bool_option X = print_option( print_bool, X )


fun array_out(
      out : outstream, 
      print : outstream * 'a -> unit, 
      Xs : 'a Array.array ) =
  let fun p S = output(out,S)
  in
  for( 0, Array.length Xs -1, fn I => (
    p( "\n" ^ Int.toString I ^ " : " ); print( out, Array.sub( Xs, I ) )
    ) )
  end

fun print_array( print : 'a -> unit, Xs : 'a Array.array ) : unit =
  array_out( !std_out, fn( _, X ) => print X, Xs )

exception My_mod_exn
fun op mod( N, K ) = 
  if N < 0 orelse K < 0 then raise My_mod_exn else N - K * ( N div K )
(* To avoid segmentation fault under gdb in SML/NJ 110.0.3 *)

val Max_int = case Int.maxInt of SOME X => X - 3
val Max_word = Word.fromInt Max_int
val Max_word32 = Word32.fromInt Max_int
val Max_real = 1.0E99


fun word32_to_bin_string( X : Word32.word ) : string =
  let
    fun g( N : int, X : Word32.word ) =
      if N = 0 then
        ""
      else
        g( N-1, Word32.>>( X, 0w1 ) ) ^
        Word32.toString( Word32.andb( X, 0w1 ) ) 
  in
    g(32,X)
  end

fun bin_string_to_word32( Xs : string ) : Word32.word =
  let
    fun h( #"0" ) = 0w0
      | h( #"1" ) = 0w1
    fun g( Xs : char list ) : Word32.word =
      case Xs of
        [X1] => h X1
      | X1::Xs1 => Word32.orb( h X1, Word32.<<( g Xs1, 0w1 ) )
  in
    g( rev( explode Xs ) )
  end

fun is_NONE NONE = true
  | is_NONE _ = false

fun is_SOME( SOME _ ) = true
  | is_SOME _ = false
fun pack( Xs : string list ) : string =
  let
    fun g [] = []
      | g( X :: Xs ) = Int.toString( String.size X ) ^ "\n" :: X :: g Xs
  in
    String.concat( g Xs )
  end
fun unpack( S : string ) : string list =
  let
    val Len = String.size S
    fun nl_pos Start =
      if Start >= Len then
        NONE
      else
        case String.sub( S, Start ) of 
          #"\n" => SOME Start
        | _ => nl_pos( Start + 1 )     

    fun read_len( Start : int ) : ( int * int ) option =
      case nl_pos Start of
        NONE => NONE
      | SOME Pos =>
      case Int.fromString( String.substring( S, Start, Pos-Start ) ) of
        SOME Len => SOME( Len, Pos+1 )

    fun g Start=
      case read_len Start of
        NONE => []
      | SOME( Len, Start ) => String.substring( S, Start, Len ) :: g(Start+Len)
  in
    g 0
  end
  
exception Internal_error

fun re_raise(Ex:exn,S:string) = (
  flush_out( !std_out );
  output(!std_out,"\nre_raise: "^S^"\n");
  flush_out( !std_out );
  raise Ex
  )

fun inc X = if !X < Max_int then X := !X + 1 else ()

fun real_inc( X : real ref ) : unit = X := !X + 1.0

fun word_inc( X : Word.word ref) =
 ( X := Word.+( !X, Word.fromInt 1) )


fun word32_inc( X : Word32.word ref) =
 ( X := Word32.+( !X, Word32.fromInt 1) )


local val Eps = 1.0E~6 in
fun real_eq(X:real,Y:real):bool =
  if abs Y < Eps then
    abs X < Eps
  else
    case X/Y of Ratio =>
      1.0-Eps<Ratio andalso Ratio<1.0+Eps
end

fun real_rep_eq( X : real, Y : real ) = 
  case Real.compare( X, Y ) of EQUAL => true | _ => false




fun to_n_decimals( N : real, X : real ) : real =
  case Real.compare( X, 0.0 ) of EQUAL => X | _ =>
let
  val { exp, man } = Real.toManExp X
  val man = Real.realFloor( N * man ) / N
in
  Real.fromManExp{ exp = exp, man = man }
end

fun real_compare_n ( N : real ) ( X : real, Y : real ) : order =
  Real.compare( to_n_decimals( N, X ), to_n_decimals( N, Y ) )
  handle E => (
    p"\n\nreal_compare_n:";
    p"\n  N = "; print_real N;
    p"\n  X = "; print_real X;
    p"\n  Y = "; print_real Y;
    nl();
    raise E )

local

fun normalize X = 
  if X > 1.0 orelse X < ~1.0 then 
    normalize( X / 2.55343525364845 )
  else
    X

in

fun normrealhash( X : real ) = 
  if Real.isNormal X then
    normalize( case Real.toManExp X of { man, exp } => 
      man * (real exp + 0.38197515646351) )
  else
    0.827651972948738


fun normrealhash'( X : real ) = 
  if Real.isNormal X then
    normalize X
  else
    0.827651972948738

end

fun max2(less,X,Y) = if less(X,Y) then Y else X
fun min2(less,X,Y) = if less(X,Y) then X else Y

fun cmp_invert cmp = fn( X, Y ) => cmp( Y, X )

fun sqr( X : real ) = X * X

fun real_pow(X,Y) = exp(Y*ln X)

fun log2 X = Math.ln X / Math.ln 2.0

fun real_factorial N = if N<=0.0 then 1.0 else N*real_factorial(N-1.0)


fun is_prime(N:int) : bool =
  let val Max=ceil(sqrt(real N))
      fun try I =
        I>Max orelse not(N mod I=0) andalso try(I+1)
  in
    try 2
  end

val Big_prime =
  let fun try N = if is_prime N then N else try(N-1) in
    try Max_int
  end

exception Real_mod
fun real_mod(X:real,Y:real) =
  X - real(trunc(X/Y))*Y
  handle Div => raise Real_mod
       | Overflow => raise Real_mod

local
  val Max = real Max_int - 7.0
in

fun hash_real_to_int( X : real ) : int = Real.trunc( normrealhash X * Max  )
handle Ex => (
  p"\nhash_real_to_int: X = "; p( Real.toString X );
  re_raise( Ex, "hash_real_to_int" ) )

fun hash_real_to_word( X : real ) : word = 
  Word.fromInt( Real.trunc( normrealhash X * Max ) )
handle Ex => (
  p"\nhash_real_to_word: X = "; p( Real.toString X );
  re_raise( Ex, "hash_real_to_word" ) )

end (* local *)

fun real_compare( X : real, Y ) =
  if X < Y then
    LESS
  else if Y < X then
    GREATER
  else 
    EQUAL

structure Int_hash_key =
struct
  type hash_key=int
  fun hashVal(X:int)= Word.fromInt X
  fun sameKey(X,Y:int)= X=Y
end

structure Int_HashTable = HashTableFn(Int_hash_key)

structure Int_dyn = DynamicArrayFn(
  struct
    open Array
    type elem = int
    type vector = elem Vector.vector
    type array = int array
    structure Vector =
struct
  open Vector
  type elem = int
  type vector = elem Vector.vector
end
  end 
  )

structure Real_dyn = DynamicArrayFn(
  struct
    open Array
    type elem = real
  type vector = elem Vector.vector
    type array = real array
    structure Vector = 
struct
  open Vector
  type elem = real
  type vector = elem Vector.vector
end
  end 
  )




structure Real_hash_key =
struct
  fun hashVal(X:real) = Word.fromInt( hash_real_to_int X )
  fun sameKey(X:real,Y:real) = real_rep_eq( X, Y )
  type hash_key=real
end

structure Real_HashTable = HashTableFn(Real_hash_key)


structure Word32_dyn = DynamicArrayFn( 
  struct
    open Array
    type elem = Word32.word
    type vector = elem Vector.vector
    type array = Word32.word array
    structure Vector =
struct
  open Vector
  type elem = Word32.word
  type vector = elem Vector.vector
end
  end 
  )

structure Word8_dyn =  DynamicArrayFn(
  struct
    open Array
    type elem = Word8.word
    type vector = elem Vector.vector
    type array = Word8.word array
    structure Vector =
struct
  open Vector
  type elem = Word8.word
  type vector = elem Vector.vector
end
  end 
  )

structure Word_hash_key =
struct
  type hash_key=word
  fun hashVal(X:word)=  X
  fun sameKey(X,Y:word)= X=Y
end

structure Word_HashTable = HashTableFn(Word_hash_key)


structure String_hash_key =
struct
  type hash_key=string
  val hashVal = HashString.hashString
  fun sameKey(X,Y:string)= X=Y
end

structure String_HashTable = HashTableFn(String_hash_key)


fun timeit( f : unit -> 'a ) =
  let
    val start = Timer.startCPUTimer ();
    val result = f();
    val non_gc_time = #usr(Timer.checkCPUTimer start);
  in
   print( Real.toString( Time.toReal non_gc_time ) );
   print "\n"; 
   result
  end;


fun time_to_real X= Time.toReal X
  handle Ex => re_raise( Ex, "time_to_real" )

fun real_to_time X = Time.fromReal X
  handle Ex => (
    output(!std_err, "\n\nreal_to_time: X = " ^ Real.toString X);
    re_raise( Ex, "real_to_time" )
    )

type timer = ( int * string * bool * real * Timer.cpu_timer ) ref

fun print_timer(T : timer) : unit =
let 
  val ( I, Id, Running, So_far, Timer ) = !T
in
  p"\n Id = "; p Id;
  p"\n I = "; print_int I;
  p"\n Running = "; print_bool Running;
  p"\n So_far = "; print_real So_far;
  nl()
end
   



local

structure H = Int_HashTable
exception Timers_exn
val Timers : timer H.hash_table = H.mkTable( 10000, Timers_exn )
exception Too_many_timers

in

fun mk_timer( Id ) : timer =  
  case H.numItems Timers of I =>
  case ref( I, Id, false, 0.0, Timer.startCPUTimer() )
    handle Ex => re_raise( Ex, "mk_timer" )
  of
    Timer => (
      if I > 10000 then raise Too_many_timers else ();
      H.insert Timers ( I, Timer );
      Timer )

exception Delete_timer_exn
fun delete_timer( T : timer ) : unit =
  case !T of ( I, Id, _, _, _ ) => 
  case H.numItems Timers of I' =>
  if I <> I'-1 then raise Delete_timer_exn else
  case H.remove Timers I of T' => case !T' of (_, Id', _, _, _ ) =>
    if Id' = Id then () else raise Delete_timer_exn

exception Start_timer
fun start_timer( T : timer ) =
  T := 
    let 
      val ( I, Id, Running, So_far, Timer ) = !T
    in
      if Running then (
        p( "\n\nstart_timer: " ^ Id );
        raise Start_timer )
      else
        ( I, Id, true, So_far, Timer.startCPUTimer() )
    end
    handle Ex => re_raise( Ex, "start_timer" )

fun timer_running( T : timer ) = #3(!T)

exception Stop_timer
fun stop_timer(T) =
  (
  T := 
    let 
      val ( I, Id, Running, So_far, Timer ) = !T
    in
      if not(Running) then (
        p( "\n\nstop_timer: " ^ Id );
        raise Stop_timer )
      else
        ( I, Id, false, 
          So_far+time_to_real(#usr(Timer.checkCPUTimer Timer)), Timer)
    end)
(*
    handle Time.Time => (
      output(!std_err,"\nstop_timer: Exn Time handled :" ^
        Real.toString(#2(!T)) ^ "\n");
      stop_timer T
      )
   | Ex => re_raise( Ex, "stop_timer" )
*)

fun check_timer(T) : real =
    let 
      val ( I, Id, Running, So_far, Timer ) = !T
    in
      if Running then
        So_far+time_to_real(#usr(Timer.checkCPUTimer Timer))
(*
        handle Time.Time => (
          output(!std_err,"\ncheck_timer: Exn Time handled :" ^
            Real.toString So_far ^ "\n");
          check_timer T
          )
*)
      else
        So_far
    end
    handle Ex => (
      p"\ncheck_timer: T = "; print_timer T; nl(); raise Ex )

fun set_timer(T,To:real) : unit =
  (case !T of ( I, Id, Running, _, _ ) =>
  T := ( I, Id, Running, To, Timer.startCPUTimer() ) )
  handle Ex => re_raise( Ex, "set_timer" )

local

val Running_timers : int list ref = ref []

in

fun prepare_timers_for_export() =
let 
  val Rs : timer H.hash_table = H.copy Timers
  val () =  H.filter (fn T => timer_running T) Rs

  val Rs : timer list = H.listItems Rs
in
  Running_timers := List.map ( fn T => #1( !T ) ) Rs;
  List.app ( fn T => stop_timer T ) Rs
end

fun recover_timers_from_export() =
  List.app ( fn I => start_timer( H.lookup Timers I ) ) ( !Running_timers )

end (* local *)

end (* local *)

fun sort (op < : 'a * 'a -> bool) ls = let 
          fun merge([],ys) = ys
            | merge(xs,[]) = xs
            | merge(x::xs,y::ys) =
                if y < x then y::merge(x::xs,ys) else x::merge(xs,y::ys)
          fun mergepairs(ls as [l], k) = ls
            | mergepairs(l1::l2::ls,k) =
                if k mod 2 = 1 then l1::l2::ls
                else mergepairs(merge(l1,l2)::ls, k div 2)
            | mergepairs _ = raise Internal_error
          fun nextrun(run,[])    = (rev run,[])
            | nextrun(run,x::xs) = if hd run < x then nextrun(x::run,xs)
                                   else (rev run,x::xs)
          fun samsorting([], ls, k)    = hd(mergepairs(ls,0))
            | samsorting(x::xs, ls, k) = let 
                val (run,tail) = nextrun([x],xs)
                in samsorting(tail, mergepairs(run::ls,k+1), k+1)
                end
          in 
            case ls of [] => [] | _ => samsorting(ls, [], 0)
          end

fun stable_merge(less,[],Ys) = Ys
  | stable_merge(less,Xs,[]) = Xs
  | stable_merge(less,X::Xs,Y::Ys) =
  if less(Y,X) then 
    Y::stable_merge(less,X::Xs,Ys) 
  else 
    X::stable_merge(less,Xs,Y::Ys)


fun cmpsort( cmp : 'a * 'a -> order, Xs : 'a list ) =
  sort ( fn( X1, X2 ) => case cmp( X1, X2 ) of LESS => true | _ => false ) Xs 



local

val Rand = Random.rand( 6951246, ~215434691 )

in

val randInt = fn() => Random.randInt Rand
val randNat = fn() => Random.randNat Rand
val randReal = fn() => Random.randReal Rand
val randRange = fn(Low,High) => Random.randRange (Low,High) Rand

end

local

fun randTime() : int =
let
  val N = Time.toReal( Time.now() )
in
  round( Real.rem( N * 100.0, 1.0e6 ) )
end

in

fun randomize( N : int ) = (
  for( 1, randTime() + N, fn _ => randReal() );
  p"\nrandomize : "; print_real( randReal() ); p"\n"
  )

end

fun int_from_string S =
  case Int.fromString S of SOME X => X
        
fun word_from_string S =
  case Word.fromString S of SOME X => X
        
fun word32_from_string S =
  case Word32.fromString S of SOME X => X
        
fun bool_from_string S =
  case Bool.fromString S of SOME X => X
      
(*

Better implementation provided in ast_aux.sml.

local

exception Real_conversion_exn
fun test( to : real -> 'a, from : 'a -> real ) =
  for( 1, 10000, fn _ =>
  let
    val X = randReal() / randReal()
    val X = if randReal() < 0.5 then ~X else X
  in
    if real_rep_eq( X, from( to X ) ) then () else raise Real_conversion_exn
  end )


exception Unexpected_Real_precision_exn

val () = 
  if Real.precision <> 52 then raise Unexpected_Real_precision_exn else ()

val K = real_pow( 2.0, 27.0 )
val K = real( Real.round K )

exception Real_conversion_failure1

fun to' X =
let
  val Negative = Real.signBit X
  val X = if Negative then ~X else X
  val { exp, man } = Real.toManExp X
  val { frac, whole } = Real.split( man * K )
  val { frac = F2, whole = W2 } = Real.split( frac * K )
  val () = 
    if real_rep_eq( F2, 0.0 ) then () else raise Real_conversion_failure1
in
  { negative = Negative, exp = exp, 
    whole = Real.round whole, w2 = Real.round W2 }
end

fun from'{ negative : bool, exp : int, whole : int, w2 : int } =
let
  val frac = real w2 / K
  val man = (real whole + frac) / K
  val X = Real.fromManExp{ exp = exp, man = man }
in
  if negative then ~X else X
end
in

fun real_to_string( X : real ) : string =
let
  val { negative, exp, whole, w2 } = to' X
in
  pack[ Bool.toString negative, Int.toString exp,
        Int.toString whole, Int.toString w2 ]
end

fun real_from_string( S : string ) : real =
let
  val [ negative, exp, whole, w2 ] = unpack S
  val whole = int_from_string whole
  val w2 = int_from_string w2
in
  if whole = 0 andalso w2 = 0 then 0.0 else
  from'{ negative = bool_from_string negative, exp = int_from_string exp, 
    whole = whole, w2 = w2 }
end
  handle Ex => (
    p"\nreal_from_string:\n";
    p" S = "; p S; p"\n\n";
    raise Ex )

val real_pack = real_to_string
val real_unpack = real_from_string

val int_pack = Int.toString
val int_unpack = fn S => case Int.fromString of SOME N => N

val () = test( real_to_string, real_from_string )


end

*)

end (* structure Lib *)


structure List1 =
struct
open Lib;

fun list_less(less,_,[]) = false
  | list_less(less,[],_) = true
  | list_less(less,X::Xs,Y::Ys) =
      less(X,Y) orelse ( not(less(Y,X)) andalso list_less(less,Xs,Ys) )

fun list_compare( cmp, [], [] ) = EQUAL
  | list_compare( cmp, [], _ ) = LESS
  | list_compare( cmp, _, [] ) = GREATER
  | list_compare( cmp, X :: Xs, Y :: Ys ) = 
  case cmp( X, Y ) of
    EQUAL => list_compare( cmp, Xs, Ys )
  | Z => Z

fun snoc(Xs,X) = Xs@(X::nil)

fun dh(X::nil) = X
  | dh(X::Xs) = dh(Xs)

fun lt(X::nil) = nil
  | lt(X::Xs) = X::(lt Xs)

exception Nth;
fun nth( X::_, 0 ) = X
  | nth( _::Xs, N ) = if N>0 then nth(Xs,N-1) else raise Nth
  | nth(_,_) = raise Nth;

fun index(X,Y::Ys) =
  if X=Y then 0 else 1+index(X,Ys)

fun index_opt(X,[]) = NONE
  | index_opt(X,Y::Ys) = if X=Y then SOME 0 else
      case index_opt(X,Ys) of NONE => NONE | SOME N => SOME(1+N)

fun index_opt'( _, [] ) = NONE
  | index_opt'( found, Y::Ys) = if found Y then SOME 0 else
      case index_opt'( found, Ys ) of NONE => NONE | SOME N => SOME(1+N)

fun take(N,[]) = []
  | take(N,X::Xs) = if N>0 then X::take(N-1,Xs) else []

fun drop(_,[]) = []
  | drop(N,X::Xs) = if N>0 then drop(N-1,Xs) else X::Xs

fun takewhile(p,[]) = []
  | takewhile(p,X::Xs) =
  if p X then X::takewhile(p,Xs) else nil

fun dropwhile(p,[]) = []
  | dropwhile(p,X::Xs) = 
      if p X then dropwhile(p,Xs) else X::Xs

exception List_replace;
fun list_replace( X::Xs, 0, Y ) = Y::Xs
  | list_replace( X::Xs, N, Y ) =
      if N>0 then X::list_replace(Xs,N-1,Y) else raise List_replace
  | list_replace(_,_,_) = raise List_replace;

exception Delete_nth
fun delete_nth(nil,_) = raise Delete_nth
  | delete_nth(X::Xs,N) = if N=0 then Xs else X::delete_nth(Xs,N-1)

fun fromto(Lower,Upper) =
  if Lower>Upper then nil else Lower::fromto(Lower+1,Upper)


fun real_sum( Xs : real list ) =
  case Xs of nil => 0.0
  | X1::Xs1 => X1+real_sum Xs1

fun real_prod( Xs : real list ) =
  case Xs of nil => 1.0
  | X1::Xs1 => X1*real_prod Xs1

fun int_sum( Xs : int list ) =
  case Xs of nil => 0
  | X1::Xs1 => X1+int_sum Xs1


fun combine( [], [] ) = []
  | combine( X::Xs, Y::Ys ) = (X,Y)::combine(Xs,Ys)

fun split [] = ([],[])
  | split( (X1,X2)::Xs ) = case split Xs of (Ys,Zs) => (X1::Ys,X2::Zs)

val zip = combine
val unzip = split

fun zip3( [], [], [] ) = []
  | zip3( X::Xs, Y::Ys, Z::Zs ) = (X,Y,Z)::zip3(Xs,Ys,Zs)

fun unzip3 [] = ([],[],[])
  | unzip3( (X,Y,Z) :: As ) = 
      case unzip3 As of (Xs,Ys,Zs ) =>
        ( X::Xs, Y::Ys, Z::Zs )
    


fun indexize( Xs : 'a list, Start : int ) =
  combine( Xs, fromto( Start, Start + length Xs - 1 ) )

fun assoc_opt( X : ''a, Xs : (''a * 'b ) list ) : 'b option =
  case Xs of
    nil => NONE
  | (X1,Y1)::Xs1 => if X1=X then SOME Y1 else assoc_opt(X,Xs1)

fun assoc_opt'(eq : 'a*'a->bool, X : 'a, Xs : ('a * 'b ) list ) : 'b option =
  case Xs of
    nil => NONE
  | (X1,Y1)::Xs1 => if eq(X1,X) then SOME Y1 else assoc_opt'(eq,X,Xs1)

fun assoc(X,Xs) = case assoc_opt(X,Xs) of SOME Y => Y

fun foldright( A, f, Xs ) =
  case Xs of nil => A
  | X1::Xs1 => f( X1, foldright(A,f,Xs1) )

fun flat_map( f, Xs ) =
  case Xs of nil => nil | X1::Xs1 => f(X1)@flat_map(f,Xs1)

fun flatten nil = nil
  | flatten (Xs::Xss) = Xs@flatten Xss

fun map( f, Xs ) =
  case Xs of nil => nil | X1::Xs1 => f(X1)::map(f,Xs1)

fun array_to_list( Xs : 'a Array.array ) : 'a list =
  map( fn I => Array.sub( Xs, I ), fromto( 0, Array.length Xs - 1 ) )

fun mapp( f, Xss ) = map( fn Xs => map( f, Xs ), Xss )

fun arrayMap( f, A ) = 
  Array.fromList( map( f, array_to_list A ) )

fun loop( f, Xs ) =
  case Xs of nil => () | X1::Xs1 => ( f X1; loop(f,Xs1) )

fun while_list( continue : unit -> bool, Xs, f ) : unit =
  case Xs of
    nil => ()
  | X1::Xs1 => 
      if continue() then
        ( f(X1); while_list(continue,Xs1,f) )
      else
        ()

fun filter(p,Xs) =
  case Xs of
    nil => nil
  | X1::Xs1 => 
      if p X1 then
        X1 :: filter( p, Xs1 )
      else
        filter( p, Xs1 )

fun pfilter( p, Xs ) =
  case Xs of
    nil => ( nil, nil )
  | X1::Xs1 => 
  case pfilter( p, Xs1 ) of ( Ys, Zs ) =>
  if p X1 then
    ( X1::Ys, Zs )
  else
    ( Ys, X1::Zs )

fun forall(p,Xs) = null( filter( fn X => not(p(X)), Xs ) )
fun exists(p,Xs) = 
  case Xs of nil => false
  | X1::Xs1 => p X1 orelse exists(p,Xs1)

fun cart_prod(Xs,Ys) = flat_map( fn X => map(fn Y=>(X,Y),Ys), Xs )

fun powset([],Base) = [Base]
  | powset(X::Xs,Base) = powset(Xs,Base) @ powset(Xs,X::Base)


exception Choose
fun choose( Xs : 'a list, K : int ) : 'a list list =
  if K > length Xs orelse K<0 then
    raise Choose
  else if K=0 then
    [[]]
  else if K=length Xs then
    [Xs]
  else case Xs of X1::Xs1 =>
    map( fn Ys => X1::Ys, choose(Xs1,K-1) ) @ choose(Xs1,K)

fun mk_eq_classes( eq : 'a * 'a -> bool, Xs : 'a list ) : 'a list list =
let
  fun g [] = []
    | g( X :: Xs ) =
        case pfilter( fn Y :: _ => eq( X, Y ), g Xs ) of
          ( [], Xss ) => [X] :: Xss
        | ( [Ys], Xss ) => ( X :: Ys ) :: Xss
in
  g Xs
end






fun count(X,Xs) =
  case Xs of nil => 0 | X1::Xs1 => 
    if X=X1 then 1+count(X,Xs1) else count(X,Xs1)

fun member(X,Xs) = 
  case Xs of nil => false | X1::Xs1 => X=X1 orelse member(X,Xs1)

fun is_subset(Xs,Ys) = forall( fn X => member(X,Ys), Xs )

fun member'(eq,X,Xs) = 
  case Xs of nil => false | X1::Xs1 => eq(X,X1) orelse member'(eq,X,Xs1)

fun is_set(Xs) =
  case Xs of nil => true | X1::Xs1 => not(member(X1,Xs1)) andalso is_set(Xs1)

fun is_set'(eq,Xs) =
  case Xs of 
    nil => true 
  | X1::Xs1 => not(member'(eq,X1,Xs1)) andalso is_set'(eq,Xs1)

fun make_set(Xs) =
  case Xs of nil => nil 
  | X1::Xs1 => if member(X1,Xs1) then make_set(Xs1) else X1::make_set(Xs1)

fun make_set'(eq,Xs) =
  case Xs of nil => nil 
  | X1::Xs1 => 
      if member'(eq,X1,Xs1) then make_set'(eq,Xs1) else X1::make_set'(eq,Xs1)

fun fast_make_set( less, Xs ) =
  let fun ms(Xs) =
    case Xs of 
      nil => Xs
    | X::nil => Xs
    | X1::(Xs1 as X2::Xs2) => if less(X1,X2) then X1::ms(Xs1) else ms Xs1
  in
    ms(Lib.sort less Xs )
  end


fun duplicates(Xs) =
case Xs of
  nil => nil
| X1::Xs1 => if member(X1,Xs1) then X1::duplicates(Xs1) else duplicates(Xs1)

fun list_eq( eq : 'a * 'a -> bool, Xs : 'a list, Ys : 'a list ) =
  let 
    fun g( [], [] ) = true
      | g( [], _ ) = false
      | g( _, [] ) = false
      | g( X :: Xs, Y :: Ys ) = eq( X, Y ) andalso g( Xs, Ys )
  in
    g( Xs, Ys )
  end

fun option_eq( eq : 'a * 'a -> bool, X : 'a option, Y : 'a option ) : bool =
  case X of
    NONE => ( case Y of NONE => true | SOME _ => false )
  | SOME X =>
  case Y of
    NONE => false
  | SOME Y => eq( X, Y )

fun stable_sort (less : 'a * 'a -> bool) Xs =
  map(#1, sort (fn((X1,N1),(X2,N2)) => 
    less(X1,X2) orelse not(less(X2,X1)) andalso N1<N2)
                (combine(Xs,fromto(1,length Xs))))

fun delete_one(X,Xs) =
  case Xs of
    nil => nil
  | X1::Xs1 => if X=X1 then Xs1 else X1::delete_one(X,Xs1)

fun min( less, Xs ) = 
  case Xs of
    X1::nil => X1
  | X1::Xs1 => let val M = min(less,Xs1) in
      if less(M,X1) then M else X1
      end

fun max( less, Xs ) =
  case Xs of
    X1::nil => X1
  | X1::X2::Xs2 => if less(X1,X2) then max(less,X2::Xs2) else max(less,X1::Xs2)

fun is_subsequence( [], _ ) = true
  | is_subsequence( X1 :: Xs1,  [] ) = false
  | is_subsequence(  Xs as X1 :: Xs1, Y1 :: Ys1 ) = 
      if X1 = Y1 then
        is_subsequence( Xs1, Ys1 )
      else
        is_subsequence( Xs, Ys1 )



local

fun lcp( eq, So_far, Xss ) =
  if exists( null, Xss ) then
    rev So_far
  else 
  case Xss of ( X :: _ ) :: Xss1 =>
  if forall( fn Y::_ => eq( X, Y ), Xss1 ) then
    lcp( eq, X :: So_far, map( tl, Xss ) )
  else
    rev So_far

in 

fun longest_common_prefix'( eq : 'a * 'a -> bool, 
      Xss : 'a list list ) : 'a list =
  case Xss of
    [] => []
  | [ Xs ] => Xs
  | _::_::_ => lcp( eq, [], Xss )

end (* local *)
  
fun longest_common_prefix( Xss : ''a list list ) : ''a list =
  longest_common_prefix'( op=,  Xss )




(*

See lcs.sml instead

local
  open Array2
in

fun lcs(eq, Xs, Ys ) : int =
  let
    val Memomatrix : int option array = 
      array( length Xs, length Ys, NONE )
    fun lcs'( _, _, [], _ ) = 0
      | lcs'( _, _, _, [] ) = 0
      | lcs'( I, J,  Xs as X1::Xs1, Ys as Y1::Ys1 ) =
      case sub( Memomatrix, I, J ) of
        SOME N => N
      | NONE =>
      let val N =
            if eq(X1,Y1) then
              1 + lcs'(I+1,J+1,Xs1,Ys1)
            else
              max2( op<, lcs'(I+1,J,Xs1,Ys),  lcs'(I,J+1,Xs,Ys1) )
      in
        update(Memomatrix,I,J,SOME N);
        N
      end
  in
    lcs'(0,0,Xs,Ys)
  end

end (* local *)

*)

(*
fun test1() = lcs(op=, [1,2,3,2,4,1,2], [2,4,3,1,2,1] )

fun test2() = timeit( fn () => lcs( op=,
  [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],
  [1,7,3,4,5,6,7,8,5,10,11,12,13,14,15,16,11,18,19,20,21,22,23,21,25]) )
*)

fun difference(Xs,Ys) =
  case Xs of nil => nil
  | X1::Xs1 =>
      if member(X1,Ys) then difference(Xs1,Ys) else X1::difference(Xs1,Ys)

fun difference'(eq,Xs,Ys) =
  case Xs of nil => nil
  | X1::Xs1 =>
      if member'(eq,X1,Ys) then difference'(eq,Xs1,Ys) else 
        X1::difference'(eq,Xs1,Ys)

fun is_sorted( less, Xs ) =
  case Xs of
    [] => true
  | [X] => true
  | X1::( Xs1 as X2::Xs2) => 
      not(less(X2,X1)) andalso is_sorted(less,Xs1)

fun cmp_is_sorted( cmp, Xs ) =
  is_sorted( fn( X, Y ) => case cmp( X, Y ) of LESS => true | _ => false, Xs )

exception Sorted_difference
fun sorted_difference( less, Xs, Ys ) =
  if not(is_sorted(less,Xs)) orelse not(is_sorted(less,Ys)) then
    raise Sorted_difference
  else
  case Xs of nil => nil
  | X1::Xs1 => case Ys of nil => Xs
  | Y1::Ys1 =>
      if less(X1,Y1) then
        X1::sorted_difference(less,Xs1,Ys)
      else if less(Y1,X1) then
        sorted_difference(less,Xs,Ys1)
      else
        sorted_difference(less,Xs1,Ys)

fun fast_difference( less, Xs, Ys ) =
  sorted_difference( less, Lib.sort less Xs, Lib.sort less Ys )



fun intersection(Xs,Ys) =
  case Xs of nil => nil
  | X1::Xs1 => 
      if member(X1,Ys) then X1::intersection(Xs1,Ys) else intersection(Xs1,Ys)

exception Sorted_intersection
fun sorted_intersection( less, Xs, Ys ) =
  if not(is_sorted(less,Xs)) orelse not(is_sorted(less,Ys)) then
    raise Sorted_intersection
  else
  case Xs of nil => nil
  | X1::Xs1 => case Ys of nil => nil
  | Y1::Ys1 =>
      if less(X1,Y1) then
        sorted_intersection(less,Xs1,Ys)
      else if less(Y1,X1) then
        sorted_intersection(less,Xs,Ys1)
      else
        X1::sorted_intersection(less,Xs1,Ys1)



fun fast_intersection( less, Xs, Ys ) =
  sorted_intersection( less, Lib.sort less Xs, Lib.sort less Ys )


fun sorted_intersections( less : 'a*'a->bool, Xss : 'a list list ) =
  case Xss of
    [] => []
  | _ =>
  let fun g Xss =
    case Xss of
      [Xs] => Xs
    | Xs::Xss => sorted_intersection( less, Xs, g Xss )
  in
    g Xss
  end



fun list_insert(less,X,Xs) =
  case Xs of
    nil => X::nil
  | X1::Xs1 => if less(X,X1) then X::X1::Xs1 else X1::list_insert(less,X,Xs1)

fun list_out(out : outstream, print : outstream * 'a -> unit, Xs : 'a list ) =
  let fun p S = output(out,S)
  in
  p "[ "; (
  case Xs of
    nil => ()
  | _::_ => (
    loop( fn X => ( print(out,X); p", " ), lt Xs );
    print( out, dh Xs ) )
  );
  p " ]"
  end

fun real_list_out(out : outstream, Xs : real list ) =
  list_out( out, fn(Stream,X) => output(Stream,Real.toString X), Xs)

fun int_list_out(out : outstream, Xs : int list ) =
  list_out( out, fn(Stream,X) => output(Stream,Int.toString X), Xs)

fun bool_list_out(out : outstream, Xs : bool list ) =
  list_out( out, fn(Stream,X) => output(Stream,Bool.toString X), Xs)

fun print_list(print : 'a -> unit, Xs : 'a list ) =
  list_out(!std_out, fn(Stream,X) => print X, Xs)

fun print_int_list( Xs : int list ) =
  print_list( fn X => output(!std_out,Int.toString X), Xs )

fun print_word32_list( Xs : Word32.word list ) =
  print_list( fn X => output(!std_out,Word32.toString X), Xs )

fun print_real_list( Xs : real list ) =
  print_list( fn X => output(!std_out,Real.toString X), Xs )

fun print_bool_list( Xs : bool list ) =
  print_list( fn X => output(!std_out,Bool.toString X), Xs )

fun print_bool_list_list( Xss : bool list list ) =
  print_list(fn Xs => (print_bool_list Xs; output(!std_out,"\n")), Xss)



fun print_int_opt NONE = p "NONE "
  | print_int_opt( SOME X ) = p( "SOME " ^ Int.toString X ^ " " )

fun print_real_opt NONE = p "NONE "
  | print_real_opt( SOME X ) = p( "SOME " ^ Real.toString X ^ " " )


(* Too slow: *)

fun scramble( Xs : 'a list ) : 'a list =
  map(#1,
    sort (fn ((_,X),(_,Y)) => X<Y)
      (combine(Xs,map(fn _ => randReal(),fromto(1,length Xs)))))

exception rand_choice_exn
fun rand_choice( Xs : 'a list ) : 'a =
  case Xs of [] => raise rand_choice_exn | _ =>
  nth( Xs, randRange( 0, length Xs -1 ) )  


exception rand_choices_exn
fun rand_choices( N : int, Xs : 'a list ) : 'a list =
  let
    val L = length Xs
    val () = if L < N then raise rand_choices_exn else ()
    val Is = map( fn _ => randRange( 0, L-1 ), fromto( 1, N ) )
  in
    map( fn I => nth( Xs, I ), Is )
  end



(* List hashing function: *)

local

val N_rands = 10000

val Rand = Random.rand( 8362696, ~279264173 )

val next = fn() => Random.randReal Rand

val Rand_vector : real vector =
  Vector.tabulate( N_rands, fn I => next() - 0.5 )

fun next_random Rand_vector_index = (
  Rand_vector_index := !Rand_vector_index + 1;
  Vector.sub( Rand_vector, !Rand_vector_index )
  )
  handle Subscript => (
    Rand_vector_index := ~1;
    next_random Rand_vector_index
    )

fun hash( Hash_val : real ref, Rand_vector_index : int ref, X : real ) : unit =
  Hash_val := 0.45243233 + X * next_random Rand_vector_index + !Hash_val
    
in (* local *)

fun list_hash( f : 'a -> real, Xs : 'a list ) : real = 
  let
    val Hash_val = ref 0.0   
    val Rand_vector_index = ref ~1
  in
    loop( fn X =>  hash( Hash_val, Rand_vector_index, f X ),  Xs );
    !Hash_val + 0.325454325
  end

end (* local *)


fun vector_to_list( V : 'a Vector.vector ) : 'a list =
  map( fn I => Vector.sub( V, I ), fromto( 0, Vector.length V - 1 ) )

fun array_to_list( V : 'a Array.array ) : 'a list =
  map( fn I => Array.sub( V, I ), fromto( 0, Array.length V - 1 ) )



fun list_pack( elem_pack : 'a -> string, Xs : 'a list ) : string =
  pack( map( elem_pack, Xs ) )

fun list_unpack( elem_unpack : string -> 'a, S : string ) : 'a list =
  map( elem_unpack, unpack S )
  

fun option_pack( elem_pack : 'a -> string, Xs : 'a option ) : string =
  case Xs of NONE => pack []  | SOME X => pack[ elem_pack X ]

fun option_unpack( elem_unpack : string -> 'a, S : string ) : 'a option =
   case unpack S of [] => NONE | [ X ] => SOME( elem_unpack X ) 


exception N_choose_k_exn
fun n_choose_k( N : int, K : int ) : real =
  case N>=0 andalso K>=0 of true =>
  if N < K then
    0.0
  else if N-K < K then
    n_choose_k( N, N-K )
  else
    let
      val X = real_prod( map( real, fromto( N-K+1, N ) ) )
      val () = if X > 1.0e300 then raise N_choose_k_exn else ()
    in
      X / real_factorial( real K )
    end

end (* List1 *)


functor Hash_make_set_functor( H : MONO_HASH_TABLE ) : 
sig
   val hash_make_set : H.Key.hash_key list -> H.Key.hash_key list
end =
struct

exception Hash_make_set_exn

fun hash_make_set Xs =
  let
    val Table : unit H.hash_table = 
      H.mkTable( length Xs, Hash_make_set_exn )
  in
    List1.filter( fn X => 
      case H.find Table X of
        NONE => ( H.insert Table (X,()); true )
      | SOME _ => false,
      Xs )
  end

end 

  
signature HASH_SET =
sig
  structure Key : HASH_KEY
  type item = Key.hash_key
  structure H : MONO_HASH_TABLE
  type set = unit H.hash_table
  val empty : unit -> set
  val insert : item * set -> unit
  val delete : item * set -> unit
  val list_to_set : item list -> set
  val set_to_list : set -> item list 
  val member : item * set -> bool
  val loop : (item -> 'a) * set -> unit
  val singleton : item -> set 
  val union : set * set -> set
  val intersection : set * set -> set
  val difference : set * set -> set
  val is_subset : set * set -> bool
  val union_map : ('a -> set) * 'a list -> set
end 

functor HashSet( Key : HASH_KEY ) : HASH_SET =
struct
structure Key = Key

type item = Key.hash_key

structure H = HashTableFn( Key )

type set = unit H.hash_table

exception HashSet_exn

fun empty() : set = H.mkTable( 10, HashSet_exn )

fun insert( X : item, Xs : set ) :  unit = H.insert Xs ( X, () )

fun delete( X : item, Xs : set ) :  unit = H.remove Xs X

fun list_to_set( Xs : item list ) : set =
  let
    val Ys = H.mkTable( length Xs, HashSet_exn )
  in
    List1.loop( fn X => insert( X, Ys ), Xs );
    Ys
  end   

fun set_to_list( Xs : set ) : item list = List1.map( #1, H.listItemsi Xs )

fun member( X : item, Xs : set ) : bool =
  case H.find Xs X of NONE => false | SOME _ => true

fun loop( f, Xs ) = H.appi ( fn( X, () ) => (f X; ()) ) Xs
   


fun singleton( X : item ) :  set =
  case empty() of Xs => ( insert( X, Xs );  Xs )

fun union( Xs : set, Ys : set ) : set =
  let
    val Zs = H.copy Xs
  in
    loop( fn Y => insert( Y, Zs ), Ys );
    Zs
  end
    
  
fun intersection( Xs : set, Ys : set ) : set =
  let
    val Zs = empty()
  in
    loop( fn X => if member( X, Ys ) then insert( X, Zs ) else (), Xs );
    Zs
  end
      
  
fun difference( Xs : set, Ys : set ) : set =
  let
    val Zs = empty()
  in
    loop( fn X => if member( X, Ys ) then () else insert( X, Zs ), Xs );
    Zs
  end
      
  
fun is_subset( Xs : set, Ys : set ) : bool =
  let
    val Is = ref true
  in
    loop( fn X => if member( X, Ys ) then () else Is := false, Xs );
    !Is
  end
      

fun union_map( f : 'a -> set, Xs : 'a list ) =
  case Xs of
    [] => empty()
  | X :: Xs => union( f X, union_map( f, Xs ) )


end (* functor HashSet *)



structure Int_set = HashSet( Lib.Int_hash_key )
structure Real_set = HashSet( Lib.Real_hash_key )
structure String_set = HashSet( Lib.String_hash_key )


structure Tree =
struct
open List1

datatype 'a tree = tree_cons of 'a * 'a tree list

datatype 'a bin_tree = bt_nil | bt_cons of 'a * 'a bin_tree * 'a bin_tree

fun bt_map( f : 'a -> 'b, Xs : 'a bin_tree ) : 'b bin_tree =
  case Xs of
    bt_nil => bt_nil
  | bt_cons(RoXs,LeXs,RiXs) => 
      bt_cons( f RoXs, bt_map(f,LeXs), bt_map(f,RiXs) )

fun is_leaf( tree_cons(_,Subs) ) = null(Subs);

fun root( tree_cons(Root,_) ) = Root;
fun subs( tree_cons(_,Subs) ) = Subs;

fun preorder( tree_cons(X,Xs) : 'a tree ) : 'a list =
  X::flat_map(preorder,Xs)


fun leaves( tree_cons(X,Xs) : 'a tree ) : 'a list =
  case Xs of
    nil => X::nil
  | _ => flat_map(leaves,Xs)

fun positions( tree_cons(Root,Subs) : 'a tree ) : int list list =
  []::flat_map( fn (Order_no,Sub_pos_list) =>
                  map( fn Sub_pos => Order_no::Sub_pos, Sub_pos_list ),
                combine( fromto(0,length(Subs)-1), map(positions,Subs) )
                )

fun pos_to_sub( T as tree_cons(Root,Subs) : 'a tree, Pos : int list )
  : 'a tree =
  case Pos of
    nil => T
  | P::Ps => pos_to_sub(nth(Subs,P),Ps)

fun pos_replace( Old as tree_cons(Root,Subs), Pos : int list, New )
  : 'a tree =
  case Pos of
    nil => New
  | P::Ps =>
    tree_cons(
      Root,
      list_replace( Subs, P, pos_replace(nth(Subs,P),Ps,New) )
      )

fun add_sub_right( T : 'a tree, Pos : int list, Sub : 'a tree)
  : 'a tree =
  let val tree_cons(X,Xs) = pos_to_sub(T,Pos)
  in
    pos_replace( T, Pos, tree_cons(X,snoc(Xs,Sub)) )
  end

end (* structure Tree *)
