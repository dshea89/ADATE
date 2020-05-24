(*
  File: mpi_interface.sml.
  Created : 2000-02-14
  Modified: 2000-02-14
*)



structure MPI_interface  :
sig

val init : unit -> unit
val finalize : unit -> unit
(* val is_client : unit -> bool *)
val get_comm_rank : unit -> int
val get_comm_size : unit -> int

val send : string * int * int -> unit

type status = 
  { info : string, source : int, tag : int, error : int }

val MPI_ANY_SOURCE : int

val receive : int * int -> status

end =
struct
open Lib List1 

structure CI = CCalls(structure CCInfo = GCCInfoX86Linux);
open CI


structure CU = CUtil(structure C = CI);
open CU

val MPI_comm_rank  = ref Max_int
val MPI_comm_size = ref Max_int
val MPI_ANY_SOURCE : int =
  Word32.toIntX( case mpi_any_source[] of Cint X => X )

val Is_client = ref false
val Is_client = ref false
val Initialized = ref false
exception MPI_not_initialized_exn

fun is_client() = 
  if not( !Initialized ) then raise MPI_not_initialized_exn else !Is_client
fun get_comm_rank() = 
  if not( !Initialized ) then raise MPI_not_initialized_exn else !MPI_comm_rank
fun get_comm_size() = 
  if not( !Initialized ) then raise MPI_not_initialized_exn else !MPI_comm_size

fun init() = 
let
  val () = prepare_timers_for_export()
  val () = Is_client := C_interface.exportML "/home/ansatte/rolando/mpi_client_image";
  val () = recover_timers_from_export()
  val Argv : string list = 
    CommandLine.name() :: CommandLine.arguments()
  val Argc = length Argv
    val ( Argv_pointer : caddr, _ ) = datumMLtoC
      ( CptrT( CvectorT( Argc, CstringT ) ) )
      ( Cptr( Cvector( Vector.fromList( map( Cstring, Argv ) ) ) ) )
in
  mpi_init[ Cint( Word32.fromInt Argc ), Caddr Argv_pointer ];
  MPI_comm_rank :=  Word32.toIntX( case mpi_comm_rank[] of Cint X => X );
  MPI_comm_size :=  Word32.toIntX( case mpi_comm_size[] of Cint X => X );
  Initialized := true
end

fun finalize() = (
  mpi_finalize[];
  if !Is_client then OS.Process.exit OS.Process.success else ()
  )

val Buffer_addr =
  case c_fun_buffer_addr[] of Cint X => Word32.toInt X


fun put( S : string ) =
  for( 0, String.size S -1, fn I =>
    C_interface.poke( Buffer_addr + I, Char.ord( String.sub( S, I ) ) ) )

fun get( Count : int ) : string =
let
  val Xs : char list =
    map( fn I => 
      Byte.byteToChar( Word8.fromInt( C_interface.peek( Buffer_addr + I ) ) ),
      fromto( 0, Count-1 ) )
in
  String.implode Xs
end

exception Send_exn
fun send( S : string, Dest : int, Tag : int ) : unit = 
  if String.size S > Constants.Buffer_size - 10 then raise Send_exn else (
  put S;
  mpi_send[ 
    Cint( Word32.fromInt( String.size S ) ),
    Cint( Word32.fromInt Dest ),
    Cint( Word32.fromInt Tag )
    ];
  () )

type status = 
  { info : string, source : int, tag : int, error : int }

exception Receive_exn
fun receive( Source : int, Tag : int ) : status =
let
  val Cptr( Cstruct[ Cint Count, Cint Source, Cint Tag, Cint Error ] ) =
    mpi_recv[ Cint( Word32.fromInt Source ), Cint( Word32.fromInt Tag ) ]
  val Count = Word32.toIntX Count
  val () = if Count > Constants.Buffer_size - 10 then raise Receive_exn else ()
  val S = get Count
in {
  info = S,
  source = Word32.toIntX Source,
  tag = Word32.toIntX Tag,
  error = Word32.toIntX Error
  }
end

  


end (* structure MPI_interface *)
