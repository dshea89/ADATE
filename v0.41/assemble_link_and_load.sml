(*
  File: assemble_link_and_load.sml.
  Created: 1996-08-08.
  Modified: 2000-03-02.

Changed 2000-03-01 to allow use of esp in indexed and indirect addressing
which requires a SIB byte to follow the ModR/M byte.
*)

signature ASSEMBLE_LINK_AND_LOAD  =
sig

val assemble_link_and_load :
      Compile.instruction Array.array * int * int * 
      int Ast.Symbol_HashTable.hash_table * Word32.word -> Word32.word 
end (* signature ASSEMBLE_LINK_AND_LOAD *)


structure Assemble_link_and_load : ASSEMBLE_LINK_AND_LOAD =
struct
open Lib List1 Ast Ast_lib Compile

structure H = Symbol_HashTable

val Index_to_addr = Word32_dyn.array( 2, 0w0 )

fun b( S : string ) = Word8.fromLargeWord( bin_string_to_word32 S )

val b10011100 = b "10011100"
val b10010100 = b "10010100"
val b01101000 = b "01101000"
val b00000101 = b "00000101"
val b11111111 = b "11111111"
val b01001100 = b "01001100"
val b11000000 = b "11000000"
val b10000000 = b "10000000"
val b01001000 = b "01001000"
val b01000000 = b "01000000"
val b00001000 = b "00001000"
val b00000000 = b "00000000"
val b01010000 = b "01010000"
val b00110000 = b "00110000"
val b01100000 = b "01100000"
val b01011000 = b "01011000"
val b10001111 = b "10001111"
val b01100001 = b "01100001"
val b11101000 = b "11101000"
val b11000011 = b "11000011"
val b10111000 = b "10111000"
val b11000111 = b "11000111"
val b10001011 = b "10001011"
val b10001001 = b "10001001"
val b00011000 = b "00011000"
val b00001111 = b "00001111"
val b10101111 = b "10101111"
val b11110111 = b "11110111"
val b10000101 = b "10000101"
val b11101001 = b "11101001"
val b10000100 = b "10000100"
val b10001111 = b "10001111"
val b01000100 = b "01000100"
val b10010000 = b "10010000"
val b00000001 = b "00000001"
val b00101001 = b "00101001"
val b00111001 = b "00111001"
val b00110001 = b "00110001"
val b10000001 = b "10000001"
val b00101000 = b "00101000"
val b00111000 = b "00111000"
val b00110000 = b "00110000"
val b00000011 = b "00000011"
val b00101011 = b "00101011"
val b00111011 = b "00111011"
val b00110011 = b "00110011"


val Machine_code = Word8Array.array( 900000, 0w0 )

fun assemble_link_and_load( 
      Assembly_code : instruction Array.array,
      Start_index : int,
      End_index : int,
      Fun_entry_table : int H.hash_table,
      Start_addr : Word32.word ) : Word32.word = 
  let

    fun print_debug_info() = (
      output( !std_err, "\n\nAssembly_code =\n" ^
        Compile.assembly_to_string( Assembly_code, 
          Start_index, End_index ));
      output(!std_err, "\n\nFun_entry_table = \n");
      loop( fn(Sym,Index) => 
        output(!std_err, symbol_to_string Sym ^ "  " ^ 
          Word32.toString( Word32.fromInt Index ) ^ "\n"),
        H.listItemsi Fun_entry_table );
      flush_out( !std_err )
      )

      (* val _ = print_debug_info() *)



    fun fun_entry_table_lookup Sym = H.lookup Fun_entry_table Sym
      handle Ex => (
        output( !std_err, "fun_entry_table_lookup : " ^ 
          symbol_to_string Sym );
        print_debug_info();
        flush_out( !std_err );
        re_raise( Ex, "fun_entry_table_lookup" )
        )
       
    val Patch_list : ( int * int * int * int ) list ref = ref []
    fun loc_to_string( Location : int ) =
      Word32.toString( Word32.+( Start_addr, Word32.fromInt Location) ) ^
      " " ^
      Int.toString(
        Word32.toInt( Word32.-(Start_addr, C_interface.Machine_code_addr)) + 
        Location )
    
    fun put_byte( Location : int, X : Word8.word ) = (
(*
      if !Ast.Debug then
        print( "\nput_byte : " ^ loc_to_string Location ^ " " ^ Word8.toString X )
      else
        ();
*)
      Word8Array.update( Machine_code, Location, X )
      )

    fun put_word( Location : int, X : Word32.word ) : unit = (
(*
        print( "\nput_word : " ^ loc_to_string Location ^ " " ^ Word32.toString X )
*)
      put_byte( Location, Word8.fromLargeWord X );
      put_byte( Location+1, Word8.fromLargeWord(Word32.>>( X, 0w8 ) ) );
      put_byte( Location+2, Word8.fromLargeWord(Word32.>>( X, 0w16 ) ) );
      put_byte( Location+3, Word8.fromLargeWord(Word32.>>( X, 0w24 ) ) )
      )

    fun rel_disp( 
          Target_addr : Word32.word,
          Current_addr : Word32.word,
          Instr_len : int ) : Word32.word = (
(*      C_interface.verify_addr Target_addr; *)
      Word32.-( 
        Target_addr, 
        Word32.+(Current_addr, Word32.fromInt Instr_len) )
      )

    fun put_relative_addr( Location : int, Current : int, 
          Instr_len : int, Assembly_code_addr : int ) : unit =
   (* Current is the index of the assembly instr being processed.
      Assembly_code_addr is the address to be translated.
      Location is where in Machine_code to put it.
   *)
      if Assembly_code_addr < Current then (
(*
        output(!std_err, "\n\nLocation = " ^ Int.toString Location ^
        "\nCurrent -> " ^ 
        Word32.toString(Word32_dyn.sub( Index_to_addr, Current )) ^
        "\nInstr_len = " ^ Int.toString Instr_len ^
        "\nAssembly_code_addr -> " ^
        Word32.toString(Word32_dyn.sub( Index_to_addr, Assembly_code_addr )) ^
        "\n\n");
        flush_out( !std_err );
*)
        put_word( Location, 
          rel_disp( 
            Word32_dyn.sub( Index_to_addr, Assembly_code_addr ),
            Word32_dyn.sub( Index_to_addr, Current ),
            Instr_len ) )
        )
      else
        Patch_list := 
          ( Location, Current, Instr_len, Assembly_code_addr ) :: 
          !Patch_list

    fun patch() = (
      loop( fn( Location, Current, Instr_len, Assembly_code_addr ) =>
        put_word( Location, 
          rel_disp( 
            Word32_dyn.sub( Index_to_addr, Assembly_code_addr ),
            Word32_dyn.sub( Index_to_addr, Current ),
            Instr_len ) ),
        !Patch_list );
      Patch_list := []
      )

    fun mk_address( Machine_code_index : int ) : Word32.word =
      case Word32.+( Start_addr, Word32.fromInt Machine_code_index ) of X =>
      ( (* C_interface.verify_addr X; *) X )

    fun reg_code( X : reg ) : Word8.word =
      case X of
        eax => 0w0
      | ecx => 0w1
      | edx => 0w2
      | ebx => 0w3
      | esp => 0w4
      | ebp => 0w5
      | esi => 0w6
      | edi => 0w7

    local

    fun mod_rm_fields( Arg : operand ) : Word8.word =
      case Arg of
        register X => Word8.orb( b11000000, reg_code X )
      | direct X => b00000101
      | indirect X => reg_code X
      | indexed( X, _ ) => Word8.orb( b10000000, reg_code X )

    fun mod_reg_rm_byte( X : Word8.word, Arg : operand ) : Word8.word =
      Word8.orb( mod_rm_fields Arg, Word8.<<( X, 0w3 ) )


    fun use_sib( indirect esp ) = true
      | use_sib( indexed( esp, _ ) ) = true
      | use_sib _ = false

    in (* local *)

    fun put_mod_rm_sib( I : int, Reg_or_op_code : Word8.word, Arg : operand )
        : int = (
      put_byte( I, mod_reg_rm_byte( Reg_or_op_code, Arg ) );
      if use_sib Arg then (
        put_byte( I+1, 0wx24 );
        2 )
      else
        1 )

    end (* local *)
      

    

    


    fun arg_data( Arg : operand ) : Word32.word =
      case Arg of
        immediate X => X
      | direct X => ((* C_interface.verify_addr X; *) X )
      | indexed( _, X ) => X

    fun dec_inc( (Mnem, Arg1, Arg2 ) : instruction, I : int ) : int =
      case Arg1 of
        register X => (
          put_byte( I, Word8.orb(
            case Mnem of dec => b01001000 | inc' => b01000000,
            reg_code X ) );
          I+1 )
      | _ => (
        put_byte( I, b11111111 );
        let
          val K = put_mod_rm_sib( I+1,
            case Mnem of dec => 0w1 | inc' => 0w0,
            Arg1 )
        in
        put_word( I+1+K, arg_data Arg1 );
        I+5+K
        end )
        


    fun set( (Mnem, Arg1, none ) : instruction, I : int ) : int = (
      put_byte( I, b00001111 );
      put_byte( I+1,
        case Mnem of setl => b10011100 | sete => b10010100);
      let
        val K = put_mod_rm_sib( I+2, 0w0, Arg1 )
      in
      case Arg1 of
        register _ => I+2+K
      | _ => ( put_word( I+2+K, arg_data Arg1 ); I+6+K )
      end
      )

    fun instr_to_code( Instr as (Mnem, Arg1, Arg2) : instruction,
          I : int, Asm_index : int ) : int =
    case Mnem of
      push => (
        case Arg1 of
          register X => (
            put_byte( I, Word8.orb( b01010000, reg_code X ) );
            I+1 )
        | immediate X => (
            put_byte( I, b01101000 );
            put_word( I+1, X );
            I+5 )
        | _ => (
          put_byte( I, b11111111 );
          let
            val K = put_mod_rm_sib( I+1, 0w6, Arg1 )
          in
          case Arg1 of
            indirect _ => I+1+K
          | _ => ( put_word( I+1+K, arg_data Arg1 ); I+5+K )
          end
          ) )
    | pusha => ( put_byte( I, b01100000 ); I+1 )
    | pop => (
        case Arg1 of
          register X => (
            put_byte( I, Word8.orb( b01011000, reg_code X ) );
            I+1 )
        | _ => (
          put_byte( I, b10001111 );
          let
            val K = put_mod_rm_sib( I+1, 0w0, Arg1 )
          in
          case Arg1 of
            indirect _ => I+1+K
          | _ => ( put_word( I+1+K, arg_data Arg1 ); I+5+K )
          end
          )
        )
    | popa => ( put_byte( I, b01100001); I+1 )
    | call => (
          put_byte( I, b11101000 );
          case Arg1 of
            label F => put_relative_addr( I+1, Asm_index, 5, 
                         fun_entry_table_lookup F )
          | immediate Addr => put_word( I+1, 
              rel_disp( Addr, Word32_dyn.sub( Index_to_addr, Asm_index ), 5 ) );
          I+5
        )
    | ret => ( put_byte( I, b11000011 ); I+1 )
    | mov => (
        case Arg2 of
          immediate Y => (
            case Arg1 of
              register X => ( (* Immediate to register *)
                put_byte( I, Word8.orb( b10111000, reg_code X ) );
                put_word( I+1, Y );
                I+5 )
            | _ => ( (* Immediate to memory *)
                put_byte( I, b11000111 );
                let
                  val K = put_mod_rm_sib( I+1, 0w0, Arg1 )
                in
                case Arg1 of
                  indirect _ => ( put_word( I+1+K, Y ); I+5+K )
                | _ => (
                  put_word( I+1+K, arg_data Arg1 );
                  put_word( I+5+K, Y );
                  I+9+K )
                end )
            )
        | register Y => (
            case Arg1 of
              register X => ( (* Register to register *)
                put_byte( I, b10001011 );
                let
                  val K = put_mod_rm_sib( I+1, reg_code X, Arg2 )
                in
                I+1+K 
                end )
            | _ => ( (* Register to memory *)
                put_byte( I, b10001001 );
                let
                  val K = put_mod_rm_sib( I+1, reg_code Y, Arg1 )
                in
                put_word( I+1+K, arg_data Arg1 );
                I+5+K 
                end )
            )
        | _=> (* Memory to register *)
          let
            val register X = Arg1
          in
            put_byte( I, b10001011 );
            let
              val K = put_mod_rm_sib( I+1, reg_code X, Arg2 )
            in
            put_word( I+1+K, arg_data Arg2 );
            I+5+K 
            end
          end
        )
    | neg => (
        put_byte( I, b11110111 );
        let
          val K = put_mod_rm_sib( I+1, 0w3, Arg1 )
        in
        case Arg1 of
          register _ => I+1+K
        | _ => ( put_word( I+1+K, arg_data Arg1 ); I+5+K )
        end
        )
    | mul =>
      let
        val register X = Arg1
      in
        put_byte( I, b00001111 );
        put_byte( I+1, b10101111 );
        let
          val K = put_mod_rm_sib( I+2, reg_code X, Arg2 )
        in
        case Arg2 of
          register _ => I+2+K
        | _ => ( put_word( I+2+K, arg_data Arg2 ); I+6+K )
        end
      end
    | dec => dec_inc( Instr, I )
    | inc' => dec_inc( Instr, I )
    | setl => set( Instr, I )
    | sete => set( Instr, I )
    | test => (
        case Arg2 of
          immediate Y => (
            put_byte( I, b11110111 );
            let
              val K = put_mod_rm_sib( I+1, 0w0, Arg1 )
            in
            case Arg1 of
              register _ => ( put_word( I+1+K, Y ); I+5+K )
            | _ => (
                put_word( I+1+K, arg_data Arg1 );
                put_word( I+5+K, Y );
                I+9+K ) 
            end )
        | _ =>
        let
          val register X = Arg1
        in
          put_byte( I, b10000101 );
          let
            val K = put_mod_rm_sib( I+1, reg_code X, Arg2 )
          in
          case Arg2 of
            register _ => I+1+K
          | _ => ( put_word( I+1+K, arg_data Arg2 ); I+5+K )
          end
        end
        )
    | jmp =>
        let
          val X =
            case Arg1 of
              immediate X => Word32.toInt X
            | label Sym => fun_entry_table_lookup Sym
        in
          put_byte( I, b11101001 );
          put_relative_addr( I+1, Asm_index, 5, X );
          I+5
        end
    | jz =>
        let
          val X =
            case Arg1 of
              immediate X => Word32.toInt X
            | label Sym => fun_entry_table_lookup Sym
         in
           put_byte( I, b00001111 );
           put_byte( I+1, b10000100 );
           put_relative_addr( I+2, Asm_index, 6, X );
           I+6
         end
    | jg =>
        let
          val X =
            case Arg1 of
              immediate X => Word32.toInt X
            | label Sym => fun_entry_table_lookup Sym
         in
           put_byte( I, b00001111 );
           put_byte( I+1, b10001111 );
           put_relative_addr( I+2, Asm_index, 6, X );
           I+6
         end
    | cmovle => (* Register to register *)
        let
          val register X = Arg1
          val register _ = Arg2
        in
          put_byte( I, b00001111 );
          put_byte( I+1, b01001100 );
          let
            val K = put_mod_rm_sib( I+2, reg_code X, Arg2 )
          in
          I+2+K
          end
        end
    | cmove => 
        let
          val register X = Arg1
          val register _ = Arg2
        in
          put_byte( I, b00001111 );
          put_byte( I+1, b01000100 );
          let
            val K = put_mod_rm_sib( I+2, reg_code X, Arg2 )
          in
          I+2+K
          end
        end
    | nop => ( put_byte( I, b10010000 ); I+1 )
    | align => 
        let
          val immediate N = Arg1
          open Word32
          fun g I =
            if (Start_addr + I) mod N = 0w0 then
              I
            else (
              put_byte( Word32.toInt I, b10010000 );
              g( I + 0w1  )
              )
        in
          Word32.toInt( g( fromInt I ) )
        end
    | _ => (* add, sub, cmp or xor *)
    case Arg2 of
      register Y => (
        put_byte( I, case Mnem of
            add => b00000001 | sub => b00101001 | cmp => b00111001
          | xor => b00110001 );
        let
          val K = put_mod_rm_sib( I+1, reg_code Y, Arg1 )
        in
        case Arg1 of
          register _ => I+1+K
        | _ => ( put_word( I+1+K, arg_data Arg1 ); I+5+K )
        end
        )
    | immediate Y => (
        put_byte( I, b10000001 );
        let
          val K = put_mod_rm_sib( I+1,
            case Mnem of add => 0w0 | sub => 0w5 | cmp => 0w7 | xor => 0w6,
            Arg1 )
        in
        case Arg1 of
          register _ => ( put_word( I+1+K, Y ); I+5+K )
        | indirect _ => ( put_word( I+1+K, Y ); I+5+K )
        | _ => (
            put_word( I+1+K, arg_data Arg1 )
            handle Ex => (
              output(!std_err, "\nASM 50\n");
              flush_out( !std_err );
              raise Ex
              );
            put_word( I+5+K, Y );
            I+9+K )
        end
        )
    | _ => (* Memory to register *)
        let
          val register X = Arg1
        in
          put_byte(I, case Mnem of
              add => b00000011 | sub => b00101011 | cmp => b00111011
            | xor => b00110011 );
          let
            val K = put_mod_rm_sib( I+1, reg_code X, Arg2 )
          in
          put_word( I+1+K, arg_data Arg2 );
          I+5+K
          end
        end

    fun assemble( Assembly_code_index : int, Machine_code_index : int ) =
      if Assembly_code_index > End_index then
        Machine_code_index
      else 
        let
          val Instr as (Mnem,_,_) =
            Array.sub( Assembly_code, Assembly_code_index )
          val _ = 
            if Mnem = align then
              ()
            else
              Word32_dyn.update( Index_to_addr, Assembly_code_index, 
                mk_address( Machine_code_index ))
          val Next_m_index = 
            instr_to_code( Instr, Machine_code_index, Assembly_code_index )
        in
          if Mnem = align then
            Word32_dyn.update( Index_to_addr, Assembly_code_index, 
              mk_address( Next_m_index ))
          else
            ();
          assemble( Assembly_code_index + 1, Next_m_index )
        end
    val Next_free_index = assemble( Start_index, 0 )
    val _ = patch()

    exception Put_code
    fun put_code Upper =
        let
          fun check X =
            case Word32.+( Start_addr, Word32.fromInt X ) of Addr =>
            if Word32.<( Addr, C_interface.Machine_code_addr ) orelse
              Word32.<( Word32.+( C_interface.Machine_code_addr, 0w900000 ),
                        Addr ) 
            then
             raise Put_code
            else
              ()
          fun put_code' Upper =
            if Upper < 0 then
              ()
            else (
              C_interface.poke( Word32.toInt Start_addr + Upper,
                Word8.toInt(Word8Array.sub( Machine_code, Upper ) ) );
              put_code'( Upper - 1 ) )
        in
          check 0;
          check Upper;
          put_code' Upper
        end
(*
    val Machine_code_vector = Vector.tabulate(
      Next_free_index,
      fn I => Word8Array.sub(Machine_code,I) )
*)
  in
    put_code( Next_free_index - 1 );
(*    
    C_interface.copy_code( Machine_code_vector, Start_addr );
*)
    Word32.+( Start_addr, 
      Word32.fromInt( Next_free_index ) )
  end (* fun assemble_link_and_load *)
handle Ex => (
  output(!std_err, "\nassemble_link_and_load :\n" );
  flush_out( !std_err );
  re_raise( Ex, "assemble_link_and_load" )
  )
end (* structure Assemble_link_and_load *)
