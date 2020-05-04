/*
  File: execute.c
  Created: 1996-08-12.
  Modified: 2006-03-10.

2000-04-04: Floating point added.
2003-08-30: Added computation of check sums for heap and machine code
  in order to facilitate trampling detection.
2006-03-10: Added math functions.
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "execute.h"
#include <math.h>

unsigned Max_time = 0;

unsigned Return_value, Saved_esp, Call_count, Status, Q_sym_code, 
  Heap_top_addr, Input_start_addr;

unsigned char Machine_code[Machine_code_size];
unsigned Act_array[Act_array_size];
unsigned Heap[Heap_size];

unsigned c_fun_max_time_addr(void) { return (unsigned)(&Max_time); }

unsigned c_fun_return_value_addr(void) { return (unsigned)(&Return_value); }
unsigned c_fun_saved_esp_addr(void) { return (unsigned)(&Saved_esp); }
unsigned c_fun_call_count_addr(void) { return (unsigned)(&Call_count); }
unsigned c_fun_q_sym_code_addr(void) { return (unsigned)(&Q_sym_code); }
unsigned c_fun_status_addr(void) { return (unsigned)(&Status); }
unsigned c_fun_heap_top_addr(void) { return (unsigned)(&Heap_top_addr); }
unsigned c_fun_input_start_addr(void) { return (unsigned)(&Input_start_addr); }

unsigned c_fun_machine_code_addr(void) { return (unsigned)(Machine_code); }

unsigned c_fun_act_array_addr(void) { return (unsigned)(Act_array); }

unsigned c_fun_heap_addr(void) { return (unsigned)(Heap); }


typedef void (*fun_type)(void);



int Execute_status_code, Execute_result, 
  Execute_call_count, Execute_allocation_count, Execute_q_sym_code; 

void c_fun_execute( unsigned Entry_point ) {
  unsigned Old_heap_top_addr;
  fun_type f;

  f = (fun_type)Entry_point;
  Call_count = -Max_time;
  Old_heap_top_addr = Heap_top_addr;
  f();

  Execute_status_code = Status;
  Execute_result = Return_value;
  Execute_call_count = Max_time + Call_count;
  Execute_allocation_count = (Heap_top_addr - Old_heap_top_addr) / 4;
  Execute_q_sym_code = Q_sym_code;
  return;
  }

void c_fun_clear_act_array( unsigned First, unsigned Last ) {
  unsigned I;
  assert( Last < Act_array_size-10 );

  for( I=First; I<=Last; I++ )
    Act_array[I] = 0;
  }

/* Code related to floating point operations: */

void write_double( unsigned Addr, double X ) {
  *(double*)Addr = X;
  }

double read_double( unsigned Addr ) {
  return *(double*)Addr;
  }

double doubleword_to_real( unsigned X1, unsigned X2 ) {
  double Y;
  *(unsigned*)&Y = X1;
  *( 1 + (unsigned*)&Y ) = X2;
  return Y;
  }

unsigned Real_to_doubleword1;
unsigned Real_to_doubleword2;

void real_to_doubleword( double Y ) {
  Real_to_doubleword1 = *(unsigned*)&Y;
  Real_to_doubleword2 = *( 1 + (unsigned*)&Y );
  return;
  }



/* Code to compute xor check sums. */

/* Computing check sum for a stretch of machine code: */
unsigned c_fun_machine_code_xor( unsigned First, unsigned Last ) {
  unsigned Sum = 0;
  int Shift = 0;
  unsigned I;
  unsigned X;
  assert( First <= Last && Last < Machine_code_size );
  for( I = First; I <= Last; I++ ) {
    X = (unsigned)( Machine_code[I] );
    X = X << Shift;
    switch( Shift ) {
      case 0 : Shift = 8; break;
      case 8 : Shift = 16; break;
      case 16 : Shift = 24; break;
      case 24 : Shift = 0; break;
      default : assert( 0 );
      }
    Sum = Sum ^ X;
    }
  return Sum;
  }
    
unsigned c_fun_heap_xor( unsigned First, unsigned Last ) {
  unsigned Sum = 0;
  unsigned I;
  assert(  First <= Last && Last < Heap_size );
  for( I = First; I <= Last; I++ ) 
    Sum = Sum ^ ( Heap[I] );
  return Sum;
  }
  


/* To allow the mlton compiler to read constants. */

int c_fun_heap_size( void ) { return Heap_size; }
int c_fun_machine_code_size( void ) { return Machine_code_size; }
int c_fun_act_array_size( void ) { return Act_array_size; }

/* Other code for mlton only: */

void c_fun_update_machine_code( int I, unsigned char To ) {
  assert( 0 <= I && I < Machine_code_size );
  Machine_code[I] = To;
  return;
  }

void c_fun_update_heap( int I, unsigned To ) {
  assert( 0 <= I && I < Heap_size );
  Heap[I] = To;
  return;
  }

unsigned c_fun_heap_sub( int I ) {
  assert( 0 <= I && I < Heap_size );
  return Heap[I];
  }

unsigned c_fun_act_array_sub( int I ) {
  assert( 0 <= I && I < Act_array_size );
  return Act_array[I];
  }

void c_fun_set_heap_top_addr( unsigned To ) { Heap_top_addr = To; }
void c_fun_set_input_start_addr( unsigned To ) { Input_start_addr = To; }
void c_fun_set_max_time( unsigned To ) { Max_time = To; }


unsigned get_real_to_doubleword1( void ) { return Real_to_doubleword1; }
unsigned get_real_to_doubleword2( void ) { return Real_to_doubleword2; }

int get_execute_status_code( void ) { return Execute_status_code; }
int get_execute_result( void ) { return Execute_result; }
int get_execute_call_count( void ) { return Execute_call_count; }
int get_execute_allocation_count( void ) { return Execute_allocation_count; }
int get_execute_q_sym_code( void ) { return Execute_q_sym_code; }


/* Functions to be called directly from ADATE generated machine code. */


void c_fun_usub( double* Z, double* X ) { *Z = -(*X); }

void c_fun_add( double* Z, double* X, double* Y ) { *Z = *X + *Y; }

void c_fun_sub( double* Z, double* X, double* Y ) { *Z = *X - *Y; }

void c_fun_mul( double* Z, double* X, double* Y ) { *Z = *X * *Y; }

void c_fun_div( double* Z, double* X, double* Y ) { *Z = *X / *Y; }

int c_fun_equal( double* X, double* Y ) { 
/*
  printf( "\nc_fun_equal: %lf %lf %d %d %d\n", 
    *X, *Y, *X < *Y, *X == *Y, *X > *Y );
  fflush( stdout );
*/
  return !( *X < *Y  || *X > *Y ); 
  }

int c_fun_less( double* X, double* Y ) { return *X < *Y; }

void c_fun_sigmoid( double* Z, double* X ) { 
  *Z = 1.0 / ( 1.0 + exp( -(*X) ) );
  }

unsigned c_fun_add_addr(void) { return (unsigned)(c_fun_add); }
unsigned c_fun_sub_addr(void) { return (unsigned)(c_fun_sub); }
unsigned c_fun_mul_addr(void) { return (unsigned)(c_fun_mul); }
unsigned c_fun_div_addr(void) { return (unsigned)(c_fun_div); }

unsigned c_fun_equal_addr(void) { return (unsigned)(c_fun_equal); }
unsigned c_fun_less_addr(void) { return (unsigned)(c_fun_less); }
unsigned c_fun_sigmoid_addr(void) { return (unsigned)(c_fun_sigmoid); }


void c_fun_realFloor( double* Z, double* X ) { *Z = floor( *X ); }
void c_fun_realCeil( double* Z, double* X ) { *Z = ceil( *X ); }
void c_fun_realTrunc( double* Z, double* X ) { *Z = trunc( *X ); }
void c_fun_realRound( double* Z, double* X ) { *Z = round( *X ); }

int c_fun_quot( int X, int Y ) { return X / Y; }
int c_fun_rem( int X, int Y ) { return X % Y; }

int c_fun_trunc( double* X ) { return (int)(*X); }
void c_fun_fromInt( double* Z, int X ) { *Z = (double)X; }

void c_fun_sqrt( double* Z, double* X ) { *Z = sqrt( *X ); }
void c_fun_sin( double* Z, double* X ) { *Z = sin( *X ); }
void c_fun_cos( double* Z, double* X ) { *Z = cos( *X ); }
void c_fun_tan( double* Z, double* X ) { *Z = tan( *X ); }
void c_fun_asin( double* Z, double* X ) { *Z = asin( *X ); }
void c_fun_acos( double* Z, double* X ) { *Z = acos( *X ); }
void c_fun_atan( double* Z, double* X ) { *Z = atan( *X ); }

void c_fun_atan2( double* Z, double* X, double* Y ) { *Z = atan2( *X, *Y ); }

void c_fun_exp( double* Z, double* X ) { *Z = exp( *X ); }
void c_fun_pow( double* Z, double* X, double* Y ) { *Z = pow( *X, *Y ); }

void c_fun_ln( double* Z, double* X ) { *Z = log( *X ); }
void c_fun_log10( double* Z, double* X ) { *Z = log10( *X ); }
void c_fun_sinh( double* Z, double* X ) { *Z = sinh( *X ); }
void c_fun_cosh( double* Z, double* X ) { *Z = cosh( *X ); }
void c_fun_tanh( double* Z, double* X ) { *Z = tanh( *X ); }


unsigned c_fun_realFloor_addr(void) { return (unsigned)(c_fun_realFloor); }
unsigned c_fun_realCeil_addr(void) { return (unsigned)(c_fun_realCeil); }
unsigned c_fun_realTrunc_addr(void) { return (unsigned)(c_fun_realTrunc); }
unsigned c_fun_realRound_addr(void) { return (unsigned)(c_fun_realRound); }
unsigned c_fun_quot_addr(void) { return (unsigned)(c_fun_quot); }
unsigned c_fun_rem_addr(void) { return (unsigned)(c_fun_rem); }
unsigned c_fun_trunc_addr(void) { return (unsigned)(c_fun_trunc); }
unsigned c_fun_fromInt_addr(void) { return (unsigned)(c_fun_fromInt); }
unsigned c_fun_sqrt_addr(void) { return (unsigned)(c_fun_sqrt); }
unsigned c_fun_sin_addr(void) { return (unsigned)(c_fun_sin); }
unsigned c_fun_cos_addr(void) { return (unsigned)(c_fun_cos); }
unsigned c_fun_tan_addr(void) { return (unsigned)(c_fun_tan); }
unsigned c_fun_asin_addr(void) { return (unsigned)(c_fun_asin); }
unsigned c_fun_acos_addr(void) { return (unsigned)(c_fun_acos); }
unsigned c_fun_atan_addr(void) { return (unsigned)(c_fun_atan); }
unsigned c_fun_atan2_addr(void) { return (unsigned)(c_fun_atan2); }
unsigned c_fun_exp_addr(void) { return (unsigned)(c_fun_exp); }
unsigned c_fun_pow_addr(void) { return (unsigned)(c_fun_pow); }
unsigned c_fun_ln_addr(void) { return (unsigned)(c_fun_ln); }
unsigned c_fun_log10_addr(void) { return (unsigned)(c_fun_log10); }
unsigned c_fun_sinh_addr(void) { return (unsigned)(c_fun_sinh); }
unsigned c_fun_cosh_addr(void) { return (unsigned)(c_fun_cosh); }
unsigned c_fun_tanh_addr(void) { return (unsigned)(c_fun_tanh); }
