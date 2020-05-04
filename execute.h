/*
  File: execute.h
  Created: 1996-08-12.
  Modified: 2003-09-09.
*/

#ifndef CINTERFACE_EXECUTE

#define CINTERFACE_EXECUTE


extern unsigned Max_time;
extern unsigned Return_value, Saved_esp, Call_count, Status, Q_sym_code, 
  Heap_top_addr, Input_start_addr;



#define Heap_size 64000000
#define Machine_code_size 16000000
#define Act_array_size 4000000
extern unsigned char Machine_code[Machine_code_size];
extern unsigned Act_array[Act_array_size];
extern unsigned Heap[Heap_size];

unsigned c_fun_max_time_addr(void);
unsigned c_fun_return_value_addr(void);
unsigned c_fun_saved_esp_addr(void);
unsigned c_fun_call_count_addr(void);
unsigned c_fun_q_sym_code_addr(void);
unsigned c_fun_status_addr(void);
unsigned c_fun_heap_top_addr(void);
unsigned c_fun_input_start_addr(void);
unsigned c_fun_machine_code_addr(void);
unsigned c_fun_act_array_addr(void);
unsigned c_fun_heap_addr(void);

extern int Execute_status_code, Execute_result, 
  Execute_call_count, Execute_allocation_count, Execute_q_sym_code; 
void c_fun_execute( unsigned Entry_point );
void c_fun_clear_act_array( unsigned First, unsigned Last );

// Code related to floating point operations:

void write_double( unsigned Addr, double X );
double read_double( unsigned Addr );
double doubleword_to_real( unsigned X1, unsigned X2 );

extern unsigned Real_to_doubleword1;
extern unsigned Real_to_doubleword2;
void real_to_doubleword( double Y );

void c_fun_usub( double* Z, double* X );
void c_fun_add( double* Z, double* X, double* Y );
void c_fun_sub( double* Z, double* X, double* Y ) ;
void c_fun_mul( double* Z, double* X, double* Y );
void c_fun_div( double* Z, double* X, double* Y );
int c_fun_equal( double* X, double* Y );
int c_fun_less( double* X, double* Y );
void c_fun_sigmoid( double* Z, double* X );
unsigned c_fun_tmp_addr(void);
unsigned c_fun_add_addr(void);
unsigned c_fun_sub_addr(void);
unsigned c_fun_mul_addr(void);
unsigned c_fun_div_addr(void);
unsigned c_fun_equal_addr(void);
unsigned c_fun_less_addr(void);
unsigned c_fun_sigmoid_addr(void);

// Code to compute xor check sums. 
unsigned c_fun_machine_code_xor( unsigned First, unsigned Last );
unsigned c_fun_heap_xor( unsigned First, unsigned Last );


  
extern double tmp;

/*
void poke( unsigned addr, unsigned char byte );
unsigned peek( unsigned addr );
*/

#endif
