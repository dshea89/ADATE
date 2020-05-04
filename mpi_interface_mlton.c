/*
  File: mpi_interface_mlton.c
  Created: 2000-02-14
  Modified: 2000-02-15
*/

#include "/home/ansatte/rolando/ML/ADATE/mpich-1.2.6/include/mpi.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <unistd.h>

static int process_rank, n_processes;
static MPI_Status status;

#define BUFFER_SIZE 4000000
#define MAXARGC 100

static int Argc = -1;
static char** Argv;

void setArgc( int To ) {
  assert( 0 <= To && To < MAXARGC );
  Argc = To;
  Argv = (char**)malloc( sizeof(char*) * ( Argc + 10 ) );
  assert( Argv );
  }

void setArgv( int I, char* Xs, int Length ) {
  int k;
  assert( 0 <= I && I < Argc );
  Argv[ I ] = malloc( Length + 10 );
  assert( Argv[ I ] );
  for( k=0; k<Length; k++ )
    (Argv[I])[k] = Xs[k];
  (Argv[I])[Length] = (char)0;
  }

void mpi_init( void ) { 
  int i;
  printf("\nmpi_init: Argc = %d Argv =\n", Argc );
  for( i=0; i<Argc; i++ )
    printf(":%s:\n", Argv[i] );
  MPI_Init( &Argc, &Argv ); 
  }

int mpi_comm_rank(void)  { 
  MPI_Comm_rank( MPI_COMM_WORLD, &process_rank );
  return process_rank;
  }
  
int mpi_comm_size(void) {
  MPI_Comm_size( MPI_COMM_WORLD, &n_processes );
  return n_processes;
  }

int mpi_any_source(void) { return MPI_ANY_SOURCE; }

static char buffer[BUFFER_SIZE];

void mpi_write_buffer( char* Xs, int Length ) {
  int i;
  assert( 0 <= Length && Length < BUFFER_SIZE );
  for( i = 0; i < Length; i++ ) 
    buffer[i] = Xs[i];
  }

unsigned char mpi_read_buffer( int I ) {
  assert( 0 <= I && I < BUFFER_SIZE );
  return (unsigned char)(buffer[I]);
  }


void mpi_send( int count, int dest, int tag ) {
  int i;
  assert( count < BUFFER_SIZE - 10 );
  MPI_Send( buffer, count, MPI_CHAR, dest, tag, MPI_COMM_WORLD );
  }

static int mpi_count;

void mpi_recv( int source, int tag ) {
  int i;

  MPI_Recv( buffer, BUFFER_SIZE, MPI_CHAR, source, tag, MPI_COMM_WORLD, 
    &status );
  MPI_Get_count( &status, MPI_CHAR, &mpi_count );
  }

int mpi_get_source( void ) { return status.MPI_SOURCE; }
int mpi_get_tag( void ) { return status.MPI_TAG; }
int mpi_get_error( void ) { return status.MPI_ERROR; }
int mpi_get_count( void ) { return mpi_count; }


void mpi_finalize( void ) { MPI_Finalize(); }
