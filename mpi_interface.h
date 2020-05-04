/*
  File: mpi_interface.h
  Created: 2000-02-15.
  Modified: 2003-09-09.
*/

#ifndef MPI_INTERFACE

#define MPI_INTERFACE

struct mpi_status {
  int count;
  int MPI_SOURCE;
  int MPI_TAG;
  int MPI_ERROR;
  };

void mpi_init( int argc, char** argv );
int mpi_comm_rank(void);
int mpi_comm_size(void);
int mpi_any_source(void);


#define BUFFER_SIZE 4000000
extern char buffer[BUFFER_SIZE];

unsigned c_fun_buffer_addr(void);
void mpi_send( int count, int dest, int tag );
struct mpi_status* mpi_recv( int source, int tag );
void mpi_finalize( void );

#endif
