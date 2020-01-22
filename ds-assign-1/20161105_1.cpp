/* MPI Program Template */

#include <stdio.h>
#include <string.h>
#include "mpi.h"

int main( int argc, char **argv ) {
  int a[2]; a[3] = -1;
  int rank, numprocs;

  /* start up MPI */
  MPI_Init( &argc, &argv );

  MPI_Comm_rank( MPI_COMM_WORLD, &rank );
  MPI_Comm_size( MPI_COMM_WORLD, &numprocs );

  /*synchronize all processes*/
  MPI_Barrier( MPI_COMM_WORLD );
  double tbeg = MPI_Wtime();

  /* write your code here */


  MPI_Barrier( MPI_COMM_WORLD );
  double elapsedTime = MPI_Wtime() - tbeg;
  double maxTime;
  MPI_Reduce( &elapsedTime, &maxTime, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD );
  if ( rank == 0 ) {
    printf( "Total time (s): %f\n", maxTime );
  }

  /* shut down MPI */
  MPI_Finalize();
  return 0;
}
