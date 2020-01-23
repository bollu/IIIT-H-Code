#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <vector>
#include <iostream>
#include "mpi.h"
int rnk, nrnk;
#define RNK cout<<"\033[31m["<<rnk<<"/" << nrnk << "]\033[0m"
using namespace std;
using I=long long int;
vector<I> a;

void pr() { RNK; printf("(size:%lu)", a.size()); for(int i = 0; i < a.size(); ++i) printf("%4lld", *(a.data() + i)); printf("\n"); }

int partition(I l, I r) {
  if (r < l) return -1;
}

void quicksort(int l, int r) {
}

int main( int argc, char **argv ) {

  assert(argc == 3);
  /* write your code here */

  /* start up MPI */
  MPI_Init( &argc, &argv );

  MPI_Comm_rank( MPI_COMM_WORLD, &rnk );
  MPI_Comm_size( MPI_COMM_WORLD, &nrnk );


  /*synchronize all processes*/
  MPI_Barrier( MPI_COMM_WORLD );
  double tbeg = MPI_Wtime();

  // our code starts here
  // ====================

  I elements_per_proc; 

  if (rnk == 0) {
    // 1. recieve input if leader
    FILE *f=fopen(argv[1], "r");
    int i; while (fscanf(f, "%d", &i) == 1) { a.push_back(i); };
    fclose(f);
    pr();
    printf("data pointer: %p\n", a.data());

    // compute nelem per proc on rank 0
    elements_per_proc = a.size() / nrnk;
    // share this with everyone else

    assert (a.size() % nrnk == 0 && "number of processors is not divisible by size");
  } 

  MPI_Bcast(&elements_per_proc, 1, MPI_LONG_LONG_INT, 
      /*root=*/0, MPI_COMM_WORLD);

  // share data amongst everyone with scatter
  I *buf = new I[elements_per_proc];
  RNK << "calling scatter...\n" << flush;
  MPI_Scatter(a.data(), elements_per_proc, MPI_LONG_LONG_INT, 
      buf, elements_per_proc, MPI_LONG_LONG_INT, 
      0, MPI_COMM_WORLD);
  RNK << "called scatter...\n" << flush;

  for (int i = 0; i < elements_per_proc; ++i) { RNK << "buf[" << i << "] := " << buf[i] << "\n"; }

  RNK << "calling  gather...\n" << flush;
  // gather all data with gather
  MPI_Gather(buf, elements_per_proc, MPI_LONG_LONG_INT, 
      a.data(), elements_per_proc, MPI_LONG_LONG_INT,
      0, MPI_COMM_WORLD);
  RNK << "GATHERED...\n" << flush;

  if (rnk == 0) {
    FILE *f = fopen(argv[2], "w");
    for(int i = 0; i < a.size(); ++i) { fprintf(f, "%d ", a[i]); }
    fprintf(f, "\n");
    fflush(f);
    fclose(f);
    pr();
  }

  MPI_Barrier( MPI_COMM_WORLD );
  double elapsedTime = MPI_Wtime() - tbeg;
  double maxTime;
  MPI_Reduce( &elapsedTime, &maxTime, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD );
  if ( rnk == 0 ) {
    printf( "Total time (s): %f\n", maxTime );
  }

  /* shut down MPI */
  MPI_Finalize();
  return 0;
}
