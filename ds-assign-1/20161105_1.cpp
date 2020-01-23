#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <vector>
#include <iostream>
#include "mpi.h"
#define RNK cout<<"\033[31m["<<rnk<<"/" << nrnk << "]\033[0m" << "{" << __LINE__ << "} "
using namespace std;
using I=long long int;
int rnk, nrnk;
static const I NODATA = -42;

void pr(I *a, I l, I r) { RNK; 
  cout<<"(size:"<<r-l+1<<")";
  for(int i = l; i <= r; ++i) cout <<a[i] <<" ";
  cout<<"\n";
}

int log2floor(int n) { if (n <= 1) return 0; return 1 + log2floor(n/2); }

I partition(I *a, I l, I r) {
  assert(l <= r);
  assert(l >= 0);
  const I part = a[r];
  I ltix = l-1; I geix = r;

  while(ltix+1 < geix && geix-1 > ltix) {
    // invariant
    assert(a[geix] >= part); if(ltix>=l) { assert(a[ltix] < part); }

    if (a[ltix+1] >= part) {
      I t=a[ltix+1]; a[ltix+1] = a[geix-1]; a[geix-1]=t;
      geix--;
    } else { ltix++; }
  }
  assert(geix-1 == ltix);
  a[r] = a[geix]; a[geix] = part;
  return geix;
}

void qs_serial(I *a, I l, I r) {
  RNK << "[" << l << "," << r << "]\n";
  assert(l >= 0);
  assert(l <= r);
  I mid = partition(a, l, r);
  assert(l <= mid);
  assert(mid <= r);

  if (l <= mid - 1) qs_serial(a, l, mid-1);
  if (mid+1 <= r) qs_serial(a, mid+1, r);
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

  // left and right sizes
  static const int LIX=0; static const int RIX=1;
  I *a = nullptr;
  int r = 0;
 
  if (rnk == 0) {
    // 1. recieve input if leader
    FILE *f=fopen(argv[1], "r");
    vector<I> avec;
    int i; while (fscanf(f, "%d", &i) == 1) { avec.push_back(i); };
    fclose(f);

    a = new I[avec.size()];
    for(int i = 0; i < avec.size(); ++i) { a[i] = avec[i]; }
    r = avec.size() - 1;
  }



  // use [1..] numbering for binary tree.
  const int rnkbin = rnk+1;
  const int rnkbinl = rnkbin*2, rnkbinr = rnkbin*2+1;
  const int rnkbinp = rnkbin == 1 ? 1 : rnkbin/2;

  const int rnkl=rnkbinl>nrnk? -1 : rnkbinl-1;
  const int rnkr=rnkbinr>nrnk ? -1 : rnkbinr-1;
  const int rnkp = rnkbin == 1 ? -1 : rnkbinp-1;


  // recieve length of data.
  if (rnk != 0) {
    MPI_Recv(&r, 1, MPI_LONG_LONG_INT, rnkp, 0, 
        MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }

  RNK << rnk << "->" << "P:"<<(rnk == 0 ? -1:rnkp) 
    << " |LC:" << rnkl << " |RC: " << rnkr << "|r: " << r << "\n";

  // if there's some data to recieve
  if (r >=  0) {
    RNK << "r(" << r << ") >= 0\n";

    // if we are not the parent node, recieve
    if (rnk != 0) {
      a = new I[r+1];
      RNK << "waiting for r\n";
      MPI_Recv(a, r+1, MPI_LONG_LONG_INT, rnkp, 0, 
          MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      pr(a, 0, r);
    }

    const I mid = partition(a, 0, r);
    const I Rr = r - (mid+1);
    const I Rl = (mid-1) - 0;

    if (rnkl != -1) {
      RNK << "sending rnkl\n";
      MPI_Send(&Rl, 1, MPI_LONG_LONG_INT, rnkl, 0, MPI_COMM_WORLD);
      if (Rl >= 0) { 
        MPI_Send(a, Rl+1, MPI_LONG_LONG_INT, rnkl, 0, MPI_COMM_WORLD);
        MPI_Recv(a, Rl+1, MPI_LONG_LONG_INT, rnkl, 0, 
            MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
    } else if (Rl >= 0) { qs_serial(a, 0, Rl); }

    if (rnkr != -1) {
      RNK << "sending rnkr\n";
      MPI_Send(&Rr, 1, MPI_LONG_LONG_INT, rnkr, 0, MPI_COMM_WORLD);
      if (Rr >= 0) { 
        MPI_Send(a+mid+1, Rr+1, MPI_LONG_LONG_INT, rnkr, 0, MPI_COMM_WORLD);
        MPI_Recv(a+mid+1, Rr+1, MPI_LONG_LONG_INT, rnkr, 0, 
            MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
    } else if (Rr >= 0) { qs_serial(a+mid+1, 0, Rr); }

    // send data back to parent
    if (rnk != 0) {
      pr(a, 0, r);
      MPI_Send(a, r+1, MPI_LONG_LONG_INT, rnkp, 0, MPI_COMM_WORLD);
    }

  } 


  if (rnk == 0) {
    FILE *f = fopen(argv[2], "w");
    for(int i = 0; i < r; ++i) { fprintf(f, "%lld ", a[i]); }
    fprintf(f, "\n");
    fflush(f);
    fclose(f);
    pr(a, 0, r);
  }

  MPI_Barrier( MPI_COMM_WORLD );
  double elapsedTime = MPI_Wtime() - tbeg;
  double maxTime;
  MPI_Reduce(&elapsedTime, &maxTime, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
  if (rnk == 0) {
    printf( "Total time (s): %f\n", maxTime );
  }

  MPI_Finalize();
  return 0;

  /*

  // if rank is non-zero, wait for your parent to have been done with
  // the partitioning.
  if (rnk != 0) {
    MPI_Recv(lr, 2, MPI_LONG_LONG_INT, rnkp, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
  }

  // signal no data with -42
  if (!(lr[0] == NODATA && lr[1] == NODATA)) {
    // if not empty, receive array.
    if (rnk != 0) { 
      a = new I[lr[1] - lr[0]+1];
      MPI_Recv(a, lr[1] - lr[0]+1, MPI_LONG_LONG_INT, rnkp, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
    }


    RNK << "[" <<  lr[0] <<"," <<lr[1] <<"]  |splitting...\n";
    I mid = partition(a, 0, lr[1] - lr[0]);
    RNK << "[" <<  lr[0] <<"," <<lr[1] <<"] |split: " << "[" << lr[0] << ","<<mid-1<<"]" << mid << "[" << mid+1 << "," << lr[1] << "]\n";

    I lrLC[2] = { lr[0], mid-1 }; 
    const I szLC = lrLC[1] - lrLC[0] + 1;
    if (szLC <= 0) { lrLC[0] = lrLC[1] = NODATA; }

    I lrRC[2] = {mid+1, lr[1]};
    const I szRC = lrRC[1] - lrRC[0] + 1;
    if (szRC <= 0) { lrRC[0] = lrRC[1] = NODATA; }

    // start sending sizes to children
    if (rnkl == -1) { 
      if (szLC > 0) qs_serial(a, 0, lrLC[1] - lrLC[0]);
    } else {
      MPI_Send(lrLC, 2, MPI_LONG_LONG_INT, rnkl, 0, MPI_COMM_WORLD);
      if (szLC > 0) { 
        MPI_Send(a, szLC, MPI_LONG_LONG_INT, rnkl, 0, MPI_COMM_WORLD);
        MPI_Recv(a, szLC, MPI_LONG_LONG_INT, rnkl, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
    } 

    if (rnkr == -1) {
      if (szRC > 0) qs_serial(a, 0, lrRC[1] - lrRC[0]);
    } else {
      MPI_Send(lrRC, 2, MPI_LONG_LONG_INT, rnkr, 0, MPI_COMM_WORLD) ;
      if (szRC > 0) { 
        MPI_Send(a+mid+1, szRC, MPI_LONG_LONG_INT, rnkr, 0, MPI_COMM_WORLD);
        MPI_Recv(a+mid+1, szRC, MPI_LONG_LONG_INT, rnkr, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE);
      }
    };

    if (rnk != 0) {
      // send full array pack to parent
      MPI_Send(a, lr[1] - lr[0] + 1, MPI_LONG_LONG_INT, rnkp, 0, MPI_COMM_WORLD);
    }
  } // end nodata check

done_par:
*/
}
