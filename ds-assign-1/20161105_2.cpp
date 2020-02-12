// https://www.cs.jhu.edu/~mdinitz/classes/IntroAlgorithms/Fall2014/Lectures/lecture13.pdf
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <vector>
#include <iostream>
#include <fstream>
#include <algorithm>
#include "mpi.h"
using namespace std;
using I = long long int;
static const I INF = 1e10L;
I V, E, ESize;
I src;
I *dist[2];
I *adj;

I* Ecur;

// I *pred;
// I *next;


// source and dest for an edge at index i
I *edgesrc; I *edgedest; I*edgewt;
int rnk, nrnk;

#define RNK cout<<"\033[31m["<<rnk<<"/" << nrnk << "]\033[0m" << "{" << __LINE__ << "}"

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

  RNK << "XX\n";

  if (rnk == 0) {
    // 1. recieve input if leader
    ifstream f(argv[1]);
    f >> V >> E;


    adj = (I*)calloc((V +1) * (V + 1), sizeof(I));
    edgesrc = (I*)calloc((E+1), sizeof(I));
    edgedest = (I*)calloc((E+1), sizeof(I));
    edgewt = (I*)calloc((E+1), sizeof(I));
    for (int i = 1; i <= E; i ++) {
      int u, v, w; f >> u >> v >> w;
      adj[u*V + v] = w;
      edgesrc[i] = u; edgedest[i] = v; edgewt[i] = w;
    }
    f >> src;


    dist[0] = new I[(V +1)];
    dist[1] = new I[(V +1)];
    for(int i = 0; i <= V; i++) {
        dist[0][i] = INF;
        adj[i] = -42;
    }
    dist[0][src] = 0;
    // pred = new I[(V +1)];
    // next = new I[(V +1)];

    RNK << "V:"  << V << "|E: " << E;
    cout << "\n";
    for (int i = 1; i <= V; ++i) {
      for (int j = 1; j <= V; ++j) { 
        cout << adj[i*V+j] << " ";
      }
      cout << "\n";
    }
    cout << "\n";

  }

  // distribute information
  MPI_Bcast(&V, 1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);
  MPI_Bcast(&E, 1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);

  const I e_cur_size = ceill((float)E / nrnk);
  if (rnk != 0) {
      Ecur = (I*)calloc((E), sizeof(I));
      edgesrc = (I*)calloc((E+1), sizeof(I));
      edgedest = (I*)calloc((E+1), sizeof(I));
      edgewt = (I*)calloc((E+1), sizeof(I));
      dist[0] = new I[(V +1)]; dist[1] = new I[(V +1)];
  }

  MPI_Bcast(&edgewt, ESize+1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);
  MPI_Bcast(&edgesrc, ESize+1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);
  MPI_Bcast(&edgedest, ESize+1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);
  MPI_Bcast(&dist[0], V+1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);
  MPI_Bcast(&dist[1], V+1,
          MPI_Datatype MPI_LONG_LONG_INT,
          /*root=*/0, MPI_COMM_WORLD);

  // distribute work
  int l = 0; int r = 0; 
  if (rnk == 0) {
      const int num_per_rank = E / nrnk;

      
      int curr = E;
      for(int i = nrnk-1; i >= 1; --i) {
          const int curl = curr - num_per_rank+1;
          MPI_Send(&curl, 1, MPI_LONG_LONG_INT, /*dest=*/i, 
                  0, MPI_COMM_WORLD);
          MPI_Send(&curr, 1, MPI_LONG_LONG_INT, /*dest=*/i, 
                  0, MPI_COMM_WORLD);
          curr = curl - 1;
      }
      r = curr;
      l = 1;
  } else {
    MPI_Recv(&l, 1, MPI_LONG_LONG_INT, /*parent=*/0, 0, 
        MPI_COMM_WORLD, MPI_STATUS_IGNORE);

    MPI_Recv(&r, 1, MPI_LONG_LONG_INT, /*parent=*/0, 0, 
        MPI_COMM_WORLD, MPI_STATUS_IGNORE);

    assert(l >= 1);
    assert(l <= r);
    assert(r <= E);
  }

  int distix = 0; // IMPORTANT: starts from 0!
  for (int i = 1; i <= V;  ++i) {
      for(int j = l; j <= r; ++j) {
          if (dist[distix][edgesrc[j]] + edgewt[j] < dist[distix][edgedest[j]]) {
              dist[distix][edgedest[j]] = dist[distix][edgesrc[j]] + edgewt[j];
          }
      }

      MPI_Allreduce(dist[distix], dist[distix^1], V+1, 
              MPI_LONG_LONG_INT, MPI_MIN, MPI_COMM_WORLD);
      distix ^= 1;
  }


  if (rnk == 0) {
    ofstream f(argv[2]);
    vector<int> sortixs(V);
    std::iota(sortixs.begin(), sortixs.end(),1);
    sort(sortixs.begin(), sortixs.end(), [&](int i,int j){return dist[distix][i]<dist[distix][j];});
    for(int i = 0; i < V; ++i) {
        f << sortixs[i] << " " << dist[distix][sortixs[i]] << "\n";
    }
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
}
