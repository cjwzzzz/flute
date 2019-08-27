#include "global.h"

extern  void  allocate_nn_arrays( long n );
extern void  deallocate_nn_arrays();

extern void  brute_force_nearest_neighbors
(
  long       n,
  Point*     pt,
  nn_array*  nn
);

extern void  dq_nearest_neighbors
(
  long       n,
  Point*     pt,
  nn_array*  nn
);

