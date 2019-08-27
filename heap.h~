#ifndef  _HEAP_H_
#define  _HEAP_H_

#include "global.h"

struct  heap_info
{
  long  key;
  long  idx;
  long  elt;
};

typedef  struct heap_info  Heap;

extern Heap*   _heap;

#define  heap_key( p )     ( _heap[p].key )
#define  heap_idx( p )     ( _heap[p].idx )
#define  heap_elt( k )     ( _heap[k].elt )

#define  in_heap( p )    ( heap_idx(p) > 0 )
#define  never_seen( p ) ( heap_idx(p) == 0 ) 

extern	void   allocate_heap( long n );
extern	void   deallocate_heap();
extern	void   heap_init( long  n );
extern	void   heap_insert( long  p,  long key );
extern	void   heap_decrease_key( long  p,  long new_key );
extern	long   heap_delete_min();

#endif /* _HEAP_H_ */
