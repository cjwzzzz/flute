#ifndef _MST2_H_
#define _MST2_H_

#include "global.h"

extern void  mst2_package_init( long  n );
extern void  mst2_package_done();
extern void  mst2( long n, Point* pt, long* parent );

#endif 

