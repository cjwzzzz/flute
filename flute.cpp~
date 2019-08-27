#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <math.h>
#include "flute.h"
#include <string.h>
#include <assert.h>
#include "dl.h"
#include "mst2.h"

#if D<=7
#define MGROUP 5040/4  // Max. # of groups, 7! = 5040
#define MPOWV 15  // Max. # of POWVs per group
#elif D==8
#define MGROUP 40320/4  // Max. # of groups, 8! = 40320
#define MPOWV 33  // Max. # of POWVs per group
#elif D==9
#define MGROUP 362880/4  // Max. # of groups, 9! = 362880
#define MPOWV 79  // Max. # of POWVs per group
#endif



#define INFNTY INT_MAX

#define D2M D2(1)     // Max net degree that flute_mr will handle
#define MR_FOR_SMALL_CASES_ONLY 1
#if MR_FOR_SMALL_CASES_ONLY
#define MAXPART D2M    // max partition of an MST
#define MAXT (D2M/D*2) 
#else
#define MAXPART (d/9*2) //(MAXD/THD*2) // max partition of an MST
#define MAXPART2 ((t1.deg+t2.deg)/9*2)
#define MAXT (d/5)
#endif

int D3=INFNTY;

int FIRST_ROUND=2; // note that num of total rounds = 1+FIRST_ROUND
int EARLY_QUIT_CRITERIA=1;

#define DEFAULT_QSIZE (3+min(d,1000))

#define USE_HASHING 1
#if USE_HASHING
#define new_ht 1
//int new_ht=1;
dl_t ht[D2M+1]; // hash table of subtrees indexed by degree
#endif

unsigned int curr_mark=0;

Tree wmergetree(Tree t1, Tree t2, int *order1, int *order2, DTYPE cx, DTYPE cy, int acc);
Tree xmergetree(Tree t1, Tree t2, int *order1, int *order2, DTYPE cx, DTYPE cy);
void color_tree(Tree t, int *color);
int longest_path_edge(int i, int j, int *e, int *p, int *es);
void preprocess_edges(int num_edges, int *edges, DTYPE *len,
		      int *e, int *p, int *es);

#define init_queue(q) { q[1] = 2; }
inline void enqueue(int **q, int e)
{
  int _qsize;
  if ((*q)[0]==(*q)[1]) { 
    _qsize=2*((*q)[0]+1);
    (*q)=(int*)realloc((*q), _qsize*sizeof(int));
    (*q)[0]=_qsize;
  }
  (*q)[(*q)[1]++]=e;
}

#define MAX_HEAP_SIZE (MAXD*2)
DTYPE **hdist;
typedef struct node_pair_s { // pair of nodes representing an edge
  int node1, node2;
} node_pair;
node_pair *heap; //heap[MAXD*MAXD]; 
int heap_size=0;
int max_heap_size = MAX_HEAP_SIZE;

int in_heap_order(int e1, int e2)
{
  if (hdist[heap[e1].node1][heap[e1].node2] <
      hdist[heap[e2].node1][heap[e2].node2]) {
    return 1;
  } else {
    return 0;
  }
}

void sift_up(int i)
{
  node_pair tmp;
  int j;

  for (j=i/2; j>=1 && in_heap_order(i, j); i=j, j/=2) {
    tmp = heap[j];
    heap[j] = heap[i];
    heap[i] = tmp;
  }
}

void sift_down(int i)
{
  int left, right, j;
  node_pair tmp;

  left = i*2;
  right = left+1;

  while (left <= heap_size) {
    if (left == heap_size || in_heap_order(left, right)) {
      j = left;
    } else {
      j = right;
    }
    if (in_heap_order(j, i)) {
      tmp = heap[j];
      heap[j] = heap[i];
      heap[i] = tmp;
      i = j;
      left = i*2;
      right = left+1;
    } else {
      break;
    }
  }
}

void insert_heap(node_pair *np)
{
  if (heap_size >= max_heap_size) {
    max_heap_size *= 2;
    heap = (node_pair*)realloc(heap, sizeof(node_pair)*(max_heap_size+1));
  }
  heap[++heap_size] = *np;
  sift_up(heap_size);
}

void extract_heap(node_pair *np)
{
  // caller has to make sure heap is not empty
  *np = heap[1];
  heap[1] = heap[heap_size--];
  sift_down(1);
}

void init_param()
{
  int i;

  heap = (node_pair*)malloc(sizeof(node_pair)*(max_heap_size+1));
}

Tree reftree;  // reference for qsort
int cmp_branch(const void *a, const void *b) {
  int n;
  DTYPE x1, x2, x3;

  x1 = reftree.branch[*(int*)a].x;
  n = reftree.branch[*(int*)a].n;
  x3 = reftree.branch[n].x;
  if (x3 < x1) x1=x3;

  x2 = reftree.branch[*(int*)b].x;
  n = reftree.branch[*(int*)b].n;
  x3 = reftree.branch[n].x;
  if (x3 < x2) x2=x3;

  return (x1 <= x2) ? -1 : 1;
}

void update_dist2(Tree t, DTYPE **dist, DTYPE longest,
		  int *host, int *min_node1, int *min_node2,
		  int **nb)
{
  int i, j, m, n, dd, node1, node2, node3, node4, p1, p2, pi, pn;
  DTYPE min_dist, smallest;
  DTYPE x1, x2, x3, x4, y1, y2, y3, y4;
  DTYPE threshold_x, threshold_y;
  DTYPE md = dist[*min_node1][*min_node2];

#if MR_FOR_SMALL_CASES_ONLY
  int isPin_base[D2M], *isPin, id[2*D2M];
  int u, v, b[D2M*2];
#else  
  int *isPin_base, *isPin, *id;
  int u, v, *b;

  isPin_base = (int*)malloc(sizeof(int)*t.deg);
  id = (int*)malloc(sizeof(int)*t.deg*2);
  b = (int*)malloc(sizeof(int)*t.deg*2);
#endif

  isPin = &(isPin_base[0]) - t.deg;
  dd = t.deg*2-2;

  for (i=0; i<t.deg; i++) {
    isPin_base[i] = -1;
  }

  for (i=t.deg; i<dd; i++) {
    host[i] = -1;
  }

  for (i=0; i<t.deg; i++) {
    n = t.branch[i].n;
    if (isPin[n] < 0 &&
	t.branch[n].x == t.branch[i].x && t.branch[n].y == t.branch[i].y) {
      isPin[n] = i;  // this steiner node coincides with a pin
    }
    host[i] = i;

    if (isPin[n]==i) {
      host[n] = host[i];
    }

  }
  
  for (i=0; i<dd; i++) {
    id[i] = i;
  }
    
  for (i=0; i<dd; i++) {
    n = t.branch[i].n;
    if (isPin[n]>=0 || n==i) {
      continue;
    }

    if (id[i] < id[n]) {
      id[n] = id[i];
    } else {
      id[i] = id[n];
    }

  }
  
  for (i=0; i<dd; i++) {
    while (id[i]!=id[id[i]]) {
      id[i] = id[id[i]];
    }
  }

  x1 = y1 = INFNTY;
  x2 = y2 = 0;
  for (i=0; i<t.deg; i++) {
    x1 = min(x1, t.branch[i].x);
    y1 = min(y1, t.branch[i].y);
    x2 = max(x2, t.branch[i].x);
    y2 = max(y2, t.branch[i].y);
  }

  threshold_x = (x2 - x1)/4;
  threshold_y = (y2 - y1)/4;
  threshold_x = min(threshold_x, longest);
  threshold_y = min(threshold_y, longest);

  for (i=0; i<dd; i++) {
    b[i] = i;
  }
  reftree = t;
  qsort(b, dd, sizeof(int), cmp_branch);

  for (u=0; u<dd; u++) {
    i = b[u];
    n = t.branch[i].n;
    node1 = host[i];
    node2 = host[n];
    if (node1 < 0 && node2 < 0) {
      continue;
    }
    if (t.branch[i].x <= t.branch[n].x) {
      x3 = t.branch[i].x;
      x4 = t.branch[n].x;
    } else {
      x3 = t.branch[n].x;
      x4 = t.branch[i].x;
    }
    if (t.branch[i].y <= t.branch[n].y) {
      y3 = t.branch[i].y;
      y4 = t.branch[n].y;
    } else {
      y3 = t.branch[n].y;
      y4 = t.branch[i].y;
    }

    for (v=u+1; v<dd; v++) {
      j=b[v];
      if (id[i]==id[j]) { // in the same connecting subtree
	continue;
      }
      if (ADIFF(t.branch[i].x, t.branch[j].x)>threshold_x ||
	  ADIFF(t.branch[i].y, t.branch[j].y)>threshold_y)
	continue;
      m = t.branch[j].n;
      node3 = host[j];
      node4 = host[m];
      if (node3 < 0 && node4 < 0) {
	continue;
      }

      if (t.branch[j].x <= t.branch[m].x) {
	x1 = t.branch[j].x;
	x2 = t.branch[m].x;
      } else {
	x1 = t.branch[m].x;
	x2 = t.branch[j].x;
      }
      if (t.branch[j].y <= t.branch[m].y) {
	y1 = t.branch[j].y;
	y2 = t.branch[m].y;
      } else {
	y1 = t.branch[m].y;
	y2 = t.branch[j].y;
      }

      if (x2 < x3) {
	min_dist = x3 - x2;
      } else if (x4 < x1) {
	min_dist = x1 - x4;
      } else {
	min_dist = 0;
      }

      if (min_dist >= threshold_x) {
	break;
      }

      if (y2 < y3) {
	min_dist += y3 - y2;
      } else if (y4 < y1) {
	min_dist += y1 - y4;
      }

      if (min_dist >= longest) {
	continue;
      }

      p1 = (node1 < 0) ? node2 : ((node2 < 0) ? node1 : -1);
      p2 = (node3 < 0) ? node4 : ((node4 < 0) ? node3 : -1);

      if (p1 >= 0 && p2 < 0) {
	dist[p1][node3] = 
	  ADIFF(t.branch[p1].x, t.branch[node3].x) +
	  ADIFF(t.branch[p1].y, t.branch[node3].y);
	dist[p1][node4] = 
	  ADIFF(t.branch[p1].x, t.branch[node4].x) +
	  ADIFF(t.branch[p1].y, t.branch[node4].y);
	p2 = (dist[p1][node3] <= dist[p1][node4]) ? node3 : node4;
      } else if (p1 < 0 && p2 >= 0) {
	dist[node1][p2] = 
	  ADIFF(t.branch[node1].x, t.branch[p2].x) +
	  ADIFF(t.branch[node1].y, t.branch[p2].y);
	dist[node2][p2] =
	  ADIFF(t.branch[node2].x, t.branch[p2].x) +
	  ADIFF(t.branch[node2].y, t.branch[p2].y);
	p1 = (dist[node1][p2] <= dist[node2][p2]) ? node1 : node2;
      } else if (p1 < 0 && p2 < 0) {
	// all 4 nodes are real, pick the closest pair
	
	dist[node1][node3] =
	  ADIFF(t.branch[node1].x, t.branch[node3].x) +
	  ADIFF(t.branch[node1].y, t.branch[node3].y);
	dist[node1][node4] =
	  ADIFF(t.branch[node1].x, t.branch[node4].x) +
	  ADIFF(t.branch[node1].y, t.branch[node4].y);
	dist[node2][node3] =
	  ADIFF(t.branch[node2].x, t.branch[node3].x) +
	  ADIFF(t.branch[node2].y, t.branch[node3].y);
	dist[node2][node4] =
	  ADIFF(t.branch[node2].x, t.branch[node4].x) +
	  ADIFF(t.branch[node2].y, t.branch[node4].y);

	p1 = node1;
	p2 = node3;
	smallest = dist[p1][p2];

	if (dist[node2][node3] < smallest) {
	  p1 = node2;
	  smallest = dist[p1][p2];
	}
	if (dist[node1][node4] < smallest) {
	  p1 = node1;
	  p2 = node4;
	  smallest = dist[p1][p2];
	}
	if (dist[node2][node4] < smallest) {
	  p1 = node2;
	  p2 = node4;
	  smallest = dist[p1][p2];
	}
      } else {
	dist[p1][p2] =
	  ADIFF(t.branch[p1].x, t.branch[p2].x) +
	  ADIFF(t.branch[p1].y, t.branch[p2].y);
      }

      if (min_dist < dist[p1][p2]) {
	dist[p1][p2] = dist[p2][p1] = min_dist;
	enqueue(&nb[p1], p2);
	enqueue(&nb[p2], p1);

	if (min_dist < md) {
	  md = min_dist;
	  *min_node1 = p1;
	  *min_node2 = p2;
	}
      }
    }
  }

#if !(MR_FOR_SMALL_CASES_ONLY)
  free(isPin_base); free(id); free(b);
#endif
}

void mst_from_heap(int d, DTYPE **dist, int node1, int node2, int **nb,
		   int *edges, int *tree_id)
{
  int i, j, itr, idx;
  node_pair e;

  hdist = dist;
  heap_size=0;

  for (i=0; i<d; i++) {
    tree_id[i] = 0;
  }

  tree_id[node1] = 1;
  tree_id[node2] = 1;
  e.node1 = edges[0] = node1;
  e.node2 = edges[1] = node2;
  idx = 2;

  insert_heap(&e);

  for (j=nb[node1][1]-1; j>1; j--) {
    i=nb[node1][j];
    if (tree_id[i]) continue;
    {
      e.node2 = i;
      insert_heap(&e);
    }
  }
  for (itr=d-2; itr>=1; itr--) {
    e.node1 = node2;

    for (j=nb[node2][1]-1; j>1; j--) {
      i=nb[node2][j];
      if (tree_id[i]) continue;
      {
	e.node2 = i;
	insert_heap(&e);
      }
    }

    do {
      //assert(heap_size>0);
      //extract_heap(&e);
      e = heap[1];
      while (tree_id[heap[heap_size].node2]) {
	heap_size--;
      }
      heap[1] = heap[heap_size--];
      sift_down(1);
      node2 = e.node2;
    } while (tree_id[node2]);
    node1 = e.node1;
    tree_id[node2] = tree_id[node1];
    edges[idx++] = node1;
    edges[idx++] = node2;
  }
  //assert(idx==2*d-2);
}

void build_rmst(long d, DTYPE *x, DTYPE *y, int *edges, int *inMST)
{
  int i, j, idx, n;
  int *map = (int*)calloc(d, sizeof(int));
  Point *pt = (Point*)calloc( 4*d, sizeof(Point) );
  long *parent = (long*)calloc( 4*d, sizeof(long) );
  long *par = (long*)calloc( 4*d, sizeof(long) );
  int *size = (int*)calloc(d, sizeof(int));

  for (i=0; i<d; i++) {
    pt[i].x = x[i];
    pt[i].y = y[i];
    parent[i] = par[i] = -1;
    size[i] = 1;
    inMST[i] = 0;
  }

  map[0]=0;
  for (i=n=1; i<d; i++) {
    if (x[i]!=x[i-1] || y[i]!=y[i-1]) {
      pt[n].x = pt[i].x;
      pt[n].y = pt[i].y;
      map[n] = i;
      n++;
    } else {
      parent[i] = i-1;
    }
  }
  
  //mst2( d, pt, parent );
  mst2_package_init(n);

  mst2( n, pt, par );

  mst2_package_done();
  
  /* special treatment for duplicated points not filtered in previous loop */
  for (i=1; i<n; i++) {
    if (par[i]<0) {
      for (j=n-1; j>=0; j--) {
	if (pt[j].x==pt[i].x && pt[j].y==pt[i].y && par[j]>=0) {
	  par[i]=j;
	  break;
	}
      }
    }
  }

  for (i=0; i<n; i++) {
    parent[map[i]] = map[par[i]];
  }

  for (i=0; i<d; i++) {
    //assert(parent[i]>=0);
    size[parent[i]]++;
  }
  
  idx = 2*d-3;
  for (i=0; i<d; i++) {
    if (inMST[i]) continue;
    j = i;
    while (size[j]<=1 && idx>0) {
      //assert(!inMST[j]);
      inMST[j] = 1;
      edges[idx--] = j;
      edges[idx--] = j = parent[j];
      size[j]--;
    }
  }
  //assert(idx==-1);

  inMST[edges[0]]=1;

  free(pt);
  free(map);
  free(parent);
  free(par);
  free(size);
}


/* cached version */
Tree flutes_c(int d, DTYPE *xs, DTYPE *ys, int *s, int acc)
{
  int i;
  //int orig_ht_flag;
  Tree t, tdup;

#if USE_HASHING
  dl_forall(Tree, ht[d], t) {
    for (i=0; i<d; i++) {
      if (t.branch[i].y != ys[i] || t.branch[i].x != xs[s[i]]) {
	break;
      }
    }
    if (i >= d) { // found a match
      tdup = t;
      tdup.branch = (Branch*)malloc(sizeof(Branch)*(2*d-2));
      for (i=2*d-3; i>=0; i--) {
	tdup.branch[i] = t.branch[i];
      }
      return tdup;
    }
  } dl_endfor;

  //orig_ht_flag = new_ht;
  //new_ht = 0;
#endif

  t = flutes_LMD(d, xs, ys, s, acc);

#if USE_HASHING
  //new_ht = orig_ht_flag;
      
  tdup = t;
  tdup.branch = (Branch*)malloc(sizeof(Branch)*(2*d-2));
  for (i=2*d-3; i>=0; i--) {
    tdup.branch[i] = t.branch[i];
  }
  dl_prepend(Tree, ht[d], tdup);
#endif  

  return t;
}

Tree flute_mr(int d, DTYPE *xs, DTYPE *ys, int *s,
	      int acc, int rounds, DTYPE **dist,
	      DTYPE *threshold_x, DTYPE *threshold_y,
	      DTYPE *threshold, 
	      int *best_round,
	      int *min_node1, int *min_node2,
	      int **nb)
{
  int i, j, k, m, n, itr, node1, node2;
  DTYPE min_dist, longest;
  DTYPE dist1, dist2;
  Tree t, best_t, *subtree, ttmp;
  DTYPE min_x, max_x;

#if MR_FOR_SMALL_CASES_ONLY
  int num_subtree, subroot[MAXPART], suproot[MAXPART], isSuperRoot[D2M];
  int tree_id[D2M], tid, tree_size[D2M], edges[2*D2M];
  int idx[MAXPART], offset[MAXPART], *order[MAXT], order_base[MAXT*D2M];
  DTYPE x[D2M+MAXPART], y[D2M+MAXPART];
  int new_s[D2M+MAXPART], si[D2M], xmap[D2M+MAXPART];
#else
  int num_subtree, *subroot, *suproot, *isSuperRoot;
  int *tree_id, tid, *tree_size, *edges;
  int *idx, *offset, **order, *order_base;
  DTYPE *x, *y;
  int *new_s, *si, *xmap;

  subroot = (int*)malloc(sizeof(int)*MAXPART);
  suproot = (int*)malloc(sizeof(int)*MAXPART);
  idx = (int*)malloc(sizeof(int)*MAXPART);
  offset = (int*)malloc(sizeof(int)*MAXPART);
  order = (int**)malloc(sizeof(int*)*MAXT);

  isSuperRoot = (int*)malloc(sizeof(int)*d);
  tree_id = (int*)malloc(sizeof(int)*d);
  tree_size = (int*)malloc(sizeof(int)*d);
  edges = (int*)malloc(sizeof(int)*d*2);
  order_base = (int*)malloc(sizeof(int)*d*MAXT);
  new_s = (int*)malloc(sizeof(int)*(d+MAXPART));
  si = (int*)malloc(sizeof(int)*d);
  xmap = (int*)malloc(sizeof(int)*(d+MAXPART));
  x = (DTYPE*)malloc(sizeof(DTYPE)*(d+MAXPART));
  y = (DTYPE*)malloc(sizeof(DTYPE)*(d+MAXPART));
#endif

#if USE_HASHING
  if (new_ht) {
    for (i=0; i<=d; i++) {
      ht[i] = dl_alloc();
    }
  }
#endif

  best_t.branch = NULL;
  best_t.length = INFNTY;

  for (i=0; i<MAXT; i++) {
    //order[i] = &(order_base[i*D2(acc)]);
    order[i] = &(order_base[i*d]);
  }

  while (rounds>=0) {
    for (i=0; i<d; i++) {
      x[i] = xs[s[i]];
      y[i] = ys[i];
      isSuperRoot[i] = 0;
    }

    if (rounds==FIRST_ROUND) {
      build_rmst((long)d, x, y, edges, tree_id);
      for (i=0; i<d; i++) dist[i][i]=0;
    } else {
      mst_from_heap(d, dist, *min_node1, *min_node2, nb, edges, tree_id);
    }

    if (rounds!=0) {
      longest = 0;
      for (i=0; i<d; i++) {
	init_queue(nb[i]);
      }
    }

    for (i=0; i<2*d-2; ) {
      node1 = edges[i++];
      node2 = edges[i++];
      if (rounds!=0) {
	enqueue(&nb[node1], node2);
	enqueue(&nb[node2], node1);
	dist[node1][node2] = dist[node2][node1] =
	  ADIFF(x[node1], x[node2]) + ADIFF(y[node1], y[node2]);
	if (longest < dist[node1][node2]) {
	  longest = dist[node1][node2];
	}
      }
    }

    for (i=0; i<d; i++) {
      tree_size[i] = 1;  // the node itself
    }

    suproot[0] = subroot[0] = edges[0];
    num_subtree=1;

    for (i=2*d-3; i>=0; ) {
      node2 = edges[i--];
      node1 = edges[i--];
      j = tree_size[node1]+tree_size[node2];
      //Chris
      if (j >= TAU(acc)) {
	isSuperRoot[node1] = 1;
	suproot[num_subtree] = node1;
	subroot[num_subtree++] = node2;
      } else {
	tree_size[node1] = j;
      }
    }

    //assert(num_subtree<=MAXT);

    for (i=1; i<num_subtree; i++) {
      tree_id[subroot[i]] = i+1;
      tree_size[subroot[i]] += 1;  // to account for the link to parent tree
    }

    for (i=0; i<2*d-2; ) {
      node1 = edges[i++];
      node2 = edges[i++];
      if (tree_id[node2]==1) { // non-root node
	tree_id[node2] = tree_id[node1];
      }
    }

    // Find inverse si[] of s[]
    for (i=0; i<d; i++)
      si[s[i]] = i;

    offset[1] = 0;
    for (i=1; i<num_subtree; i++) {
      offset[i+1] = offset[i] + tree_size[subroot[i-1]];
    }
    //assert(offset[num_subtree]==d+num_subtree-1-tree_size[subroot[num_subtree-1]]);

    for (i=0; i<=num_subtree; i++)
      idx[i] = 0;

    for (i=0; i<d; i++) {
      tid = tree_id[si[i]];
      j = idx[tid]++;
      x[offset[tid]+j] = xs[i];
      xmap[i] = j;

      if (isSuperRoot[si[i]]) {
	for (k=1; k<num_subtree; k++) {
	  if (suproot[k]==si[i]) {
	    tid = k+1;
	    j = idx[tid]++;
	    x[offset[tid]+j] = xs[i];
	    xmap[d-1+tid] = j;
	  }
	}
      }
    }

    for (i=0; i<=num_subtree; i++)
      idx[i] = 0;

    for (i=0; i<d; i++) {
      tid = tree_id[i];
      j = idx[tid]++;
      y[offset[tid]+j] = ys[i];
      new_s[offset[tid]+j] = xmap[s[i]];
      order[tid-1][j] = i;

      if (isSuperRoot[i]) {
	for (k=1; k<num_subtree; k++) {
	  if (suproot[k]==i) {
	    tid = k+1;
	    j = idx[tid]++;
	    y[offset[tid]+j] = ys[i];
	    new_s[offset[tid]+j] = xmap[d-1+tid];
	    order[tid-1][j] = i;
	  }
	}
      }
    }

    subtree = (Tree*)malloc(num_subtree*sizeof(Tree));
    for (i=1; i<=num_subtree; i++) {
      if (tree_size[subroot[i-1]] <= 1) {
	subtree[i-1].deg = 0;
	continue;
      }

      t = flutes_c(tree_size[subroot[i-1]], x+offset[i], y+offset[i],
		   new_s+offset[i], acc);
    
      subtree[i-1] = t;
    }


    for (i=1; i<num_subtree; i++) {
      //assert(tree_id[suproot[i]] != tree_id[subroot[i]]);

      t = wmergetree(subtree[tree_id[suproot[i]]-1],
		     subtree[tree_id[subroot[i]]-1],
		     order[tree_id[suproot[i]]-1],
		     order[tree_id[subroot[i]]-1],
		     xs[s[suproot[i]]], ys[suproot[i]], acc);

      subtree[tree_id[subroot[i]]-1].deg = 0;
      subtree[tree_id[suproot[i]]-1] = t;
    }

    t = subtree[0];
    free(subtree);
  
    if (best_t.length < t.length) {
      if (*best_round-rounds >= EARLY_QUIT_CRITERIA) {
	if (t.branch) {
	  free(t.branch);
	}
	break;
      }
    } else if (best_t.length == t.length) {
      *best_round = rounds;
    } else if (best_t.length > t.length) {
      if (best_t.branch) {
	free(best_t.branch);
      }
      best_t = t;
      *best_round = rounds;
    }

    if (rounds > 0) {
      for (i=0; i<d; i++) {
	x[i] = xs[s[i]];
	y[i] = ys[i];
      }

      *min_node1 = edges[0];
      *min_node2 = edges[1];

      update_dist2(t, dist, longest, edges, min_node1, min_node2, nb);
    }

    if (t.branch != 0 && best_t.branch != t.branch) {
      free(t.branch);
    }

    rounds--;
  }
  
#if !(MR_FOR_SMALL_CASES_ONLY)
  free(subroot); free(suproot); free(idx); free(offset); free(order);
  free(isSuperRoot); free(tree_id); free(tree_size); free(edges);
  free(order_base); free(new_s); free(si); free(xmap); free(x); free(y);
#endif
  
#if USE_HASHING
  if (new_ht) {
    for (i=0; i<=d; i++) {
      dl_forall(Tree, ht[i], ttmp) {
	free(ttmp.branch);
      } dl_endfor;
      dl_free(ht[i]);
    }
  }
#endif
  
  return best_t;
}

Tree flute_am(int d, DTYPE *xs, DTYPE *ys, int *s, int acc, 
	      DTYPE *threshold_x, DTYPE *threshold_y, DTYPE *threshold)
{
  int i, j, k, m, n, itr, node1, node2;
  DTYPE smallest_gap, gap;
  Tree t, t0, *subtree;
  int prev_effort;
  /*
  int num_subtree, subroot[MAXPART], suproot[MAXPART], isSuperRoot[MAXD];
  int tree_id[MAXD], tid, tree_size[MAXD], edges[2*MAXD];
  int idx[MAXPART], offset[MAXPART], *order[MAXT],
        order_base[MAXD+10]; //order_base[MAXT*MAXD];
  DTYPE x[MAXD+MAXPART], y[MAXD+MAXPART];
  int new_s[MAXD+MAXPART], si[MAXD], xmap[MAXD+MAXPART];
  */
  DTYPE *x, *y;
  int num_subtree, subroot[3], suproot[3], *isSuperRoot;
  int *tree_id, tid, *tree_size, *edges;
  int idx[3], offset[3], *order[3], *order_base;
  int *new_s, *si, *xmap;

  int maxd = d+1;
  x = (DTYPE*)malloc(sizeof(DTYPE)*(maxd+3));
  y = (DTYPE*)malloc(sizeof(DTYPE)*(maxd+3));
  isSuperRoot = (int*)malloc(sizeof(int)*maxd);
  tree_id = (int*)malloc(sizeof(int)*maxd);
  tree_size = (int*)malloc(sizeof(int)*maxd);
  edges = (int*)malloc(sizeof(int)*maxd*2);
  order_base = (int*)malloc(sizeof(int)*(maxd+10));
  new_s = (int*)malloc(sizeof(int)*(maxd+3));
  si = (int*)malloc(sizeof(int)*maxd);
  xmap = (int*)malloc(sizeof(int)*(maxd+3));

  /*
  for (i=0; i<MAXT; i++) {
    order[i] = &(order_base[i*MAXD]);
  }
  */

  for (i=0; i<d; i++) {
    x[i] = xs[s[i]];
    y[i] = ys[i];
    isSuperRoot[i] = 0;
  }

  build_rmst((long)d, x, y, edges, tree_id);

  for (i=0; i<d; i++) {
    tree_size[i] = 1;  // the node itself
  }

  suproot[0] = subroot[0] = edges[0];
  num_subtree=1;

  /*
  for (i=2*d-3; i>=0; ) {
    node2 = edges[i--];
    node1 = edges[i--];
    j = tree_size[node1]+tree_size[node2];
    //if (j >= d/2) {
    if (j >= d/2 && num_subtree<2) {
      isSuperRoot[node1] = 1;
      suproot[num_subtree] = node1;
      subroot[num_subtree++] = node2;
    } else {
      tree_size[node1] = j;
    }
  }
  */

  for (i=2*d-3; i>=0; ) {
    node2 = edges[i--];
    node1 = edges[i--];
    tree_size[node1] += tree_size[node2];
  }

  j = 0;
  smallest_gap = ADIFF(tree_size[j], d/2);
  for (i=1; i<d; i++) {
    gap = ADIFF(tree_size[i], d/2);
    if (gap < smallest_gap) {
      j = i;
      smallest_gap = gap;
    }
  }

  for (i=2*d-3; i>=0; ) {
    node2 = edges[i--];
    node1 = edges[i--];
    if (node2==j) {
      isSuperRoot[node1] = 1;
      suproot[num_subtree] = node1;
      subroot[num_subtree++] = node2;
      tree_size[subroot[0]] -= tree_size[j];
      break;
    }
  }

  //assert(num_subtree<=MAXT);

  for (i=1; i<num_subtree; i++) {
    tree_id[subroot[i]] = i+1;
    tree_size[subroot[i]] += 1;  // to account for the link to parent tree
  }

  for (i=0; i<2*d-2; ) {
    node1 = edges[i++];
    node2 = edges[i++];
    if (tree_id[node2]==1) { // non-root node
      tree_id[node2] = tree_id[node1];
    }
  }

  // Find inverse si[] of s[]
  for (i=0; i<d; i++)
    si[s[i]] = i;

  offset[1] = 0;
  for (i=1; i<num_subtree; i++) {
    offset[i+1] = offset[i] + tree_size[subroot[i-1]];
  }
  //assert(offset[num_subtree]==d+num_subtree-1-tree_size[subroot[num_subtree-1]]);

  for (i=0; i<num_subtree; i++) {
    order[i] = &(order_base[offset[i+1]]);
  }

  for (i=0; i<=num_subtree; i++)
    idx[i] = 0;

  for (i=0; i<d; i++) {
    tid = tree_id[si[i]];
    j = idx[tid]++;
    x[offset[tid]+j] = xs[i];
    xmap[i] = j;

    if (isSuperRoot[si[i]]) {
      for (k=1; k<num_subtree; k++) {
	if (suproot[k]==si[i]) {
	  tid = k+1;
	  j = idx[tid]++;
	  x[offset[tid]+j] = xs[i];
	  xmap[d-1+tid] = j;
	}
      }
    }
  }

  for (i=0; i<=num_subtree; i++)
    idx[i] = 0;

  for (i=0; i<d; i++) {
    tid = tree_id[i];
    j = idx[tid]++;
    y[offset[tid]+j] = ys[i];
    new_s[offset[tid]+j] = xmap[s[i]];
    order[tid-1][j] = i;

    if (isSuperRoot[i]) {
      for (k=1; k<num_subtree; k++) {
	if (suproot[k]==i) {
	  tid = k+1;
	  j = idx[tid]++;
	  y[offset[tid]+j] = ys[i];
	  new_s[offset[tid]+j] = xmap[d-1+tid];
	  order[tid-1][j] = i;
	}
      }
    }
  }

  subtree = (Tree*)malloc(num_subtree*sizeof(Tree));
  for (i=1; i<=num_subtree; i++) {
    if (tree_size[subroot[i-1]] <= 1) {
      subtree[i-1].deg = 0;
      continue;
    }

    t = flutes_ALLD(tree_size[subroot[i-1]], x+offset[i], y+offset[i],
		    new_s+offset[i], acc);
    subtree[i-1] = t;
  }

  for (i=1; i<num_subtree; i++) {
    //assert(tree_id[suproot[i]] != tree_id[subroot[i]]);

    t = xmergetree(subtree[tree_id[suproot[i]]-1],
		   subtree[tree_id[subroot[i]]-1],
		   order[tree_id[suproot[i]]-1],
		   order[tree_id[subroot[i]]-1],
		   xs[s[suproot[i]]], ys[suproot[i]]);
    
    subtree[tree_id[subroot[i]]-1].deg = 0;
    subtree[tree_id[suproot[i]]-1] = t;
  }

  t0 = subtree[0];
  free(subtree);
  
  t = t0;

  free(x); free(y); free(isSuperRoot); free(tree_id); free(tree_size);
  free(edges); free(order_base); free(new_s); free(si); free(xmap);

  return t;
}

Tree flutes_HD(int d, DTYPE *xs, DTYPE *ys, int *s, int acc)
{
  int i, A, orig_D3;
  Tree t;
  //DTYPE *dist[MAXD], *dist_base;
  DTYPE **dist, *dist_base;
  DTYPE threshold, threshold_x, threshold_y;
  int best_round, min_node1, min_node2;
  int **nb;
  DTYPE prev_len;
  
  //Chris
  if (d<=D2(acc)) {
      if (acc <= 6) {
          FIRST_ROUND = 0;
          A = acc;
      }
      else {
          FIRST_ROUND = acc-6;
          A = 6 + ((acc-5)/4)*2;  // Even A is better
      }
      EARLY_QUIT_CRITERIA = (int) (0.75*FIRST_ROUND + 0.5);

      dist_base = (DTYPE*)malloc(d*d*sizeof(DTYPE));
      dist = (DTYPE**)malloc(d*sizeof(DTYPE*));
      nb = (int**)malloc(d*sizeof(int*));
      for (i=0; i<d; i++) {
	dist[i] = &(dist_base[i*d]);
	nb[i] = (int*)malloc(DEFAULT_QSIZE*sizeof(int));
	nb[i][0] = DEFAULT_QSIZE;
	nb[i][1] = 2; // queue head
      }

      t = flute_mr(d, xs, ys, s, A, FIRST_ROUND,
		   dist, &threshold_x, &threshold_y, &threshold,
		   &best_round, &min_node1,
		   &min_node2, nb);

      free(dist_base);
      free(dist);
      for (i=0; i<d; i++) {
	free(nb[i]);
      }
      free(nb);
  }
  else {
      A = acc;
      orig_D3 = D3;
      if (orig_D3 >= INFNTY && d > 1000) {
	D3 = (d <= 10000) ? 1000 : 10000;
      }
      t = flute_am(d, xs, ys, s, A, 
		   &threshold_x, &threshold_y, &threshold);
      if (orig_D3 >= INFNTY) {
	D3 = orig_D3;
      }
  }

  return t;
}

int pickWin(Tree t, DTYPE cx, DTYPE cy, int inWin[])
{
#if MR_FOR_SMALL_CASES_ONLY
  int i, j, n, dd, cnt, stack[D2M*2], top=0, prev, curr, next;
  int isPin_base[D2M], *isPin, nghbr_base[D2M], *nghbr, q[2*D2M];
#else
  int i, j, n, dd, cnt, *stack, top=0, prev, curr, next;
  int *isPin_base, *isPin, *nghbr_base, *nghbr, *q;

  stack = (int*)malloc(sizeof(int)*t.deg*2);
  isPin_base = (int*)malloc(sizeof(int)*t.deg);
  nghbr_base = (int*)malloc(sizeof(int)*t.deg);
  q = (int*)malloc(sizeof(int)*t.deg*2);
#endif

  if (t.deg <= 3) {
    for (i=0; i<t.deg*2-2; i++) {
      inWin[i] = 1;
    }
#if !(MR_FOR_SMALL_CASES_ONLY)
    free(stack); free(isPin_base); free(nghbr_base); free(q);
#endif
    return t.deg;
  }

  memset(nghbr_base, 0, sizeof(int)*t.deg);
  nghbr = &(nghbr_base[0]) - t.deg;
  isPin = &(isPin_base[0]) - t.deg;

  for (i=0; i<t.deg; i++) {
    isPin_base[i] = -1;
  }

  dd = t.deg*2-2;
  for (i=0; i<dd; i++) {
    inWin[i] = 0;
    nghbr[t.branch[i].n]++;
  }

  for (i=t.deg+1; i<dd; i++) {
    nghbr[i] += nghbr[i-1];
  }
  nghbr[dd] = nghbr[dd-1];

  for (i=0; i<dd; i++) {
    q[--nghbr[t.branch[i].n]] = i;
  }

  cnt = 0;
  for (i=0; i<t.deg; i++) {
    n = t.branch[i].n;
    if (t.branch[n].x == t.branch[i].x && t.branch[n].y == t.branch[i].y) {
      isPin[n] = i;  // this steiner node coincides with a pin
    }
    if (t.branch[i].x == cx && t.branch[i].y == cy) {
      inWin[i] = 1;
      cnt++;
      if (isPin[n]==i) {
	inWin[n] = 1;
	stack[top++] = t.branch[n].n;
	for (j=nghbr[n]; j<nghbr[n+1]; j++) {
	  if (q[j]==i) {
	    continue;
	  }
	  stack[top++] = q[j];
	}
      } else {
	stack[top++] = n;
      }
    }
  }
  //assert(top > 0);
  
  while (top > 0) {
    i = stack[--top];
    if (inWin[i]) {
      continue;
    }
    inWin[i] = 1;
    if (i < t.deg) {
      cnt++;
      continue;
    }
    n = isPin[i];
    if (n >= 0) {
      if (!inWin[n]) {
	inWin[n] = 1;
	cnt++;
      }
    } else {
      stack[top++] = t.branch[i].n;
      for (j=nghbr[i]; j<nghbr[i+1]; j++) {
	stack[top++] = q[j];
      }
    }
  }
  
  for (i=0; i<t.deg; i++) {
    if (inWin[i]) {
      n = t.branch[i].n;
      if (isPin[n]!=i) {
	continue;
      }
      prev = n;
      curr = t.branch[n].n;
      next = t.branch[curr].n;
      while (curr != next) {
        t.branch[curr].n = prev;
        prev = curr;
        curr = next;
        next = t.branch[curr].n;
      }
      t.branch[curr].n = prev;
      t.branch[n].n = n;
    }
  }

  //assert(cnt>0);
#if !(MR_FOR_SMALL_CASES_ONLY)
  free(stack); free(isPin_base); free(nghbr_base); free(q);
#endif
  return cnt;
}

/* merge tree t2 into tree t1, which have shared common nodes.  The intention
   is to add the non-common tree nodes of t2 into t1, as well as the 
   associated steiner nodes */
Tree merge_into(Tree t1, Tree t2, int common[], int nc, int *o1, int *o2)
{
  Tree t;
  DTYPE cx, cy;
#if MR_FOR_SMALL_CASES_ONLY
  int i, j, k, d, n, offset, map[2*D2M], reachable[2*D2M];
  int o[D2M+MAXPART];
#else
  int i, j, k, d, n, offset, *map, *reachable;
  int *o;

  map = (int*)malloc(sizeof(int)*(t1.deg+t2.deg)*2);
  reachable = (int*)malloc(sizeof(int)*(t1.deg+t2.deg)*2);
  o = (int*)malloc(sizeof(int)*(t1.deg+t2.deg+MAXPART2));
#endif
  
  if (t2.deg <= nc) {
    free(t2.branch);
#if !(MR_FOR_SMALL_CASES_ONLY)
    free(map); free(reachable); free(o);
#endif
    return t1;
  }

  t.deg = t1.deg + t2.deg - nc;
  t.branch = (Branch *) malloc((2*t.deg-2)*sizeof(Branch));

  offset = t2.deg - nc;

  for (i=t1.deg; i<t1.deg*2-2; i++) {
    t.branch[i+offset] = t1.branch[i];
    t.branch[i+offset].n = t1.branch[i].n + offset;
  }

  memset(reachable, 0, sizeof(int)*2*t2.deg);
  for (i=2*t2.deg-3; i>=0; i--) {
    if (!common[i] && t2.branch[i].n!=i) {
      reachable[t2.branch[i].n] = 1;
    }
  }

  for (i=2*t2.deg-3; i>=0; i--) {
    map[i] = -1;
  }

  d = t1.deg*2 - 2;

  /* a slow method; could be sped up here */
  for (i=0; i<t2.deg; i++) {
    if (common[i]) {
      n = t2.branch[i].n;
      if (map[n]!=-1 || !reachable[n]) {
	continue;
      }
      if (t2.branch[i].x != t2.branch[n].x ||
	  t2.branch[i].y != t2.branch[n].y) {
	continue;
      }
      for (j=0; j<t1.deg; j++) {
	if (t1.branch[j].x == t2.branch[i].x &&
	    t1.branch[j].y == t2.branch[i].y) {
	  break;
	}
      }
      //assert(j<t1.deg);
      n = t1.branch[j].n;
      if (t1.branch[j].x == t1.branch[n].x &&
	  t1.branch[j].y == t1.branch[n].y) {
	/* pin j in t1 is also a steiner node */
	map[i] = n;
      } else { // create a steiner node for the common pin in t1
	t.branch[d+offset] = t1.branch[j];
	t.branch[d+offset].n += offset;
	t1.branch[j].n = d;
	map[i] = d;
	d++;
	//assert(d+offset<=t.deg*2-2);
      }

      map[t2.branch[i].n] = map[i];
    }
  }

  for (; i<2*t2.deg-2; i++) {
    if (map[i]==-1 && !common[i] && reachable[i]) {
      map[i] = d++;
      //assert(d+offset<=t.deg*2-2);
    }
  }

  /* merge the pin nodes in the correct order */
  j = i = k = 0;
  while (k<t2.deg && common[k]) { k++; }

  do {
    if (k>=t2.deg) {
      for (; i<t1.deg; i++) {
	t.branch[j] = t1.branch[i];
	t.branch[j].n = t1.branch[i].n + offset;
	o[j] = o1[i];
	j++;
      }
    } else if (i>=t1.deg) {
      for (; k<t2.deg; k++) {
	if (common[k]) {
	  continue;
	}
	t.branch[j] = t2.branch[k];
	n = t2.branch[k].n;
	//assert(map[n]>=t1.deg);
	t.branch[j].n = map[n] + offset;
	o[j] = o2[k];
	j++;
      }
    } else if (o1[i] < o2[k]) {
      t.branch[j] = t1.branch[i];
      t.branch[j].n = t1.branch[i].n + offset;
      o[j] = o1[i];
      j++;
      i++;
    } else {
      t.branch[j] = t2.branch[k];
      n = t2.branch[k].n;
      //assert(map[n]>=t1.deg);
      t.branch[j].n = map[n] + offset;
      o[j] = o2[k];
      j++;
      do {
	k++;
      } while (k<t2.deg && common[k]);
    }
  }while (i<t1.deg || k<t2.deg);
  //assert(j==t.deg);

  for (i=0; i<j; i++) {
    o1[i] = o[i];
  }

  j += t1.deg - 2;
  for (i=t2.deg; i<2*t2.deg-2; i++) {
    if (!common[i] && reachable[i]) {
      t.branch[map[i]+offset] = t2.branch[i];
      n = t2.branch[i].n;
      //assert(map[n]>=t1.deg);
      t.branch[map[i]+offset].n = map[n] + offset;
      j++;
    }
  }

  j = d+offset;
  //assert(j <= t.deg*2-2);
  while (j < t.deg*2-2) {
    /* redundant steiner nodes */
    t.branch[j] = t2.branch[0];
    t.branch[j].n = j;
    j++;
  }

  /*
  for (i=0; i<t.deg; i++) {
    assert(t.branch[i].n>=t.deg);
  }
  */

  t.length = wirelength(t);

  free(t1.branch);
  free(t2.branch);

#if !(MR_FOR_SMALL_CASES_ONLY)
  free(map); free(reachable); free(o);
#endif
  return t;
}

/* simply merge two trees at their common node */
Tree smergetree(Tree t1, Tree t2, int *o1, int *o2,
		DTYPE cx, DTYPE cy)
{
  Tree t;
  int d, i, j, k, n, ci, cn, mapped_cn, prev, curr, next, offset;
#if MR_FOR_SMALL_CASES_ONLY
  int o[D2M+MAXPART], map[2*D2M];
#else
  int *o, *map;

  map = (int*)malloc(sizeof(int)*(t1.deg+t2.deg)*2);
  o = (int*)malloc(sizeof(int)*(t1.deg+t2.deg+MAXPART2));  
#endif

  t.deg = t1.deg + t2.deg - 1;
  t.branch = (Branch *) malloc((2*t.deg-2)*sizeof(Branch));

  offset = t2.deg - 1;
  d = t1.deg*2-2;

  for (i=0; i<t1.deg; i++) {
    if (t1.branch[i].x==cx && t1.branch[i].y==cy) {
      break;
    }
  }
  n = t1.branch[i].n;
  if (t1.branch[n].x==cx && t1.branch[n].y==cy) {
    mapped_cn = n;
  } else {
    t.branch[d+offset] = t1.branch[i];
    t.branch[d+offset].n += offset;
    t1.branch[i].n = d;
    mapped_cn = d;
    d++;
  }

  for (i=t2.deg; i<t2.deg*2-2; i++) {
    map[i] = -1;
  }
  for (i=0; i<t2.deg; i++) {
    if (t2.branch[i].x==cx && t2.branch[i].y==cy) {
      ci = i;
      break;
    }
  }

  n = t2.branch[i].n;

  if (t2.branch[n].x==cx && t2.branch[n].y==cy) {
    cn = n;
  } else {
    cn = i;
  }

  prev = n;
  curr = t2.branch[n].n;
  next = t2.branch[curr].n;
  while (curr != next) {
    t2.branch[curr].n = prev;
    prev = curr;
    curr = next;
    next = t2.branch[curr].n;
  }
  t2.branch[curr].n = prev;
  t2.branch[n].n = cn;

  for (i=t2.deg; i<2*t2.deg-2; i++) {
    if (i!=cn) {
      map[i] = d++;
    }
  }
  map[cn] = mapped_cn;

  /* merge the pin nodes in the correct order */
  j = i = k = 0;
  if (k==ci) { k++; }

  do {
    if (k>=t2.deg) {
      for (; i<t1.deg; i++) {
	t.branch[j] = t1.branch[i];
	t.branch[j].n = t1.branch[i].n + offset;
	o[j] = o1[i];
	j++;
      }
    } else if (i>=t1.deg) {
      for (; k<t2.deg; k++) {
	if (k==ci) {
	  continue;
	}
	t.branch[j] = t2.branch[k];
	n = t2.branch[k].n;
	t.branch[j].n = map[n] + offset;
	o[j] = o2[k];
	j++;
      }
    } else if (o1[i] < o2[k]) {
      t.branch[j] = t1.branch[i];
      t.branch[j].n = t1.branch[i].n + offset;
      o[j] = o1[i];
      j++;
      i++;
    } else {
      t.branch[j] = t2.branch[k];
      n = t2.branch[k].n;
      t.branch[j].n = map[n] + offset;
      o[j] = o2[k];
      j++;
      k++;
      if (k==ci) { k++; }
    }
  }while (i<t1.deg || k<t2.deg);
  //assert(j==t.deg);

  for (i=0; i<j; i++) {
    o1[i] = o[i];
  }

  for (i=t1.deg; i<t1.deg*2-2; i++) {
    t.branch[i+offset] = t1.branch[i];
    t.branch[i+offset].n = t1.branch[i].n + offset;
  }

  for (i=t2.deg; i<2*t2.deg-2; i++) {
    if (i != cn) {
      t.branch[map[i]+offset] = t2.branch[i];
      n = t2.branch[i].n;
      t.branch[map[i]+offset].n = map[n] + offset;
    }
  }

  for (i=d+offset; i<t.deg*2-2; i++) {
    t.branch[i] = t2.branch[0];
    t.branch[i].n = i;
  }

  free(t1.branch);
  free(t2.branch);

  t.length = wirelength(t);

#if !(MR_FOR_SMALL_CASES_ONLY)
  free(map); free(o);
#endif
  return t;
}

/* window-based heuristics */
Tree wmergetree(Tree t1, Tree t2, int *order1, int *order2,
		DTYPE cx, DTYPE cy, int acc)
{
  Tree t, t3, t4;
#if MR_FOR_SMALL_CASES_ONLY
  int s[D2M], inWin[2*D2M], d, d2, i, ci, n;
  int i1, i2, o[D2M], os[D2M], si[D2M];
  DTYPE x[D2M], y[D2M], tmp;
#else
  int *s, *inWin, d, d2, i, ci, n;
  int i1, i2, *o, *os, *si;
  DTYPE *x, *y, tmp;

  s = (int*)malloc(sizeof(int)*(t1.deg+t2.deg));
  inWin = (int*)malloc(sizeof(int)*(t1.deg+t2.deg)*2);
  o = (int*)malloc(sizeof(int)*(t1.deg+t2.deg));
  os = (int*)malloc(sizeof(int)*(t1.deg+t2.deg));
  si = (int*)malloc(sizeof(int)*(t1.deg+t2.deg));
  x = (DTYPE*)malloc(sizeof(DTYPE)*(t1.deg+t2.deg));
  y = (DTYPE*)malloc(sizeof(DTYPE)*(t1.deg+t2.deg));
#endif

  if (t1.deg <= 0) {
    for (i=0; i<t2.deg; i++) {
      order1[i] = order2[i];
    }
#if !(MR_FOR_SMALL_CASES_ONLY)
    free(s); free(inWin); free(o); free(os); free(si); free(x); free(y);
#endif
    return t2;
  } else if (t2.deg <= 0) {
#if !(MR_FOR_SMALL_CASES_ONLY)
    free(s); free(inWin); free(o); free(os); free(si); free(x); free(y);
#endif
    return t1;
  }

  d = pickWin(t1, cx, cy, inWin);
  d2 = pickWin(t2, cx, cy, inWin+2*t1.deg);
  d += d2;

  //if (d<t1.deg+t2.deg && t1.deg>2 && t2.deg>2) {
  if (d<t1.deg+t2.deg) {
    for (i=0; i<t2.deg; i++) {
      if (t2.branch[i].x == cx && t2.branch[i].y == cy) {
	ci = i;
	break;
      }
    }

    d--;  // to exclude the duplicated common point (cx, cy)

    n = 0;

    i1 = i2 = 0;
    while (i1<t1.deg && !inWin[i1]) { i1++; }
    while (i2<t2.deg && (!inWin[i2+2*t1.deg] || i2==ci)) { i2++; }
    do {
      if (i2 >= t2.deg) {
	for (; i1<t1.deg; i1++) {
	  if (inWin[i1]) {
	    x[n] = t1.branch[i1].x;
	    y[n] = t1.branch[i1].y;
	    o[n] = order1[i1];
	    n++;
	  }
	}
      } else if (i1 >= t1.deg) {
	for (; i2<t2.deg; i2++) {
	  if (inWin[i2+2*t1.deg] && i2!=ci) {
	    x[n] = t2.branch[i2].x;
	    y[n] = t2.branch[i2].y;
	    o[n] = order2[i2];
	    n++;
	  }
	}
      } else if (order1[i1] < order2[i2]) {
	x[n] = t1.branch[i1].x;
	y[n] = t1.branch[i1].y;
	o[n] = order1[i1];
	n++;
	i1++;
	while (i1<t1.deg && !inWin[i1]) { i1++; }
      } else {
	x[n] = t2.branch[i2].x;
	y[n] = t2.branch[i2].y;
	o[n] = order2[i2];
	n++;
	i2++;
	while (i2<t2.deg && (!inWin[i2+2*t1.deg] || i2==ci)) { i2++; }
      }
    } while (i1 < t1.deg || i2 < t2.deg);
    //assert(n==d);

    for (i=0; i<d; i++) {
      si[i]=i;
    }
    for (i=0; i<d; i++) {
      n = i;
      for (i1=i+1; i1<d; i1++) {
	if (x[i1] < x[n]) {
	  n=i1;
	}
      }
      tmp = x[i];
      x[i] = x[n];
      x[n] = tmp;
      tmp = si[n];
      si[n] = si[i];
      si[i] = tmp;
    }
    for (i=0; i<d; i++) {
      os[si[i]] = i;
    }
    t3 = flutes_LMD(d, x, y, os, acc);
    t = merge_into(t3, t2, inWin+2*t1.deg, d2, o, order2);
    t4 = merge_into(t, t1, inWin, d+1-d2, o, order1);
  } else 
  if (t2.deg > 2) {
    for (i=0; i<t2.deg; i++) {
      o[i]=order2[i];
    }
    t4 = smergetree(t2, t1, o, order1, cx, cy);
  } else {
    for (i=0; i<t1.deg; i++) {
      o[i]=order1[i];
    }
    t4 = smergetree(t1, t2, o, order2, cx, cy);
  }
  
  for (i=0; i<t4.deg; i++) {
    order1[i] = o[i];
  }

#if !(MR_FOR_SMALL_CASES_ONLY)
    free(s); free(inWin); free(o); free(os); free(si); free(x); free(y);
#endif

  return t4;
}

/* xmerge heuristics */
typedef struct TreeNode_s{
  struct TreeNode_s *parent;
  dl_t children;
  int order, id;
  unsigned int mark;
  DTYPE x, y;
  DTYPE blen;  // length of this edge (i.e. branch length)
  // longest edge from here, use child node of an edge to represent it
  struct TreeNode_s *e;
  DTYPE len;  // len of current e
} TreeNode;

void redirect(Tree t, DTYPE cx, DTYPE cy)
{
  int i, root, prev, curr, next;

  /* assume that one of the nodes must match (cx, cy) */
  root = 0;
  for (i=1; i<t.deg; i++) {
    if (t.branch[i].x==cx && t.branch[i].y==cy) {
      root = i;
      break;
    }
  }

  prev = root;
  curr = t.branch[root].n;
  next = t.branch[curr].n;
  while (curr != next) {
    t.branch[curr].n = prev;
    prev = curr;
    curr = next;
    next = t.branch[curr].n;
  }
  t.branch[curr].n = prev;

  t.branch[root].n = root;
}

void update_subtree(TreeNode *p, int id)
{
  TreeNode *child, *grandp;
  dl_t subtree=dl_alloc();

  dl_append(TreeNode*, subtree, p);

  while (dl_length(subtree)>0) {
    dl_pop_first(TreeNode*, subtree, p);
    p->e = p;
    grandp = p->parent;
    if (grandp) {
      p->len = p->blen = ADIFF(p->x, grandp->x) + ADIFF(p->y, grandp->y);
      if (p->len < grandp->len) {
	p->len = grandp->len;
	p->e = grandp->e;
      }
    } else {
      p->len = 0;
    }

    if (id) {
      p->id = id;
    }

    dl_forall(TreeNode*, p->children, child) {
      dl_prepend(TreeNode*, subtree, child);
    } dl_endfor;
  }

  dl_free(subtree);
}

TreeNode *createRootedTree(Tree t, int *order, int id, dl_t list_of_nodes)
{
  int i, dd, n;
  TreeNode *root=0, **nodes, *p;

  dd = t.deg*2-2;
  nodes = (TreeNode**)malloc(sizeof(TreeNode*)*dd);
  for (i=0; i<dd; i++) {
    nodes[i] = (TreeNode*)malloc(sizeof(TreeNode));
    nodes[i]->mark = curr_mark;
    nodes[i]->children = dl_alloc();
  }

  curr_mark++;
  for (i=0; i<dd; i++) {
    nodes[i]->mark = curr_mark;
    n = t.branch[i].n;
    if (i==n) {
      if (i < t.deg) {
	//assert(root==0);
	nodes[i]->parent = 0;
	root = nodes[i];
      } else {  /* must be redundant */
	dl_free(nodes[i]->children);
	free(nodes[i]);
	nodes[i] = 0;
	continue;
      }
    } else {
      p = nodes[n];
      nodes[i]->parent = p;
      dl_append(TreeNode*, p->children, nodes[i]);
    }
    nodes[i]->order = (i < t.deg) ? order[i] : -1;
    nodes[i]->id = id;
    nodes[i]->x = t.branch[i].x;
    nodes[i]->y = t.branch[i].y;

    /* len will be computed in update_subtree 
    nodes[i]->blen =
      ADIFF(t.branch[i].x, t.branch[n].x)+ADIFF(t.branch[i].y, t.branch[n].y);

    nodes[i]->e = nodes[i];
    nodes[i]->len =
      ADIFF(t.branch[i].x, t.branch[n].x)+ADIFF(t.branch[i].y, t.branch[n].y);
    */

    dl_append(TreeNode*, list_of_nodes, nodes[i]);
  }

  //assert(root);
  
  update_subtree(root, 0);

  for (i=0; i<dd; i++) {
    if (nodes[i] && nodes[i]->mark!=curr_mark) {
      dl_free(nodes[i]->children);
      free(nodes[i]);
    }
  }

  free(nodes);
  return root;
}

void freeTree(TreeNode *t)
{
  TreeNode *child;
  dl_forall(TreeNode *, t->children, child) {
    freeTree(child);
  } dl_endfor;
  dl_free(t->children);
  free(t);
}

int cmpNodeByYX(const void* a, const void* b)
{
  DTYPE ay = (*(TreeNode**)a)->y;
  DTYPE by = (*(TreeNode**)b)->y;
  DTYPE ax, bx;
  
  if (ay < by) return -1;
  if (ay > by) return 1;

  ax = (*(TreeNode**)a)->x;
  bx = (*(TreeNode**)b)->x;

  if (ax < bx) return -1;
  if (ax > bx) return 1;
  return 0;
}

int cmpNodeByXY(const void* a, const void* b)
{
  DTYPE ax = (*(TreeNode**)a)->x;
  DTYPE bx = (*(TreeNode**)b)->x;
  DTYPE ay, by;
  
  if (ax < bx) return -1;
  if (ax > bx) return 1;

  ay = (*(TreeNode**)a)->y;
  by = (*(TreeNode**)b)->y;

  if (ay < by) return -1;
  if (ay > by) return 1;
  return 0;
}

void remove_child(dl_t children_list, TreeNode* c)
{
  TreeNode *child;
  dl_forall(TreeNode*, children_list, child) {
    if (child==c) {
      dl_delete_current();
      break;
    }
  } dl_endfor;
}

void cleanTree(TreeNode* tn)
{
  /*
  TreeNode *c, *p;

  dl_forall(TreeNode*, tn->children, c) {
    cleanTree(c);
  } dl_endfor;

  p = tn->parent;
  if (!p) return;

  if (tn->order >= 0) return;  // don't clean pin nodes

  if (dl_length(tn->children)<=0) {
    remove_child(p->children, tn);
    dl_free(tn->children);
    free(tn);
  } else if (dl_length(tn->children)<=1) {
    c = dl_first(TreeNode*, tn->children);
    c->parent = p;
    dl_append(TreeNode*, p->children, c);
    remove_child(p->children, tn);
    dl_free(tn->children);
    free(tn);
  }
  */

  // non-recursive version
  TreeNode *c, *p;
  dl_t nlist=dl_alloc();

  dl_append(TreeNode*, nlist, tn);

  while (dl_length(nlist)>0) {
    dl_pop_first(TreeNode*, nlist, tn);
    dl_forall(TreeNode*, tn->children, c) {
      dl_append(TreeNode*, nlist, c);
    } dl_endfor;

    p = tn->parent;
    if (p && tn->order < 0) {
      if (dl_length(tn->children)<=0) {
	remove_child(p->children, tn);
	dl_free(tn->children);
	free(tn);
      } else if (dl_length(tn->children)<=1) {
	c = dl_first(TreeNode*, tn->children);
	c->parent = p;
	dl_append(TreeNode*, p->children, c);
	remove_child(p->children, tn);
	dl_free(tn->children);
	free(tn);
      }
    }
  }

  dl_free(nlist);
}

int cmpNodeByOrder(void* a, void* b)
{
  int ax = (*(TreeNode**)a)->order;
  int bx = (*(TreeNode**)b)->order;
  
  if (ax < bx) return -1;
  if (ax > bx) return 1;
  return 0;
}

Tree mergeRootedTrees(TreeNode *tn1, TreeNode *tn2, int *order1)
{
  int i, n, redundant;
  Tree t;
  TreeNode *child, *p;
  dl_t list_of_nodes=dl_alloc();
  dl_t pin_nodes=dl_alloc(), steiner_nodes=dl_alloc();

  //assert(tn1->x==tn2->x && tn1->y==tn2->y);

  /* merge tn2 to tn1 */
  while (dl_length(tn2->children)>0) {
    dl_pop_first(TreeNode*, tn2->children, child);
    child->parent = tn1;
    dl_append(TreeNode*, tn1->children, child);
  }
  dl_free(tn2->children);
  free(tn2);

  cleanTree(tn1);

  /* convert tn1 back to a Tree */

  dl_append(TreeNode*, list_of_nodes, tn1);
  do {
    dl_pop_first(TreeNode*, list_of_nodes, child);
    if (child->order < 0) {
      if (dl_length(child->children)==1) { /* redundant steiner node */
	p = dl_first(TreeNode*, child->children);
	p->parent = child->parent;
	/* note that p->parent's children list is already gone */
	dl_append(TreeNode*, list_of_nodes, p);
	dl_free(child->children);
	free(child);
	continue;
      } else if (dl_length(child->children)==0) {
	dl_free(child->children);
	free(child);
	continue;
      }
      dl_append(TreeNode*, steiner_nodes, child);
    } else {
      dl_append(TreeNode*, pin_nodes, child);
    }
    dl_concat(list_of_nodes, child->children);
  } while (dl_length(list_of_nodes)>0);
  dl_free(list_of_nodes);

  dl_sort(pin_nodes, sizeof(TreeNode*), cmpNodeByOrder);

  i=0;
  dl_forall(TreeNode*, pin_nodes, child) {
    child->id = i++;
  } dl_endfor;

  t.deg = i;

  dl_forall(TreeNode*, steiner_nodes, child) {
    child->id = i++;
  } dl_endfor;

  //assert(i<=2*t.deg-2);

  t.branch = (Branch*)malloc(sizeof(Branch)*(t.deg*2-2));

  redundant = i;
  for (; i<2*t.deg-2; i++) {
    t.branch[i].n = i;
    t.branch[i].x = tn1->x;
    t.branch[i].y = tn1->y;
  }

  t.branch[tn1->id].n = -1;

  dl_forall(TreeNode*, pin_nodes, child) {
    i = child->id;
    if (child->order >= 0) {
      order1[i] = child->order;
    }
    t.branch[i].x = child->x;
    t.branch[i].y = child->y;
    p = child->parent;
    if (p) {
      if (p->id >= t.deg) {
	t.branch[i].n = p->id;
      } else {
	//assert(p==tn1);
	//assert(redundant<t.deg*2-2);
	t.branch[i].n = redundant;
	t.branch[p->id].n = redundant;
	t.branch[redundant].x = p->x;
	t.branch[redundant].y = p->y;
	redundant++;
      }
    }
  } dl_endfor;
  dl_forall(TreeNode*, steiner_nodes, child) {
    i = child->id;
    if (child->order >= 0) {
      order1[i] = child->order;
    }
    t.branch[i].x = child->x;
    t.branch[i].y = child->y;
    p = child->parent;
    if (p->id < t.deg) { // must be the root
      if (t.branch[p->id].n < 0) {
	t.branch[p->id].n = i;
	t.branch[i].n = i;
      } else {
	n = t.branch[p->id].n;
	if (t.branch[p->id].x==t.branch[n].x &&
	    t.branch[p->id].y==t.branch[n].y) {
	  t.branch[i].n = n;
	} else {
	  //assert(redundant<t.deg*2-2);
	  t.branch[redundant].x = t.branch[p->id].x;
	  t.branch[redundant].y = t.branch[p->id].y;
	  t.branch[redundant].n = t.branch[p->id].n;
	  t.branch[p->id].n = redundant;
	  t.branch[i].n = redundant;
	  redundant++;
	}
      }
    } else {
      t.branch[i].n = p->id;
    }
  } dl_endfor;

  dl_forall(TreeNode*, pin_nodes, child) {
    free(child);
  } dl_endfor;
  dl_free(pin_nodes);

  dl_forall(TreeNode*, steiner_nodes, child) {
    free(child);
  } dl_endfor;
  dl_free(steiner_nodes);

  t.length = wirelength(t);
  return t;
}

void collect_nodes(TreeNode* tn, dl_t nlist)
{
  /*
  TreeNode* c;
  
  dl_append(TreeNode*, nlist, tn);
  dl_forall(TreeNode*, tn->children, c) {
    collect_nodes(c, nlist);
  }dl_endfor;
  */
  // non-recursive version
  TreeNode* c;
  dl_el *curr;
  
  dl_append(TreeNode*, nlist, tn);

  for (curr=nlist->last; curr; curr=curr->next) {
    tn = dl_data(TreeNode*, curr);
    dl_forall(TreeNode*, tn->children, c) {
      dl_append(TreeNode*, nlist, c);
    }dl_endfor;
  }
}

typedef struct {
  TreeNode *n1, *n2;
  DTYPE new_x, new_y, gain;
} xdata;

int cmpXdata(void *a, void *b)
{
  DTYPE ga = (*(xdata*)a).gain;
  DTYPE gb = (*(xdata*)b).gain;
  if (ga > gb) return -1;
  if (ga < gb) return 1;
  return 0;
}

inline TreeNode *cedge_lca(TreeNode* n1, TreeNode* n2, DTYPE *len, int *n2ton1)
{
  int i;
  TreeNode *curr, *lca, *e;

  curr_mark++;

  curr = n1;
  while (curr) {
    curr->mark = curr_mark;
    curr = curr->parent;
  }

  lca = n2;
  while (lca && lca->mark!=curr_mark) {
    lca->mark = curr_mark;
    lca = lca->parent;
  }

  if (!lca) {
    n1 = n1->parent;
    if (n1 && n1!=lca && (n1->len > n2->len)) {
      *n2ton1 = 0;
      *len = n1->len;
      return n1->e;
    } else {
      *n2ton1 = 1;
      *len = n2->len;
      return n2->e;
    }
  }

  if (lca==n1 || lca==n1->parent || lca==n2) {
    if (lca!=n2) {
      *n2ton1 = 1;
      *len = n2->blen;
      e = n2;
      curr = n2->parent;
    } else {
      *n2ton1 = 0;
      *len = n1->blen;
      e = n1;
      curr = n1->parent;
    }
    while (curr != lca) {
      if (*len < curr->blen) {
	*len = curr->blen;
	e = curr;
      }
      curr = curr->parent;
    }
    return e;
  }

  /* lca is above both n1 and n2 */
  *n2ton1 = 0;
  n1 = n1->parent;
  *len = n1->blen;
  e = n1;
  curr = n1;
  for (i=0; i<2; i++, curr=n2) {
    while (curr != lca) {
      if (*len < curr->blen) {
	if (i>0) {
	  *n2ton1 = 1;
	}
	*len = curr->blen;
	e = curr;
      }
      curr = curr->parent;
    }
  }

  return e;

}

TreeNode *critical_edge(TreeNode* n1, TreeNode* n2, DTYPE *len, int *n2ton1)
{
  if (n1->id != n2->id) {
    n1 = n1->parent;
    if (n1 && (n1->len > n2->len)) {
      *n2ton1 = 0;
      *len = n1->len;
      return n1->e;
    } else {
      *n2ton1 = 1;
      *len = n2->len;
      return n2->e;
    }
  }

  return cedge_lca(n1, n2, len, n2ton1);
}

void splice2(TreeNode *n1, TreeNode *n2, TreeNode *e)
{
  TreeNode *curr, *prev, *next, *s;

  //assert(n2->parent);
  //assert(e->id==n2->id);

  prev = n2;
  curr = n2->parent;
  next = curr->parent;
  while (prev != e) {
    remove_child(curr->children, prev);
    curr->parent = prev;
    dl_append(TreeNode*, prev->children, curr);
    prev = curr;
    curr = next;
    next = curr->parent;
  }
  remove_child(curr->children, prev);

  n2->parent = n1;
  dl_append(TreeNode*, n1->children, n2);

  update_subtree(n1, n1->parent->id);
}

void cut_and_splice(TreeNode *n1, TreeNode *n2,
		    DTYPE new_x, DTYPE new_y,
		    DTYPE *x1, DTYPE *y1, DTYPE *x2, DTYPE *y2,
		    TreeNode *e, int n2ton1)
{
  TreeNode *p1, *node, *s;
  
  /* new steiner node */
  p1 = n1->parent;
  remove_child(p1->children, n1);
  node = (TreeNode*)malloc(sizeof(TreeNode));
  node->x = new_x;
  node->y = new_y;
  node->mark = curr_mark;

  node->parent = p1;
  dl_append(TreeNode*, p1->children, node);
  n1->parent = node;
  node->children = dl_alloc();
  dl_append(TreeNode*, node->children, n1);
  node->order = -1;

  node->e = n1->e;
  node->id = n1->id;

  if (*x1==n1->x) {
    *x2 = new_x;
  } else {
    *x1 = new_x;
  }
  if (*y1==n1->y) {
    *y2 = new_y;
  } else {
    *y1 = new_y;
  }

  if (n2->order >= 0) {
    /* n2 is a pin, need to replicate a steiner node */
    s = n2->parent;
    if (s->x!=n2->x || s->y!=n2->y) {
      s = (TreeNode*)malloc(sizeof(TreeNode));
      s->mark = curr_mark;
      s->order = -1;
      s->id = n2->id;
      s->x = n2->x;
      s->y = n2->y;
      s->e = n2->e;
      if (s->e == n2) {
	s->e = s;
      }
      if (e == n2) {
	e = s;
      }
      s->len = n2->len;
      s->blen = n2->blen;
      n2->blen = 0;

      remove_child(n2->parent->children, n2);
      dl_append(TreeNode*, n2->parent->children, s);
      s->parent = n2->parent;
      n2->parent = s;
      s->children = dl_alloc();
      dl_append(TreeNode*, s->children, n2);
    }
    n2 = s;
  }

  if (n2ton1) {
    splice2(node, n2, e);
  } else {
    splice2(n2, node, e);
  }
}

typedef struct {
  TreeNode *n1, *n2;
  DTYPE min_dist, new_x, new_y;
  int n2ton1;
} splice_info;

DTYPE exchange_branches_order_x(int num_nodes, TreeNode **nodes, 
				DTYPE threshold_x, DTYPE threshold_y,
				DTYPE max_len)
{
  int n2ton1;
  TreeNode *n1, *p1, *n2, *p2, *node, *e, *s;
  DTYPE  x1, x2, y1, y2, min_dist, new_x, new_y, len;
  DTYPE gain=0;
  int i, j, curr_row, next_header, num_rows, start, end, mid;
  int *header=(int*)malloc(sizeof(int)*(num_nodes+1));
  dl_t batch_list=dl_alloc();
  splice_info sinfo;

  int batch_mode = (num_nodes >= D3);

  header[0]=0;

  y1 = nodes[0]->y;
  for (i=num_rows=1; i<num_nodes; i++) {
    if (nodes[i]->y == y1) {
      continue;
    }
    header[num_rows++] = i;
    y1 = nodes[i]->y;
  }
  header[num_rows] = i;

  curr_row = 0;
  next_header = header[1];
  for (i=0; i<num_nodes; i++) {
    if (i >= next_header) {
      curr_row++;
      next_header = header[curr_row+1];
    }
    n1 = nodes[i];
    p1 = n1->parent;
    if (!p1) {
      continue;
    }
    if (p1->x == n1->x && p1->y == n1->y) {
      continue;
    }
    if (n1->x <= p1->x) {
      x1 = n1->x;  x2 = p1->x;
    } else {
      x1 = p1->x;  x2 = n1->x;
    }
    if (n1->y <= p1->y) {
      y1 = n1->y;  y2 = p1->y;
    } else {
      y1 = p1->y;  y2 = n1->y;
    }

    if (curr_row > 0) {
      for (j=curr_row-1; j>0; j--) {
	if (y1 - threshold_y > nodes[header[j]]->y) {
	  j++;
	  break;
	}
      }
    } else {
      j = 0;
    }
    for (;j < num_rows && nodes[header[j]]->y <= y2 + threshold_y; j++) {
      /* find the closest node on row j */
      start = header[j];
      end = header[j+1];
      while (start < end) {
	mid = (start+end)/2;
	if (nodes[mid]->x <= x1) {
	  start = mid + 1;
	} else {
	  end = mid;
	}
      }
      //assert(start==end);

      if (start >= header[j+1]) {
	continue;
      }
      n2 = nodes[start];

      if (batch_mode && n1->id==n2->id) continue;

      if (!n2->parent) {
	continue;
      }

      min_dist = n2->x - x2;

      if (abs(min_dist) > threshold_x) {
	continue;
      } else if (min_dist < 0) {
	min_dist = 0;
	new_x = n2->x;
      } else {
	new_x = x2;
      }
      
      if (n2->y < y1) {
	min_dist += y1 - n2->y;
	new_y = y1;
      } else if (n2->y > y2) {
	min_dist += n2->y - y2;
	new_y = y2;
      } else {
	new_y = n2->y;
      }

      if (min_dist ==0 || min_dist > max_len) {
	continue;
      }

      e = critical_edge(n1, n2, &len, &n2ton1);
      if (min_dist < len && e!=n1) {
	if (batch_mode) {
	  sinfo.n1 = n1;
	  sinfo.n2 = n2;
	  sinfo.min_dist = min_dist;
	  sinfo.new_x = new_x;
	  sinfo.new_y = new_y;
	  sinfo.n2ton1 = n2ton1;
	  dl_append(splice_info, batch_list, sinfo);
	} else {
	  gain += len - min_dist;
	  cut_and_splice(n1, n2, new_x, new_y, &x1, &y1, &x2, &y2, e, n2ton1);
	}
      }
    }
  }

  dl_forall(splice_info, batch_list, sinfo) {
    n1 = sinfo.n1;
    n2 = sinfo.n2;
    n2ton1 = sinfo.n2ton1;
    min_dist = sinfo.min_dist;

    e = critical_edge(n1, n2, &len, &n2ton1);
    if (min_dist < len && e!=n1) {
      gain += len - min_dist;
      cut_and_splice(n1, n2, sinfo.new_x, sinfo.new_y,
		     &x1, &y1, &x2, &y2, e, n2ton1);
    }
  } dl_endfor;

  dl_free(batch_list);

  free(header);

  return gain;
}

DTYPE exchange_branches_order_y(int num_nodes, TreeNode **nodes, 
				DTYPE threshold_x, DTYPE threshold_y,
				DTYPE max_len)
{
  int n2ton1;
  TreeNode *n1, *p1, *n2, *p2, *node, *e, *s;
  DTYPE  x1, x2, y1, y2, min_dist, new_x, new_y, len;
  DTYPE gain=0;
  int i, j, curr_row, next_header, num_rows, start, end, mid;
  int *header=(int*)malloc(sizeof(int)*(num_nodes+1));
  dl_t batch_list=dl_alloc();
  splice_info sinfo;

  int batch_mode = (num_nodes >= D3);

  header[0]=0;

  x1 = nodes[0]->x;
  for (i=num_rows=1; i<num_nodes; i++) {
    if (nodes[i]->x == x1) {
      continue;
    }
    header[num_rows++] = i;
    x1 = nodes[i]->x;
  }
  header[num_rows] = i;

  curr_row = 0;
  next_header = header[1];
  for (i=0; i<num_nodes; i++) {
    if (i >= next_header) {
      curr_row++;
      next_header = header[curr_row+1];
    }
    n1 = nodes[i];
    p1 = n1->parent;
    if (!p1) {
      continue;
    }
    if (p1->x == n1->x && p1->y == n1->y) {
      continue;
    }
    if (n1->x <= p1->x) {
      x1 = n1->x;  x2 = p1->x;
    } else {
      x1 = p1->x;  x2 = n1->x;
    }
    if (n1->y <= p1->y) {
      y1 = n1->y;  y2 = p1->y;
    } else {
      y1 = p1->y;  y2 = n1->y;
    }

    if (curr_row > 0) {
      for (j=curr_row-1; j>0; j--) {
	if (x1 - threshold_x > nodes[header[j]]->x) {
	  j++;
	  break;
	}
      }
    } else {
      j = 0;
    }
    for (;j < num_rows && nodes[header[j]]->x <= x2 + threshold_x; j++) {
      /* find the closest node on row j */
      start = header[j];
      end = header[j+1];
      while (start < end) {
	mid = (start+end)/2;
	if (nodes[mid]->y <= y1) {
	  start = mid + 1;
	} else {
	  end = mid;
	}
      }
      //assert(start==end);
      if (start >= header[j+1]) {
	continue;
      }
      n2 = nodes[start];

      if (batch_mode && n1->id==n2->id) continue;

      if (!n2->parent) {
	continue;
      }

      min_dist = n2->y - y2;

      if (abs(min_dist) > threshold_y) {
	continue;
      } else if (min_dist < 0) {
	min_dist = 0;
	new_y = n2->y;
      } else {
	new_y = y2;
      }
      
      if (n2->x < x1) {
	min_dist += x1 - n2->x;
	new_x = x1;
      } else if (n2->x > x2) {
	min_dist += n2->x - x2;
	new_x = x2;
      } else {
	new_x = n2->x;
      }

      if (min_dist ==0 || min_dist > max_len) {
	continue;
      }

      e = critical_edge(n1, n2, &len, &n2ton1);
      if (min_dist < len && e!=n1) {
	if (batch_mode) {
	  sinfo.n1 = n1;
	  sinfo.n2 = n2;
	  sinfo.min_dist = min_dist;
	  sinfo.new_x = new_x;
	  sinfo.new_y = new_y;
	  sinfo.n2ton1 = n2ton1;
	  dl_append(splice_info, batch_list, sinfo);
	} else {
	  gain += len - min_dist;
	  cut_and_splice(n1, n2, new_x, new_y, &x1, &y1, &x2, &y2, e, n2ton1);
	}
      }
    }
  }

  dl_forall(splice_info, batch_list, sinfo) {
    n1 = sinfo.n1;
    n2 = sinfo.n2;
    n2ton1 = sinfo.n2ton1;
    min_dist = sinfo.min_dist;

    e = critical_edge(n1, n2, &len, &n2ton1);
    if (min_dist < len && e!=n1) {
      gain += len - min_dist;
      cut_and_splice(n1, n2, sinfo.new_x, sinfo.new_y,
		     &x1, &y1, &x2, &y2, e, n2ton1);
    }
  } dl_endfor;

  dl_free(batch_list);

  free(header);

  return gain;
}

/* cross exchange branches after merging */
Tree xmergetree(Tree t1, Tree t2, int *order1, int *order2,
		DTYPE cx, DTYPE cy)
{
  int i, num, cnt, order_by_x=1;
  Tree t;
  TreeNode *tn1, *tn2, *n1, *p1, **nodes;
  dl_t list_of_nodes=dl_alloc();
  DTYPE threshold_x, threshold_y;
  DTYPE min_x, max_x, max_len, len, gain;

  if (t1.deg <= 0) {
    for (i=0; i<t2.deg; i++) {
      order1[i] = order2[i];
    }
    return t2;
  } else if (t2.deg <= 0) {
    return t1;
  }

  redirect(t1, cx, cy);
  redirect(t2, cx, cy);

  curr_mark = 0;
  tn1 = createRootedTree(t1, order1, 1, list_of_nodes);
  tn2 = createRootedTree(t2, order2, 2, list_of_nodes);

  num = dl_length(list_of_nodes);
  nodes = (TreeNode**)malloc(sizeof(TreeNode*)*num);
  i = 0;
  dl_forall(TreeNode*, list_of_nodes, n1) {
    nodes[i++] = n1;
  } dl_endfor;
  dl_clear(list_of_nodes);

  qsort(nodes, num, sizeof(TreeNode*), cmpNodeByYX);

  max_len = 0;
  min_x = max_x = nodes[0]->x;
  for (i=0; i<num; i++) {
    n1 = nodes[i];
    p1 = n1->parent;
    if (p1) {
      len = ADIFF(n1->x, p1->x) + ADIFF(n1->y, p1->y);
      if (len > max_len) {
	max_len = len;
      }
    }
    if (n1->x < min_x) {
      min_x = n1->x;
    } else if (n1->x > max_x) {
      max_x = n1->x;
    }
  }

  threshold_x = (max_x - min_x)/4;
  threshold_y = (nodes[num-1]->y - nodes[0]->y)/4;

  threshold_x = min(threshold_x, max_len);
  threshold_y = min(threshold_y, max_len);

  for (cnt=(t1.deg+t2.deg)/2; cnt>0; cnt--) {
    gain = (order_by_x) ?
      exchange_branches_order_x(num, nodes, threshold_x, threshold_y, max_len):
      exchange_branches_order_y(num, nodes, threshold_x, threshold_y, max_len);

    //assert(gain>=0);

    if (gain <= 0 && !order_by_x) {
       break;
    }
    if (cnt>1) {
      collect_nodes(tn1, list_of_nodes);
      num = dl_length(list_of_nodes);
      if (num <= 1) {
	break;
      }

      collect_nodes(tn2, list_of_nodes);
      if (dl_length(list_of_nodes)-num <= 1) {
	break;
      }

      free(nodes);
      num = dl_length(list_of_nodes);
      nodes = (TreeNode**)malloc(sizeof(TreeNode*)*num);
      i = 0;
      dl_forall(TreeNode*, list_of_nodes, n1) {
	nodes[i++] = n1;
      } dl_endfor;
      dl_clear(list_of_nodes);

      if (order_by_x) {
	order_by_x = 0;
	qsort(nodes, num, sizeof(TreeNode*), cmpNodeByXY);
      } else {
	order_by_x = 1;
	qsort(nodes, num, sizeof(TreeNode*), cmpNodeByYX);
      }
    }
  }

  dl_free(list_of_nodes);
  free(nodes);

  t = mergeRootedTrees(tn1, tn2, order1);

  free(t1.branch);
  free(t2.branch);

  return t;
}



int numgrp[10] = { 0, 0, 0, 0, 6, 30, 180, 1260, 10080, 90720 };

struct csoln {
    unsigned char parent;
    unsigned char seg[11];  // Add: 0..i, Sub: j..10; seg[i+1]=seg[j-1]=0
    unsigned char rowcol[D - 2];  // row = rowcol[]/16, col = rowcol[]%16,
    unsigned char neighbor[2 * D - 2];
};
struct csoln *LUT[D + 1][MGROUP];  // storing 4 .. D
struct csoln *LUT1[MGROUP];
int numsoln[D + 1][MGROUP];

void readLUT();
DTYPE flute_wl(int d, DTYPE x[], DTYPE y[], int acc);
DTYPE flutes_wl_LD(int d, DTYPE xs[], DTYPE ys[], int s[]);
DTYPE flutes_wl_MD(int d, DTYPE xs[], DTYPE ys[], int s[], int acc);
DTYPE flutes_wl_RDP(int d, DTYPE xs[], DTYPE ys[], int s[], int acc);
Tree flute(int d, DTYPE x[], DTYPE y[], int acc);
Tree flutes_LD(int d, DTYPE xs[], DTYPE ys[], int s[]);
Tree flutes_MD(int d, DTYPE xs[], DTYPE ys[], int s[], int acc);
Tree flutes_HD(int d, DTYPE xs[], DTYPE ys[], int s[], int acc);
Tree flutes_RDP(int d, DTYPE xs[], DTYPE ys[], int s[], int acc);
Tree dmergetree(Tree t1, Tree t2);
Tree hmergetree(Tree t1, Tree t2, int s[]);
Tree vmergetree(Tree t1, Tree t2);
void local_refinement(Tree *tp, int p);
DTYPE wirelength(Tree t);
void printtree(Tree t);
void plottree(Tree t);

void readLUT() {
    unsigned char charnum[256], line[32], *linep, c;
    FILE *fpwv, *fprt;
    struct csoln *p;
    int d, i, j, k, kk, ns, nn;

    for (i = 0; i <= 255; i++) {
        if ('0' <= i && i <= '9')
            charnum[i] = i - '0';
        else if (i >= 'A')
            charnum[i] = i - 'A' + 10;
        else
            // if (i=='$' || i=='\n' || ... )
            charnum[i] = 0;
    }

    fpwv = fopen(POWVFILE, "r");
    if (fpwv == NULL) {
        printf("Error in opening %s\n", POWVFILE);
        exit(1);
    }

#if ROUTING==1
    fprt = fopen(POSTFILE, "r");
    if (fprt == NULL) {
        printf("Error in opening %s\n", POSTFILE);
        exit(1);
    }
#endif

    for (d = 4; d <= D; d++) {
        fscanf(fpwv, "d=%d\n", &d);
#if ROUTING==1
        fscanf(fprt, "d=%d\n", &d);
#endif
        for (k = 0; k < numgrp[d]; k++) {
            ns = (int) charnum[fgetc(fpwv)];

            if (ns == 0) {  // same as some previous group
                fscanf(fpwv, "%d\n", &kk);
                numsoln[d][k] = numsoln[d][kk];
                LUT[d][k] = LUT[d][kk];
            } else {
                fgetc(fpwv);  // '\n'
                numsoln[d][k] = ns;
                p = (struct csoln*) malloc(ns * sizeof(struct csoln));
                LUT[d][k] = p;
                for (i = 1; i <= ns; i++) {
                    linep = (unsigned char *) fgets((char *) line, 32, fpwv);
                    p->parent = charnum[*(linep++)];
                    j = 0;
                    while ((p->seg[j++] = charnum[*(linep++)]) != 0)
                        ;
                    j = 10;
                    while ((p->seg[j--] = charnum[*(linep++)]) != 0)
                        ;
#if ROUTING==1
                    nn = 2 * d - 2;
                    fread(line, 1, d - 2, fprt);
                    linep = line;
                    for (j = d; j < nn; j++) {
                        c = charnum[*(linep++)];
                        p->rowcol[j - d] = c;
                    }
                    fread(line, 1, nn / 2 + 1, fprt);
                    linep = line;  // last char \n
                    for (j = 0; j < nn;) {
                        c = *(linep++);
                        p->neighbor[j++] = c / 16;
                        p->neighbor[j++] = c % 16;
                    }
#endif
                    p++;
                }
            }
        }
    }
}

DTYPE flute_wl(int d, DTYPE x[], DTYPE y[], int acc) {
    DTYPE xs[MAXD], ys[MAXD], minval, l, xu, xl, yu, yl;
    int s[MAXD];
    int i, j, k, minidx;
    struct point {
        DTYPE x, y;
        int o;
    } pt[MAXD], *ptp[MAXD], *tmpp;

    if (d == 2)
        l = ADIFF(x[0], x[1]) + ADIFF(y[0], y[1]);
    else if (d == 3) {
        if (x[0] > x[1]) {
            xu = max(x[0], x[2]);
            xl = min(x[1], x[2]);
        } else {
            xu = max(x[1], x[2]);
            xl = min(x[0], x[2]);
        }
        if (y[0] > y[1]) {
            yu = max(y[0], y[2]);
            yl = min(y[1], y[2]);
        } else {
            yu = max(y[1], y[2]);
            yl = min(y[0], y[2]);
        }
        l = (xu - xl) + (yu - yl);
    } else {
        for (i = 0; i < d; i++) {
            pt[i].x = x[i];
            pt[i].y = y[i];
            ptp[i] = &pt[i];
        }

        // sort x
        for (i = 0; i < d - 1; i++) {
            minval = ptp[i]->x;
            minidx = i;
            for (j = i + 1; j < d; j++) {
                if (minval > ptp[j]->x) {
                    minval = ptp[j]->x;
                    minidx = j;
                }
            }
            tmpp = ptp[i];
            ptp[i] = ptp[minidx];
            ptp[minidx] = tmpp;
        }

#if REMOVE_DUPLICATE_PIN==1
        ptp[d] = &pt[d];
        ptp[d]->x = ptp[d]->y = -999999;
        j = 0;
        for (i = 0; i < d; i++) {
            for (k = i + 1; ptp[k]->x == ptp[i]->x; k++)
                if (ptp[k]->y == ptp[i]->y)  // pins k and i are the same
                    break;
            if (ptp[k]->x != ptp[i]->x)
                ptp[j++] = ptp[i];
        }
        d = j;
#endif

        for (i = 0; i < d; i++) {
            xs[i] = ptp[i]->x;
            ptp[i]->o = i;
        }

        // sort y to find s[]
        for (i = 0; i < d - 1; i++) {
            minval = ptp[i]->y;
            minidx = i;
            for (j = i + 1; j < d; j++) {
                if (minval > ptp[j]->y) {
                    minval = ptp[j]->y;
                    minidx = j;
                }
            }
            ys[i] = ptp[minidx]->y;
            s[i] = ptp[minidx]->o;
            ptp[minidx] = ptp[i];
        }
        ys[d - 1] = ptp[d - 1]->y;
        s[d - 1] = ptp[d - 1]->o;

        l = flutes_wl(d, xs, ys, s, acc);
    }
    return l;
}

// xs[] and ys[] are coords in x and y in sorted order
// s[] is a list of nodes in increasing y direction
//   if nodes are indexed in the order of increasing x coord
//   i.e., s[i] = s_i as defined in paper
// The points are (xs[s[i]], ys[i]) for i=0..d-1
//             or (xs[i], ys[si[i]]) for i=0..d-1

DTYPE flutes_wl_RDP(int d, DTYPE xs[], DTYPE ys[], int s[], int acc) {
    int i, j, ss;

    for (i = 0; i < d - 1; i++) {
        if (xs[s[i]] == xs[s[i + 1]] && ys[i] == ys[i + 1]) {
            if (s[i] < s[i + 1])
                ss = s[i + 1];
            else {
                ss = s[i];
                s[i] = s[i + 1];
            }
            for (j = i + 2; j < d; j++) {
                ys[j - 1] = ys[j];
                s[j - 1] = s[j];
            }
            for (j = ss + 1; j < d; j++)
                xs[j - 1] = xs[j];
            for (j = 0; j <= d - 2; j++)
                if (s[j] > ss)
                    s[j]--;
            i--;
            d--;
        }
    }
    return flutes_wl_ALLD(d, xs, ys, s, acc);
}

// For low-degree, i.e., 2 <= d <= D
DTYPE flutes_wl_LD(int d, DTYPE xs[], DTYPE ys[], int s[]) {
    int k, pi, i, j;
    struct csoln *rlist;
    DTYPE dd[2 * D - 2];  // 0..D-2 for v, D-1..2*D-3 for h
    DTYPE minl, sum, l[MPOWV + 1];

    if (d <= 3)
        minl = xs[d - 1] - xs[0] + ys[d - 1] - ys[0];
    else {
        k = 0;
        if (s[0] < s[2])
            k++;
        if (s[1] < s[2])
            k++;

        for (i = 3; i <= d - 1; i++) {  // p0=0 always, skip i=1 for symmetry
            pi = s[i];
            for (j = d - 1; j > i; j--)
                if (s[j] < s[i])
                    pi--;
            k = pi + (i + 1) * k;
        }

        if (k < numgrp[d])  // no horizontal flip
            for (i = 1; i <= d - 3; i++) {
                dd[i] = ys[i + 1] - ys[i];
                dd[d - 1 + i] = xs[i + 1] - xs[i];
            }
        else {
            k = 2 * numgrp[d] - 1 - k;
            for (i = 1; i <= d - 3; i++) {
                dd[i] = ys[i + 1] - ys[i];
                dd[d - 1 + i] = xs[d - 1 - i] - xs[d - 2 - i];
            }
        }

        minl = l[0] = xs[d - 1] - xs[0] + ys[d - 1] - ys[0];
        rlist = LUT[d][k];
        for (i = 0; rlist->seg[i] > 0; i++)
            minl += dd[rlist->seg[i]];

        l[1] = minl;
        j = 2;
        while (j <= numsoln[d][k]) {
            rlist++;
            sum = l[rlist->parent];
            for (i = 0; rlist->seg[i] > 0; i++)
                sum += dd[rlist->seg[i]];
            for (i = 10; rlist->seg[i] > 0; i--)
                sum -= dd[rlist->seg[i]];
            minl = min(minl, sum);
            l[j++] = sum;
        }
    }

    return minl;
}

// For medium-degree, i.e., D+1 <= d
DTYPE flutes_wl_MD(int d, DTYPE xs[], DTYPE ys[], int s[], int acc) {
    DTYPE x1[MAXD], x2[MAXD], y1[MAXD], y2[MAXD];
    int si[MAXD], s1[MAXD], s2[MAXD];
    float score[2 * MAXD], penalty[MAXD], pnlty, dx, dy;
    DTYPE ll, minl, extral;
    int i, r, p, maxbp, nbp, bp, ub, lb, n1, n2, newacc;
    int ms, mins, maxs, minsi, maxsi;
    DTYPE distx[MAXD], disty[MAXD], xydiff;

    if (s[0] < s[d - 1]) {
        ms = max(s[0], s[1]);
        for (i = 2; i <= ms; i++)
            ms = max(ms, s[i]);
        if (ms <= d - 3) {
            for (i = 0; i <= ms; i++) {
                x1[i] = xs[i];
                y1[i] = ys[i];
                s1[i] = s[i];
            }
            x1[ms + 1] = xs[ms];
            y1[ms + 1] = ys[ms];
            s1[ms + 1] = ms + 1;

            s2[0] = 0;
            for (i = 1; i <= d - 1 - ms; i++)
                s2[i] = s[i + ms] - ms;

            return flutes_wl_LMD(ms+2, x1, y1, s1, acc) + flutes_wl_LMD(d - ms, xs + ms, ys + ms, s2, acc);
        }
    } else {  // (s[0] > s[d-1])
        ms = min(s[0], s[1]);
        for (i = 2; i <= d - 1 - ms; i++)
            ms = min(ms, s[i]);
        if (ms >= 2) {
            x1[0] = xs[ms];
            y1[0] = ys[0];
            s1[0] = s[0] - ms + 1;
            for (i = 1; i <= d - 1 - ms; i++) {
                x1[i] = xs[i + ms - 1];
                y1[i] = ys[i];
                s1[i] = s[i] - ms + 1;
            }
            x1[d - ms] = xs[d - 1];
            y1[d - ms] = ys[d - 1 - ms];
            s1[d - ms] = 0;

            s2[0] = ms;
            for (i = 1; i <= ms; i++)
                s2[i] = s[i + d - 1 - ms];

            return flutes_wl_LMD(d+1-ms, x1, y1, s1, acc) + flutes_wl_LMD(ms + 1, xs, ys + d - 1 - ms, s2, acc);
        }
    }

// Find inverse si[] of s[]
    for (r = 0; r < d; r++)
        si[s[r]] = r;

// Determine breaking directions and positions dp[]
    lb = (d - 2 * acc + 2) / 4;
    if (lb < 2)
        lb = 2;
    ub = d - 1 - lb;

// Compute scores    
#define AAWL 0.6
#define BBWL 0.3
    float CCWL = 7.4 / ((d + 10.) * (d - 3.));
    float DDWL = 4.8 / (d - 1);

    // Compute penalty[]    
    dx = CCWL * (xs[d - 2] - xs[1]);
    dy = CCWL * (ys[d - 2] - ys[1]);
    for (r = d / 2, pnlty = 0; r >= 0; r--, pnlty += dx)
        penalty[r] = pnlty, penalty[d - 1 - r] = pnlty;
    for (r = d / 2 - 1, pnlty = dy; r >= 0; r--, pnlty += dy)
        penalty[s[r]] += pnlty, penalty[s[d - 1 - r]] += pnlty;
//#define CCWL 0.16
//    for (r=0; r<d; r++)
//        penalty[r] = abs(d-1-r-r)*dx + abs(d-1-si[r]-si[r])*dy;

    // Compute distx[], disty[]
    xydiff = (xs[d - 1] - xs[0]) - (ys[d - 1] - ys[0]);
    if (s[0] < s[1])
        mins = s[0], maxs = s[1];
    else
        mins = s[1], maxs = s[0];
    if (si[0] < si[1])
        minsi = si[0], maxsi = si[1];
    else
        minsi = si[1], maxsi = si[0];
    for (r = 2; r <= ub; r++) {
        if (s[r] < mins)
            mins = s[r];
        else if (s[r] > maxs)
            maxs = s[r];
        distx[r] = xs[maxs] - xs[mins];
        if (si[r] < minsi)
            minsi = si[r];
        else if (si[r] > maxsi)
            maxsi = si[r];
        disty[r] = ys[maxsi] - ys[minsi] + xydiff;
    }

    if (s[d - 2] < s[d - 1])
        mins = s[d - 2], maxs = s[d - 1];
    else
        mins = s[d - 1], maxs = s[d - 2];
    if (si[d - 2] < si[d - 1])
        minsi = si[d - 2], maxsi = si[d - 1];
    else
        minsi = si[d - 1], maxsi = si[d - 2];
    for (r = d - 3; r >= lb; r--) {
        if (s[r] < mins)
            mins = s[r];
        else if (s[r] > maxs)
            maxs = s[r];
        distx[r] += xs[maxs] - xs[mins];
        if (si[r] < minsi)
            minsi = si[r];
        else if (si[r] > maxsi)
            maxsi = si[r];
        disty[r] += ys[maxsi] - ys[minsi];
    }

    nbp = 0;
    for (r = lb; r <= ub; r++) {
        if (si[r] == 0 || si[r] == d - 1)
            score[nbp] = (xs[r + 1] - xs[r - 1]) - penalty[r] - AAWL * (ys[d - 2] - ys[1]) - DDWL * disty[r];
        else
            score[nbp] = (xs[r + 1] - xs[r - 1]) - penalty[r] - BBWL * (ys[si[r] + 1] - ys[si[r] - 1]) - DDWL * disty[r];
        nbp++;

        if (s[r] == 0 || s[r] == d - 1)
            score[nbp] = (ys[r + 1] - ys[r - 1]) - penalty[s[r]] - AAWL * (xs[d - 2] - xs[1]) - DDWL * distx[r];
        else
            score[nbp] = (ys[r + 1] - ys[r - 1]) - penalty[s[r]] - BBWL * (xs[s[r] + 1] - xs[s[r] - 1]) - DDWL * distx[r];
        nbp++;
    }

    if (acc <= 3)
        newacc = 1;
    else {
        newacc = acc / 2;
        if (acc >= nbp)
            acc = nbp - 1;
    }

    minl = (DTYPE) INT_MAX;
    for (i = 0; i < acc; i++) {
        maxbp = 0;
        for (bp = 1; bp < nbp; bp++)
            if (score[maxbp] < score[bp])
                maxbp = bp;
        score[maxbp] = -9e9;

#define BreakPt(bp) ((bp)/2+lb)
#define BreakInX(bp) ((bp)%2==0)
        p = BreakPt(maxbp);
// Breaking in p
        if (BreakInX(maxbp)) {  // break in x
            n1 = n2 = 0;
            for (r = 0; r < d; r++) {
                if (s[r] < p) {
                    s1[n1] = s[r];
                    y1[n1] = ys[r];
                    n1++;
                } else if (s[r] > p) {
                    s2[n2] = s[r] - p;
                    y2[n2] = ys[r];
                    n2++;
                } else { // if (s[r] == p)  i.e.,  r = si[p]
                    s1[n1] = p;
                    s2[n2] = 0;
                    if (r == d - 1 || r == d - 2) {
                        y1[n1] = y2[n2] = ys[r - 1];
                        extral = ys[r] - ys[r - 1];
                    }
                    if (r == 0 || r == 1) {
                        y1[n1] = y2[n2] = ys[r + 1];
                        extral = ys[r + 1] - ys[r];
                    } else {
                        y1[n1] = y2[n2] = ys[r];
                        extral = 0;
                    }
                    n1++;
                    n2++;
                }
            }
            ll = extral + flutes_wl_LMD(p + 1, xs, y1, s1, newacc) + flutes_wl_LMD(d - p, xs + p, y2, s2, newacc);
        } else {  // if (!BreakInX(maxbp))
            n1 = n2 = 0;
            for (r = 0; r < d; r++) {
                if (si[r] < p) {
                    s1[si[r]] = n1;
                    x1[n1] = xs[r];
                    n1++;
                } else if (si[r] > p) {
                    s2[si[r] - p] = n2;
                    x2[n2] = xs[r];
                    n2++;
                } else { // if (si[r] == p)  i.e.,  r = s[p]
                    s1[p] = n1;
                    s2[0] = n2;
                    if (r == d - 1 || r == d - 2) {
                        x1[n1] = x2[n2] = xs[r - 1];
                        extral = xs[r] - xs[r - 1];
                    }
                    if (r == 0 || r == 1) {
                        x1[n1] = x2[n2] = xs[r + 1];
                        extral = xs[r + 1] - xs[r];
                    } else {
                        x1[n1] = x2[n2] = xs[r];
                        extral = 0;
                    }
                    n1++;
                    n2++;
                }
            }
            ll = extral + flutes_wl_LMD(p + 1, x1, ys, s1, newacc) + flutes_wl_LMD(d - p, x2, ys + p, s2, newacc);
        }
        if (minl > ll)
            minl = ll;
    }
    return minl;
}

Tree flute(int d, DTYPE x[], DTYPE y[], int acc) {
    DTYPE *xs, *ys, minval;
    int *s;
    int i, j, k, minidx;
    struct point {
        DTYPE x, y;
        int o;
    } *pt, **ptp, *tmpp;
    Tree t;

    if (d == 2) {
        t.deg = 2;
        t.length = ADIFF(x[0], x[1]) + ADIFF(y[0], y[1]);
        t.branch = (Branch *) malloc(2 * sizeof(Branch));
        t.branch[0].x = x[0];
        t.branch[0].y = y[0];
        t.branch[0].n = 1;
        t.branch[1].x = x[1];
        t.branch[1].y = y[1];
        t.branch[1].n = 1;
    } else {
	xs = (DTYPE *)malloc(sizeof(DTYPE)*(d));
	ys = (DTYPE *)malloc(sizeof(DTYPE)*(d));
	s = (int *)malloc(sizeof(int)*(d));
	pt= (struct point *)malloc(sizeof(struct point)*(d+1));
	ptp= (struct point **)malloc(sizeof(struct point)*(d+1));
        for (i = 0; i < d; i++) {
            pt[i].x = x[i];
            pt[i].y = y[i];
            ptp[i] = &pt[i];
        }

        // sort x
        for (i = 0; i < d - 1; i++) {
            minval = ptp[i]->x;
            minidx = i;
            for (j = i + 1; j < d; j++) {
                if (minval > ptp[j]->x) {
                    minval = ptp[j]->x;
                    minidx = j;
                }
            }
            tmpp = ptp[i];
            ptp[i] = ptp[minidx];
            ptp[minidx] = tmpp;
        }

#if REMOVE_DUPLICATE_PIN==1
        ptp[d] = &pt[d];
        ptp[d]->x = ptp[d]->y = -999999;
        j = 0;
        for (i = 0; i < d; i++) {
            for (k = i + 1; ptp[k]->x == ptp[i]->x; k++)
                if (ptp[k]->y == ptp[i]->y)  // pins k and i are the same
                    break;
            if (ptp[k]->x != ptp[i]->x)
                ptp[j++] = ptp[i];
        }
        d = j;
#endif

        for (i = 0; i < d; i++) {
            xs[i] = ptp[i]->x;
            ptp[i]->o = i;
        }

        // sort y to find s[]
        for (i = 0; i < d - 1; i++) {
            minval = ptp[i]->y;
            minidx = i;
            for (j = i + 1; j < d; j++) {
                if (minval > ptp[j]->y) {
                    minval = ptp[j]->y;
                    minidx = j;
                }
            }
            ys[i] = ptp[minidx]->y;
            s[i] = ptp[minidx]->o;
            ptp[minidx] = ptp[i];
        }
        ys[d - 1] = ptp[d - 1]->y;
        s[d - 1] = ptp[d - 1]->o;

        t = flutes(d, xs, ys, s, acc);
	free(xs);
	free(ys);
	free(s);
	free(pt);
	free(ptp);
    }
    return t;
}

// xs[] and ys[] are coords in x and y in sorted order
// s[] is a list of nodes in increasing y direction
//   if nodes are indexed in the order of increasing x coord
//   i.e., s[i] = s_i as defined in paper
// The points are (xs[s[i]], ys[i]) for i=0..d-1
//             or (xs[i], ys[si[i]]) for i=0..d-1

Tree flutes_RDP(int d, DTYPE xs[], DTYPE ys[], int s[], int acc) {
    int i, j, ss;

    for (i = 0; i < d - 1; i++) {
        if (xs[s[i]] == xs[s[i + 1]] && ys[i] == ys[i + 1]) {
            if (s[i] < s[i + 1])
                ss = s[i + 1];
            else {
                ss = s[i];
                s[i] = s[i + 1];
            }
            for (j = i + 2; j < d; j++) {
                ys[j - 1] = ys[j];
                s[j - 1] = s[j];
            }
            for (j = ss + 1; j < d; j++)
                xs[j - 1] = xs[j];
            for  (j = 0; j <= d - 2; j++)
                if (s[j] > ss)
                    s[j]--;
            i--;
            d--;
        }
    }
    return flutes_ALLD(d, xs, ys, s, acc);
}

// For low-degree, i.e., 2 <= d <= D
Tree flutes_LD(int d, DTYPE xs[], DTYPE ys[], int s[]) {
    int k, pi, i, j;
    struct csoln *rlist, *bestrlist;
    DTYPE dd[2 * D - 2];  // 0..D-2 for v, D-1..2*D-3 for h
    DTYPE minl, sum, l[MPOWV + 1];
    int hflip;
    Tree t;

    t.deg = d;
    t.branch = (Branch *) malloc((2 * d - 2) * sizeof(Branch));
    if (d == 2) {
        minl = xs[1] - xs[0] + ys[1] - ys[0];
        t.branch[0].x = xs[s[0]];
        t.branch[0].y = ys[0];
        t.branch[0].n = 1;
        t.branch[1].x = xs[s[1]];
        t.branch[1].y = ys[1];
        t.branch[1].n = 1;
    } else if (d == 3) {
        minl = xs[2] - xs[0] + ys[2] - ys[0];
        t.branch[0].x = xs[s[0]];
        t.branch[0].y = ys[0];
        t.branch[0].n = 3;
        t.branch[1].x = xs[s[1]];
        t.branch[1].y = ys[1];
        t.branch[1].n = 3;
        t.branch[2].x = xs[s[2]];
        t.branch[2].y = ys[2];
        t.branch[2].n = 3;
        t.branch[3].x = xs[1];
        t.branch[3].y = ys[1];
        t.branch[3].n = 3;
    } else {
        k = 0;
        if (s[0] < s[2])
            k++;
        if (s[1] < s[2])
            k++;

        for (i = 3; i <= d - 1; i++) {  // p0=0 always, skip i=1 for symmetry
            pi = s[i];
            for (j = d - 1; j > i; j--)
                if (s[j] < s[i])
                    pi--;
            k = pi + (i + 1) * k;
        }

        if (k < numgrp[d]) { // no horizontal flip
            hflip = 0;
            for (i = 1; i <= d - 3; i++) {
                dd[i] = ys[i + 1] - ys[i];
                dd[d - 1 + i] = xs[i + 1] - xs[i];
            }
        } else {
            hflip = 1;
            k = 2 * numgrp[d] - 1 - k;
            for (i = 1; i <= d - 3; i++) {
                dd[i] = ys[i + 1] - ys[i];
                dd[d - 1 + i] = xs[d - 1 - i] - xs[d - 2 - i];
            }
        }

        minl = l[0] = xs[d - 1] - xs[0] + ys[d - 1] - ys[0];
        rlist = LUT[d][k];
        for (i = 0; rlist->seg[i] > 0; i++)
            minl += dd[rlist->seg[i]];
        bestrlist = rlist;
        l[1] = minl;
        j = 2;
        while (j <= numsoln[d][k]) {
            rlist++;
            sum = l[rlist->parent];
            for (i = 0; rlist->seg[i] > 0; i++)
                sum += dd[rlist->seg[i]];
            for (i = 10; rlist->seg[i] > 0; i--)
                sum -= dd[rlist->seg[i]];
            if (sum < minl) {
                minl = sum;
                bestrlist = rlist;
            }
            l[j++] = sum;
        }

        t.branch[0].x = xs[s[0]];
        t.branch[0].y = ys[0];
        t.branch[1].x = xs[s[1]];
        t.branch[1].y = ys[1];
        for (i = 2; i < d - 2; i++) {
            t.branch[i].x = xs[s[i]];
            t.branch[i].y = ys[i];
            t.branch[i].n = bestrlist->neighbor[i];
        }
        t.branch[d - 2].x = xs[s[d - 2]];
        t.branch[d - 2].y = ys[d - 2];
        t.branch[d - 1].x = xs[s[d - 1]];
        t.branch[d - 1].y = ys[d - 1];
        if (hflip) {
            if (s[1] < s[0]) {
                t.branch[0].n = bestrlist->neighbor[1];
                t.branch[1].n = bestrlist->neighbor[0];
            } else {
                t.branch[0].n = bestrlist->neighbor[0];
                t.branch[1].n = bestrlist->neighbor[1];
            }
            if (s[d - 1] < s[d - 2]) {
                t.branch[d - 2].n = bestrlist->neighbor[d - 1];
                t.branch[d - 1].n = bestrlist->neighbor[d - 2];
            } else {
                t.branch[d - 2].n = bestrlist->neighbor[d - 2];
                t.branch[d - 1].n = bestrlist->neighbor[d - 1];
            }
            for (i = d; i < 2 * d - 2; i++) {
                t.branch[i].x = xs[d - 1 - bestrlist->rowcol[i - d] % 16];
                t.branch[i].y = ys[bestrlist->rowcol[i - d] / 16];
                t.branch[i].n = bestrlist->neighbor[i];
            }
        } else {  // !hflip
            if (s[0] < s[1]) {
                t.branch[0].n = bestrlist->neighbor[1];
                t.branch[1].n = bestrlist->neighbor[0];
            } else {
                t.branch[0].n = bestrlist->neighbor[0];
                t.branch[1].n = bestrlist->neighbor[1];
            }
            if (s[d - 2] < s[d - 1]) {
                t.branch[d - 2].n = bestrlist->neighbor[d - 1];
                t.branch[d - 1].n = bestrlist->neighbor[d - 2];
            } else {
                t.branch[d - 2].n = bestrlist->neighbor[d - 2];
                t.branch[d - 1].n = bestrlist->neighbor[d - 1];
            }
            for (i = d; i < 2 * d - 2; i++) {
                t.branch[i].x = xs[bestrlist->rowcol[i - d] % 16];
                t.branch[i].y = ys[bestrlist->rowcol[i - d] / 16];
                t.branch[i].n = bestrlist->neighbor[i];
            }
        }
    }
    t.length = minl;

    return t;
}

// For medium-degree, i.e., D+1 <= d
Tree flutes_MD(int d, DTYPE xs[], DTYPE ys[], int s[], int acc) {
    DTYPE x1[MAXD], x2[MAXD], y1[MAXD], y2[MAXD];
    int si[MAXD], s1[MAXD], s2[MAXD];
    float score[2 * MAXD], penalty[MAXD], pnlty, dx, dy;
    DTYPE ll, minl, coord1, coord2;
    int i, r, p, maxbp, bestbp, bp, nbp, ub, lb, n1, n2, nn1, nn2, newacc;
    Tree t, t1, t2, bestt1, bestt2;
    int ms, mins, maxs, minsi, maxsi;
    DTYPE distx[MAXD], disty[MAXD], xydiff;

    if (s[0] < s[d - 1]) {
        ms = max(s[0], s[1]);
        for (i = 2; i <= ms; i++)
            ms = max(ms, s[i]);
        if (ms <= d - 3) {
            for (i = 0; i <= ms; i++) {
                x1[i] = xs[i];
                y1[i] = ys[i];
                s1[i] = s[i];
            }
            x1[ms + 1] = xs[ms];
            y1[ms + 1] = ys[ms];
            s1[ms + 1] = ms + 1;

            s2[0] = 0;
            for (i = 1; i <= d - 1 - ms; i++)
                s2[i] = s[i + ms] - ms;

            t1 = flutes_LMD(ms + 2, x1, y1, s1, acc);
            t2 = flutes_LMD(d - ms, xs + ms, ys + ms, s2, acc);
            t = dmergetree(t1, t2);
            free(t1.branch);
            free(t2.branch);

            return t;
        }
    } else {  // (s[0] > s[d-1])
        ms = min(s[0], s[1]);
        for (i = 2; i <= d - 1 - ms; i++)
            ms = min(ms, s[i]);
        if (ms >= 2) {
            x1[0] = xs[ms];
            y1[0] = ys[0];
            s1[0] = s[0] - ms + 1;
            for (i = 1; i <= d - 1 - ms; i++) {
                x1[i] = xs[i + ms - 1];
                y1[i] = ys[i];
                s1[i] = s[i] - ms + 1;
            }
            x1[d - ms] = xs[d - 1];
            y1[d - ms] = ys[d - 1 - ms];
            s1[d - ms] = 0;

            s2[0] = ms;
            for (i = 1; i <= ms; i++)
                s2[i] = s[i + d - 1 - ms];

            t1 = flutes_LMD(d + 1 - ms, x1, y1, s1, acc);
            t2 = flutes_LMD(ms + 1, xs, ys + d - 1 - ms, s2, acc);
            t = dmergetree(t1, t2);
            free(t1.branch);
            free(t2.branch);

            return t;
        }
    }

// Find inverse si[] of s[]
    for (r = 0; r < d; r++)
        si[s[r]] = r;

// Determine breaking directions and positions dp[]
    lb = (d - 2 * acc + 2) / 4;
    if (lb < 2)
        lb = 2;
    ub = d - 1 - lb;

// Compute scores    
#define AA 0.6  // 2.0*BB
#define BB 0.3
    float CC = 7.4 / ((d + 10.) * (d - 3.));
    float DD = 4.8 / (d - 1);

    // Compute penalty[]    
    dx = CC * (xs[d - 2] - xs[1]);
    dy = CC * (ys[d - 2] - ys[1]);
    for (r = d / 2, pnlty = 0; r >= 2; r--, pnlty += dx)
        penalty[r] = pnlty, penalty[d - 1 - r] = pnlty;
    penalty[1] = pnlty, penalty[d - 2] = pnlty;
    penalty[0] = pnlty, penalty[d - 1] = pnlty;
    for (r = d / 2 - 1, pnlty = dy; r >= 2; r--, pnlty += dy)
        penalty[s[r]] += pnlty, penalty[s[d - 1 - r]] += pnlty;
    penalty[s[1]] += pnlty, penalty[s[d - 2]] += pnlty;
    penalty[s[0]] += pnlty, penalty[s[d - 1]] += pnlty;
//#define CC 0.16
//#define v(r) ((r==0||r==1||r==d-2||r==d-1) ? d-3 : abs(d-1-r-r))
//    for (r=0; r<d; r++)
//        penalty[r] = v(r)*dx + v(si[r])*dy;

    // Compute distx[], disty[]
    xydiff = (xs[d - 1] - xs[0]) - (ys[d - 1] - ys[0]);
    if (s[0] < s[1])
        mins = s[0], maxs = s[1];
    else
        mins = s[1], maxs = s[0];
    if (si[0] < si[1])
        minsi = si[0], maxsi = si[1];
    else
        minsi = si[1], maxsi = si[0];
    for (r = 2; r <= ub; r++) {
        if (s[r] < mins)
            mins = s[r];
        else if (s[r] > maxs)
            maxs = s[r];
        distx[r] = xs[maxs] - xs[mins];
        if (si[r] < minsi)
            minsi = si[r];
        else if (si[r] > maxsi)
            maxsi = si[r];
        disty[r] = ys[maxsi] - ys[minsi] + xydiff;
    }

    if (s[d - 2] < s[d - 1])
        mins = s[d - 2], maxs = s[d - 1];
    else
        mins = s[d - 1], maxs = s[d - 2];
    if (si[d - 2] < si[d - 1])
        minsi = si[d - 2], maxsi = si[d - 1];
    else
        minsi = si[d - 1], maxsi = si[d - 2];
    for (r = d - 3; r >= lb; r--) {
        if (s[r] < mins)
            mins = s[r];
        else if (s[r] > maxs)
            maxs = s[r];
        distx[r] += xs[maxs] - xs[mins];
        if (si[r] < minsi)
            minsi = si[r];
        else if (si[r] > maxsi)
            maxsi = si[r];
        disty[r] += ys[maxsi] - ys[minsi];
    }

    nbp = 0;
    for (r = lb; r <= ub; r++) {
        if (si[r] <= 1)
            score[nbp] = (xs[r + 1] - xs[r - 1]) - penalty[r] - AA * (ys[2] - ys[1]) - DD * disty[r];
        else if (si[r] >= d - 2)
            score[nbp] = (xs[r + 1] - xs[r - 1]) - penalty[r] - AA * (ys[d - 2] - ys[d - 3]) - DD * disty[r];
        else
            score[nbp] = (xs[r + 1] - xs[r - 1]) - penalty[r] - BB * (ys[si[r] + 1] - ys[si[r] - 1]) - DD * disty[r];
        nbp++;

        if (s[r] <= 1)
            score[nbp] = (ys[r + 1] - ys[r - 1]) - penalty[s[r]] - AA * (xs[2] - xs[1]) - DD * distx[r];
        else if (s[r] >= d - 2)
            score[nbp] = (ys[r + 1] - ys[r - 1]) - penalty[s[r]] - AA * (xs[d - 2] - xs[d - 3]) - DD * distx[r];
        else
            score[nbp] = (ys[r + 1] - ys[r - 1]) - penalty[s[r]] - BB * (xs[s[r] + 1] - xs[s[r] - 1]) - DD * distx[r];
        nbp++;
    }

    if (acc <= 3)
        newacc = 1;
    else {
        newacc = acc / 2;
        if (acc >= nbp)
            acc = nbp - 1;
    }

    minl = (DTYPE) INT_MAX;
    bestt1.branch = bestt2.branch = NULL;
    for (i = 0; i < acc; i++) {
        maxbp = 0;
        for (bp = 1; bp < nbp; bp++)
            if (score[maxbp] < score[bp])
                maxbp = bp;
        score[maxbp] = -9e9;

#define BreakPt(bp) ((bp)/2+lb)
#define BreakInX(bp) ((bp)%2==0)
        p = BreakPt(maxbp);
// Breaking in p
        if (BreakInX(maxbp)) {  // break in x
            n1 = n2 = 0;
            for (r = 0; r < d; r++) {
                if (s[r] < p) {
                    s1[n1] = s[r];
                    y1[n1] = ys[r];
                    n1++;
                } else if (s[r] > p) {
                    s2[n2] = s[r] - p;
                    y2[n2] = ys[r];
                    n2++;
                } else { // if (s[r] == p)  i.e.,  r = si[p]
                    s1[n1] = p;
                    s2[n2] = 0;
                    y1[n1] = y2[n2] = ys[r];
                    nn1 = n1;
                    nn2 = n2;
                    n1++;
                    n2++;
                }
            }

            t1 = flutes_LMD(p + 1, xs, y1, s1, newacc);
            t2 = flutes_LMD(d - p, xs + p, y2, s2, newacc);
            ll = t1.length + t2.length;
            coord1 = t1.branch[t1.branch[nn1].n].y;
            coord2 = t2.branch[t2.branch[nn2].n].y;
            if (t2.branch[nn2].y > max(coord1, coord2))
                ll -= t2.branch[nn2].y - max(coord1, coord2);
            else if (t2.branch[nn2].y < min(coord1, coord2))
                ll -= min(coord1, coord2) - t2.branch[nn2].y;
        } else {  // if (!BreakInX(maxbp))
            n1 = n2 = 0;
            for (r = 0; r < d; r++) {
                if (si[r] < p) {
                    s1[si[r]] = n1;
                    x1[n1] = xs[r];
                    n1++;
                } else if (si[r] > p) {
                    s2[si[r] - p] = n2;
                    x2[n2] = xs[r];
                    n2++;
                } else { // if (si[r] == p)  i.e.,  r = s[p]
                    s1[p] = n1;
                    s2[0] = n2;
                    x1[n1] = x2[n2] = xs[r];
                    n1++;
                    n2++;
                }
            }

            t1 = flutes_LMD(p + 1, x1, ys, s1, newacc);
            t2 = flutes_LMD(d - p, x2, ys + p, s2, newacc);
            ll = t1.length + t2.length;
            coord1 = t1.branch[t1.branch[p].n].x;
            coord2 = t2.branch[t2.branch[0].n].x;
            if (t2.branch[0].x > max(coord1, coord2))
                ll -= t2.branch[0].x - max(coord1, coord2);
            else if (t2.branch[0].x < min(coord1, coord2))
                ll -= min(coord1, coord2) - t2.branch[0].x;
        }
        if (minl > ll) {
            minl = ll;
            free(bestt1.branch);
            free(bestt2.branch);
            bestt1 = t1;
            bestt2 = t2;
            bestbp = maxbp;
        } else {
            free(t1.branch);
            free(t2.branch);
        }
    }

#if LOCAL_REFINEMENT==1
    if (BreakInX(bestbp)) {
        t = hmergetree(bestt1, bestt2, s);
        local_refinement(&t, si[BreakPt(bestbp)]);
    } else {
        t = vmergetree(bestt1, bestt2);
        local_refinement(&t, BreakPt(bestbp));
    }
#else
    if (BreakInX(bestbp)) {
        t = hmergetree(bestt1, bestt2, s);
    } else {
        t = vmergetree(bestt1, bestt2);
    }
#endif

    free(bestt1.branch);
    free(bestt2.branch);

    return t;
}

Tree dmergetree(Tree t1, Tree t2) {
    int i, d, prev, curr, next, offset1, offset2;
    Tree t;

    t.deg = d = t1.deg + t2.deg - 2;
    t.length = t1.length + t2.length;
    t.branch = (Branch *) malloc((2 * d - 2) * sizeof(Branch));
    offset1 = t2.deg - 2;
    offset2 = 2 * t1.deg - 4;

    for (i = 0; i <= t1.deg - 2; i++) {
        t.branch[i].x = t1.branch[i].x;
        t.branch[i].y = t1.branch[i].y;
        t.branch[i].n = t1.branch[i].n + offset1;
    }
    for (i = t1.deg - 1; i <= d - 1; i++) {
        t.branch[i].x = t2.branch[i - t1.deg + 2].x;
        t.branch[i].y = t2.branch[i - t1.deg + 2].y;
        t.branch[i].n = t2.branch[i - t1.deg + 2].n + offset2;
    }
    for (i = d; i <= d + t1.deg - 3; i++) {
        t.branch[i].x = t1.branch[i - offset1].x;
        t.branch[i].y = t1.branch[i - offset1].y;
        t.branch[i].n = t1.branch[i - offset1].n + offset1;
    }
    for (i = d + t1.deg - 2; i <= 2 * d - 3; i++) {
        t.branch[i].x = t2.branch[i - offset2].x;
        t.branch[i].y = t2.branch[i - offset2].y;
        t.branch[i].n = t2.branch[i - offset2].n + offset2;
    }

    prev = t2.branch[0].n + offset2;
    curr = t1.branch[t1.deg - 1].n + offset1;
    next = t.branch[curr].n;
    while (curr != next) {
        t.branch[curr].n = prev;
        prev = curr;
        curr = next;
        next = t.branch[curr].n;
    }
    t.branch[curr].n = prev;

    return t;
}

Tree hmergetree(Tree t1, Tree t2, int s[]) {
    int i, prev, curr, next, extra, offset1, offset2;
    int p, ii, n1, n2, nn1, nn2;
    DTYPE coord1, coord2;
    Tree t;

    t.deg = t1.deg + t2.deg - 1;
    t.length = t1.length + t2.length;
    t.branch = (Branch *) malloc((2 * t.deg - 2) * sizeof(Branch));
    offset1 = t2.deg - 1;
    offset2 = 2 * t1.deg - 3;

    p = t1.deg - 1;
    n1 = n2 = 0;
    for (i = 0; i < t.deg; i++) {
        if (s[i] < p) {
            t.branch[i].x = t1.branch[n1].x;
            t.branch[i].y = t1.branch[n1].y;
            t.branch[i].n = t1.branch[n1].n + offset1;
            n1++;
        } else if (s[i] > p) {
            t.branch[i].x = t2.branch[n2].x;
            t.branch[i].y = t2.branch[n2].y;
            t.branch[i].n = t2.branch[n2].n + offset2;
            n2++;
        } else {
            t.branch[i].x = t2.branch[n2].x;
            t.branch[i].y = t2.branch[n2].y;
            t.branch[i].n = t2.branch[n2].n + offset2;
            nn1 = n1;
            nn2 = n2;
            ii = i;
            n1++;
            n2++;
        }
    }
    for (i = t.deg; i <= t.deg + t1.deg - 3; i++) {
        t.branch[i].x = t1.branch[i - offset1].x;
        t.branch[i].y = t1.branch[i - offset1].y;
        t.branch[i].n = t1.branch[i - offset1].n + offset1;
    }
    for (i = t.deg + t1.deg - 2; i <= 2 * t.deg - 4; i++) {
        t.branch[i].x = t2.branch[i - offset2].x;
        t.branch[i].y = t2.branch[i - offset2].y;
        t.branch[i].n = t2.branch[i - offset2].n + offset2;
    }
    extra = 2 * t.deg - 3;
    coord1 = t1.branch[t1.branch[nn1].n].y;
    coord2 = t2.branch[t2.branch[nn2].n].y;
    if (t2.branch[nn2].y > max(coord1, coord2)) {
        t.branch[extra].y = max(coord1, coord2);
        t.length -= t2.branch[nn2].y - t.branch[extra].y;
    } else if (t2.branch[nn2].y < min(coord1, coord2)) {
        t.branch[extra].y = min(coord1, coord2);
        t.length -= t.branch[extra].y - t2.branch[nn2].y;
    } else
        t.branch[extra].y = t2.branch[nn2].y;
    t.branch[extra].x = t2.branch[nn2].x;
    t.branch[extra].n = t.branch[ii].n;
    t.branch[ii].n = extra;

    prev = extra;
    curr = t1.branch[nn1].n + offset1;
    next = t.branch[curr].n;
    while (curr != next) {
        t.branch[curr].n = prev;
        prev = curr;
        curr = next;
        next = t.branch[curr].n;
    }
    t.branch[curr].n = prev;

    return t;
}

Tree vmergetree(Tree t1, Tree t2) {
    int i, prev, curr, next, extra, offset1, offset2;
    DTYPE coord1, coord2;
    Tree t;

    t.deg = t1.deg + t2.deg - 1;
    t.length = t1.length + t2.length;
    t.branch = (Branch *) malloc((2 * t.deg - 2) * sizeof(Branch));
    offset1 = t2.deg - 1;
    offset2 = 2 * t1.deg - 3;

    for (i = 0; i <= t1.deg - 2; i++) {
        t.branch[i].x = t1.branch[i].x;
        t.branch[i].y = t1.branch[i].y;
        t.branch[i].n = t1.branch[i].n + offset1;
    }
    for (i = t1.deg - 1; i <= t.deg - 1; i++) {
        t.branch[i].x = t2.branch[i - t1.deg + 1].x;
        t.branch[i].y = t2.branch[i - t1.deg + 1].y;
        t.branch[i].n = t2.branch[i - t1.deg + 1].n + offset2;
    }
    for (i = t.deg; i <= t.deg + t1.deg - 3; i++) {
        t.branch[i].x = t1.branch[i - offset1].x;
        t.branch[i].y = t1.branch[i - offset1].y;
        t.branch[i].n = t1.branch[i - offset1].n + offset1;
    }
    for (i = t.deg + t1.deg - 2; i <= 2 * t.deg - 4; i++) {
        t.branch[i].x = t2.branch[i - offset2].x;
        t.branch[i].y = t2.branch[i - offset2].y;
        t.branch[i].n = t2.branch[i - offset2].n + offset2;
    }
    extra = 2 * t.deg - 3;
    coord1 = t1.branch[t1.branch[t1.deg - 1].n].x;
    coord2 = t2.branch[t2.branch[0].n].x;
    if (t2.branch[0].x > max(coord1, coord2)) {
        t.branch[extra].x = max(coord1, coord2);
        t.length -= t2.branch[0].x - t.branch[extra].x;
    } else if (t2.branch[0].x < min(coord1, coord2)) {
        t.branch[extra].x = min(coord1, coord2);
        t.length -= t.branch[extra].x - t2.branch[0].x;
    } else
        t.branch[extra].x = t2.branch[0].x;
    t.branch[extra].y = t2.branch[0].y;
    t.branch[extra].n = t.branch[t1.deg - 1].n;
    t.branch[t1.deg - 1].n = extra;

    prev = extra;
    curr = t1.branch[t1.deg - 1].n + offset1;
    next = t.branch[curr].n;
    while (curr != next) {
        t.branch[curr].n = prev;
        prev = curr;
        curr = next;
        next = t.branch[curr].n;
    }
    t.branch[curr].n = prev;

    return t;
}

void local_refinement(Tree *tp, int p) {
    int d, dd, i, ii, j, prev, curr, next, root;
    int SteinerPin[2 * MAXD], index[2 * MAXD];
    DTYPE x[MAXD], xs[D], ys[D];
    int ss[D];
    Tree tt;

    d = tp->deg;
    root = tp->branch[p].n;

// Reverse edges to point to root    
    prev = root;
    curr = tp->branch[prev].n;
    next = tp->branch[curr].n;
    while (curr != next) {
        tp->branch[curr].n = prev;
        prev = curr;
        curr = next;
        next = tp->branch[curr].n;
    }
    tp->branch[curr].n = prev;
    tp->branch[root].n = root;

// Find Steiner nodes that are at pins
    for (i = d; i <= 2 * d - 3; i++)
        SteinerPin[i] = -1;
    for (i = 0; i < d; i++) {
        next = tp->branch[i].n;
        if (tp->branch[i].x == tp->branch[next].x && tp->branch[i].y == tp->branch[next].y)
            SteinerPin[next] = i; // Steiner 'next' at Pin 'i'
    }
    SteinerPin[root] = p;

// Find pins that are directly connected to root    
    dd = 0;
    for (i = 0; i < d; i++) {
        curr = tp->branch[i].n;
        if (SteinerPin[curr] == i)
            curr = tp->branch[curr].n;
        while (SteinerPin[curr] < 0)
            curr = tp->branch[curr].n;
        if (curr == root) {
            x[dd] = tp->branch[i].x;
            if (SteinerPin[tp->branch[i].n] == i && tp->branch[i].n != root)
                index[dd++] = tp->branch[i].n;  // Steiner node
            else
                index[dd++] = i;  // Pin
        }
    }

    if (4 <= dd && dd <= D) {
// Find Steiner nodes that are directly connected to root    
        ii = dd;
        for (i = 0; i < dd; i++) {
            curr = tp->branch[index[i]].n;
            while (SteinerPin[curr] < 0) {
                index[ii++] = curr;
                SteinerPin[curr] = INT_MAX;
                curr = tp->branch[curr].n;
            }
        }
        index[ii] = root;

        for (ii = 0; ii < dd; ii++) {
            ss[ii] = 0;
            for (j = 0; j < ii; j++)
                if (x[j] < x[ii])
                    ss[ii]++;
            for (j = ii + 1; j < dd; j++)
                if (x[j] <= x[ii])
                    ss[ii]++;
            xs[ss[ii]] = x[ii];
            ys[ii] = tp->branch[index[ii]].y;
        }

        tt = flutes_LD(dd, xs, ys, ss);

// Find new wirelength
        tp->length += tt.length;
        for (ii = 0; ii < 2 * dd - 3; ii++) {
            i = index[ii];
            j = tp->branch[i].n;
            tp->length -= ADIFF(tp->branch[i].x, tp->branch[j].x) + ADIFF(tp->branch[i].y, tp->branch[j].y);
        }

// Copy tt into t
        for (ii = 0; ii < dd; ii++) {
            tp->branch[index[ii]].n = index[tt.branch[ii].n];
        }
        for (; ii <= 2 * dd - 3; ii++) {
            tp->branch[index[ii]].x = tt.branch[ii].x;
            tp->branch[index[ii]].y = tt.branch[ii].y;
            tp->branch[index[ii]].n = index[tt.branch[ii].n];
        }
        free(tt.branch);
    }

    return;
}

DTYPE wirelength(Tree t) {
    int i, j;
    DTYPE l = 0;

    for (i = 0; i < 2 * t.deg - 2; i++) {
        j = t.branch[i].n;
        l += ADIFF(t.branch[i].x, t.branch[j].x) + ADIFF(t.branch[i].y, t.branch[j].y);
    }

    return l;
}

void printtree(Tree t) {
    int i;

    for (i = 0; i < t.deg; i++)
        printf(" %-2d:  x=%4g  y=%4g  e=%d\n", i, (float) t.branch[i].x, (float) t.branch[i].y, t.branch[i].n);
    for (i = t.deg; i < 2 * t.deg - 2; i++)
        printf("s%-2d:  x=%4g  y=%4g  e=%d\n", i, (float) t.branch[i].x, (float) t.branch[i].y, t.branch[i].n);
    printf("\n");
}

// Output in a format that can be plotted by gnuplot
void plottree(Tree t) {
    int i;

    for (i = 0; i < 2 * t.deg - 2; i++) {
        printf("%d %d\n", static_cast<int>(t.branch[i].x), static_cast<int>(t.branch[i].y));
        printf("%d %d\n\n", static_cast<int>(t.branch[t.branch[i].n].x), static_cast<int>(t.branch[t.branch[i].n].y));
    }
}
