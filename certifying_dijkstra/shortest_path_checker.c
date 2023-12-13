// shortest_path_checker.c
// Anonymous Authors
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include "shortest_path_checker.h"

#define HEAP_MAX 500000

#define parent(i) ((i - 1) / 2)
#define left_child(i) (2 * i + 1)
#define right_child(i) (2 * i + 2)

// adjacency list implementation

typedef struct node {
    unsigned int second;
    unsigned int edge_id;
    struct node *next;
} Node;

// Internal priority queue

typedef struct pq_elem {
    unsigned int index;
    EInt value;
} PQ_Element;

void swap(PQ_Element *x, PQ_Element *y) {
    PQ_Element temp = *x;
    *x = *y;
    *y = temp;
}

int EInt_lt(EInt x, EInt y) {
    if(x.isInf || (x.isInf && y.isInf)) return 0;
    if(y.isInf) return 1;
    return x.val < y.val;
}

int EInt_gt(EInt x, EInt y) {
    return EInt_lt(y, x);
}

void enqueue(PQ_Element a[], PQ_Element data, unsigned int *n) {
    if(*n >= HEAP_MAX) {
        fprintf(stderr, "FAILURE: PQ reached maximum elements!\n");
        return;
    }
    a[*n] = data;
    *n = *n + 1;
    unsigned int i = *n - 1;
    while(i != 0 && EInt_gt(a[parent(i)].value, a[i].value)) {
        swap(&a[parent(i)], &a[i]);
        i = parent(i);
    }
}

void min_heapify(PQ_Element a[], unsigned int i, unsigned int n) {
    unsigned int left = left_child(i);
    unsigned int right = right_child(i);
    unsigned int smallest = i;
    if(left <= n && EInt_lt(a[left].value, a[smallest].value))
        smallest = left;
    if(right <= n && EInt_lt(a[right].value, a[smallest].value)) 
        smallest = right;

    if(smallest != i) {
        PQ_Element temp = a[i];
        a[i] = a[smallest];
        a[smallest] = temp;
        min_heapify(a, smallest, n);
    }
}

PQ_Element get_min(PQ_Element a[]) {
    return a[0];
}
PQ_Element dequeue(PQ_Element a[], int *n) {
    PQ_Element min_item = a[0];
    a[0] = a[*n - 1];
    *n = *n - 1;
    min_heapify(a, 0, *n);
    return min_item;
}

#ifdef DEBUG_TRUE
void print_PQ(PQ_Element a[], int n) {
    printf("PQ state: \n");
    printf("[ \n");
    if(n != 0) 
        for(int i = 0; i < n - 1; i++)
            printf("\t{ index = %lu, value = { isInf = %lu, val = %lu} }, \n", a[i].index, a[i].value.isInf, a[i].value.val);
    else printf(" ]\n");
    if(n > 1) 
        printf("\t{ index = %lu, value = { isInf = %lu, val = %lu} }\n ]\n", a[n-1].index, a[n-1].value.isInf, a[n-1].value.val);
}
#endif

// The original Dijkstra's algorithm with binary heap-based priority queue.

void dijkstra(Graph *g, EInt *dist, unsigned int *c, unsigned int s) {
    // priority queue initialisation
    PQ_Element queue[HEAP_MAX];
    unsigned int n = 0;
    // initialise source distance, num, and pred
    dist[s].val = 0; dist[s].isInf = 0;
    // initialising the return values
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(v != s) {
            dist[v].isInf = 1;
        }
        PQ_Element vd;
        vd.index = v; vd.value = dist[v];
        enqueue(queue, vd, &n);
    }

    // construct adjacency list here
    Node *elist[vertex_cnt(g)];
    for(unsigned int v = 0; v < vertex_cnt(g); v++) elist[v] = NULL;
    for(unsigned int e = 0; e < edge_cnt(g); e++) {
        Node *n = malloc(sizeof(Node));
        n->second = arcs(g, e).second;
        n->edge_id = e;
        n->next = elist[arcs(g, e).first];
        elist[arcs(g, e).first] = n;
    }

    while(n != 0) {
        PQ_Element u = dequeue(queue, &n);
        for(Node *node = elist[u.index]; node != NULL; node = node->next) {
            unsigned int v = node->second;
            EInt alt = { .isInf = dist[u.index].isInf, .val = dist[u.index].val + c[node->edge_id]};
            if(EInt_lt(alt, dist[v])) {
                dist[v] = alt;
                PQ_Element vn = { .index = v, .value = alt };
                enqueue(queue, vn, &n);
            }
        }
    }

/*
    while(n != 0) {
#ifdef DEBUG_TRUE
        printf("PQ size: %lu\n", n);
#endif
        PQ_Element u = dequeue(queue, &n);
        for(int e = 0; e < edge_cnt(g); e++) {
            if(arcs(g, e).first != u.index) continue;
#ifdef DEBUG_TRUE
            printf("->edge %lu: (%lu, %lu)\n", e, u.index, arcs(g, e).second);
#endif
            unsigned int v = arcs(g, e).second;
            EInt alt;
            alt.isInf = 0, alt.val = dist[u.index].val + c[e];
            if(EInt_lt(alt, dist[v])) {
#ifdef DEBUG_TRUE
                printf("-->alt(dist[%lu] + c[%lu] (i.e. %lu)): { isInf = %lu, val = %lu }\n", u.index, e, c[e], alt.isInf, alt.val);
                printf("-->dist[%lu]: { isInf = %lu, val = %lu }\n", v, dist[v].isInf, dist[v].val);
#endif

                dist[v] = alt;
                PQ_Element vn;
                vn.index = v;
                vn.value = alt;
                enqueue(queue, vn, &n);
            }
        }
    }
*/
}

// certifying Dijkstra's algorithm implementation

void certifying_dijkstra(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred) {
    // priority queue initialisation
    PQ_Element queue[HEAP_MAX];
    unsigned int n = 0;
    // initialise source distance, num, and pred
    dist[s].val = 0; dist[s].isInf = 0;
    enu[s].val = 0; enu[s].isInf = 0;
    pred[s] = -1;
    // initialising the return values
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(v != s) {
            dist[v].isInf = 1;
            enu[v].isInf = 1;
            pred[v] = -1;
        }
        PQ_Element vd;
        vd.index = v; vd.value = dist[v];
        enqueue(queue, vd, &n);
    }

    // construct adjacency list here
    Node *elist[vertex_cnt(g)];
    for(unsigned int v = 0; v < vertex_cnt(g); v++) elist[v] = NULL;
    for(unsigned int e = 0; e < edge_cnt(g); e++) {
        Node *n = malloc(sizeof(Node));
        n->second = arcs(g, e).second;
        n->edge_id = e;
        n->next = elist[arcs(g, e).first];
        elist[arcs(g, e).first] = n;
    }

    while(n != 0) {
        PQ_Element u = dequeue(queue, &n);
        for(Node *node = elist[u.index]; node != NULL; node = node->next) {
            unsigned int v = node->second;
            EInt alt = { .isInf = dist[u.index].isInf, .val = dist[u.index].val + c[node->edge_id]};
            if(EInt_lt(alt, dist[v])) {
                dist[v] = alt;
                enu[v].isInf = 0;
                enu[v].val = enu[u.index].val + 1;
                pred[v] = node->edge_id;
                PQ_Element vn = { .index = v, .value = alt };
                enqueue(queue, vn, &n);
            }
        }
    }
/*
    while(n != 0) {
#ifdef DEBUG_TRUE
        printf("PQ size: %lu\n", n);
        print_PQ(queue, n);
#endif
        PQ_Element u = dequeue(queue, &n);
        for(int e = 0; e < edge_cnt(g); e++) {
#ifdef DEBUG_TRUE

            printf("->edge %lu?: (%lu, %lu)\n", e, u.index, arcs(g, e).second);
#endif
            if(arcs(g, e).first != u.index) continue;
#ifdef DEBUG_TRUE
            printf("->edge %lu: (%lu, %lu)\n", e, u.index, arcs(g, e).second);
#endif
            unsigned int v = arcs(g, e).second;
            EInt alt;
            alt.isInf = dist[u.index].isInf, alt.val = dist[u.index].val + c[e];
#ifdef DEBUG_TRUE
            printf("-->dist[%lu] (before): { isInf = %lu, val = %lu }\n", v, dist[v].isInf, dist[v].val);
            printf("-->alt: { isInf = %lu, val = %lu }\n", alt.isInf, alt.val);
#endif
            if(EInt_lt(alt, dist[v])) {
                dist[v] = alt;
                enu[v].isInf = 0;
                enu[v].val = enu[u.index].val + 1;
                pred[v] = e;
                PQ_Element vn;
                vn.index = v;
                vn.value = alt;
#ifdef DEBUG_TRUE
                printf("-->dist[%lu] (after): { isInf = %lu, val = %lu }\n", v, dist[v].isInf, dist[v].val);
#endif
                enqueue(queue, vn, &n);
#ifdef DEBUG_TRUE
                printf("-->AFTER ENQUEUE:\n");
                print_PQ(queue, n);
#endif
            }
        }
    }
*/
}

// Procedures

int is_wellformed(Graph *g) {
    Edge e;
     for(unsigned int i = 0; i < edge_cnt(g); i++) {
         e = arcs(g, i);
        if(vertex_cnt(g) <= e.first) return 0;
        if(vertex_cnt(g) <= e.second) return 0;
    }
    return 1;
}

int trian(Graph *g, EInt *dist, unsigned int *c) {
    for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
        if(dist[arcs(g, edge_id).first].isInf == 0) {
            if(dist[arcs(g, edge_id).second].isInf != 0) return 0;
            if((unsigned long) dist[arcs(g, edge_id).second].val > (unsigned long) dist[arcs(g, edge_id).first].val + (unsigned long)c[edge_id]) return 0;
        }
    }
    return 1;
}

int just(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) pred[v];
        if(v != s) {
            if(enu[v].isInf == 0) {
                if(pred[v] < 0) return 0;
                if(edge_id >= edge_cnt(g)) return 0;
                if(arcs(g, edge_id).second != v) return 0;
                if((dist[v].isInf == 0) != (dist[arcs(g, edge_id).first].isInf == 0)) return 0;
                if(dist[v].isInf == 0)
                    if((unsigned long) dist[v].val != (unsigned long) dist[arcs(g, edge_id).first].val + (unsigned long) c[edge_id]) return 0;
                if(enu[arcs(g, edge_id).first].isInf != 0) return 0;
                if((unsigned long) enu[v].val != (unsigned long) enu[arcs(g, edge_id).first].val + 1) return 0;
            }
        }
    }
    return 1;
}

int no_path(Graph *g, EInt *dist, EInt *enu) {
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if((dist[v].isInf == 0) != (enu[v].isInf == 0)) return 0;
    }
    return 1;
}

int check_basic_just_sp(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred) {
    if(!is_wellformed(g)) return 0;
    if(s >= vertex_cnt(g)) return 0;
    if(dist[s].isInf != 0) return 0;
    if(dist[s].val > 0) return 0;
    if(!trian(g, dist, c)) return 0;
    if(!just(g, dist, c, s, enu, pred)) return 0;
    return 1;
}

int check_sp(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred) {
    if(!check_basic_just_sp(g, dist, c, s, enu, pred)) return 0;
    if(dist[s].val != 0) return 0;
    if(!no_path(g, dist, enu)) return 0;
    return 1;
}

