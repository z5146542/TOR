// shortest_path_checker.c
// Anonymous Authors
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
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

// stack implementation -- a more sophisticated structure that 
// keeps track of the size could be used, but the following 
// technically suffices.

typedef struct stack {
    unsigned int vertex;
    struct stack *next;
} Stack;

// doubly linked list (with tail) implementation

typedef struct listnode {
    unsigned int value;
    struct listnode *next;
    struct listnode *prev;
} ListNode;

typedef struct list {
    unsigned int size;
    ListNode *head;
    ListNode *tail;
} List;

// Internal priority queue

typedef struct pq_elem {
    unsigned int index;
    ENInt value;
} PQ_Element;

void swap(PQ_Element *x, PQ_Element *y) {
    PQ_Element temp = *x;
    *x = *y;
    *y = temp;
}

int ENInt_lt(ENInt x, ENInt y) {
    if(x.isInf || (x.isInf && y.isInf)) return 0;
    if(y.isInf) return 1;
    return x.val < y.val;
}

int ENInt_gt(ENInt x, ENInt y) {
    return ENInt_lt(y, x);
}

void enqueue(PQ_Element a[], PQ_Element data, unsigned int *n) {
    if(*n >= HEAP_MAX) {
        fprintf(stderr, "FAILURE: PQ reached maximum elements!\n");
        return;
    }
    a[*n] = data;
    *n = *n + 1;
    unsigned int i = *n - 1;
    while(i != 0 && ENInt_gt(a[parent(i)].value, a[i].value)) {
        swap(&a[parent(i)], &a[i]);
        i = parent(i);
    }
}

void min_heapify(PQ_Element a[], unsigned int i, unsigned int n) {
    unsigned int left = left_child(i);
    unsigned int right = right_child(i);
    unsigned int smallest = i;
    if(left <= n && ENInt_lt(a[left].value, a[smallest].value))
        smallest = left;
    if(right <= n && ENInt_lt(a[right].value, a[smallest].value)) 
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

void dijkstra(Graph *g, ENInt *dist, unsigned int *c, unsigned int s) {
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
            ENInt alt = { .isInf = dist[u.index].isInf, .val = dist[u.index].val + c[node->edge_id]};
            if(ENInt_lt(alt, dist[v])) {
                dist[v] = alt;
                PQ_Element vn = { .index = v, .value = alt };
                enqueue(queue, vn, &n);
            }
        }
    }
}

void certifying_dijkstra(Graph *g, ENInt *dist, unsigned int *c, unsigned int s, ENInt *enu, int *pred) {
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
            ENInt alt = { .isInf = dist[u.index].isInf, .val = dist[u.index].val + c[node->edge_id]};
            if(ENInt_lt(alt, dist[v])) {
                dist[v] = alt;
                enu[v].isInf = 0;
                enu[v].val = enu[u.index].val + 1;
                pred[v] = node->edge_id;
                PQ_Element vn = { .index = v, .value = alt };
                enqueue(queue, vn, &n);
            }
        }
    }
}

// list operations

List *create_list() {
    List *list = malloc(sizeof(List));
    list->size = 0;
    list->head = list->tail = NULL;
    return list;
}

void free_list(List *list) {
    ListNode *curr = list->head;
    while(curr) {
        ListNode *temp = curr;
        curr = curr->next;
        free(temp);
    }
    free(list);
}

ListNode *list_push(List *list, unsigned int v) {
    ListNode *head = malloc(sizeof(ListNode));
    head->value = v;
    head->next = list->head;
    head->prev = NULL;
    if(list->head) list->head->prev = head;
    list->head = head;
    if(list->size == 0) list->tail = head;
    list->size++;
    return head;
}

ListNode *list_append(List *list, unsigned int v) {
    ListNode *tail = malloc(sizeof(ListNode));
    tail->value = v;
    tail->next = NULL;
    tail->prev = list->tail;
    if(list->tail) list->tail->next = tail;
    list->tail = tail;
    if(list->size == 0) list->head = tail;
    list->size++;
    return tail;
}

unsigned int list_pop(List *list) {
    // precondition: list is non-empty
    ListNode *head = list->head;
    unsigned int v = list->head->value;
    list->head = list->head->next;
    if(list->head) list->head->prev = NULL;
    list->size--;
    free(head);
    return v;
}

unsigned int list_pop_tail(List *list) {
    ListNode *tail = list->tail;
    unsigned int v = list->tail->value;
    list->tail = list->tail->prev;
    if(list->tail) list->tail->next = NULL;
    list->size--;
    free(tail);
    return v;
}

bool list_empty(List *list) {
    return list->size == 0;
}

// technically, insert after pos
ListNode *list_insert(List *list, unsigned int x, ListNode *pos) {
    if(pos == list->tail) return list_append(list, x);
    ListNode *node = malloc(sizeof(ListNode));
    node->value = x;
    node->prev = pos;
    node->next = pos->next;
    

    pos->next->prev = node;
    pos->next = node;
    list->size++;
    return node;
    /*
    ListNode *curr = list->head;

    while(curr) {
        if(curr->value == pos) {
            ListNode *next = curr->next;
            node->prev = curr;
            node->next = next;
            curr->next = node;
            if(next) next->prev = node;
            else list->tail = node;
            list->size++;
            return node;
        }
        curr = curr->next;
    }
    return NULL;
    */
}

ListNode *list_succ(List *list, ListNode *w) {
    return w->next;
}

void list_del_item(List *list, ListNode *w) {
    if(list_empty(list)) return;
    if(!w) return;
    if(list->head == w) {
        list_pop(list);
        return;
    }
    if(list->tail == w) {
        list_pop_tail(list);
        return;
    }
    w->prev->next = w->next;
    w->next->prev = w->prev;
    list->size--;
    free(w);
}

// TODO: implement BF_delete_subtree and BF_add_to_Vm

ListNode *BF_delete_subtree(ListNode *w_item, List *Q, List *T, int t_degree[], ListNode *pos_in_Q[], ListNode *pos_in_T[]) {
    ListNode *child = list_succ(T, w_item);
    unsigned int w = w_item->value;
    while(t_degree[w] > 0) {
        t_degree[w]--;
        child = BF_delete_subtree(child, Q, T, t_degree, pos_in_Q, pos_in_T);
    }
    pos_in_T[w] = NULL;
    list_del_item(T, w_item);
    if(pos_in_Q[w]) {
        list_del_item(Q, pos_in_Q[w]);
        pos_in_Q[w] = NULL;
    }
    return child;
}

void BF_add_to_Vm(Graph *g, Node *elist[], unsigned int z, bool in_Vm[], int *pred, List *Q, List *T, int t_degree[], ListNode *pos_in_Q[], ListNode *pos_in_T[]) {
    for(Node *node = elist[z]; node != NULL; node = node->next) {
        unsigned int e = node->edge_id;
        unsigned int w = node->second;
        if(!in_Vm[w]) {
            if(pos_in_T[w]) {
                BF_delete_subtree(pos_in_T[w], Q, T, t_degree, pos_in_Q, pos_in_T);
                if(pred[w] != -1) t_degree[arcs(g, pred[w]).first]--;
            }
            pred[w] = e;
            in_Vm[w] = true;
            BF_add_to_Vm(g, elist, w, in_Vm, pred, Q, T, t_degree, pos_in_Q, pos_in_T);
        }
    }
}

void create_adjacency_list(Graph *g, Node *elist[]) {
    for(unsigned int v = 0; v < vertex_cnt(g); v++) elist[v] = NULL;
    for(unsigned int e = 0; e < edge_cnt(g); e++) {
        Node *n = malloc(sizeof(Node));
        n->second = arcs(g, e).second;
        n->edge_id = e;
        n->next = elist[arcs(g, e).first];
        elist[arcs(g, e).first] = n;
    }
}

void free_adjacency_list(Graph *g, Node *elist[]) {
    for(unsigned v = 0; v < vertex_cnt(g); v++) {
        Node *curr = elist[v];
        while(curr != NULL) {
            Node *temp = curr;
            curr = curr->next;
            free(temp);
        }
    }
}

void certifying_bellmanford_LEDA(Graph *g, unsigned int s, int *c, ENInt *dist, int *pred) {
    // node_array<list_item> pos_in_Q(G, nil);
    // node_array<int>       t_degree(G, 0);
    // node_array<list_item> pos_in_T(G, nil);
    ListNode *pos_in_Q[vertex_cnt(g)]; // noting -1 denotes the position does not exist
    int t_degree[vertex_cnt(g)];
    ListNode *pos_in_T[vertex_cnt(g)];
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        pos_in_Q[v] = NULL;
        t_degree[v] = 0;
        pos_in_T[v] = NULL;
    }

    for(unsigned int v = 0; v < vertex_cnt(g); v++) pred[v] = -1;
    dist[s].isInf = 0; dist[s].val = 0;

    // list<node> Q; pos_in_Q[s] = Q.append(s);
    // list<node> T; pos_in_T[s] = T.append(s);

    List *Q = create_list(); pos_in_Q[s] = list_append(Q, s);
    List *T = create_list(); pos_in_T[s] = list_append(T, s);

    bool in_Vm[vertex_cnt(g)];
    for(unsigned int v = 0; v < vertex_cnt(g); v++) in_Vm[v] = false;
    bool no_negative_cycle = true;

    // construct adjacency list here (needed for efficiency)
    Node *elist[vertex_cnt(g)];
    create_adjacency_list(g, elist);

    while(!list_empty(Q)) {
        unsigned int v = list_pop(Q); pos_in_Q[v] = NULL;
        for(Node *node = elist[v]; node != NULL; node = node->next) {
            unsigned int e = node->edge_id;
            unsigned int w = node->second;
            if(in_Vm[w]) continue;
            ENInt d;
            d.isInf = dist[v].isInf;
            d.val = dist[v].val + c[e];
            if( (pred[w] == -1 && w != s) || (d.isInf < dist[w].isInf) || 
                (d.isInf == 0 && dist[w].isInf == 0 && d.val < dist[w].val) ) {
                dist[w] = d;
                // remove the subtree rooted at w from T and Q
                // if w has a parent, decrease its degree 

                if(pos_in_T[w]) {
                    BF_delete_subtree(pos_in_T[w], Q, T, t_degree, pos_in_Q, pos_in_T);
                    if(pred[w] != -1) t_degree[arcs(g,pred[w]).first]--;
                }

                pred[w] = e;

                if(pos_in_T[v] == NULL) {
                    no_negative_cycle = false;

                    unsigned int z = v;
                    do {
                        in_Vm[z] = true;
                        z = arcs(g, pred[z]).first;
                    } while(z != v);
                    do {
                        BF_add_to_Vm(g, elist, z, in_Vm, pred, Q, T, t_degree, pos_in_Q, pos_in_T);
                        z = arcs(g,pred[z]).first;
                    } while(z != v);
                } else {
                    pos_in_T[w] = list_insert(T, w, pos_in_T[v]);
                    t_degree[v]++;
                    pos_in_Q[w] = list_append(Q, w);
                }
            }
        }
    }

    free_adjacency_list(g, elist);
}

// Procedures

// the following is the LEDA checker and its helper functions

void dfs(Graph *g, unsigned int s, bool reached[], Node *elist[]) {
    reached[s] = true;
    for(Node *node = elist[s]; node != NULL; node = node->next)
        if(!reached[node->second]) dfs(g, node->second, reached, elist);
}

void DFS(Graph *g, unsigned int s, bool reached[]) {
    // construct adjacency list here -- reduces time complexity for finding adjacent nodes
    Node *elist[vertex_cnt(g)];
    create_adjacency_list(g, elist);
    dfs(g, s, reached, elist);
    // free the adjacency list -- the lines below can be deleted if overall time is affected non-trivially
    free_adjacency_list(g, elist);
    return;
}

// stack operations

void stack_push(Stack *s, unsigned int v) {
    Stack *head = malloc(sizeof(Stack));
    head->vertex = v;
    head->next = s;
    s = head;
}

unsigned int stack_pop(Stack *s) {
    unsigned int v = s->vertex;
    Stack *head = s;
    s = s->next;
    free(head);
    return v;
}

bool stack_empty(Stack *s) {
    return s == NULL;
}

void stack_clear(Stack *s) {
    while(s != NULL) {
        Stack *head = s;
        s = head->next;
        free(head);
    }
}
// implementation of checkers

/* Keep in mind this is the LEDA version, which is proven to be unsound from the paper.
   The implementation was manually imported from the C++ source code in the LEDA
   library. The only noticable difference in this implementation from that of LEDA
   lies in the implementation of the DFS algorihtm, where the graph is interpreted
   as an adjacency list for performanece purposes. All other aspects of the
   checker has been left as is. */

enum { NEG_CYCLE = -2, ATT_TO_CYCLE = -1, FINITE = 0, PLUS = 1,
       CYCLE = 2, ON_CUR_PATH = 3, UNKNOWN = 4  };
void check_sp_LEDA(Graph *g, unsigned int s, int *c, ENInt *dist, int *pred) {
    unsigned int label[vertex_cnt(g)];
    bool reachable[vertex_cnt(g)];
    for(unsigned int i = 0; i < vertex_cnt(g); i++) {
        label[i] = UNKNOWN;
        reachable[i] = false;
    }

    DFS(g, s, reachable);
    for(unsigned int v; v < vertex_cnt(g); v++) {
        if (v != s) {
            assert((pred[v] == -1) == (reachable[v] == false));
            if (reachable[v] == false) label[v] = PLUS;
        }
    }

    if(pred[s] == -1) label[s] = FINITE;
    for(unsigned int v; v < vertex_cnt(g); v++) {
        if (label[v] == UNKNOWN) {
            Stack *s = NULL;
            unsigned int w = v;
            while(label[w] == UNKNOWN) {
                label[w] = ON_CUR_PATH;
                stack_push(s, w);
                w = arcs(g, pred[w]).first;
            }

            int t = label[w];
            if(t == ON_CUR_PATH) {
                unsigned int z;
                do {
                    z = stack_pop(s);
                    label[z] = CYCLE;
                } while(z != w);
                while(!stack_empty(s)) label[stack_pop(s)] = ATT_TO_CYCLE;
            } else {
                if (t == CYCLE) t = ATT_TO_CYCLE;
                while(!stack_empty(s)) label[stack_pop(s)] = t;
            }
        }
    }

    for(unsigned int v; v < vertex_cnt(g); v++) {
        if(label[v] == CYCLE) {
            unsigned int w = v;
            long cycle_length = 0;
            do {
                cycle_length += c[pred[w]];
                label[w] = NEG_CYCLE;
                w = arcs(g, pred[w]).first;
            } while(w != v);
            assert(cycle_length < 0);
        }
    }

    if(label[s] == FINITE) assert(dist[s].isInf == 0 && dist[s].val == 0);

    for(unsigned int e; e < edge_cnt(g); e++) {
        unsigned int v = arcs(g, e).first;
        unsigned int w = arcs(g, e).second;
        if(label[w] == FINITE) {
            assert(label[v] == FINITE || label[v] == PLUS);
            if(label[v] == FINITE) {
                // trian and just checked here
                assert(dist[v].val + c[e] >= dist[w].val);
                if(e == pred[w]) assert(dist[v].val + c[e] == dist[w].val);
            }
        }
    }
    return;
}

// the following procedures are from the nonnegative shortest path 

int is_wellformed(Graph *g) {
    Edge e;
    for(unsigned int i = 0; i < edge_cnt(g); i++) {
        e = arcs(g, i);
        if(vertex_cnt(g) <= e.first) return 0;
        if(vertex_cnt(g) <= e.second) return 0;
    }
    return 1;
}

int trian(Graph *g, ENInt *dist, int *c) {
    for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
        if(dist[arcs(g, edge_id).first].isInf == 0) {
            if(dist[arcs(g, edge_id).second].isInf > 0) return 0;
            if(dist[arcs(g, edge_id).second].isInf == 0) {
                if((long) dist[arcs(g, edge_id).second].val > 
                   (long) dist[arcs(g, edge_id).first].val + 
                   (long) c[edge_id]) return 0;
            }
        }
        if(dist[arcs(g, edge_id).first].isInf < 0) {
            if(dist[arcs(g, edge_id).second].isInf >= 0) return 0;
        }
    }
    return 1;
}

int just(Graph *g, ENInt *dist, int *c, unsigned int s, unsigned int *num, int *pred) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) pred[v];
        if(v != s) {
            if(dist[v].isInf == 0) {
                if(pred[v] < 0) return 0;
                if(edge_id >= edge_cnt(g)) return 0;
                if(arcs(g, edge_id).second != v) return 0;
                if(dist[arcs(g, edge_id).first].isInf != 0) return 0;
                if((long) dist[v].val != 
                   (long) dist[arcs(g, edge_id).first].val + 
                   (long) c[edge_id]) return 0;
                if((unsigned long) num[v] != 
                   (unsigned long) num[arcs(g, edge_id).first] + 1) return 0;
            }
        }
    }
    return 1;
}

int check_basic_just_sp(Graph *g, ENInt *dist, int *c, unsigned int s, unsigned int *num, int *pred) {
    if(!is_wellformed(g)) return 0;
    if(dist[s].isInf > 0) return 0;
    if(dist[s].isInf == 0)
        if(dist[s].val > 0) return 0;
    if(!trian(g, dist, c)) return 0;
    if(!just(g, dist, c, s, num, pred)) return 0;
    return 1;
}

// the folloiwng are for the general-weight edge shrotest path

// locale 1
int s_assms(Graph *g, unsigned int s, ENInt *dist, int *parent_edge, unsigned int *num) {
    if(s >= vertex_cnt(g)) return 0;
    if(dist[s].isInf > 0) return 0;
    if(!(parent_edge[s] < 0)) return 0;
    if(num[s] != 0) return 0;
    return 1;
}

int parent_num_assms(Graph *g, unsigned int s, ENInt *dist, int *parent_edge, unsigned int *num) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) parent_edge[v];
        if(v != s) {
            if(dist[v].isInf <= 0) {
                if(parent_edge[v] < 0) return 0;
                if(edge_id >= edge_cnt(g)) return 0;
                if(arcs(g, edge_id).second != v) return 0;
                if(dist[arcs(g, edge_id).first].isInf > 0) return 0;
                if((unsigned long) num[v] != 
                   (unsigned long) num[arcs(g, edge_id).first] + 1) return 0;
            }
        }
    }
    return 1;
}

// locale 2
int source_val(Graph *g, unsigned int s, ENInt *dist, unsigned int *num){
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf == 0) {
            if(dist[s].isInf != 0) return 0;
            if(dist[s].val != 0) return 0;
            return 1;
        }
    }
    return 1;
}

int no_edge_Vm_Vf(Graph *g, ENInt *dist) {
    for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
        if(dist[arcs(g, edge_id).first].isInf < 0) {
            if(dist[arcs(g, edge_id).second].isInf == 0) return 0;
        }
    }
    return 1;
}

// helpers for locale 3

int cyc_in_graph(Graph *g, Cycle *C) {
  // u \in verts G
    if(C->start >= vertex_cnt(g)) return 0;
    // set p \subsetof arcs G
    for(unsigned int z = 0; z < C->length; z++)
        if(C->path[z] >= edge_cnt(g)) return 0;
    return 1;
}

int cas(Graph *g, Cycle *C) {
    // cas u p v 
    Edge e1;
    Edge e2;
    if (C-> length == 0) return 1;

    e1 = arcs(g, C->path[0]);
    if(e1.first != C->start) return 0;

    e2 = arcs(g, C->path[C->length -1]);
    if(e2.second != C->start) return 0;

    for(unsigned int z = 0; z < C->length - 1; z++) {
        e1 = arcs(g, C->path[z]);
        e2 = arcs(g, C->path[z+1]);
        if (e1.second != e2.first) return 0;
    }  
    return 1;
}

int awalk(Graph *g, Cycle *C) {
    if(!cyc_in_graph(g, C)) return 0;
    if(!cas(g, C)) return 0;
    return 1;
}
// returns the total cost of the path

long awalk_cost_neg(int *c, Cycle *C) {
    long total = 0;
    for(unsigned int e = 0; e < C->length; e++) {
        total = total + (signed long) c[C->path[e]];
    }
    return total;
}

// assume that a cycle is defined with a fixed length
// then the following holds

int C_se(Graph *g, Cycle_set *cse, int *c, ENInt *dist) {
    for(unsigned int y = 0; y < cse->no_cycles; y++) {
        if(dist[cse->cyc_obj[y].start].isInf > 0) return 0;
        if(awalk(g, &(cse->cyc_obj[y])) == 0) return 0;
        if(awalk_cost_neg(c, &(cse->cyc_obj[y])) >= 0) return 0;
    }
    return 1;
}

int int_neg_cyc(Graph *g, unsigned int s, ENInt *dist, Cycle_set *cse, int *c, int *parent_edge, unsigned int *num) {
    unsigned int is_neg_cycle;
    unsigned int no_cycles = cse->no_cycles;
    Cycle *cyc = cse->cyc_obj;

    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf < 0) {
            is_neg_cycle = 0;
            unsigned int u = v;

            for(unsigned int j = 0; j <= num[v]; j++) {
                for(unsigned int i = 0; i < no_cycles; i++) {
                    if(u == cyc[i].start) is_neg_cycle = 1;
                }
                u = arcs(g, parent_edge[u]).first;
            }
            if(is_neg_cycle == 0) return 0;
        }
    }
    return 0;
}

int shortest_paths_locale_step1(Graph *g, unsigned int s, unsigned int *num, int *parent_edge, ENInt *dist) {
    if(!is_wellformed(g)) return 0;
    if(!s_assms(g, s, dist, parent_edge, num)) return 0;
    if(!parent_num_assms(g, s, dist, parent_edge, num)) return 0;
    return 1;
}

int shortest_paths_locale_step2(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, int *parent_edge) {
    if(!shortest_paths_locale_step1(g, s, num, parent_edge, dist)) return 0;
    if(!check_basic_just_sp(g, dist, c, s, num, pred)) return 0;
    if(!source_val(g, s, dist, num)) return 0;
    if(!no_edge_Vm_Vf(g, dist)) return 0;
    return 1;
}

int shortest_paths_locale_step3(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, Cycle_set *cse, int *parent_edge) {
    if(shortest_paths_locale_step2(g, s, c, num, pred, dist, parent_edge) == 0) return 0;
    if(C_se(g, cse, c, dist) == 0) return 0;
    if(int_neg_cyc(g, s, dist, cse, c, parent_edge, num) == 0) return 0;
    return 1;
}

int check_sp(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, Cycle_set *cse, int *parent_edge) {
    return shortest_paths_locale_step3(g, s, c, num, pred, dist, cse, parent_edge);
}

