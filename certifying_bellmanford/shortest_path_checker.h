// shortest_path_checker.h
// Anonymous Authors

// Type Synonyms

typedef struct Edge {
    unsigned int first;
    unsigned int second;
} Edge;

typedef struct Graph {
    unsigned int num_vertices;
    unsigned int num_edges;
    Edge *arcs;
} Graph;

// used for dist
typedef struct ENInt {
    int val;
    // isInf < 0 --> -inf
    // isInf = 0 --> finite, value determined by .val
    // isInf > 0 --> inf
    int isInf;
} ENInt;

// Cycle contains a starting vertex, the length of the path, and the path itself
// locale 3 related data structures will be dealt later.
typedef struct Cycle {
    // 'a 
    unsigned int start;
    // 'b awalk; needs two components in C
    unsigned int length;
    unsigned int *path;
} Cycle;

typedef struct Cycle_set {
    unsigned int no_cycles;
    Cycle *cyc_obj;
} Cycle_set;

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// Normal Algorithms

void bellmanford(Graph *g, unsigned int s, int *c, ENInt *dist);

// Certifying Algorithms

void certifying_bellmanford_LEDA(Graph *g, unsigned int s, int *c, ENInt *dist, int *pred);

void certifying_bellmanford(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, Cycle_set *cse, int *parent_edge);

// Checkers

void check_sp_LEDA(Graph *g, unsigned int s, int *c, ENInt *dist, int *pred);

int check_sp(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, Cycle_set *cse, int *parent_edge);

