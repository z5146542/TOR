// shortest_path_checker.h
// Anonymous Authors

// Type Synonyms

typedef struct Edge {
    unsigned int first;
    unsigned int second;
} Edge;

typedef struct Graph {
    unsigned int num_edges;
    unsigned int num_vertices;
    Edge *arcs;
} Graph;

// Datatype for dist and num, which encodes inf
typedef struct EInt {
    unsigned int val;
    unsigned int isInf;
} EInt;

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// Normal Algorithm

void dijkstra(Graph *g, EInt *dist, unsigned int *c, unsigned int s);

// Certifying Algorithm

void certifying_dijkstra(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred);

// Checker

int check_sp(Graph *g, EInt *dist, unsigned int *c, unsigned int s, EInt *enu, int *pred);

