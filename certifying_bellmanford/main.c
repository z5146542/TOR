#include "shortest_path_checker.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_VERTICES 10
#define NUM_EDGES 11

int main() {
    Edge *arcs = malloc(sizeof(Edge) * NUM_EDGES);
    
    arcs[0].first = 0;
    arcs[0].second = 1;
    arcs[1].first = 1;
    arcs[1].second = 2;
    arcs[2].first = 1;
    arcs[2].second = 3;
    arcs[3].first = 2;
    arcs[3].second = 3;
    arcs[4].first = 4;
    arcs[4].second = 3;
    arcs[5].first = 3;
    arcs[5].second = 5;
    arcs[6].first = 4;
    arcs[6].second = 5;
    arcs[7].first = 6;
    arcs[7].second = 4;
    arcs[8].first = 5;
    arcs[8].second = 6;
    arcs[9].first = 6;
    arcs[9].second = 7;
    arcs[10].first = 8;
    arcs[10].second = 9;
    
    Graph *graph = malloc(sizeof(Graph));
    vertex_cnt(graph) = NUM_VERTICES;
    edge_cnt(graph) = NUM_EDGES;
    graph->arcs = arcs;
    
    unsigned int s = 1;

    int *c = malloc(sizeof(unsigned int) * NUM_EDGES);

    c[0] = 4;
    c[1] = -2;
    c[2] = 3;
    c[3] = -2;
    c[4] = 3;
    c[5] = -3;
    c[6] = -2;
    c[7] = 2;
    c[8] = -1;
    c[9] = 1;
    c[10] = -3;

    ENInt *dist = malloc(sizeof(ENInt) * NUM_VERTICES);
#ifdef CERTIFYING
    unsigned int *num = malloc(sizeof(unsigned int) * NUM_VERTICES);
    int *pred = malloc(sizeof(int) * NUM_VERTICES);
    int *parent_edge = malloc(sizeof(int) * NUM_VERTICES);
    Cycle_set *cse = malloc(sizeof(Cycle_set));
    cse->no_cycles = 0;
    cse->cyc_obj = malloc(sizeof(Cycle) * NUM_VERTICES);
#endif

#ifdef CERTIFYING
    if (dist == NULL || num == NULL || pred == NULL) {
        fprintf(stderr, "allocation size reached maximum.\n");
        return EXIT_FAILURE;
    }
#else 
    if (dist == NULL) {
        fprintf(stderr, "allocation size reached maximum.\n");
        return EXIT_FAILURE;
    }
#endif

/*
#ifdef CERTIFYING
    printf("Running certifying algorithm...\n");
    certifying_dijkstra(graph, dist, c, s, num, pred);
    printf("Verifying output using checker...");
    printf("%s\n", check_sp(graph, dist, c, s, num, pred) ? "\033[0;32mtrue\033[0m" : "\033[0;31mfalse\033[0m");
#else
    printf("Running dijkstra's algorithm...");
    dijkstra(graph, dist, c, s);
    printf("Done.\n");
#endif
*/
    printf("Running certifying Bellman--Ford algorithm...\n");
    certifying_bellmanford_LEDA(graph, s, c, dist, pred);
    printf("Verifying output using LEDA checker...");
    check_sp_LEDA(graph, s, c, dist, pred);
    printf("done.\n");
    printf("Running certifying Bellman--Ford algorithm again...\n");
    certifying_bellmanford(graph, s, c, num, pred, dist, cse, parent_edge);
    printf("Verifying output using new checker...");
    printf("%s\n", check_sp(graph, s, c, num, pred, dist, cse, parent_edge) ? "\033[0;32mtrue\033[0m" : "\033[0;31mfalse\033[0m");
}
