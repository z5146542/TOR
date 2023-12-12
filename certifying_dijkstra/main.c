#include "shortest_path_checker.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_VERTICES 5
#define NUM_EDGES 6

int main() {
    Edge *arcs = malloc(sizeof(Edge) * NUM_EDGES);
    
    arcs[0].first = 0;
    arcs[0].second = 1;
    arcs[1].first = 0;
    arcs[1].second = 2;
    arcs[2].first = 1;
    arcs[2].second = 4;
    arcs[3].first = 2;
    arcs[3].second = 3;
    arcs[4].first = 2;
    arcs[4].second = 4;
    arcs[5].first = 3;
    arcs[5].second = 4;
    
    Graph *graph = malloc(sizeof(Graph));
    vertex_cnt(graph) = NUM_VERTICES;
    edge_cnt(graph) = NUM_EDGES;
    graph->arcs = arcs;
    
    unsigned int s = 0;

    unsigned int *c = malloc(sizeof(unsigned int) * NUM_EDGES);
    
    c[0] = 15;
    c[1] = 4;
    c[2] = 5;
    c[3] = 2;
    c[4] = 11;
    c[5] = 3;

    EInt *dist = malloc(sizeof(EInt) * NUM_VERTICES);
#ifdef CERTIFYING
    EInt *num = malloc(sizeof(EInt) * NUM_VERTICES);
    int *pred = malloc(sizeof(int) * NUM_VERTICES);
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

#ifdef CERTIFYING
    printf("Running certifying algorithm...\n");
    certifying_dijkstra(graph, dist, c, s, num, pred);
    printf("Verifying output and checker...");
    printf("%s\n", check_sp(graph, dist, c, s, num, pred) ? "\033[0;32mtrue\033[0m" : "\033[0;31mfalse\033[0m");
#else
    printf("Running dijkstra's algorithm...");
    dijkstra(graph, dist, c, s);
    printf("Done.\n");
#endif
}
