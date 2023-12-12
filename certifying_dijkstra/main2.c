#include "shortest_path_checker.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_VERTICES 2000
#define NUM_EDGES (NUM_VERTICES * NUM_VERTICES)

int main() {
    Edge *arcs = malloc(sizeof(Edge) * NUM_EDGES);
    unsigned int *c = malloc(sizeof(unsigned int) * NUM_EDGES);

    for(unsigned long i = 0; i < NUM_VERTICES; i++) {
        for(unsigned long j = 0; j < NUM_VERTICES; j++) {
            arcs[i * NUM_VERTICES + j].first = i;
            arcs[i * NUM_VERTICES + j].second = j;
        }
    }
    
    for(unsigned long e = 0; e < NUM_EDGES; e++) {
        c[e] = e;
    }
    
    Graph *graph = malloc(sizeof(Graph));
    vertex_cnt(graph) = NUM_VERTICES;
    edge_cnt(graph) = NUM_EDGES;
    graph->arcs = arcs;
    
    unsigned int s = 0;

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
