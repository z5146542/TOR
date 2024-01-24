#include "shortest_path_checker.h"
#include <stdlib.h>
#include <stdio.h>

#define NUM_VERTICES 2
#define NUM_EDGES 1

int main() {
    Edge *arcs = malloc(sizeof(Edge) * NUM_EDGES);
    
    arcs[0].first = 0;
    arcs[0].second = 1;
    
    Graph *graph = malloc(sizeof(Graph));
    vertex_cnt(graph) = NUM_VERTICES;
    edge_cnt(graph) = NUM_EDGES;
    graph->arcs = arcs;
    
    unsigned int s = 1;

    int *c = malloc(sizeof(unsigned int) * NUM_EDGES);

    c[0] = 1;

    ENInt *dist = malloc(sizeof(ENInt) * NUM_VERTICES);
#ifdef CERTIFYING
    ENInt *num = malloc(sizeof(ENInt) * NUM_VERTICES);
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
    printf("We have the graph of the following form: v -1-> s,\n");
    printf("and we have:\n");
    printf("\tpred(s) = (v,s), \tpred(v) = nil\n");
    printf("\tdist(s) = 17, \t\tdist(v) = 17\n");
    printf("...clearly which is incorrect, but check_sp_LEDA returns without\n");
    printf("violating any assertions.\n");
    dist[0].isInf = 0; dist[0].val = 17;
    dist[1].isInf = 0; dist[1].val = 17;
    pred[0] = -1;
    pred[1] = 0;
    check_sp_LEDA(graph, s, c, dist, pred);
}
