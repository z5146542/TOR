// Graph.c
// Seung Hoon Park

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

typedef struct EInt {
    unsigned int val;
    unsigned int isInf;
} EInt;
// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

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
            // if(dist[arcs(g, edge_id).first].val > dist[arcs(g, edge_id).first].val + c[edge_id]) return 0; // check there is no overflow
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
                // if(enu[arcs(g, edge_id).first].val > enu[arcs(g, edge_id).first].val + 1) return 0;
                // if(enu[v].val >= vertex_cnt(g)) return 0;
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

// int pos_cost(Graph *g, unsigned int *c) {
    // for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
        // if(c[edge_id] < 0) return 0;
    // }
    // return 1;
// }

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
    // if(!pos_cost(g, c)) return 0;
    return 1;
}

int main(int argc, char **argv) {
    return 0;
}
