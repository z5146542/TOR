// Graph.c
// Seung Hoon Park and Christine Rizkallah


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

// used for enum
// semantics equivalent to ENInt in shortest_path_checker.c
typedef struct EInt {
    unsigned int val;
    unsigned int isInf;
} EInt;

// Cycle contains a starting vertex, the length of the path, and the path itself
// locale 3 related data structures will be dealt later.
/*typedef struct Cycle {
    unsigned int start;
    unsigned int length;
    unsigned int *path;
} Cycle;*/

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// Procedures

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

int just(Graph *g, ENInt *dist, int *c, unsigned int s, EInt *num, int *pred) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) pred[v];
        if(v != s) {
            if(num[v].isInf == 0) {
                if(pred[v] < 0) return 0;
                if(edge_id >= edge_cnt(g)) return 0;
                if(arcs(g, edge_id).second != v) return 0;
                if((dist[v].isInf > 0) != (dist[arcs(g, edge_id).first].isInf > 0)) return 0;
                if((dist[v].isInf < 0) != (dist[arcs(g, edge_id).first].isInf < 0)) return 0;
                if(dist[v].isInf == 0)
                    if((long) dist[v].val != 
                       (long) dist[arcs(g, edge_id).first].val + 
                       (long) c[edge_id]) return 0;
                if(num[arcs(g, edge_id).first].isInf != 0) return 0;
                if((unsigned long) num[v].val != 
                   (unsigned long) num[arcs(g, edge_id).first].val + 1) return 0;
            }
        }
    }
    return 1;
}

int check_basic_just_sp(Graph *g, ENInt *dist, int *c, unsigned int s, EInt *num, int *pred) {
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
int s_assms(Graph *g, unsigned int s, ENInt *dist, int *pred, EInt *num) {
    if(s >= vertex_cnt(g)) return 0;
    if(dist[s].isInf > 0) return 0;
    if(pred[s] >= 0) return 0;
    if(num[s].isInf != 0) return 0;
    if(num[s].val != 0) return 0;
    return 1;
}

int parent_num_assms(Graph *g, unsigned int s, ENInt *dist, int *pred, EInt *num) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) pred[v];
        if(v != s) {
            if(dist[v].isInf <= 0) {
                if(pred[v] < 0) return 0;
                if(edge_id >= edge_cnt(g)) return 0;
                if(arcs(g, edge_id).second != v) return 0;
                if(dist[arcs(g, edge_id).first].isInf > 0) return 0;
                // work on logic here
                if(num[v].isInf != 0) return 0;
                if(num[arcs(g, edge_id).first].isInf != 0) return 0;
                if((unsigned long) num[v].val != 
                   (unsigned long) num[arcs(g, edge_id).first].val + 1) return 0;
            }
        }
    }
    return 1;
}

/* int no_p_edge(Graph *g, ENInt *dist) {
    for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
        if(dist[arcs(g, edge_id).first].isInf <= 0) {
            if(dist[arcs(g, edge_id).second].isInf > 0) return 0;
        }
    }
    return 1;
} */

// locale 2
int source_val(Graph *g, unsigned int s, ENInt *dist, EInt *num){
    /*
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(num[v].isInf <= 0) {
            if(dist[s].isInf == 0) {
                if(dist[s].val == 0) return 1;
            }
        }
    }
    return 0;*/
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(num[v].isInf <= 0) {
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


// the following functions are all related to locale 3, which will be dealt with later. 
/*
// helpers

// checks if the sequence of edge_ids are connected
// also checks if the last vertex and the first vertex are the same

int awalk(Graph *g, Cycle C) {
    for(unsigned int z = 0; z < C.length - 1; z++) {
        // return false if the second vertex of the first edge is not the same as the first vertex of the second edge
        if(arcs(g, C.path[z]).second != arcs(g, C.path[z+1]).first) return 0;
    }
    return 1;
}

// returns the total cost of the path

int awalk_cost(int *c, unsigned int *path, unsigned int length) {
    int total = 0;
    for(unsigned int e = 0; e < length; e++) {
        total = total + c[path[e]];
    }
    return total;
}

// assume that a cycle is defined with a fixed length
// then the following holds

int C_se(Graph *g, Cycle *C, int *c, unsigned int nc, ENInt *dist) {
    for(unsigned int y = 0; y < nc; y++) {
        if(dist[C[y].start].isInf > 0) return 0;
        if(awalk(g, C[y]) == 0) return 0;
        if(awalk_cost(c, C[y].path, C[y].length) >= 0) return 0;
    }
    return 1;
}

// checks if a vertex s is connected to the vertex v given a list of parent edges of each respective vertices

int is_connected(Graph *g, unsigned int s, int *p, unsigned int v) {
    unsigned int n = v;
    // the while loop will eventually terminate given n is either the source vertex or some other disjoint vertex
    while(p[n] >= 0) {
        if(n == s) return 1;
        n = arcs(g, p[n]).first;
    }
    return 0;
}

// pwalk: function from vertices to paths.
// it is the path obtained by concatenating the edges defined by the parent-edge function form v to s for vertices in Vf union Vm different from s, otherwise it is the empty path.

// int_neg_cyc: For each vertex v in Vm, pwalk v intersects a cycle in C
// hence, each vertex v in Vm is connected to s with a walk that contains a negative cycle 
// maybe define pwalk internally?

// note pedge defines the edgeid of parent edges of vertices
int int_neg_cyc(Graph *g, unsigned int s, ENInt *dist, Cycle *C, int *c, int *p, unsigned int nc) {
    unsigned int u;
    unsigned int i;
    unsigned int is_neg_cycle;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf < 0) {
            is_neg_cycle = 0;
            // check if v == s, whcih we then check if s itself is the start of a negative cycle
            if(v == s) {
                for(i = 0; i < nc; i++) {
                    if(s == C[i].start) is_neg_cycle = 1;
                }
            }
            // if is_connected returns false, then a path from s to v does not exist, which is false
            if(is_connected(g, s, p, v) == 0) return 0;
            // checks every vertex u between s and v.
            // the next vertex on the loop will always be the predecessing vertex on the path
            // since is_connected is true, the for loop will terminate towards s, where 
            for(u = v; v != s; v = arcs(g, p[u]).first) {
                for(i = 0; i < nc; i++) {
                    if(u == C[i].start) is_neg_cycle = 1;
                }
            }
            if(is_neg_cycle == 0) return 0;
        }
    }
    return 1;
}
*/
int shortest_paths_locale_step1(Graph *g, unsigned int s, int *c, EInt *num, int *pred, ENInt *dist) {
    if(!is_wellformed(g)) return 0;
    if(!s_assms(g, s, dist, pred, num)) return 0;
    if(!parent_num_assms(g, s, dist, pred, num)) return 0;
    // if(!no_p_edge(g, dist)) return 0;
    return 1;
}

int shortest_paths_locale_step2(Graph *g, unsigned int s, int *c, EInt *num, int *pred, ENInt *dist) {
    if(!shortest_paths_locale_step1(g, s, c, num, pred, dist)) return 0;
    if(!check_basic_just_sp(g, dist, c, s, num, pred)) return 0;
    if(!source_val(g, s, dist, num)) return 0;
    if(!no_edge_Vm_Vf(g, dist)) return 0;
    return 1;
}
/*
int shortest_paths_locale_step3(Graph *g, unsigned int s, int *c, EInt *num, int *pred, ENInt *dist, Cycle *C, unsigned int nc) {
    if(shortest_paths_locale_step2(g, s, c, num, pred, dist) == 0) return 0;
    if(C_se(g, C, c, nc, dist) == 0) return 0;
    if(int_neg_cyc(g, s, dist, C, c, pred, nc) == 0) return 0;
    return 1;
}*/


int main(int argc, char **argv) {
    return 0;
}
