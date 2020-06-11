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

// Cycle contains a starting vertex, the length of the path, and the path itself
typedef struct Cycle {
    // 'a 
    unsigned int start;
    // 'b awalk; needs two components in C
    unsigned int length;
    unsigned int *path;
} Cycle;

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
int s_assms(Graph *g, unsigned int s, ENInt *dist, int *pred, unsigned int *num) {
    if(s >= vertex_cnt(g)) return 0;
    if(dist[s].isInf > 0) return 0;
    if(!(pred[s] < 0)) return 0;
    if(num[s] != 0) return 0;
    return 1;
}

int parent_num_assms(Graph *g, unsigned int s, ENInt *dist, int *pred, unsigned int *num) {
    unsigned int edge_id;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        edge_id = (unsigned int) pred[v];
        if(v != s) {
            if(dist[v].isInf <= 0) {
                if(pred[v] < 0) return 0;
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


// the following functions are all related to locale 3, which will be dealt with later. 

// helpers

int awalk(Graph *g, unsigned int u, unsigned int length, unsigned int *path, unsigned int v) {
    // u in verts G
    if(u >= vertex_cnt(g)) return 0;
    // set p subsetof arcs G
    for(int i = 0; i < length; i++)
        if(path[i] >= edge_cnt(g)) return 0;
    // cas u p v
    // if(!(cas(g, u, length, path, v))) return 0;
    unsigned int edge_id;
    unsigned int next = u;
    for(unsigned int i = 0; i <= length; i++) {
        // cas u [] v = (u = v)
        if(i == length) {
            if(next != v) return 0;
            return 1;
        }
        edge_id = path[i];
        // tail G e = u
        if(arcs(g, edge_id).first != next) return 0;
        // cas (head G e) es v
        next = arcs(g, edge_id).second;
    }   
    return 1;
}

// returns the total cost of the path

int awalk_cost(int *c, unsigned int length, unsigned int *path) {
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
        if(awalk(g, C[y].start, C[y].length, C[y].path, C[y].start) == 0) return 0;
        if(awalk_cost(c, C[y].length, C[y].path) >= 0) return 0;
    }
    return 1;
}

// int_neg_cyc: For each vertex v in Vm, pwalk v intersects a cycle in C
// hence, each vertex v in Vm is connected to s with a walk that contains a negative cycle 
// maybe define pwalk internally?

// note pedge defines the edgeid of parent edges of vertices
int int_neg_cyc(Graph *g, unsigned int s, ENInt *dist, Cycle *C, unsigned int nc, int *c, int *p) {
    unsigned int edge_id;
    unsigned int baby_vertex;
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf < 0) {
            // idea: sort the Cycle array in terms of the start element in increasing order (do this outside the for loop)
            //       or for simplicity, just use sequential search (probably reduces complexity of verification at the cost of t cplxty)
            //       implement pwalk within function, where pwalk produces an array of edges
            //       or alternatively, implement an array of vertices where each succeeding pair is an edge (s only if empty)
            //       for each vertex in the the awalks_verts array, perform binary search on Cycle.start to find if 
            //       intersecting element is present.
            //       If present, continue (as this implies intersection is not the empty set)
            // case: parent(fst edge) is negative
            //       just check source
            //       parent(v).first outputs vertex
            //       check if fst edge is in start of any cycle by bin/seq search
            //       if exists, check next vertex parent(v).snd, otherwise return 0
            edge_id = p[v];
            baby_vertex = arcs(g, edge_id).first;
            while(p[baby_vertex] > 0 && dist[baby_vertex].isInf <= 0 && baby_vertex < vertex_cnt(g)) {
                // TODO: serach if baby_vertex = any start of a cycle
                // return 1 if true, continue if false
                edge_id = p[arcs(g, edge_id).second];
                baby_vertex = arcs(g, edge_id).first;
            }
            // final case: check if last vertex is in cycle
            // last vertex is either source, start of a different component of the same graph
            // TODO: search if baby_vertex = any start of a cycle
            // return 1 if exists, continue if false
        }
    }
    return 0;
}

int shortest_paths_locale_step1(Graph *g, unsigned int s, unsigned int *num, int *pred, ENInt *dist) {
    if(!is_wellformed(g)) return 0;
    if(!s_assms(g, s, dist, pred, num)) return 0;
    if(!parent_num_assms(g, s, dist, pred, num)) return 0;
    return 1;
}

int shortest_paths_locale_step2(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist) {
    if(!shortest_paths_locale_step1(g, s, num, pred, dist)) return 0;
    if(!check_basic_just_sp(g, dist, c, s, num, pred)) return 0;
    if(!source_val(g, s, dist, num)) return 0;
    if(!no_edge_Vm_Vf(g, dist)) return 0;
    return 1;
}

int shortest_paths_locale_step3(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, Cycle *C, unsigned int nc) {
    if(shortest_paths_locale_step2(g, s, c, num, pred, dist) == 0) return 0;
    if(C_se(g, C, c, nc, dist) == 0) return 0;
    if(int_neg_cyc(g, s, dist, C, nc, c, pred) == 0) return 0;
    return 1;
}

int main(int argc, char **argv) {
    return 0;
}
