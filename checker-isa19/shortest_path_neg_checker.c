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
// may not be necessary; remove for now
/*
typedef struct Cycle {
    // 'a 
    unsigned int start;
    // 'b awalk; needs two components in C
    unsigned int length;
    unsigned int *path;
} Cycle;
*/

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// for the label array
#define UNKNOWN         0
#define PLUS            1
#define FINITE          2
#define ON_CURR_PATH    3
#define ATT_TO_CYC      4
#define CYC             5
#define NEG_CYC         6


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

// locale 3
// cycles : array of size vertex_cnt(g). cycles[v] < 0 --> v is not in a negative cycle
//          cycles[v] >= 0 --> v is in a negative cycle, and cycles[v] returns the edge that's part of the cycle
//          note: if there is a vertex v, part of a negative cycle, where there is an edge (v, u) that denotes the next veretex,
//          then cycles[v] returns the edge (v, u) where arcs(g, cycles[v]).first = v, unlike pedge, which is the opposite case.
// visited: array of size vertex_cnt(g). All vertices are initially 0. When visited, value increments by 1.
/*
int C_se(Graph *g, int *c, ENInt *dist, int *cycles, unsigned int *visited) {
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(cycles[v] >= 0 && visited[v] == 0) {
            unsigned int cycle_edge = cycles[v];
            // dist u = -inf
            if(dist[v].isInf >= 0) return 0;
            // awalk u p v
            // awalk u p v -> u in verts G (no need to check as v is always in vertex of g)
            // if(v >= vertex_cnt(g)) return 0;
            // awalk u p v -> set p subsetof arcs G
            if(cycle_edge >= edge_cnt(g)) return 0;
            // awalk u p v -> cas u p v
            if(v != arcs(g, cycle_edge).first) return 0;
            // check for all other vertices
            // also check awalk_cost here
            visited[v] = 1;
            long cost = c[cycle_edge];
            unsigned int start_vert = v;
            unsigned int curr_vert = arcs(g, cycle_edge).second;
            while(start_vert != curr_vert) {
                // check if vertex already visited; should not be the case
                if(visited[curr_vert] != 0) return 0;
                cycle_edge = cycles[curr_vert];
                // awalk u p v -> set p subsetof arcs G
                if(cycle_edge >= edge_cnt(g)) return 0;
                // awalk u p v -> cas u p v
                if(curr_vert != arcs(g, cycle_edge).first) return 0;
                visited[curr_vert] = 1;;
                cost += c[cycle_edge];
                curr_vert = arcs(g, cycle_edge).second;
            }
            if(cost >= 0) return 0;
        }
    }
    return 1;
}
*/

// C_se must check two properties as per the theory file.
// 1. check that negative cycles are actually cycles
// 2. check that negative cycles have negative cumulative cost
int C_se(Graph *g, int *c, unsigned int s, ENInt *dist, int *pred, int *label) {
    // the following labelling idea is adapted from the LEDA checker algorithm. 
    // precondition: label is an array of size vertex_cnt(g). 
    // first: iterate through array, label vertices v with dist[v].isInf > 0 PLUS
    //                                                     otherwise         UNKNOWN
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf > 0) label[v] = PLUS;
        else label[v] = UNKNOWN;
    }

    // initial condition
    if(pred[s] < 0) label[s] = FINITE;

    // next, we iterate through each vertices
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        // only perform the following if v is not labelled
        if(label[v] == UNKNOWN) {
            // initialise stack. This will track which vertices will potentially be a cycle once it is detected
            Stack s = new_stack();
            unsigned int w = v;
            // iterate through pred until non-UNKNOWN vertex is visited
            while(label[w] == UNKNOWN) {
                label[w] = ON_CURR_PATH;
                s.push(w);
                w = arcs(g, pred[w]).first;
            }
            unsigned int t = label[w];
            // at this point, a non-UNKNOWN vertex is visited. Two cases here:
            // case 1: forming a new negative cycle
            if(t == ON_CURR_PATH) {
                unsigned int z;
                do {
                    z = s.pop();
                    label[z] = CYC;
                } while (z != w);
                // remaining vertices in stack are attached to this negative cycle. Label them as such.
                while (!s.empty()) label[s.pop()] = ATT_TO_CYC;
            }
            // case 2: negative cycle or ATT_TO_NEG_CYC already defiend for w. Then the vertices in the stack are attached to a negative cycle.
            //         or, the vertex is simply in the finite set. 
            if(t == CYC) t = ATT_TO_CYC;
            while(!s.empty()) label[s.pop()] = t;
        }
    }

    // finally, check that each negative cycle is negative in cumulative cost
    for(unsigned int v = 0; v < vertex_cnt(g); v++) {
        if(label[v] == NEG_CYC) {
            unsigned int w = v;
            long total_cost = 0;
            do {
                total_cost == c[pred[w]];
                label[w] = NEG_CYC;
                w = arcs(g, pred[w]).first;
            } while(w != v);
            if(total_cost >= 0) return 0;
        }
    } 

    return 1;
}


// visited: at this point, dist[v] = -inf && visited[v] = 0 --> v is in V_m but not in negative cycle
//                         dist[v] = -inf && visited[v] = 1 --> v is in V_m and is in negative cycle
//                         any other combination: v not in V_m. Note: visited[v] must be 0 in this case
// idea: find all v s.t.   dist[v] = -inf && visited[v] = 0 and check if arcs(g, pedge[v]).first
//       is connected to a negative cycle and so on... 
int int_neg_cyc(Graph *g, unsigned int s, ENInt *dist, int *c, int *p, unsigned int *visited) {
    for(int v = 0; v < vertex_cnt(g); v++) {
        if(dist[v].isInf < 0 && visited[v] == 0) {
            int pedge = p[v];
            // must check if parent edge exists first
            if(pedge < 0) return 0;
            visited[v] = 1;
            unsigned int curr_vert = arcs(g, pedge).first;
            while(visited[curr_vert] != 0) {
                if(dist[curr_vert].isInf >= 0) return 0;
                pedge = p[curr_vert];
                if(pedge < 0) return 0;
                visited[curr_vert] = 1;
                curr_vert = arcs(g, pedge).first;
            }    
        }
    }
    return 1;
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

int shortest_paths_locale_step3(Graph *g, unsigned int s, int *c, unsigned int *num, int *pred, ENInt *dist, int *cycles, unsigned int *visited) {
    if(shortest_paths_locale_step2(g, s, c, num, pred, dist) == 0) return 0;
    for(unsigned int i = 0; i < vertex_cnt(g); i++) visited[i] = 0;
    if(C_se(g, c, dist, cycles, visited) == 0) return 0;
    if(int_neg_cyc(g, s, dist, c, pred, visited) == 0) return 0;
    return 1;
}

int main(int argc, char **argv) {
    return 0;
}
