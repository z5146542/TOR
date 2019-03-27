// Graph.c
// Seung Hoon Park and Christine Rizkallah


typedef struct IEdge {
	unsigned int first;
	unsigned int second;
} IEdge;

typedef struct IGraph {
	unsigned int num_vertices;
	unsigned int num_edges;
	IEdge *arcs;
} IGraph;

//typedef int enat;
typedef struct EInt {
	unsigned int val;
  // For dist:
	// isInf < 0 --> -inf
	// isInf = 0 --> finite, value determined by .val
	// isInf > 0 --> inf
  // For num:
	// isInf < 0 --> inf
	// isInf = 0 --> finite, value determined by .val
	// isInf > 0 --> inf
	int isInf;
} EInt;

// Cycle contains a starting vertex, the length of the path, and the path itself

typedef struct Cycle {
	unsigned int start;
	unsigned int length;
	unsigned int *path;
} Cycle;

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// Procedures

// the following procedures are from the nonnegative shortest path 

int is_wellformed(IGraph *g) {
	IEdge e;
	for(unsigned int i = 0; i < edge_cnt(g); i++) {
		e = arcs(g, i);
		if(vertex_cnt(g) <= e.first) return 0;
		if(vertex_cnt(g) <= e.second) return 0;
	}
	return 1;
}

int trian(IGraph *g, EInt *dist, int *c) {
	for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		// confirms the distance to some vertices are finite
		if(dist[arcs(g, edge_id).second].isInf != 0) return 0;
		if(dist[arcs(g, edge_id).first].isInf != 0) return 0;
		if(dist[arcs(g, edge_id).second].val > dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
	}
	return 1;
}

int just(IGraph *g, EInt *dist, int *c, unsigned int s, EInt *onum, int *pred) {
	unsigned int edge_id;
	for(unsigned int v = 0; v < vertex_cnt(g); v++) {
		edge_id = (unsigned int) pred[v];
		if(v != s) {
			if(onum[v].isInf == 0) {
				if(edge_id >= edge_cnt(g)) return 0;
				if(arcs(g, edge_id).second != v) return 0;
				// confirms the distance to some vertices are finite
				if(dist[v].isInf != 0) return 0;
				if(dist[arcs(g, edge_id).first].isInf != 0) return 0;
				if(dist[v].val != dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
				if(onum[v].val != onum[arcs(g, edge_id).first].val + 1) return 0;
			}
		}
	}
	return 1; 
}

int check_basic_just_sp(IGraph *g, EInt *dist, int *c, unsigned int s, EInt *onum, int *pred) {
	if(!is_wellformed(g)) return 0;
	if(dist[s].isInf > 0) return 0;
	if(dist[s].isInf == 0 && dist[s].val > 0) return 0;
	if(!trian(g, dist, c)) return 0;
	if(!just(g, dist, c, s, onum, pred)) return 0;
	return 1;
}

// the folloiwng are for the general-weight edge shrotest path

int s_assums(IGraph *g, unsigned int s, EInt *dist, int *pred, EInt *onum) {
	if(s >= vertex_cnt(g)) return 0;
	if(dist[s].isInf > 0) return 0;
	if(pred[s] >= 0) return 0;
	if(onum[s].val != 0) return 0;
	return 1;
}

int parent_num_assms(IGraph *g, unsigned int s, EInt *dist, int *pred, EInt *onum) {
	unsigned int edge_id;
	for(unsigned int v = 0; v < vertex_cnt(g); v++) {
		edge_id = pred[v];
		if(v != s) {
			if(dist[v].isInf <= 0) {
				if(edge_id >= edge_cnt(g)) return 0;
				if(arcs(g, edge_id).second != v) return 0;
				if(dist[arcs(g, edge_id).first].isInf > 0) return 0;
				if(onum[v].val != onum[arcs(g, edge_id).first].val + 1) return 0;
			}
		}
	}
	return 1;
}

int no_p_edge(IGraph *g, EInt *dist) {
	for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		if(dist[arcs(g, edge_id).first].isInf <= 0) {
			if(dist[arcs(g, edge_id).second].isInf > 0) return 0;
		}
	}
	return 1;
}

int source_val(IGraph *g, unsigned int s, EInt *dist, EInt *onum){
	for(unsigned int v = 0; v < vertex_cnt(g); v++) {
		if(onum[v].isInf == 0 && onum[v].val == 0) {
			if(dist[s].isInf == 0) {
				if(dist[s].val == 0) return 1;
			}
		}
	}
	return 0;
}

int no_edge_Vm_Vf(IGraph *g, EInt *dist) {
	for(unsigned int edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		if(dist[arcs(g, edge_id).first].isInf < 0) {
			if(dist[arcs(g, edge_id).second].isInf == 0) return 0;
		}
	}
	return 1;
}

// helpers

// checks if the sequence of edge_ids are connected
// also checks if the last vertex and the first vertex are the same

int awalk(IGraph *g, Cycle C) {
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

int C_se(IGraph *g, Cycle *C, int *c, unsigned int nc, EInt *dist) {
	for(unsigned int y = 0; y < nc; y++) {
		if(dist[C[y].start].isInf > 0) return 0;
		if(awalk(g, C[y]) == 0) return 0;
		if(awalk_cost(c, C[y].path, C[y].length) >= 0) return 0;
	}
	return 1;
}

// checks if a vertex s is connected to the vertex v given a list of parent edges of each respective vertices

int is_connected(IGraph *g, unsigned int s, int *p, unsigned int v) {
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
int int_neg_cyc(IGraph *g, unsigned int s, EInt *dist, Cycle *C, int *c, int *p, unsigned int nc) {
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

int shortest_paths_locale_step1(IGraph *g, unsigned int s, int *c, EInt *onum, int *pred, EInt *dist) {
	if(s_assums(g, s, dist, pred, onum) == 0) return 0;
	if(parent_num_assms(g, s, dist, pred, onum) == 0) return 0;
	if(no_p_edge(g, dist) == 0) return 0;
	return 1;
}

int shortest_paths_locale_step2(IGraph *g, unsigned int s, int *c, EInt *onum, int *pred, EInt *dist) {
	if(shortest_paths_locale_step1(g, s, c, onum, pred, dist) == 0) return 0;
	if(check_basic_just_sp(g, dist, c, s, onum, pred) == 0) return 0;
	if(source_val(g, s, dist, onum) == 0) return 0;
	if(no_edge_Vm_Vf(g, dist) == 0) return 0;
	return 1;
}

int shortest_paths_locale_step3(IGraph *g, unsigned int s, int *c, EInt *onum, int *pred, EInt *dist, Cycle *C, unsigned int nc) {
	if(shortest_paths_locale_step2(g, s, c, onum, pred, dist) == 0) return 0;
	if(C_se(g, C, c, nc, dist) == 0) return 0;
	if(int_neg_cyc(g, s, dist, C, c, pred, nc) == 0) return 0;
	return 1;
}


int main(int argc, char **argv) {
	return 0;
}
