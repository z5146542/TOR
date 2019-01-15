// Graph.c
// Seung Hoon Park

// Type Synonums

typedef unsigned int nat;
//typedef int enat;
typedef struct enat {
	int val;
	// inf_status < 0 --> -inf
	// inf_status = 0 --> finite, value determined by .val
	// inf_status > 0 --> inf
	int inf_status;
} enat;


typedef nat Vertex;
typedef nat Edge_Id;
typedef int Cost;
typedef enat Dist;
typedef int PEdge;
typedef int Num;

typedef struct Edge {
	Vertex first;
	Vertex second;
} Edge;

typedef struct Graph {
	nat num_vertices;
	nat num_edges;
	Edge *arcs;
} Graph;

// Cycle contains a starting vertex, the length of the path, and the path itself

typedef struct Cycle {
	Vertex start;
	nat length;
	Edge_Id *path;
} Cycle;

// Abbreviations

#define vertex_cnt(g) g->num_vertices

#define edge_cnt(g) g->num_edges

#define arcs(g, e) g->arcs[e]

// Procedures

// the following procedures are from the nonnegative shortest path 

int is_wellformed(Graph *g) {
	Edge e;
	nat i;
	for(i = 0; i < edge_cnt(g); i++) {
		e = arcs(g, i);
		if(vertex_cnt(g) <= e.first) return 0;
		if(vertex_cnt(g) <= e.second) return 0;
	}
	return 1;
}

int trian(Graph *g, Dist *dist, Cost *c) {
	Edge_Id edge_id;
	for(edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		// confirms the distance to some vertices are finite
		if(dist[arcs(g, edge_id).second].inf_status > 0) return 0;
		if(dist[arcs(g, edge_id).first].inf_status > 0) return 0;
		if(dist[arcs(g, edge_id).second].val > dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
	}
	return 1;
}

int just(Graph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	Edge_Id edge_id;
	Vertex v;
	for(v = 0; v < vertex_cnt(g); v++) {
		edge_id = pred[v];
		if(v != s) {
			if(onum[v] >= 0) {
				if(edge_id >= edge_cnt(g)) return 0;
				if(arcs(g, edge_id).second != v) return 0;
				// confirms the distance to some vertices are finite
				if(dist[v].inf_status != 0) return 0;
				if(dist[arcs(g, edge_id).first].inf_status != 0) return 0;
				if(dist[v].val != dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
				if(onum[v] != onum[arcs(g, edge_id).first] + 1) return 0;
			}
		}
	}
	return 1; 
}

int no_path(Graph *g, Dist *dist, Num *onum) {
	for(Vertex v = 0; v < vertex_cnt(g); v++) {
		if(dist[v].inf_status > 0) {
			if(onum[v] >= 0) return 0;
		}
		else {
			if(onum[v] < 0) return 0;
		}
	}
	return 1;
}

int pos_cost(Graph *g, Cost *c) {
	Edge_Id edge_id;
	for(edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		if(c[edge_id] < 0) return 0;
	}
	return 1;
}

int check_basic_just_sp(Graph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	if(!is_wellformed(g)) return 0;
	if(dist[s].inf_status != 0) return 0;
	if(dist[s].val > 0) return 0;
	if(!trian(g, dist, c)) return 0;
	if(!just(g, dist, c, s, onum, pred)) return 0;
	return 1;
}

int check_sp(Graph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	if(!check_basic_just_sp(g, dist, c, s, onum, pred)) return 0;
	if(s >= vertex_cnt(g)) return 0;
	if(dist[s].inf_status != 0) return 0;
	if(dist[s].val != 0) return 0;
	if(!no_path(g, dist, onum)) return 0;
	if(!pos_cost(g, c)) return 0;
	return 1;
}

// the folloiwng are for the general-weight edge shrotest path

int s_assums(Graph *g, Vertex s, Dist *dist, PEdge *pred, Num *onum) {
	if(s >= vertex_cnt(g)) return 0;
	if(dist[s].inf_status > 0) return 0;
	if(pred[s] >= 0) return 0;
	if(onum[s] != 0) return 0;
	return 1;
}

int parent_num_assms(Graph *g, Vertex s, Dist *dist, PEdge *pred, Num *onum) {
	Vertex v;
	Edge_Id edge_id;
	for(v = 0; v < vertex_cnt(g); v++) {
		edge_id = pred[v];
		if(v != s) {
			if(dist[v].inf_status <= 0) {
				if(edge_id >= edge_cnt(g)) return 0;
				if(arcs(g, edge_id).second != v) return 0;
				if(dist[arcs(g, edge_id).first].inf_status > 0) return 0;
				if(onum[v] != onum[arcs(g, edge_id).first] + 1) return 0;
			}
		}
	}
	return 1;
}

int no_p_edge(Graph *g, Dist *dist) {
	Edge_Id edge_id;
	for(edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		if(dist[arcs(g, edge_id).first].inf_status <= 0) {
			if(dist[arcs(g, edge_id).second].inf_status > 0) return 0;
		}
	}
	return 1;
}

int source_val(Graph *g, Vertex s, Dist *dist, Num *onum){
	Vertex v;
	for(v = 0; v < vertex_cnt(g); v++) {
		if(onum[v] > 0) {
			if(dist[s].inf_status != 0) return 0;
			if(dist[s].val != 0) return 0;
		}
	}
	return 1;
}

int no_edge_Vm_Vf(Graph *g, Dist *dist) {
	Edge_Id edge_id;
	for(edge_id = 0; edge_id < edge_cnt(g); edge_id++) {
		if(dist[arcs(g, edge_id).first].inf_status < 0) {
			if(dist[arcs(g, edge_id).second].inf_status == 0) return 0;
		}
	}
	return 1;
}

// helpers

// checks if the sequence of edge_ids are connected
// also checks if the last vertex and the first vertex are the same

int awalk(Graph *g, Cycle *C, nat y, nat last_edge) {
	nat z;
	for(z = 0; z < last_edge; z++) {
		// return false if the second vertex of the first edge is not the same as the first vertex of the second edge
		if(arcs(g, C[y].path[z]).second != arcs(g, C[y].path[z+1]).first) return 0;
	}
	// if the first vertex and the last vertex are not the same return false
	if(C[y].start != arcs(g, C[y].path[last_edge]).second) return 0;
	return 1;
}

// returns the total cost of the path

int awalk_cost(Graph *g, Cost *c, Edge_Id *path, nat length) {
	int total = 0;
	nat e;
	for(e = 0; e < length; e++) {
		total = total + c[path[e]];
	}
	return total;
}

// assume that a cycle is defined with a fixed length
// then the following holds

int C_se(Graph *g, Cycle *C, Cost *c, nat nc, Dist *dist) {
	nat y;
	Edge_Id last_edge;
	for(y = 0; y < nc; y++) {
		last_edge = C[y].length - 1;
		if(dist[C[y].start].inf_status > 0) return 0;
		if(awalk(g, C, y, last_edge) == 0) return 0;
		if(awalk_cost(g, c, C[y].path, C[y].length) >= 0) return 0;
	}
	return 1;
}

// pwalk: function from vertices to paths.
// it is the pathobtained by concatenating the edges defined by the parent-edge function form v to s for vertices in Vf union Vm different from s, otherwise it is the empty path.

// int_neg_cyc: For each vertex v in Vm, pwalk v intersects a cycle in C
// hence, each vertex v in Vm is connected to s with a walk that contains a negative cycle 
// maybe define pwalk internally? should this be done on the verification level?

int int_neg_cyc(Graph *g, Dist *dist, Cycle *C, Cost *c, PEdge *p, nat nc) {
	Vertex v;
	int u;
	for(v = 0; v < vertex_cnt(g); v++) {
		if(dist[v].inf_status < 0) {
			// check if any vertex in pwalk v intersects with the first vertex on a cycle struct
			// done by obtaining pwalk v first
			// then check for each element in pwalk v if it matches an element in one of the cycle
			// once there is a match halt
			for(u = v; u >= 0; u = )
		}
	}
	return 1;
}

int shortest_paths_locale_step1(Graph *g, Vertex s, Cost *c, Num *onum, PEdge *pred, Dist *dist) {
	if(s_assums(g, s, dist, pred, onum) == 0) return 0;
	if(parent_num_assms(g, s, dist, pred, onum) == 0) return 0;
	if(no_p_edge(g, dist) == 0) return 0;
	return 1;
}

int shortest_paths_locale_step2(Graph *g, Vertex s, Cost *c, Num *onum, PEdge *pred, Dist *dist) {
	if(shortest_paths_locale_step1(g, s, c, onum, pred, dist) == 0) return 0;
	if(check_basic_just_sp(g, dist, c, s, onum, pred) == 0) return 0;
	if(source_val(g, s, dist, onum) == 0) return 0;
	if(no_edge_Vm_Vf(g, dist) == 0) return 0;
	return 1;
}

int shortest_paths_locale_step3(Graph *g, Vertex s, Cost *c, Num *onum, PEdge *pred, Dist *dist, Cycle *C, nat nc) {
	if(shortest_paths_locale_step2(g, s, c, onum, pred, dist) == 0) return 0;
	if(C_se(g, C, c, nc, dist) == 0) return 0;
	if(int_neg_cyc(g, dist, C, c, pred, nc) == 0) return 0;
	return 1;
}


int main(int argc, char **argv) {
	return 0;
}
