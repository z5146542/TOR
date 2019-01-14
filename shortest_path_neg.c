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
	PEdge *path;
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

int awalk_cost(Graph *g, Cost *c, PEdge *p, nat length) {
	int total = 0;
	nat e;
	for(e = 0; e < length; e++) {
		total = total + c[p[e]];
	}
	return total;
}

int pwalk_verts() {
	return 1;
}

// assume that a cycle is defined with a fixed length
// then the following holds

int C_se(Graph *g, Cycle *C, Cost *c, nat nc, Dist *dist) {
	nat y;
	Edge_Id last_edge;
	for(y = 0; y < nc; y++) {
		last_edge = C[y].length - 1;
		if(dist[C[y].start].inf_status > 0) return 0;
		if(C[y].start != arcs(g, last_edge).second) return 0;
		if(awalk_cost(g, c, C[y].path, C[y].length) >= 0) return 0;
	}
	return 1;
}

int int_neg_cyc(Graph *g, Dist *dist, Cycle *C, Cost *c, nat nc) {
	Vertex v;
	nat y;
	for(v = 0; v < vertex_cnt(g); v++) {
		if(dist[v].inf_status < 0) {
			for(y = 0; y < nc; y++) {
				// TODO: finish implementation "(fst ` C) \cap pwalk_verts v != {}"
				if(pwalk_verts()) return 0;
			}
		}
	}
	return 1;
}

int main(int argc, char **argv) {
	return 0;
}
