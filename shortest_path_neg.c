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
typedef enat Num;

typedef struct Edge {
	Vertex first;
	Vertex second;
} Edge;

typedef struct Graph {
	nat num_vertices;
	nat num_edges;
	Edge *arcs;
} Graph;

// for set of cycles?

typedef struct Cycle {
	Vertex start;
	nat length;
	Vertex *path;
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
		if (dist[arcs(g, edge_id).second].val > dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
	}
	return 1;
}

int just(Graph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	Edge_Id edge_id;
	Vertex v;
	for(v = 0; v < vertex_cnt(g); v++) {
		edge_id = pred[v];
		if(v != s) {
			if(onum[v].inf_status <= 0) {
				if(edge_id >= edge_cnt(g)) return 0;
				if(arcs(g, edge_id).second != v) return 0;
				if(dist[v].val != dist[arcs(g, edge_id).first].val + c[edge_id]) return 0;
				if(onum[v].val != onum[arcs(g, edge_id).first].val + 1) return 0; // onum
			}
		}
	}
	return 1;
}

int no_path(Graph *g, Dist *dist, Num *onum) {
	for(Vertex v = 0; v < vertex_cnt(g); v++) {
		if(dist[v].inf_status > 0) {
			if(onum[v].inf_status <= 0) return 0;
		}
		else {
			if(onum[v].inf_status > 0) return 0;
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

int check_basic_just_sp(Gist[s].inf_status raph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	if(!is_wellformed(g)) return 0;
	if(dist[s].val > 0) return 0;
	if(!trian(g, dist, c)) return 0;
	if(!just(g, dist, c, s, onum, pred)) return 0;
	return 1;
}

int check_sp(Graph *g, Dist *dist, Cost *c, Vertex s, Num *onum, PEdge *pred) {
	if(!check_basic_just_sp(g, dist, c, s, onum, pred)) return 0;
	if(s >= vertex_cnt(g)) return 0;
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
	if(onum[s].val != 0) return 0;
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
				if(onum[v].val != onum[arcs(dist[s].inf_status > 0) retcs(g, edge_id).first].val + 1) return 0;
			}
		}(dist[s].inf_status > 0) ret
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
		if(onum[v].inf_status == 0) {
			if((dist[s].inf_status == 0 && dist[s].val != 0) || dist[s].inf_status != 0) return 0;
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

int C_se(Cycle C) {
	
	return 1;
}

int int_neg_cyc() {
	return 1;
}

int main(int argc, char **argv) {
	return 0;
}
