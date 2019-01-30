// Graph.c
// Seung Hoon Park

// Type Synonums

typedef struct IEdge {
	unsigned int first;
	unsigned int second;
} IEdge;

typedef struct IGraph {
	unsigned int num_edges;
	unsigned int num_vertices;
	IEdge *arcs;
} IGraph;

// Abbreviations

#define ivertex_cnt(g) g->num_vertices

#define iedge_cnt(g) g->num_edges

#define iarcs(g, e) g->arcs[e]

// Procedures

int is_wellformed(IGraph *g) {
	IEdge e;
	for(unsigned int i = 0; i < iedge_cnt(g); i++) {
		e = iarcs(g, i);
		if(ivertex_cnt(g) <= e.first) return 0;
		if(ivertex_cnt(g) <= e.second) return 0;
	}
	return 1;
}

int trian(IGraph *g, int *dist, unsigned int *c) {
	for(unsigned int edge_id = 0; edge_id < iedge_cnt(g); edge_id++) {
		if (dist[iarcs(g, edge_id).second] > dist[iarcs(g, edge_id).first] + c[edge_id]) return 0;
	}
	return 1;
}

int just(IGraph *g, int *dist, unsigned int *c, unsigned int s, int *enu, int *pred) {
	unsigned int edge_id;
	for(unsigned int v = 0; v < ivertex_cnt(g); v++) {
		edge_id = pred[v];
		if(v != s) {
			if(enu[v] >= 0) {
				if(edge_id >= iedge_cnt(g)) return 0;
				if(iarcs(g, edge_id).second != v) return 0;
				if(dist[v] != dist[iarcs(g, edge_id).first] + c[edge_id]) return 0;
				if(enu[v] != enu[iarcs(g, edge_id).first] + 1) return 0; // onum
			}
		}
	}
	return 1;
}

int no_path(IGraph *g, int *dist, int *enu) {
	for(unsigned int v = 0; v < ivertex_cnt(g); v++) {
		if(dist[v] < 0) {
			if(enu[v] >= 0) return 0;
		}
		else {
			if(enu[v] < 0) return 0;
		}
	}
	return 1;
}

int pos_cost(IGraph *g, unsigned int *c) {
	for(unsigned int edge_id = 0; edge_id < iedge_cnt(g); edge_id++) {
		if(c[edge_id] < 0) return 0;
	}
	return 1;
}

int check_basic_just_sp(IGraph *g, int *dist, unsigned int *c, unsigned int s, int *enu, int *pred) {
	if(!is_wellformed(g)) return 0;
	if(dist[s] > 0) return 0;
	if(!trian(g, dist, c)) return 0;
	if(!just(g, dist, c, s, enu, pred)) return 0;
	return 1;
}

int check_sp(IGraph *g, int *dist, unsigned int *c, unsigned int s, int *enu, int *pred) {
	if(!check_basic_just_sp(g, dist, c, s, enu, pred)) return 0;
	if(s >= ivertex_cnt(g)) return 0;
	if(dist[s] != 0) return 0;
	if(!no_path(g, dist, enu)) return 0;
	if(!pos_cost(g, c)) return 0;
	return 1;
}

int main(int argc, char **argv) {
	return 0;
}
