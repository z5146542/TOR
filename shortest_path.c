// Graph.c
// Seung Hoon Park

// Type Synonums

typedef unsigned int nat;
typedef struct enat {
	nat val;
	int isInf;
} enat;

typedef nat IVertex;
typedef nat IEdge_Id;
typedef nat ICost;
typedef enat IDist; // use enat for now to avoid messy float calculations
typedef enat IPEdge;
typedef enat INum;

typedef struct IEdge {
	IVertex first;
	IVertex second;
} IEdge;

typedef struct IGraph {
	nat num_vertices;
	nat num_edges;
	IEdge *arcs;
} IGraph;

// Abbreviations

#define ivertex_cnt(g) g->num_vertices

#define iedge_cnt(g) g->num_edges

#define iarcs(g, e) g->arcs[e]

// Procedures

int is_wellformed(IGraph *g) {
	IEdge e;
	nat i;
	for(i = 0; i < iedge_cnt(g); i++) {
		e = iarcs(g, i);
		if(ivertex_cnt(g) <= e.first) return 0;
		if(ivertex_cnt(g) <= e.second) return 0;
	}
	return 1;
}

int trian(IGraph *g, IDist *dist, ICost *c) {
	IEdge_Id edge_id;
	for(edge_id = 0; edge_id < iedge_cnt(g); edge_id++) {
		if (dist[iarcs(g, edge_id).second].val > dist[iarcs(g, edge_id).first].val + c[edge_id]) return 0;
	}
	return 1;
}

int just(IGraph *g, IDist *dist, ICost *c, IVertex s, INum *enu, IPEdge *pred) {
	IEdge_Id edge_id;
	IVertex v;
	for(v = 0; v < ivertex_cnt(g); v++) {
		edge_id = pred[v].val;
		if(v != s) {
			if(enu[v].isInf > 0) {
				if(edge_id >= iedge_cnt(g)) return 0;
				if(iarcs(g, edge_id).second != v) return 0;
				if(dist[v].val != dist[iarcs(g, edge_id).first].val + c[edge_id]) return 0;
				if(enu[v].val != enu[iarcs(g, edge_id).first].val + 1) return 0;
			}
		}
	}
	return 1;
}

int no_path(IGraph *g, IDist *dist, INum *enu) {
	IVertex v;
	for(v = 0; v < ivertex_cnt(g); v++) {
		if(dist[v].isInf) {
			if(!enu[v].isInf) return 0;
		}
		else {
			if(enu[v].isInf) return 0;
		}
	}
	return 1;
}

int pos_cost(IGraph *g, ICost *c) {
	IEdge_Id edge_id;
	for(edge_id = 0; edge_id < iedge_cnt(g); edge_id++) {
		if(c[edge_id] < 0) return 0;
	}
	return 1;
}

int check_basic_just_sp(IGraph *g, IDist *dist, ICost *c, IVertex s, INum *enu, IPEdge *pred) {
	if(!is_wellformed(g)) return 0;
	if(dist[s].val > 0) return 0;
	if(!trian(g, dist, c)) return 0;
	if(!just(g, dist, c, s, enu, pred)) return 0;
	return 1;
}

int check_sp(IGraph *g, IDist *dist, ICost *c, IVertex s, INum *enu, IPEdge *pred) {
	if(!check_basic_just_sp(g, dist, c, s, enu, pred)) return 0;
	if(s >= ivertex_cnt(g)) return 0;
	if(dist[s].val != 0) return 0;
	if(!no_path(g, dist, enu)) return 0;
	if(!pos_cost(g, c)) return 0;
	return 1;
}

int main(int argc, char **argv) {
	return 0;
}
