#include <Graph.h>
#include <math.h>

// Abbreviations

nat ivertex_cnt(IGraph *g) {
	return g->num_vertices;
}

nat iedge_cnt(IGraph *g) {
	return g->num_edges;
}

IEdge iarcs(IGraph *g, IEdge_Id e) {
	return g->arcs[e];
}


// Definitinos

int is_wellinformed_inv(IGraph *g, nat i) {
	for(nat k = 0; k < i; k++) {
		if(ivertex_cnt(g) > iarcs(g, k).first && ivertex_cnt(g) > iarcs(g, k).second) continue;
		return 0;
	}
	return 1;
}

int trian_inv(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), nat m) {
	for(nat i = 0; i < m; i++) {
		if (d(iarcs(g).second) <= d(iarcs(g).first) + (float) c(i)) continue;
		return 0;
	}
	return 1;
}

int just_inv(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*n)(Ivertex), IPEdge (*p)(IVertex), nat k) {
	for(int v = 0; v < k; v++) {
		if(v != s && n(v) >= 0) {
			int flag = 0;
			for(nat e = 0; e < iedge_cnt(g); e++) {
				if(e == (nat) p(v) && e < iedge_cnt(g) && v == iarcs(g, e).second && d(v) == d(iarcs(g, e).first) + (ereal) c(e) && n(v) == n(iarcs(g, e).first) + 1) {
					flag = 1;
					break;
				}
			}
			if(!flag) return 0;
		}
	}
	return 1;
}

int no_path_inv(IGraph *g, IDist (*d)(IVertex), INum (*n)(IVertex), nat k) {
	for(int v = 0; v < k; v++) {
		if(d(v) == INFINITY) {
			if(n(v) >= 0) return 0;
		}
		else 
		{
			if(n(v) < 0) {
			  return 0;
		}
	}
	return 1;
}

int pos_cost_inv(IGraph *g, ICost (*c)(IEdge_Id)) {
	for(int e = 0; e < iedge_cnt(g); e++) {
		if(c(e) >= 0) continue;
		return 0;
	}
	return 1;
}


// procedures

int is_wellformed(IGraph *g) {
	nat i;
	IEdge e;
	int r;
	
	r = 1;
	i = 0;
	
	while(i < iedge_cnt(g)) {
		if((is_wellformed_inv(g, i) && i <= iedge_cnt(g)) == 0) return 0;
		e* = iarcs(G, i);
		if(ivertex_cnt(g) <= e.first || ivertex_cnt(g) <= e.second) return 0;
		i++;
	}
	return is_wellformed_inv(g, iedge_cnt(g));
}

int trian(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id)) {
	IEdge_Id edge_id;
	int r;
	
	r = 1;
	edge_id = 0;
	
	while(edge_id < iedge_cnt(g)) {
		if((trian_inv(g, dist, c, edge_id) && edge_id <= iedge_cnt(g)) == 0) return 0;
		if(dist(iarcs(g, edge_id).second > dist(iarcs(g, edge_id).first + (ereal) c(edge_id)) return 0;
		edge_id++;
	}
	return trian_inv(g, dist, c, iedge_cnt(g));
}

int just(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*enu)(IVertex), IPEdge (*pred)(IVertex)) {
	IVertex v;
	IEdge_Id edge_id;
	int r;
	
	r = 1;
	v = 0;
	
	while(v < ivertex_cnt(g)) {
		if((just_inv(g, dist, c ,s, enu, pred, v) && v <= ivertex_cnt(g)) == 0) return 0;
		edge_id = (IEdge_Id) pred(v);
		if(v != s && enu(v) >= 0 && (edge_id >= iedge_cnt(g)
								  || iarcs(g, edge_id).second != v
								  || dist(v) != dist(iarcs(g, edge_id).first) + (ereal) c(edge_id)
								  || enu(v) != enu(iarcs(g, edge_id).first) + 1 )) return 0;
		v++;
	}
	return just_inv(g, dist, c, s, enu, pred(ivertex_cnt(g));
}

int no_path(IGraph *g, IDist (*dist)(IVertex), INum (*enu)(IVertex)) {
	IVertex v;
	int r;
	
	r = 1;
	v = 0;
	
	while(v < ivertex_cnt(g)) {
		if((no_path_inv(g, dist, enu, v) && v <= ivertex_cnt(g)) == 0) return 0;
		if(
	}
}

int pos_=cost(IGraph *g, ICost (*c)(IEdge_Id)) {
	
}


int check_basic_just_sp(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*enu)(IVertex), IPEdge (*pred)(IVertex)) {
	
}

int check_sp(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id), IVertex s, IPEdge (*pred)(Ivertex)) {
	
}


// implentation functions

IGraph *newGraph(nat num_vertices, nat num_edges, IEdge *arcs) {
	
}

#endif
