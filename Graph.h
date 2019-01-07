#ifndef GRAPH_H
#define GRAPH_H

typedef unsigned int nat;
typedef nat IVertex;
typedef nat IEdge_Id;

typedef struct IEdge {
    IVertex first;
    IVertex second;
} IEdge;

typedef struct IGraph {
	nat num_vertices;
	nat num_edges;
	IEdge *arcs;
} IGraph;

nat ivertex_cnt(IGraph g);
nat iedge_cnt(IGraph g);
IEdge iarcs(IGraph g, IEdge_Id e);



#endif
