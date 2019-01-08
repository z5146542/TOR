#ifndef GRAPH_H
#define GRAPH_H

// Type Synonyms

typedef unsigned int nat;
typedef int enat; // negative numbers will be treated as infinity for this purpose
typedef float ereal; // the IMFINITY constant in math.h will be used for infinity

typedef nat IVertex;
typedef nat IEdge_Id;
typedef nat ICost;
typedef ereal IDist;
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

nat ivertex_cnt(IGraph *g);
nat iedge_cnt(IGraph *g);
IEdge iarcs(IGraph *g, IEdge_Id e);

// Definitinos

int is_wellinformed_inv(IGraph *g, nat i);
int trian_inv(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), nat m);
int just_inv(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*n)(Ivertex), IPEdge (*p)(IVertex), nat k);
int no_path_inv(IGraph *g, IDist (*d)(IVertex), INum (*n)(IVertex), nat k);
int pos_cost_inv(IGraph *g, ICost (*c)(IEdge_Id), nat m);

// procedures

int is_wellformed(IGraph *g);
int trian(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id));
int just(IGraph *g, IDist (*dist)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*enu)(IVertex), IPEdge (*pred)(IVertex));
int no_path(IGraph *g, IDist (*d)(IVertex), INum (*enu)(IVertex));
int pos_cost(IGraph *g, ICost (*c)(IEdge_Id));

int check_basic_just_sp(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), IVertex s, INum (*enu)(IVertex), IPEdge (*pred)(IVertex));
int check_sp(IGraph *g, IDist (*d)(IVertex), ICost (*c)(IEdge_Id), IVertex s, IPEdge (*pred)(Ivertex));

// implentation functions

IGraph *newGraph(nat num_vertices, nat num_edges, IEdge *arcs);
#endif
