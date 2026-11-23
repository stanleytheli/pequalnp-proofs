"""Integral, positive singular-border Hamiltonian construction on odd subdivisions."""
from dataclasses import dataclass
from itertools import combinations,product
from hamiltonian_seed import WeightedGraph,circuit_formula


@dataclass
class Physical:
    graph: WeightedGraph             # labels are (absent exponent, marker or None)
    roots: int
    root_edges: list
    routes: list
    stars: dict
    degree_sum: int
    block_count: int
    leading_exponent: int
    optimum_gates: int


def records(n,clauses,data,opposite_data=None):
    opposite_data = {} if opposite_data is None else opposite_data
    g=WeightedGraph()
    bits={}
    for i in range(1,n+1):
        zero=g.vertex(data.get(i))
        one=g.vertex(opposite_data.get(i))
        bits[i]=(zero,one)
        g.edge(zero,one)
    for clause in clauses:
        scope=sorted({abs(lit) for lit in clause})
        if len(scope)>3 or any(not 1<=j<=n for j in scope):
            raise ValueError("requires clauses of at most three distinct, valid variables")
        candidates=[]
        for values in product((0,1),repeat=len(scope)):
            chosen=dict(zip(scope,values))
            if not any(chosen[abs(lit)]==(lit>0) for lit in clause):
                continue
            v=g.vertex(None)
            candidates.append(v)
            for i,b in chosen.items():
                g.edge(v,bits[i][1-b])
        for a,b in combinations(candidates,2):
            g.edge(a,b)
    return g,n+len(clauses)


def switches(g):
    out=WeightedGraph()
    ports=[]
    all_ports=set()
    for marker,d in zip(g.labels,g.degrees()):
        if not d:
            raise ValueError("isolated record")
        ps=[out.vertex((3 if j==0 else 2,marker if j==0 else None)) for j in range(d)]
        ns=[out.vertex((2,None)) for _ in range(d)]
        for j,p in enumerate(ps):
            out.edge(p,ns[j])
            if d>1:
                out.edge(ns[j],ps[(j+1)%d])
        all_ports.update(ps)
        ports.append(iter(ps))
    for u,v in g.edges:
        out.edge(next(ports[u]),next(ports[v]))
    return out,all_ports


def physical(record,block_count,h=3):
    if h<3:
        raise ValueError("the physical gate optimum uses h >= 3")
    root,ports=switches(record)
    outdegree=[0]*len(root.labels)
    for u,v in root.edges:
        outdegree[u]+=1
    graph=WeightedGraph([(a+h*outdegree[v],tag) for v,(a,tag) in enumerate(root.labels)])
    stars={}
    routes=[]
    private=h+4
    for u,v in root.edges:
        route=[u]+[graph.vertex((private+int(j%2==1),None)) for j in range(1,2*h+1)]+[v]
        routes.append(route)
        for a,b in zip(route,route[1:]):
            graph.edge(a,b)
        reading=route if u in ports else route[::-1]
        assert reading[0] in ports
        for j,(a,b) in enumerate(zip(reading,reading[1:])):
            if b in ports:
                center,other=b,a
            else:
                center,other=(a,b) if j%2==0 else (b,a)
            stars.setdefault(center,[]).append(other)
    D=sum(record.degrees())
    G=len(root.edges)
    W=2*D+len(record.labels)-block_count+h*(private+1)*G
    optimum=(3*h+1)*G+D-1
    assert len(graph.edges)+len(stars)-1==optimum
    occurs=[0]*len(graph.labels)
    for a,others in stars.items():
        occurs[a]+=1
        for b in others:
            occurs[b]+=1
    assert min(occurs)>=1 and max(occurs)<=2 and max(graph.degrees())<=3
    return Physical(graph,len(root.labels),root.edges,routes,stars,D,block_count,W,optimum)


def hamiltonian(n,h=3):
    f,edge_bits,_=circuit_formula(n)
    markers={v:(i,j) for i,row in enumerate(edge_bits) for j,v in enumerate(row)}
    b,k=records(f.variables,f.clauses,markers)
    return physical(b,k,h)
