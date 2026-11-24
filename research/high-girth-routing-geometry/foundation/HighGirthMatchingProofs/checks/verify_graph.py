"""Enumerate perfect matchings from adjacency lists, independently of the gadget bijection."""
from collections import deque
from itertools import permutations
from math import factorial

def build(m,h):
    adjacency={}
    variables={}
    def connect(u,v,variable=None):
        if u==v or v in adjacency.setdefault(u,set()):
            raise ValueError("not a simple graph")
        adjacency[u].add(v)
        adjacency.setdefault(v,set()).add(u)
        if variable is not None:
            variables[frozenset((u,v))]=variable
    for i in range(m):
        for j in range(m-1):
            for column, gap in [(False,'rg'),(True,'cg')]:
                port='c' if column else 'r'
                connect((port,i,j),(gap,i,j))
                connect((gap,i,j),(port,i,j+1))
        for j in range(m):
            path=[('r',i,j)]+[('p',i,j,a) for a in range(2*h)]+[('c',j,i)]
            for a,(u,v) in enumerate(zip(path,path[1:])):
                connect(u,v,(i,j) if a==0 else None)
    return adjacency,variables

def monomials(adjacency,variables):
    hits={}
    def recurse(vertices,factors):
        if not vertices:
            key=tuple(sorted(factors)); hits[key]=hits.get(key,0)+1
            return
        u=min(vertices,key=lambda u:len(adjacency[u]&vertices))
        for v in adjacency[u]&vertices:
            key=variables.get(frozenset((u,v)))
            recurse(vertices-{u,v},factors+([key] if key is not None else []))
    recurse(set(adjacency),[])
    return hits

def girth(adjacency):
    answer=None
    for initial in adjacency:
        distance={initial:0}
        parent={initial:None}
        queue=deque([initial])
        while queue:
            u=queue.popleft()
            for v in adjacency[u]:
                if v not in distance:
                    distance[v]=distance[u]+1
                    parent[v]=u
                    queue.append(v)
                elif parent[u]!=v and parent[v]!=u:
                    d=distance[u]+distance[v]+1
                    answer=d if answer is None else min(d,answer)
    return answer

def main():
    tested=0;total=0
    for m in range(1,6):
        expected={tuple(enumerate(p)):1 for p in permutations(range(m))}
        for h in range(4):
            adj,var=build(m,h)
            assert set(var.values())=={(i,j) for i in range(m) for j in range(m)}
            assert len(adj)==2*m*(2*m-1)+2*h*m*m
            assert max(map(len,adj.values()))<=3
            assert sum(map(len,adj.values()))//2==4*m*(m-1)+(2*h+1)*m*m
            assert girth(adj)==(4*(2*h+3) if m>=2 else None)
            assert monomials(adj,var)==expected
            tested+=1;total+=factorial(m)
    print(f"Verified {tested} graph instances and {total} individual matchings, including girth and exact monomial multiplicities.")

if __name__=="__main__":
    main()
