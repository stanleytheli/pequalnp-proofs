"""Make a protected balanced subcubic graph regular while preserving a girth bound."""
from collections import deque
from dataclasses import dataclass
from typing import List, Set, Tuple
from verify_graph import build, girth

@dataclass
class Completion:
    neighbors: List[Set[int]]
    protected: Set[Tuple[int,int]]
    added: Set[Tuple[int,int]]
    copies: int
    switches: int
    base_order: int
    base_edges: list
    side: List[int]

def within(graph, starts, radius):
    seen=set(starts)
    boundary=set(starts)
    for _ in range(radius):
        nxt=set()
        for u in boundary:
            nxt.update(graph[u])
        boundary=nxt-seen
        seen.update(boundary)
        if not boundary:
            break
    return seen

def bipartition(graph):
    side={}
    for start in sorted(graph):
        if start in side:
            continue
        side[start]=0
        queue=deque([start])
        while queue:
            u=queue.popleft()
            for v in sorted(graph[u]):
                if v in side:
                    assert side[u]!=side[v]
                else:
                    side[v]=1-side[u]
                    queue.append(v)
    return side

def complete(m,h,g):
    base,_=build(m,h)
    if m<2 or g<3 or g>4*(2*h+3):
        raise ValueError("invalid base graph or target girth")
    side0=bipartition(base)
    ordered=sorted(base)
    index={v:i for i,v in enumerate(ordered)}
    n=len(ordered)//2
    assert len(ordered)==2*n and sum(side0.values())==n
    deficit=sum(3-len(base[v]) for v in base if side0[v]==0)
    copies=(16*(1<<g)+deficit-1)//deficit
    edges0=sorted((index[u],index[v]) for u in base if side0[u]==0 for v in base[u])
    graph=[set() for _ in range(2*n*copies)]
    protected=set()
    sides=[side0[v] for _ in range(copies) for v in ordered]
    def add(u,v):
        assert sides[u]==0 and sides[v]==1 and v not in graph[u]
        graph[u].add(v);graph[v].add(u)
    for i in range(copies):
        for a,b in edges0:
            u,v=2*n*i+a,2*n*i+b
            add(u,v);protected.add((u,v))
    left={v for v,x in enumerate(sides) if x==0 and len(graph[v])<3}
    right={v for v,x in enumerate(sides) if x==1 and len(graph[v])<3}
    filler=set()
    switches=0
    while left:
        u=min(left)
        close=within(graph,[u],g-2)
        far=right-close
        if far:
            v=min(far)
            add(u,v);filler.add((u,v))
        else:
            v=min(right)
            forbidden=within(graph,[u,v],g-1)
            x,y=min((x,y) for x,y in filler if x not in forbidden and y not in forbidden)
            graph[x].remove(y);graph[y].remove(x);filler.remove((x,y))
            add(u,y);filler.add((u,y))
            add(x,v);filler.add((x,v))
            switches+=1
        if len(graph[u])==3:
            left.remove(u)
        if len(graph[v])==3:
            right.remove(v)
    assert not right
    return Completion(graph,protected,filler,copies,switches,2*n,edges0,sides)

def check(c,g):
    total=len(c.neighbors)
    assert c.protected.isdisjoint(c.added)
    assert all(len(n)==3 for n in c.neighbors)
    for u,ns in enumerate(c.neighbors):
        for v in ns:
            assert u in c.neighbors[v] and c.side[v]!=c.side[u]
    actual={(u,v) for u in range(total) if c.side[u]==0 for v in c.neighbors[u]}
    assert actual==c.protected|c.added
    base=set(c.base_edges)
    for i in range(c.copies):
        off=c.base_order*i
        obs={(u-off,v-off) for u,v in c.protected if off<=u<off+c.base_order}
        assert obs==base
    vertex_map=dict(enumerate(c.neighbors))
    measured=girth(vertex_map)
    assert measured is not None and measured>=g
    return total,measured

def main():
    switches=0
    for m,h,g in [(2,0,4),(2,0,5),(2,1,6),(3,1,5),(3,0,6),(4,0,7)]:
        result=complete(m,h,g)
        n,gg=check(result,g)
        switches+=result.switches
        print(f"m={m} h={h} minimum-girth={g} N={n} observed={gg} copies={result.copies} switches={result.switches}")
    assert switches>0

if __name__=="__main__":
    main()
