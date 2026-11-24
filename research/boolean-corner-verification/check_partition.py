"""Contract leading terms directly from physical Bernoulli factors and edge lists.

This oracle does not use vertex covers, matchings, special-edge conditioning,
gate truth semantics, path identities, or the compiler's bipartition.
"""
from heapq import heapify, heappop, heappush
from itertools import product
from closure import construct, evaluate, stretch


def contraction(graph, bits, cap=14):
    n=len(graph.costs)
    links=[set() for _ in range(n)]
    edges=graph.edges+graph.special
    for u,v in edges:
        links[u].add(v);links[v].add(u)
    heap=[(len(ns),i) for i,ns in enumerate(links)]
    heapify(heap)
    order=[]
    width=0
    while heap:
        d,u=heappop(heap)
        ns=links[u]
        if ns is None or d!=len(ns):
            continue
        width=max(width,d)
        if width>cap:
            raise ValueError(f"contraction width {width} exceeds cap {cap}")
        order.append(u)
        for v in ns:
            links[v].discard(u)
            links[v].update(ns-{v})
            heappush(heap,(len(links[v]),v))
        links[u]=None
    position={v:i for i,v in enumerate(order)}
    buckets=[[] for _ in order]
    for v,cost in enumerate(graph.costs):
        # Spin 0 is absent: weight t^c. Spin 1 is present: weight 1-t^c.
        assert cost.at(bits)>0
        buckets[position[v]].append(((v,),[(cost.at(bits),1),(0,1)]))
    for u,v in edges:
        buckets[min(position[u],position[v])].append(((u,v),[(0,1),(0,1),(0,1),None]))
    result=(0,1)
    for step,u in enumerate(order):
        factors=buckets[step]
        ns=sorted({v for scope,_ in factors for v in scope if v!=u},key=position.get)
        scope=[u]+ns
        views=[([scope.index(v) for v in old],table) for old,table in factors]
        table=[]
        for state in range(1<<len(ns)):
            best,count=None,0
            for chosen in (state*2,state*2+1):
                exponent,coef=0,1
                for positions,values in views:
                    local=sum(((chosen>>p)&1)<<j for j,p in enumerate(positions))
                    term=values[local]
                    if term is None:
                        break
                    exponent+=term[0];coef*=term[1]
                else:
                    if best is None or exponent<best:
                        best,count=exponent,coef
                    elif exponent==best:
                        count+=coef
            table.append(None if best is None else (best,count))
        if ns:
            buckets[position[ns[0]]].append((ns,table))
        else:
            result=(result[0]+table[0][0],result[1]*table[0][1])
    return result[0],result[1],width


def check():
    total=0
    largest=0
    for n,t,gates in [(1,0,[]),(1,1,[]),(2,0,[(0,1,6)]),(1,1,[(0,1,14)])]:
        base=construct(n,t,gates)
        for g in (base,stretch(base)):
            for bits in product((0,1),repeat=n):
                count=sum(evaluate(bits+w,gates) for w in product((0,1),repeat=t))
                exp,coef,width=contraction(g,bits)
                assert exp==g.base+int(count==0)
                assert (coef if exp==g.base else 0)==count
                total+=1
                largest=max(largest,width)
    print(f"{total} raw physical Bernoulli leading-term contractions passed; largest elimination width {largest}")


if __name__=='__main__':
    check()
