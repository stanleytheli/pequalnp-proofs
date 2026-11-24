"""Physical positive-corner compilation of binary truth tables and witness bits."""
from dataclasses import dataclass
from typing import Optional
from collections import deque


@dataclass(frozen=True)
class Cost:
    """Integer absence exponent at the two Boolean values of one input."""
    zero: int
    one: int
    index: int = -1

    def at(self,bits):
        return self.one if self.index >= 0 and bits[self.index] else self.zero

    def plus(self,b):
        return Cost(self.zero+b,self.one+b,self.index)

    def from_total(self,b):
        return Cost(b-self.zero,b-self.one,self.index)


def fixed(w):
    return Cost(w,w)


@dataclass
class Graph:
    costs: list
    sides: list
    edges: list
    special: list
    base: int
    stars: Optional[dict] = None

    def add_vertex(self, weight, side):
        self.costs.append(weight)
        self.sides.append(side)
        return len(self.sides)-1


def construct(inputs, guesses, gates):
    """Gate tuples (a,b,truth) refer to input/guess/previous-result indices.
    Bit position 2*i+j of truth is f(i,j). The last signal is the output.
    """
    if inputs+guesses+len(gates)==0:
        raise ValueError("an output signal is required")
    scales=[2 * 16**i for i in reversed(range(len(gates)))]
    large=10*sum(scales)+3
    payouts=[]
    implications=set()
    def signal(off,on):
        payouts.append((off,on))
        return len(payouts)-1
    rails=[]
    special_pairs=[]
    for i in range(inputs):
        pair=[]
        for value in (0,1):
            good=Cost(0,2*large,i) if value==0 else Cost(2*large,0,i)
            pair.append(signal(fixed(large),good))
        rails.append(pair)
    for _ in range(guesses):
        pair=[signal(fixed(large),fixed(0)) for _ in range(2)]
        rails.append(pair)
        special_pairs.append(tuple(pair))
    for (a,b,truth),delta in zip(gates,scales):
        if not (0<=a<len(rails) and 0<=b<len(rails) and 0<=truth<16):
            raise ValueError("invalid circuit gate")
        out=[signal(fixed(0),fixed(delta)) for _ in range(2)]
        for i in (0,1):
            for j in (0,1):
                h=signal(fixed(2*delta),fixed(0))
                value=(truth>>(2*i+j))&1
                for endpoint in (rails[a][i],rails[b][j],out[value]):
                    implications.add((h,endpoint))
        rails.append(out)
    o=rails[-1][0]
    off,on=payouts[o]
    payouts[o]=(off,on.plus(1))
    payload=(inputs+guesses)*large+7*sum(scales)
    H=payload+2
    usages=[0]*len(payouts)
    for a,b in list(implications)+special_pairs:
        usages[a]+=1
        usages[b]+=1
    g=Graph([],[],[],[],0)
    clone=[]
    for (off,on),count in zip(payouts,usages):
        row=[]
        for j in range(max(2,count)):
            l=g.add_vertex(on.plus(H) if j==0 else fixed(H),0)
            r=g.add_vertex(off.plus(H) if j==0 else fixed(H),1)
            row.append((l,r))
            g.edges.append((l,r))
        for j,(_,r) in enumerate(row):
            g.edges.append((row[(j+1)%len(row)][0],r))
        clone.append(iter(row))
    for a,b in sorted(implications):
        _,r=next(clone[a])
        l,_=next(clone[b])
        g.edges.append((l,r))
    for a,b in special_pairs:
        _,r=next(clone[a])
        _,s=next(clone[b])
        g.special.append((r,s))
    g.base=(len(g.costs)//2)*H+payload
    return g


def stretch(g,k=5):
    if k<4:
        raise ValueError("read-two optimum uses paths of length at least eight")
    degree=[0]*len(g.costs)
    for u,v in g.edges+g.special:
        degree[u]+=1;degree[v]+=1
    dominance=1+max(max(c.zero,c.one) for c in g.costs)
    private=dominance+k-1
    correction=[d*dominance for d in degree]
    for u,v in g.special:
        correction[v]+=k
    right=sum(c.zero for c,s in zip(g.costs,g.sides) if s)
    assert all(c.index<0 for c,s in zip(g.costs,g.sides) if s)
    costs=[c if side==0 else c.from_total(extra) for c,side,extra in zip(g.costs,g.sides,correction)]
    out=Graph(costs,[0]*len(costs),[],[],g.base+k*private*len(g.edges)+((k+1)*private+1)*len(g.special)-right)
    out.stars={}
    for edge_list,parity in ((g.edges,0),(g.special,1)):
        for u,v in edge_list:
            path=[u]+[out.add_vertex(fixed(private+int(i%2==0)),i%2) for i in range(1,2*k+parity)]+[v]
            for j,(a,b) in enumerate(zip(path,path[1:])):
                center,other=(b,a) if j==len(path)-2 or j%2 else (a,b)
                out.stars.setdefault(center,[]).append(other)
                if out.sides[a]==out.sides[b]:
                    out.special.append((a,b))
                elif out.sides[a]==0:
                    out.edges.append((a,b))
                else:
                    out.edges.append((b,a))
    return out


def evaluate(bits, gates):
    vals=list(bits)
    for a,b,table in gates:
        vals.append((table>>(2*vals[a]+vals[b]))&1)
    return vals[-1]


def optimum(g,bits,with_count=False):
    """Branch on only one endpoint per exceptional edge; on each branch use flow."""
    from itertools import product
    weights=[w.at(bits) for w in g.costs]
    assert all(v>=0 for v in weights)
    exceptional=list({a for a,b in g.special})
    all_edges=g.edges+g.special
    best,ways=None,0
    for choice in product((False,True),repeat=len(exceptional)):
        take={v for v,b in zip(exceptional,choice) if b}
        omit=set(exceptional)-take
        if any(u in omit and v in omit for u,v in all_edges):
            continue
        take.update(v for u,v in all_edges if u in omit)
        take.update(u for u,v in all_edges if v in omit)
        value=sum(weights[v] for v in take)
        residual=[(u,v) for u,v in g.edges if u not in take and v not in take]
        extra,n=flow_cover(weights,g.sides,residual,with_count)
        value+=extra
        if best is None or value<best:
            best,ways=value,n
        elif value==best:
            ways+=n
    return best,ways


def flow_cover(weights,sides,edges,with_count):
    n=len(weights)
    source,sink=n,n+1
    graph=[[] for _ in range(n+2)]
    def arc(a,b,w):
        x=[b,w,None]
        y=[a,0,x]
        x[2]=y
        graph[a].append(x);graph[b].append(y)
    used={v for e in edges for v in e}
    for v in used:
        if sides[v]:
            arc(v,sink,weights[v])
        else:
            arc(source,v,weights[v])
    inf=1+sum(weights)
    for l,r in edges:
        assert sides[l]==0 and sides[r]==1
        arc(l,r,inf)
    ans=0
    while True:
        levels=[-1]*(n+2)
        levels[source]=0
        todo=deque([source])
        while todo:
            u=todo.popleft()
            for v,w,_ in graph[u]:
                if w and levels[v]<0:
                    levels[v]=levels[u]+1;todo.append(v)
        if levels[sink]<0:
            if not with_count:
                return ans,0
            # Minimum cuts are the successor-closed vertex sets of the residual
            # digraph containing the source and excluding the sink.
            forward={u:{v for v,w,_ in graph[u] if w} for u in used|{source,sink}}
            backward={u:set() for u in forward}
            for u,ns in forward.items():
                for v in ns:
                    backward[v].add(u)
            def closure(start,arcs,allowed):
                seen={start}
                stack=[start]
                while stack:
                    for v in arcs[stack.pop()]:
                        if v in allowed and v not in seen:
                            seen.add(v)
                            stack.append(v)
                return seen
            remaining=used-closure(source,forward,set(forward))-closure(sink,backward,set(forward))
            def count(free):
                if not free:
                    return 1
                u=next(iter(free))
                return (count(free-closure(u,forward,free))+
                        count(free-closure(u,backward,free)))
            return ans,count(remaining)
        it=[0]*(n+2)
        def send(u,limit):
            if u==sink:
                return limit
            while it[u]<len(graph[u]):
                e=graph[u][it[u]]
                v,w,back=e
                if w and levels[v]==levels[u]+1:
                    f=send(v,min(limit,w))
                    if f:
                        e[1]-=f;back[1]+=f
                        return f
                it[u]+=1
            return 0
        while (f:=send(source,inf)):
            ans+=f
