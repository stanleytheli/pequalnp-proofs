"""Choose private tree ports by multi-source BFS as each demand is routed."""
from collections import deque
from random import Random
from time import process_time
import sys
from sextet import sextet
from sextet_routes import contract

def fan(c,depth,adj,used,rng):
    seen={c}; front=[(c,)]
    for _ in range(depth):
        rng.shuffle(front)
        nxt=[]
        for p in front:
            options=list(adj[p[-1]])
            rng.shuffle(options)
            for v in options:
                if v in seen or v in used:
                    continue
                seen.add(v)
                nxt.append(p+(v,))
        front=nxt
    return {p[-1]:p for p in front},seen

def bridge(start,end,adj,used,rng):
    sources=list(start); rng.shuffle(sources)
    prev={a:None for a in sources}
    queue=deque(sources)
    while queue:
        v=queue.popleft()
        if v in end:
            path=[]
            while v is not None:
                path.append(v);v=prev[v]
            return tuple(reversed(path))
        for w in adj[v]:
            if w not in prev and (w not in used or w in end):
                prev[w]=v;queue.append(w)
    return None

def route(m,adj,back,seed,extra=0):
    rng=Random(seed)
    order=list(adj);rng.shuffle(order)
    depth=(m-2).bit_length()+extra
    used=set();centers=[];fw=[];bw=[]
    for c in order:
        if c in used:
            continue
        f,one=fan(c,depth,adj,used,rng)
        if len(f)<m-1:
            continue
        b,two=fan(c,depth,back,used|(one-{c}),rng)
        if len(b)<m-1:
            continue
        centers.append(c);fw.append(f);bw.append(b);used.update(one|two)
        if len(centers)==m:
            break
    if len(centers)!=m:
        return
    # Round-robin scheduling spreads consumption over the source and target
    # port trees, retaining several endpoint choices for most demands.
    shifts=list(range(1,m));rng.shuffle(shifts)
    demands=[]
    for jump in shifts:
        start=list(range(m));rng.shuffle(start)
        demands.extend((i,(i+jump)%m) for i in start)
    paths={};links={}
    for i,j in demands:
        link=bridge(fw[i],bw[j],adj,used,rng)
        if link is None:
            return
        path=fw[i].pop(link[0])+link[1:-1]+bw[j].pop(link[-1])[::-1]
        assert len(path)==len(set(path))
        paths[i,j]=path;links[i,j]=link
        used.update(link)
    return centers,paths,links

def test(p,m,limit,extra=0):
    vertices=sextet(p)
    adj,back,_=contract(vertices)
    for seed in range(limit):
        res=route(m,adj,back,seed,extra)
        if res:
            centers,paths,links=res
            print('found',p,m,'seed',seed,'extra',extra,'active',len(set().union(*map(set,paths.values()))),flush=True)
            return res
    print('unresolved',p,m,'attempts',limit,'extra',extra,flush=True)

if __name__=='__main__':
    p,lo,hi,tries=map(int,sys.argv[1:5])
    extra=int(sys.argv[5]) if len(sys.argv)>5 else 0
    for m in range(lo,hi+1):
        test(p,m,tries,extra)
