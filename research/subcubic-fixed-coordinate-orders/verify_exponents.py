"""Check the maximizing face, maximal encodings, and arbitrary fixed weights."""
from collections import Counter
from itertools import combinations, product
from random import Random
from leading_term import leading_term


def source(r):
    weights=[1]*5
    edges={(i,(i+1)%5) for i in range(5)}
    edges={tuple(sorted(e)) for e in edges}
    newest=4
    bags=[set(range(4))] if r else [set(range(5))]
    for _ in range(r):
        neighbors={v for u,v in edges if u==newest}|{u for u,v in edges if v==newest}
        old=[v for v in range(len(weights)) if v!=newest]
        relabel={v:i for i,v in enumerate(old)}
        bags=[{relabel[v] for v in bag if v!=newest} for bag in bags]
        nextid=len(old)
        fresh=list(range(nextid,nextid+5))
        edges={tuple(sorted((relabel[u],relabel[v]))) for u,v in edges
               if u!=newest and v!=newest}
        edges.update(tuple(sorted((u,fresh[(i+1)%5]))) for i,u in enumerate(fresh))
        edges.update(tuple(sorted((u,relabel[v]))) for u in fresh for v in neighbors)
        weights=[2*weights[v] for v in old]+[1]*5
        # Split one newly inserted module vertex into a path, retaining
        # separate exterior and cycle-neighbor groups on its ends.
        v=fresh[-1]
        exterior=[relabel[u] for u in neighbors]
        assert len(exterior)==2
        internal=[fresh[0],fresh[-2]]
        edges={e for e in edges if v not in e}
        left,middle,right=v,v+1,v+2
        edges.update(tuple(sorted((u,left))) for u in exterior)
        edges.update(tuple(sorted((u,right))) for u in internal)
        edges.add((left,middle));edges.add((middle,right))
        weights.extend([1,1])
        newest=middle
        bags.append(set(exterior+fresh[:-1]+[left,right]))
    if r:
        bags.append({left,middle,right})
    return weights,sorted(edges),bags


def independent(n,edges):
    earlier=[0]*n
    for u,v in edges:
        assert u<v
        earlier[v]|=1<<u
    masks=[0]
    for i in range(n):
        masks += [m|(1<<i) for m in masks if not(m&earlier[i])]
    return masks


def rank(rows,prime=1009):
    pivots={}
    for row in rows:
        v=[e%prime for e in row]
        for i in range(len(v)):
            if not v[i]:
                continue
            if i in pivots:
                m=v[i]
                v=[(a-m*b)%prime for a,b in zip(v,pivots[i])]
            else:
                r=pow(v[i],-1,prime)
                pivots[i]=[a*r%prime for a in v]
                break
    return len(pivots)


def build(weights,edges,h):
    deg=Counter(v for e in edges for v in e)
    H=1+sum(weights)
    bonus_max=H+max(weights)
    B=bonus_max+h+1
    roots=[]
    labels=[]
    pts=[]
    core=[]
    for v,w in enumerate(weights):
        d=deg[v]
        assert d>=2
        P=[];G=[]
        for j in range(d):
            P.append(len(roots));roots.append(H+w*(j==0));labels.append((v,True))
            G.append(len(roots));roots.append(H);labels.append((v,False))
        for j in range(d):
            core.append((P[j],G[j]));core.append((G[j],P[(j+1)%d]))
        pts.append(iter(P))
    for u,v in edges:
        core.append((next(pts[u]),next(pts[v])))
    reward=roots[:]
    paths=[];physical=[]
    for u,v in core:
        reward[u]+=h
        private=[]
        for j in range(1,2*h+1):
            private.append(len(reward));reward.append(B+int(j%2==1))
        path=[u]+private+[v]
        physical.extend(zip(path,path[1:]))
        paths.append(path)
    return labels,paths,reward,physical,H,B


def canonical(mask,labels,paths):
    chosen={i for i,(v,b) in enumerate(labels) if bool(mask>>v&1)==b}
    for route in paths:
        u,v=route[0],route[-1]
        assert not(u in chosen and v in chosen)
        # At 10 take all even private positions; at 00 or 01 take all odd.
        chosen.update(route[(2 if u in chosen else 1):-1:2])
    return chosen


def check_width(labels,paths,bags,graph):
    root_bags=[{i for i,(v,_) in enumerate(labels) if v in bag} for bag in bags]
    assigned=[[] for _ in bags]
    for path in paths:
        j=next(j for j,bag in enumerate(root_bags) if {path[0],path[-1]}<=bag)
        assigned[j].append(path)
    last=set()
    finished=set()
    seen=set()
    width=0
    for roots,routes in zip(root_bags,assigned):
        local=[set()]
        for path in routes:
            private=path[1:-1]
            local.extend(set(private[i:i+2]) for i in range(len(private)))
        for extras in local:
            bag=roots|extras
            assert bag.isdisjoint(finished)
            finished|=last-bag
            last=bag
            width=max(width,len(bag)-1)
            for u in bag:
                seen.update((u,v) for v in graph[u] if u<v and v in bag)
    assert len(seen)==sum(map(len,graph))//2
    assert len(finished|last)==len(graph)
    assert width<=113
    return width


def check():
    rng=Random(1429187)
    total=0
    for r in range(6):
        w,edges,bags=source(r)
        n=len(w)
        assert n==5+6*r and len(edges)==15*r+5 and max(w)==2**r and min(w)==1
        assert max(Counter(v for e in edges for v in e).values())<=7
        masks=independent(n,edges)
        score={u:sum(a for v,a in enumerate(w) if u>>v&1) for u in masks}
        optimum=max(score.values())
        face=[s for s in masks if score[s]==optimum]
        first=face[0]
        assert rank([[(s>>v&1)-(first>>v&1) for v in range(n)] for s in face[1:]])==n-1
        h=3
        labels,paths,weights,physical,H,B=build(w,edges,h)
        count=len(weights)
        assert count==(10*h+4)*len(edges)
        graph=[set() for _ in weights]
        for i,j in physical:
            graph[i].add(j);graph[j].add(i)
        assert max(map(len,graph))<=3
        pathwidth=check_width(labels,paths,bags,graph)
        # A face-exposing facet normal can have either sign.
        other=[rng.randrange(101)-50 for _ in weights]
        empty=canonical(0,labels,paths)
        total0=sum(other[i] for i in empty)
        theta=[sum(other[i] for i in canonical(1<<v,labels,paths))-total0 for v in range(n)]
        check_masks=masks if r<=3 else list(set(rng.sample(masks,min(150,len(masks))))|set(face)|{0})
        for mask in check_masks:
            chosen=canonical(mask,labels,paths)
            assert all(not(i in chosen and j in chosen) for i,j in physical)
            assert all(i in chosen or not graph[i].isdisjoint(chosen) for i in range(count))
            assert sum(other[i] for i in chosen)==total0+sum(theta[v] for v in range(n) if mask>>v&1)
            assert sum(weights[i] for i in chosen)==h*(B+1)*len(paths)+2*len(edges)*H+score[mask]
            total+=1
        if r<=1:
            expo,coef,width=leading_term(weights,physical)
            target=sum(weights)-h*(B+1)*len(paths)-2*len(edges)*H-optimum
            assert (expo,coef)==(target,len(face))
            print(f"raw physical contraction order={expo} coefficient={coef} width={width}")
        print(f"substitutions={r} source={n} source_edges={len(edges)} max_weight={max(w)} "
              f"ray_rank={n-1} face={len(face)} physical={count} path_width<={pathwidth} checked_encodings={len(check_masks)}")
    print(f"{total} independent-set encodings checked for inclusion-maximality and affine scores")


if __name__=='__main__':
    check()
