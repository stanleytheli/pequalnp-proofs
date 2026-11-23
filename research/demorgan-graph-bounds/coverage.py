"""Verify graph coverage, orbit counts, vertex covers and matching upper circuits."""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations
from math import factorial
from pathlib import Path
import argparse

def vertices(mask):
    while mask:
        v=mask & -mask
        yield v.bit_length()-1
        mask ^= v

def degree(mask):
    return bin(mask).count('1')

def from_mask(n,mask):
    rows=[0]*n
    for k,(i,j) in enumerate(combinations(range(n),2)):
        if mask>>k&1:
            rows[i]|=1<<j
            rows[j]|=1<<i
    assert mask<1<<(n*(n-1)//2)
    return tuple(rows)

@lru_cache(None)
def colors(g):
    values=tuple(map(degree,g))
    history=[]
    while True:
        keys=[(values[i],tuple(sorted(values[j] for j in vertices(g[i])))) for i in range(len(g))]
        types=sorted(set(keys))
        history.append(tuple((kind,keys.count(kind)) for kind in types))
        new=tuple(types.index(k) for k in keys)
        if len(set(new))==len(set(values)):
            return new,tuple(history)
        values=new

def maps(a,b,first_only=False):
    ca,sa=colors(a);cb,sb=colors(b)
    if sa!=sb:return 0
    order=sorted(range(len(a)),key=lambda i:(ca.count(ca[i]),-degree(a[i]),i))
    image=[]
    def dfs(t,used):
        if t==len(order):return 1
        i=order[t];result=0;groups=defaultdict(list)
        for j in range(len(b)):
            if used>>j&1 or ca[i]!=cb[j]:continue
            if any((a[i]>>k&1)!=(b[j]>>h&1) for k,h in zip(order[:t],image)):continue
            # Two eligible twins differ only by a transposition of the target.
            for k in groups:
                if not ((b[k]^b[j]) & ~((1<<k)|(1<<j))):
                    groups[k].append(j);break
            else:groups[j].append(j)
        for j,group in groups.items():
            image.append(j);count=dfs(t+1,used|(1<<j));image.pop()
            if count and first_only:return 1
            result+=len(group)*count
        return result
    return dfs(0,0)

def distances(g,start):
    result={start:0}
    queue=[start]
    for v in queue:
        for w in vertices(g[v]):
            if w not in result:
                result[w]=result[v]+1
                queue.append(w)
    return result

def admissible(g):
    if any(degree(v)>3 for v in g):return False
    for v,row in enumerate(g):
        for w in vertices(row):
            if w<=v:continue
            h=list(g);h[v]^=1<<w;h[w]^=1<<v
            if distances(h,v).get(w,100)<6:return False
    return True

def extensions(g):
    dist=[distances(g,i) for i in range(len(g))]
    eligible=[i for i,row in enumerate(g) if degree(row)<3]
    return sum(all(dist[i].get(j,100)>=5 for i,j in combinations(neighbors,2))
               for k in range(4) for neighbors in combinations(eligible,k))

@lru_cache(None)
def raw(n):
    total=1<<n
    mask=(1<<total)-1
    return tuple((mask//((1<<(1<<v))+1))<<(1<<v) for v in range(n))

def upper(g,expected):
    n=len(g)
    edges=[(i,j) for i,j in combinations(range(n),2) if g[i]>>j&1]
    for size in range(n+1):
        cover=next((set(q) for q in combinations(range(n),size) if all(i in q or j in q for i,j in edges)),None)
        if cover is not None:break
    owned={i:[] for i in cover}
    for i,j in edges:
        if i in cover:owned[i].append(j)
        else:owned[j].append(i)
    assert all(owned.values())
    gates=[]
    def append(op,a,b):
        gates.append((op,a,b))
        return n+len(gates)-1
    roots=[]
    for i,leaves in owned.items():
        root=leaves[0]
        for j in leaves[1:]:root=append('or',root,j)
        roots.append(append('and',root,i))
    out=roots[0]
    for j in roots[1:]:out=append('or',out,j)
    assert len(gates)==expected
    values=list(raw(n))
    for op,a,b in gates:
        assert 0<=a<len(values) and 0<=b<len(values)
        values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
    target=0
    for i,j in edges:target|=values[i]&values[j]
    assert values[out]==target

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('upto',type=int)
    parser.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
    args=parser.parse_args()
    all_old=[((),1)]
    for n in range(1,args.upto+1):
        expected=sum(orbit*extensions(g) for g,orbit in all_old)
        old_with_isolate=[(g+(0,),None) for g,_ in all_old]
        cases=[]
        if n>1:
            for row in (args.directory/f'catalogue-{n}.txt').read_text().splitlines():
                m,target=map(int,row.split());g=from_mask(n,m)
                assert all(g)
                assert admissible(g)
                upper(g,target);cases.append((g,target))
        all_old=[];seen=defaultdict(list);active=0
        for g,target in old_with_isolate+cases:
            _,signature=colors(g)
            assert not any(maps(g,h,True) for h in seen[signature]),'repeated isomorphism type'
            seen[signature].append(g);aut=maps(g,g)
            assert aut>0 and factorial(n)%aut==0
            orbit=factorial(n)//aut
            all_old.append((g,orbit))
            if target is not None:active+=orbit
        assert sum(o for _,o in all_old)==expected,'missing labeled extensions'
        print(n,'essential classes',len(cases),'labeled',active,'all labeled',expected,flush=True)
if __name__=='__main__':main()
