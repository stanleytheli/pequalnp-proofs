"""Construct the full labelled symmetry group and the maximal negative assignments for PG(2,3)."""
from itertools import combinations,permutations
from collections import deque
from functools import lru_cache
POINTS=13
SIDES=((0,1,3,9),(0,2,8,12),(1,7,11,12),(0,6,10,11),(5,9,10,12),(4,8,9,11),(3,7,8,10),(2,6,7,9),(1,5,6,8),(0,4,5,7),(3,4,6,12),(2,3,5,11),(1,2,4,10))
# SIDES[p] lists which of the 13 lines contain point p.
edges=[(i,13+j) for i,js in enumerate(SIDES) for j in js]
neighbors=[0]*26
for i,j in edges:
    neighbors[i]|=1<<j;neighbors[j]|=1<<i
def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x^=b
@lru_cache(None)
def meet(i,j):
    both=neighbors[i]&neighbors[j]
    assert both.bit_count()==1
    return next(bits(both))
def closure(frame):
    known=list(frame);construction=[]
    for a in known:
        for b in known[:known.index(a)]:
            if (a<13)!=(b<13):continue
            c=meet(a,b)
            if c not in known:
                construction.append((known.index(a),known.index(b)));known.append(c)
    return known,construction
def group():
    for f in combinations(range(13),4):
        base,construction=closure(f)
        if len(base)==26:break
    assert len(base)==26
    output=[]
    for side in (range(13),range(13,26)):
        for f in permutations(side,4):
            if any(meet(a,b)==meet(a,c) for a,b,c in combinations(f,3)):continue
            v=list(f)
            for a,b in construction:v.append(meet(v[a],v[b]))
            assert len(set(v))==26
            perm=[0]*26
            for i,w in enumerate(base):perm[w]=v[i]
            assert all(neighbors[perm[i]]>>perm[j]&1 for i,j in edges)
            output.append(tuple(perm))
    assert len(output)==11232
    return output
def negatives():
    ans=set()
    for points in range(1<<13):
        lines=((1<<13)-1)<<13
        for p in bits(points):lines&=~neighbors[p]
        pts=(1<<13)-1
        for l in bits(lines):pts&=~neighbors[l]
        if pts==points:ans.add(pts|lines)
    return sorted(ans)
if __name__=='__main__':
    print('edges',len(edges),'negative extrema',len(negatives()),'incidence symmetries',len(group()))
