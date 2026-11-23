"""Enumerate short one-output formulas up to Heawood symmetry, then test reuse bounds."""
from collections import Counter
from functools import lru_cache
from pathlib import Path
from itertools import permutations
import sys
from sharing import EDGES,COLUMNS,W,raw,combine,capacities,three_rectangles

FULL=(1<<14)-1

def bitset(mask):
    while mask:
        bit=mask&-mask
        yield bit.bit_length()-1
        mask-=bit

def group():
    neighbors=[sum(1<<(a if v==b else b) for a,b in EDGES if v in (a,b))for v in range(14)]
    lines=[tuple(bitset(neighbors[i])) for i in range(7,14)]
    for side in (0,1):
        other=neighbors[:7] if side else neighbors[7:]
        for p in permutations(range(7)):
            points=[a+7*side for a in p]
            masks=[sum(1<<points[i] for i in line) for line in lines]
            if not all(s in other for s in masks):continue
            perm=points+[other.index(s)+7*(1-side) for s in masks]
            edges=[EDGES.index(tuple(sorted((perm[a],perm[b])))) for a,b in EDGES]
            yield edges,perm

def tables(perm):
    tbl=[]
    for pos in range(0,len(perm),7):
        bits=[1<<x for x in perm[pos:pos+7]]
        row=[0]*(1<<len(bits))
        for n in range(1,len(row)):
            bit=n&-n
            row[n]=row[n^bit]|bits[bit.bit_length()-1]
        tbl.append(row)
    return tbl

def transformations():
    return [(tables(ep),tables(np)) for ep,np in group()]

def orbit(sig,group):
    p,q=sig
    a,b,c=p&127,(p>>7)&127,p>>14
    d,e=q&127,q>>7
    return {(ei[0][a]|ei[1][b]|ei[2][c],ni[0][d]|ni[1][e]) for ei,ni in group}

def uppermass(p,q):
    return sum(max(0,W[i][j]) for i in bitset(p) for j in bitset(q))

def main(kmax):
    perms=transformations()
    reps=[{min(orbit(raw(0),perms))}]
    wires=[{raw(v) for v in range(14)}]
    upto=set(reps[0])
    for k in range(1,kmax+1):
        found=set()
        for i in range((k-1)//2+1):
            j=k-1-i
            if len(wires)<=i:
                wires.append(set().union(*(orbit(z,perms) for z in reps[i])))
            for a in reps[j]:
                for b in wires[i]:
                    for op in ('or','and'):
                        cand=combine(a,b,op)
                        if cand[0] and cand[1]:found.add(cand)
        canon=set()
        unseen=found
        count=0
        while unseen:
            s=next(iter(unseen));o=orbit(s,perms)
            c=min(o)
            if c not in upto:
                canon.add(c);count+=len(o)
            unseen.difference_update(o)
        upto.update(canon);reps.append(canon)
        high=[z for z in canon if uppermass(*z)>6*(2+k)]
        print('cost',k,'orbits',len(canon),'concrete',count,'needs capacity check',len(high),flush=True)
        issues=[]
        for sig in high:
            m1,m2,inf=capacities(*sig)
            failure=[]
            for r in range(2,inf//6+1):
                cap=min(inf,(r//2)*m2+(r%2)*m1)
                if cap>6*(r+k) and r==3 and min(sig[0].bit_count(),sig[1].bit_count())<=7:
                    cap=min(cap,three_rectangles(*sig))
                if cap>6*(r+k):failure.append(r)
            if failure:issues.append((sig,m1,m2,inf,failure))
        print('unresolved',len(issues),issues[:10],flush=True)
        (Path(__file__).parent/f'cones-{k}.txt').write_text('\n'.join(map(repr,issues))+'\n')
if __name__=='__main__':main(int(sys.argv[1]))
