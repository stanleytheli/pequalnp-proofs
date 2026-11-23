from itertools import combinations, product
from random import Random
from optimal_circuit import build

def audit(n, paths, bits=False):
    odd = [(u,v) for u,v,k in paths if k%2]
    even = [(u,v) for u,v,k in paths if k%2==0]
    def score(mask):
        if any(not(mask>>u&1 or mask>>v&1) for u,v in odd):
            return 10**9
        return mask.bit_count()+sum(not(mask>>u&1 and mask>>v&1) for u,v in even)
    tau = sum((k-1)//2 for _,_,k in paths)+min(map(score,range(1<<n)))
    result=build(n,paths)
    assert len(result['cover'])==tau
    assert len(result['gates'])==tau+sum(k for _,_,k in paths)-1
    if not bits:
        return
    width=64; vars=[rng.getrandbits(width) for _ in range(result['inputs'])]
    vals=vars.copy(); off=n; truth=0
    for u,v,length in paths:
        path=[u,*range(off,off+length-1),v];off+=length-1
        for a,b in zip(path,path[1:]):truth|=vars[a]&vars[b]
    for op,a,b in result['gates']:vals.append(vals[a]&vals[b] if op=='AND' else vals[a]|vals[b])
    assert vals[result['output']]==truth

rng=Random(66103)
tests=0
for n in (2,3):
    pairs=list(combinations(range(n),2))
    for shape in product(range(9), repeat=len(pairs)):
        paths=[]
        for sh,(u,v) in zip(shape,pairs):
            paths.extend([(u,v,7)]*(sh%3))
            paths.extend([(v,u,8)]*(sh//3))
        if paths:
            audit(n,paths,True);tests+=1
for i in range(2000):
    n=rng.randrange(2,10)
    paths=[(*rng.sample(range(n),2),rng.randrange(7,20)) for _ in range(rng.randrange(1,20))]
    audit(n,paths,True);tests+=1
print(tests, 'multigraph compilers matched minimum covers, exact sizes, and 64 physical truth-table columns each.')
