from itertools import combinations
from pathlib import Path
import sys

root=Path(__file__).parent
n=4
pairs=list(combinations(range(n),2))
allrows=(1<<(1<<n))-1
inputs=tuple(sum(1<<row for row in range(1<<n) if row&(1<<v)) for v in range(n))
targets={}
records=[]
for graph in range(1,1<<len(pairs)):
    edges=[(a,b) for i,(a,b) in enumerate(pairs) if graph>>i&1]
    if len({v for e in edges for v in e})!=n:continue
    independent=[r for r in range(1<<n) if not any((r>>a&1) and (r>>b&1) for a,b in edges)]
    alpha=max(bin(r).count('1') for r in independent)
    truth=allrows^sum(1<<r for r in independent)
    targets[graph]=truth
    records.append((graph,len(edges)+n-alpha-1))
targets_file=root/'controls-targets.txt'
if len(sys.argv)==1:
    targets_file.write_text(''.join(f'{g} {s}\n' for g,s in records))
    raise SystemExit()
lower={int(z[0]):int(z[1]) for r in Path(sys.argv[1]).read_text().splitlines() if (z:=r.split())}
assert set(lower)==set(targets)
truths=set(targets.values());found={}
seen={tuple(sorted(inputs))}
for k in range(1,6):
    nxt=set()
    for available in seen:
        possible={allrows^x for x in available}
        for a,b in combinations(available,2):
            possible.add(a&b);possible.add(a|b)
        for w in possible.difference(available,{0,allrows}):
            if w in truths:found.setdefault(w,k)
            if k<5:nxt.add(tuple(sorted((*available,w))))
    seen=nxt
results={'checked':0,'matched':0,'proper_gap':[]}
for g,nominal in records:
    f=targets[g]
    if f not in found:continue
    exact=found[f];got=lower[g]
    assert got<=exact,(g,got,exact)
    results['checked']+=1;results['matched']+=int(got==exact)
    if exact<nominal:results['proper_gap'].append([g,got,exact,nominal])
assert results['proper_gap']
print(results)
