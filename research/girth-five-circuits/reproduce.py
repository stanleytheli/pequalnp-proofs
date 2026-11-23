"""Validate graph data, build star-cover circuits, and reproduce the two finite searches."""
from pathlib import Path
from itertools import combinations, permutations
from tempfile import TemporaryDirectory
import json, subprocess, sys

D=Path(__file__).resolve().parent
def construct(n, item):
    edges=[tuple(p) for p in item['edges']]
    covers=(s for k in range(1,n+1) for s in combinations(range(n),k))
    cover=next(s for s in covers if all(u in s or v in s for u,v in edges))
    assert len(cover)==item['cover']
    groups={i:[] for i in cover}
    for u,v in edges:
        i,j=(u,v) if u in groups else (v,u)
        groups[i].append(j)
    gates=[]
    def binary(op,a,b):
        gates.append((op,a,b))
        return n+len(gates)-1
    def disjunction(values):
        w,*rest=values
        for v in rest:w=binary('or',w,v)
        return w
    centers=[]
    for i,neighbors in groups.items():
        assert neighbors
        centers.append(binary('and',i,disjunction(neighbors)))
    output=disjunction(centers)
    assert len(gates)==item['target']
    for mask in range(1<<n):
        wires=[bool(mask>>i&1) for i in range(n)]
        for op,a,b in gates:
            wires.append((wires[a] and wires[b]) if op=='and' else (wires[a] or wires[b]))
        assert wires[output]==any(mask>>a&mask>>b&1 for a,b in edges)

def main():
    data=json.loads((D/'graphs.json').read_text())
    flat=[(int(n),case['mask'],case['target']) for n,cases in data.items() for case in cases]
    assert flat==[tuple(map(int,line.split())) for line in (D/'graphs.txt').read_text().splitlines()]
    for n,cases in data.items():
        pairs=list(combinations(range(int(n)),2))
        for case in cases:
            assert case['edges']==[list(e) for k,e in enumerate(pairs) if case['mask']>>k&1]
            construct(int(n),case)
    last=next(c for c in data['8'] if c['mask']==53643800)
    order={p:i for i,p in enumerate(combinations(range(7),2))}
    seven={c['mask']:c['target'] for c in data['7']}
    deletion=[]
    for omit in range(8):
        verts=[i for i in range(8) if i!=omit]
        chosen=[(verts.index(a),verts.index(b)) for a,b in last['edges'] if omit not in (a,b)]
        matches={seven[m] for perm in permutations(range(7))
                 if (m:=sum(1<<order[tuple(sorted((perm[a],perm[b])))] for a,b in chosen)) in seven}
        assert len(matches)==1
        deletion.append(matches.pop())
    assert deletion==[11,11,11,11,9,9,9,9]
    assert len(flat)==113
    print('Checked all 113 minimum-cover circuits on their full truth tables.',flush=True)
    if '--search' not in sys.argv: return
    with TemporaryDirectory() as scratch:
        temp=Path(scratch)
        for src,exe in [('verify_graphs.cpp','verify'),('catalogue.cpp','search'),('last_case.cpp','last')]:
            subprocess.run(['c++','-O3','-std=c++17',str(D/src),'-o',str(temp/exe)],check=True)
        subprocess.run([str(temp/'verify'),str(D/'graphs.txt')],check=True)
        for n in range(2,9):
            cases=data[str(n)]
            path=temp/f'graphs-{n}.txt'
            path.write_text(''.join(f"{c['mask']} {c['target']}\n" for c in cases))
            upper=min(11,max(c['target'] for c in cases)-1)
            if upper<n-1:continue
            result=subprocess.run([str(temp/'search'),str(n),str(n-1),str(upper),str(path)],check=True,capture_output=True,text=True)
            print(result.stdout,flush=True)
            assert all('targets-below 0' in l for l in result.stdout.splitlines() if l.startswith('gates '))
            assert 'short pair model' not in result.stdout
        result=subprocess.run([str(temp/'last'),'53643800','12','0','10000'],check=True,capture_output=True,text=True)
        assert 'MATCH ' not in result.stdout and result.stdout.rstrip().endswith('found 0')
        print(result.stdout,flush=True)
if __name__=='__main__':main()
