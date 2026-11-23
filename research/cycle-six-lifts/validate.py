"""Independently check the exact lift formula on every emitted circuit, with full truth tables."""
from pathlib import Path
from collections import Counter
import json,sys
D=Path(__file__).resolve().parent
E=((0,1),(1,2),(2,3),(3,4),(4,5),(0,5),(0,6),(1,7))
truth=sum(1<<x for x in range(256) if any(x>>a&x>>b&1 for a,b in E))
inputs=[sum(1<<x for x in range(256) if x>>i&1) for i in range(8)]
def simulate(circuit):
    v=inputs.copy()
    for op,a,b in circuit:
        assert op in (0,1) and 0<=a<len(v) and 0<=b<len(v)
        v.append(v[a]&v[b] if op else v[a]|v[b])
    return v
def and_pairs(circuit):
    ands={i for i,(op,a,b) in enumerate(circuit) if op}
    result=set()
    for start in ands:
        todo=[start];visited=set()
        while todo:
            gate=todo.pop()
            for wire in circuit[gate][1:]:
                parent=wire-8
                if parent>=0 and parent not in visited:
                    visited.add(parent);todo.append(parent)
                    if parent in ands:result.add((start,parent))
    return result
def verify(circuit):
    v=simulate(circuit)
    assert len(circuit)==11
    assert all((v[-1]>>(1<<a|1<<b)&1)==(truth>>(1<<a|1<<b)&1) for a in range(8) for b in range(a+1,8))
    if v[-1]!=truth:return 'pair-only',None
    old=len(and_pairs(circuit))
    if not old:return 'flat',None
    for j,(op,a,b) in enumerate(circuit[:-1]):
        if op:continue
        for keep,lift in ((a,b),(b,a)):
            if v[lift]&~truth:continue
            reduced=list(circuit);reduced[j]=(0,keep,keep);reduced.append((0,18,lift))
            if simulate(reduced)[-1]!=truth:continue
            new=len(and_pairs(reduced))
            if new<old:return 'reducible',(j,keep,lift,old,new)
    return 'resistant',None
def main():
    count=Counter();n=0;hist=Counter()
    for line in (D/'pair-candidates.txt').read_text().splitlines():
        bits=list(map(int,line.split()));assert len(bits)==33
        c=[tuple(bits[i:i+3]) for i in range(0,33,3)]
        kind,check=verify(c);count[kind]+=1;n+=1
        if check:hist[check[-2:]]+=1
    print(n,dict(count),dict(hist))
    if '--complete' in sys.argv:
        assert n==1174 and count=={'pair-only':76,'flat':702,'reducible':396}
if __name__=='__main__':main()
