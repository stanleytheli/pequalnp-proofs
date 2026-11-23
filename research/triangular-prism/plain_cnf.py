"""Unrestricted padded binary circuit, allowing a false wire and identical operands."""
import sys
from itertools import combinations, combinations_with_replacement
from pathlib import Path
edge={(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)}
rows=[(1<<a|1<<b, (a,b) in edge) for a,b in combinations(range(6),2)]

class CNF:
    def __init__(self): self.n=0;self.cs=[]
    def v(self): self.n+=1;return self.n
    def add(self,*l): self.cs.append(' '.join(map(str,l))+' 0\n')
    def one(self,x):
        self.add(*x)
        for a,b in combinations(x,2):self.add(-a,-b)
    def dump(self,path):
        path.write_text(f'p cnf {self.n} {len(self.cs)}\n'+''.join(self.cs))


def make(n=8):
    c=CNF(); val=[[c.v() for _ in rows] for _ in range(7+n)]
    for h,(mask,on) in enumerate(rows):
        for i in range(7): c.add(val[i][h] if i<6 and mask>>i&1 else -val[i][h])
        c.add(val[-1][h] if on else -val[-1][h])
    for z in range(7,7+n):
        op=c.v(); pairs=list(combinations_with_replacement(range(z),2));sels=[c.v() for ab in pairs]
        c.one(sels)
        for (a,b),s in zip(pairs,sels):
            for i in range(len(rows)):
                x=val[a][i];y=val[b][i];out=val[z][i]
                c.add(-s,-op,-out,x);c.add(-s,-op,-out,y);c.add(-s,-op,-x,-y,out)
                c.add(-s,op,out,-x);c.add(-s,op,out,-y);c.add(-s,op,x,y,-out)
    return c
if __name__=='__main__':
    if len(sys.argv)!=2: raise SystemExit("usage: plain_cnf.py output.cnf")
    formula=make()
    formula.dump(Path(sys.argv[1]))
    print(formula.n,len(formula.cs))
