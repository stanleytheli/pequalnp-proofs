"""Search exactly the desk's erase-and-append lifts and junk drops on an eight-input circuit."""
from collections import Counter, deque
from pathlib import Path
import json,sys

D=Path(__file__).resolve().parent
edges=((0,1),(1,2),(2,3),(3,4),(0,4),(3,5),(4,6),(0,7))
inputs=tuple(sum(1<<mask for mask in range(256) if mask>>j&1) for j in range(8))
expected=sum(1<<mask for mask in range(256) if any(mask>>a&mask>>b&1 for a,b in edges))

def evaluate(c):
    wires=list(inputs)
    for op,a,b in c:
        assert 0<=a<len(wires) and 0<=b<len(wires) and op in (0,1)
        wires.append((wires[a]&wires[b]) if op else (wires[a]|wires[b]))
    return wires

def nested(c):
    ancestors=[0]*8
    total=0
    for j,(op,a,b) in enumerate(c):
        prior=ancestors[a]|ancestors[b]
        if op:
            total+=bin(prior).count('1')
            prior|=1<<j
        ancestors.append(prior)
    return total

def moves(c, values):
    for j,(op,a,b) in enumerate(c):
        if not op:
            for keep,lift in ((a,b),(b,a)):
                if lift<8 or values[lift]&~values[-1]:continue
                w=8+j
                def redirect(i):return keep if i==w else i-int(i>w)
                out=redirect(8+len(c)-1)
                T=c[:j]+tuple((op1,redirect(u),redirect(v)) for op1,u,v in c[j+1:])+((0,out,lift),)
                if T!=c:yield ('lift',j,keep,lift),T
        else:
            for side,w in enumerate((a,b)):
                if w<8 or c[w-8][0]:continue
                for keep in c[w-8][1:]:
                    T=c[:j]+(((1,keep,b) if side==0 else (1,a,keep)),)+c[j+1:]
                    if T!=c:yield ('junk',j,side,keep),T

def state(c,values):
    return tuple(sorted((op,min(values[a],values[b]),max(values[a],values[b])) for op,a,b in c))

def path(c):
    vals=evaluate(c)
    if vals[-1]!=expected:return 'wrong',[]
    if not nested(c):return 'flat',[]
    stack=deque([(c,vals,[])])
    visited={state(c,vals)}
    while stack:
        net,vals,steps=stack.popleft()
        for step,T in moves(net,vals):
            values=evaluate(T)
            if values[-1]!=expected:continue
            follow=steps+[step]
            if not nested(T):return 'flattened',follow
            key=state(T,values)
            if key not in visited:
                visited.add(key);stack.append((T,values,follow))
    return 'trapped',len(visited)

def main():
    outcomes=Counter();dist=Counter();witnesses=[]
    for idx,line in enumerate((D/'pair-candidates.txt').read_text().splitlines()):
        bits=list(map(int,line.split()))
        assert len(bits)==33
        c=tuple(tuple(bits[j:j+3]) for j in range(0,33,3))
        tag,steps=path(c);outcomes[tag]+=1
        if tag=='flattened':dist[len(steps)]+=1
        if tag=='trapped':
            print('trapped',idx,steps,c,flush=True)
        witnesses.append([tag,steps])
    print('outcomes',dict(outcomes),'shortest paths',dict(sorted(dist.items())),flush=True)
    (D/'certificates.json').write_text(json.dumps(witnesses))
if __name__=='__main__':main()
