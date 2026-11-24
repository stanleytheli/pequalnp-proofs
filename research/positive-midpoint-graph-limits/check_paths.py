"""Exact controls for positivity under path and odd-cycle maximum-independent-set constraints."""
from itertools import combinations, product
from random import Random


def extension(length,forced,cycle):
    # Max-plus independent-set DP, with the first vertex recorded for the wrap edge.
    out=-10**9
    for first in [0,1]:
        if 0 in forced and first==0: continue
        states={first:first}
        for j in range(1,length):
            states={bit:max((score+bit for prev,score in states.items() if not (prev and bit)),default=-10**9)
                    for bit in [0,1] if bit or j not in forced}
        out=max(out,max((score for last,score in states.items() if not (cycle and last and first)),default=-10**9))
    return out


def arity_controls():
    rng=Random(37)
    for length in range(3,15):
        sets=[s for s in range(1<<length) if not (s&(s<<1)) and not (s&1 and s>>(length-1))]
        for w in [[1]*length]+[[rng.randrange(4) for _ in range(length)] for _ in range(8)]:
            scores=[sum(w[i] for i in range(length) if s>>i&1) for s in sets]
            best=max(scores)
            mx=[s for s,v in zip(sets,scores) if v==best]
            feas={0}
            for s in mx:
                k=s
                while k:
                    feas.add(k);k=(k-1)&s
            for s in range(1<<length):
                if s in feas: continue
                elems=[j for j in range(length) if s>>j&1]
                if all((s^(1<<j)) in feas for j in elems): assert len(elems)<=2+length%2
    for length in range(9,41,2):
        for n in range(4):
            for S in combinations([0,3,6],n):
                assert (extension(length,set(S),True)==length//2)==(n<3)
    print('weighted cyclic pin obstructions: 108 exact priority-weight cases; three-port odd-cycle gadget at 16 lengths')


def odd_layout(widths,want):
    cursor=0; rows=[]
    for j,width in enumerate(widths):
        cursor+=4
        if cursor%2!=j%2: cursor+=1
        part={}
        for v in range(1<<width):
            if bin(v).count('1')%2==want[j]:
                part[v]=cursor;cursor+=2
        rows.append(part)
    length=cursor+5
    if length%2==0: length+=1
    return length,rows


def path_layout(widths,want):
    # With zero-based indexing, an odd-position pin followed by an even-position one is forbidden.
    cursor=0;rows=[]
    for j,width in enumerate(widths):
        cursor+=4
        if cursor%2!=1-j: cursor+=1
        part={}
        for v in range(1<<width):
            if bin(v).count('1')%2==want[j]:
                part[v]=cursor;cursor+=2
        rows.append(part)
    return cursor+(cursor%2),rows


def parity_controls(blocks):
    total=0
    for n in range(blocks,12):
        widths=[n//blocks+int(i<n%blocks) for i in range(blocks)]
        cycle=blocks==3
        build=odd_layout if cycle else path_layout
        components=[build(widths,want) for want in product(range(2),repeat=blocks) if sum(want)%2==0]
        for x in range(1<<n):
            values=[x>>sum(widths[:j]) & ((1<<w)-1) for j,w in enumerate(widths)]
            ok=True
            for length,rows in components:
                pins={row[v] for row,v in zip(rows,values) if v in row}
                ok=ok and extension(length,pins,cycle)==length//2
            assert ok==(bin(x).count('1')%2==1)
            total+=1
    print(f'{blocks}-block parity graph: {total} full corner assignments matched a direct dynamic program')

if __name__=='__main__':
    arity_controls()
    parity_controls(2);parity_controls(3)
