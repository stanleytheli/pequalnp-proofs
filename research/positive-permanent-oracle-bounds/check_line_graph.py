"""Construct the sparse physical graphs and audit the permanent coefficient, using no dependencies."""
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial, prod


def construction(m, length=3):
    base = []
    ports = {}
    order = 0
    for side in range(2):
        for owner in range(m):
            block = list(range(order, order+2*m-1))
            order += len(block)
            base.extend((a,b,None) for a,b in zip(block,block[1:]))
            for j in range(m):
                ports[side,owner,j] = block[2*j]
    base.extend((ports[0,i,j],ports[1,j,i],(i,j)) for i in range(m) for j in range(m))
    edges = []
    for u,v,cell in base:
        middle = list(range(order,order+length-1))
        order += len(middle)
        path = [u]+middle+[v]
        for p,(a,b) in enumerate(zip(path,path[1:])):
            edges.append((a,b,cell if p==1 else None))
    return order,edges


def incident(order, edges):
    lists = [[] for _ in range(order)]
    for e,(a,b,_) in enumerate(edges):
        lists[a].append((b,e))
        lists[b].append((a,e))
    return lists


def verify_perfect(m):
    order, edges = construction(m)
    nbrs = incident(order,edges)
    assert all(len(nb)<=3 for nb in nbrs)
    assert all(len(nbrs[u])+len(nbrs[v])-2<=3 for u,v,_ in edges)
    used_labels = {e:1<<(i*m+j) for e,(_,_,cell) in enumerate(edges) if cell for i,j in [cell]}
    full = sum(used_labels.values())
    actual = []
    def search(rest, selected):
        if not rest:
            actual.append(full ^ selected)
            return
        best = None
        its = rest
        while its:
            low = its&-its
            its ^= low
            u = low.bit_length()-1
            nb = [(v,e) for v,e in nbrs[u] if rest>>v & 1]
            if not nb:
                return
            if best is None or len(nb)<len(best[1]):
                best = u,nb
                if len(nb)==1:
                    break
        u,nb = best
        for v,e in nb:
            search(rest ^ (1<<u) ^ (1<<v),selected | used_labels.get(e,0))
    search((1<<order)-1,0)
    expected = {sum(1<<(i*m+j) for i,j in enumerate(p)) for p in permutations(range(m))}
    assert len(actual)==len(expected)==factorial(m) and set(actual)==expected
    return order,len(edges),len(actual)


def bernoulli_coefficient(m, matrix, length=3):
    order,edges = construction(m,length)
    n = len(edges)
    inc = incident(order,edges)
    neighbors = [sum(1<<k for k in ({k for _,k in inc[u]+inc[v]}-{e}))
                 for e,(u,v,cell) in enumerate(edges)]
    d = [Fraction(1) if cell is None else matrix[cell[0]][cell[1]] for _,_,cell in edges]
    def add_term(target, poly, shift, scale):
        for i,val in enumerate(poly):
            target[i+shift] += val*scale
    @lru_cache(None)
    def law(mask):
        if not mask:
            return (Fraction(1),)
        low = mask&-mask
        v = low.bit_length()-1
        others = mask ^ low
        forbidden = others & neighbors[v]
        # v absent, or v present with every neighbor absent. This is the physical graph law.
        a,b = law(others),law(others ^ forbidden)
        inds = [i for i in range(n) if forbidden>>i&1]
        coef = prod(d[i] for i in inds)
        out = [Fraction(0)]*(bin(mask).count('1')+1)
        add_term(out,a,1,d[v])
        add_term(out,b,len(inds),coef)
        add_term(out,b,len(inds)+1,-coef*d[v])
        return tuple(out)
    p = law((1<<n)-1)
    h = n-order//2
    target = sum(prod(matrix[i][j] for i,j in enumerate(s)) for s in permutations(range(m)))
    assert all(z==0 for z in p[:h]) and p[h]==target
    return n,h,target


if __name__=='__main__':
    for m in range(1,6):
        print('order, B vertices, physical H vertices, matching monomials',m,*verify_perfect(m),flush=True)
    for length in (3,5,7):
        for x in (((0,1),(1,0)),((Fraction(1,2),Fraction(2,3)),(Fraction(1,4),Fraction(3,4))),((0,0),(1,1))):
            print('raw Bernoulli N, pole, coefficient',*bernoulli_coefficient(2,x,length),flush=True)
