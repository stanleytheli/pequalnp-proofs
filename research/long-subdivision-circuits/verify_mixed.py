"""Independent finite checks of the long-path cover and terminal-forest arithmetic."""
from itertools import combinations, product

def cover_cost(path_length, left, right):
    """Enumerate all internal selections on a single path with endpoints fixed."""
    size = path_length-1
    best = size+1
    for mask in range(1 << size):
        chosen = (bool(left),) + tuple(bool(mask >> i & 1) for i in range(size)) + (bool(right),)
        if all(a or b for a,b in zip(chosen,chosen[1:])):
            best = min(best, mask.bit_count())
    return best

def terminal_bound(edges, lengths):
    """Optimize separately over the two physical outcomes of each path reduction."""
    best = None
    for choices in product(range(2), repeat=len(edges)):
        heads=set()
        tips=paid=0
        for (u,v),length,choice in zip(edges,lengths,choices):
            half=(length-1)//2
            paid += 3*half
            if length%2:
                tips+=1
                heads.add((u,v)[choice])
            elif choice:
                tips+=2
                heads.update((u,v))
            else:
                paid+=3
        cost=paid+tips+len(heads)-1
        best=cost if best is None else min(best,cost)
    return best

def minimum_cover(n,edges,lengths,local):
    best=sum(lengths)
    for mask in range(1<<n):
        k=mask.bit_count()
        for (u,v),length in zip(edges,lengths):
            k+=local[length,mask>>u&1,mask>>v&1]
        best=min(best,k)
    return best

def main():
    local={}
    for length in range(7,14):
        h=(length-1)//2
        for u,v in product(range(2),repeat=2):
            c=cover_cost(length,u,v)
            local[length,u,v]=c
            penalty=(not (u or v)) if length%2 else (not (u and v))
            assert c==h+penalty
    audits=0
    for n in range(2,6):
        possible=list(combinations(range(n),2))
        for mask in range(1,1<<len(possible)):
            edges=[e for i,e in enumerate(possible) if mask>>i&1]
            for scheme in range(3):
                lengths=[7 if scheme==0 else 8 if scheme==1 else 7+(i+mask)%7 for i in range(len(edges))]
                c=minimum_cover(n,edges,lengths,local)
                assert terminal_bound(edges,lengths)==sum(lengths)+c-1
                audits+=1
    print('Independent checks passed for 28 fixed path-boundary instances and',audits,'subdivided graph instances.')
if __name__=='__main__':
    main()
