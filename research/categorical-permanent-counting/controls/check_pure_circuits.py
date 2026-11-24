"""Exhaust finite local parse semantics of small shared oracle circuits."""
from itertools import permutations, product
from collections import Counter

def perm_slots(rows):
    return tuple(tuple(rows[i][p[i]] for i in range(len(rows))) for p in permutations(range(len(rows))))

def operators(n):
    out = {((a,), (b,)) for a in range(n) for b in range(a,n)}
    out.update({((a,b),) for a in range(n) for b in range(a,n)})
    for a,b,c,d in product(range(n),repeat=4):
        out.add(tuple(sorted((tuple(sorted((a,d))),tuple(sorted((b,c)))))))
    return sorted(out)

def joined(colors):
    answer=0
    for color in colors:answer|=color
    return answer

def check(gates,cnt):
    # Leaves contribute neither color, X, and Y respectively.
    semantics=[{0},{1},{2}]
    for choices in gates:
        semantics.append({joined(outcome) for slots in choices for outcome in product(*(semantics[a] for a in slots))})
    if semantics[-1]!={1,2}:return
    cnt['flexible_pure_roots']+=1
    root=len(semantics)-1
    used={root}
    for g in range(root,2,-1):
        if g in used:
            for slots in gates[g-3]:used.update(slots)
    flex={g for g in used if semantics[g]=={1,2}}
    for g in used:
        assert 3 not in semantics[g]
        assert 1 not in semantics[g] or 2 not in semantics[g] or g in flex
    ref=[min(s) for s in semantics]
    for g in sorted(used):
        if g<3:continue
        for slots in gates[g-3]:
            ff=[a for a in slots if a in flex]
            assert not ff or g in flex
            assert len(ff)<=1
            if g not in flex:continue
            frozen=joined(ref[a] for a in slots)
            new_color=joined(2 if a in flex else ref[a] for a in slots)
            assert frozen in {1,2} and new_color in {1,2}
            correction=int(frozen==1)-sum(ref[a]==1 for a in ff)
            assert correction==int(new_color==1)
            for outcome in product(*(semantics[a] for a in slots)):
                cnt['checked_local_outcomes']+=1
                assert int(joined(outcome)==1)==correction+sum(c==1 for a,c in zip(slots,outcome) if a in flex)
    if any(len(set(slots))!=len(slots) for g in used if g>=3 for slots in gates[g-3]):cnt['repeated_child_slots']+=1

if __name__=='__main__':
    cnt=Counter()
    first=operators(3); second=operators(4)
    for a,b in product(first,second):
        cnt['circuits']+=1;check((a,b),cnt)
    # A 3-by-3 matching fiber whose alternating color classes have unequal parity.
    perms=list(permutations(range(3)))
    sign=lambda p:sum(p[j]<p[i] for i in range(3) for j in range(i+1,3))%2
    even=[p for p in perms if not sign(p)];odd=[p for p in perms if sign(p)]
    A=set(even[:2]+odd[:1]);All=set(perms)
    rows=tuple(tuple(1 if {p for p in perms if p[i]==j}<=A else 2 if {p for p in perms if p[i]==j}<=All-A else 0 for j in range(3)) for i in range(3))
    big=perm_slots(rows)
    for b,c in product(second,operators(5)):
        cnt['circuits']+=1;check((big,b,c),cnt)
    print(dict(sorted(cnt.items())))
