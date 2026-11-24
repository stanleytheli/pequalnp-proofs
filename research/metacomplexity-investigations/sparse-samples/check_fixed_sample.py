"""Compile switch clauses to a cubic graph; solve its tight independent transversal."""
from collections import Counter, defaultdict
from itertools import combinations, product


def host(clauses):
    """Ints ±j are literals; tuple ('switch',i) denotes one optional position."""
    occ = Counter(abs(lit) for C in clauses for lit in C if isinstance(lit,int))
    clauses = list(clauses)
    for var, d in list(occ.items()):
        if d < 2:
            clauses.append((var,-var,var))
            occ[var] += 3
    assert all(len(C)==3 for C in clauses)
    total, edges, blocks, switches = 0, set(), [], {}
    def edge(u,v):
        assert u != v
        pair = tuple(sorted((u,v)))
        assert pair not in edges
        edges.add(pair)
    cy = {}
    for var, degree in sorted(occ.items()):
        ring = list(range(total, total+2*degree))
        total += len(ring)
        for i,v in enumerate(ring):
            edge(v,ring[(i+1)%len(ring)])
        cy[var] = ring
        blocks.extend([(ring[i],ring[i+1]) for i in range(0,len(ring),2)])
    seen = Counter()
    for C in clauses:
        tri = tuple(range(total,total+3))
        total += 3
        for u,v in combinations(tri,2):
            edge(u,v)
        blocks.append(tri)
        for node, lit in zip(tri,C):
            if isinstance(lit,int):
                var = abs(lit)
                edge(node, cy[var][2*seen[var]+int(lit>0)])
                seen[var] += 1
            else:
                _, key = lit
                assert key not in switches
                switches[key] = node
    rest = set(range(total))-set(switches.values())
    deg = Counter(v for e in edges for v in e)
    dummies = []
    for v in range(total):
        if deg[v] == 2:
            edge(v,total)
            dummies.append(total)
            total += 1
        else:
            assert deg[v] == 3
    assert len(dummies) >= 3
    for i,v in enumerate(dummies):
        edge(v,dummies[(i+1)%len(dummies)])
    assert set(Counter(v for e in edges for v in e).values()) == {3}
    return total, sorted(edges), blocks, rest, switches


def solver(g):
    """Independent transversal search; uses the graph and block partition only."""
    total, edges, blocks, fixed, switches = g
    adj = [0]*total
    for u,v in edges:
        adj[u] |= 1<<v
        adj[v] |= 1<<u
    groups = [sum(1<<v for v in b) for b in blocks]
    fixed_mask = sum(1<<v for v in fixed)
    def solve(enabled):
        avail = fixed_mask | sum(1<<switches[i] for i in enabled)
        def dfs(choices):
            if not choices:
                return True
            j = min(range(len(choices)),key=lambda t:bin(choices[t]).count("1"))
            options = choices[j]
            others = choices[:j]+choices[j+1:]
            while options:
                low = options & -options
                v = low.bit_length()-1
                new = [m & ~adj[v] for m in others]
                if all(new) and dfs(new):
                    return True
                options ^= low
            return False
        return dfs([g & avail for g in groups])
    return solve


def universal(n):
    clauses = []
    for quad in combinations(range(1,n+1),3):
        for signs in product((-1,1),repeat=3):
            clauses.append(tuple(x*s for x,s in zip(quad,signs)))
    constr = []
    for i,(a,b,c) in enumerate(clauses):
        z = n+1+i
        constr.extend([(a,b,z),(-z,c,("switch",i))])
    return clauses,host(constr)


def sat(clauses,n):
    return any(all(any((val[abs(x)-1]) == (x>0) for x in C) for C in clauses)
               for val in product((False,True),repeat=n))


def clique_template(n,k):
    """Use a fixed CNF counter whose gate variables have unique evaluations."""
    free = n
    constraints = []
    def fresh():
        nonlocal free
        free += 1
        return free
    def clause(*lits):
        ls = list(lits)
        while len(ls)<3:
            ls.append(ls[-1])
        constraints.append(tuple(ls))
    t, f = fresh(),fresh()
    clause(t)
    clause(-f)
    prev = [t]+[f]*k
    for v in range(1,n+1):
        nxt = [t]
        for j in range(1,k+1):
            a, b = fresh(),fresh()
            # a <-> v AND prev[j-1]
            clause(-a,v)
            clause(-a,prev[j-1])
            clause(a,-v,-prev[j-1])
            # b <-> prev[j] OR a
            clause(b,-prev[j])
            clause(b,-a)
            clause(-b,prev[j],a)
            nxt.append(b)
        prev = nxt
    clause(prev[k])
    for u,v in combinations(range(1,n+1),2):
        constraints.append((-u,-v,("switch",(u,v))))
    return host(constraints)


if __name__ == "__main__":
    clauses, g = universal(3)
    N, edges, blocks, fixed, switches = g
    M = len(clauses)
    assert (N,len(edges),len(blocks)) == (22*M,33*M,7*M)
    assert 4*len(edges)+N-1-len(blocks) == 147*M-1
    check = solver(g)
    yes = 0
    for code in range(1<<M):
        enabled = {j for j in range(M) if code>>j&1}
        correct = sat([C for j,C in enumerate(clauses) if j not in enabled],3)
        assert check(enabled) == correct
        yes += correct
    print(f"3-variable universal sample: {M} switches, {N} old vertices, {6*len(edges)} sparse examples, all {1<<M} masks agree with truth-table SAT ({yes} yes)")
    # One fixed graph represents the monotone predicate (a AND b) OR c.
    logic = [(1,3,3),(2,3,3)]
    logic += [(-i,-i,("switch",i)) for i in (1,2,3)]
    check = solver(host(logic))
    for a,b,c in product((0,1),repeat=3):
        assert check({i for i,x in enumerate((a,b,c),1) if x}) == ((a and b) or c)
    print("All eight monotone-verifier-model switch inputs agree")
    # Small tests of the actual cardinality-counter clique template.
    for n,k in [(3,2),(3,3)]:
        data = clique_template(n,k)
        check = solver(data)
        ed = list(combinations(range(1,n+1),2))
        for code in range(1<<len(ed)):
            present = {e for i,e in enumerate(ed) if code>>i&1}
            correct = any(all(e in present for e in combinations(group,2)) for group in combinations(range(1,n+1),k))
            assert check(present) == correct
        print(f"CLIQUE({n},{k}): all {1<<len(ed)} inputs agree; {len(data[2])} independent-set blocks checked graphically")
