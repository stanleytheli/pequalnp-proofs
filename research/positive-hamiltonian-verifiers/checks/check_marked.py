"""Direct tour enumeration vs independent truth-table and old-arc checks."""
from collections import Counter
from itertools import product, combinations
from marked_hamiltonian import Digraph,compile_positive_exact_one,nand_exact_one


def cube(n):
    return product(range(2),repeat=n)


def oracle(n, clauses, labels):
    return Counter(tuple(sorted(v for i,bit in enumerate(bits) for v in labels.get((i,bit),())))
                   for bits in cube(n) if all(sum(bits[i] for i in row)==1 for row in clauses))


def switches():
    cases=0
    for n in (3,4):
        edges=[(a,b) for a in range(n) for b in range(n) if a!=b]
        for ia,ib in combinations(range(len(edges)),2):
            g=Digraph(n)
            for i,(a,b) in enumerate(edges):
                g.arc(a,b,(i,))
            expect=Counter(g.monomial(t) for t in g.tours() if (ia in t)!=(ib in t))
            g.xor(ia,ib)
            assert g.polynomial()==expect
            cases+=1
    return cases


def main():
    rows=[(1,[(0,)]),(2,[(0,1)]),(3,[(0,1,2)]),(3,[(0,1),(1,2)]),
          (3,[(0,1,2),(0,1)]),(3,[(0,),(0,1),(1,)]),
          (4,[(0,1,2),(1,2,3)]),(2,[(0,0,1)]),(2,[()]),(2,[])]
    checked=0
    for n,clauses in rows:
        for labels in ({(i,b):((i,b),) for i in range(n) for b in range(2)},
                       {(i,1):("x",) for i in range(n)},{}):
            g=compile_positive_exact_one(n,clauses,labels)
            assert g.polynomial()==oracle(n,clauses,labels)
            checked+=1
    clauses, wires=nand_exact_one()
    seen=Counter(tuple(bits[i] for i in wires) for bits in cube(15)
                 if all(sum(bits[i] for i in c)==1 for c in clauses))
    assert seen==Counter({(a,b,int(not(a and b))):1 for a,b in cube(2)})
    print(f"{switches()} direct weighted arc-pair replacements on all complete digraphs of orders 3 and 4")
    print(f"{checked} exact formal polynomial comparisons, including empty constraints, repetitions and incompatible pins")
    print("32,768 ternary-CSP assignments checked for the parsimonious NAND truth table")


if __name__=="__main__":
    main()
