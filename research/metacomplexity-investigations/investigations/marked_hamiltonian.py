"""Weighted parsimonious positive exact-one constraints as directed tours.

A directed arc has its own ID, two endpoints and a monomial (a tuple of
variable names). A graph may have parallel arcs while the compilation is in
progress. The output adjacency matrix sums the labels of arcs in each cell.
"""
from collections import Counter


class Digraph:
    def __init__(self, vertices):
        self.vertices = vertices
        self.arcs = {}
        self.next_id = 0

    def arc(self, a, b, label=()):
        key = self.next_id
        self.next_id += 1
        self.arcs[key] = a, b, tuple(label)
        return key

    def xor(self, first, second):
        if first == second:
            raise ValueError("two distinct physical arcs are required")
        a,b,x = self.arcs.pop(first)
        c,d,y = self.arcs.pop(second)
        p,q,r = range(self.vertices, self.vertices+3)
        self.vertices += 3
        for u,v in ((p,q),(q,p),(q,r),(r,q),(r,b),(p,d)):
            self.arc(u,v)
        # Each replacement is used exactly when its old arc was used.
        return self.arc(a,p,x), self.arc(c,r,y)

    def tours(self):
        out = [[] for _ in range(self.vertices)]
        for key,(u,v,_) in self.arcs.items():
            out[u].append((v,key))
        def visit(u, used, edges):
            if len(edges) == self.vertices-1:
                for v,i in out[u]:
                    if v == 0:
                        yield edges+(i,)
                return
            for v,i in out[u]:
                if not (used >> v)&1:
                    yield from visit(v,used | 1<<v,edges+(i,))
        yield from visit(0,1,())

    def monomial(self, tour):
        return tuple(sorted(v for i in tour for v in self.arcs[i][2]))

    def polynomial(self):
        return Counter(self.monomial(t) for t in self.tours())


def compile_positive_exact_one(bits, clauses, labels=None):
    labels = labels or {}
    groups = max(3, bits+len(clauses))
    g = Digraph(groups)
    options=[]
    for i in range(bits):
        options.append([g.arc(i,(i+1)%groups,labels.get((i,b),())) for b in (0,1)])
    clause_options=[]
    for j,clause in enumerate(clauses):
        i=bits+j
        clause_options.append([g.arc(i,(i+1)%groups) for _ in clause])
    for i in range(bits+len(clauses),groups):
        g.arc(i,(i+1)%groups)
    for j,clause in enumerate(clauses):
        for k,bit in enumerate(clause):
            if not 0 <= bit < bits:
                raise ValueError("unbound input bit")
            options[bit][0],clause_options[j][k] = g.xor(options[bit][0],clause_options[j][k])
    return g


def nand_exact_one():
    """Positive ternary clauses with uniquely forced false and true flags.

    The first four variables are the pinned constants a,b,c,d, and variable e
    is true. The wire pairs are a0/a1, b0/b1, z0/z1. The remaining variables
    encode one of the four input pairs; z0 must then equal selector t11.
    """
    a,b,c,d,e=range(5)
    a0,a1,b0,b1,z0,z1=range(5,11)
    t00,t01,t10,t11=range(11,15)
    clauses=[(a,b,c),(a,b,d),(c,d,e),(e,a,c)]
    clauses += [(a0,a1,c),(b0,b1,c),(z0,z1,c)]
    clauses += [(a0,t10,t11),(a1,t00,t01),(b0,t01,t11),(b1,t00,t10),(z1,t11,c)]
    return clauses,(a1,b1,z1)
