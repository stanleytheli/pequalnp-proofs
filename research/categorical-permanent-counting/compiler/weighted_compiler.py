"""Weighted tight-cut messages and monotone elimination of Laurent monomials."""
from fractions import Fraction
from itertools import permutations
from matching_lift import Board, Lift, solve


class Circuit:
    def __init__(self, dimension):
        self.dimension = dimension
        self.nodes = []
        self.zero = self.scalar(0)
        self.one = self.scalar(1)

    def node(self, operation, payload):
        self.nodes.append((operation,payload))
        return len(self.nodes)-1

    def scalar(self, value):
        if value<0:
            raise ValueError("Only nonnegative coefficients are allowed")
        return self.node("scalar",Fraction(value))

    def monomial(self, exponents):
        exponents = tuple(exponents)
        if len(exponents)!=self.dimension or not all(isinstance(x,int) for x in exponents):
            raise ValueError("One integral exponent per coordinate is required")
        return self.node("monomial",exponents) if any(exponents) else self.one

    def plus(self, children):
        terms = tuple(t for t in children if t!=self.zero)
        return self.node("plus",terms) if len(terms)>1 else next(iter(terms),self.zero)

    def times(self, children):
        terms = tuple(t for t in children if t!=self.one)
        if self.zero in terms:
            return self.zero
        return self.node("times",terms) if len(terms)>1 else next(iter(terms),self.one)

    def perm(self, matrix):
        matrix = tuple(tuple(row) for row in matrix)
        if not matrix:
            return self.one
        if len(matrix)==1:
            return matrix[0][0]
        return self.node("perm", matrix)

    def positive_power(self, var_nodes, exponents):
        factors = []
        for base, power in zip(var_nodes,exponents):
            if power<0:
                raise ValueError("A negative reduced exponent survived")
            while power:
                if power&1:
                    factors.append(base)
                power //= 2
                if power:
                    base = self.times((base,base))
        return self.times(factors)

    def explicit_size(self):
        return sum(1+(len(data)**2 if op=="perm" else len(data) if op in ("plus","times") else 0)
                   for op,data in self.nodes)

    def evaluate(self, root, values):
        from math import prod
        values = tuple(Fraction(x) for x in values)
        result = []
        for op, data in self.nodes[:root+1]:
            if op=="scalar":
                v = data
            elif op=="monomial":
                v = prod(x**d for x,d in zip(values,data))
            elif op=="plus":
                v = sum(result[j] for j in data)
            elif op=="times":
                v = prod(result[j] for j in data)
            else:
                v = sum(prod(result[row[p[i]]] for i,row in enumerate(data))
                        for p in permutations(range(len(data))))
            result.append(v)
        return result[root]


def integer_assignment_dual(cost):
    """Minimum-cost matching plus integral attaining row and column potentials."""
    n = len(cost)
    if not n:
        return 0,[],[]
    bound = max([abs(x) for row in cost for x in row if x is not None]+[0])
    forbidden = 2*n*bound+1
    matrix = [[forbidden if x is None else x for x in row] for row in cost]
    u,v,matched = [0]*(n+1),[0]*(n+1),[0]*(n+1)
    for row in range(1,n+1):
        matched[0] = row
        visited,slack,parent = set(),[None]*(n+1),[None]*(n+1)
        j = 0
        while matched[j]:
            visited.add(j)
            i = matched[j]
            for k in range(1,n+1):
                if k in visited:
                    continue
                gap = matrix[i-1][k-1]-u[i]-v[k]
                if slack[k] is None or gap<slack[k]:
                    slack[k],parent[k] = gap,j
            next_col = min((k for k in range(1,n+1) if k not in visited),key=slack.__getitem__)
            delta = slack[next_col]
            for k in visited:
                u[matched[k]] += delta
                v[k] -= delta
            for k in range(1,n+1):
                if k not in visited:
                    slack[k] -= delta
            j = next_col
        while j:
            prev = parent[j]
            matched[j] = matched[prev]
            j = prev
    if any(cost[matched[j]-1][j-1] is None for j in range(1,n+1)):
        return None
    objective = sum(u[1:])+sum(v[1:])
    assert objective==sum(matrix[matched[j]-1][j-1] for j in range(1,n+1))
    assert all(u[i+1]+v[j+1]<=x for i,row in enumerate(cost) for j,x in enumerate(row) if x is not None)
    return objective,u[1:],v[1:]


def normalize(source, root):
    """Compile into variable, nonnegative-scalar and ordinary gate nodes."""
    dim = source.dimension
    out = Circuit(dim)
    basis = [out.monomial(tuple(int(i==j) for j in range(dim))) for i in range(dim)]
    def shift(vec):
        return out.positive_power(basis,vec)
    minima, normalized = [],[]
    z = (0,)*dim
    for op, data in source.nodes[:root+1]:
        if op=="scalar":
            mu, target = (z if data else None), (out.scalar(data) if data else out.zero)
        elif op=="monomial":
            mu, target = data,out.one
        elif op=="times":
            if any(minima[g] is None for g in data):
                mu, target = None, out.zero
            else:
                mu = tuple(sum(minima[g][i] for g in data) for i in range(dim))
                target = out.times(normalized[g] for g in data)
        elif op=="plus":
            available = [g for g in data if minima[g] is not None]
            if available:
                mu = tuple(min(minima[g][i] for g in available) for i in range(dim))
                target = out.plus(out.times((normalized[g],shift(tuple(x-y for x,y in zip(minima[g],mu)))))
                                  for g in available)
            else:
                mu, target = None, out.zero
        else:
            n = len(data)
            cells = [(i,j) for i,row in enumerate(data) for j,g in enumerate(row) if minima[g] is not None]
            if solve(Board.square(n,cells))[0] is None:
                mu, target = None,out.zero
            else:
                duals = [integer_assignment_dual([[minima[g][d] if minima[g] is not None else None
                                                    for g in row] for row in data]) for d in range(dim)]
                mu = tuple(r[0] for r in duals)
                def slot(i,j,g):
                    if minima[g] is None: return out.zero
                    reduced = tuple(minima[g][d]-u[i]-v[j] for d,(_,u,v) in enumerate(duals))
                    return out.times((normalized[g],shift(reduced)))
                target = out.perm([[slot(i,j,g) for j,g in enumerate(row)] for i,row in enumerate(data)])
        minima.append(mu)
        normalized.append(target)
    if minima[root] is None:
        return out,out.zero
    return out,out.times((normalized[root],shift(minima[root])))


def compile_weighted(lift, forms, circuit, weight):
    """Emit one monomial per readout, keeping the coefficient from each source edge.

    The weight dict contains arithmetic gate IDs. Each chosen occurrence of a
    physical source edge contributes its weight once even when copied by cuts.
    """
    if len(forms)!=circuit.dimension:
        raise ValueError("Readout dimension mismatch")
    forest = [[] for _ in lift.leaves]
    for a,b,cut in lift.links:
        forest[a].append((b,cut))
        forest[b].append((a,cut))
    seen = set()

    def visit(i, parent, interface):
        assert i not in seen
        seen.add(i)
        leaf = lift.leaves[i]
        board = leaf.board
        slots = {e:([weight[e]] if lift.edge_owner[e]==i else []) for e in board.edges}
        for child,cut in forest[i]:
            if child==parent: continue
            answers = visit(child,i,cut)
            for e in cut:
                slots[e].append(answers[e])
        def local(key):
            return circuit.monomial(tuple(f.terms.get((i,key),0) for f in forms))
        if leaf.kind=="small":
            table = {m:circuit.times([local(m)]+[circuit.times(slots[e]) for e in sorted(m)])
                     for m in leaf.matches}
            return {p:circuit.plus(val for m,val in table.items() if p is None or p in m)
                    for p in interface}
        wire = {e:circuit.times(slots[e]+[local(e)]) for e in board.edges}
        def matching(pin):
            fixed = board.edges[pin] if pin is not None else (None,None)
            left = sorted(board.left-{fixed[0]})
            right = sorted(board.right-{fixed[1]})
            bycell = {}
            for e,ij in board.edges.items():
                bycell.setdefault(ij,[]).append(wire[e])
            matrix = [[circuit.plus(bycell.get((a,b),())) for b in right] for a in left]
            return circuit.times((circuit.perm(matrix),wire[pin] if pin is not None else circuit.one))
        return {p:matching(p) for p in interface}

    factors = [circuit.monomial(tuple(f.constant for f in forms))]
    for i in range(len(lift.leaves)):
        if i not in seen:
            factors.append(visit(i,None,(None,))[None])
    return circuit.times(factors)
