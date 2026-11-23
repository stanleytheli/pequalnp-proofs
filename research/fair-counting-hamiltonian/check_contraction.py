"""Check projected partition functions directly on the emitted physical graph.

This exact finite-field contraction receives only the vertex labels and edge list.
It has no information about paths, equality gadgets, CNF variables or clauses.
"""
from collections import deque
from functools import reduce
from itertools import permutations
from operator import mul

from hamiltonian_seed import build


def transpose(a):
    return (a[0], a[2], a[1], a[3])


class Network:
    def __init__(self, graph, matrix, prime):
        self.prime = prime
        self.scale = 1
        self.unary = {}
        self.neighbors = {i: {} for i in range(len(graph.labels))}
        self.pending = deque(self.neighbors)
        for i, value in enumerate(graph.labels):
            if isinstance(value, int):
                self.unary[i] = (1, value % prime)
            else:
                kind, row, col = value
                x = matrix[row][col] % prime
                self.unary[i] = (1, x) if kind == "x" else (x, (1-x) % prime)
        for i, j in graph.edges:
            self.neighbors[i][j] = self.neighbors[j][i] = (1, 1, 1, 0)

    def edge(self, i, j, factor):
        old = self.neighbors[i].get(j)
        if old is not None:
            factor = tuple(a*b % self.prime for a, b in zip(old, factor))
        self.neighbors[i][j] = factor
        self.neighbors[j][i] = transpose(factor)
        self.pending.extend((i, j))

    def weight(self, i, factor):
        self.unary[i] = tuple(a*b % self.prime for a, b in zip(self.unary[i], factor))
        self.pending.append(i)

    def remove(self, i):
        row = self.neighbors.pop(i)
        weight = self.unary.pop(i)
        for j in row:
            del self.neighbors[j][i]
            self.pending.append(j)
        return row, weight

    def simplify(self):
        p = self.prime
        while self.pending and self.scale:
            i = self.pending.pop()
            if i not in self.neighbors:
                continue
            edges = self.neighbors[i]
            w = self.unary[i]
            if 0 in w:
                value = int(bool(w[1]))
                self.scale = self.scale * w[value] % p
                self.remove(i)
                for j, a in edges.items():
                    self.weight(j, (a[2*value], a[2*value+1]))
            elif not edges:
                self.scale = self.scale * sum(w) % p
                self.remove(i)
            elif len(edges) == 1:
                (j, a), = edges.items()
                self.remove(i)
                self.weight(j, ((w[0]*a[0]+w[1]*a[2]) % p, (w[0]*a[1]+w[1]*a[3]) % p))
            elif len(edges) == 2:
                (j, a), (k, b) = edges.items()
                self.remove(i)
                f = tuple((w[0]*a[x]*b[y]+w[1]*a[2+x]*b[2+y]) % p
                          for x in range(2) for y in range(2))
                self.edge(j, k, f)
            else:
                for j, a in list(edges.items()):
                    if (a[1] or a[2]) and (a[0] or a[3]):
                        continue
                    flip = int(not (a[0] or a[3]))
                    self.remove(i)
                    self.weight(j, tuple(w[y^flip]*a[2*(y^flip)+y] for y in range(2)))
                    for k, b in edges.items():
                        if k != j:
                            self.edge(j, k, tuple(b[2*(y^flip)+x] for y in range(2) for x in range(2)))
                    break

    def remaining_factors(self):
        factors = [((i,), w) for i, w in self.unary.items()]
        links = {i:set(row) for i,row in self.neighbors.items()}
        for i, ns in self.neighbors.items():
            factors += [((i,j), transpose(a)) for j,a in ns.items() if i < j]
        return factors, links


def contract(graph, matrix, prime, width_cap=20):
    net = Network(graph, matrix, prime)
    net.simplify()
    factors, links = net.remaining_factors()
    maximum = 0
    scalar = net.scale
    while links and scalar:
        i = min(links,key=lambda v: (len(links[v]), v))
        ns = tuple(sorted(links.pop(i)))
        maximum = max(maximum, len(ns))
        if maximum > width_cap:
            raise ValueError(f"contraction width {maximum} exceeded cap {width_cap}")
        for j in ns:
            links[j].discard(i)
            links[j].update(k for k in ns if k!=j)
        involved = [f for f in factors if i in f[0]]
        factors = [f for f in factors if i not in f[0]]
        order = (i,)+ns
        table = [1] * (1<<len(order))
        for scope, values in involved:
            positions = [order.index(x) for x in scope]
            for state, old in enumerate(table):
                selector = sum(((state>>pos)&1)<<j for j,pos in enumerate(positions))
                table[state] = old*values[selector] % prime
        reduced = tuple((a+b) % prime for a,b in zip(table[::2], table[1::2]))
        if ns:
            factors.append((ns,reduced))
        else:
            scalar = scalar*reduced[0] % prime
    return scalar, maximum


def cycles(matrix, prime):
    n=len(matrix)
    result=0
    for seq in permutations(range(1,n)):
        cycle=(0,)+seq+(0,)
        result += reduce(mul,(matrix[u][v] for u,v in zip(cycle,cycle[1:])),1)
    return result % prime


if __name__ == "__main__":
    from argparse import ArgumentParser
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--prime',type=int,default=101)
    parser.add_argument('--probability-leaves',action='store_true')
    args=parser.parse_args()
    n=args.n
    graph=build(n,probability_leaves=args.probability_leaves)
    matrix=[[(19*i+7*j+3*i*j+5)**2+3 for j in range(n)] for i in range(n)]
    result,width=contract(graph,matrix,args.prime)
    expected=cycles(matrix,args.prime)
    assert result==expected,(result,expected)
    print(f"n={n} prime={args.prime} probability_leaves={args.probability_leaves} vertices={len(graph.labels)} edges={len(graph.edges)} width={width} value={result}")
