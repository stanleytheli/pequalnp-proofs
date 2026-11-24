"""A parsimonious Hamiltonian-cycle witness of O(n²) gates and clauses.

WeightedGraph and Tseitin gate encodings are from the companion seed program.
One-hot addresses are encoded by a balanced OR tree. A Batcher network sorts
one destination/rank record per vertex; no individual arc copies a rank.
"""
from itertools import permutations, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/'graph-transfer'))
from hamiltonian_seed import Formula, literal_graph, successor


class Builder(Formula):
    def __init__(self):
        super().__init__()
        self.false = self.variable()
        self.clause(-self.false)

    def both(self,a,b):
        if a == self.false or b == self.false or a == -b:
            return self.false
        if a == -self.false or a == b:
            return b
        if b == -self.false:
            return a
        return self.conjunction(a,b)

    def either(self,a,b):
        return -self.both(-a,-b)

    def difference(self,a,b):
        if a == b:
            return self.false
        if a == -b:
            return -self.false
        if a == self.false:
            return b
        if b == self.false:
            return a
        if a == -self.false:
            return -b
        if b == -self.false:
            return -a
        return self.exclusive_or(a,b)

    def choose(self,selector,yes,no):
        if yes == no:
            return yes
        return self.either(self.both(selector,yes),self.both(-selector,no))

    def same(self,a,b):
        if a != b:
            self.clause(-a,b)
            self.clause(a,-b)

    def address(self,row):
        """Return any-set and little-endian address; enforce at most one."""
        if len(row) == 1:
            return row[0],[]
        cut = len(row)//2
        left,ls = self.address(row[:cut])
        right,rs = self.address(row[cut:])
        if left != self.false and right != self.false:
            self.clause(-left,-right)
        return self.either(left,right), [self.either(a,b) for a,b in zip(ls,rs)]+[right]

    def compare(self,left,right,ascending):
        lk,ld = left
        rk,rd = right
        swap = self.false
        for a,b in zip(lk,rk):
            if a == b:
                continue
            swap = self.choose(self.difference(a,b),a if ascending else b,swap)
        def exchange(a,b):
            d = self.both(swap,self.difference(a,b))
            return self.difference(a,d),self.difference(b,d)
        keys = [exchange(a,b) for a,b in zip(lk,rk)]
        data = [exchange(a,b) for a,b in zip(ld,rd)]
        return ([ab[0] for ab in keys],[ab[0] for ab in data]), ([ab[1] for ab in keys],[ab[1] for ab in data])

    def sort(self,records):
        size = 2
        while size <= len(records):
            stride = size // 2
            while stride:
                for i in range(len(records)):
                    j = i ^ stride
                    if i < j:
                        records[i],records[j] = self.compare(records[i],records[j],(i & size)==0)
                stride //= 2
            size *= 2


def formula(n):
    if n < 2:
        raise ValueError('the witness is defined for n >= 2')
    b = (n-1).bit_length()
    m = 1<<b
    f = Builder()
    edges = [[f.variable() for j in range(n)] for i in range(n)]
    ranks = [[f.variable() for _ in range(b)] for i in range(n)]
    for z in ranks[0]:
        f.clause(-z)
    records = []
    for row,rank in zip(edges,ranks):
        present,address = f.address(row+[f.false]*(m-n))
        f.clause(present)
        records.append((address+[f.false],successor(f,rank,n)))
    dummy = ([f.false]*b+[-f.false],[f.false]*b)
    records.extend([dummy]*(m-n))
    f.sort(records)
    for j in range(n):
        key,rank = records[j]
        for bit,wire in enumerate(key):
            f.clause(wire if j>>bit & 1 else -wire)
        for a,z in zip(rank,ranks[j]):
            f.same(a,z)
    return f, edges, ranks


def seed(n,probability_leaves=True):
    f,arcs,_ = formula(n)
    graph,literal = literal_graph(f.variables,f.clauses)
    for i,row in enumerate(arcs):
        for j,bit in enumerate(row):
            if probability_leaves:
                graph.edge(graph.vertex(('prob',i,j)),literal[bit])
            else:
                graph.labels[literal[bit]] = ('x',i,j)
    return graph


def evaluate(f,arcs,ranks,out,values):
    state = [False]*(f.variables+1)
    for i,row in enumerate(arcs):
        state[row[out[i]]] = True
        for k,wire in enumerate(ranks[i]):
            state[wire] = bool(values[i]>>k & 1)
    def bit(z):
        return state[abs(z)] != (z<0)
    for z,gate,a,b in f.operations:
        u,v = bit(a),bit(b)
        state[z] = u and v if gate == 'and' else u != v
    return all(any(bit(l) for l in clause) for clause in f.clauses)


def expected(out):
    path = []
    v = 0
    while v not in path:
        path.append(v)
        v = out[v]
    if v != 0 or len(path) != len(out):
        return None
    return tuple(path.index(i) for i in range(len(out)))


def check():
    comparisons = 0
    for n in (2,3):
        f,arcs,ranks = formula(n)
        m = 1<<((n-1).bit_length())
        for out in product(range(n),repeat=n):
            answer = expected(out)
            for tail in product(range(m),repeat=n-1):
                vals = (0,)+tail
                assert evaluate(f,arcs,ranks,out,vals) == (answer==vals)
                comparisons += 1
    for n in (4,5,6):
        f,arcs,ranks = formula(n)
        tests = 0
        for out in permutations(range(n)):
            answer = expected(out)
            values = answer or tuple(range(n))
            assert evaluate(f,arcs,ranks,out,values) == (answer is not None)
            bad = list(values)
            bad[-1] ^= 1
            assert not evaluate(f,arcs,ranks,out,bad)
            tests += 2
        comparisons += tests
        print(f'n={n} assignments={tests} variables={f.variables} clauses={len(f.clauses)}',flush=True)
    print('independently checked anchored rank assignments:',comparisons,flush=True)


if __name__ == '__main__':
    check()
