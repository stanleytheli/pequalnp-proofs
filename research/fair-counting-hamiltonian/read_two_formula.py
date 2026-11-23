"""A balanced, explicit optimum read-two formula for an even-subdivided graph.

Inputs are the base edge list and the common even path length. Physical input
numbering matches hamiltonian_seed.subdivide and fair_counting.unweighted_subdivision.
"""
from dataclasses import dataclass, field
from incident_matching import incident_matching


@dataclass
class Formula:
    variables: int
    gates: list = field(default_factory=list)
    output: int = -1

    def binary(self, operation, left, right):
        self.gates.append((operation, left, right))
        return self.variables + len(self.gates) - 1

    def disjunction(self, wires):
        if not wires:
            raise ValueError("a nonempty star list is required")
        while len(wires) > 1:
            following = [self.binary("or", wires[i], wires[i+1]) for i in range(0, len(wires)-1, 2)]
            if len(wires)%2:
                following.append(wires[-1])
            wires = following
        return wires[0]

    def evaluate(self, values):
        if len(values) != self.variables:
            raise ValueError("incorrect assignment length")
        bits = list(values)
        for operation, left, right in self.gates:
            bits.append(bits[left] and bits[right] if operation == "and" else bits[left] or bits[right])
        return bits[self.output]

    def audit(self):
        reads = [0]*(self.variables+len(self.gates))
        for index, (kind, a, b) in enumerate(self.gates):
            if kind not in {"and","or"} or not (0<=a<self.variables+index and 0<=b<self.variables+index):
                raise ValueError("invalid binary gate")
            reads[a] += 1
            reads[b] += 1
        if any(use != 1 for use in reads[self.variables:self.output]) or reads[self.output] != 0:
            raise ValueError("an internal gate is shared or unused")
        if not all(1<=use<=2 for use in reads[:self.variables]):
            raise ValueError("the input occurrence limit fails")
        return max(reads[:self.variables])


def build_formula(vertex_count, edges, length=10):
    if length<8 or length%2:
        raise ValueError("every path must have an even length of at least eight")
    if not edges:
        raise ValueError("the graph must contain an edge")
    incident_matching(vertex_count,edges)
    variables = vertex_count + (length-1)*len(edges)
    f = Formula(variables)
    stars = {}
    for index,(u,v) in enumerate(edges):
        first = vertex_count + (length-1)*index
        route = [u,*range(first,first+length-1),v]
        for j in range(1,length,2):
            for center in (route[j-1],route[j+1]):
                stars.setdefault(center,[]).append(route[j])
    roots = [f.binary("and",center,f.disjunction(others)) for center,others in stars.items()]
    f.output = f.disjunction(roots)
    h = (length-2)//2
    optimum = (3*h+2)*len(edges)+vertex_count-1
    assert len(f.gates) == optimum
    f.audit()
    return f


if __name__ == "__main__":
    from random import Random
    from hamiltonian_seed import hc_seed,split_degree,subdivide
    rng = Random(20261123)
    for n in (2,3,4,5):
        base = split_degree(hc_seed(n,probability_leaves=True))
        physical = subdivide(base)
        f = build_formula(len(base.labels),base.edges)
        assert f.variables==len(physical.labels)
        for _ in range(8):
            ones = set(rng.sample(range(f.variables),int(f.variables**.5)))
            assert f.evaluate([i in ones for i in range(f.variables)])==any(u in ones and v in ones for u,v in physical.edges)
        for u,v in (physical.edges[0],physical.edges[-1]):
            assert f.evaluate([i==u or i==v for i in range(f.variables)])
            assert not f.evaluate([i==u for i in range(f.variables)])
        print(f"HC n={n} variables={f.variables} gates={len(f.gates)} max_reads={f.audit()}")
