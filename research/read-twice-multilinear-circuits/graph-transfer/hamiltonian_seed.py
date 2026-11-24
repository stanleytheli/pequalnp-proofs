"""Polynomial explicit Hamiltonian-cycle projection to a bounded-degree long subdivision.

The returned graph is unsigned. Its vertex labels specify the requested algebraic
specialization of the multivariate independence polynomial. A label ("x", i, j)
denotes a matrix variable. In probability-leaf mode ("prob", i, j) is a leaf
with probability 1-x_ij and all other labels are constant activities.
"""

from dataclasses import dataclass, field


@dataclass
class Formula:
    variables: int = 0
    clauses: list = field(default_factory=list)
    operations: list = field(default_factory=list)

    def variable(self):
        self.variables += 1
        return self.variables

    def clause(self, *literals):
        self.clauses.append(tuple(dict.fromkeys(literals)))

    def conjunction(self, a, b):
        z = self.variable()
        self.clause(-z, a)
        self.clause(-z, b)
        self.clause(z, -a, -b)
        self.operations.append((z, "and", a, b))
        return z

    def exclusive_or(self, a, b):
        z = self.variable()
        self.clause(a, b, -z)
        self.clause(-a, -b, -z)
        self.clause(a, -b, z)
        self.clause(-a, b, z)
        self.operations.append((z, "xor", a, b))
        return z


def successor(formula, bits, modulus):
    """Increment modulo the next power of two, except that modulus-1 goes to zero."""
    reset_literals = [bit if (modulus - 1) >> i & 1 else -bit for i, bit in enumerate(bits)]
    reset = reset_literals[0]
    for bit in reset_literals[1:]:
        reset = formula.conjunction(reset, bit)
    increment = [-bits[0]]
    carry = bits[0]
    for i in range(1, len(bits)):
        increment.append(formula.exclusive_or(bits[i], carry))
        if i + 1 < len(bits):
            carry = formula.conjunction(carry, bits[i])
    return [formula.conjunction(bit, -reset) for bit in increment]


def circuit_formula(n):
    if n < 2:
        raise ValueError("the Hamiltonian seed uses n >= 2")
    b = (n - 1).bit_length()
    formula = Formula()
    edges = [[formula.variable() for _ in range(n)] for _ in range(n)]
    ranks = [[formula.variable() for _ in range(b)] for _ in range(n)]
    for bit in ranks[0]:
        formula.clause(-bit)
    for row in edges:
        seen = row[0]
        for entry in row[1:]:
            formula.clause(-seen, -entry)
            seen = -formula.conjunction(-seen, -entry)
        formula.clause(seen)
    successors = [successor(formula, bits, n) for bits in ranks]
    for i, row in enumerate(edges):
        for j, entry in enumerate(row):
            for this, following in zip(successors[i], ranks[j]):
                formula.clause(-entry, -this, following)
                formula.clause(-entry, this, -following)
    return formula, edges, ranks


@dataclass
class WeightedGraph:
    labels: list = field(default_factory=list)
    edges: list = field(default_factory=list)

    def vertex(self, label):
        self.labels.append(label)
        return len(self.labels) - 1

    def edge(self, u, v):
        if u == v:
            raise ValueError("loop")
        self.edges.append((u, v))

    def degrees(self):
        degree = [0] * len(self.labels)
        for u, v in self.edges:
            degree[u] += 1
            degree[v] += 1
        return degree


def literal_graph(variable_count, clauses):
    graph = WeightedGraph()
    literal = {}
    for bit in range(1, variable_count + 1):
        literal[bit] = graph.vertex(1)
        literal[-bit] = graph.vertex(1)
        flag = graph.vertex(-1)
        graph.edge(literal[bit], literal[-bit])
        graph.edge(flag, literal[bit])
        graph.edge(flag, literal[-bit])
    for clause in clauses:
        flag = graph.vertex(-1)
        for entry in clause:
            graph.edge(flag, literal[entry])
    return graph, literal


def hc_seed(n, probability_leaves=False):
    formula, edge_bits, _ = circuit_formula(n)
    graph, literal = literal_graph(formula.variables, formula.clauses)
    for i, row in enumerate(edge_bits):
        for j, bit in enumerate(row):
            if probability_leaves:
                leaf = graph.vertex(("prob", i, j))
                graph.edge(leaf, literal[bit])
            else:
                graph.labels[literal[bit]] = ("x", i, j)
    if len(graph.edges) % 2:
        graph.edge(literal[-1], graph.vertex(0))
    return graph


def split_degree(graph, sign_at_end=False):
    degree = graph.degrees()
    if not all(degree):
        raise ValueError("isolated vertices must first be treated separately")
    result = WeightedGraph()
    copies = []
    for activity, count in zip(graph.labels, degree):
        row = [result.vertex(activity)]
        sign_index = count-1 if sign_at_end else 1
        for k in range(1, count):
            row.append(result.vertex(-1 if k == sign_index and count % 2 == 0 else 1))
        copies.append(iter(row))
        for a, b in zip(row, row[1:]):
            s = result.vertex(-1)
            t = result.vertex(-1)
            result.edge(a, s)
            result.edge(s, t)
            result.edge(t, b)
    for u, v in graph.edges:
        result.edge(next(copies[u]), next(copies[v]))
    return result


def subdivide(graph, length=10):
    if length < 10 or length % 6 != 4:
        raise ValueError("use an even length congruent to 4 modulo 6 and at least 10")
    result = WeightedGraph(graph.labels.copy())
    for u, v in graph.edges:
        previous = u
        for _ in range(length - 1):
            following = result.vertex(-1)
            result.edge(previous, following)
            previous = following
        result.edge(previous, v)
    return result


def build(n, length=10, probability_leaves=False):
    return subdivide(split_degree(hc_seed(n, probability_leaves)), length)
