"""Construct bounded-occurrence 3-CNFs with a fixed one-hot satisfying assignment.

All expressions use signed integer literals. A new variable denotes each binary
gate. This file uses only the Python standard library.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import combinations


def truth(values, literal):
    return values[abs(literal)] == (literal > 0)


class Circuit:
    def __init__(self, primary_count):
        self.primary_count = primary_count
        self.gates = []

    def gate(self, op, a, b):
        self.gates.append((op, a, b))
        return self.primary_count + len(self.gates)

    def collect(self, op, items):
        items = list(items)
        if not items:
            return self.gate("or" if op == "and" else "and", 1, -1)
        while len(items) > 1:
            combined = [self.gate(op, a, b) for a, b in zip(items[::2], items[1::2])]
            items = combined + (items[-1:] if len(items) % 2 else [])
        return items[0]

    def exactly_one(self, items):
        items = tuple(items)
        at_least = self.collect("or", items)
        at_most = [self.gate("or", -a, -b) for a, b in combinations(items, 2)]
        return self.collect("and", [at_least, *at_most])

    def evaluate(self, primaries):
        assert len(primaries) == self.primary_count
        values = [False, *primaries]
        for op, a, b in self.gates:
            left, right = truth(values, a), truth(values, b)
            values.append((left and right) if op == "and" else (left or right))
        return values

    def clauses(self, output):
        clauses = []
        for idx, (op, a, b) in enumerate(self.gates, self.primary_count + 1):
            if op == "and":
                clauses.extend(((-idx, a), (-idx, b), (idx, -a, -b)))
            else:
                clauses.extend(((idx, -a), (idx, -b), (-idx, a, b)))
        return clauses + [(output,)]


def cycle_checker(circuit, edges):
    order = len(edges)
    constraints = [circuit.exactly_one(row) for row in edges]
    constraints.extend(circuit.exactly_one(col) for col in zip(*edges))
    # Every vertex must be reachable from zero in at most order-1 steps.
    # Reachability is deterministic. There is exactly one setting of its wires.
    reached = [circuit.collect("and", []), *[circuit.collect("or", [])] * (order - 1)]
    for _ in range(order - 1):
        reached = [circuit.collect("or", [reached[j], *[
            circuit.gate("and", reached[i], edges[i][j]) for i in range(order)
        ]]) for j in range(order)]
    return circuit.collect("and", constraints + reached)


@dataclass
class Encoded:
    clauses: list
    signed_copies: list
    representative: list

    def extend(self, original):
        return [False, *[truth(original, literal) for literal in self.signed_copies[1:]]]

    def accepts(self, assignment):
        return all(any(truth(assignment, lit) for lit in clause) for clause in self.clauses)

    def occurrences(self):
        return Counter(abs(lit) for clause in self.clauses for lit in clause)


def bounded_occurrence(clauses, baseline, keep_positive=()):
    """One fresh physical variable per literal occurrence, one directed cycle per rail.

    A variable's physical value equals its logical value except for a possible
    fixed complement. Supply a known assignment baseline to move that assignment
    to zero at every physical coordinate except designated representatives.
    """
    copies = [[] for _ in baseline]
    owner = [0]
    result = []
    keep_positive = set(keep_positive)
    for clause in clauses:
        new_clause = []
        for old_lit in clause:
            old = abs(old_lit)
            flip = baseline[old] and (copies[old] or old not in keep_positive)
            physical = len(owner)
            owner.append(-old if flip else old)
            logical_positive = -physical if flip else physical
            copies[old].append(logical_positive)
            new_clause.append(logical_positive if old_lit > 0 else -logical_positive)
        result.append(tuple(new_clause))
    for old in range(1, len(copies)):
        if not copies[old]:
            raise ValueError("the declared exponent variable is unused")
        if len(copies[old]) >= 2:
            for a, b in zip(copies[old], copies[old][1:] + copies[old][:1]):
                result.append((-a, b))
    return Encoded(result, owner, [0, *[group[0] for group in copies[1:]]])


def planted(source_clauses, witness_bits, order):
    if order < 2:
        raise ValueError("Hamiltonian cycle order must be at least two")
    if any(len(clause) > 3 or any(not 1 <= abs(lit) <= witness_bits for lit in clause)
           for clause in source_clauses):
        raise ValueError("source must be a 3-CNF over the declared witnesses")
    flag = 1
    rails = [(2 + 2*i, 3 + 2*i) for i in range(witness_bits)]
    first_edge = 2 + 2*witness_bits
    edges = [[first_edge + order*i + j for j in range(order)] for i in range(order)]
    circuit = Circuit(first_edge - 1 + order*order)
    source = [circuit.collect("or", [rails[abs(lit)-1][lit > 0] for lit in clause])
              for clause in source_clauses]
    hard = circuit.collect("and", [-flag, *[circuit.exactly_one(pair) for pair in rails],
                                   *source, cycle_checker(circuit, edges)])
    base = circuit.collect("and", [flag, *[-i for i in range(2, circuit.primary_count+1)]])
    output = circuit.gate("or", base, hard)
    baseline = circuit.evaluate([True, *[False]*(circuit.primary_count-1)])
    bounded = bounded_occurrence(circuit.clauses(output), baseline, [flag])
    return circuit, bounded, rails, edges, output


def signed_transfer(positive, negative, positive_bits, negative_bits, order):
    """Compile two #SAT counts into a single signed transfer to the cycle polynomial."""
    flag_hc, flag_pos, flag_neg = 1, 2, 3
    p = list(range(4, 4+positive_bits))
    n = list(range(4+positive_bits, 4+positive_bits+negative_bits))
    start = 4+positive_bits+negative_bits
    edges = [[start + order*i + j for j in range(order)] for i in range(order)]
    edge_vars = [v for row in edges for v in row]
    circuit = Circuit(start-1+order*order)

    def sat(clauses, bits):
        return circuit.collect("and", [circuit.collect("or", [
            bits[abs(lit)-1] if lit > 0 else -bits[abs(lit)-1] for lit in cl
        ]) for cl in clauses])

    h = circuit.collect("and", [flag_hc, -flag_pos, -flag_neg, cycle_checker(circuit, edges),
                                 *[-v for v in p+n]])
    a = circuit.collect("and", [-flag_hc, flag_pos, -flag_neg, sat(positive, p),
                                 *[-v for v in n+edge_vars]])
    b = circuit.collect("and", [-flag_hc, -flag_pos, flag_neg, sat(negative, n),
                                 *[-v for v in p+edge_vars]])
    output = circuit.collect("or", [h, a, b])
    bounded = bounded_occurrence(circuit.clauses(output), [False]*(circuit.primary_count+len(circuit.gates)+1))
    return circuit, bounded, (flag_hc, flag_pos, flag_neg), p, n, edges, output


def tour_index(circuit, edges, count):
    """Order of visits to the disjoint pairs (1,2),(3,4),... on a tour."""
    order = len(edges)
    if order < 2*count+1:
        raise ValueError("need two non-root vertices per index bit")
    maybe_true = circuit.collect("and", [])
    maybe_false = circuit.collect("or", [])
    exact = [maybe_true, *[maybe_false]*(order-1)]
    seen_earlier = [maybe_false]*count
    earlier_first = [maybe_false]*count
    for _ in range(order):
        for i in range(count):
            left, right = 2*i+1, 2*i+2
            finished = circuit.gate("and", seen_earlier[i], exact[right])
            earlier_first[i] = circuit.gate("or", earlier_first[i], finished)
            seen_earlier[i] = circuit.gate("or", seen_earlier[i], exact[left])
        exact = [circuit.collect("or", [
            circuit.gate("and", exact[i], edges[i][j]) for i in range(order)
        ]) for j in range(order)]
    return earlier_first


def unsigned_fibers(clauses, index_bits, witness_bits, order, baseline):
    """Coefficients of accepted tours equal (baseline? 1 : 0) + #witnesses.

    The relation clauses use index bits first and witness bits last.
    """
    flag = 1
    witnesses = list(range(2, 2+witness_bits))
    start = 2+witness_bits
    edges = [[start + order*i + j for j in range(order)] for i in range(order)]
    circuit = Circuit(start-1+order*order)
    indices = tour_index(circuit, edges, index_bits)
    bits = indices + witnesses
    checks = [circuit.collect("or", [bits[abs(lit)-1] if lit > 0 else -bits[abs(lit)-1]
                                     for lit in clause]) for clause in clauses]
    witness_branch = circuit.collect("and", [-flag, *checks])
    if baseline:
        empty_branch = circuit.collect("and", [flag, *[-v for v in witnesses]])
        choice = circuit.gate("or", empty_branch, witness_branch)
    else:
        choice = witness_branch
    output = circuit.gate("and", choice, cycle_checker(circuit, edges))
    bounded = bounded_occurrence(circuit.clauses(output), [False]*(circuit.primary_count+len(circuit.gates)+1))
    return circuit, bounded, flag, witnesses, edges, indices, output
