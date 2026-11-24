"""Three disjoint clause layers yielding a homogeneous paired model enumerator."""
from dataclasses import dataclass
from itertools import chain


@dataclass
class LayeredCNF:
    variable_count: int
    layers: list
    owner: list
    first: list

    def extend(self, assignment):
        return [False, *[(assignment[abs(v)] if v > 0 else not assignment[-v]) for v in self.owner[1:]]]

    def accepts(self, physical):
        return all(any(physical[abs(v)] == (v > 0) for v in clause)
                   for layer in self.layers for clause in layer)


def paired_layers(clauses, count):
    """Split old clauses into a read-once payload and two matchings.

    Source assignments are indexed starting at one. Each positional pair is
    (old bit, complementary old bit), even for repeated literals of one clause.
    """
    if any(not 1 <= len(cl) <= 3 or any(not 1 <= abs(l) <= count for l in cl) for cl in clauses):
        raise ValueError("input needs nonempty clauses of width at most three")
    old = [tuple(cl) if len(cl) > 1 else (cl[0], cl[0]) for cl in clauses]
    used = {abs(v) for cl in old for v in cl}
    old.extend((i, -i) for i in range(1, count+1) if i not in used)
    groups = [[] for _ in range(count+1)]
    owner = [0]
    payload = []
    for clause in old:
        copies = []
        for _ in range(2):
            row = []
            mates = []
            for literal in clause:
                v = abs(literal)
                bit = len(owner)
                mate = bit+1
                owner.extend((v, -v))
                groups[v].append((bit, mate))
                row.append(bit if literal > 0 else -bit)
                mates.append(mate)
            copies.append(mates)
            payload.append(tuple(row))
        # The two mate coordinates for the same old literal are equal, so this
        # extra binary clause costs no model and consumes one slot on each.
        payload.extend((a, -b) for a, b in zip(*copies))
    first_layer = []
    second_layer = []
    for group in groups[1:]:
        for (x, mate), (next_x, _) in zip(group, group[1:]+group[:1]):
            first_layer.append((-x, -mate))
            second_layer.append((mate, next_x))
    return LayeredCNF(len(owner)-1, [first_layer, second_layer, payload], owner,
                      [0, *[g[0][0] for g in groups[1:]]])


def dualized_gates(circuit, output, baseline_flag=1):
    """Encode the old Boolean network relative to a new reference coordinate."""
    phase = circuit.primary_count + len(circuit.gates) + 1
    conditions = []
    for z, (op, x, y) in enumerate(circuit.gates, circuit.primary_count+1):
        signed = (x, y, phase if op == "and" else -phase)
        for i, j in ((0,1), (0,2), (1,2)):
            a, b = signed[i], signed[j]
            conditions.append((-a, -b, z))
            conditions.append((a, b, -z))
    # Absolute accepted output is opposite the reference phase.
    conditions.extend(((output, phase), (-output, -phase)))
    # In phase one retain only the old logical baseline, whose absolute
    # baseline flag is then zero. All other accepted models use phase zero.
    conditions.append((-phase,-baseline_flag))
    return conditions, phase
