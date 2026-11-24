"""Read-once recognition for a trimmed, all-essential, binary monotone circuit."""
from collections import Counter
from itertools import combinations, product

# Signatures list truth values in order 00, 10, 01, 11 (low bit first).
FIRST = 10
SECOND = 12
AND = 8
OR = 14
TRUE = 15
MONOTONE = (0, TRUE, FIRST, SECOND, AND, OR)


def gate_value(operation, left, right):
    return left & right if operation == 'and' else left | right


def check_cone(n, gates):
    if n < 2 or not gates:
        raise ValueError('expected at least two inputs and one gate')
    uses = Counter()
    for wire, (operation, left, right) in enumerate(gates, n):
        if operation not in ('and', 'or') or not (0 <= left < wire and 0 <= right < wire):
            raise ValueError(f'invalid gate at wire {wire}')
        uses.update((left, right))
    if any(uses[wire] == 0 for wire in range(n + len(gates) - 1)):
        raise ValueError('circuit must be trimmed')
    return uses


def attainable(n, gates, first, second, uses=None):
    """Return each attainable signature with one witnessing background assignment."""
    if uses is None:
        uses = check_cone(n, gates)
    shared = [wire for wire, count in uses.items() if count > 1]
    choices = []
    for wire in shared:
        if wire == first:
            choices.append((FIRST,))
        elif wire == second:
            choices.append((SECOND,))
        elif wire < n:
            choices.append((0, TRUE))
        else:
            choices.append(MONOTONE)
    answers = {}
    for signatures in product(*choices):
        guesses = dict(zip(shared, signatures))
        wires = []
        background = 0
        for wire in range(n + len(gates)):
            if wire < n:
                if wire == first:
                    values = {FIRST: 0}
                elif wire == second:
                    values = {SECOND: 0}
                else:
                    values = {0: 0, TRUE: 1 << wire}
            else:
                operation, left, right = gates[wire - n]
                values = {}
                for left_word, left_bits in wires[left].items():
                    for right_word, right_bits in wires[right].items():
                        word = gate_value(operation, left_word, right_word)
                        values.setdefault(word, left_bits | right_bits)
            if wire in guesses:
                selected = guesses[wire]
                if selected not in values:
                    break
                background |= values[selected]
                values = {selected: 0}
            wires.append(values)
        else:
            for word, bits in wires[-1].items():
                answers.setdefault(word, background | bits)
    return answers


def evaluate_circuit(n, gates, assignment):
    wires = [(assignment >> wire) & 1 for wire in range(n)]
    for operation, left, right in gates:
        wires.append(gate_value(operation, wires[left], wires[right]))
    return wires[-1]


def components(vertices, linked):
    unseen = set(vertices)
    groups = []
    while unseen:
        start = min(unseen)
        unseen.remove(start)
        group = [start]
        for source in group:
            for target in sorted(unseen):
                if linked(source, target):
                    unseen.remove(target)
                    group.append(target)
        groups.append(tuple(sorted(group)))
    return groups


def cotree(vertices, pairs):
    if len(vertices) == 1:
        return vertices[0]
    def adjacent(left, right):
        return (min(left, right), max(left, right)) in pairs
    groups = components(vertices, adjacent)
    operation = 'or'
    if len(groups) == 1:
        groups = components(vertices, lambda left, right: not adjacent(left, right))
        operation = 'and'
    if len(groups) == 1:
        raise ValueError('the promised essential monotone inputs do not admit this cotree')
    nodes = [cotree(group, pairs) for group in groups]
    tree = nodes[0]
    for node in nodes[1:]:
        tree = (operation, tree, node)
    return tree


def recognize(n, gates):
    """Return (True, optimal tree) or (False, (a,b,AND-background,OR-background))."""
    uses = check_cone(n, gates)
    pairs = set()
    for first, second in combinations(range(n), 2):
        found = attainable(n, gates, first, second, uses)
        if AND in found and OR in found:
            return False, (first, second, found[AND], found[OR])
        if AND in found:
            pairs.add((first, second))
    return True, cotree(tuple(range(n)), pairs)


def essential_support(n, gates):
    """Compute the actual semantic support using only two-input cofactor sets."""
    uses = check_cone(n, gates)
    support = set()
    for first, second in combinations(range(n), 2):
        words = attainable(n, gates, first, second, uses)
        for word in words:
            # Adjacent bits correspond to changing the first distinguished input.
            if (word ^ (word >> 1)) & 0b0101:
                support.add(first)
            if (word ^ (word >> 2)) & 0b0011:
                support.add(second)
    return support


def evaluate_tree(tree, assignment):
    if isinstance(tree, int):
        return (assignment >> tree) & 1
    operation, left, right = tree
    return gate_value(operation, evaluate_tree(left, assignment), evaluate_tree(right, assignment))
