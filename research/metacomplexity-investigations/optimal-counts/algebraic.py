"""Deterministic recognition of all-binary read-once functions by four-copy contraction."""
from collections import Counter
from functools import cache
from itertools import product

SCORES = (2, -2, 4, -8, 17)
MODES = ('one', 'zero', 'sign')


def operation(gate, a, b):
    return (gate >> (a + 2*b)) & 1


@cache
def word_operation(gate, left, right):
    return sum(operation(gate, left >> i & 1, right >> i & 1) << i for i in range(4))


def terminal_weight(mode, word):
    if mode == 'one':
        return int(word == 15)
    if mode == 'zero':
        return int(word == 0)
    return (-1) ** word.bit_count()


class BinaryCircuit:
    def __init__(self, n, gates):
        self.n = n
        self.gates = tuple(gates)
        self.uses = Counter()
        for wire, (operation_id, left, right) in enumerate(self.gates, n):
            if operation_id not in range(16) or left not in range(wire) or right not in range(wire):
                raise ValueError('invalid gate')
            self.uses.update((left, right))
        if n < 2 or not gates or any(self.uses[wire] == 0 for wire in range(n + len(gates) - 1)):
            raise ValueError('expected a trimmed circuit on at least two named inputs')
        self.shared = tuple(wire for wire, uses in self.uses.items() if uses > 1)

    def evaluate(self, bits):
        values = [bits >> i & 1 for i in range(self.n)]
        for gate, left, right in self.gates:
            values.append(operation(gate, values[left], values[right]))
        return values[-1]

    def contract(self, unary, mode):
        """Return the exact signed partition sum for four copies of this circuit."""
        choices = [tuple(unary[wire]) if wire < self.n else range(16) for wire in self.shared]
        total = 0
        for proposal in product(*choices):
            fixed = dict(zip(self.shared, proposal))
            factor = 1
            weights = []
            for wire in range(self.n + len(self.gates)):
                if wire < self.n:
                    row = unary[wire]
                else:
                    gate, left, right = self.gates[wire - self.n]
                    row = {}
                    for a, aw in weights[left].items():
                        for b, bw in weights[right].items():
                            output = word_operation(gate, a, b)
                            row[output] = row.get(output, 0) + aw*bw
                if wire in fixed:
                    guess = fixed[wire]
                    factor *= row.get(guess, 0)
                    if factor == 0:
                        break
                    row = {guess: 1}
                weights.append(row)
            else:
                total += factor * sum(weight * terminal_weight(mode, word)
                                      for word, weight in weights[-1].items())
        return total

    def energy(self, pins, first, second, mode):
        """Compute sum of squared commutators over every ternary background."""
        background = {word: SCORES[word.bit_count()] for word in range(16)}
        unary = [{15*pins[i]: 1} if i in pins else background for i in range(self.n)]
        # Each ordered pair encodes one of the four Boolean corner cofactors.
        diagonal = ((0, 0), (1, 1))
        opposite = ((0, 1), (1, 0))
        result = 0
        for corners, multiplicity in ((diagonal*2, 1), (opposite*2, 1), (diagonal+opposite, -2)):
            unary[first] = {sum(a << j for j, (a, b) in enumerate(corners)): 1}
            unary[second] = {sum(b << j for j, (a, b) in enumerate(corners)): 1}
            result += multiplicity * self.contract(unary, mode)
        assert result >= 0
        return result

    def model(self, pins, wanted):
        """Find a Boolean normalizing corner in the given restricted circuit."""
        choices = [(pins[v],) if v in pins else (0, 1) for v in self.shared]
        for proposal in product(*choices):
            fixed = dict(zip(self.shared, proposal))
            background = 0
            wires = []
            for wire in range(self.n + len(self.gates)):
                if wire < self.n:
                    values = {b: b << wire for b in ((pins[wire],) if wire in pins else (0, 1))}
                else:
                    gate, left, right = self.gates[wire - self.n]
                    values = {}
                    for a, ax in wires[left].items():
                        for b, bx in wires[right].items():
                            values.setdefault(operation(gate, a, b), ax | bx)
                if wire in fixed:
                    selected = fixed[wire]
                    if selected not in values:
                        break
                    background |= values[selected]
                    values = {selected: 0}
                wires.append(values)
            else:
                if wanted in wires[-1]:
                    return background | wires[-1][wanted]
        return None

    def recognize(self, active=None, pins=None):
        """Return a signed-leaf read-once tree, or None, under the essential-input promise."""
        if pins is None:
            pins = {}
        if active is None:
            active = tuple(range(self.n))
        if len(active) == 1:
            wire = active[0]
            baseline = sum(value << i for i, value in pins.items())
            v0 = self.evaluate(baseline)
            if v0 == self.evaluate(baseline | (1 << wire)):
                raise ValueError('restricted input is inessential')
            return ('leaf', wire, v0)
        for mode in MODES:
            anchor = active[0]
            # Nonzero commutator pairs form disjoint cliques, one for each factor.
            component = {anchor} | {v for v in active[1:] if self.energy(pins, anchor, v, mode)}
            if len(component) == len(active):
                continue
            left = tuple(sorted(component))
            right = tuple(v for v in active if v not in component)
            if mode == 'sign':
                corner = sum(value << i for i, value in pins.items())
                gate = 9 if self.evaluate(corner) else 6
            else:
                corner = self.model(pins, int(mode == 'one'))
                if corner is None:
                    raise ValueError('constant restricted function')
                gate = 8 if mode == 'one' else 14
            ltree = self.recognize(left, pins | {i: corner >> i & 1 for i in right})
            rtree = self.recognize(right, pins | {i: corner >> i & 1 for i in left})
            if ltree is None or rtree is None:
                return None
            return (gate, ltree, rtree)
        return None


def tree_value(tree, bits):
    if tree[0] == 'leaf':
        return ((bits >> tree[1]) & 1) ^ tree[2]
    gate, left, right = tree
    return operation(gate, tree_value(left, bits), tree_value(right, bits))


def physical_gates(n, tree):
    """Compile a returned signed-leaf tree to exactly N-1 ordinary binary gates."""
    gates = []
    def emit(node):
        if node[0] == 'leaf':
            return node[1], node[2]
        code, left, right = node
        left_wire, left_sign = emit(left)
        right_wire, right_sign = emit(right)
        adjusted = sum(operation(code, a ^ left_sign, b ^ right_sign) << (a + 2*b)
                       for a, b in product((0, 1), repeat=2))
        gates.append((adjusted, left_wire, right_wire))
        return n + len(gates) - 1, 0
    output, output_sign = emit(tree)
    if output_sign or output != n + len(gates) - 1 or len(gates) != n - 1:
        raise ValueError('expected a read-once tree spanning all named variables')
    return gates


def canonical_shape(tree):
    """Contract nested nodes of the same normalized associative root family."""
    if tree[0] == 'leaf':
        return ('leaf', [])
    gate, left, right = tree
    family = 'one' if gate == 8 else 'zero' if gate == 14 else 'sign'
    children = []
    for subtree in (left, right):
        label, grandchildren = canonical_shape(subtree)
        if label == family:
            children.extend(grandchildren)
        else:
            children.append((label, grandchildren))
    return family, children


def optimal_syntax(tree):
    """Count ordered optimum tree syntaxes and their common XOR-family gate count."""
    from math import comb, factorial
    def summarize(node):
        label, children = node
        if label == 'leaf':
            return 1, 1, 0
        k = len(children)
        choices = factorial(k) * (comb(2*k-2, k-1) // k)
        leaves = 0
        parity_count = k - 1 if label == 'sign' else 0
        for child in children:
            size, refinements, parity_gates = summarize(child)
            leaves += size
            choices *= refinements
            parity_count += parity_gates
        return leaves, choices, parity_count
    leaves, choices, parity_count = summarize(canonical_shape(tree))
    if leaves < 2:
        raise ValueError('expected a formula on at least two essential inputs')
    return (1 << (leaves - 2)) * choices, parity_count


def optimal_programs(tree):
    """Count all gate-indexed, topologically ordered minimum straight-line programs."""
    from fractions import Fraction
    from math import comb, factorial, prod
    @cache
    def hook_sum(groups):
        if sum(m for weight, m in groups) == 1:
            return Fraction(1)
        result = Fraction(0)
        for selected in product(*(range(m+1) for weight, m in groups)):
            left = tuple((w, v) for (w, m), v in zip(groups, selected) if v)
            right = tuple((w, m-v) for (w, m), v in zip(groups, selected) if m-v)
            if not left or not right:
                continue
            distinct_labels = prod(comb(m,v) for (w,m),v in zip(groups,selected))
            result += distinct_labels * hook_sum(left) * hook_sum(right)
        return result / (sum(w*m for w,m in groups) - 1)
    def fold(node):
        label, children = node
        if label == 'leaf':
            return 1, Fraction(1)
        parts = [fold(child) for child in children]
        weights = tuple(sorted(Counter(size for size, _ in parts).items()))
        return sum(size for size, _ in parts), hook_sum(weights) * prod(count for _, count in parts)
    n, total = fold(canonical_shape(tree))
    if n < 2:
        raise ValueError('expected a formula on at least two essential inputs')
    result = (1 << (n-2)) * factorial(n-1) * total
    assert result.denominator == 1
    return result.numerator
