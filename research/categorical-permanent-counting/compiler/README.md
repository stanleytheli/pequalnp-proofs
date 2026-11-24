# Compiling pure corner counts into ordinary monotone circuits

The compiler takes a finite arithmetic circuit with nonnegative real or rational coefficients, ordinary variables, sums, products and explicitly wired square permanent gates. It also takes a list of pairs of variable sets. For each pair, every positive parse at the output must meet exactly one side. Several occurrences from the same side are allowed. An output variable records whether the parse met the first side. The compiled polynomial has one copy of each such variable, with exactly the original parse coefficient. This preserves the weighted sum across all parses yielding the same support.

For the perfect-matching count, take one pair for each edge. The first side contains just that edge and the second contains its competitors at one endpoint. A directed tour works the same way using arcs leaving its tail. Exact agreement on the Boolean cube forces every positive parse to have exactly the support of a target witness, so these are valid pairs. More generally, the input may be any circuit satisfying the indicated categorical promise.

The implementation uses a bipartite matching routine to remove unusable slots and finds a tight cut from a failed attempt to prescribe two disjoint matched edges. At terminal factors of order at most three it lists the individual matchings, including parallel-edge choices. Larger terminal factors use affine sums of edge incidences. Messages on the tree of factors preserve original coefficients. A final pass eliminates all Laurent monomials with negative exponents using integral assignment potentials. The returned circuit contains ordinary variable leaves, nonnegative scalars, additions, multiplications and permanent gates. Shared expressions are represented by reused gate indices.

From this directory run the following with Python 3.9 or later.

```sh
python3 check_compiler.py
```

The controls compare the output with exact interpolation of the original circuit on every Boolean input in small examples. They include zero coordinates and positive rational evaluations outside the unit cube. Separate tests compare each recovered indicator directly on individual matchings and each integral assignment dual with an exhaustive optimum. The implementation builds a circuit in polynomial time under its stated promise. Evaluating a permanent gate for the included small tests explicitly enumerates its permutations.

A minimal example follows. The 3 by 3 matrix has permanent 2x+x²+2y+y². The compiled output is 3x+3y.

```python
from weighted_compiler import Circuit
from purify_circuit import purify

source = Circuit(2)
x = source.monomial((1, 0))
y = source.monomial((0, 1))
one = source.one
root = source.perm([[x, one, y], [y, one, x], [one, one, one]])
result, output = purify(source, root, [({0}, {1}), ({1}, {0})])
assert result.evaluate(output, [2, 7]) == 27
```
