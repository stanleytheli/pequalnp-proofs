# Circuit minimization at the first possible gate count

Consider a Boolean function depending on all N input bits, specified by a
single-output, acyclic, fan-in-two circuit. Each binary gate costs one. Wires
and fanout are free. Write g for the size of the supplied circuit after
removing unused gates, and r=g−N+1. The question is whether the function
has a circuit of size at most N−1. The upper bounds below allow arbitrary
binary Boolean gates in a candidate minimum circuit.

## Why N−1 means read-once

The cone of the output is connected as an undirected graph. With N inputs
and g gates it has N+g vertices and at most 2g edges, counting repeated
operands separately. Thus g≥N−1. At equality the cone is a tree, with
every input appearing exactly once. In particular the function has a
read-once binary formula. Conversely each read-once binary formula
depending on all N inputs uses N−1 gates.

If the resulting function is monotone, every essential internal subformula
of such a tree is monotone or antitone. Fix variables outside it so that
the parent context depends on its value. The context then returns either
that value or its complement. Orient its output accordingly. The oriented
children of each gate depend on disjoint variable sets and attain both
values. Endpoints of increasing assignments in these two sets show that
the oriented gate is monotone separately in both arguments. Every
essential two-input monotone Boolean function is AND or OR. Consequently
the arbitrary-basis read-once and monotone read-once criteria agree for
monotone targets.

## Recognition from an explicit near-minimal circuit

**Theorem.** An N-variable syntactically monotone circuit with g=N−1+r
gates and all N inputs essential admits deterministic time
O(N²g·6^r) recognition at threshold N−1. The algorithm can return two
explicit restrictions witnessing failure or an optimal formula witnessing
success.

For distinct inputs a,b, consider all two-variable functions obtained by
fixing every other input. Some minterm contains a,b exactly when AND is
one such restriction. A minterm yields this restriction by setting its
other variables to one and all variables outside the minterm to zero.
Conversely the true (1,1) corner of an AND restriction contains a minterm;
neither distinguished input can be omitted since the other two corners
are false. Dually, some minimal set of zeros forcing rejection contains
both variables exactly when OR is an attainable restriction. Every
minterm meets every such minimal zero set. By Gurvich's characterization
the function is read-once exactly when no pair admits both kinds of
restriction. [Karchmer, Linial, Newman, Saks and Wigderson, Theorem 1.1](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KLNSW93/paper.pdf)

Count each use of a wire, including both positions of a repeated operand.
Every nonsink wire has a consumer. For a trimmed binary circuit, the sum
of (outdegree minus one) over nonsink wires is 2g−(N+g−1)=r. Thus at
most r wires have multiple consumers. Fix the distinguished pair. Guess
one of the six monotone Boolean functions on two variables at every such
wire: zero, one, either projection, AND or OR. A shared primary input
other than a,b may only be guessed constant; a,b have their fixed
projections. Cut all outgoing uses of each shared wire and regard the
copies as leaves carrying its guessed function. Its defining computation
still has to produce that guess.

The uncut portions form disjoint trees. For unshared primary variables
other than a,b the possible signatures are zero and one. At an internal
gate combine the two sets of possible child signatures using its
operation. The Cartesian product is exact because their unguessed
primary assignments are disjoint. At the defining root of every guessed
gate reject the guess if the claimed signature is unattainable; use only
that signature on later wires. This preserves simultaneous feasibility:
the actual primary variables used to satisfy the separate defining
roots are disjoint. Record all signatures attainable at the output.
Each of the O(N²) pairs consumes O(g) work per guess, since a signature
set has at most six members. Backpointers recover the two assignments in
a rejection certificate.

On a successful instance one can also construct the optimal formula.
Connect a,b in an undirected graph exactly when their AND restriction is
attainable. In a read-once formula their lowest common ancestor is then
AND; an OR ancestor gives an OR restriction instead. Fixing the sibling
subtrees to neutral values proves attainability in both cases. At an
OR root this graph decomposes as a disjoint union; at an AND root its
complement decomposes as a disjoint union. Recurse on those components.
Merging equal operations only changes associativity. This construction
takes O(N³), within the stated bound for N≥2.

The essential-input promise is testable with the same cofactor sets. A variable is essential exactly when an attainable cofactor involving it actually depends on it. The criterion works even if the other distinguished input is inessential. On an arbitrary monotone circuit one can instead find all essential inputs and apply the read-once test on their support (returning constants and projections directly for support of size zero or one). This latter test uses the baseline of the actual support. If the number of nominal variables exceeds the number of essential variables, the original threshold N−1 can permit extra gates above that baseline. The Python reference stores explicit assignments as integers, so its bit complexity may incur polynomial factors beyond the backpointer algorithm.

If the input circuit uses arbitrary binary gates but is promised to compute
a monotone function, the same proof uses the sixteen possible two-bit
truth tables at intermediate wires and gives O(N²g·16^r).

## Exponential parameter dependence under sparse ETH

Use the explicit hypothesis that 3SAT instances with n variables and O(n)
clauses have no 2^{o(n)}-time algorithm. Any 2^{o(r)}poly(N)-time
recognizer in the preceding theorem would contradict this hypothesis.

For each Boolean variable use a pair of literal wires and include their
AND in the reference output. Add two new disjoint matching edges ab and
cd. The OR of all matching edges is a read-once reference F. Build the
monotone CNF Ψ of the original clauses on the literal wires, and supply

    F OR (a AND c AND Ψ).

On a consistent selection of literal wires, satisfying Ψ is equivalent to
the existence of an extending satisfying assignment. Hence an
unsatisfiable instance gives F itself. For a satisfying assignment set
exactly its selected literal wires to one. The remaining four-variable
function is ab OR cd OR ac, the edge function of a path on four
vertices. This function has no read-once formula over arbitrary two-input
gates. In a read-once root bipartition its communication table would have
at most two row types and two column types. Every one-versus-three split
has at least three functions of the one-bit side (zero, the bit, one).
For the splits ab|cd, ac|bd, ad|bc, respectively, three distinct row
types are (cd,c,1), (0,b,d), and (0,b OR c,c). Thus the original output
cannot be read-once. Every input remains essential, witnessed by its
own matching edge. The description and r have size O(n) on sparse
instances. Padding with disjoint fresh read-once branches can make the
supplied size at most N−1+N^α for any fixed α>0 while preserving the
read-once answer and O(n) excess.

Hardness of recognizing read-once functions from a matching predicate OR
a monotone CNF is due to Gurvich. Kozachinskiy also proves hardness for
a different depth-three read-twice representation. The reduction above
records the excess parameter and supplies an explicit four-variable
certificate in the satisfiable case. [Kozachinskiy, 2018](https://arxiv.org/abs/1802.03815)

## Related representation and parameter choices

Carmosino, Dang and Jackman study the simple-extension problem for a fixed function, including XOR over De Morgan and Red'kin gate-count conventions. Their algorithms use enumeration of optimal base circuits and structural conditions including bounded fanout. The result here takes as input a specific succinct monotone circuit and parameterizes by the number of gates that presentation uses above its connected-tree baseline. The single-point parity query construction here gives XOR a single binary gate for each pair it combines. [Carmosino, Dang and Jackman, STACS 2026](https://doi.org/10.4230/LIPIcs.STACS.2026.23)

Cavalar, de Rezende, Gray and Santhanam prove randomized-ETH lower bounds for PAC learning and for multiplicatively approximating the least monotone circuit size consistent with a labeled sample. Their hardness statements concern general samples or distributions. The sparse-ETH reduction above concerns exact semantic recognition from an explicit succinct circuit at a fixed threshold. The quantum and classical oracle bounds in this packet count membership queries for exact recognition and allow an arbitrary amount of computation between queries. [Cavalar et al., CCC 2026](https://doi.org/10.4230/LIPIcs.CCC.2026.40)

A given read-once reference H can be checked for exact equivalence to the supplied monotone circuit in the same parameterized time. If C is outside the read-once class, its two restrictions give six test points on which H cannot agree with C everywhere. If C is read-once, compare their essential supports and canonical alternating AND/OR trees, equivalently the recorded pairwise AND-ancestor graphs on the common support. This checks an arbitrary read-once reference without enumerating the possibly exponential number of its minterms and maximal false inputs.
