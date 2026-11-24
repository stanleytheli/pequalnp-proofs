# A singly exponential exact algorithm for arbitrary binary circuits

Let C be a physically trimmed N-input circuit with g binary gates computing an arbitrary Boolean function f depending on all N≥2 inputs. Each gate may have any binary truth table. Let b count all distinct shared producers, including gates and primary inputs read more than once. There is a deterministic algorithm using

    O(N² (N+g) 16^b)

integer arithmetic operations to decide whether f has circuit size N−1 over the full binary basis, returning an optimal circuit when it does. All intermediate integers have O(N+g) bits. The same recognition problem takes 2^O(w) poly(N+g) bit time given a width-w decomposition of the physical wire graph. The reduction in `recognition.md` rules out a 2^o(b) poly(N+g) algorithm under sparse ETH. The controls and executable `algebraic.py` implement the shared-producer version. The decision threshold is the least possible gate count for N essential inputs. The theorem does not require monotonicity or algebraic gate semantics.

## Which splits could be binary roots?

For any restriction h, consider the three real functions T=h, T=1−h, and T=1−2h. Each is a tensor with a binary index for each remaining input. Its multilinear interpolation P is the unique polynomial affine in each variable with Boolean-corner values T. A nontrivial product split of any of these three interpolants derives from, and gives, an arbitrary binary gate root on its variable blocks.

Specifically, an essential Boolean gate has one true entry, one false entry, or two true entries on a diagonal of its 2×2 table. In the first case its truth indicator is the product of two Boolean functions, possibly complementing either input. In the second case its false indicator is such a product. In the diagonal case its sign (1−2h) is the product of two signs up to an overall minus sign. A factorization on Boolean inputs that uses disjoint variable groups extends to the multilinear interpolation by uniqueness.

Conversely suppose P factors across nonempty groups A,B. Pick a Boolean corner (a₀,b₀) with P(a₀,b₀) nonzero. Such a point exists for every nonzero multilinear polynomial. Then on all corners,

    P(a,b) = P(a,b₀) P(a₀,b) / P(a₀,b₀).

For T=h or 1−h choose a corner where the indicator is one. The original h is respectively AND or OR of the children h(·,b₀) and h(a₀,·). For T=1−2h any corner works, and h is XOR or XNOR of these same children, with the extra constant h(a₀,b₀). Because all variables are essential, these two child restrictions depend on every variable on their own sides. Restricting a read-once function always leaves a read-once function up to simplifying unary and constant gates. Hence any valid split can be used recursively. Conversely, a completed recursion certifies a read-once formula. At unary leaves a sign is absorbed into the parent's binary table, giving exactly N−1 gates.

## Commutators locate variable blocks

For i≠j denote the four polynomials P with its i,j coordinates set to a,b by P_ab. Define

    Δ_ij = P_00 P_11 − P_01 P_10.

This commutator and its relation to multiplicative separation of a multilinear polynomial are classical. Here is a direct proof of the exact criterion used. Factor P in the unique factorization domain Q[x₁,…,x_N]. Since degrees in each variable add under multiplication and P is multilinear, the nonconstant irreducible factors have disjoint variable supports and occur once. Writing P locally as A+B x_i+C x_j+D x_i x_j gives Δ_ij=AD−BC=P·∂_ij P−(∂_i P)(∂_j P). If i and j occur in different factors, this expression vanishes by the product rule. If they occur in the same irreducible Q, put R=P/Q. Modulo Q the expression is −(∂_i Q)(∂_j Q)R², nonzero since Q is prime, is coprime to R, and does not divide either nonzero derivative of lower degree. Thus the graph joining nonzero commutator pairs consists of disjoint cliques, one per irreducible support. An anchor input compared with every other input therefore finds its entire factor block with at most N−1 identity tests. At least two blocks give a valid split. [Shpilka and Volkovich, On Reconstruction and Testing of Read-Once Formulas, §2.2](https://theoryofcomputing.org/articles/v010a018/)

## A deterministic four-copy identity test

The commutator has degree at most two in each unfixed coordinate. It vanishes identically exactly when

    S_ij = ∑_{z∈{0,1,2}^(N−2)} Δ_ij(z)² = 0.

Three evaluations per coordinate suffice by univariate interpolation and induction, and the summands are nonnegative. The algorithm computes this integer without enumerating the ternary grid. Expand the square into P_00²P_11² + P_01²P_10² − 2P_00P_11P_01P_10. Each summand uses four polynomial evaluations on the same background z, with possibly different fixed values of i,j.

Expand each interpolant evaluation in the Boolean Lagrange basis. For each of the four copies independently, a Boolean input bit x contributes z if x=1 and 1−z if x=0. For any background coordinate, let k be the number of ones among its four Boolean copies. Summing that coordinate of z out now contributes the local factor

    w(k)=∑_{a=0,1,2} a^k (1−a)^(4−k) = 2, −2, 4, −8, 17   for k=0,…,4.

Fix the four i and j bits individually as that summand specifies. A pin from an earlier recursive call fixes all four copies of its input to the prescribed bit. At each physical gate, the 4-bit output word is obtained by applying its original Boolean truth table in each position. At the output multiply the four values of T. Thus each of the three summands is an exact signed count of four simultaneous evaluations on the same physical circuit with local input weights. The support of the circuit is unchanged. In particular one must use Boolean interpolation for C's output; composing arithmetizations of shared gates can give a polynomial that is not multilinear.

For the shared-producer bound, guess the 4-bit word of every shared producer in at most 16^b ways. At a primary input store its local weight for each possible word. At each gate form its output table by multiplying child weights, summing over input pairs giving that output word. At a guessed producer multiply the running factor by the weight of its guessed word and pass a point mass of weight one at that word to all later readers. This evaluates each defining tree exactly once. The primary variables still to be summed in different child subtrees are disjoint, so the products are valid even for signed weights. A repeated operand automatically belongs to a shared producer and incurs its defining weight once. Finally sum the output table with its output factor, multiply by the running factor, and sum over guesses. The 16 states make each gate calculation constant-cost per guess. Intermediate table entries and factors are bounded by weighted sums over at most four copies of each input, with local factors bounded by 17; their bit lengths are O(N+g). Subtractions take place only in exact integer arithmetic.

For the treewidth version, take any width-w tree decomposition of the physical undirected wire graph and enlarge each bag by the two operands of every gate it contains. Every wire's bag set stays connected, since the subtree for each reader already touches that wire's old bag subtree. The width becomes at most 3(w+1)−1. Assign each gate constraint, input weight, and output factor to any one bag containing its scope. Sum-product dynamic programming over the bag interfaces computes the same signed sum in 16^O(w) polynomial time. No assumption is made about the treewidth of an unknown optimal realization.

The normalizing Boolean corner can be found in O(2^b(N+g)) using the one-copy version of the guessed-producer algorithm with witness backpointers instead of signed counting. For a sign tensor one can use the all-zero free corner. On recursion retain the original program and pin the opposite block to the chosen corner. There are at most 2N−1 nodes in the recovered tree, and at most three (|U|−1) anchor comparisons at a node with active set U. This proves the stated total time. `algebraic_check.py` compares the signed counts to direct ternary-grid interpolation and reconstructs formulas on arbitrary binary presentations.

`TensorContraction.lean` proves the arbitrary finite product–sum identity used to contract simultaneous evaluations, the actual four-copy integer weights, and exact interpolation of a product of two Boolean multilinear tensors from ternary-grid values. In particular a zero rational sum of squared differences on that grid implies equality of the products at all rational points. The graph factorization, shared-producer dynamic program, runtime argument and formula reconstruction have written proofs and executable checks.
