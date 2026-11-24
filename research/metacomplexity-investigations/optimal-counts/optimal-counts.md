# Counting optimum binary formulas and numbered gate programs

Let f depend on all N≥2 named inputs and have minimum arbitrary-binary circuit size N−1. Every such circuit is a binary tree with each input appearing once. Each gate can be any of the sixteen binary truth tables. We count operand positions as ordered, the input names as fixed, and the final output as the root. We give separate counts for ordered formula syntaxes and for topologically numbered straight-line programs. Both depend only on a decomposition that the parameterized algorithm in `algebraic.md` reconstructs.

## The canonical hierarchy

Write P for the multilinear interpolant of f over the rationals. At most one shift P−c for c∈{0,1,1/2} can factor across a nontrivial disjoint variable split. Suppose P−c admits a split into irreducible factors with disjoint variable groups. For i,j in different groups, its commutator is zero, while ∂ᵢⱼP is nonzero by the product rule. The commutator of P−d is therefore −(d−c)∂ᵢⱼP for every d≠c. Its commutator graph contains all edges between distinct original groups and is connected. Hence P−d has no nontrivial disjoint factorization. The shifts correspond, up to nonzero scalar factors, to the truth, falsehood and sign tensors in `algebraic.md`.

At each group take the finest irreducible factor supports of its unique splitting tensor. These are the children of a node of arity k≥2. Restricting all other factors to a nonzero Boolean base corner leaves a chosen factor, multiplied by a nonzero scalar. In the indicator cases the Boolean-normalized factor is independent of which nonzero base corner is used. In the sign case changing the base may complement the child function, which preserves its support hierarchy. Complement swaps the roles of truth and falsehood and multiplies the sign tensor by −1. Recursion therefore gives a unique hierarchy of named input sets up to complementing intermediate labels. The existence of canonical disjoint-support decompositions and their associative nodes is classical. Here uniqueness for the binary case follows directly from the shift calculation. [Damiani and Bertacco, The Disjunctive Decomposition of Logic Functions](https://web.eecs.umich.edu/~valeria/research/publications/IWLS97.pdf)

Every binary root partitions the finest factor supports into two nonempty unions. Every such partition is allowed by the factorization. Until only one factor remains on a side, its normalized tensor is a product of exactly the remaining irreducibles, with the same type of root (true product, false product or sign product). This proves that the possible binary trees are exactly the binary refinements of all canonical nodes. In `algebraic.py` the pairwise recursive recognizer always chooses normalized AND, OR, XOR or XNOR of literal cofactors. Contracting neighboring nodes of the same normalized family recovers the hierarchy. Separate arbitrary gate orientations are counted below.

## Ordered tree syntax and gate types

For an internal hierarchy node v let k_v be its arity. Its children carry distinct support sets. A binary refinement is an ordered binary tree on its k_v named children, admitting k_v!·Catalan(k_v−1) choices. These choices are independent across the hierarchy.

Once the refined ordered tree is fixed, every internal nonroot signal is determined up to complement. For example, the two row classes of the root's communication matrix are the only possible binary labels on that side up to exchange. The same statement applies recursively to either chosen side label; complementing it leaves its partition classes unchanged. One may flip any subset of the N−2 internal nonroot signals and conjugate the incident truth tables accordingly. These choices are all distinct since every such signal is nonconstant. Raw input leaves have fixed signals, and the root output is prescribed. Each local gate is then uniquely fixed by its input and output labels, since all four pairs of child values occur on their disjoint supports. The number of syntaxes is consequently

    2^(N−2) · ∏_v k_v! Catalan(k_v−1).

All optimum realizations contain the same number of XOR/XNOR gates, namely the sum of k_v−1 over the sign-product nodes. The other binary gates have one true or one false table entry, a property preserved under independent input/output complementation. The statement concerns optimal size N−1, including all complement orientations of optimal intermediate signals.

## Topologically numbered programs

A refined tree with fixed ordered syntax permits several gate-index assignments. The number of legal interleavings of its N−1 gates equals

    (N−1)! / ∏_u (n_u−1),

where the product is over its binary internal nodes and n_u counts primary leaves below u. This is the usual rooted-tree hook formula. For completeness, the root must be latest. Binomially interleaving the independently ordered gate sequences of its two children and applying induction gives exactly the displayed ratio.

For a canonical node with child input counts w₁,…,w_k, define H for a *labeled* multiset of weights W. Set H({w})=1 and, for at least two children, let

    H(W) = (1/(sum(W)−1)) · ∑_{∅≠S⊊W} H(S)H(W\S).

The sum ranges over labeled child subsets (equal weights from distinct children still count separately). It is precisely the sum over all ordered binary refinements of this canonical node of the reciprocal hooks contributed by its new internal nodes. Each hook depends only on the sum of the child weights below it, independently of the internal binary refinements of those child shapes. Thus the exact number of gate-indexed programs is

    2^(N−2) (N−1)! · ∏_v H(weights of the children of v).

Every numbered minimum circuit gives exactly one ordered syntax and one linear extension; conversely they recover the program by assigning successive gate indices. Shared inputs and ignored or dead gates cannot occur in a minimum N−1-gate circuit on N essential inputs.

Grouping equal weights gives a subexponential exact dynamic program in N after the hierarchy is known. If the multiset has m_w parts of size w, splitting a submultiset with a_w of them into the left branch contributes ∏_w binom(m_w,a_w) choices. Every submultiset is an integer partition of some t≤N. The total number of such partitions is exp(O(√N)): put x=exp(−1/√N) in the partition generating product; then log ∏_{j≥1}(1−x^j)^−1 = ∑_{k≥1} 1/[k(exp(k/√N)−1)] ≤ √N∑_{k≥1}1/k². Checking pairs of these submultisets preserves the same asymptotic bound. Every rational summand's denominator divides ((N−1)!)^(N−1) and the numbers of ordered refinements have O(N log N) bits, giving polynomial bit lengths. Ordered-tree syntax counts and XOR profiles take only polynomial work once the hierarchy is available. The displayed subexponential bound for numbered programs is an upper bound on this algorithm.

`syntax_check.py` directly enumerates every optimal ordered binary tree and gate-type assignment, independently chooses each successive pair of live signals and gate label for every numbered program, and compares both counts against the formulas for each represented Boolean function through four inputs. `optimal_syntax` and `optimal_programs` accept trees returned by `BinaryCircuit.recognize`.
