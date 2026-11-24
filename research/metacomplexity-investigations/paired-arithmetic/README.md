# Arithmetic circuit minimization at its first possible gate count

For a formal polynomial involving every one of N variables, the minimum possible size of a binary straight-line program that counts its leaves is 2N−1. This note characterizes that first gate count exactly for binary set-multilinear 0/1 polynomials. It also gives a succinct representation on which the floor is coNP-complete to distinguish from a superpolynomial bound, even when the coefficient predicate is an intersection of three read-once CNFs.

## 1. The exact recognition theorem

There are d designated pairs of variables, N=2d and d≥1. A solution family A⊆{0,1}ᵈ specifies the formal polynomial

    F_A(X) = ∑_{a∈A} ∏_{i=1}^d X_{i,a_i}.

Assume every one of the N variables occurs. Distinct assignments contribute distinct monomials with unit coefficient, over any field. Fix a∈A, put B={u XOR a : u∈A}, and identify the vectors in B with subsets of [d].

**Theorem 1.** The following are equivalent over every field.

1. F_A is computable by 2N−1 gates counting variable and scalar leaves.
2. F_A is coefficientwise approximable by the same number of gates with constants from the formal Laurent-series field.
3. B is closed under complement and intersection.
4. Some partition of [d] has B as its family of all unions of blocks.

In particular, the recognized class does not depend on the chosen reference assignment. On the promise of full variable dependence, the theorem gives membership in coNP when the membership predicate for A is given by a Boolean circuit or CNF. A negative certificate contains an accepted reference assignment and one or two accepted assignments whose normalized complement or intersection maps to a rejected assignment.

**Gate budget.** In the cone of the chosen output let there be l leaves and b binary gates. Every node except the output is read at least once, so l+b−1≤2b, counting repeated operands with multiplicity. Every essential variable has a separate variable leaf. Thus total size ≥l+b≥2N−1. A variable that occurs in a paired monomial is essential in every characteristic: set all coordinates incompatible with that fixed assignment to zero and set its selected coordinates to one; zeroing its selected variable changes the result from one to zero. This also shows why cancellation cannot conceal a variable here.

At equality there are exactly N leaves and N−1 binary gates. Every variable appears once, there are no constants or unused gates, and every nonoutput node has exactly one reader. The computation is a read-once binary tree on the raw variables. These conclusions apply to Laurent approximation too. A variable absent from the Laurent circuit is absent from its coefficientwise residue. Essentiality of the target therefore forces N distinct variable leaves in that circuit. With no scalar leaves left, the tree computes a polynomial over the prime subfield, constant in the Laurent parameter. Its residue equals that same polynomial.

**Support at equality.** A constant-free read-once tree has only coefficients zero and one. Its two children use disjoint variables. At an addition their monomials are nonempty and have disjoint variable supports, so no monomial is duplicated. At a multiplication every result has a unique decomposition into the two child monomials. This induction applies unchanged in all characteristics.

At an addition root, each summand contributes degree-d monomials, and therefore needs at least d variables. There are 2d variables in total and the children use disjoint variable sets. Each child has exactly d variables and contributes just the product of all of them. The two resulting supports are complementary choices, one per pair. At a multiplication root both variables of each pair lie on the same side. Otherwise choose from each child a monomial containing its variable from that pair. Their product illegally contains both. This argument uses full variable dependence. Consequently the root splits whole pairs, and each factor is a fully variable-dependent one-per-pair polynomial on its group. Induction on the tree shows that F_A is a product of factors of the form

    ( ∏_{i∈C} X_{i,a_i} + ∏_{i∈C} X_{i,1−a_i} ),

over a partition into nonempty classes C. Each factor permits a uniform flip of one block relative to a. Conversely expanding this expression gives exactly all unions of the blocks, with unit coefficients and 2N−1 gates (a full binary tree on N distinct leaves).

**Finite set algebra.** Since ∅∈B, closure under intersections and complements also gives the whole ground set and finite unions. Declare i∼j if every member of B gives them the same membership bit. For each i its equivalence class belongs to B: take the complement of the union of all sets in B omitting i. Complement closure makes this precisely the equivalence class. Every member is a union of classes, and every such union belongs to B. This proves the remaining equivalence. The finite classification and two read-once support arguments are checked separately in Lean.

## 2. Hardness, with three clause layers and all coordinates essential

**Theorem 2.** For each fixed field there is κ>0 such that the following promise distinction is coNP-complete under deterministic polynomial-time reductions. The input is a 3-CNF on N exponent bits with a fixed partition into pairs and a known accepting assignment. Every accepted exponent has exactly one bit from every pair; every exponent variable is essential in the enumerator. The YES side has exact and Laurent gate size exactly 2N−1. On the NO side each size exceeds exp(κ(log N)^(4/3)). The same holds under the following simultaneous syntactic restrictions.

* Every variable occurs exactly three times, once in each of three supplied read-once clause layers, in both polarities overall.
* Each of the first two layers is a perfect matching of binary clauses. In the third, the disjoint clauses, all of width two or three, partition the variables. All underlying variables in a clause are distinct.
* The constructed examples have a publicly known complementary pair of accepting assignments, the only such pair. All their model monomials have the same degree N/2. The coNP upper bound from Theorem 1 requires only the full-essential, paired support and one known assignment.

The reduction uses the all-field Hamiltonian-cycle lower bound published at the pinned upstream revision. The theorem there is about formal division-free exact and Laurent-series programs. A coefficient-oracle formula is simply a representation of the input instance in this reduction. [Upstream statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean) · [Solution](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Solution.lean) · [Official verification](https://github.com/anthropics/formal-math/actions/runs/45272623486/job/138036167794)

### A Boolean verifier with one baseline

Given a source 3-CNF ψ and a tour order m, use a branch flag b, two SAT rails per witness bit, and m² directed edge bits. Accept either b=1 with all other primary bits zero, or b=0 with exactly one high rail per bit, a satisfying assignment of ψ and a valid Hamiltonian tour. The tour tester uses O(m³) binary gates: enforce one incoming and outgoing edge at each vertex and iterate bounded reachability from vertex zero for m−1 steps. The Boolean computation is deterministic. For each accepting primary assignment there is exactly one full wire assignment.

### Two antipodal baselines, with no other antipodal pair

Add a phase bit r. Store every old logical bit u as the physical bit u XOR r. Absolute negation still implements signed logical negation. Relative AND of absolute inputs x,y has physical output MAJ(x,y,r); relative OR has physical output MAJ(x,y,¬r). A majority equation z=MAJ(x,y,t) uses six three-literal clauses without auxiliary wires. For each of the three input pairs (i,j), include (¬i∨¬j∨z) and (i∨j∨¬z). Impose that the absolute output differs from r, so the logical output was accepting, and impose the extra clause (¬r∨¬b_abs).

In phase zero, precisely the original accepting computations occur. In phase one, the extra clause requires the old logical baseline flag to be one, so there is just the complementary copy of the original baseline. This gives exactly one pair of complementary complete assignments. Any extra witness/tour assignment has (r,b_abs)=(0,0), and its complement with (1,1) violates the extra clause.

### Exact-three balanced occurrences and homogeneous support

It is useful to give the full construction on an arbitrary CNF of width at most three with nonempty clauses. If it contains a unit ℓ, write it twice within the same clause (ℓ∨ℓ); expansion into physical occurrences below gives distinct variables. An old variable that never appears can be used in a harmless clause (v∨¬v). Duplicate every payload clause once.

For each resulting literal *position*, introduce two physical variables x_j,y_j. The old literal uses x_j with its original sign. For each old variable arrange all of its positions in a directed cycle with successor τ. In the first layer put (¬x_j∨¬y_j) for every j. In the second put (y_j∨x_{τ(j)}) for every j. Both layers are perfect matchings. If x_j=1 then y_j=0 and x_{τ(j)}=1. Around the finite cycle, the x_j are constant. If they are zero, the second clauses force the y_j to be one; if they are one, the first clauses force all y_j to be zero. Thus y_j=1−x_j, including the zero case, and every old assignment extends uniquely.

The third layer contains the duplicated payload clauses on their independent x_j positions. Pair the mates y_j,y_{j′} for two corresponding positions from the two copies of an old clause. Include (y_j∨¬y_{j′}). These two bits are equal by cycle consistency, so this clause adds no semantic restriction. Every physical coordinate now occurs exactly once per layer and once in each polarity among its two cycle links. Each old assignment has one physical extension; complementing all old assignments' bits complements their physical extensions. Every solution selects exactly one element from each pair, yielding a set-multilinear formal polynomial.

When ψ is unsatisfiable the only physical assignments are the two complementary baselines. Their monomials are disjoint and the sum costs exactly 2N−1. When ψ is satisfiable, choose a satisfying α. Send a distinguished positive x_j for r and for b_abs to zero. This deletes both baselines. Send an x_j for the wrong SAT rail of each bit to zero and for the right rail to one. For each primary edge send one distinguished x_j to the corresponding tour variable, and send every other coordinate, including all y_j, to one. Precisely one extension of each tour under witness α survives. Thus the formal polynomial projects to HC_m with coefficient exactly one over every field. Applying a 0/1/variable projection preserves the exact number of gates in exact and Laurent programs. For Laurent coefficients, the finitely many source coefficients contributing to any projected coefficient are regular, and taking their residues commutes with finite summation. This gives the stated NO bound.

There is also a direct witness of failure of floor size on each reduced NO instance. A Boolean subalgebra with at least three elements contains at least two complementary pairs. Here the two baselines form the only complementary pair and there is a third model precisely when ψ is satisfiable. This argument proves strictness above the floor independently of the quantitative upstream bound.

### Linear size and a time lower bound

Let L count variables plus literal occurrences in the source. Choose m as the larger of the fixed characteristic threshold and the ceiling of L^(1/3), increased to two if needed. The verifier has O(L+m³) gates, and every remaining construction has constant cost per old gate or literal occurrence. The final number of exponent variables and total literal positions are O(L) for large L, while m≥Ω(N^(1/3)). The upstream m^(c(log₂m)^(1/3)) lower bound therefore gives the claimed rate in N. The per-characteristic finite threshold may be hardwired in the reduction. Encoding occurrence indices in bits costs only a logarithmic factor and does not change the variable-count parameter.

Under the Exponential Time Hypothesis this promise distinction admits no time 2^o(N)·poly(input length) algorithm. By the 3-SAT sparsification lemma it suffices to reduce formulas with O(n) clauses for each fixed sparsification constant. The construction gives O(n) exponent bits and total literal positions on those instances. This is a fine-grained reduction for the succinct coefficient presentation. [Impagliazzo, Paturi and Zane, Which Problems Have Strongly Exponential Complexity?](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturiZane_2001_jcss.pdf)

### Sharp tractable neighbors of the three-layer theorem

The same floor question is in deterministic polynomial time on either of two broader neighboring inputs: clause width at most two with arbitrary occurrence, or at most two occurrences per variable with arbitrary clause width. The paired-support and full-dependence promises still apply. A satisfying baseline may be supplied or found by standard SAT self-reduction in either case.

To check complement closure, a complement violates a clause C iff its original vector makes every individual literal of C true. Pin those values and test satisfiability. To check normalized intersection closure, use two independent assignments x,y. Their resulting raw exponent bit at position j is x_j AND y_j at a zero baseline bit, and x_j OR y_j at a one baseline bit. This agrees with paired normalization on the positive and negative coordinates of every pair. Guess a clause C that the resulting assignment violates. Making one of C's literals false imposes either two single-coordinate pins or one binary clause relating x_j and y_j. At width two the two source copies together with these tests still give 2-SAT.

For occurrence two and arbitrary width, first remove C from both copies. Enumerate one literal witnessing C in x and another witnessing C in y; enforce them by fixing their variables and simplifying the formula, with O(|C|²) choices. For each literal of C impose the above pins or linking clause. Each occurrence removed from either copy has been replaced with at most one occurrence in that copy, and simplification at a pin never increases occurrences. The resulting arbitrary-width residual formula therefore still has occurrence at most two and can be solved by eliminating pure variables or resolving the unique positive/negative pair. A successful residual checks a closure violation. This gives the algorithm in read_two_floor.py. It recognizes Boolean-subalgebra closure of a normalized read-two CNF even without a set-multilinear promise; the promise supplies its connection to the arithmetic first gate count.

## 3. Representation and previous work

The measured object is an arithmetic circuit for the enumerator. Its input presentation is a Boolean predicate for an exponent. A three-layer read-once *coefficient predicate* does not itself give an arithmetic read-once expression for that enumerator. Dense algebraic-MCSP, Boolean MCSP, and arithmetic circuit minimization with an arithmetic input circuit use different input representations. These results do not establish Boolean P≠NP.

Briquel and Koiran study this assignment-monomial enumerator and identify which constraint languages support VNP-hard families. Tovey established the bounded-occurrence decision-SAT thresholds; the companion packet explains why width two or maximum occurrence two makes its one-hot uniqueness gap easy. Shpilka and Volkovich address arithmetic read-once testing and reconstruction, with different allowed leaves and arithmetic evaluation access. The exact first counted gate budget on binary set-multilinear supports and the bundled three-layer gap are the statements investigated here. Priority for this combination has not been established. [Briquel and Koiran](https://arxiv.org/abs/0902.2300) · [Tovey](https://doi.org/10.1016/0166-218X(84)90081-7) · [Shpilka and Volkovich](https://www.theoryofcomputing.org/articles/v010a018/)

A simple access-model distinction also follows from Theorem 1. Given a positive floor promise and a SAT oracle, one can reconstruct a minimum tree: query a model separating each pair of normalized coordinates, group equal profiles, and use the displayed block formula. With only individual coefficient queries and a known baseline, exact reconstruction can require exponentially many queries even when *both* choices are floor instances. A one-block family has just the two baseline assignments. A two-block family adds the two complementary indicators of an unknown nontrivial bipartition. On a uniform hidden unordered bipartition, a fixed other query hits these additional assignments with probability 2/(2ᵈ−2). Coupling the one-block query transcript to the two-block instance gives Ω(2ᵈ) queries at constant error; the table has 2ᵈ possible paired coefficients. This lower bound concerns coefficient queries and leaves arithmetic evaluation algorithms outside its model.


## 4. Reproduction and audit scope

The unchanged text files of the foundation are under `foundation/AlgebraicMetacomplexity/`. Their original archive SHA-256 is `e78233bf3a29c971ed5f20d9d9f3176f528380b3e6b433ed9d5273ce52ea7fca`; its independent clean replay passed. The supplementary reproducible archive with that ZIP embedded has SHA-256 `62325ce3279e6d26cb9a345cdef8f013b257160bb080c8b9da565d1cddb09e84`. This editable tree replaces ZIP extraction with direct source reads. The driver first verifies both SHA-256 manifests and then rebuilds the required files into a new temporary object directory without network access. From an installed Lean 4.36.0 and built Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, run

```sh
MATHLIB_ROOT=/absolute/path/to/mathlib4 sh check-package.sh
```

The controls use only the Python standard library. The complete physical truth tables for five example compiler outputs check 131,840 rows, including all inconsistent duplicate assignments. Larger planted tests check the literal projection and each layer's occurrence/width specification. The phase controls confirm both complementary baselines, the absence of other antipodal pairs, and the correct Hamiltonian coefficient at both satisfiable and unsatisfiable examples. A separate finite test enumerates every constant-free read-once arithmetic support on up to six individual variables. The recognition test compares the closure criterion with all 63,775 full-essential four-pair support families (49 floor families), and independently enumerates tree expressions through three pairs. The read-two test compares the polynomial-time procedure with exhaustive truth tables at 13,246 satisfying baselines.

The following independently kernel-checked Lean modules have exact audit output in `checks/lean-axioms.txt`.

| Module | Checked assertions |
|---|---|
| IncidenceCompiler | An actual sign-labeled clause/variable incidence transformation preserves the entire model set bijectively, gives maximum occurrence three, preserves all payload clause widths and adds binary linking clauses. This is the general signed-cycle compiler from the companion work, with one reserved coordinate per old variable. |
| PairedLayers | Both cycle-matching layers force exactly one member of each pair and a common primary bit throughout each permutation cycle. Every selected variable is semantically essential in the paired polynomial, over any nontrivial commutative semiring. |
| PhaseCircuit | Six three-literal clauses simulate a majority gate; a full gate sequence with phase r checks exactly the original circuit under XOR decoding. The flag condition pinpoints when complements may coexist. |
| GateLeaves | Every semantically essential variable has a variable leaf in the root cone of any acyclic binary arithmetic DAG, and d essential variables require at least 2d−1 counted gates. |
| TightCone | At the exact floor, every gate is live, every leaf is one of the essential variables, the output is unread and each other wire has exactly one consumer slot. This is the DAG-to-read-once step. |
| AntipodalFloor | A homogeneous top sum on two disjoint groups of total size 2d can have only its two group monomials. Closure of a genuine two-sided product under recombination creates a second antipodal pair. |
| BooleanBlocks | A finite collection closed under Boolean algebra operations consists exactly of unions of its coordinate equivalence blocks. |

The complete coNP and ETH reductions and their asymptotic consequences are mathematical arguments, supported by the original executable encoders and finite computations. The generic kernel lemmas certify their named components; they do not constitute a full Lean formalization of the complete complexity-theoretic statements or ETH. No external project build was run on the host. The proof of the Hamiltonian lower bound is from the official published verification, separately reviewed as described in the foundation packet.

A [clause-width counting bound](ClauseWidthBoundary.md) shows that any fully paired support with an antipodal pair and maximum occurrence three requires at least 3N/4 binary clauses if all other clauses have width three on distinct variables.
