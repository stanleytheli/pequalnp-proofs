# A circuit-size gap and exact tests for proposed hardness projections

This note gives polynomial-time reductions for multilinear formal polynomials specified by a bounded-occurrence 3-CNF on their exponent bits. One reduction gives a one-gate versus superpolynomial-size promise problem. Three others classify a proposed transfer of the Hamiltonian-cycle lower bound. The input representation, the signs permitted in a transfer, and the field characteristic matter.

## 1. Model and results

For a Boolean formula Φ on N bits, let PΦ(X) be the sum over its satisfying assignments a of the squarefree monomial ∏_{j:a_j=1} X_j. A coefficient is zero or one in every field. A 3-CNF here has clauses of width **at most** three. An occurrence counts a literal position, including either polarity. The formulas constructed below have at most three occurrences of each exponent bit. They may have binary clauses.

A size is a nonuniform, division-free, fan-in-two algebraic straight-line program over formal polynomials. A variable or scalar leaf counts as one gate. The approximation variant permits constants in the formal Laurent-series field F((ε)) and requires each polynomial coefficient to be regular with the specified constant term. These conventions are those of the pinned formal statement cited below. The target HC_m is the sum of the distinct permutation monomials corresponding to directed cycles visiting all m vertices once, with m≥2. It has (m−1)! monomials, all with coefficient one. Distinct rotations of one cycle yield the same permutation and are counted once.

| Decision | Encoding and field | Complexity under deterministic polynomial-time many-one reductions |
|---|---|---|
| One gate versus both exact and Laurent size greater than exp(κ(log N)^(4/3)) | Three-occurrence 3-CNF, known one-hot satisfying exponent, any fixed field | Promise-coNP-complete, using the pinned HC bound |
| Does a displayed signed projection send PΦ to HC_m? | Images are 0, 1, −1 or variables, characteristic zero | C₌P-complete, already for m=2 |
| Does a displayed unsigned projection send PΦ to HC_m? | Images are 0, 1 or variables, characteristic zero, variable m | Complete for ∀·US, defined by “for every index there is exactly one witness” |
| Same transfer identity, signed or unsigned | Any fixed prime characteristic p, variable m | coNP^ModₚP-complete, already with unsigned projections |

A separate oracle corollary in section 5 quantifies how many entries of a dense coefficient slice a verifier must inspect when its only access to the input is entry queries. The complexity classifications in the last three rows are independent of the circuit lower bound. Each acquires an additional interpretation as verification of a proposed lower-bound proof after applying that theorem.

## 2. A public one-hot baseline and a large gap

Fix a field F. Assume the formal theorem that there is c>0 such that, for all m beyond a threshold depending only on the characteristic, HC_m requires more than m^(c(log₂m)^(1/3)) gates in each of the exact and Laurent models. The published nonuniform result provides this theorem over every field. The encoding below gives a promise-coNP-complete gap for some absolute κ>0. The finite initial threshold can be hardwired for each fixed characteristic. Finite input sizes can be excluded from the promise or mapped to fixed instances by finite lookup. [Formal statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean) · [Solution](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Solution.lean) · [Upstream verification job](https://github.com/anthropics/formal-math/actions/runs/45272623486/job/138036167794)

Given a 3-CNF ψ of encoding length L, choose m equal to the larger of L+2 and a sufficiently large fixed characteristic threshold. Use a branch bit b, a positive and a negative rail for each variable of ψ, and m² primary edge bits. A deterministic Boolean circuit accepts in either of two cases.

1. The branch bit is one and every other primary bit is zero.
2. The branch bit is zero, exactly one rail per pair is high, the positive rails satisfy ψ, and the edge bits describe one directed Hamiltonian cycle on m vertices.

The cycle test checks the row and column sums of the edge mask are one and every vertex is reachable from vertex zero. Pairwise exclusion within each row or column and m−1 rounds of propagation from vertex zero give O(m³) binary gates. Polynomial size is sufficient here. The program in this packet implements this deterministic test, so its auxiliary variables describe a single extension for each choice of primary bits.

For each binary gate introduce its output bit and the three Tseitin clauses for equivalence to that gate, using signed inputs to represent negations. Require the final output bit to be true. Each assignment of primary bits has exactly one extension satisfying the gate definitions, and this extension satisfies the forcing unit clause precisely when the circuit accepts.

To bound occurrences, replace every old literal occurrence with a fresh physical bit. For every old bit, arrange its copies in a cycle and write the binary implication from each copy to the next. A cycle of length one needs no additional clause. These implications permit exactly the constant logical assignments to the copies. Each copy appears in one old clause and in at most two new clauses. This operation is parsimonious. An unused primary bit, if required by a general encoding, can be included using a tautological clause. The two reductions in the executable use every declared primary bit.

The accepting baseline assignment in case 1 can be computed by evaluating the Boolean circuit. At the physical CNF coordinates, complement every bit whose baseline value is one, except for one distinguished representative of the branch bit. Flip its literal polarities everywhere it occurs whenever a coordinate is complemented. The known solution now has precisely one high bit. The ordinary logical baseline of the witnesses and edge bits is all zero, hence those representatives have their original polarity.

If ψ is unsatisfiable, the unique satisfying exponent of Φ is the known baseline e★. Thus PΦ=X★, which costs exactly one gate. If ψ has a witness α, use this displayed literal projection:

* Send the distinguished branch bit to zero.
* For each witness rail, send its distinguished representative to one if that rail matches α and to zero otherwise.
* Send one distinguished representative of each edge bit to its target variable X_ij.
* Send every other physical coordinate to one.

The first line removes the baseline monomial, while α's rails remove every other witness. For each tour there is exactly one remaining CNF solution. Its monomial projects to precisely that tour's monomial. Thus PΦ projects to HC_m with coefficient one over every field, including characteristic two. The second rail per witness is essential to reject either incorrect bit value using multiplication by zero.

Literal projections do not increase a program's size. Replace each original input leaf with the designated input or scalar. For a Laurent program, the coefficient of each resulting monomial is a finite field-linear combination of source coefficients and taking the constant term commutes with this substitution on the regular coefficients. The exact and border lower bounds consequently both transfer. The occurrence transformation introduces O(m³+L) physical variables for this circuit, so log m ≥ c₁ log N for large m and a uniform constant c₁>0. This gives the displayed threshold with a suitably reduced κ.

The promise problem designates the one-gate case as YES, large in both models as NO, and stipulates a displayed known one-hot satisfying exponent. On promised inputs a second satisfying exponent certifies NO, and every NO has one. A size-one exact program in the presence of this baseline must be X★. The same holds for a size-one Laurent program because its output can only be a single variable or a scalar series. Further syntactic baseline checks take deterministic polynomial time. The reduction is from UNSAT. For a general promise-coNP problem use its coNP separator before this reduction. Any collection of polynomial-length YES certificates verifiable in deterministic polynomial time on all promised instances would imply NP=coNP. The simpler exact identity test PΦ=X★ is coNP-complete without the upstream lower bound.

### Exact restrictions at the tractability boundary

For a promised one-hot baseline, both exact and border questions have their small side exactly when the given assignment is unique. This characterization also gives polynomial algorithms for two nearby restrictions.

* With clause width at most two and unrestricted occurrence, solve the N conditioned 2-SAT instances obtained by requiring one coordinate to differ from the baseline. A second assignment exists iff at least one conditioned instance is satisfiable.
* With at most two occurrences of each variable and arbitrary clause width, conditioning preserves the occurrence bound. For satisfiability eliminate a variable of one polarity by setting it to satisfy all its occurrences. For a variable used once positively and once negatively in distinct clauses, replace the two clauses by their single resolvent. The old variable can be filled consistently iff the resolvent is satisfied. Remove tautologies and duplicate literals first. No other variable gains occurrences and the total number of literal positions strictly decreases. This is a polynomial-time algorithm, also after every conditioning.

Thus increasing each of these bounds from two to three really matters to this promise reduction. There is a second sharp syntax caveat. Suppose every clause has exactly three distinct underlying variables, each variable occurs at most three times, and there is at least one variable. Such a formula cannot have a unique solution. At a putatively unique assignment, flipping any single bit must break some clause. That clause has just one true literal at the assignment, on the flipped variable, so clauses assigned to different variables are distinct. There are at least N clauses. Counting positions gives at most N clauses; hence every clause has exactly one true literal. Complementing every bit now satisfies each clause at its other two literals, a contradiction. In particular replacing the binary implication clauses by exact-three padding without relaxing occurrences or the one-gate baseline would be unsound.

## 3. Testing a supplied transfer

A transfer instance gives a 3-CNF, the image of each exponent variable (a target variable or an allowed scalar), and target order m specified in unary or with its m² variables explicit. Its question is equality as *formal polynomials*. No guessed arithmetic circuit or bound is part of this test. All reductions below use the same parsimonious functional and occurrence transformations. When the baseline is unnecessary, no polarity changes are needed. Map only one representative of each primary projected bit to its specified image and all duplicate/depth wires to one, preserving the intended weighting.

### Signed images, characteristic zero

For C₌P hardness, take two Boolean 3-CNFs α and β. Construct three disjoint tagged branches for a valid m-cycle mask, a satisfying α-assignment, and a satisfying β-assignment. The first branch accepts every m-cycle exactly once. Each branch sets the other branches' input payloads to zero so their unused bits introduce no multiplicities. All branches deterministically extend to gate and copy coordinates. Retain variables for directed edges, assign −1 to the distinguished β-branch tag, and assign one to the remaining coordinates. The result is
$$\mathrm{HC}_m + (\#\mathrm{SAT}(\alpha)-\#\mathrm{SAT}(\beta)).$$
The identity holds iff the two counts coincide. One may set m=2 throughout. The complexity input is the counting instance, independently of the number of target variables. Equality of two #SAT counts is C₌P-complete by the definition using differences of #P functions and a parsimonious tableau circuit encoding.

For membership, for each canonically encoded target exponent a, let D(a) be its projected signed coefficient minus its HC coefficient. D is GapP. Guess a source assignment, test satisfaction, discard magnitudes killed by a zero leaf, check that its projected exponent is a, and count with the parity sign of its selected negative leaves. Subtract the deterministically computable target coefficient. The target exponents have polynomial-bit encodings since each coordinate is ≤max(N,1), where N counts source exponent bits, and m² is polynomially bounded. Assign zero to unused encodings. The integer G=∑ₐD(a)² is GapP by closure under products and exponentially many polynomially indexed sums. Equality is equivalent to G=0 in the integers. Every fixed characteristic-zero field embeds these integer coefficients faithfully. Polynomially short deterministic certificates for all affirmative transfer claims would give C₌P⊆NP and therefore NP=coNP. [Fenner, Fortnow and Kurtz, Gap-Definable Counting Classes](https://newtraell.cs.uchicago.edu/research/publications/techreports/TR-91-30)

### Unsigned images, characteristic zero

Define ∀·US as the languages with a polynomial-time Boolean relation R and polynomial length bounds such that membership means **for every bitstring u there is exactly one bitstring v with R(x,u,v)**. The exactly-one class US permits zero or multiple witnesses on a negative instance. This definition specifies the class even where naming conventions vary. [Blass and Gurevich, On the Unique Satisfiability Problem](https://web.eecs.umich.edu/~gurevich/Opera/42.pdf)

For a projected coefficient at a, count the satisfying assignments with projected exponent a and nonzero scalar product. With 0,1 weights, this is the exact nonnegative integer coefficient. Append a single fresh distinguished dummy witness when HC(a)=0. This new relation has exactly one witness for every a precisely when all the coefficients agree. Invalid encodings have just the dummy witness.

Conversely, choose m≥2|u|+1 and designate disjoint pairs of vertices other than vertex zero. Traverse a tour from zero and read whether each pair occurs in its prescribed relative order. This deterministic tour index attains every bitstring: concatenate the vertex pairs in fixed pair order, reversing individual pairs as needed, close the cycle via any unused vertices. A deterministic Boolean circuit verifies a valid tour T, computes its index t(T), and accepts witness v iff R(x,t(T),v). Parsimoniously encode its circuit to three-occurrence 3-CNF. Keep the distinguished edge-mask variables and send every other coordinate to one. Its projected polynomial contains the monomial of T with coefficient exactly the number of v satisfying R(x,t(T),v). There are no other monomials. Surjectivity of the tour index proves the equivalence and the reduction gives the stated completeness. This result changes when positive weights other than 0,1 are allowed.

### Unsigned or signed images, fixed prime characteristic

Write ModₚP for problems for which a #P acceptance count is nonzero modulo a fixed prime p. To test *nonidentity*, nondeterministically choose an exponent and test whether its coefficient difference is nonzero modulo p. Signed terms can be simulated with multiplicity p−1. A single negative target term uses the same convention. This puts identity in coNP^ModₚP for every field of characteristic p.

For hardness, every NP^ModₚP predicate can be written as “some u has g(x,u) nonzero modulo p” for a #P function g. Indeed, u specifies a nondeterministic path and all its claimed oracle replies. First check consistency of the simulated deterministic steps on these replies. For each oracle query with acceptance count a, Fermat's theorem makes a^(p−1) a Boolean residue, one on a true answer and zero on a false one. For a claimed false reply use 1−a^(p−1). Products of all the reply conditions force all replies correct. Polynomially many #P products are #P by guessing all witnesses; subtraction modulo fixed p is addition of p−1 copies. This accounts for adaptive queries as well. Choose the underlying accepting witness relation V(x,u,v) for g, padding with a unique canonical suffix if needed.

Alongside an independent branch producing HC_m, create a branch for every accepting (u,v), pinning its inactive payloads and the unused branch's tag exactly as in the preceding construction. In this branch retain one marker variable Z and an exponent variable U_i for each bit of u; project its other physical coordinates to one. Choose m≥|u|+1 and use distinct *diagonal* target variables for Z,U₁,…,U_|u|. The original HC branch uses only off-diagonal variables in accepted tours, so the extra contribution is
$$ Z \sum_u g(x,u) \prod_{i:u_i=1} U_i . $$
Different u have different squarefree monomials. Equality with HC_m is equivalent to g(x,u)=0 modulo p for all u. Every image in this construction is a target variable or one. Field extension degree does not matter because all resulting coefficients lie in the prime subfield.

### Fixed target order and support-covering transfers

When m is any fixed integer ≥2 only polynomially many exponent vectors are possible, even if different source exponent bits are sent to the same target variable. In characteristic zero with unsigned weights, multiply the adjusted fiber counts from the membership proof over all these exponents. This product is #P, and is one exactly when every adjusted count is one, giving membership in US. Hardness attaches an arbitrary witness relation to every fixed tour, so equality is equivalent to exactly one accepting witness. The class is US-complete. In characteristic p, test all the polynomially many coefficients by the modular Boolean product argument. This yields ModₚP membership; an always-present tour plus a single positive #SAT-count branch gives hardness by the complement closure for each fixed prime. The signed characteristic-zero test remains C₌P-complete at every fixed m≥2.

For variable m, the mod-p hardness persists under a tighter structural promise. Use the same surjective tour index as in the unsigned characteristic-zero proof. Independently at each tour T, admit one canonical baseline extension and one additional extension per accepting witness of V(x,t(T),·), on disjoint branches. The integer coefficient of T is exactly 1+g(x,t(T)); no other support is present. Send one distinct representative per edge bit to its own target variable and every remaining variable to one. This supplies an unsigned, already support-preserving projection, with at least one preimage of every tour and no illegal surviving exponent. It equals HC over a field of characteristic p iff all the extra fiber counts are zero modulo p, giving coNP^ModₚP hardness under this stronger promise. The same support promise over a characteristic-zero field makes unsigned identity coNP-complete: two distinct surviving source assignments for the same tour certify NO. For hardness attach extra witnesses from a SAT instance to a baseline copy of every tour. This distinction comes entirely from the characteristic.

## 4. Relation to earlier work

Briquel and Koiran used the same assignment-monomial polynomial and classified the polynomial families possible for fixed Boolean constraint languages, including VNP-hard monotone 2-CNF families. Hard individual polynomials at width two coexist with the easy *promised uniqueness test* at width two above. Tovey proved the bounded-occurrence SAT tractability threshold and the satisfiability of exact-width-three instances with maximum occurrence three. The straightforward deterministic circuit encoding, implication-cycle occurrence bound, closure properties of GapP, and circuit-size monotonicity of projections are classical ingredients. [Briquel and Koiran, A Dichotomy Theorem for Polynomial Evaluation](https://arxiv.org/abs/0902.2300) · [Tovey, A Simplified NP-Complete Satisfiability Problem](https://doi.org/10.1016/0166-218X(84)90081-7)

Every PΦ in the first row comes from a VNP Boolean-sum description. For Boolean witness bits e the product over j of (1−e_j+e_j X_j) selects its monomial. Multiply this by the product of the clause-satisfaction indicators, using 1 minus the product of the false-literal indicators for each clause. The summand has linear-size arithmetic formulas and degree O(N+literal occurrences). Summing over e gives PΦ over every field. Taking the always-true ψ with no witness bits gives a uniform explicit read-three 3-CNF coefficient family projecting to HC, hence a VNP-complete family under standard field p-projections. The substantial gap for its minimization uses the quantitative circuit lower bound. [Fournier et al., HC completeness in every characteristic](https://webusers.imj-prg.fr/~herve.fournier/publications/vnp.pdf)

 Counting-HC source polynomials and projections have an extensive earlier algebraic-complexity literature. Mahajan and Saurabh study particular SAT and tour generating polynomial families and projection barriers. Forbes, Shpilka and Volk investigate algebraic natural proofs via succinct hitting sets. Garlík, Gryaznov, Lu, Santhanam and Tzameret study bounded-arithmetic/propositional proofs of algebraic lower bounds. The questions in this packet are the complexity of reasoning about a bounded-occurrence **exponent predicate** and the cost of auditing a single supplied literal projection. A systematic priority claim for this precise combination remains open. Dewan's linear-equivalence problem also has HC as target; there the unknown change of variables and input access differ from our test of a single explicitly given literal map. [Dewan, Testing Equivalence to the Hamiltonian Cycle Polynomial](https://arxiv.org/abs/2606.26653) [Mahajan and Saurabh](https://eccc.weizmann.ac.il/report/2016/038/) · [Forbes, Shpilka and Volk](https://theoryofcomputing.org/articles/v014a018/) · [Garlík et al.](https://arxiv.org/abs/2610.33938)

Ordinary dense algebraic-MCSP supplies the list of coefficients; it can be exponentially longer than the 3-CNF in these reductions. Arithmetic circuit minimization instead supplies an arithmetic circuit for the target; the Boolean circuit in our encoder computes *individual coefficients*, and a hard polynomial here cannot have a small arithmetic presentation. The stronger input access/different length parameters make transfers to those two models unwarranted. Boolean P versus NP also remains a separate question. [The Complexity of Order-Finding for ROABPs, discussion of MCSP and minimization](https://anamay.bitbucket.io/assets/docs/papers/orderFinding.pdf)


## 5. A tight entry-query obstruction for interactive verification

Let n count data variables. Fix k=⌊n/2⌋ and m≥2 with m²+k−m≤n. On k−m fresh variables use their product T and call H=T·HC_m on m² other data variables. Remaining variables are unused. The support comprises exactly h=(m−1)! distinct squarefree degree-k monomials. Padded tags may be specialized to one at zero additional cost. Let an additional variable X★ supply a shared nonzero baseline. The easy polynomial is X★; the hard inputs are X★+Hπ for all coordinate permutations π of the n data variables. Killing X★ and setting the tag variables to one gives HC_m on each hard input. Its coefficient predicate is computed in polynomial time from the permuted vertex labeling.

A verifier may interact arbitrarily with a prover. It obtains its actual input only by querying individual formal coefficients. Assume completeness c on the baseline and soundness s<c on every hard input. Fix an honest prover strategy for the easy input, including its possible randomness. On every hard input a dishonest prover may emulate this same strategy. Use the same verifier and prover coins on the baseline and alternative transcripts. Until the verifier asks for a coefficient at which its oracles differ, *its entire transcript* is identical, regardless of the length of messages or how it chose the next query. For uniform π each degree-k squarefree exponent belongs to the changed support with probability h/N, where N=binom(n,k), by transitivity. Other exponent queries never detect a change. Record all the queries on the easy transcript first; this random list is independent of π. Its probability of detecting any change is at most (h/N) times its expected length q. Consequently

    q ≥ (c−s) N / h.

The bound holds even with unbounded prover computation, arbitrary rounds and proof length, and for adaptive queries with an expected bound on the easy input. On the two-orbit promise, sampling uniformly random degree-k squarefree coefficients gives the matching O(N/h) upper bound for constant error. When m=⌊n^δ⌋ with fixed 0<δ<1/2, h=exp(o(n)), N=exp(Θ(n)), so the lower bound is N^(1−o(1)); the algebraic exact and Laurent gap is exp(Ω((log n)^(4/3))). This is an oracle result. It does not limit algorithms that read the explicit short coefficient predicate, ask for polynomial evaluations, or obtain authenticated aggregate answers.

The same coupling extends to the shared dense positive selector construction developed independently in the companion project. Over the reals put L(z)=∏(1+zᵢ), D(z)=∏(1−zᵢ), choose B>1, and use at least one selector bit. A fixed easy table is E=B·L(x)L(w)+L(x)D(w). Its hard perturbation is E−2Hπ(x)D(w). At each data exponent a the selector coefficients are B±1 in exactly equal numbers, including after perturbation; summing out any nonempty subset of selector bits eliminates the difference. Coordinatewise for x,w≥0 the ratio differs from one by at most 2/(B−1). Recover Hπ by fixing w=0, subtracting the known (B+1)L(x), and multiplying by −1/2. This costs O(n) additional gates. The argument for N/h probes uses the same data coordinates and supports of size h. This real construction is supplementary to the all-characteristic CNF gap.


## 6. Reproduction and evidence

With Python 3.10+ and no third-party packages, run the three control programs:

```sh
python3 check_gap.py
python3 check_fibers.py
python3 check_boundary.py
```

To generate an actual DIMACS instance and a literal projection, prepare a source file `small.cnf` containing the two lines `p cnf 2 1` and `1 -2 0`, then run

```sh
python3 export_instance.py small.cnf --order 2 --witness 10 --projection map.json > planted.cnf
```

This produces 330 exponent bits and 472 clauses, and a JSON map with unspecified coordinates sent to one. The program validates the witness and prints the known one-hot baseline coordinate as a DIMACS comment. The two-vertex example illustrates the reduction at a finite size; the nonuniform circuit lower bound applies asymptotically.

The first control compares the compiled CNF to its intended predicate on 3,296 exhaustive or explicitly targeted small primary assignments, checks every three-vertex edge mask in the baseline circuit, both signs of count differences, Tseitin truth tables, and all signed-copy cycles up to length eight. The second tests 176 actual tour/witness encodings including a matrix of order five, missing and repeated coefficients, exact agreement over the integers, a disagreement that vanishes modulo two, and one that vanishes modulo three. The last compares the occurrence-two algorithm with brute force on 1,400 sampled formulas and 11,200 restrictions, then checks 9,678 three-/four-variable exact-width-three formulas. These finite controls are reproducible examples. The asymptotic arguments and counting-complexity reductions are mathematical proofs in sections 1–5.

The Lean modules use Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The portable replay expects an already-built checkout and invokes no network tools.

```sh
MATHLIB_ROOT=/absolute/path/to/mathlib4 sh check-package.sh
```

The independent entry points are as follows.

| Module | Kernel-checked assertion |
|---|---|
| OccurrenceCycle | Local signed implications around a cycle force a unique logical bit. |
| FunctionalCNF | A typed fan-in-two Boolean circuit over signed wires has exactly one satisfying assignment to its Tseitin clauses per accepted primary input. |
| EncodedModels | The joined compiler gives a bijection from accepting primary inputs to signed-cycle, functionally consistent physical assignments, and an equality of their full projected monomial sums. A clause placement must agree with the gate CNF once copies are identified. |
| CopyCompiler | An equivalence between original and copied satisfying-assignment types, plus preservation of a selected copy's projected monomial. The predicate can be the actual positional CNF. |
| PlantedSlices | The algebraic planted-witness polynomial projects to the entire selected target over any commutative semiring. An empty witness set produces one fixed baseline variable. |
| SignedTransfer | Exactly matched positive/negative witness counts characterize equality with the base polynomial over the integers, and bijective unique extensions preserve an entire polynomial sum. |
| FiberPolynomial | Equality with a desired coefficient-one support is equivalent to equality of all the ordinary fiber cardinalities after mapping them into the coefficient semiring. |
| QueryCounting | The transcript union bound and the double-counting identity for a regular finite point/world incidence relation. |
| ExactWidth | A satisfying assignment to an exact-width-three, maximum-occurrence-three formula with at least two distinct variables per clause and a nonempty variable set always has a different mate. The kernel also checks the stronger clause-count condition used in its proof. |

Every listed theorem has been kernel-checked from these original modules with at most propositional extensionality, classical choice and quotient soundness. No theorem in the table imports the Anthropic proof. The source archive includes the exact axiom-audit transcript. The all-field asymptotic circuit bound comes from the separately reviewed upstream proof and CI. The supplied Python reductions and the complexity-class completeness/membership arguments have not been translated into end-to-end Lean definitions of the complexity classes. Earlier project's independently checked `SparsePermanent.Leaf.computes` and `SparsePermanent.Leaf.approximates` prove the exact same-budget projection principle against the upstream statement's definitions, including its Laurent regularity conditions.
