# Almost every tour forces many distinct repeated edges

Let a circuit use variables, nonnegative real constants, sums, products and explicitly wired permanent gates, sharing arbitrarily many subcircuits. In Boolean decision mode its positive output means acceptance. Even if tested only on graphs with at most m directed edges, a polynomial-size circuit that correctly recognizes the m-city Hamiltonian tours has the following property. Outside a fraction at most exp(−Ω(m)) of the labeled tours, every accepting parse supported on that tour repeats Ω(m/log m) **distinct** edges. A repeated edge is an input label occurring at least twice anywhere in the unrolled parse tree. Two calls to a shared subcomputation count as two occurrences. The same conclusion holds for recognition of perfect matchings on an even number m of vertices, tested on graphs with at most m/2 edges.

The statement also holds for monotone Boolean AND/OR circuits with bipartite-perfect-matching oracle gates, by interpreting AND as multiplication, OR as addition and a matching query as its permanent. In these circuits an accepting parse chooses a witness perfect matching at each query. Formal numerical coefficients in this lifted circuit are nonnegative and its support records exactly the parses. The lower bound concerns the structure of witnesses available to small circuits. Existence of such decision circuits is a separate question. For exact counting on Boolean inputs, the argument gives a quantitative average error between Boolean vertices.

## A face construction for a single set of labels

Let F be a family of h-element subsets of n variables. Let A be the finite set of exponent vectors from a nonnegative formal polynomial P. Assume every monomial in P uses at least h distinct variables and every support of size exactly h belongs to F. These two assumptions follow when the circuit correctly rejects every nonmember on the Boolean layers up to h. Some members of F can even be missed. Write X=conv(A) and Y=conv{1_S : S∈F}. For K a set of at most h labels, the linear inequality

    Σ_{i outside K} a_i ≥ h−|K|

holds throughout X. On each exponent the slack is exactly

    (|supp(a)|−h) + |K outside supp(a)| + Σ_{i in supp(a) outside K}(a_i−1).

All three terms are nonnegative. Equality therefore selects precisely the degree-h-support monomials that contain every label in K and have each outside exponent at most one. The equality set is a face, possibly empty. Forget the original coordinates on K and restore the constant one on each of them. The affine image of this face is the convex hull of the zero-one indicators of these valid supports. This uses an extension of X with only one additional equation.

Suppose a witness of S repeats at most r distinct labels. Pad its set of repeated labels to any r-subset K of S, taking 0≤r≤h. This witness is captured by the face for K. Conversely each target recovered by such a face has a witness that repeats only labels in K. Thus the convex hull of the captured vertices has extension complexity at most O((xc(X)+1) binom(n,r)). One can take bounded extensions: equivalently use the bounded circuit occurrence-flow formulation in this packet. For general unbounded extensions the usual homogenized formulation for the convex hull of the union also works because every projected recession direction of an extension of a polytope is zero. Affine maps contribute their constant times the corresponding convex mixing weight.

## Transitivity upgrades existence to an exponentially small success fraction

Suppose a permutation group on the input coordinates acts transitively on F. Let M=|F| and let δ>0 be the fraction captured. Independently apply L uniformly random group elements to the known captured polytope. The probability that any fixed member is missed by all L translates is (1−δ)^L≤exp(−δ L). Taking L=ceil((1+log M)/δ) gives strictly fewer than one missed member in expectation, hence there are translates covering every member. All translated polytopes lie inside Y, and the convex hull of their union contains every vertex of Y. Consequently

    δ ≤ C (1+log M) (xc(X)+1) binom(n,r) / xc(Y)

for a universal constant, with the claim trivial if no vertex is captured. This applies separately to any polynomial with the stated support soundness and does not require that the circuit or its parsed witnesses respect any symmetries. Both undirected perfect matchings and directed Hamiltonian cycles are transitive under permutations of the graph vertices.

Their target polytopes have extension complexity at least exp(c m) for some fixed c>0. For tours use the projection onto the undirected traveling-salesman polytope obtained by adding opposite arc coordinates. Here n≤m² and log M=O(m log m). An explicitly wired polynomial-size permanent-oracle circuit has xc(X)≤poly(m) by the occurrence formulation. Choose r=floor(c' m/log m) for a sufficiently small positive c'. Since binom(n,r)≤n^r, the captured fraction is at most exp(−c''m) for some c''>0. This proves the stated frequency bound. The same estimate applies if the circuit is merely sound on the lower layers and recognizes only a subset of the valid inputs. All missed targets simply count as uncaptured. [Rothvoß, matching and tour lower bounds](https://arxiv.org/abs/1311.2369)

## Average loss away from the Boolean cube

Suppose in addition P counts the target's homogeneous multilinear indicator polynomial F exactly at each Boolean vertex. On the support S of an individual tour or perfect matching only terms with support S survive. Their coefficients sum to one (or to the coefficient of S for a weighted target). At ρ·1_S, for fixed 0<ρ<1, a term with r distinctly repeated labels has at least h+r total degree. Its value relative to its Boolean value times ρ^h is at most ρ^r. Thus for a uniform random valid S the expected ratio P(ρ·1_S)/F(ρ·1_S) is at most δ+ρ^r=exp(−Ω(m/log m)). This is conditional on exact Boolean counting by an explicitly wired polynomial-size monotone permanent-oracle circuit. Exact counting restricted just to each of the valid minimal supports is also sufficient provided all smaller Boolean inputs are rejected.

The face identity and transitivity argument are written proofs. The source of the exponential constants is the published extension-complexity bound. The relation to the questions about functional reductions and exact Boolean counting is a partial obstruction; research priority for this formulation has not been established. [Grochow, Questions 5.1, 5.2 and 5.6](https://toc.cs.uchicago.edu/articles/v013a018/v013a018.pdf)
