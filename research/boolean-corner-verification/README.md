# Positive graph probabilities at Boolean corners characterize bounded verification

Let \(Q_H(p)\) denote the probability that independently selected vertices of a finite graph form an independent set. For each input length allow graphs of polynomial size, arbitrary real cube-preserving affine vertex probabilities, and one positive scalar per approximant. Require convergence to a finite, nonnegative value at each Boolean input. The approximants can depend on the length and the approximation step. Their supports are the inputs with strictly positive limits.

For a bound \(b=b(n)\), restrict every graph to become bipartite after deletion of at most \(b\) vertices. **The supported languages are exactly those with a polynomial-advice verifier using at most \(b\) Boolean witness bits and deterministic polynomial time.** In particular bipartite graphs give exactly P/poly. Polynomially many witness bits give NP/poly. The converse construction recovers the entire integer witness count on Boolean inputs. It uses at most two affine parameters involving any one input bit.

The graphs realizing these counts can be subcubic, have arbitrary fixed polynomially growing girth short of linear in the physical vertex count, and have a known gate-optimal read-two monotone formula for their Boolean edge predicates. For zero guess bits they are entirely even subdivisions. With guesses, there is just one exceptional odd-length base path per guess. All approximating probabilities preserve the full real cube. The normalized values are required to converge only on Boolean corners. Coefficientwise convergence imposes a stronger condition, as seen in the explicit [nonreachability example](corner-separation.md).

## Upper inclusion

Normalize the smallest positive target value at a given length to one, and treat the empty support separately. A finite positive-separation argument turns membership into existence of a cover of an advised graph with nonnegative integer cost strictly below an advised threshold. Each vertex's input-dependent cost is the minimum of a polynomial number of fixed nonnegative integer labels activated by input literals. The integers have polynomial bit length, including the replacement for an infinite weight. The complete proof is reproduced in [the finite separator](positive-border.md). Its extraction of weights holds for arbitrary graphs.

Provide an odd-cycle deletion set and bipartition in the advice. Guess one cover-membership bit for each deleted vertex. Reject if two omitted deleted vertices are adjacent. Charge the included deleted vertices, and force into the residual cover every surviving neighbor of an omitted deleted vertex. Remove those forced vertices, charge them, and find a minimum-weight bipartite vertex cover on the remaining graph by minimum cut. The check is deterministic polynomial time after the at most \(b\) guesses.

## A constant gate cost for every correct truth-table evaluation

Fix any polynomial-size binary circuit verifying ordinary input \(x\) and guessed bits \(w\). Hardwire its advice. Write \(s\) for its number of gates. Represent every signal by two Boolean rails, exactly one of which will be true in a faithful state. Give gate \(j=1,\ldots,s\) priority \(\delta_j=2\cdot16^{s-j}\). For gate \(g=f(a,b)\) introduce four row flags \(h_{ij}\) for \(i,j\in\{0,1\}\), two output rails \(g_0,g_1\), and the fixed implications
\[
 h_{ij}\Rightarrow a_i,\qquad h_{ij}\Rightarrow b_j,\qquad h_{ij}\Rightarrow g_{f(i,j)}.
\]
The gate objective, for its own priority \(\delta\), is
\[
 2\delta\sum_{ij}(1-h_{ij})+\delta(g_0+g_1).
\]
Once the predecessor rails are faithful, just one row is eligible. Selecting that row and exactly its required output rail has cost \(7\delta\). Every other feasible local state costs at least \(8\delta\). This holds for all sixteen binary truth tables. In particular the cost of a correct gate is independent of the data passing through it.

Take \(K=10\sum_j\delta_j+3\). For an ordinary input rail claiming \(x_i=b\), set the cost of leaving it false to \(K\). The cost of setting it true is zero when the claim matches and \(2K\) otherwise. The minimum for both rails is \(K\), uniquely attained by the correct rails. For a guessed bit, give either rail cost zero when true and \(K\) when false, and forbid both from being true. Its minimum cost is \(K\), attained once for each possible witness-bit value. Finally charge one if the circuit's rejection rail is true.

A correctly evaluated computation has total cost
\[
 A+\mathbf 1_{\rm reject},\qquad A=(n+b)K+7\sum_j\delta_j .
\]
An input or guess-rail error costs an extra \(K\), exceeding all possible savings relative to faithful later gates and the rejection term. With faithful source rails, consider the first erroneous gate in topological order. Its penalty is at least \(\delta_j>1+7\sum_{i>j}\delta_i\). The costs of later gates are nonnegative. Thus every optimizer is faithful. Each accepting witness supplies exactly one state of cost \(A\), and if there are no accepting witnesses the minimum is \(A+1\). This includes a verifier without gates whose output is already a source signal. Constant signals can be realized with a constant binary truth table.

## A subcubic weighted graph with one exceptional edge per guess

For each Boolean closure variable \(z\) create a left/right vertex pair with a diagonal edge. One covered endpoint encodes its value: the left endpoint represents \(z=1\), the right represents \(z=0\). Put the corresponding unary costs on these endpoints, plus \(H=A+2\) on each. For an implication \(a\Rightarrow b\) add the edge \(R_aL_b\). For the two rails \(u,v\) of a guessed input put a single exceptional edge \(R_uR_v\), which forbids both from being true when exactly one vertex per diagonal is covered.

To bound the degree, give each variable at least two clones, using a separate clone for every occurrence as an implication or exceptional-edge endpoint. Each clone has its own diagonal edge. Connect successive clones by cyclic implications, so their values agree whenever exactly one endpoint per diagonal is covered. Charge the substantive unary costs on just one clone and retain the common \(H\) on all endpoints. The diagonals and cyclic implications of every variable form an ordinary bipartite cycle visiting all its clone vertices. Each endpoint has at most one extra edge, giving maximum degree three. No two edges have the same pair of endpoints. There are only a constant number of flags and implication incidences per circuit gate, so the core has linear size in the circuit and its source signals. An optimum takes exactly one endpoint per diagonal: doubling any pair costs at least \(H\) beyond the common baseline, whereas a faithful cover's total surplus is at most \(A+1\). Consequently optimal covers correspond bijectively to faithful optimizing states. The total base exponent is \(B=H\cdot(\#\text{clone pairs})+A\).

Use absence probability \(q_v=t^{c_v}\) at a vertex of fixed weight \(c_v\). The parameter \(t\) tends to zero through positive reals. If a vertex's weight is \(c_0\) or \(c_1\) according to the ordinary bit \(x_i\), set \(q_v=(1-x_i)t^{c_0}+x_i t^{c_1}\). All input-dependent weights lie on left endpoints; every right weight is fixed. All weights are positive. At a Boolean input the lowest exponent of the no-edge probability is the cheapest cover, and its coefficient counts those covers: exactly the vertices of a cover are absent, and each selected vertex contributes a factor with constant term one. Thus \(t^{-B}Q_H\) tends to the number of accepting witnesses. The graph size and bit lengths of all exponents are polynomial. The polynomial degrees in this small parameter can be exponential. Each required power nevertheless has a repeated-squaring arithmetic circuit of polynomial size. If these degrees must be polynomially bounded, the bipartite corner model lies in nonuniform NC. [Parallel upper bound](degree-control.md)

The construction also gives an algebraic interpretation at the Boolean corners. In the quotient by all relations \(x_i^2=x_i\), the scaled probability is regular at the parameter origin and its constant coefficient is the canonical multilinear extension of the integer witness-count function. Indeed the evaluation at each corner lies in \(t^B\mathbb Z[t]\), with its specified leading coefficient. The Boolean Lagrange basis \(\prod_{i:x_i=1}X_i\prod_{i:x_i=0}(1-X_i)\) recombines these identities over the integers. The quotient identity specializes to every field. In positive characteristic the witness counts are reduced in that field; deterministic acceptance remains exactly zero or one. The ordinary polynomial before reduction by the Boolean relations can diverge at non-Boolean inputs.

## Long paths, unique minimum covers, and optimal read-two formulas

The regular edges have endpoints in opposite parts. Replace each of them by an even path of length \(2k\), \(k\ge4\). Replace each exceptional edge, with an arbitrary orientation from one right endpoint to the other, by an odd path of length \(2k+1\). Write \(C\) for a positive integer large enough that \(D=C-k+1\) exceeds every old weight on either Boolean value of its input. Assign cover cost \(C\) at every odd-position private vertex and \(C+1\) at every even-position private vertex, in path order. For fixed covered endpoint bits \(x,y\), the minimum private cost is attained uniquely.

| Old endpoint bits | Even path, \(2k\) edges | Odd path, \(2k+1\) edges |
| --- | ---: | ---: |
| \(00\) | \(kC\) | \((k+1)C+1\) |
| \(10\) | \(kC\) | \(k(C+1)\) |
| \(01\) | \(kC\) | \(kC\) |
| \(11\) | \((k-1)(C+1)\) | \(kC\) |

Cardinality dominates every possible unit bonus because \(C>k\) in this construction. At the same cardinality all available odd positions are chosen whenever that yields a cover. On the odd path with endpoints \(00\), the last even position is also required. The even-\(11\) and odd-\(10\) cases force the all-even pattern by alternating along the remaining odd-order path. The even table equals \(kC-Dxy\); the odd table equals \((k+1)C+1-Dx-(C+1)y+Dxy\).

For regular edges interpret the physical left endpoint bit as its original cover bit \(a_l\), and the physical right endpoint bit as \(1-b_r\), the complement of its original cover bit. Keep every left weight \(c_l\). At a right vertex sum corrections \(D\) from each regular incidence, \(D\) from each outgoing exceptional incidence, and \(C+1\) from each incoming exceptional incidence. Give the physical vertex that sum minus \(c_r\); it is positive and fixed. The transformed cost is an input-independent constant plus the original objective in the proposed cover plus \(D\) for each uncovered original edge. The constant is
\[
 kC|E_{\rm reg}|+((k+1)C+1)|E_{\rm exc}|-\sum_r c_r .
\]
Adding one endpoint per uncovered edge costs strictly less than the penalties removed. Every optimum therefore covers all old edges. Each original optimum has exactly one physical cover extending it at the transformed minimum by the path table. Rescaling by the new common base exponent preserves the whole accepting-witness count at the corners.

Every regular path has even length, so all its old endpoints lie on the same side of the resulting physical bipartition. Deleting one endpoint of each exceptional odd path makes the remaining graph bipartite: any remaining part of such a path is a pendant path or an isolated segment. Degrees stay at most three. The initial base is simple and has no isolated vertices. Polynomially long paths give girth at least \(N^\alpha\) for any fixed \(0<\alpha<1\), where \(N\) is the actual number of physical vertices. Indeed with \(M\) base edges and minimum path length \(L=2k\), the size is at most \((L+2)M\) and girth at least \(3L\); choose \(L\ge(3M)^q\) with \(q/(q+1)\ge\alpha\).

For the unsigned Boolean graph, taking every old vertex and a minimum private cover on each path gives a minimum vertex cover. Deleting any set \(U\) of old vertices changes the optimized unweighted cover cost by
\[
 -|U|+\#\{\text{regular edges incident to }U\}
       +\#\{\text{exceptional edges internal to }U\}.
\]
The disjoint clone cycles give a different incident regular edge to each old vertex by orienting every cycle. Hence this change is nonnegative. An optimal read-two formula follows by grouping incident physical edges at the cover's star centers. On each even path, use every even private position as a center, making old endpoints centers as well. On an odd path whose endpoints are both centers, use the even private positions as centers and assign its final edge to the old endpoint. An old center has a regular incident edge and occurs once. Each private noncenter has degree two. The node count is \(|E_{\rm phys}|+\tau(H_{\rm phys})-1\), optimum even among unrestricted binary De Morgan circuits by the long-subdivision theorem. [Long-subdivision circuit result and verification](https://github.com/stanleytheli/pequalnp-proofs/tree/a31fcb5bd01e0bd1ba8e58c7c7db40195392c5fa/research/long-subdivision-circuits)

## Reproduction

For an example, `stretch(construct(2, 0, [(0, 1, 6)]))` in `closure.py` emits the complete physical graph for exclusive OR on two bits. In a truth-table integer, bit position \(2i+j\) is the output at input pair \(i,j\). The graph's `base` is the positive scale exponent and `stars` lists the variable-occurrence-limited formula explicitly. Each vertex lists its absent exponents at the zero and one values of its sole controlling input, or one constant exponent.

Run `python3 check_closure.py` using Python's standard library. Its graph optimizer reads the supplied physical edge lists and vertex weights, conditions on exceptional endpoints and reduces the remaining bipartite problem to maximum flow. A residual-cut enumeration counts the actual minimum covers and compares their multiplicity with direct witness evaluation, including on the physical long subdivisions. Run `python3 check_partition.py` for an independent contraction of the leading Bernoulli factors from the raw physical graph. It uses no matching or cover computation and checks the coefficient as well as its order. The Lean files check the four conditional path minima, the gate's local truth-row cost, first-error arithmetic, repair of uncovered edges, and the Boolean interpolation factorization in Mathlib 4.36.0. The complete hierarchy and circuit proof is given above. Weighted closure and its network algorithms have a classical literature. [Picard, *Maximal Closure of a Graph and Applications to Combinatorial Problems*](https://doi.org/10.1287/mnsc.22.11.1268)
