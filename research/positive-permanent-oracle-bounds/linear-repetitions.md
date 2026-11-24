# Linear distinct repetitions on matchings and tours

Let `P` be a formal polynomial with nonnegative real coefficients computed by a monotone arithmetic circuit with permanent oracles. Write `s` for its scalar gates and explicit oracle input slots, counting multiplicities. The argument also applies whenever `xc(Newt(P)) ≤ s` directly. A positive monomial on an edge set `H` means a monomial of nonzero coefficient whose support is contained in `H`. An edge repeats in this monomial if its exponent exceeds one.

Assume **global Boolean soundness**. For every edge assignment, `P>0` implies the presence of a witness of the indicated kind. Therefore the support of every positive monomial contains a witness. On an individual minimum witness `H`, each positive monomial has support exactly `H`. A witness is *easy* at threshold `r` if it has some positive monomial on which at most `r` distinct edges repeat. The bounds below permit a circuit that is positive on only some witnesses. Global soundness is essential to the face arguments on assignments with more edges than a witness.

For either perfect matchings or Hamiltonian cycles on a complete graph with `m` vertices, there are absolute `c,γ>0` such that when `s` is polynomial in `m`, at most `exp(−γm)` of all witnesses are easy at `r=⌊cm⌋`, for all sufficiently large `m`. This includes both directed and undirected simple Hamiltonian cycles. The corresponding polynomial-size permanent-oracle circuit statement uses the shared-gate Newton-polytope formulation in `oracle-circuits.md`.

## Orbit covering

Let `F` be a finite, transitively permuted family of `0/1` vectors, and let `Q ⊆ conv(F)` contain a fraction `θ>0` of its vertices. The image under a uniform group element contains any specified vertex with probability at least `θ`. The expected number of uncovered vertices after `t` independent translates is at most `|F| exp(−tθ)`. Taking `t=⌈(1+log|F|)/θ⌉` gives a cover, so the convex hull of the translates equals `conv(F)`. The disjunctive convex-hull formulation costs at most `t(xc(Q)+1)` inequalities, up to an inessential absolute term. Applied to all perfect matchings on `2d` vertices, Rothvoß gives `xc ≥ 2^(Ω(d))`. Consequently a subpolytope of this matching polytope of extension complexity `s` can contain at most `(s+1) poly(d) 2^(−Ω(d))` of the matchings as vertices. [Rothvoß, *The matching polytope has exponential extension complexity*](https://arxiv.org/abs/1311.2369). [Balas, *Disjunctive programming*](https://doi.org/10.1016/S0167-5060(08)70342-X).

## Perfect matchings

Write `m=2h`, let `a(h)=(2h−1)!!`, and let `δ` be the easy fraction. For each easy perfect matching `M`, select one witnessing monomial. Choose exactly `r` edges of `M` that include its repeating edges, adding arbitrary further edges if needed. Record the set `R` of their `2r` endpoints.

Fix `R`. Take the face of `Newt(P)` on which the sum of all crossing-edge exponents is zero. Every surviving monomial contains a perfect matching, and this matching must consist of edges internal to `R` and edges internal to its complement `S`. The sum of all exponents on edges internal to `S` is consequently at least `h−r`. Intersect with the equality face at `h−r`. On every surviving monomial, the edges in `S` then have exponents zero or one and form a perfect matching of `S`. Projecting to those coordinates produces a subpolytope `Q_R` of the matching polytope of `S`, with extension complexity at most `s`. Each easy matching assigned to `R` is tight on both faces, so its outside matching is a vertex of `Q_R`.

Some `R` has at least `δ a(h)/binom(2h,2r)` assigned matchings. An outside matching extends to at most `a(r)` full matchings assigned to this `R`. The identity

`binom(2h,2r) a(r) a(h−r) = a(h) binom(h,r)`

follows by counting a matching together with a choice of `r` of its edges. Thus this `Q_R` captures a fraction at least `δ/binom(h,r)` of all matchings of `S`. Orbit covering gives

`δ ≤ (s+1) poly(h) binom(h,r) 2^(−Ω(h−r))`.

For sufficiently small fixed `r/h>0`, binary entropy bounds `binom(h,r) ≤ 2^(h H₂(r/h))`, yielding an exponential upper bound on `δ`.

## Undirected Hamiltonian cycles

For `m=2h≥6`, color the alternating edges of a uniformly chosen tour by a uniformly chosen one of its two colorings. This gives an ordered uniformly random pair `(A,B)` of perfect matchings whose union is a single cycle. Some fixed `A` has at least a `δ` fraction of easy tours among its compatible `B`. There are exactly `b(h)=2^(h−1)(h−1)!` compatible `B` for this fixed `A`. To count them, cyclically arrange the `h` distinguishable `A`-edges, orient each, and identify reversal. Therefore

`b(h)/a(h) = 2^(2h−1)/(h binom(2h,h)) ≥ 1/(2h)`.

For each easy compatible tour, absorb its repeating `B`-edges in the endpoints `R` of exactly `r` edges of `B`. Repetitions on `A` may occur anywhere. For a fixed `R`, take the face that sets to zero every crossing-edge coordinate *except* those in `A`. Every surviving monomial contains a Hamiltonian cycle by global soundness. Each vertex of `S=V\R` must use at least one cycle edge not in `A`, since `A` is a matching. Every such edge lies entirely in `S`. The total exponent on edges of `S` outside `A` is therefore at least `|S|/2=h−r`. At equality those coordinates describe a perfect matching of `S`. Project to these coordinates, filling the excluded `A` coordinates on `S` with zero. The resulting `Q_R` lies in the full matching polytope of `S`. An easy tour assigned to `R` contributes its outside `B` matching, regardless of repeat exponents on `A`.

Some `R` collects at least `δ b(h)/binom(2h,2r)` good `B`. Each outside matching comes from at most `a(r)` such `B`. Consequently `Q_R` contains a fraction at least `δ b(h)/(a(h) binom(h,r))` of all matchings of `S`. The previous entropy and orbit argument applies, costing an additional factor at most `2h`.

For odd `m`, fix a vertex `v`. Its two neighbors in a tour form an unordered pair. Some pair `{a,b}` retains at least the overall easy fraction among tours having this wedge. Make a monotone substitution that sends `va` to `x_ab`, `vb` to `1`, all other edges incident to `v` to `0`, and the old edge `ab` to `0`. A tour in an expanded assignment contracts to a tour on the remaining `m−1` vertices using `ab`, so soundness survives. A selected easy monomial becomes an easy monomial on the contracted tour, as its only retained source for `x_ab` was `va`. All even tours containing `ab` arise by this contraction, and form the fraction `2/(m−2)` of all even tours. The preceding even bound for arbitrary sound circuits absorbs this polynomial factor.

For directed cycles, identify `x_ij` and `x_ji` with one undirected edge variable. Any positive monomial then contains an undirected tour. An easy monomial on a simple directed tour maps to a monomial with the same repeat count, because each unordered edge of that tour has only one orientation. Each undirected tour has exactly two oriented lifts for `m≥3`, so the directed easy fraction is at most the undirected easy fraction for the identified circuit.

## Evaluation inside a witness

Suppose in addition that `P` agrees with the witness-counting polynomial on Boolean corners. For a fixed minimum witness `H`, every contributing term has support `H`, and `P(1_H)` is its total coefficient. For `0<ρ<1` and any difficult witness, all contributing terms have degree at least `|H|+r+1`, hence

`P(ρ 1_H)/(ρ^|H| P(1_H)) ≤ ρ^(r+1)`.

For an easy witness the same ratio is at most one. For each fixed `ρ<1`, the average ratio is at most `δ+ρ^(r+1)=exp(−Ω_ρ(m))`. This bound is compatible with exact counting at all Boolean corners. It quantifies the loss on scaled witnesses. All results in this note are mathematical deductions; no Lean replay of the orbit-cover or entropy argument is asserted.

## Related circuit models

Jukna studies monotone arithmetic circuits that agree with a target on Boolean inputs and distinguishes the decision condition of agreeing on the zero set. His Boolean read-`k` model requires one monomial per prime implicant in which every individual exponent is at most `k`. The estimates above bound how many *different* edge variables must have exponent greater than one in every monomial of almost all witnesses, and allow explicit arbitrary-depth permanent oracle gates. Linear repetition is consistent with each of those individual exponents being two. I did not identify the matching-vertex face and alternating-tour counting argument in these references. [Jukna, *Lower Bounds for Monotone Counting Circuits*](https://arxiv.org/abs/1502.01865). [Jukna, *Notes on Boolean Read-k and Multilinear Circuits*](https://arxiv.org/abs/2207.08701).
