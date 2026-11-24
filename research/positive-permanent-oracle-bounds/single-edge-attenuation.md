# A constant approximation gap with one fractional edge

Fix \(0<\rho<1\). Let \(W\) be the matching-count or Hamiltonian-cycle-count polynomial, and write \(H\) for an individual undirected perfect matching, undirected tour, or directed tour. All its witnesses have the same size \(h=\Theta(m)\), where \(m\) is the number of graph vertices. On \(1_H\) let \(B_H=W(1_H)>0\). On the assignment \(x^{H,e}\) obtained by replacing only edge \(e\in H\) by \(\rho\), the target is exactly \(\rho B_H\).

Let \(P\) have nonnegative coefficients and be globally sound on Boolean inputs: every positive Boolean assignment contains a witness. Its formal Newton polytope has extension complexity at most \(s\). The orbit-cover and entropy bounds in the [linear-repetition argument](linear-repetitions.md) supply constants \(\beta,\gamma>0\) and a polynomial \(L(m)\), independent of \(s\), such that the fraction of witnesses having *any* realizing source monomial with at most \(r=\lfloor\beta h\rfloor\) distinct repeated edges is at most
\[
  (s+1)L(m)\,2^{-\gamma m}.
\]
Here a realizing monomial on \(H\) has variable support exactly \(H\). For odd tours the one-vertex contraction costs a polynomial factor; rounding the threshold by a constant is absorbed by choosing a smaller \(\beta\). A globally valid multiplicative approximation on the Boolean cube automatically meets soundness at all zero assignments.

For every other witness \(H\) with \(P(1_H)>0\), weight the realizing monomials \(x^a\) by their coefficients divided by \(P(1_H)\). They form a probability distribution because every positive term on \(1_H\) contains the whole witness. Put \(\eta_e=\Pr[a_e\ge2]\). Then \(\sum_{e\in H}\eta_e\ge r+1>\beta h\), and at least \(\beta h/(2-\beta)\) edges satisfy \(\eta_e\ge\beta/2\). Otherwise the total would be less than \(\beta h\), by bounding each large term by one and each remaining term by \(\beta/2\). For every such edge,
\[
 \frac{P(x^{H,e})}{\rho P(1_H)}
   =\mathbb E[\rho^{a_e-1}]
   \le 1-(1-\rho)\eta_e
   \le 1-d,\qquad d=(1-\rho)\beta/2>0 .
\]
This estimate holds uniformly over the magnitudes and the multiplicities of the coefficients.

If \(P\) is a simultaneous \((1\pm\varepsilon)\) multiplicative approximation at all Boolean points and all these single-fractional points, the same ratio must be at least \((1-\varepsilon)/(1+\varepsilon)\). Choose any \(0\le\varepsilon<d/(2-d)\). The two inequalities conflict, so **every** witness must have an easy monomial. The easy-fraction bound now forces
\[
  s+1\ \ge\ 2^{\gamma m}/L(m).
\]
Consequently an explicitly wired monotone arithmetic circuit with permanent oracles requires exponential size for this approximation. Exact counts on other interior inputs are unnecessary. The full Boolean zero tests ensure global soundness and the positive witnesses calibrate the allowed multiplicative scale.

There is also a distributional version for globally sound circuits. Choose a uniform witness \(H\), then with probability one half test \(1_H\), and otherwise test \(x^{H,e}\) for a uniformly chosen \(e\in H\). If a difficult witness has \(P(1_H)=0\) or its value at \(1_H\) is outside tolerance, the Boolean branch fails. Otherwise its \(\beta h/(2-\beta)\) affected fractional tests fall below the requested lower bound. Thus the failure probability is at least
\[
 \frac{\beta}{2(2-\beta)}
 \max\{0,\,1-(s+1)L(m)2^{-\gamma m}\}.
\]
This proof assumes global Boolean soundness, but requires no accuracy premise on the positive Boolean witnesses for the distributional lower bound.
