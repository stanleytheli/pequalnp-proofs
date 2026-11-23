# A fixed family for fair counting under zero restrictions

There is a polynomial-time constructible sequence of unweighted subcubic bipartite graphs \(H_m\) for integers \(m\ge1\), together with optimal monotone read-two formulas for their edge functions, with the following property. A CNF on at most \(m\) variables and at most \(m\) clauses determines only a set of input vertices to fix to Boolean zero. The graph and formula are fixed for the entire bound \(m\). The number of accepting assignments on the remaining free bits determines the original satisfying count by one polynomial-time metric reduction. Its low bit already equals the low bit of the satisfying count.

Thus exact counting on zero restrictions of this fixed family is #P-complete under polynomial-time metric reductions, and the parity question is ⊕P-complete under many-one reductions. The parameter may be given in unary or the fixed graph may be included explicitly. Independent input probabilities are either 0 or 1/2. The optimality statement concerns the original supplied formula before restricting its inputs.

## Universal witness

Use \(m\) witness bits \(z_1,\ldots,z_m\). For each clause slot \(i\) and each of the \(2m\) possible literals \(\ell\), introduce a parameter bit \(a_{i,\ell}\) for its presence. Introduce a bit \(t_{i,\ell}\) and three clauses expressing \(t_{i,\ell}\leftrightarrow(a_{i,\ell}\land \ell)\). Add one clause \(\bigvee_\ell t_{i,\ell}\) per row. This fixed CNF has \(O(m^2)\) variables, clauses and literal occurrences. The \(t\) bits are uniquely determined once \(z,a\) are fixed.

Write each input clause into one row of the incidence matrix. Fill unused rows by the tautology \(z_1\lor\neg z_1\). Pin unused witness bits to false, including \(z_1\) when the instance has no witness bits. This maintains exactly the original number of extensions even for empty clauses, tautologies and empty formulas.

## Physical zero pins and the shared modulus

Use the signed literal triangles and clause flags, split degrees using signed equality paths, and place each split parity sign at a free end as in [the fair-counting proof](fair-counting.md). For every pinned logical bit, forbid the vertex representing its *opposite* literal by fixing that physical input vertex to zero. Use the first clone in a split cluster. Its neutral activity allows the zero pin. Cancellation of the private triangle flag forces exactly one of the two literals in every surviving contribution. The equality-path identity is diagonal and holds even with this clone fixed. All parameters can therefore be supplied by forbidding vertices. The number of remaining logical witnesses is at most \(2^m\), regardless of the \(O(m^2)\) auxiliary bits.

Take the first \(D\equiv9\pmod{30}\) with \(Q=F_D>2^m\) and put \(a=F_{D-1}\). Attach a path with \(D-3\) vertices at every negative-weight site. This represents the relative signed activities by the two conditional counts \((a,-a)\pmod Q\). Replace every edge of this fixed scaffold by an even path of length \(L=D+1\). Additional girth padding can increase \(L\) by multiples of \(10D\). All original root coordinates, including the pin locations, remain available. Entrywise modulo \(Q\) the path signature is an edge signature multiplied by \(a^{(L-1)/D}\); this identity remains valid when specified roots are held absent.

Let \(N\) be the final number of vertices, \(P\) the physical pin set, \(M\) the scaffold edge count, \(T\) the number of former negative-weight sites, \(\eta\in\{-1,1\}\) the degree-splitting sign, and let \(A\) count assignments on the free vertices containing an edge. The least nonnegative residue of
\[
 \eta\,a^{-T-M(L-1)/D}\left(2^{N-|P|}-A\right) \pmod Q
\]
is the exact satisfying count. The inverse exists by coprimality of successive Fibonacci numbers. Every factor in the decoder except the number of free bits depends only on \(m\). Since \(3\mid D\), the modulus \(Q\) is even and the multiplying unit is odd. At least one unpinned bit remains, so \(A\bmod2\) is the parity of the original number of satisfying assignments.

The unpadded family has \(O(m^4)\) vertices. The signed seed and its split contain \(O(m^2)\) vertices and edges; \(D=O(m+1)\) from Fibonacci growth. The tails and the final even subdivisions each cost at most an additional factor \(O(m+1)\). All components contain a literal triangle before splitting, and splitting preserves a cycle in each component. Tails preserve that property. The even-subdivision formula centered at every even position therefore attains the unrestricted gate optimum and reads each variable at most twice. For any fixed \(\alpha<1\), padding \(L\) as in the fair-counting proof gives girth at least \(N^\alpha\).

[The generator](universal_fair.py) constructs the same graph independently of the instance before providing its zero pins. [Physical contraction controls](check_universal.py) tested fourteen alternative subcubes across three fixed graphs, including true and false instances at zero source variables. The largest tested graph had 67,683 vertices. The controls compare exact modular decoding and parity against enumeration on the source variables.

The zero restrictions can equivalently be specified by cube-preserving one-coordinate affine probabilities. For each supplied bit \(a\), give its two opposite literal representatives probabilities \(a/2\) and \((1-a)/2\). At Boolean inputs this leaves the required literal fair and the opposite literal absent. Keep every remaining free bit fair and every dummy pin at zero. All physical probabilities then lie in \([0,1/2]\). The empty selection has positive mass at every input. The decoded information lies in the modular value of the count.
