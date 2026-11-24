# The constants fit in an extension of degree at most three

The ten-edge specialization for subcubic seeds with constant root activities in {0,1,−1} needs very little extra field structure. It works over the ground field in characteristic zero and in every prime characteristic at least 11. In characteristics 3, 5 and 7 an extension of degree at most two suffices. In characteristic 2 an extension of degree at most three suffices. The choices do not depend on the order of the target Hamiltonian cycle or the seed graph.

For t=1 and u=2, the three middle quantities are A=1/13, B=21 and C=13. The ordinary end activities are −63/26 and −3/338; the data end activities are −21/13 and −2/169. The recurring middle activities are 1 and −21/13. The only primes where a denominator, a scalar, or a normalization 1+z can vanish are 2, 3, 5, 7, 13, 37, 67 and 167, including the nonzero root denominators 2^d+c for d=1,2,3 and c in {0,1,−1}. Thus this one rational substitution works in characteristic zero and outside this list. For the exceptional primes the following choices give both nonzero path signatures and all nine root denominators.

| Characteristic | Finite field containing the chosen constants | t | u |
|---|---|---|---|
| 2 | F₂[w]/(w³+w+1) | 1+w | w |
| 3 | F₃[w]/(w²−2) | w | 1+w |
| 5 | F₅[w]/(w²−2) | 1 | w |
| 7 | F₇[w]/(w²−3) | w | w |
| 13 | F₁₃ | 2 | 6 |
| 37, 67, 167 | the prime field | 1 | 3 |

For a field F of one of these characteristics, take the compositum with the indicated finite field in an algebraic closure. Its degree over F is at most the degree displayed. The extension has the same characteristic. Consequently the original lower bound, which is uniform over fields of each characteristic, applies after this constant extension.

The table can be checked by direct finite arithmetic. The accompanying program also explicitly sums over all 512 internal bit assignments for each of the eight endpoint cases in both path types. It separately tested the four small prime fields and F₄. In these fields, this particular uniform two-parameter choice cannot meet the requirements for all nine pairs of degree and root activity. This observation concerns the displayed gadget and uniform parameterization only.
