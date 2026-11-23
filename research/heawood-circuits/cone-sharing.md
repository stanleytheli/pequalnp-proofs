# Shared formula cones of up to eight gates

For the Heawood edge function, every binary monotone circuit of at most 26 gates must have either two internally shared gates on a common path or a shared gate with at least nine private gates in its input formula. This finite result uses the weighted Karchmer–Wigderson game in formula-certificate.md.

Start with the live cone of the circuit, folding constants and repeated-operand identities. When internally shared gates form an antichain, each such gate h has a private input formula consisting of k gates including h. Two such formulas can share only primary variables. Cutting them out gives a main formula with an auxiliary variable for each h. Let r be its multiplicity in the main formula, so r≥2.

Write P for the subset of the 21 true edge rows making h true and Q for the subset of the 14 negative tagged rows making h false. The r leaf rectangles for h are disjoint and lie inside P×Q. Denote by M_r the most weight these rectangles can receive. Each ordinary variable leaf receives at most six. Since the main formula has at most s−Σk+1 leaves, its total weight is at most 6(s+1) plus the sum of the positive local excesses M_r−6(r+k).

## Finite enumeration

With a current Python 3, run `python3 cone_profiles.py 8` in this directory. For every k, enumerate pairs of smaller formula signatures of total cost k−1 and apply the AND and OR operations componentwise. Quotient by all 336 side-preserving and side-exchanging symmetries of the Heawood graph. Every complete orbit is obtained by combining a fixed representative of the larger operand's orbit with every orientation of the smaller one. Signatures already achieved at lower cost need not be stored again.

A wire with empty P or empty Q can be omitted from this enumeration. If its parent's combination remains nonempty on both sides, the resulting legal rectangle is contained in the legal rectangle of the other operand. Each combining operation is monotone under componentwise inclusion. Consequently every formula root with nonempty legal rectangle is dominated by a no-more-expensive retained formula root. For the excess analysis the original cost only helps.

For each new orbit compute M₁, M₂, and M∞, the sum of the positive entries. Two disjoint rectangles separate along the row or column axis. Enumerating a partition of that axis and looking up the best subrectangle on each side gives M₂ exactly. In general, M_r is at most the minimum of M∞ and floor(r/2) M₂ + (r mod 2) M₁. A sharper value for r=3 or r=4 comes from choosing masks for the rectangles on the smaller axis, then independently choosing disjoint active masks of greatest combined weight in each perpendicular column. A repeated nonempty axis mask can be merged across two rectangles because their perpendicular sets are disjoint.

| Private gates k | New signature orbits | Distinct concrete signatures |
|---:|---:|---:|
| 1 | 4 | 112 |
| 2 | 11 | 1,078 |
| 3 | 70 | 9,947 |
| 4 | 325 | 71,008 |
| 5 | 1,753 | 443,429 |
| 6 | 7,798 | 2,285,808 |
| 7 | 33,069 | 10,196,480 |
| 8 | 117,302 | 37,591,708 |

Only these minimal-cost profiles have positive excess, with masks in the coordinate orders of verify.py.

| k | P | Q | Excess at r=2 | Excess at r=3 | Excess at r≥4 |
|---:|---:|---:|---:|---:|---:|
| 6 | 122 | 16383 | 1 | 0 | 0 |
| 7 | 63 | 16383 | 1 | 0 | 0 |
| 7 | 969 | 16383 | 4 | 1 | 0 |

Here a zero denotes an upper bound of zero for the excess. The supplemental exact packing checks are reproduced by `c++ -O3 -std=c++17 rectpack.cpp -o rectpack` followed by `python3 verify_cones.py`. The size-eight residual candidate has M₃=60, below the allowance of 66.

## Combining exceptional cones

A positive excess survives replacement by a dominating minimal-cost signature only if the original cone has exactly that signature's cost: every exception is smaller than six. The true edge profile of the original cone may be a subset of the retained representative's edge set; the bounds below use only containment.

Two excess-four cones each cost seven gates. After cutting just these cones, the residual circuit has at most twelve gates and both auxiliary variables occupy at least four operand slots. A connected binary DAG with g gates has at most g+1 operand slots available for primary or auxiliary wires because its g−1 nonoutput gates need at least one reader each. There can therefore be at most nine distinct ordinary inputs. But for any two oriented profiles of type 969, the edges covered by neither touch at least ten vertices, as verified by verify_cones.py. Each of these vertices must occur as an ordinary input. On an uncovered edge and either of its singleton subsets, both auxiliary signals are zero by monotonicity, so the vertex added to a singleton must be read ordinarily to distinguish the outputs.

Three cones with total excess at least six that include exactly one excess-four cone cost at least 7+6+6=19 gates. After cutting them the residual has at most seven gates, and the three auxiliary signals occupy at least six slots, leaving at most two ordinary variables. The three positive profiles have size at most six each. At least three edges lie outside the union. In a simple graph they touch at least three distinct mandatory ordinary variables. Finally, with no excess-four cone, six units of positive excess require six distinct cones costing at least six each, already above the gate budget.

The total excess is thus at most five whenever s≤26. But the game's weight is 168, strictly greater than 6(26+1)+5. This proves the claim for shared, disjoint cones of up to eight gates.
