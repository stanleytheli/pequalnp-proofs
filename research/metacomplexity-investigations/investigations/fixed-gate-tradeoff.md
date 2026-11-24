# Sharp dependence of dense output length on a fixed circuit budget

Fix a nonnegative size bound s, set k=s+1, and let each encoded
output bit read a fixed set of at most q source bits, q≥1. Use the
project's fixed dense partial-table format, and require exact parity
reduction on every source input. As n/q grows, the minimum achievable
target arity a satisfies

    a + 1 = Θ_s(2^{n/(q(s+1))}).

Equivalently, for the shortest dense output of length M,

    log₂ log₂ M = n/(q(s+1)) + O_s(1).

The constants may depend on s. This quantifies how much a fixed extra
gate budget saves on row count. The result concerns representation
length under the specified locality; it grants the constructor as much
time as needed to write its output.

## Lower bound from the inputs a circuit actually reads

Every single-output circuit of at most s fan-in-two gates depends on
at most k distinct raw inputs. Trim to its output, and count edges of
the connected fan-in cone, or unfold the graph while counting shared
vertices only once. With g gates and h distinct used raw inputs,
connectivity gives h+g−1≤2g. Constants and unused raw inputs only
decrease h. A zero-gate circuit is a projection or the default false.

Consequently the number of distinct possible witness functions on a
named inputs is at most C_s(a+1)^k. For example, choose up to k
essential variables in order and assign any Boolean truth table on
k padded arguments; even 2^(2^k) suffices for C_s. The consistency
set of each small function is a width-q CNF, and exact parity makes
all its satisfying assignments isolated. By the satisfiability coding
lemma at least 2^(n/q−1) distinct small functions are needed. Taking
kth roots gives the claimed lower bound. This support count avoids
paying separately for both operand choices at every gate.

## Upper bound from one hitting-set choice per group

First split the n source bits into m=⌈n/q⌉ nonempty blocks, each of
size at most q, and let b₁,…,b_m be their parities. Split these m
parities into k nonempty groups of nearly equal length. This requires
m≥k, which holds in the regime of the theorem. The target coordinates
of group G are all pairs (w,p), where w is any bit vector with the
group's length and p is an entering parity bit. A candidate's exiting
parity is p XOR parity(w). There are at most 2k·2^⌈m/k⌉ such coordinates.

Prescribe zero at the all-zero row. Every other prescribed row will
be one, with its input vector the indicator of a set of coordinates.
Use the following sets.

* Include each whole group, once, with no auxiliary coordinates in
  these k rows. Any hitting set of size at most k must choose exactly
  one coordinate in each group.
* Include the first-group candidates with entering parity zero and
  the last-group candidates with exiting parity one.
* For each adjacent pair of groups include two sets. The first
  contains previous candidates with exit zero and next candidates
  with entry one. The second contains previous candidates with exit
  one and next candidates with entry zero. Hitting both is exactly
  equality of the selected exit and entry.
* For each block index i allocate two sets containing group candidates
  whose local bit at i is respectively zero or one. Prescribe only
  the row for b_i, leaving its counterpart unspecified.

To keep every row index distinct, add ⌈log₂(2m+2k+1)⌉ auxiliary
coordinates and append distinct nonzero binary tags to all rows after
the k whole-group rows. This adds O(log(m+k)) to the arity. None of
these tag coordinates can be selected because all k choices are
already committed to the disjoint group rows. None of the tagged
rows coincides with the prescribed zero. Both bits of every dynamic
row are the same q-junta, choosing between 00 and 11. All other
encoding bits, including the header, are constant.

A hitting set of size k exists exactly when the local group words
agree with the actual block parities and their running parity starts
at zero and finishes at one, exactly the source's odd-parity condition.
If such a set exists, OR its k selected coordinates using k−1=s
binary gates. Conversely, the support of any size-s circuit completing
the table must meet every specified positive set, since its value
differs from the all-zero row. Its support has size at most k, so it
gives precisely a feasible hitting set. This argument also works for
a larger target gate basis that allows arbitrary binary truth tables
and includes binary OR. The sparse Hitting Set equivalence in the
public program uses this same basic reduction.

The resulting arity is at most 2k·2^⌈m/k⌉+O(log(m+k)), giving the
upper bound for fixed s. The length encoding M=s+1+2^(a+1) translates
this into the displayed double-logarithmic equality. At s=0 the
companion note gives the exact optimum, including additive constants,
in several regimes.
[Swarm Hitting Set theorem](https://data.pequalnp.com/data/lemma/L-meta-015.7f52365aee0b.json) ·
[Fixed-scope width-q certificate proof](junta-cells.md) ·
[Satisfiability coding lemma](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/PaturiPudlakZane_1999_cjtcs.pdf)

## A bound uniform in the gate budget

One can replace the constant C_s with an explicit estimate that also
applies when s grows. Every trimmed binary circuit has an encoding by
an ordered binary tree: starting at its output, expand each gate at
its first encounter in a depth-first traversal. Represent later
encounters by a leaf referring to the earlier gate's preorder index.
Other leaves refer to one of the a variables or to false. Gate inputs
of arity below two can be padded, with the original gate represented
by the appropriate two-input truth table. An absent operand can use
the false leaf. A full tree with g internal nodes has g+1 leaves,
fewer than or equal to 4^g possible shapes, and at most 16^g ways
to label its gates. This encodes every circuit with g used gates,
allowing harmless extra codes for invalid references. The functions
with no used gates are accounted for by a single leaf.

There are therefore at most

    Σ_{g=0}^s 64^g(a+s+1)^(g+1) ≤ [65(a+s+1)]^(s+1)

possible functions. Combining this with the width-q witness bound gives

    a + k ≥ 2^{(n/q−1)/k} / 65,       k=s+1.

The construction above gives a+1≤C k 2^{n/(qk)} for an absolute
constant C when 1≤k≤⌈n/q⌉: round a block and group size up, and
bound the number of tags by a constant times k·2^{n/(qk)}.
These inequalities retain useful information when the gate bound
grows with n. They imply the fixed-budget asymptotic with no
constant from counting arbitrary truth tables on k variables.

## Which part uses fixed bit scopes

In the project's encoding under ordinary input-dependent certificates,
a disagreeing specified row has a certificate of size at most 2q.
The witness-count lower bound then has exponent n/(2q), whereas the
fixed-scope construction is still allowed. Thus for a fixed s the
leading lower and upper exponents in the double logarithm differ by
at most a factor of two. The exact leading exponent in that model is
left open by these arguments.

A common alternative encoding uses separate indicators for a specified
zero and a specified one; absence means both indicators are zero.
In that encoding every disagreement already has a q-certificate under
ordinary input-dependent certificate locality. The width-q lower
bound goes through directly. The tagged hitting sets in the upper
bound still use only constant bits or a single block's parity, so they
satisfy that certificate condition. Hence the same sharp fixed-s
asymptotic applies to the one-hot encoding even with input-dependent
query sets. The zero-gate sharpness constructions carry over as well.
This explains exactly where the choice of row encoding enters the
proof; the project's end-to-end Lean theorem uses its original
presence/value encoding.
