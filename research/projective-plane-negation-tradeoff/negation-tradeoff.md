# The cost of few negations for finite-plane line ORs

Let P be a projective plane of order q, with n=q²+q+1 input points and n output lines. The output at a line is the OR of its q+1 input bits. Count fan-in-two AND, OR, and NOT gates with arbitrary fanout, allowing outputs to share any wire. There is an explicit tradeoff between total gates s and the number t of NOT gates.

For every integer h with 1≤h≤q, put J=2ᵗ−1. At least

    h · max(0, n−1−qJh)

gates are necessary. When t=0 the sharper monotone bound is nq. In particular, for t≥1 with 2J≤q there is a lower bound q³/(8J). At each fixed negation budget this is a cubic-in-q bound. Any circuit of size at most n·polylog(n) for this operator consequently needs at least (1/2)log₂ n−O(log log n) negations.

## Why a small set of inputs can stabilize every negation

Order the NOT gates by their place in the circuit and encode their outputs as a binary word, most significant bit first. If one increases an input assignment coordinatewise and the words differ, examine the first differing NOT. All earlier NOT outputs have the same values at both endpoints. Substituting these values as constants leaves a monotone computation of the operand of the first differing gate. Its output can therefore only change from 1 to 0. The word strictly decreases in binary order. This is the chain argument behind Markov's inversion bound. [Markov, 1957, English translation 1958](https://doi.org/10.1145/320941.320945)

Begin with the empty selected set. Whenever adding at most h new points can change the word, make one such change. There are at most J strict decreases of the word. This gives a base B of size at most Jh on which **every** extension by at most h points has the same NOT word. Freeze all the NOT outputs to their values there. The resulting monotone circuit agrees with the original circuit throughout this upward Hamming ball, by induction on the topological order.

At most 1+q|B| lines meet a nonempty B. The first point meets q+1 lines and each further point shares at least one of its q+1 lines with the first. For empty B, all n lines survive. For each surviving line S, the pinned circuit with B clamped to true computes the OR of S on inputs of weight at most h.

Clamping causes no gate cost in this model. Replace each NOT by the constant gate with its chosen value. In every positive gate reading a fixed input, remove the neutral constant operands or replace the gate by the appropriate constant if an absorbing operand occurs. Empty AND and OR realize constants. A surviving nonsingleton line cannot be computed by an output that is a clamped raw input. Thus the surviving output wires of the same-size list have the required semantics.

The one-window private-gate lemma for pairwise-linear ORs gives at least min(h+1,|S|)−1=h gates per surviving line. The gates used by two lines are disjoint because each charged gate has singleton support of size at least two contained in its line, whereas two distinct lines share exactly one point. The lemma only needs agreement on the low-weight inputs and can be checked by the monotone frontier argument in the companion Lean development. Multiplying yields the stated bound.

For the numerical form, take h=floor(q/(2J)). With q≥2J this satisfies h≥q/(4J), Jh≤q/2, and more than q²/2 lines survive. Rearranging for s≤n·polylog n gives the claimed logarithmic negation requirement. When 2J>q, this rearranged negation conclusion already follows from J>q/2. The result is about an explicit multi-output Boolean operator.

## An almost linear upper bound in even characteristic

For q=2^b, the same line operator has fan-in-two Boolean circuits of size O(n log²n) with at most ceil(log₂(n+1)) NOT gates. Combined with the lower bound, the order of growth of the required number of negations for almost-linear size is Θ(log n) along this family.

First ignore the negation count. Use affine coordinates (x,y) in F_q², together with q+1 points at infinity. For a direction a in F_q let gₐ(z)=Σₓ f(x,ax+z), an ordinary integer count. The Walsh transform of the plane is indexed by additive characters. If the additive coordinates are binary vectors with the ordinary dot product and Mₐ is multiplication by a in that basis, then

    ĝₐ(v) = f̂(Mₐᵀv, v).

For the vertical lines ĝ∞(u)=f̂(u,0). Both identities follow by changing variables in the finite sum; the transpose is needed for an arbitrary binary basis. Compute the two-dimensional Walsh transform once in O(q² log q) integer additions and subtractions. Apply the one-dimensional Walsh transform to the q+1 slices to recover q times each line count, also in O(q² log q) operations. All intermediate magnitudes are bounded by q³, so fixed-width signed add/subtract networks with O(log q) Boolean gates per operation suffice. Test nonzero, OR with the corresponding point at infinity, and OR together all the infinity points for the remaining line. This proves the size bound. Finite-group Radon/Fourier identities have a long history. [Matúš and Flusser, 1993](https://doi.org/10.1109/34.254058)

For completeness one can limit negations without losing this asymptotic size. Sort the n bits with a padded Batcher sorting network; each comparator is one AND and one OR. The sorted Boolean vector gives all thresholds Tⱼ=[weight≥j]. Recover the exact weight indicators using one NOT at each of ceil(log₂(n+1)) binary decision levels. At a level, the unique live prefix selects its threshold Tⱼ. Compute the next bit as the OR over current prefix indicators AND their thresholds. Negate this bit once and use the bit and its complement to split every prefix. Missing thresholds beyond n are false. This takes O(n) positive gates over all levels and yields an indicator per possible weight. Their prefix sums using OR give every negated sorted bit.

Reverse the sorting network. For a comparator receiving a,b, let A=¬(a AND b) and B=¬(a OR b) be known from the reverse step. Then ¬a=B OR (A AND b), and ¬b=B OR (A AND a). All forward values remain available by fanout. Four positive gates per comparator suffice, so one has every negated raw input using O(n log²n) gates and the displayed NOT budget. Represent every subsequent circuit signal by a positive and negative wire. AND and OR use De Morgan’s identities, while NOT swaps the two references. This realizes the original Fourier circuit at a constant-factor overhead and adds no more NOT gates. Sorting-based inverter constructions precede this application. [Batcher, 1968](https://doi.org/10.1145/1468075.1468121) [Beals, Nishino and Tanaka](https://citeseerx.ist.psu.edu/document?doi=80b6bee408c5146f35a9048d42bb7190483e2e9e&repid=rep1&type=pdf)

The greedy small-extension argument and its application to private-gate charges are the points being investigated. The classical inversion, sorting and Fourier constructions are ingredients. Priority for the combined finite-plane lower bound has not been established.
