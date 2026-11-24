# Binary clauses forced by antipodal paired support

Let a Boolean CNF on N variables have B clauses of width two and T clauses of width three. Each clause uses distinct underlying variables. Suppose two complementary satisfying assignments a and ¬a are each isolated, meaning that flipping any single coordinate makes the assignment fail. If each variable occurs at most three times, then

    2B + T ≥ 2N,       2B + 3T ≤ 3N,
    T ≤ N/2,           B ≥ 3N/4.

For the first inequality, fix one baseline. For each of its N single-coordinate flips, choose a clause which the flip falsifies. Its unique true literal before the flip must be the changed coordinate. A clause can witness at most one coordinate at this baseline. A binary clause can witness at most two across the two baselines. A ternary clause can witness at most one across them, because complementation exchanges its numbers of true and false literals. Thus at most 2B + T of the 2N witnesses are available. The second inequality counts all literal occurrences. Subtraction yields 2T ≤ N, and substitution gives 4B ≥ 3N.

Every assignment in a one-from-each-pair support is isolated in the full Boolean cube. Therefore this bound applies to the promised inputs with an accepted antipodal pair in the main reduction. In particular, replacing its binary clauses by width-three clauses on three distinct variables while maintaining maximum occurrence three, the paired support and the accepted antipodal pair is impossible. This counting argument concerns the physical CNF representation and does not require the arithmetic lower bound.

For arbitrary width-three CNFs with maximum occurrence three, an antipodal pair implies at least 2^ceil(N/14) satisfying assignments. Indeed, there are at most N clauses. At one baseline at most floor(N/2) clauses have exactly one true literal, so at least ceil(N/2) coordinates may be flipped individually. Join two such coordinates if they occur together in a clause. Each has at most six neighbors. The greedy independent-set bound gives at least ceil(N/14) of these coordinates with no pair sharing a clause. Every subset may be flipped simultaneously, since each clause sees at most one of these changes.
