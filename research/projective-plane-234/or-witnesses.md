# Counting physical OR gates in a monotone circuit

Let R be a set of input coordinates and Y a set disjoint from R. Say a wire is **sound for R** when every assignment on which it is true contains a true coordinate in R. Suppose a wire o in a monotone fan-in-two circuit is sound for R and is true on every test Y ∪ {p}, for p ∈ R. There are at least |R| − 1 physical OR gates, truncated at zero, each sound for R and true on at least two of those tests. The conclusion permits all fan-outs, empty gates, repeated operands and malformed references in the project's array circuit semantics. The theorem is `heavy_or997`.

Set X to the complement of R. A monotone wire is sound for R exactly when it is false at X. Start with the false output at X. Expand physical gates backwards, stopping outside the class G of sound gates that fire on two or more tests. A false AND needs one false antecedent; a false OR may need both. Expanding each slot once in decreasing wire order gives a boundary of at most one plus the number of physical OR gates in G. A repeated use of the same slot counts only once. An absent or forward wire always contributes false as an operand and costs no new gate.

Every boundary wire is false at X, hence sound. Each such wire fires on at most one test: an earlier gate firing twice would belong to G, a raw input sound for R belongs to R and fires at most once, and an out-of-range wire never fires. For every p ∈ R at least one boundary wire fires on Y ∪ {p}. Otherwise the entire false certificate persists at a test where o is true. The boundary therefore has at least |R| elements.

## Several output rows

Suppose |Rᵢ ∩ Rⱼ| ≤ 1 for distinct rows. Choose a base Yᵢ disjoint from each row Rᵢ, with the same output assumptions as above. For every i ≠ j assume Yᵢ misses Rⱼ or Yⱼ misses Rᵢ. A physical witness cannot serve two rows. For instance, if Yᵢ misses both, a slot sound for both and firing on two of the tests based at Yᵢ would put their two distinct added points in Rᵢ ∩ Rⱼ. The theorem `or_family997` therefore charges the sum of all row costs to distinct OR slots.

## An actual one-NOT circuit

Consider the original array circuit with one exceptional NOT, all other operations AND or OR with fan-in at most two. Let h be the value read by the NOT in the preceding physical prefix. On any input Y that makes h true, select any output subfamily of linearly intersecting rows all disjoint from Y. Then the original circuit contains at least the sum over this subfamily of |Rᵢ| − 1 OR gates.

To see this, pin the NOT output to false using an empty OR at the same slot. The pinned circuit lies pointwise below the original on each wire and agrees with it above Y, since h is monotone. Its output wires are therefore sound and pass all of the selected tests. The OR inserted at the NOT slot fires on no test, so it cannot be a private OR. Every remaining witness is an OR at the same slot in the original circuit. Row overlap is ruled out by the shared base condition above. The common-base statement is `physical_or_family997` in `PinnedOr997.lean`. The stronger `physical_or_oriented997` allows a separate true assignment for each row under the same pairwise orientation condition as the monotone theorem. Both permit empty and singleton rows. The projective-plane bound in the companion note uses a separate transparent-reader and sparse-certificate argument.
