import HallBlocks
import BraceReadout

namespace PositivePermanent.HallBlocks
variable {A B E C : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

open scoped Classical in
/-- Every category of a complete multigraph readout on a large Hall-plus-two
factor is integral affine on ordinary physical matching incidences. -/
theorem brace_affine_from_plus_two (row : E → A) (col : E → B) (N : A → Finset B)
    (cells : ∀ i j, j ∈ N i ↔ ∃ e, row e = i ∧ col e = j)
    (balance : Fintype.card A = Fintype.card B) (large : 4 ≤ Fintype.card A)
    (plus : PlusTwo N) (tag : E → Option C) (pure : BraceReadout.Pure tag (PhysicalMatching row col))
    (c : C) : ∃ (b : ℤ) (weight : E → ℤ), ∀ M, PhysicalMatching row col M →
      (if ∃ e ∈ M, tag e = some c then 1 else 0 : ℤ) = b + ∑ e ∈ M, weight e := by
  have ext : BraceReadout.Extend row col (PhysicalMatching row col) :=
    extend_two_physical row col N cells balance plus
  have ind : BraceReadout.Independent row col (PhysicalMatching row col) :=
    fun _ hm _ he _ hf ne => physical_independent hm he hf ne
  have deg := brace_degrees N large plus
  have avoid := BraceReadout.avoid_from_neighbors ind ext N (fun i j => (cells i j).mp) deg.1 deg.2
  exact BraceReadout.affine_readout ind ext avoid pure c

#print axioms brace_affine_from_plus_two
end PositivePermanent.HallBlocks
