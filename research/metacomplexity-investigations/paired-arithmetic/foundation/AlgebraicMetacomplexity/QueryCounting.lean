import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AlgebraicMeta
open Finset

/-- With at most u hidden worlds per probe, a given no-hit transcript's
queries can distinguish no more than q·u worlds from the baseline. -/
theorem transcript_bound {Q W : Type*} [DecidableEq W]
    (queries : Finset Q) (changed : Q → Finset W) (u : ℕ)
    (capacity : ∀ i∈queries, (changed i).card ≤ u) :
    (queries.biUnion changed).card ≤ queries.card * u :=
  Finset.card_biUnion_le_card_mul queries changed u capacity

/-- Double-counting the incidence graph equates the world/point densities.
This statement permits many relabellings producing the same changed support. -/
theorem regular_incidence {Q W : Type*} (slots : Finset Q) (worlds : Finset W)
    (hit : Q → W → Bool) (perSlot perWorld : ℕ)
    (columns : ∀ q∈slots, (worlds.filter (fun w => hit q w)).card = perSlot)
    (rows : ∀ w∈worlds, (slots.filter (fun q => hit q w)).card = perWorld) :
    slots.card * perSlot = worlds.card * perWorld := by
  classical
  calc
    slots.card * perSlot = ∑ q∈slots, ∑ w∈worlds, if hit q w then 1 else 0 := by
      symm
      apply Finset.sum_const_nat
      intro q hq
      simpa only [Finset.sum_boole,Nat.cast_id] using columns q hq
    _ = ∑ w∈worlds, ∑ q∈slots, if hit q w then 1 else 0 := Finset.sum_comm
    _ = worlds.card * perWorld := by
      apply Finset.sum_const_nat
      intro w hw
      simpa only [Finset.sum_boole,Nat.cast_id] using rows w hw

end AlgebraicMeta
#print axioms AlgebraicMeta.transcript_bound
#print axioms AlgebraicMeta.regular_incidence
