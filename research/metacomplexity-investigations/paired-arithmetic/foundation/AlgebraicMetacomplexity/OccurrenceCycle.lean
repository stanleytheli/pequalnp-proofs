import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega

namespace AlgebraicMeta

/-- Binary implication clauses around one logical variable's copies force the
same bit throughout. Index 0 through n; the final clause joins n to 0. -/
theorem occurrence_cycle (n : ℕ) (bit : ℕ → Bool)
    (step : ∀ j, j < n → bit j ≤ bit (j+1)) (close : bit n ≤ bit 0) :
    ∀ j, j ≤ n → bit j = bit 0 := by
  have chain (i j : ℕ) (lo : i ≤ j) (hi : j ≤ n) : bit i ≤ bit j := by
    induction j with
    | zero =>
      have hz : i = 0 := by omega
      subst i
      exact le_rfl
    | succ j ih =>
      by_cases h : i = j+1
      · subst i
        exact le_rfl
      · exact le_trans (ih (by omega) (by omega)) (step j (by omega))
  intro j hj
  exact le_antisymm (le_trans (chain j n hj le_rfl) close) (chain 0 j (Nat.zero_le _) hj)

/-- Boolean complementation permits a different known baseline at each copy. -/
theorem signed_occurrence_cycle (n : ℕ) (bits flips : ℕ → Bool)
    (step : ∀ j, j < n → xor (bits j) (flips j) ≤ xor (bits (j+1)) (flips (j+1)))
    (close : xor (bits n) (flips n) ≤ xor (bits 0) (flips 0)) :
    ∃! logical : Bool, ∀ j, j ≤ n → xor (bits j) (flips j) = logical := by
  refine ⟨xor (bits 0) (flips 0), occurrence_cycle n _ step close, ?_⟩
  intro y hy
  exact (hy 0 (Nat.zero_le _)).symm

end AlgebraicMeta
#print axioms AlgebraicMeta.occurrence_cycle
#print axioms AlgebraicMeta.signed_occurrence_cycle
