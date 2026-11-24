import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Each one-coordinate flip bijects parity slices. A local cap on
the number of small neighbors of large centers bounds global success. -/
namespace MetaComplexity.ParityEdgeCount
open Finset
open scoped BigOperators
variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y] [DecidableEq Y]

def neighbors (flip : I → X ≃ Y) (small : Finset Y) (x : X) : ℕ :=
  ∑ i, if flip i x ∈ small then 1 else 0

theorem count (flip : I → X ≃ Y) (small : Finset Y) :
    (∑ x,neighbors flip small x)=Fintype.card I * small.card := by
  classical
  unfold neighbors
  rw [Finset.sum_comm]
  have one (i : I) : (∑ x, if flip i x∈small then 1 else 0 : ℕ)=small.card := by
    rw [Equiv.sum_comp (flip i) (fun y => if y∈small then (1:ℕ) else 0)]
    simp
  simp [one]

theorem edge_cap [DecidableEq X] (flip : I → X ≃ Y) (small : Finset Y)
    (large : Finset X) (B : ℕ) (cap : ∀x∈large, neighbors flip small x ≤ B) :
    Fintype.card I * small.card ≤
      Fintype.card I * (Fintype.card X - large.card) + B * large.card := by
  classical
  rw [←count flip small]
  have bound (x : X) : neighbors flip small x ≤ if x∈large then B else Fintype.card I := by
    split_ifs with h
    · exact cap x h
    · calc
        _ ≤ ∑ _i : I, (1:ℕ) := sum_le_sum (fun i _ => by split <;> decide)
        _ = _ := by simp
  calc
    _ ≤ ∑ x : X, (if x∈large then B else Fintype.card I) := sum_le_sum (fun x _=>bound x)
    _ = _ := by
      rw [←Finset.sum_sdiff (s₁:=large) (s₂:=univ) (f:=fun x => if x∈large then B else Fintype.card I) (subset_univ _)]
      have outside : (∑ x∈univ \ large, (if x∈large then B else Fintype.card I)) =
          ∑ _x∈univ \ large, Fintype.card I := by
        apply sum_congr rfl
        intro x hx
        simp [(mem_sdiff.mp hx).2]
      have inside : (∑ x∈large, (if x∈large then B else Fintype.card I)) =
          ∑ _x∈large, B := by
        apply sum_congr rfl
        intro x hx
        simp [hx]
      simp [inside,outside,Finset.card_sdiff_of_subset (subset_univ large),Nat.mul_comm,Nat.add_comm]
end MetaComplexity.ParityEdgeCount
#print axioms MetaComplexity.ParityEdgeCount.edge_cap
