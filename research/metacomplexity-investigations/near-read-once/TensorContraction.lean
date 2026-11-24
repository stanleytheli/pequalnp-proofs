import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring

/-! Exact contraction and ternary-grid identity tests for products of Boolean
multilinear interpolants. These identities concern semantic truth-value tensors. -/
namespace NearReadOnce.Tensor

open Finset

noncomputable section

variable {I J B D R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype B] [Fintype D] [CommSemiring R]

/-- Evaluate a Boolean (or any finite-alphabet) tensor in a product basis. -/
def evalTensor (T : (I → B) → R) (K : I → B → R) : R :=
  ∑ x : I → B, T x * ∏ i, K i (x i)

private theorem expand_product (T : J → (I → B) → R) (K : I → B → R) :
    ∏ j, evalTensor (T j) K =
    ∑ X : J → I → B, (∏ j, T j (X j)) * ∏ i, ∏ j, K i (X j i) := by
  classical
  unfold evalTensor
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro X _
  rw [Finset.prod_mul_distrib, Finset.prod_comm (s := (univ : Finset J))]

/-- Sum out each grid coordinate locally after expanding simultaneous tensor copies. -/
theorem contract (T : J → (I → B) → R) (K : I → D → B → R) (W : I → D → R) :
    ∑ z : I → D, (∏ i, W i (z i)) * ∏ j, evalTensor (T j) (fun i => K i (z i)) =
    ∑ X : J → I → B, (∏ j, T j (X j)) * ∏ i, ∑ v, W i v * ∏ j, K i v (X j i) := by
  classical
  simp_rw [expand_product, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro X _
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro z _
  rw [Finset.prod_mul_distrib]
  ac_rfl

def bitWeight {K : Type*} [Ring K] (z : K) (x : Bool) := if x then z else 1-z

def weightByCount : Nat → Int
  | 0 => 2
  | 1 => -2
  | 2 => 4
  | 3 => -8
  | _ => 17

/-- Four Boolean copies integrated over the three integer interpolation points. -/
theorem four_local_weights : ∀ bits : Fin 4 → Bool,
    (∑ v : Fin 3, ∏ j : Fin 4, bitWeight (v.val : Int) (bits j)) =
    weightByCount (∑ j, if bits j then 1 else 0) := by decide

/-- The actual four-copy signed count; there are 16 possible words per physical wire. -/
theorem four_copy_contraction (T : Fin 4 → (I → Bool) → Int) :
    ∑ z : I → Fin 3, ∏ j, evalTensor (T j) (fun i => bitWeight ((z i).val : Int)) =
    ∑ X : Fin 4 → I → Bool, (∏ j, T j (X j)) *
      ∏ i, weightByCount (∑ j, if X j i then 1 else 0) := by
  classical
  have h := contract T (fun (_ : I) (v : Fin 3) => bitWeight (v.val : Int)) (fun _ _ => 1)
  simpa only [Finset.prod_const_one, one_mul, four_local_weights] using h

def lagrange (x : Rat) (v : Fin 3) : Rat :=
  if v = 0 then (x-1)*(x-2)/2 else if v = 1 then x*(2-x) else x*(x-1)/2

private theorem quadratic_local (x : Rat) (bits : Fin 2 → Bool) :
    (∑ v : Fin 3, lagrange x v * ∏ j : Fin 2, bitWeight (v.val : Rat) (bits j)) =
    ∏ j : Fin 2, bitWeight x (bits j) := by
  cases h₀ : bits 0 <;> cases h₁ : bits 1 <;>
    simp [Fin.sum_univ_succ, Fin.prod_univ_succ, lagrange, bitWeight, h₀, h₁] <;> ring

/-- Multiquadratic interpolation applied to a product of two multilinear tensors. -/
theorem interpolate_two (T : Fin 2 → (I → Bool) → Rat) (x : I → Rat) :
    (∑ z : I → Fin 3, (∏ i, lagrange (x i) (z i)) *
      ∏ j, evalTensor (T j) (fun i => bitWeight ((z i).val : Rat))) =
    ∏ j, evalTensor (T j) (fun i => bitWeight (x i)) := by
  classical
  rw [contract T (fun (_ : I) (v : Fin 3) => bitWeight (v.val : Rat))
    (fun i v => lagrange (x i) v), expand_product]
  simp only [quadratic_local]

/-- Equality of two tensor products on the ternary grid suffices everywhere over Q. -/
theorem equality_of_grid (A B : Fin 2 → (I → Bool) → Rat)
    (h : ∀ z : I → Fin 3,
      (∏ j, evalTensor (A j) (fun i => bitWeight ((z i).val : Rat))) =
       ∏ j, evalTensor (B j) (fun i => bitWeight ((z i).val : Rat)))
    (x : I → Rat) : (∏ j, evalTensor (A j) (fun i => bitWeight (x i))) =
      ∏ j, evalTensor (B j) (fun i => bitWeight (x i)) := by
  rw [← interpolate_two A x, ← interpolate_two B x]
  simp_rw [h]

/-- A zero sum of squared commutators on this grid proves a global product identity. -/
theorem equality_of_zero_energy (A B : Fin 2 → (I → Bool) → Rat)
    (h : (∑ z : I → Fin 3,
      ((∏ j, evalTensor (A j) (fun i => bitWeight ((z i).val : Rat))) -
       (∏ j, evalTensor (B j) (fun i => bitWeight ((z i).val : Rat))))^2) = 0)
    (x : I → Rat) : (∏ j, evalTensor (A j) (fun i => bitWeight (x i))) =
      ∏ j, evalTensor (B j) (fun i => bitWeight (x i)) := by
  classical
  apply equality_of_grid A B _ x
  intro z
  let d (z : I → Fin 3) :=
    (∏ j, evalTensor (A j) (fun i => bitWeight ((z i).val : Rat))) -
    (∏ j, evalTensor (B j) (fun i => bitWeight ((z i).val : Rat)))
  change (∑ z, d z ^ 2) = 0 at h
  have hle := Finset.single_le_sum (s := univ) (f := fun z => d z ^ 2)
    (fun i _ => sq_nonneg (d i)) (mem_univ z)
  rw [h] at hle
  have hz : d z ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end
end NearReadOnce.Tensor

#print axioms NearReadOnce.Tensor.four_copy_contraction
#print axioms NearReadOnce.Tensor.equality_of_zero_energy
