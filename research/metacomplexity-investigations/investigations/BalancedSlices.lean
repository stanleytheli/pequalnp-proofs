import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-! Parity masking, conditional histogram equality and signed extraction. -/
namespace MetaComplexity.BalancedSlices
open Finset
open scoped BigOperators

def signBit : Bool → ℤ
  | false => 1
  | true => -1

lemma signBit_not (b : Bool) : signBit (!b) = -signBit b := by cases b <;> decide

variable {I : Type*} [Fintype I] [DecidableEq I]

def phase (w : I → Bool) : ℤ := ∏ i, signBit (w i)
def flip (i : I) (w : I → Bool) : I → Bool := Function.update w i (!w i)

omit [Fintype I] in
lemma flip_twice (i : I) (w : I → Bool) : flip i (flip i w) = w := by
  funext j
  by_cases h : j=i
  · subst j
    simp [flip]
  · simp [flip, h]

def flipEquiv (i : I) : Equiv.Perm (I → Bool) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_twice i
  right_inv := flip_twice i

lemma phase_flip (i : I) (w : I → Bool) : phase (flip i w) = -phase w := by
  classical
  unfold phase
  rw [← Finset.mul_prod_erase univ (fun j => signBit (flip i w j)) (mem_univ i),
      ← Finset.mul_prod_erase univ (fun j => signBit (w j)) (mem_univ i)]
  have h : (∏ j ∈ univ.erase i, signBit (flip i w j)) =
      ∏ j ∈ univ.erase i, signBit (w j) := by
    apply prod_congr rfl
    intro j hj
    simp [flip,(mem_erase.mp hj).1]
  rw [h]
  simp [flip, signBit_not]

def level (B : ℤ) (marked : Bool) (w : I → Bool) : ℤ :=
  B + if marked then -phase w else phase w

theorem conditional_marginal (B : ℤ) (a : Bool) (i : I) (w : I → Bool) :
    level B a w + level B a (flip i w) = 2*B := by
  cases a <;> simp only [level, phase_flip, Bool.false_eq_true,
    ite_false, ite_true, neg_neg] <;> ring

theorem conditional_histogram {S : Type*} [AddCommMonoid S]
    (B : ℤ) (a : Bool) (i : I) (statistic : ℤ → S) :
    (∑ w : I → Bool, statistic (level B a w)) =
      ∑ w : I → Bool, statistic (level B false w) := by
  cases a with
  | false => rfl
  | true =>
    have point (w : I → Bool) :
        statistic (level B true w) = statistic (level B false (flipEquiv i w)) := by
      change statistic (level B true w) = statistic (level B false (flip i w))
      simp [level, phase_flip]
    simp_rw [point]
    exact Equiv.sum_comp (flipEquiv i) (fun w => statistic (level B false w))

section
variable {R S : Type*} [CommRing R] [CommRing S]

def mixture (A B U H V D : R) : R := (A+B)*U*V + (A-B)*H*D

theorem specialize (φ : R →+* S) (A B U H V D : R)
    (v : φ V=1) (d : φ D=1) :
    φ (mixture A B U H V D) - (φ A+φ B)*φ U = (φ A-φ B)*φ H := by
  simp [mixture, v, d]

theorem masked_difference (A B U H Q V D : R) :
    mixture A B U H V D - mixture A B U Q V D = (A-B)*(H-Q)*D := by
  unfold mixture
  ring
end
end MetaComplexity.BalancedSlices

#print axioms MetaComplexity.BalancedSlices.conditional_marginal
#print axioms MetaComplexity.BalancedSlices.conditional_histogram
#print axioms MetaComplexity.BalancedSlices.specialize
