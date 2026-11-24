import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-! A sufficient set of numerical corner tests for an exact support family:
tests on each witness, its single deletions and the total mass at all ones. -/
namespace PositivePermanent.Corner
open Finset
open scoped BigOperators
noncomputable section
variable {A I : Type*} [Fintype A] [DecidableEq I]

def atCorner (support : A→Finset I) (weight : A→ℝ) (x : Finset I) : ℝ :=
  ∑ a, if support a⊆x then weight a else 0

lemma corner_le (support : A→Finset I) (weight : A→ℝ) (pos : ∀ a,0<weight a)
    (x : Finset I) (a : A) (h : support a⊆x) : weight a≤atCorner support weight x := by
  classical
  have lower := Finset.single_le_sum (f:=fun b=>if support b⊆x then weight b else 0)
    (fun b (_ : b∈Finset.univ)=>by split <;> simp [(pos b).le]) (Finset.mem_univ a)
  simpa [atCorner,h] using lower

lemma supported_witness (support : A→Finset I) (weight : A→ℝ) (pos : ∀ a,0<weight a)
    (H : Finset I) (deletions : ∀ i∈H,atCorner support weight (H.erase i)=0)
    (a : A) (ha : support a⊆H) : support a=H := by
  apply Finset.Subset.antisymm ha
  intro i hi
  by_contra missing
  have sub : support a⊆H.erase i := Finset.subset_erase.mpr ⟨ha,missing⟩
  have le := corner_le support weight pos (H.erase i) a sub
  rw [deletions i hi] at le
  exact (pos a).not_ge le

lemma pure_corner (support : A→Finset I) (weight : A→ℝ) (pos : ∀ a,0<weight a)
    (H : Finset I) (del : ∀ i∈H,atCorner support weight (H.erase i)=0) :
    atCorner support weight H = ∑ a,if support a=H then weight a else 0 := by
  unfold atCorner
  apply Finset.sum_congr rfl
  intro a _
  by_cases sub : support a⊆H
  · simp [sub,supported_witness support weight pos H del a sub]
  · have ne : support a≠H := fun eq=>sub eq.le
    simp [sub,ne]

theorem mass_exhausts (support : A→Finset I) (weight : A→ℝ) (pos : ∀ a,0<weight a)
    (F : Finset (Finset I)) (del : ∀ H∈F,∀ i∈H,atCorner support weight (H.erase i)=0)
    (mass : (∑ H∈F,atCorner support weight H) = ∑ a,weight a)
    (cover : ∀ H∈F,0<atCorner support weight H) :
    (∀ a,support a∈F) ∧ (∀ H∈F,∃ a,support a=H) := by
  classical
  have eq : (∑ H∈F,atCorner support weight H) = ∑ a,if support a∈F then weight a else 0 := by
    calc
      _ = ∑ H∈F,∑ a,if support a=H then weight a else 0 :=
        Finset.sum_congr rfl (fun H h=>pure_corner support weight pos H (del H h))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        simp [Finset.sum_ite_eq]
  rw [eq] at mass
  constructor
  · intro a
    by_contra out
    have lt : (∑ b : A,if support b∈F then weight b else 0) < ∑ b,weight b := by
      apply Finset.sum_lt_sum
      · intro b _; split <;> simp [(pos b).le]
      · exact ⟨a,Finset.mem_univ a,by simp [out,pos]⟩
    exact (ne_of_lt lt) mass
  · intro H h
    by_contra none
    push Not at none
    have z := pure_corner support weight pos H (del H h)
    simp [none] at z
    linarith [cover H h]

end
end PositivePermanent.Corner
#print axioms PositivePermanent.Corner.mass_exhausts
