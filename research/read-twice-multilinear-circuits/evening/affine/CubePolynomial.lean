import ReadOnce
import Mathlib.Combinatorics.Nullstellensatz

/-! Unique multilinear extension over every field, including F₂. -/
namespace SparseAffine.Cube
open MvPolynomial
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

def basis (b : V → Bool) : MvPolynomial V K :=
  ∏ v, ReadOnce.bernoulli (X v) (b v)

def extension (f : (V → Bool) → Bool) : MvPolynomial V K :=
  ∑ b, if f b then basis b else 0

theorem eval_basis (p : V → K) (b : V → Bool) :
    eval p (basis b) = ReadOnce.weight p b := by
  unfold basis ReadOnce.weight
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro v _
  cases b v <;> simp [ReadOnce.bernoulli]

theorem eval_extension (p : V → K) (f : (V → Bool) → Bool) :
    eval p (extension f) = ReadOnce.expectation p f := by
  unfold extension ReadOnce.expectation
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  cases f b <;> simp [eval_basis,ReadOnce.indicator]

theorem weight_at_bit (b z : V → Bool) :
    ReadOnce.weight (fun i => (ReadOnce.indicator (b i) : K)) z = if b=z then 1 else 0 := by
  classical
  by_cases eq : b=z
  · subst z
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    cases hb : b i <;> simp [hb,ReadOnce.bernoulli,ReadOnce.indicator]
  · rw [if_neg eq]
    obtain ⟨i,h⟩ := Function.ne_iff.mp eq
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hb : b i <;> cases hz : z i <;> simp_all [ReadOnce.bernoulli,ReadOnce.indicator]

theorem corners (f : (V → Bool) → Bool) (b : V → Bool) :
    eval (fun i => (ReadOnce.indicator (b i) : K)) (extension f) = ReadOnce.indicator (f b) := by
  classical
  rw [eval_extension]
  simp [ReadOnce.expectation,weight_at_bit,ite_mul]

theorem degree_basis (b : V → Bool) (i : V) : degreeOf i (basis (K:=K) b) ≤ 1 := by
  classical
  unfold basis
  apply (degreeOf_prod_le i _ _).trans
  calc
    _ ≤ ∑ j : V, (if i=j then 1 else 0 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      cases b j with
      | true => simp [ReadOnce.bernoulli,degreeOf_X]
      | false =>
        change degreeOf i (1-X j : MvPolynomial V K) ≤ _
        exact (degreeOf_sub_le _ _ _).trans (by simp [degreeOf_X])
    _ = 1 := by simp

theorem multilinear (f : (V → Bool) → Bool) (i : V) : degreeOf i (extension (K:=K) f) ≤ 1 := by
  classical
  apply (degreeOf_sum_le i _ _).trans
  apply Finset.sup_le
  intro b _
  cases f b <;> simp [degree_basis]

theorem unique (f : (V→Bool)→Bool) (p : MvPolynomial V K)
    (multi : ∀ i, degreeOf i p ≤ 1)
    (agree : ∀ b, eval (fun i => ReadOnce.indicator (b i)) p = ReadOnce.indicator (f b)) :
    p = extension f := by
  classical
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero_at_prod_finset _ (fun _ => {0,1})
  · intro i
    have deg := degreeOf_sub_le i p (extension (K:=K) f)
    have bound := (deg.trans (max_le (multi i) (multilinear f i)))
    simpa using (show degreeOf i (p-extension f)<2 by omega)
  · intro x hx
    let b := fun i => decide (x i=1)
    have eq : x=fun i => ReadOnce.indicator (b i) := by
      funext i
      have hi : x i=0 ∨ x i=1 := by simpa using hx i
      rcases hi with h|h <;> simp [b,h,ReadOnce.indicator]
    rw [eq,map_sub,agree,corners,sub_self]

end
end SparseAffine.Cube
#print axioms SparseAffine.Cube.multilinear
#print axioms SparseAffine.Cube.unique
