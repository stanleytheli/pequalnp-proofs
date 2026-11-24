import GoodCovers
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Finite sums for the Bernoulli no-edge event and its cover-event sandwich. -/
namespace Midpoint
open scoped BigOperators
noncomputable section
variable {I L R : Type*} [Fintype I] [DecidableEq I] [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

def chosen (b : I→Bool) : Finset I := Finset.univ.filter fun i => b i

def bitMass (q : ℝ) (b : Bool) : ℝ := if b then 1-q else q

def config (q : I→ℝ) (b : I→Bool) := ∏ i, bitMass (q i) (b i)

def clipped (A : Finset I) (q : I→ℝ) (b : I→Bool) :=
  ∏ i, if i∈A ∨ b i=false then bitMass (q i) (b i) else 0

lemma clipped_eq (A : Finset I) (q : I→ℝ) (b : I→Bool) :
    clipped A q b = if chosen b ⊆ A then config q b else 0 := by
  classical
  by_cases ok : chosen b ⊆ A
  · rw [if_pos ok]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : b i=true
    · have hi : i∈A := ok (by simp [chosen,h])
      simp [hi]
    · simp [Bool.eq_false_iff.mpr h]
  · rw [if_neg ok]
    obtain ⟨i,hi,ha⟩ := Finset.not_subset.mp ok
    have hb : b i=true := (Finset.mem_filter.mp hi).2
    exact Finset.prod_eq_zero (f:=fun j => if j∈A ∨ b j=false then bitMass (q j) (b j) else 0)
      (Finset.mem_univ i) (by simp [ha,hb])

lemma factor_expand (A : Finset I) (q : I→ℝ) : factor A q = ∑ b : I→Bool, clipped A q b := by
  unfold factor clipped
  rw [←Fintype.prod_sum (fun i b => if i∈A ∨ b=false then bitMass (q i) b else 0)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i∈A <;> simp [Fintype.sum_bool,bitMass,hi]

lemma nonneg_config (q : I→ℝ) (bound : ∀ i,0≤q i ∧ q i≤1) (b : I→Bool) : 0≤config q b := by
  apply Finset.prod_nonneg
  intro i _
  cases h : b i <;> simp [bitMass,h,(bound i).1,(bound i).2]

lemma nonneg_clipped (A : Finset I) (q : I→ℝ) (bound : ∀ i,0≤q i ∧ q i≤1) (b : I→Bool) : 0≤clipped A q b := by
  rw [clipped_eq]
  split
  · exact nonneg_config _ bound _
  · rfl

def covers (edge : L→R→Prop) : Finset (Omitted L R) := by classical exact Finset.univ.filter (Legal edge)

lemma mem_covers (edge : L→R→Prop) (a : Omitted L R) : a∈covers edge ↔ Legal edge a := by
  classical
  simp [covers]

def prob (edge : L→R→Prop) (u : L→ℝ) (v : R→ℝ) : ℝ := by
  classical exact ∑ x : L→Bool, ∑ y : R→Bool,
    if Legal edge (chosen x,chosen y) then config u x * config v y else 0

lemma expand_event (a : Omitted L R) (u : L→ℝ) (v : R→ℝ) :
    event a u v = ∑ x : L→Bool, ∑ y : R→Bool, clipped a.1 u x * clipped a.2 v y := by
  unfold event
  rw [factor_expand,factor_expand,Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem event_le_prob (edge : L→R→Prop) (a : Omitted L R) (ha : Legal edge a)
    (u : L→ℝ) (v : R→ℝ) (bu : ∀ i,0≤u i ∧ u i≤1) (bv : ∀ j,0≤v j ∧ v j≤1) :
    event a u v ≤ prob edge u v := by
  classical
  rw [expand_event,prob]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  have nonneg := mul_nonneg (nonneg_config u bu x) (nonneg_config v bv y)
  have yes (hx : chosen x⊆a.1) (hy : chosen y⊆a.2) : Legal edge (chosen x,chosen y) :=
    fun l hl r hr => ha l (hx hl) r (hy hr)
  by_cases ok : Legal edge (chosen x,chosen y)
  · by_cases hx : chosen x⊆a.1 <;> by_cases hy : chosen y⊆a.2 <;> simp [clipped_eq,hx,hy,ok,nonneg]
  · by_cases hx : chosen x⊆a.1
    · have hy : ¬chosen y⊆a.2 := fun hy => ok (yes hx hy)
      simp [clipped_eq,hx,hy,ok]
    · simp [clipped_eq,hx,ok]

theorem prob_le_events (edge : L→R→Prop) (u : L→ℝ) (v : R→ℝ)
    (bu : ∀ i,0≤u i ∧ u i≤1) (bv : ∀ j,0≤v j ∧ v j≤1) :
    prob edge u v ≤ ∑ a∈covers edge, event a u v := by
  classical
  simp_rw [expand_event]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=covers edge) (t:=(Finset.univ : Finset (R→Bool)))]
  unfold prob
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  have nneg (a : Omitted L R) (_ : a∈covers edge) : 0≤clipped a.1 u x*clipped a.2 v y :=
    mul_nonneg (nonneg_clipped _ _ bu _) (nonneg_clipped _ _ bv _)
  by_cases valid : Legal edge (chosen x,chosen y)
  · rw [if_pos valid]
    have member := (mem_covers edge (chosen x,chosen y)).mpr valid
    simpa only [clipped_eq,Finset.Subset.rfl,ite_true] using Finset.single_le_sum nneg member
  · rw [if_neg valid]
    exact Finset.sum_nonneg nneg

end
end Midpoint
#print axioms Midpoint.event_le_prob
#print axioms Midpoint.prob_le_events
