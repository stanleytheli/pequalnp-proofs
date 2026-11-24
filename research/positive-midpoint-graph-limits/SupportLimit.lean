import EventBounds
import Mathlib.Topology.Algebra.Monoid

namespace Midpoint
open Filter
open scoped Topology BigOperators
noncomputable section
variable {I L R : Type*} [Fintype I] [DecidableEq I] [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

lemma factor_mul (a : Finset I) (u d : I→ℝ) :
    factor a (fun i => u i*d i) = factor a u*factor a d := by
  simp only [factor,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : i∈a <;> simp [h]

lemma event_split (a : Omitted L R) (u d : L→ℝ) (v e : R→ℝ) :
    event a (fun i => u i*d i) (fun r => v r*e r) = event a u v * event a d e := by
  simp only [event,factor_mul]; ring

lemma factor_cont (a : Finset I) (d : ℕ→I→ℝ) (D : I→ℝ)
    (lim : ∀ i,Tendsto (fun j=>d j i) atTop (𝓝 (D i))) :
    Tendsto (fun j=>factor a (d j)) atTop (𝓝 (factor a D)) := by
  apply tendsto_finsetProd
  intro i _
  by_cases h : i∈a
  · simp only [if_pos h]; exact tendsto_const_nhds
  · simpa only [if_neg h] using lim i

lemma factor_nonneg (a : Finset I) (d : I→ℝ) (pos : ∀ i,0≤d i) : 0≤factor a d := by
  apply Finset.prod_nonneg
  intro i _
  split <;> first | positivity | exact pos i

def forbidden (d : I→ℝ) : Finset I := by classical exact Finset.univ.filter (fun i=>d i=0)

lemma factor_pos_iff (a : Finset I) (d : I→ℝ) (pos : ∀ i,0≤d i) :
    0<factor a d ↔ forbidden d⊆a := by
  classical
  constructor
  · intro p i hi
    have zero : d i=0 := (Finset.mem_filter.mp hi).2
    by_contra h
    have z : factor a d=0 := Finset.prod_eq_zero
      (f:=fun j=>if j∈a then 1 else d j) (Finset.mem_univ i) (by simp [h,zero])
    rw [z] at p
    exact lt_irrefl _ p
  · intro sub
    apply Finset.prod_pos
    intro i _
    by_cases h : i∈a
    · simp [h]
    · have nz : d i≠0 := fun z => h (sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z⟩))
      simpa [h] using lt_of_le_of_ne (pos i) (Ne.symm nz)

/-- Along a common convergent subsequence the pointwise graph probability
has positive limit exactly for the pins feasible in the positive-cover lattice. -/
theorem support_limit (edge : L→R→Prop) (c : ℕ→ℝ) (u d : ℕ→L→ℝ) (v e : ℕ→R→ℝ)
    (D : L→ℝ) (E : R→ℝ) (w : Omitted L R→ℝ) (f : ℝ)
    (cs : ∀ j,0≤c j) (ds : ∀ i,0≤D i) (es : ∀ i,0≤E i)
    (wu : ∀ a,Legal edge a → 0≤w a)
    (bu : ∀ j i,0≤u j i*d j i ∧ u j i*d j i≤1)
    (bv : ∀ j i,0≤v j i*e j i ∧ v j i*e j i≤1)
    (ld : ∀ i,Tendsto (fun j=>d j i) atTop (𝓝 (D i)))
    (le_ : ∀ i,Tendsto (fun j=>e j i) atTop (𝓝 (E i)))
    (lw : ∀ a,Legal edge a → Tendsto (fun j=>c j*event a (u j) (v j)) atTop (𝓝 (w a)))
    (lf : Tendsto (fun j=> c j * prob edge (fun i=>u j i*d j i) (fun i=>v j i*e j i)) atTop (𝓝 f)) :
    0<f ↔ Feasible {a | Legal edge a ∧ 0<w a} (forbidden D) (forbidden E) := by
  classical
  let value (a : Omitted L R) := w a*event a D E
  have nonneg (a) (ha : a∈covers edge) : 0≤value a := mul_nonneg (wu a ((mem_covers edge a).mp ha))
    (mul_nonneg (factor_nonneg _ _ ds) (factor_nonneg _ _ es))
  have conv (a) (ha : a∈covers edge) :
      Tendsto (fun j => c j*event a (fun i=>u j i*d j i) (fun i=>v j i*e j i)) atTop (𝓝 (value a)) := by
    simp only [event_split,←mul_assoc]
    exact (lw a ((mem_covers edge a).mp ha)).mul ((factor_cont _ _ _ ld).mul (factor_cont _ _ _ le_))
  have lower (a) (ha : a∈covers edge) : value a ≤ f :=
    le_of_tendsto_of_tendsto' (conv a ha) lf (fun j => mul_le_mul_of_nonneg_left
      (event_le_prob edge a ((mem_covers edge a).mp ha) _ _ (bu j) (bv j)) (cs j))
  have upper : f ≤ ∑ a∈covers edge, value a := by
    apply le_of_tendsto_of_tendsto' lf (tendsto_finsetSum (covers edge) conv)
    intro j
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (prob_le_events edge _ _ (bu j) (bv j)) (cs j)
  constructor
  · intro pos
    obtain ⟨a,ha,pa⟩ := (Finset.sum_pos_iff_of_nonneg nonneg).mp (pos.trans_le upper)
    have legal := (mem_covers edge a).mp ha
    have coverPos : 0<w a := pos_of_mul_pos_left pa (mul_nonneg (factor_nonneg _ _ ds) (factor_nonneg _ _ es))
    have eventPos : 0<event a D E := pos_of_mul_pos_right pa (wu a legal)
    exact ⟨a,⟨legal,coverPos⟩,(factor_pos_iff _ _ ds).mp (pos_of_mul_pos_left eventPos (factor_nonneg _ _ es)),
      (factor_pos_iff _ _ es).mp (pos_of_mul_pos_right eventPos (factor_nonneg _ _ ds))⟩
  · rintro ⟨a,⟨legal,coverPos⟩,left,right⟩
    exact (mul_pos coverPos (mul_pos ((factor_pos_iff _ _ ds).mpr left) ((factor_pos_iff _ _ es).mpr right))).trans_le
      (lower a ((mem_covers edge a).mpr legal))

end
end Midpoint
#print axioms Midpoint.support_limit
