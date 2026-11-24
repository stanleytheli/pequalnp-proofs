import SupportLimit
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Compactness.Compact

namespace Midpoint
open Filter
open scoped Topology BigOperators
noncomputable section

lemma finite_extract {I : Type*} [Fintype I] (s : ℕ→I→ℝ) (M : ℝ)
    (range : ∀ j i,0≤s j i ∧ s j i≤M) :
    ∃ w : I→ℝ, ∃ φ : ℕ→ℕ, StrictMono φ ∧ (∀ i,0≤w i) ∧
      ∀ i, Tendsto (fun j=>s (φ j) i) atTop (𝓝 (w i)) := by
  let box : Set (I→ℝ) := Set.univ.pi (fun _ => Set.Icc 0 M)
  have comp : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  have stay (j : ℕ) : s j ∈ box := fun i _ => range j i
  obtain ⟨w,hw,φ,mono,lim⟩ := comp.tendsto_subseq stay
  refine ⟨w,φ,mono,fun i => (hw i (Set.mem_univ i)).1,?_⟩
  exact fun i=> (continuous_apply i).continuousAt.tendsto.comp lim

def ratio (x a : ℝ) := x/a

lemma ratio_bounds {x a : ℝ} (zero : 0≤x) (a0 : 0≤a) (upper : x≤2*a) :
    0≤ratio x a ∧ ratio x a≤2 ∧ a*(ratio x a)=x := by
  by_cases az : a=0
  · subst a
    have : x=0 := by linarith
    simp [this,ratio]
  · have ap := lt_of_le_of_ne a0 (Ne.symm az)
    exact ⟨div_nonneg zero a0,(div_le_iff₀ ap).mpr upper,by unfold ratio; rw [mul_div_assoc',mul_comm a x,mul_div_cancel_right₀ _ az]⟩

abbrev Sample (L R X : Type*) := (L×X) ⊕ (R×X) ⊕ Omitted L R

variable {L R X : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [Fintype X]

/-- The physical midpoint bounds every cover event. All normalized corner
parameters and all legal cover weights admit one common subsequence. -/
theorem midpoint_extract (edge : L→R→Prop) (c : ℕ→ℝ) (a : ℕ→L→ℝ) (b : ℕ→R→ℝ)
    (u : ℕ→L→X→ℝ) (v : ℕ→R→X→ℝ) (M : ℝ) (cs : ∀ j,0≤c j)
    (ba : ∀ j i,0≤a j i ∧ a j i≤1) (bb : ∀ j i,0≤b j i ∧ b j i≤1)
    (bu : ∀ j i x,0≤u j i x ∧ u j i x≤2*a j i)
    (bv : ∀ j i x,0≤v j i x ∧ v j i x≤2*b j i)
    (bound : ∀ j,c j*prob edge (a j) (b j) ≤ M) :
    ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃ D : L→X→ℝ, ∃ E : R→X→ℝ, ∃ w : Omitted L R→ℝ,
      (∀ i x,0≤D i x) ∧ (∀ i x,0≤E i x) ∧ (∀ A,0≤w A) ∧
      (∀ i x,Tendsto (fun j=>ratio (u (φ j) i x) (a (φ j) i)) atTop (𝓝 (D i x))) ∧
      (∀ i x,Tendsto (fun j=>ratio (v (φ j) i x) (b (φ j) i)) atTop (𝓝 (E i x))) ∧
      (∀ A,Legal edge A → Tendsto (fun j=>c (φ j)*event A (a (φ j)) (b (φ j))) atTop (𝓝 (w A))) := by
  classical
  let s (j : ℕ) : Sample L R X → ℝ
    | .inl (i,x) => ratio (u j i x) (a j i)
    | .inr (.inl (i,x)) => ratio (v j i x) (b j i)
    | .inr (.inr A) => if Legal edge A then c j * event A (a j) (b j) else 0
  have range (j) (i) : 0≤s j i ∧ s j i≤max 2 M := by
    rcases i with ⟨l,x⟩ | ⟨r,x⟩ | A
    · have h := ratio_bounds (bu j l x).1 (ba j l).1 (bu j l x).2
      exact ⟨h.1,h.2.1.trans (le_max_left _ _)⟩
    · have h := ratio_bounds (bv j r x).1 (bb j r).1 (bv j r x).2
      exact ⟨h.1,h.2.1.trans (le_max_left _ _)⟩
    · by_cases legal : Legal edge A
      · simp only [s,ite_eq_left legal]
        exact ⟨mul_nonneg (cs _) (mul_nonneg (factor_nonneg _ _ (fun l=>(ba j l).1))
          (factor_nonneg _ _ (fun r=>(bb j r).1))),
          ((mul_le_mul_of_nonneg_left (event_le_prob edge A legal _ _ (ba j) (bb j)) (cs j)).trans (bound j)).trans (le_max_right _ _)⟩
      · simp [s,legal]
  obtain ⟨z,φ,mono,nn,lim⟩ := finite_extract s (max 2 M) range
  refine ⟨φ,mono,(fun i x=>z (.inl (i,x))),(fun i x=>z (.inr (.inl (i,x)))),
    (fun A=>z (.inr (.inr A))),fun i x=>nn _,fun i x=>nn _,fun A=>nn _,fun i x=>lim _,fun i x=>lim _,?_⟩
  intro A legal
  simpa only [s,ite_eq_left legal] using lim (.inr (.inr A))

end
end Midpoint
#print axioms Midpoint.midpoint_extract
