import MidpointCNF
import Mathlib.Algebra.BigOperators.Field

namespace Midpoint
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

def corner (b : ℝ) (a : I→ℝ) (x : Finset I) : ℝ := b + ∑ i∈x,a i

def AffineTable (f : Finset I→ℝ) : Prop :=
  ∀ x, f x = corner (f ∅) (fun i=>f {i}-f ∅) x

omit [Fintype I] [DecidableEq I] in
lemma affine_corner (b : ℝ) (a : I→ℝ) : AffineTable (corner b a) := by
  intro x
  simp [corner]

omit [Fintype I] [DecidableEq I] in
lemma affine_ratio (f : Finset I→ℝ) (t : ℝ) (aff : AffineTable f) :
    AffineTable (fun x=>ratio (f x) t) := by
  intro x
  unfold ratio corner
  simp_rw [←sub_div]
  rw [←Finset.sum_div,←add_div]
  exact congrArg (fun a : ℝ=>a/t) (aff x)

omit [Fintype I] [DecidableEq I] in
lemma affine_limit (f : ℕ→Finset I→ℝ) (F : Finset I→ℝ) (aff : ∀ j,AffineTable (f j))
    (lim : ∀ x,Tendsto (fun j=>f j x) atTop (𝓝 (F x))) : AffineTable F := by
  intro x
  apply tendsto_nhds_unique (lim x)
  apply ((lim ∅).add (tendsto_finsetSum x (fun i _=>(lim {i}).sub (lim ∅)))).congr'
  exact Filter.Eventually.of_forall (fun j=>(aff j x).symm)

def least (a : I→ℝ) : Finset I := by classical exact Finset.univ.filter (fun i=>a i<0)
def literal (a : I→ℝ) (x : Finset I) (i : I) : Prop :=
  (0<a i ∧ i∈x) ∨ (a i<0 ∧ i∉x)

lemma corner_difference (b : ℝ) (a : I→ℝ) (x : Finset I) :
    corner b a x = corner b a (least a) +
      ∑ i, (if literal a x i then |a i| else 0) := by
  classical
  unfold corner
  rw [add_assoc]
  congr 1
  have sum_as (s : Finset I) : (∑ i∈s,a i) = ∑ i,if i∈s then a i else 0 := by
    simp [Finset.sum_ite_mem]
  rw [sum_as x,sum_as (least a)]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (a i) 0 with h|h|h
  · have z : ¬0<a i := not_lt.mpr h.le
    by_cases mem : i∈x <;> simp [least,literal,h,z,mem,abs_of_neg h]
  · by_cases mem : i∈x <;> simp [least,literal,h,mem]
  · have z : ¬a i<0 := not_lt.mpr h.le
    by_cases mem : i∈x <;> simp [least,literal,h,z,mem,abs_of_pos h]

/-- The positive support of any nonnegative affine corner table is a single
literal disjunction, with a possible always-true intercept. -/
theorem positive_clause (f : Finset I→ℝ) (aff : AffineTable f) (pos : ∀ x,0≤f x) :
    ∃ b : Prop, ∃ p n : Finset I, ∀ x,
      0<f x ↔ b ∨ (∃ i∈p,i∈x) ∨ (∃ i∈n,i∉x) := by
  classical
  let a := fun i : I=>f {i}-f ∅
  let m := f (least a)
  refine ⟨0<m,Finset.univ.filter (fun i=>0<a i),Finset.univ.filter (fun i=>a i<0),?_⟩
  intro x
  have eq : f x = m + ∑ i, (if literal a x i then |a i| else 0) := by
    rw [aff x,corner_difference,←aff (least a)]
  have nonneg (i : I) (_ : i∈Finset.univ) : 0≤(if literal a x i then |a i| else 0) := by
    split <;> positivity
  have piece (i : I) : 0<(if literal a x i then |a i| else 0) ↔ literal a x i := by
    by_cases h : literal a x i
    · simp only [iff_true_intro h,iff_true]
      rcases h with h|h
      · exact abs_pos.mpr h.1.ne'
      · exact abs_pos.mpr h.1.ne
    · simp [h]
  have add_iff (b s : ℝ) (hb : 0≤b) (hs : 0≤s) : 0<b+s ↔ 0<b ∨ 0<s := by
    constructor
    · intro h; by_cases z : 0<b
      · exact Or.inl z
      · exact Or.inr (by linarith)
    · rintro (h|h) <;> linarith
  rw [eq,add_iff _ _ (pos _) (Finset.sum_nonneg nonneg),Finset.sum_pos_iff_of_nonneg nonneg]
  apply or_congr_right
  constructor
  · rintro ⟨i,_,hi⟩
    rcases (piece i).mp hi with hp|hn
    · exact Or.inl ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.1⟩,hp.2⟩
    · exact Or.inr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn.1⟩,hn.2⟩
  · rintro (⟨i,hi,hm⟩|⟨i,hi,hm⟩)
    · exact ⟨i,Finset.mem_univ _,(piece i).mpr (Or.inl ⟨(Finset.mem_filter.mp hi).2,hm⟩)⟩
    · exact ⟨i,Finset.mem_univ _,(piece i).mpr (Or.inr ⟨(Finset.mem_filter.mp hi).2,hm⟩)⟩

end
end Midpoint
#print axioms Midpoint.affine_limit
#print axioms Midpoint.positive_clause
