import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Two finite distributions with the same cut-edge marginal have a joint
distribution supported on compatible perfect-matching choices. Its two linear
projections give exactly the requested local distributions. -/
namespace PositivePermanent.Cut
open Finset
open scoped BigOperators
noncomputable section

variable {A B I : Type*} [Fintype A] [Fintype B] [DecidableEq I]
def marginal (l : A→I) (a : A→ℝ) (i : I) : ℝ :=
  ∑ u,if l u=i then a u else 0

lemma marginal_nonneg (l : A→I) (a : A→ℝ) (nn : ∀ u,0≤a u) (i) : 0≤marginal l a i :=
  Finset.sum_nonneg (fun u _=>by split <;> simp [nn])

lemma le_marginal (l : A→I) (a : A→ℝ) (nn : ∀ u,0≤a u) (u : A) : a u≤marginal l a (l u) := by
  classical
  have h := Finset.single_le_sum (f:=fun v=>if l v=l u then a v else 0)
    (fun v (_ : v∈Finset.univ)=>by split <;> simp [nn]) (Finset.mem_univ u)
  simpa [marginal] using h

def join (l : A→I) (r : B→I) (a : A→ℝ) (b : B→ℝ) (u : A) (v : B) : ℝ :=
  if l u=r v then a u*b v/marginal l a (l u) else 0

lemma join_nonneg (l : A→I) (r : B→I) (a : A→ℝ) (b : B→ℝ)
    (ha : ∀ u,0≤a u) (hb : ∀ v,0≤b v) (u v) : 0≤join l r a b u v := by
  unfold join
  split
  · exact div_nonneg (mul_nonneg (ha u) (hb v)) (marginal_nonneg l a ha _)
  · exact le_rfl

lemma join_left (l : A→I) (r : B→I) (a : A→ℝ) (b : B→ℝ) (ha : ∀ u,0≤a u)
    (same : ∀ i,marginal l a i=marginal r b i) (u) : (∑ v,join l r a b u v)=a u := by
  by_cases z : marginal l a (l u)=0
  · have au : a u=0 := le_antisymm (z ▸ le_marginal l a ha u) (ha u)
    simp [join,au]
  · have eq : (∑ v,join l r a b u v)=a u*(marginal r b (l u))/marginal l a (l u) := by
      simp only [join,marginal,Finset.mul_sum,Finset.sum_div, mul_ite,mul_zero,ite_div,zero_div]
      apply Finset.sum_congr rfl
      intro v _
      by_cases he : l u=r v <;> simp [he,eq_comm]
    rw [eq,← same]
    exact mul_div_cancel_right₀ _ z

lemma join_symm (l : A→I) (r : B→I) (a : A→ℝ) (b : B→ℝ)
    (same : ∀ i,marginal l a i=marginal r b i) (u v) :
    join l r a b u v=join r l b a v u := by
  by_cases eq : l u=r v
  · simp [join,eq,same,mul_comm]
  · simp [join,eq,Ne.symm eq]

theorem coupled_laws (l : A→I) (r : B→I) (a : A→ℝ) (b : B→ℝ)
    (ha : ∀ u,0≤a u) (hb : ∀ v,0≤b v) (one : ∑ u,a u=1)
    (same : ∀ i,marginal l a i=marginal r b i) :
    ∃ w : A→B→ℝ, (∀ u v,0≤w u v) ∧ (∀ u v,l u≠r v → w u v=0) ∧
      (∀ u,(∑ v,w u v)=a u) ∧ (∀ v,(∑ u,w u v)=b v) ∧ (∑ u,∑ v,w u v)=1 := by
  refine ⟨join l r a b,join_nonneg l r a b ha hb,fun u v neq=>by simp [join,neq],
    join_left l r a b ha same,?_,?_⟩
  · intro v
    simp_rw [join_symm l r a b same]
    exact join_left r l b a hb (fun i=>(same i).symm) v
  · simpa only [join_left l r a b ha same] using one

end
end PositivePermanent.Cut
#print axioms PositivePermanent.Cut.coupled_laws
