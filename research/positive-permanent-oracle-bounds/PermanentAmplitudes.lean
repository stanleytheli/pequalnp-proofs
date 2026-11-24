import ToricAmplitudes
import Mathlib.Data.Fintype.Perm

namespace PositivePermanent
open Filter
open scoped BigOperators Topology
noncomputable section

variable {I T X : Type*} [Fintype I] [DecidableEq I]

private lemma selected_product (d : I × I → ℝ) (s : Equiv.Perm I) :
    (∏ e : I × I, d e ^ (if s e.1 = e.2 then 1 else 0 : ℕ)) =
       ∏ i, d (i, s i) := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [apply_ite, pow_one, pow_zero]
  simp [Finset.prod_ite_eq]

/-- When the positive permutations form the coordinate face on their union of
edges, a single nonnegative matrix and positive common scale realize every
limiting weight, including the zero ones. -/
theorem matching_amplitudes {l : Filter T} [NeBot l]
    (c : T → ℝ) (a : T → I → I → ℝ) (w : Equiv.Perm I → ℝ)
    (lim : ∀ s, Tendsto (fun t => c t * ∏ i, a t i (s i)) l (𝓝 (w s)))
    (nonneg : ∀ s, 0 ≤ w s)
    (face : ∀ s : Equiv.Perm I, (∀ i, ∃ u, 0 < w u ∧ u i = s i) → 0 < w s) :
    ∃ b : ℝ, 0 < b ∧ ∃ d : I → I → ℝ, (∀ i j, 0 ≤ d i j) ∧
      (∀ i j, 0 < d i j ↔ ∃ u, 0 < w u ∧ u i = j) ∧
      ∀ s, w s = b * ∏ i, d i (s i) := by
  classical
  let S := {s : Equiv.Perm I // 0 < w s}
  let m (s : S) (e : I × I) : ℕ := if s.val e.1 = e.2 then 1 else 0
  obtain ⟨b, hb, weights, hw, heq⟩ := positive_amplitudes m c
    (fun t e => a t e.1 e.2) (fun s => w s.val) (fun s => s.property)
    (fun s => by simpa only [m, selected_product] using lim s.val)
  let good (i j : I) := ∃ u, 0 < w u ∧ u i = j
  let d (i j : I) := if good i j then weights (i,j) else 0
  have zeros (i j : I) : 0 < d i j ↔ good i j := by
    by_cases h : good i j <;> simp [d, h, hw]
  refine ⟨b, hb, d, fun i j => ?_, zeros, fun s => ?_⟩
  · by_cases h : good i j <;> simp [d, h, (hw (i,j)).le]
  · by_cases h : 0 < w s
    · have eq := heq (⟨s,h⟩ : S)
      change w s = b * (∏ e : I × I, weights e ^ (if s e.1 = e.2 then 1 else 0 : ℕ)) at eq
      rw [selected_product] at eq
      rw [eq]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      have hi : good i (s i) := ⟨s,h,rfl⟩
      simp [d, hi]
    · have missing : ¬∀ i, good i (s i) := fun yes => h (face s yes)
      obtain ⟨i,hi⟩ := not_forall.mp missing
      have z : d i (s i) = 0 := by simp [d, hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) z, mul_zero]
      exact le_antisymm (not_lt.mp h) (nonneg s)

/-- Normalize the input polynomials separately. The limit of their weighted
permanent is exactly the permanent of their limits with fixed matrix weights. -/
theorem normalized_permanent_limit {l : Filter T} [NeBot l]
    (c : T → ℝ) (a : T → I → I → ℝ) (w : Equiv.Perm I → ℝ)
    (p : T → I → I → X → ℝ) (q : I → I → X → ℝ)
    (lim : ∀ s, Tendsto (fun t => c t * ∏ i, a t i (s i)) l (𝓝 (w s)))
    (nonneg : ∀ s, 0 ≤ w s)
    (face : ∀ s : Equiv.Perm I, (∀ i, ∃ u, 0 < w u ∧ u i = s i) → 0 < w s)
    (children : ∀ i j x, Tendsto (fun t => p t i j x) l (𝓝 (q i j x))) :
    ∃ b : ℝ, 0 < b ∧ ∃ d : I → I → ℝ, (∀ i j, 0 ≤ d i j) ∧ ∀ x,
      Tendsto (fun t => ∑ s : Equiv.Perm I,
        (c t * ∏ i, a t i (s i)) * ∏ i, p t i (s i) x) l
        (𝓝 (b * ∑ s : Equiv.Perm I, ∏ i, d i (s i) * q i (s i) x)) := by
  obtain ⟨b, hb, d, hd, _, hw⟩ := matching_amplitudes c a w lim nonneg face
  refine ⟨b, hb, d, hd, fun x => ?_⟩
  rw [Finset.mul_sum]
  apply tendsto_finsetSum
  intro s _
  rw [Finset.prod_mul_distrib, ← mul_assoc, ← hw s]
  apply (lim s).mul
  exact tendsto_finsetProd _ (fun i _ => children i (s i) x)

end
end PositivePermanent

#print axioms PositivePermanent.matching_amplitudes
#print axioms PositivePermanent.normalized_permanent_limit
