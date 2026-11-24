import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

namespace PositivePermanent
open Filter
open scoped BigOperators Topology
noncomputable section

variable {S E T : Type*} [Fintype E]

/-- Logarithms of the common scale and entry weights give this linear map. -/
def logAmplitudes (m : S → E → ℕ) : (ℝ × (E → ℝ)) →ₗ[ℝ] (S → ℝ) where
  toFun z s := z.1 + ∑ e, (m s e : ℝ) * z.2 e
  map_add' x y := by
    ext s
    simp [mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c z := by
    ext s
    simp [mul_add, Finset.mul_sum, mul_left_comm]

/-- On all indices with positive limiting amplitude, one finite, strictly positive
choice of common scale and edge weights realizes the limits simultaneously.
Zero factors along the approximating net are allowed. -/
theorem positive_amplitudes [Finite S] {l : Filter T} [NeBot l]
    (m : S → E → ℕ) (c : T → ℝ) (entry : T → E → ℝ) (p : S → ℝ)
    (pos : ∀ s, 0 < p s)
    (lim : ∀ s, Tendsto (fun t => c t * ∏ e, entry t e ^ m s e) l (𝓝 (p s))) :
    ∃ b : ℝ, 0 < b ∧ ∃ d : E → ℝ, (∀ e, 0 < d e) ∧
      ∀ s, p s = b * ∏ e, d e ^ m s e := by
  classical
  let g := logAmplitudes m
  let z : T → ℝ × (E → ℝ) := fun t => (Real.log (c t), fun e => Real.log (entry t e))
  have conv : Tendsto (fun t => g (z t)) l (𝓝 (fun s => Real.log (p s))) := by
    apply tendsto_pi_nhds.mpr
    intro s
    apply ((Real.continuousAt_log (pos s).ne').tendsto.comp (lim s)).congr'
    filter_upwards [(lim s).eventually_ne (pos s).ne'] with t nz
    change Real.log (c t * ∏ e, entry t e ^ m s e) =
      Real.log (c t) + ∑ e, (m s e : ℝ) * Real.log (entry t e)
    obtain ⟨hc, hp⟩ := mul_ne_zero_iff.mp nz
    rw [Real.log_mul hc hp, Real.log_prod (Finset.prod_ne_zero_iff.mp hp)]
    simp [Real.log_pow]
  have hin : (fun s => Real.log (p s)) ∈ LinearMap.range g :=
    (LinearMap.range g).isClosed_of_finiteDimensional.mem_of_tendsto conv
      (Eventually.of_forall fun t => ⟨z t, rfl⟩)
  obtain ⟨q, hq⟩ := hin
  refine ⟨Real.exp q.1, Real.exp_pos _, fun e => Real.exp (q.2 e),
    fun _ => Real.exp_pos _, fun s => ?_⟩
  have eq := congrFun hq s
  change q.1 + ∑ e, (m s e : ℝ) * q.2 e = Real.log (p s) at eq
  rw [← Real.exp_log (pos s), ← eq, Real.exp_add, Real.exp_sum]
  simp [Real.exp_nat_mul]

end
end PositivePermanent

#print axioms PositivePermanent.positive_amplitudes
