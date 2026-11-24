import Consequence
import GraphOrder

namespace SparsePermanent
universe u

/-- The circuit lower bound is superpolynomial in the number of vertices, with
the full 4/3 logarithmic exponent, for each fixed polynomial subdivision depth. -/
theorem exact_lower_order (upstream : Statement.MainTheorem.{u}) (q : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (K : Type u) [Field K] [CharP K p],
      ∀ k s : ℕ, m₀≤k+1 → p≠2 → Statement.Computes (familyGeneric K k ((k+1)^q)) s →
        Statement.Beyond c (order k ((k+1)^q)) s := by
  obtain ⟨c,hc,L⟩:=exact_lower upstream
  refine ⟨c/((q+5:ℕ):ℝ)^2,by positivity,fun p=>?_⟩
  obtain ⟨m₀,hm₀⟩:=L p
  refine ⟨max 2 m₀,fun K _ _ k s h hp hcomp=>?_⟩
  have hm : 2≤k+1 := (le_max_left _ _).trans h
  have bound:=hm₀ K k ((k+1)^q) s ((le_max_right _ _).trans h) hp hcomp
  exact (rate_rescale hc.le (by omega : 1≤q+5) (order_positive ..) (by omega) (order_poly k q hm)).trans_lt bound

theorem approximate_lower_order (upstream : Statement.MainTheoremApprox.{u}) (q : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (K : Type u) [Field K] [CharP K p],
      ∀ k s : ℕ, m₀≤k+1 → p≠2 → Statement.Approximates (familyGeneric K k ((k+1)^q)) s →
        Statement.Beyond c (order k ((k+1)^q)) s := by
  obtain ⟨c,hc,L⟩:=approximate_lower upstream
  refine ⟨c/((q+5:ℕ):ℝ)^2,by positivity,fun p=>?_⟩
  obtain ⟨m₀,hm₀⟩:=L p
  refine ⟨max 2 m₀,fun K _ _ k s h hp hcomp=>?_⟩
  have hm : 2≤k+1 := (le_max_left _ _).trans h
  have bound:=hm₀ K k ((k+1)^q) s ((le_max_right _ _).trans h) hp hcomp
  exact (rate_rescale hc.le (by omega : 1≤q+5) (order_positive ..) (by omega) (order_poly k q hm)).trans_lt bound

end SparsePermanent
#print axioms SparsePermanent.exact_lower_order
#print axioms SparsePermanent.approximate_lower_order
