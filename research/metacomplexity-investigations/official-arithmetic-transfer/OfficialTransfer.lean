import Projection
import PlantedSlices

namespace AlgebraicMeta
open MvPolynomial SparsePermanent
universe u
variable {I V : Type} [Fintype I] [DecidableEq I]

def pickLeaf (a : I → Bool) : Vars I V → Leaf V
  | .inl none => .zero
  | .inl (some (i,b)) => if b=a i then .one else .zero
  | .inr v => .var v

theorem pickLeaf_poly (R : Type u) [CommSemiring R] (a : I → Bool) (v : Vars I V) :
    (pickLeaf a v).poly R=pick (R:=R) a v := by
  rcases v with (opt|v)
  · rcases opt with _|⟨i,b⟩
    · rfl
    · by_cases h : b=a i <;> simp [pickLeaf,Leaf.poly,pick,h]
  · rfl

theorem restrict_planted {R : Type u} [CommSemiring R] (valid : Finset (I → Bool))
    {a : I → Bool} (ha : a∈valid) (h : MvPolynomial V R) :
    Leaf.projection R (pickLeaf a) (plant valid h)=h := by
  change aeval (fun v => (pickLeaf a v).poly R) (plant valid h)=h
  simp only [pickLeaf_poly]
  rw [planted_projection]
  simp [ha]

theorem planted_computes {R : Type u} [CommSemiring R] (valid : Finset (I → Bool))
    {a : I → Bool} (ha : a∈valid) (h : MvPolynomial V R) {s : ℕ}
    (actual : Statement.Computes (plant valid h) s) : Statement.Computes h s := by
  have transferred := Leaf.computes (pickLeaf a) actual
  rwa [restrict_planted valid ha] at transferred

theorem planted_approximates {R : Type u} [Field R] (valid : Finset (I → Bool))
    {a : I → Bool} (ha : a∈valid) (h : MvPolynomial V R) {s : ℕ}
    (actual : Statement.Approximates (plant valid h) s) : Statement.Approximates h s := by
  have transferred := Leaf.approximates (pickLeaf a) actual
  rwa [restrict_planted valid ha] at transferred

/-- The two main theorem statements of the official release imply the two
separate superpolynomial rates for every nonempty planted-witness polynomial. -/
theorem upstream_planted (exactBound : Statement.MainTheorem.{u})
    (borderBound : Statement.MainTheoremApprox.{u}) :
    ∃ c d : ℝ, 0<c ∧ 0<d ∧ ∀ p : ℕ, ∃ threshold : ℕ,
      ∀ (K : Type u) [Field K] [CharP K p], ∀ m≥threshold, ∀ s : ℕ,
      ∀ (valid : Finset (I → Bool)) (a : I → Bool), a∈valid →
      (Statement.Computes (plant valid (Statement.hc K m)) s → Statement.Beyond c m s) ∧
      (Statement.Approximates (plant valid (Statement.hc K m)) s → Statement.Beyond d m s) := by
  obtain ⟨c,hc,cd⟩ := exactBound
  obtain ⟨d,hd,dd⟩ := borderBound
  refine ⟨c,d,hc,hd,fun p=>?_⟩
  obtain ⟨mc,hmc⟩ := cd p
  obtain ⟨md,hmd⟩ := dd p
  refine ⟨max mc md,?_⟩
  intro K _ _ m hm s valid a ha
  exact ⟨fun h => (hmc K m ((le_max_left ..).trans hm) s).1 (planted_computes valid ha _ h),
    fun h => (hmd K m ((le_max_right ..).trans hm) s).1 (planted_approximates valid ha _ h)⟩

end AlgebraicMeta
#print axioms AlgebraicMeta.planted_computes
#print axioms AlgebraicMeta.planted_approximates
#print axioms AlgebraicMeta.upstream_planted
