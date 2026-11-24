import Statement

namespace SparsePermanent
open MvPolynomial
universe u v
variable {V W : Type} {F : Type u}

/-- The individual leaves allowed in a 0/1 projection. -/
inductive Leaf (W : Type) where
  | zero
  | one
  | var (w : W)

namespace Leaf
noncomputable section
def poly (R : Type*) [CommSemiring R] : Leaf W → MvPolynomial W R
  | .zero => 0
  | .one => 1
  | .var w => X w

def projection (R : Type*) [CommSemiring R] (r : V → Leaf W) :
    MvPolynomial V R →ₐ[R] MvPolynomial W R := aeval (fun i => (r i).poly R)

theorem maps {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (r : V → Leaf W) (f : MvPolynomial V R) :
    MvPolynomial.map φ (projection R r f)=projection S r (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [projection]
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp,map_X]
    congr 1
    cases h : r i <;> simp [projection,h,poly]

/-- Arithmetic circuit size is preserved, including the upstream convention that a
constant or variable contributes one gate. -/
theorem computes {R : Type*} [CommSemiring R] (r : V → Leaf W) {f : MvPolynomial V R} {s : ℕ}
    (h : Statement.Computes f s) : Statement.Computes (projection R r f) s := by
  obtain ⟨l,valid,k,hk,out⟩:=h
  refine ⟨fun i => projection R r (l i),fun i hi => ?_,k,hk,congrArg (projection R r) out⟩
  dsimp only
  rcases valid i hi with ⟨j,hj⟩|⟨a,ha⟩|⟨a,ha,b,hb,e⟩|⟨a,ha,b,hb,e⟩
  · simp only [hj]
    cases eq : r j with
    | zero => exact Or.inr (Or.inl ⟨0,by simp [projection,eq,poly]⟩)
    | one => exact Or.inr (Or.inl ⟨1,by simp [projection,eq,poly]⟩)
    | var w => exact Or.inl ⟨w,by simp [projection,eq,poly]⟩
  · exact Or.inr (Or.inl ⟨a,by simp [ha,projection]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a,ha,b,hb,by simp [e]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,by simp [e]⟩))

section Laurent
variable [Field F]
private abbrev intoLaurent := HahnSeries.ofPowerSeries ℤ F
private abbrev atZero := PowerSeries.constantCoeff (R:=F)

private theorem regular (f : LaurentSeries F) :
    (∀ i : ℤ, i<0 → f.coeff i = 0) ↔ ∃ w : PowerSeries F, intoLaurent w=f := by
  have h := LaurentSeries.val_le_one_iff_eq_coe F f
  rw [LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F one_ne_zero,WithZero.log_one,neg_zero] at h
  exact h

private theorem constant_eq (f : PowerSeries F) : (intoLaurent f).coeff 0 = atZero f := by
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ:=ℤ) f 0
  simpa only [Nat.cast_zero,PowerSeries.coeff_zero_eq_constantCoeff_apply] using h

/-- A regular polynomial over Laurent series admits a polynomial lift to power
series. The residue of that lift is exactly the target polynomial. -/
theorem regular_polynomial (q : MvPolynomial V (LaurentSeries F)) (f : MvPolynomial V F) :
    (∀ (d : V →₀ ℕ) (i : ℤ), i≤0 → (q.coeff d).coeff i=if i=0 then f.coeff d else 0) ↔
      ∃ w : MvPolynomial V (PowerSeries F), MvPolynomial.map intoLaurent w=q ∧
        MvPolynomial.map atZero w=f := by
  classical
  constructor
  · intro good
    have lift : q ∈ Set.range (MvPolynomial.map intoLaurent) := by
      apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
      intro a ha
      obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp (show a∈q.coeffs from ha)
      apply (regular _).mp
      intro i hi
      simpa [hi.ne] using good d i hi.le
    obtain ⟨w,rfl⟩:=lift
    refine ⟨w,rfl,?_⟩
    ext d
    have eq:=good d 0 le_rfl
    simpa only [coeff_map,ite_true,constant_eq] using eq
  · rintro ⟨w,rfl,rfl⟩ d i hi
    simp only [coeff_map]
    by_cases e : i=0
    · subst i
      simp [constant_eq]
    · rw [ite_eq_right_iff.mpr (fun h => (e h).elim)]
      exact (regular _).mpr ⟨_,rfl⟩ i (lt_of_le_of_ne hi e)

/-- A 0/1/variable projection preserves the *same* gate budget for Laurent
approximation too, including when negative orders occur inside the circuit. -/
theorem approximates (r : V → Leaf W) {f : MvPolynomial V F} {s : ℕ}
    (h : Statement.Approximates f s) : Statement.Approximates (projection F r f) s := by
  obtain ⟨q,compute,good⟩:=h
  obtain ⟨w,qmap,fmap⟩:=(regular_polynomial q f).mp good
  refine ⟨projection (LaurentSeries F) r q,computes r compute,(regular_polynomial _ _).mpr ?_⟩
  exact ⟨projection (PowerSeries F) r w, (maps _ _ _).trans (congrArg _ qmap),
    (maps _ _ _).trans (congrArg _ fmap)⟩

end Laurent
end
end Leaf
end SparsePermanent

#print axioms SparsePermanent.Leaf.computes
#print axioms SparsePermanent.Leaf.regular_polynomial
#print axioms SparsePermanent.Leaf.approximates
