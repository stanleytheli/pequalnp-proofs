import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AlgebraicMeta
open Finset MvPolynomial

/-- A displayed unsigned projection groups its surviving, weight-one
monomials according to their target exponent. -/
noncomputable def fiberPoly {V A R : Type*} [CommSemiring R]
    (solutions : Finset A) (image : A → V →₀ ℕ) : MvPolynomial V R :=
  ∑ a ∈ solutions, monomial (image a) 1

theorem coeff_fiber {V A R : Type*} [CommSemiring R] [DecidableEq V]
    (solutions : Finset A) (image : A → V →₀ ℕ) (w : V →₀ ℕ) :
    (fiberPoly (R:=R) solutions image).coeff w = ((solutions.filter (fun a => image a=w)).card:R) := by
  classical
  simp [fiberPoly,coeff_monomial,Finset.sum_boole]

/-- Equality to a coefficient-one support is exactly the family of ordinary
fiber counts mapped into the coefficient semiring. In characteristic zero
these counts are exact; in positive characteristic they test residues. -/
theorem transfer_iff_fibers {V A R : Type*} [CommSemiring R] [DecidableEq V]
    (solutions : Finset A) (image : A → V →₀ ℕ) (wanted : Finset (V →₀ ℕ)) :
    fiberPoly (R:=R) solutions image = fiberPoly (R:=R) wanted id ↔
      ∀ w, ((solutions.filter (fun a => image a=w)).card:R) = if w∈wanted then 1 else 0 := by
  classical
  have unitFiber (w : V →₀ ℕ) :
      (fiberPoly (R:=R) wanted id).coeff w = if w∈wanted then 1 else 0 := by
    simp only [fiberPoly,coeff_sum,coeff_monomial,id_eq]
    by_cases hw : w∈wanted <;> simp [hw]
  constructor
  · intro he w
    rw [← coeff_fiber,he,unitFiber]
  · intro h
    ext w
    rw [coeff_fiber,unitFiber,h w]

end AlgebraicMeta
#print axioms AlgebraicMeta.coeff_fiber
#print axioms AlgebraicMeta.transfer_iff_fibers
