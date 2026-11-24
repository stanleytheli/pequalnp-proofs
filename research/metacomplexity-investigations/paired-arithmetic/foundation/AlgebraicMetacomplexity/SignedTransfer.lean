import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace AlgebraicMeta
open Finset MvPolynomial

/-- The first summand provides the target variables, the other two index
accepted witnesses in the positively and negatively weighted branches. -/
abbrev SignedVars (V A B : Type*) := V ⊕ (A ⊕ B)

noncomputable def signedSource {V A B : Type*} [Fintype A] [Fintype B]
    (h : MvPolynomial V ℤ) : MvPolynomial (SignedVars V A B) ℤ :=
  rename Sum.inl h + (∑ a : A, X (.inr (.inl a))) + ∑ b : B, X (.inr (.inr b))

noncomputable def signedMap {V A B : Type*} : SignedVars V A B → MvPolynomial V ℤ
  | .inl v => X v
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

theorem signed_transfer {V A B : Type*} [Fintype A] [Fintype B] (h : MvPolynomial V ℤ) :
    aeval signedMap (signedSource (A:=A) (B:=B) h) =
      h + C ((Fintype.card A : ℤ) - Fintype.card B) := by
  classical
  simp only [signedSource,map_add,aeval_rename,map_sum,aeval_X,signedMap]
  change aeval (X (R:=ℤ)) h + (∑ _ : A, (1 : MvPolynomial V ℤ)) +
      (∑ _ : B, (-1 : MvPolynomial V ℤ)) = _
  rw [aeval_X_left_apply]
  simp [sub_eq_add_neg,add_assoc]

theorem signed_identity_iff {V A B : Type*} [Fintype A] [Fintype B] (h : MvPolynomial V ℤ) :
    aeval signedMap (signedSource (A:=A) (B:=B) h) = h ↔ Fintype.card A = Fintype.card B := by
  rw [signed_transfer]
  constructor
  · intro e
    have hzero : C ((Fintype.card A : ℤ) - Fintype.card B) = (0 : MvPolynomial V ℤ) :=
      add_left_cancel (show h + C ((Fintype.card A : ℤ) - Fintype.card B) = h + 0 by simpa using e)
    have hzero' := MvPolynomial.C_eq_zero.mp hzero
    exact Int.ofNat_inj.mp (sub_eq_zero.mp hzero')
  · intro e
    rw [e]
    simp

/-- Any bijective encoding with a monomial-preserving projection preserves the
whole generating polynomial, including multiplicities, over every semiring. -/
theorem sum_unique_extensions {V W A B R : Type*} [CommSemiring R] [Fintype A] [Fintype B]
    (e : A ≃ B) (source : A → MvPolynomial V R) (target : B → MvPolynomial W R)
    (project : V → MvPolynomial W R)
    (term : ∀ a, aeval project (source a) = target (e a)) :
    aeval project (∑ a, source a) = ∑ b, target b := by
  classical
  simp only [map_sum,term]
  exact e.sum_comp target

end AlgebraicMeta
#print axioms AlgebraicMeta.signed_transfer
#print axioms AlgebraicMeta.signed_identity_iff
#print axioms AlgebraicMeta.sum_unique_extensions
