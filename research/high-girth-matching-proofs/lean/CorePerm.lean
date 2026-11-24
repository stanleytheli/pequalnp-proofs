import Core
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators

namespace SparsePermanent
namespace CoreMatching
variable {k : ℕ}

theorem decode_wires (b : MatchingData k) : b.wires.data=b := by
  apply MatchingData.ext
  · funext r
    apply Selector.ext
    intro j
    have h := b.wires.row_value r j
    change Sum.inl (r,(b.row r).port j)=Sum.inl (r,(b.wires.row r).port j) at h
    exact (Prod.mk.inj (Sum.inl.inj h)).2.symm
  · funext c
    apply Selector.ext
    intro j
    have h := b.wires.col_value c j
    change Sum.inl ((b.col c).port j,c)=Sum.inl ((b.wires.col c).port j,c) at h
    exact (Prod.mk.inj (Sum.inl.inj h)).1.symm

theorem wires_decode (p : CoreMatching k) : p.data.wires=p := by
  apply Subtype.ext
  apply Equiv.ext
  rintro (⟨r,c⟩|⟨c,j⟩)
  · change p.data.forward (.inl (r,c))=p.val (.inl (r,c))
    change (match (p.row r).which c with
      | some j => Sum.inr (r,j) | none => Sum.inl (r,c))=p.val (.inl (r,c))
    cases h : (p.row r).which c with
    | none => exact ((p.row_unused r c).mp (((p.row r).which_eq_none _).mp h)).symm
    | some j =>
      have e := ((p.row r).which_eq_some _ _).mp h
      have q := p.row_value r j
      rw [e] at q
      exact p.val.symm_apply_eq.mp q
  · exact (p.col_value c j).symm

/-- An actual perfect matching of the sparse bipartite matrix is uniquely extended
from a permutation of the dense input. -/
noncomputable def equivOriginal : CoreMatching k ≃ Equiv.Perm (Node k) :=
  (Equiv.mk data MatchingData.wires wires_decode decode_wires).trans MatchingData.equivPerm

@[simp] theorem original_inv (p : Equiv.Perm (Node k)) :
    equivOriginal.symm p=(MatchingData.ofPerm p).wires := rfl

end CoreMatching

variable {k : ℕ} {R : Type*} [CommSemiring R]
def weight (A : Matrix (Node k) (Node k) R) : Position k → Position k → R
  | .inl (r,c), .inl _ => A c r
  | _, _ => 1

noncomputable def sparseMatrix (A : Matrix (Node k) (Node k) R) : Matrix (Position k) (Position k) R :=
  fun y x => by classical exact if edge x y then weight A x y else 0

theorem weight_port (A : Matrix (Node k) (Node k) R) (b : MatchingData k) (r c : Node k) :
    weight A (.inl (r,c)) (b.forward (.inl (r,c))) =
      if c=b.movement r then A c r else 1 := by
  cases h : (b.row r).which c with
  | none =>
    have eq := ((b.row r).unused c).mp (((b.row r).which_eq_none _).mp h)
    change c=b.movement r at eq
    rw [if_pos eq]
    simp only [MatchingData.forward,h,weight]
  | some j =>
    have ne : c≠b.movement r := by
      intro e
      exact ((b.row r).unused c).mpr e ⟨j, ((b.row r).which_eq_some _ _).mp h⟩
    simp [MatchingData.forward,h,weight,ne]

theorem product_weights (A : Matrix (Node k) (Node k) R) (b : MatchingData k) :
    ∏ x, weight A x (b.forward x) = ∏ r, A (b.movement r) r := by
  rw [Fintype.prod_sum_type]
  have gaps : (∏ a : Node k × Fin k, weight A (.inr a) (b.forward (.inr a)))=1 := by
    apply Finset.prod_eq_one
    rintro ⟨c,j⟩ _
    rfl
  rw [gaps,mul_one,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  simp only [weight_port]
  simp

/-- The specialized matching polynomial is the ordinary permanent over every
commutative semiring. Each dense variable occupies one physical sparse entry. -/
theorem permanent_sparse (A : Matrix (Node k) (Node k) R) :
    (sparseMatrix A).permanent = A.permanent := by
  classical
  let valid := fun p : Equiv.Perm (Position k) => ∀ x, edge x (p x)
  unfold Matrix.permanent
  rw [← Fintype.sum_subtype_add_sum_subtype valid]
  have zero : (∑ p : {p // ¬ valid p}, ∏ x, sparseMatrix A (p.val x) x)=0 := by
    apply Finset.sum_eq_zero
    intro p _
    have := p.prop
    dsimp [valid] at this
    push Not at this
    obtain ⟨x,hx⟩:=this
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [sparseMatrix,hx])
  rw [zero,add_zero]
  apply (Fintype.sum_equiv CoreMatching.equivOriginal _ _)
  intro p
  change (∏ x, sparseMatrix A (p.val x) x)=∏ r, A (p.data.movement r) r
  calc
    _ = ∏ x, weight A x (p.val x) := by
      apply Finset.prod_congr rfl
      intro x _
      simp [sparseMatrix,p.prop x]
    _ = ∏ x, weight A x (p.data.forward x) := by
      have hp := congrArg Subtype.val (CoreMatching.wires_decode p)
      apply Finset.prod_congr rfl
      intro x _
      exact congrArg (weight A x) (Equiv.congr_fun hp x).symm
    _ = _ := product_weights A p.data

end SparsePermanent

#print axioms SparsePermanent.CoreMatching.equivOriginal
#print axioms SparsePermanent.permanent_sparse
