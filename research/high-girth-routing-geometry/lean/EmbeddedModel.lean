import RoutedModel
import Padding
import Mathlib.Logic.Equiv.Set

namespace SparsePermanent.RoutedModel
variable {R : Type*} [CommSemiring R]

/-- Embed an arbitrary finite weighted bipartite matrix into a larger
matched graph. On the unused pairs retain a single unit matching. -/
theorem embed_matrix {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (B : Matrix (Fin n) (Fin n) R) (H : J→J→Prop) (f : Fin n↪J)
    (cover : ∀i j,B j i≠0→H (f i) (f j)) (matching : ∀x,H x x)
    (Q : R→Prop) (zero:Q 0) (one:Q 1) (labels:∀i j,Q (B j i)) :
    ∃ A : Matrix J J R,A.permanent=B.permanent ∧ (∀i j,¬H i j→A j i=0) ∧ ∀i j,Q (A j i) := by
  classical
  let C:=(Set.range f)ᶜ
  let e : Fin n⊕C≃J := (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl C)).trans (Equiv.Set.sumCompl (Set.range f))
  let D:=padded B (Equiv.refl C)
  let A:=D.submatrix e.symm e.symm
  refine ⟨A,(reindex_permanent D e.symm).trans (permanent_padded B (Equiv.refl C)),?_,?_⟩
  · rintro i j bad
    obtain ⟨x,rfl⟩:=e.surjective i
    obtain ⟨y,rfl⟩:=e.surjective j
    simp only [A,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    rcases x with i|x <;> rcases y with j|y
    · exact not_ne_iff.mp (fun nz=>bad (cover i j nz))
    · rfl
    · rfl
    · have ne:x≠y:=by rintro rfl;exact bad (matching _)
      simp [D,padded,ne]
  · intro i j
    obtain ⟨x,rfl⟩:=e.surjective i
    obtain ⟨y,rfl⟩:=e.surjective j
    simp only [A,Matrix.submatrix_apply,Equiv.symm_apply_apply]
    rcases x with i|x <;> rcases y with j|y
    · exact labels _ _
    · exact zero
    · exact zero
    · by_cases eq:x=y
      · simpa [D,padded,eq] using one
      · simpa [D,padded,eq] using zero

end SparsePermanent.RoutedModel
#print axioms SparsePermanent.RoutedModel.embed_matrix
