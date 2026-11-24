import DirectedSplit
import Mathlib.Logic.Equiv.Fin.Basic

namespace SparsePermanent
namespace RoutedModel
variable {R : Type*} [CommSemiring R]

theorem reindex_permanent {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix J J R) (e : I≃J) : (A.submatrix e e).permanent=A.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv e.permCongr _ _
  intro p
  apply Fintype.prod_equiv e _ _
  intro i
  simp [Matrix.submatrix]

/-- Number the extra matched pair of a vertex split in the same finite index
type as the rest of the directed model. -/
def numbered {n : ℕ} (A : Matrix (Option (Fin n)) (Option (Fin n)) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  A.submatrix (finSuccEquiv n) (finSuccEquiv n)

/-- A finite sequence of directed tree splits: a singleton group extends a
private directed link, while larger groups grow the incoming or outgoing
branch tree at an original matrix index. -/
inductive Generated {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    {n : ℕ}→Matrix (Fin n) (Fin n) R→Prop
  | base : Generated A A
  | outgoing {n : ℕ} {B : Matrix (Fin n) (Fin n) R} (h : Generated A B)
      (v : Fin n) (S : Finset (Fin n)) :
      Generated A (numbered (DirectedSplit.outgoing B v (·∈S)))
  | incoming {n : ℕ} {B : Matrix (Fin n) (Fin n) R} (h : Generated A B)
      (v : Fin n) (S : Finset (Fin n)) :
      Generated A (numbered (DirectedSplit.incoming B v (·∈S)))

theorem Generated.permanent {m n : ℕ} {A : Matrix (Fin m) (Fin m) R} {B : Matrix (Fin n) (Fin n) R}
    (model : Generated A B) : B.permanent=A.permanent := by
  induction model with
  | base=>rfl
  | outgoing _ v S ih=>rw [numbered,reindex_permanent,DirectedSplit.permanent_outgoing]; exact ih
  | incoming _ v S ih=>rw [numbered,reindex_permanent,DirectedSplit.permanent_incoming]; exact ih

private theorem labels_out {n : ℕ} (B : Matrix (Fin n) (Fin n) R) (Q : R→Prop)
    (zero : Q 0) (one : Q 1) (ok : ∀ i j,Q (B i j)) (v : Fin n) (S : Finset (Fin n)) :
    ∀ i j,Q (DirectedSplit.outgoing B v (·∈S) i j) := by
  rintro (_|i) (_|j) <;> dsimp only [DirectedSplit.outgoing] <;>
    first | exact one | split <;> first | exact one | exact zero | exact ok _ _

theorem Generated.labels {m n : ℕ} {A : Matrix (Fin m) (Fin m) R} {B : Matrix (Fin n) (Fin n) R}
    (model : Generated A B) (Q : R→Prop) (zero : Q 0) (one : Q 1) (leaf : ∀ i j,Q (A i j)) :
    ∀ i j,Q (B i j) := by
  induction model with
  | base=>exact leaf
  | outgoing _ v S ih=>intro i j; exact labels_out _ Q zero one ih v S _ _
  | incoming _ v S ih=>intro i j; exact labels_out _ Q zero one (fun a b=>ih b a) v S _ _

end RoutedModel
end SparsePermanent
#print axioms SparsePermanent.RoutedModel.Generated.permanent
#print axioms SparsePermanent.RoutedModel.Generated.labels
