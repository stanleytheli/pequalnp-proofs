import Explicit

namespace SparsePermanent

private theorem same_run {I D R S : Type*} [DecidableEq D] [DecidableEq I]
    [CommSemiring R] [CommSemiring S] (B : Board D I R) (C : Board D I S)
    (adj : B.adj=C.adj) (row : B.firstRow=C.firstRow) (col : B.firstCol=C.firstCol) (ops : List D) :
    (B.run ops).adj=(C.run ops).adj ∧ (B.run ops).firstRow=(C.run ops).firstRow ∧
    (B.run ops).firstCol=(C.run ops).firstCol := by
  induction ops with
  | nil => exact ⟨adj,row,col⟩
  | cons d ds step =>
    obtain ⟨a,r,c⟩:=step
    change (divideAdj _ _ _=divideAdj _ _ _) ∧ (Board.step _ d).firstRow=(Board.step _ d).firstRow ∧
      (Board.step _ d).firstCol=(Board.step _ d).firstCol
    refine ⟨by rw [a,r,c],?_,?_⟩
    · dsimp only [Board.step]; rw [r]
    · apply Function.Embedding.ext
      intro u
      change some ((B.run ds).firstCol u)=some ((C.run ds).firstCol u)
      rw [c]

/-- The physical graph uses no coefficient information, across arbitrary
coefficient universes as well as different edge labelings. -/
theorem family_shape {R S : Type*} [CommSemiring R] [CommSemiring S]
    {k : ℕ} (h : ℕ) (A : Matrix (Node k) (Node k) R) (B : Matrix (Node k) (Node k) S) :
    (familyBoard h A).adj=(familyBoard h B).adj :=
  (same_run (coreBoard A) (coreBoard B) rfl rfl rfl _).1

noncomputable def physical (k h : ℕ) := (familyBoard h (0 : Matrix (Node k) (Node k) ℕ)).adj

end SparsePermanent
#print axioms SparsePermanent.family_shape
