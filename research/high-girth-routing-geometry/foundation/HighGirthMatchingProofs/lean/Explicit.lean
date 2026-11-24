import Iterate

namespace SparsePermanent
variable {R : Type*} [CommSemiring R]

namespace Board
variable {D I : Type*} [DecidableEq D] [DecidableEq I]

/-- Subdivision inserts only zero/one constants and transfers an old label. -/
theorem all_entries (B : Board D I R) (P : R→Prop) (zero : P 0) (one : P 1)
    (base : ∀ u v, P (B.matrix u v)) (ops : List D) :
    ∀ u v, P ((B.run ops).matrix u v) := by
  induction ops with
  | nil => exact base
  | cons e rest ih =>
    change ∀ u v : Option _, P (divideEdge (B.run rest).matrix _ _ u v)
    rintro (_|u) (_|v)
    · exact one
    · change P (if _ then _ else _)
      split <;> first | exact zero | exact ih _ _
    · change P (if _ then _ else _)
      split <;> first | exact zero | exact one
    · change P (if _ then _ else _)
      split <;> first | exact zero | exact ih _ _

end Board

abbrev Join (k : ℕ) := Node k × Node k

noncomputable def coreBoard {k : ℕ} (A : Matrix (Node k) (Node k) R) :
    Board (Join k) (Position k) R where
  adj := edge
  matrix := sparseMatrix A
  off x y h := by simp [sparseMatrix,h]
  firstRow := ⟨Sum.inl,Sum.inl_injective⟩
  firstCol := ⟨Sum.inl,Sum.inl_injective⟩
  marked e := by rcases e with ⟨r,c⟩; exact ⟨rfl,rfl⟩

/-- Numbered layers of two-vertex subdivisions, one step per designated join in
every layer. The order of different joins has no effect on their weights. -/
noncomputable def operations (k : ℕ) : ℕ → List (Join k)
  | 0 => []
  | h+1 => Finset.univ.toList ++ operations k h

@[simp] theorem count_operations (k h : ℕ) (e : Join k) : (operations k h).count e=h := by
  induction h with
  | zero => simp [operations]
  | succ h ih =>
    have once : (Finset.univ : Finset (Join k)).toList.count e=1 :=
      List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.mpr (Finset.mem_univ e))
    simp [operations,once,ih,Nat.add_comm]

@[simp] theorem length_operations (k h : ℕ) : (operations k h).length=h*(k+1)^2 := by
  induction h with
  | zero => simp [operations]
  | succ h ih => simp [operations,ih,Join,Node,pow_two,Nat.succ_mul,Nat.add_comm]

abbrev Side (k h : ℕ) := Board.Index (Position k) (operations k h).length

noncomputable def familyBoard {k : ℕ} (h : ℕ) (A : Matrix (Node k) (Node k) R) :
    Board (Join k) (Side k h) R := (coreBoard A).run (operations k h)

/-- The full family, for every number of subdividing pairs h. -/
theorem permanent_family {k : ℕ} (h : ℕ) (A : Matrix (Node k) (Node k) R) :
    (familyBoard h A).matrix.permanent=A.permanent :=
  ((coreBoard A).run_permanent _).trans (permanent_sparse A)

theorem degree_family {k : ℕ} (h : ℕ) (A : Matrix (Node k) (Node k) R) :
    (∀ x,Nat.card {y // (familyBoard h A).adj x y}≤3) ∧
    (∀ y,Nat.card {x // (familyBoard h A).adj x y}≤3) :=
  (coreBoard A).run_degrees left_degree right_degree _

theorem card_side (k h : ℕ) : Nat.card (Side k h)=(k+1)^2+(k+1)*k+h*(k+1)^2 := by
  rw [show Nat.card (Side k h) = _ from Board.index_card (I:=Position k) (operations k h).length,
    length_operations]
  simp [Position,Node,pow_two]

theorem labels_family {k : ℕ} (h : ℕ) (A : Matrix (Node k) (Node k) R) :
    ∀ u v, (familyBoard h A).matrix u v=0 ∨ (familyBoard h A).matrix u v=1 ∨
      ∃ i j,(familyBoard h A).matrix u v=A i j := by
  apply (coreBoard A).all_entries (fun z=>z=0 ∨ z=1 ∨ ∃ i j,z=A i j)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rintro (⟨u,v⟩|⟨u,j⟩) (⟨r,c⟩|⟨c,i⟩) <;> change _=0 ∨ _=1 ∨ ∃ _ _, _=_ <;>
      dsimp only [coreBoard,sparseMatrix] <;> split <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_,_,rfl⟩)

end SparsePermanent

#print axioms SparsePermanent.permanent_family
#print axioms SparsePermanent.degree_family
#print axioms SparsePermanent.count_operations
#print axioms SparsePermanent.card_side
#print axioms SparsePermanent.labels_family
