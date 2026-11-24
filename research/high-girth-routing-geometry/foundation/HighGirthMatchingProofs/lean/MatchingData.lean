import Selector
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace SparsePermanent
variable (k : ℕ)
abbrev Node := Fin (k+1)

/-- Internal matchings of every row and column selector. The same join is left
unmatched by its row and its column. The edge-set formulation is linked below. -/
structure MatchingData where
  row : Node k → Selector k
  col : Node k → Selector k
  agree : ∀ r c, (¬∃ j, (row r).port j = c) ↔ (¬∃ j, (col c).port j = r)

namespace MatchingData
variable {k}

@[ext] theorem ext {a b : MatchingData k} (row : a.row = b.row) (col : a.col = b.col) : a=b := by
  cases a; cases b; cases row; cases col; rfl

theorem holes (a : MatchingData k) (r c : Node k) :
    c=Selector.equivPort (a.row r) ↔ r=Selector.equivPort (a.col c) := by
  simpa only [Selector.unused] using a.agree r c

noncomputable def movement (a : MatchingData k) : Equiv.Perm (Node k) where
  toFun r := Selector.equivPort (a.row r)
  invFun c := Selector.equivPort (a.col c)
  left_inv r := ((a.holes r _).mp rfl).symm
  right_inv c := ((a.holes _ c).mpr rfl).symm

def ofPerm (p : Equiv.Perm (Node k)) : MatchingData k where
  row r := Selector.atHole (p r)
  col c := Selector.atHole (p.symm c)
  agree r c := by
    rw [Selector.unused_iff, Selector.unused_iff]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      simp

/-- The bijection preserves each exact choice of the original row-column joins. -/
noncomputable def equivPerm : MatchingData k ≃ Equiv.Perm (Node k) where
  toFun := movement
  invFun := ofPerm
  left_inv a := by
    apply ext <;> funext i <;> exact Selector.atHole_equivPort _
  right_inv p := by
    apply Equiv.ext
    intro i
    exact Selector.equivPort_atHole _

noncomputable instance : Fintype (MatchingData k) := Fintype.ofEquiv _ equivPerm.symm

@[simp] theorem movement_ofPerm (p : Equiv.Perm (Node k)) : movement (ofPerm p)=p :=
  equivPerm.right_inv p

end MatchingData

end SparsePermanent

#print axioms SparsePermanent.MatchingData.equivPerm
