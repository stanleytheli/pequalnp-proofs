import MatchingData
import Mathlib.LinearAlgebra.Matrix.Permanent

namespace SparsePermanent

abbrev Position (k : ℕ) := (Node k × Node k) ⊕ (Node k × Fin k)

def near {k : ℕ} (j : Fin k) (u : Node k) : Prop := u=j.castSucc ∨ u=j.succ

/-- Domain vertices are row ports and column gaps; codomain vertices are column
ports and row gaps. Each allowed pair is one edge of the bipartite graph. -/
def edge {k : ℕ} : Position k → Position k → Prop
  | .inl (r,c), .inl (u,v) => r=u ∧ c=v
  | .inl (r,c), .inr (u,j) => r=u ∧ near j c
  | .inr (c,j), .inl (r,v) => c=v ∧ near j r
  | .inr _, .inr _ => False

abbrev CoreMatching (k : ℕ) := {p : Equiv.Perm (Position k) // ∀ x, edge x (p x)}

namespace Selector
variable {k : ℕ}
noncomputable def which (a : Selector k) (u : Node k) : Option (Fin k) :=
  if h : ∃ j, a.port j=u then some h.choose else none

theorem which_eq_some (a : Selector k) (u : Node k) (j : Fin k) :
    a.which u=some j ↔ a.port j=u := by
  classical
  unfold which
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro e
      exact a.port.injective (h.choose_spec.trans e.symm)
  · rename_i h
    constructor
    · intro v
      cases v
    · intro e
      exact False.elim (h ⟨j,e⟩)

theorem which_eq_none (a : Selector k) (u : Node k) :
    a.which u=none ↔ ¬∃ j, a.port j=u := by
  classical
  unfold which
  split <;> simp_all

@[simp] theorem which_port (a : Selector k) (j : Fin k) : a.which (a.port j)=some j :=
  (a.which_eq_some _ _).mpr rfl

end Selector
namespace MatchingData
variable {k : ℕ}

noncomputable def forward (b : MatchingData k) : Position k → Position k
  | .inl (r,c) => match (b.row r).which c with
    | some j => .inr (r,j)
    | none => .inl (r,c)
  | .inr (c,j) => .inl ((b.col c).port j,c)

noncomputable def backward (b : MatchingData k) : Position k → Position k
  | .inl (r,c) => match (b.col c).which r with
    | some j => .inr (c,j)
    | none => .inl (r,c)
  | .inr (r,j) => .inl (r,(b.row r).port j)

theorem forward_backward (b : MatchingData k) (x : Position k) :
    b.forward (b.backward x)=x := by
  rcases x with ⟨r,c⟩ | ⟨r,j⟩
  · cases h : (b.col c).which r with
    | none =>
      have hh := ((b.row r).which_eq_none c).mpr ((b.agree r c).mpr (((b.col c).which_eq_none r).mp h))
      simp [forward,backward,h,hh]
    | some j =>
      have hh := ((b.col c).which_eq_some _ _).mp h
      simp [forward,backward,h,hh]
  · simp [forward,backward]

theorem backward_forward (b : MatchingData k) (x : Position k) :
    b.backward (b.forward x)=x := by
  rcases x with ⟨r,c⟩ | ⟨c,j⟩
  · cases h : (b.row r).which c with
    | none =>
      have hh := ((b.col c).which_eq_none r).mpr ((b.agree r c).mp (((b.row r).which_eq_none c).mp h))
      simp [forward,backward,h,hh]
    | some j =>
      have hh := ((b.row r).which_eq_some _ _).mp h
      simp [forward,backward,h,hh]
  · simp [forward,backward]

noncomputable def wires (b : MatchingData k) : CoreMatching k :=
  ⟨⟨b.forward,b.backward,b.backward_forward,b.forward_backward⟩, by
    rintro (⟨r,c⟩|⟨c,j⟩)
    · change edge _ (b.forward (.inl (r,c)))
      cases h : (b.row r).which c with
      | none => simp [forward,h,edge]
      | some j =>
        have eq := ((b.row r).which_eq_some _ _).mp h
        simpa [forward,h,edge,near,←eq] using (b.row r).adjacent j
    · exact ⟨rfl,(b.col c).adjacent j⟩⟩

end MatchingData
namespace CoreMatching
variable {k : ℕ}
variable (p : CoreMatching k)

private theorem appears_row (r : Node k) (j : Fin k) :
    ∃ c, p.val.symm (.inr (r,j)) = .inl (r,c) ∧ near j c := by
  have h := p.prop (p.val.symm (.inr (r,j)))
  rw [Equiv.apply_symm_apply] at h
  generalize eq : p.val.symm (.inr (r,j))=q at h ⊢
  rcases q with ⟨u,c⟩|⟨v,l⟩
  · obtain ⟨rfl,h⟩ := h
    exact ⟨c,rfl,h⟩
  · exact False.elim h

private theorem appears_col (c : Node k) (j : Fin k) :
    ∃ r, p.val (.inr (c,j)) = .inl (r,c) ∧ near j r := by
  have h := p.prop (.inr (c,j))
  generalize eq : p.val (.inr (c,j))=q at h ⊢
  rcases q with ⟨r,v⟩|⟨u,l⟩
  · obtain ⟨rfl,h⟩ := h
    exact ⟨r,rfl,h⟩
  · exact False.elim h

noncomputable def row (r : Node k) : Selector k where
  port := ⟨fun j => (p.appears_row r j).choose, by
    intro i j eq
    change (p.appears_row r i).choose = (p.appears_row r j).choose at eq
    have h := (p.appears_row r i).choose_spec.1
    rw [eq,←(p.appears_row r j).choose_spec.1] at h
    exact (Prod.mk.inj (Sum.inr.inj (p.val.symm.injective h))).2⟩
  adjacent j := (p.appears_row r j).choose_spec.2

noncomputable def col (c : Node k) : Selector k where
  port := ⟨fun j => (p.appears_col c j).choose, by
    intro i j eq
    change (p.appears_col c i).choose = (p.appears_col c j).choose at eq
    have h := (p.appears_col c i).choose_spec.1
    rw [eq,←(p.appears_col c j).choose_spec.1] at h
    exact (Prod.mk.inj (Sum.inr.inj (p.val.injective h))).2⟩
  adjacent j := (p.appears_col c j).choose_spec.2

theorem row_value (r : Node k) (j : Fin k) :
    p.val.symm (.inr (r,j))=.inl (r,(p.row r).port j) := (p.appears_row r j).choose_spec.1

theorem col_value (c : Node k) (j : Fin k) :
    p.val (.inr (c,j))=.inl ((p.col c).port j,c) := (p.appears_col c j).choose_spec.1

theorem row_unused (r c : Node k) : (¬∃ j, (p.row r).port j = c) ↔
    p.val (.inl (r,c))=.inl (r,c) := by
  constructor
  · intro free
    have h := p.prop (.inl (r,c))
    generalize eq : p.val (.inl (r,c))=q at h ⊢
    rcases q with ⟨u,v⟩ | ⟨u,j⟩
    · obtain ⟨rfl,rfl⟩ := h
      rfl
    · obtain ⟨rfl,_⟩ := h
      have q := (p.row_value r j).symm.trans (p.val.symm_apply_eq.mpr eq.symm)
      exact False.elim (free ⟨j,(Prod.mk.inj (Sum.inl.inj q)).2⟩)
  · rintro eq ⟨j,hit⟩
    have q := p.val.eq_symm_apply.mp (p.row_value r j).symm
    rw [hit,eq] at q
    cases q

theorem col_unused (r c : Node k) : (¬∃ j, (p.col c).port j = r) ↔
    p.val (.inl (r,c))=.inl (r,c) := by
  constructor
  · intro free
    have h := p.prop (p.val.symm (.inl (r,c)))
    rw [Equiv.apply_symm_apply] at h
    generalize eq : p.val.symm (.inl (r,c))=q at h
    rcases q with ⟨u,v⟩ | ⟨v,j⟩
    · obtain ⟨rfl,rfl⟩ := h
      exact p.val.eq_symm_apply.mp eq.symm
    · obtain ⟨vc,_⟩ := h
      subst v
      have q := (p.col_value c j).symm.trans (p.val.eq_symm_apply.mp eq.symm)
      exact False.elim (free ⟨j,(Prod.mk.inj (Sum.inl.inj q)).1⟩)
  · rintro eq ⟨j,hit⟩
    have q := p.col_value c j
    rw [hit,←eq] at q
    have zz := p.val.injective q
    cases zz

noncomputable def data : MatchingData k :=
  ⟨p.row,p.col,fun r c => (p.row_unused r c).trans (p.col_unused r c).symm⟩

end CoreMatching
end SparsePermanent
