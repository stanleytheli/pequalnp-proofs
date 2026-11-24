import Girth
import FlowSquare
import FlowUpper

namespace SparsePermanent

/-- Exact Mathlib girth for every dense dimension m=k+2 and subdivision depth h. -/
theorem family_egirth_eq {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node (k+1)) (Node (k+1)) R) :
    (bipGraph (familyBoard h A).adj).egirth=((4*(2*h+3) : ℕ) : ℕ∞) := by
  apply le_antisymm _ (family_egirth_lower h A)
  obtain ⟨Z,hm⟩:=lift_family_flow h A (Square.square k)
  change Z.mass=(Square.square k).mass+2*h*CoreFlow.joinMass (Square.square k) at hm
  rw [Square.mass,Square.joins] at hm
  have live : ∃ x y,Z.val x y≠0 := by
    by_contra! off
    have z : Z.mass=0 := by simp [Flow.mass,off]
    omega
  obtain ⟨x,y,pos⟩:=live
  have exactMass : Z.mass=4*(2*h+3) := by omega
  rw [←exactMass]
  exact CycleFlow.egirth_le_mass Z pos

theorem family_girth_eq {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node (k+1)) (Node (k+1)) R) :
    (bipGraph (familyBoard h A).adj).girth=4*(2*h+3) := by
  rw [SimpleGraph.girth,family_egirth_eq]
  rfl

end SparsePermanent
#print axioms SparsePermanent.family_egirth_eq
#print axioms SparsePermanent.family_girth_eq
