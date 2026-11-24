import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

namespace AlgebraicMeta.AntipodalFloor
open Finset

/-- In homogeneous degree d on a 2d-element universe, a top addition on
disjoint sets of variables can only contribute one monomial from each side. -/
theorem add_support {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (s : Finset (Finset V)) (l r : Finset V) (size : Fintype.card V=2*d)
    (separate : Disjoint l r) (degree : ∀ a∈s,a.card=d)
    (split : ∀ a∈s,a⊆l ∨ a⊆r)
    (leftHit : ∃ a∈s,a⊆l) (rightHit : ∃ a∈s,a⊆r) :
    ∀ a∈s, a=l ∨ a=r := by
  obtain ⟨a,ha,al⟩ := leftHit
  obtain ⟨b,hb,br⟩ := rightHit
  have ll := card_le_card al
  have rr := card_le_card br
  rw [degree a ha] at ll
  rw [degree b hb] at rr
  have ur := card_le_univ (l∪r)
  rw [card_union_of_disjoint separate,size] at ur
  have lc : l.card=d := by omega
  have rc : r.card=d := by omega
  intro x hx
  rcases split x hx with inl|inr
  · exact Or.inl (eq_of_subset_of_card_le inl (by rw [lc,degree x hx]))
  · exact Or.inr (eq_of_subset_of_card_le inr (by rw [rc,degree x hx]))

def complement {A : Type*} (f : A → Bool) : A → Bool := fun i => !(f i)

theorem complement_ne {A : Type*} [Nonempty A] (a : A → Bool) : complement a ≠ a := by
  classical
  intro eq
  have h := congrFun eq (Classical.choice ‹Nonempty A›)
  simp [complement] at h

/-- A genuine product's rectangle closure forces a second antipodal pair
whenever its support contains one pair and both variable sides are nonempty. -/
theorem product_forces_second {A B : Type*} [Nonempty A] [Nonempty B]
    (present : (A → Bool) → (B → Bool) → Prop)
    (rectangle : ∀ {u v x y}, present u v → present x y → present u y)
    (x : A → Bool) (y : B → Bool) (p : present x y)
    (q : present (complement x) (complement y)) :
    present x (complement y) ∧ present (complement x) y ∧
    (x,complement y) ≠ (x,y) ∧ (x,complement y) ≠ (complement x,complement y) := by
  refine ⟨rectangle p q,rectangle q p,?_,?_⟩
  · intro e
    exact complement_ne y (congrArg Prod.snd e)
  · intro e
    exact complement_ne x (congrArg Prod.fst e).symm

end AlgebraicMeta.AntipodalFloor
#print axioms AlgebraicMeta.AntipodalFloor.add_support
#print axioms AlgebraicMeta.AntipodalFloor.product_forces_second
