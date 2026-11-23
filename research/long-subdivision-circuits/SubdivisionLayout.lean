import Mathlib
namespace Subdivision
open Finset
abbrev Assignment (n : ℕ) := Fin n → Bool
/-- Paths have disjoint internal coordinates, none of which is an original endpoint. -/
structure Layout (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  distinct : ∀ e, left e ≠ right e
  half : Fin m → ℕ
  long : ∀ e, 3 ≤ half e
  inner : (e : Fin m) → Fin (2*half e) ↪ Fin n
  apart : ∀ {e j} (i : Fin (2*half e)) (t : Fin (2*half j)), e≠j → inner e i≠inner j t
  notLeft : ∀ e i j, inner e i≠left j
  notRight : ∀ e i j, inner e i≠right j
namespace Layout
variable {n m : ℕ} (B : Layout n m)
def first (e : Fin m) : Fin (2*B.half e) := ⟨0,by have := B.long e; omega⟩
def head (e : Fin m) (side : Bool) := if side then B.left e else B.right e
def chain {k : ℕ} (l r : Bool) (z : Fin k → Bool) : Prop :=
  ∃ i, z i=true ∧ ((i.val=0 ∧ l=true) ∨ (i.val+1=k ∧ r=true) ∨ ∃ j : Fin k, j.val=i.val+1 ∧ z j=true)
def active (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) (x : Assignment n) : Prop :=
  if e∈S then chain (x (B.left e)) (x (B.right e)) (fun i => x (B.inner e i))
  else x (B.head e (o e))=true ∧ x (B.inner e (B.first e))=true
noncomputable def board (S : Finset (Fin m)) (o : Fin m → Bool) (x : Assignment n) : Bool := by
  classical
  exact decide (∃ e, B.active S o e x)
noncomputable def outside (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) (x : Assignment n) : Bool := by
  classical
  exact decide (∃ j, j≠e ∧ B.active S o j x)

end Layout
end Subdivision
