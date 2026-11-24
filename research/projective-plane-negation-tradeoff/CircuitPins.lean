import StableWindow
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Hom.Basic

/-! Successive NOT bits of an actual straight-line computation. Wires are
numbered by naturals. The operand of each stage may be any monotone function
of the current wires, which includes binary AND, OR, and raw-wire selection. -/
namespace LimitedNegation
noncomputable section

abbrev Wires := ℕ → Bool

inductive Stage
  | positive (target : ℕ) (operand : Wires →o Bool)
  | negative (target : ℕ) (operand : Wires →o Bool)

def negations : List Stage → ℕ
  | [] => 0
  | .positive _ _ :: gs => negations gs
  | .negative _ _ :: gs => negations gs + 1

def run : List Stage → Wires → Wires
  | [],w => w
  | .positive i f :: gs,w => run gs (Function.update w i (f w))
  | .negative i f :: gs,w => run gs (Function.update w i (!(f w)))

def choices : List Stage → Wires → List Bool
  | [],_ => []
  | .positive i f :: gs,w => choices gs (Function.update w i (f w))
  | .negative i f :: gs,w => (!(f w)) :: choices gs (Function.update w i (!(f w)))

def pin : List Stage → List Bool → Wires → Wires
  | [],_,w => w
  | .positive i f :: gs,bits,w => pin gs bits (Function.update w i (f w))
  | .negative i _ :: gs,bits,w => pin gs bits.tail (Function.update w i (bits.headD false))

/-- Hardwiring the NOT values observed on an input reproduces every wire. -/
theorem pin_choices (gs : List Stage) (w : Wires) : pin gs (choices gs w) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => cases g <;> exact ih _

private def updateM {A : Type*} [Preorder A] (w : A →o Wires) (i : ℕ) (z : A →o Bool) :
    A →o Wires where
  toFun a := Function.update (w a) i (z a)
  monotone' := by
    intro a b h k
    by_cases hik : k=i
    · subst k
      simpa using z.monotone h
    · simpa [Function.update_of_ne hik] using w.monotone h k

def tree {A : Type*} [Preorder A] : (gs : List Stage) → (A →o Wires) → PinTree A (negations gs)
  | [],_ => .done
  | .positive i f :: gs,w => tree gs (updateM w i (f.comp w))
  | .negative i f :: gs,w => .next (fun x => !(f (w x))) (by
      intro x y h
      have v := f.monotone (w.monotone h)
      cases hx : f (w x) <;> cases hy : f (w y) <;> simp_all [Bool.le_iff_imp])
      (fun b => tree gs (updateM w i (OrderHom.const _ b)))

theorem tree_tracks {A : Type*} [Preorder A] (gs : List Stage) (w : A →o Wires) (x : A) :
    (tree gs w).word x = choices gs (w x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | positive i f => exact ih _
    | negative i f =>
      change (!(f (w x))) :: _ = (!(f (w x))) :: _
      exact congrArg (List.cons _) (ih _)

/-- At most (2^t-1)h bits must be set before every NOT of the circuit remains
constant on the next h upper Hamming layers. At these inputs a single frozen
positive program reproduces all output wires simultaneously. -/
theorem circuit_window {A : Type*} [DecidableEq A] (gs : List Stage) (input : Finset A →o Wires)
    (h : ℕ) :
    ∃ base : Finset A, base.card ≤ (2^(negations gs)-1)*h ∧
      ∀ z : Finset A, base ⊆ z → z.card ≤ base.card+h →
        pin gs (choices gs (input base)) (input z) = run gs (input z) := by
  obtain ⟨b,hb,good⟩ := stable_pins (tree gs input) h
  refine ⟨b,hb,?_⟩
  intro z hz hs
  have same := good z hz hs
  rw [tree_tracks,tree_tracks] at same
  rw [← same,pin_choices]

end
end LimitedNegation
#print axioms LimitedNegation.tree_tracks
#print axioms LimitedNegation.circuit_window
