import OccurrenceCycle
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma

namespace AlgebraicMeta.CopyCompiler
open Finset MvPolynomial

/-- Variable v has count(v)+1 named occurrence coordinates. Each has a fixed
choice of literal orientation. -/
abbrev Pos {V : Type*} (count : V → ℕ) := Σ v, Fin (count v+1)

variable {V W R : Type*} (count : V → ℕ) (flip : Pos count → Bool)

def logical (bits : Pos count → Bool) (p : Pos count) : Bool := xor (bits p) (flip p)

def physical (a : V → Bool) (p : Pos count) : Bool := xor (a p.1) (flip p)

theorem logical_physical (a : V → Bool) (p : Pos count) :
    logical count flip (physical count flip a) p = a p.1 := by
  unfold logical physical
  cases a p.1 <;> cases flip p <;> rfl

def pos (v : V) (i : ℕ) : Pos count :=
  ⟨v,⟨min i (count v),Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩⟩

/-- One two-literal implication per step and a closing implication.
The singleton cycle can omit its reflexive closing clause. -/
def Cycling (bits : Pos count → Bool) : Prop :=
  ∀ v,
    (∀ j, j<count v → logical count flip bits (pos count v j) ≤ logical count flip bits (pos count v (j+1))) ∧
    logical count flip bits (pos count v (count v)) ≤ logical count flip bits (pos count v 0)

def read (bits : Pos count → Bool) (v : V) : Bool := logical count flip bits ⟨v,0⟩

theorem physical_cycling (a : V → Bool) : Cycling count flip (physical count flip a) := by
  intro v
  constructor
  · intro i hi
    simp only [logical_physical,pos,le_refl]
  · simp only [logical_physical,pos,le_refl]

theorem logical_of_cycling {bits : Pos count → Bool} (h : Cycling count flip bits) (p : Pos count) :
    logical count flip bits p = read count flip bits p.1 := by
  obtain ⟨v,j⟩ := p
  have e := occurrence_cycle _ (fun i => logical count flip bits (pos count v i)) (h v).1 (h v).2
      j.val (Nat.le_of_lt_succ j.isLt)
  simpa [pos,read,Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)] using e

theorem read_physical (a : V → Bool) : read count flip (physical count flip a) = a := by
  funext v
  exact logical_physical count flip _ _

theorem physical_read {bits : Pos count → Bool} (h : Cycling count flip bits) :
    physical count flip (read count flip bits) = bits := by
  funext p
  change xor (read count flip bits p.1) (flip p) = bits p
  rw [← logical_of_cycling count flip h p]
  unfold logical
  cases bits p <;> cases flip p <;> rfl

/-- Each displayed formula on occurrences can be any predicate, allowing its
original clauses to retain their specific positions and signs. -/
def modelEquiv (accept : (Pos count → Bool) → Prop) :
    {a : V → Bool // accept (fun p => a p.1)} ≃
    {b : Pos count → Bool // Cycling count flip b ∧ accept (logical count flip b)} where
  toFun a := ⟨physical count flip a.1,physical_cycling count flip a.1,by
    simpa only [show logical count flip (physical count flip a.1) = (fun p => a.1 p.1) from
      funext (logical_physical count flip a.1)] using a.2⟩
  invFun b := ⟨read count flip b.1,by
    simpa only [← show logical count flip b.1 = (fun p => read count flip b.1 p.1) from
      funext (logical_of_cycling count flip b.2.1)] using b.2.2⟩
  left_inv a := Subtype.ext (read_physical count flip a.1)
  right_inv b := Subtype.ext (physical_read count flip b.2.1)

/-- A finite squarefree monomial specified directly by its Boolean exponents. -/
noncomputable def wireMonomial [Fintype V] [CommSemiring R] (a : V → Bool) (r : V → MvPolynomial W R) :
    MvPolynomial W R := ∏ v, if a v then r v else 1

/-- Project a single representative of each occurrence cycle and all duplicate
bits to one. A flipped distinguished representative may be discarded with
weight one, as happens for auxiliary wires in the planted construction. -/
theorem copied_monomial [Fintype V] [CommSemiring R] (a : V → Bool) (r : V → MvPolynomial W R)
    (orientation : ∀ v, flip ⟨v,0⟩ = true → r v=1) :
    (∏ v, ∏ j : Fin (count v+1),
      if physical count flip a ⟨v,j⟩ then (if j=0 then r v else 1) else 1) =
      wireMonomial a r := by
  classical
  unfold wireMonomial
  apply Finset.prod_congr rfl
  intro v hv
  rw [Finset.prod_eq_single_of_mem 0 (Finset.mem_univ _) (fun j _ hj => by simp [hj])]
  by_cases h : flip ⟨v,0⟩=true
  · simp [orientation v h]
  · have hf : flip ⟨v,0⟩=false := by simpa using h
    simp [physical,hf]

end AlgebraicMeta.CopyCompiler
#print axioms AlgebraicMeta.CopyCompiler.modelEquiv
#print axioms AlgebraicMeta.CopyCompiler.copied_monomial
