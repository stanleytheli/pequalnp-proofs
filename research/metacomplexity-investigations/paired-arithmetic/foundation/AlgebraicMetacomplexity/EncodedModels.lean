import CopyCompiler
import FunctionalCNF
import SignedTransfer

namespace AlgebraicMeta
open Finset MvPolynomial CopyCompiler FunctionalCNF

/-- A positional description places every literal occurrence of the gate CNF
at a chosen copy of its original bit. The third premise is the erasure law:
on assignments equal at every copy, this placement reads the original CNF. -/
structure Placement {n k : ℕ} (net : Network n k) (out : Literal k) (count : Fin k → ℕ) where
  allowed : (Pos count → Bool) → Prop
  erase : ∀ w : Fin k → Bool,
    allowed (fun p => w p.1) ↔ net.valid w ∧ out.read w=true

abbrev Primary {n k : ℕ} (net : Network n k) (out : Literal k) :=
  {a : Fin n → Bool // out.read (net.eval a)=true}

abbrev Copied {n k : ℕ} {net : Network n k} {out : Literal k} {count : Fin k → ℕ}
    (p : Placement net out count) (flips : Pos count → Bool) :=
  {b : Pos count → Bool // Cycling count flips b ∧ p.allowed (logical count flips b)}

/-- The source assignment and every local gate/copy certificate extend
uniquely through both the Boolean gate and bounded-occurrence encodings. -/
def placedEquiv {n k : ℕ} {net : Network n k} {out : Literal k} {count : Fin k → ℕ}
    (p : Placement net out count) (flips : Pos count → Bool) :
    Primary net out ≃ Copied p flips :=
  (net.accepted_model_equiv out).trans <|
    (Equiv.subtypeEquivRight fun w => (p.erase w).symm).trans <| modelEquiv count flips p.allowed

/-- Each accepting Boolean input contributes exactly its intended monomial
to the 0/1/variable projection, after all duplicate wires are assigned one. -/
theorem placed_weight {n k : ℕ} {net : Network n k} {out : Literal k} {count : Fin k → ℕ}
    (p : Placement net out count) (flips : Pos count → Bool)
    {W R : Type*} [CommSemiring R] (r : Fin k → MvPolynomial W R)
    (orientation : ∀ v, flips ⟨v,0⟩ = true → r v=1) (a : Primary net out) :
    (∏ v, ∏ j : Fin (count v+1),
      if (placedEquiv p flips a).1 ⟨v,j⟩ then (if j=0 then r v else 1) else 1) =
      wireMonomial (net.eval a.1) r :=
  copied_monomial count flips (net.eval a.1) r orientation

open Classical in
theorem placed_sum {n k : ℕ} {net : Network n k} {out : Literal k} {count : Fin k → ℕ}
    (p : Placement net out count) (flips : Pos count → Bool)
    {W R : Type*} [CommSemiring R] (r : Fin k → MvPolynomial W R)
    (orientation : ∀ v, flips ⟨v,0⟩ = true → r v=1) :
    (∑ b : Copied p flips, ∏ v, ∏ j : Fin (count v+1),
      if b.1 ⟨v,j⟩ then (if j=0 then r v else 1) else 1) =
      ∑ a : Primary net out, wireMonomial (net.eval a.1) r := by
  classical
  let f (b : Copied p flips) := ∏ v, ∏ j : Fin (count v+1),
    if b.1 ⟨v,j⟩ then (if j=0 then r v else 1) else 1
  rw [← (placedEquiv p flips).sum_comp f]
  exact Finset.sum_congr rfl (fun a _ => placed_weight p flips r orientation a)

end AlgebraicMeta
#print axioms AlgebraicMeta.placedEquiv
#print axioms AlgebraicMeta.placed_sum
