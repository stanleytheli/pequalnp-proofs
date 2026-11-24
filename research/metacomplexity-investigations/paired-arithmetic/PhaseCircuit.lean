import FunctionalCNF

namespace AlgebraicMeta.PhaseCircuit
open FunctionalCNF

def majority (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-- Both directions of the majority gate relation use only three-literal
clauses, one positive and one negative implication per pair of inputs. -/
def majorityClauses (x y z out : Bool) : Prop :=
  ((!x) || (!y) || out)=true ∧ (x || y || (!out))=true ∧
  ((!x) || (!z) || out)=true ∧ (x || z || (!out))=true ∧
  ((!y) || (!z) || out)=true ∧ (y || z || (!out))=true

theorem majority_iff (x y z out : Bool) : majorityClauses x y z out ↔ out=majority x y z := by
  cases x <;> cases y <;> cases z <;> cases out <;> simp [majorityClauses,majority]

def reference : Op → Bool → Bool
  | .meet, r => r
  | .join, r => !r

theorem relative_gate (op : Op) (r x y z : Bool) :
    majorityClauses x y (reference op r) z ↔ op.clauses (xor x r) (xor y r) (xor z r) := by
  cases op <;> cases r <;> cases x <;> cases y <;> cases z <;>
    simp [majorityClauses,reference,Op.clauses]

def decode {k : ℕ} (r : Bool) (w : Fin k → Bool) : Fin k → Bool := fun i => xor (w i) r

theorem read_decode {k : ℕ} (lit : Literal k) (w : Fin k → Bool) (r : Bool) :
    lit.read (decode r w)=xor (lit.read w) r := by
  rcases lit with ⟨i,s⟩
  unfold Literal.read decode
  cases s <;> cases w i <;> cases r <;> rfl

def phased {n k : ℕ} (net : Network n k) (r : Bool) (w : Fin k → Bool) : Prop :=
  match net with
  | .inputs => True
  | .add old g => phased old r (prior w) ∧ majorityClauses (g.left.read (prior w))
      (g.right.read (prior w)) (reference g.op r) (w (Fin.last _))

theorem phased_iff {n k : ℕ} (net : Network n k) (r : Bool) (w : Fin k → Bool) :
    phased net r w ↔ net.valid (decode r w) := by
  induction net with
  | inputs => rfl
  | add old g ih =>
    change (phased old r (prior w) ∧ _) ↔ (old.valid (decode r (prior w)) ∧
      g.op.clauses (g.left.read (decode r (prior w))) (g.right.read (decode r (prior w)))
        (xor (w (Fin.last _)) r))
    rw [ih,relative_gate,read_decode,read_decode]

def permit (r flag : Bool) : Prop := ((!r) || (!flag))=true

theorem antipodal_gate (r flag : Bool) :
    permit r flag ∧ permit (!r) (!flag) ↔ xor flag r=true := by
  cases r <;> cases flag <;> simp [permit]

end AlgebraicMeta.PhaseCircuit
#print axioms AlgebraicMeta.PhaseCircuit.phased_iff
#print axioms AlgebraicMeta.PhaseCircuit.antipodal_gate
