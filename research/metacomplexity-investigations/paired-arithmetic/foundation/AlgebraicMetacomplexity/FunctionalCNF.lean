import Mathlib.Data.Fin.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Defs

namespace AlgebraicMeta.FunctionalCNF

structure Literal (n : ℕ) where
  wire : Fin n
  positive : Bool

def Literal.read {n : ℕ} (l : Literal n) (w : Fin n → Bool) : Bool :=
  if l.positive then w l.wire else !(w l.wire)

inductive Op where | meet | join

def Op.run : Op → Bool → Bool → Bool
  | .meet, x, y => x && y
  | .join, x, y => x || y

/-- At most three literals in each clause, including the two signed inputs. -/
def Op.clauses (op : Op) (x y z : Bool) : Prop :=
  match op with
  | .meet => ((!z) || x) = true ∧ ((!z) || y) = true ∧ (z || (!x) || (!y)) = true
  | .join => (z || (!x)) = true ∧ (z || (!y)) = true ∧ ((!z) || x || y) = true

theorem Op.clauses_iff (op : Op) (x y z : Bool) : op.clauses x y z ↔ z=op.run x y := by
  cases op <;> cases x <;> cases y <;> cases z <;> simp [Op.clauses,Op.run]

structure Gate (k : ℕ) where
  op : Op
  left : Literal k
  right : Literal k

inductive Network (n : ℕ) : ℕ → Type where
  | inputs : Network n n
  | add {k} : Network n k → Gate k → Network n (k+1)

def prior {k : ℕ} (w : Fin (k+1) → Bool) : Fin k → Bool := fun i => w i.castSucc

def append {k : ℕ} (w : Fin k → Bool) (b : Bool) : Fin (k+1) → Bool := Fin.lastCases b w

@[simp] theorem prior_append {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    prior (append w b)=w := by funext i; simp [prior,append]

@[simp] theorem last_append {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    append w b (Fin.last k)=b := by simp [append]

theorem append_prior {k : ℕ} (w : Fin (k+1) → Bool) :
    append (prior w) (w (Fin.last k))=w := by
  funext i
  induction i using Fin.lastCases <;> simp [append,prior]

def Network.eval {n k : ℕ} (net : Network n k) (a : Fin n → Bool) : Fin k → Bool :=
  match net with
  | .inputs => a
  | .add old gate =>
      let w := old.eval a
      append w (gate.op.run (gate.left.read w) (gate.right.read w))

def Network.roots {n k : ℕ} (net : Network n k) (w : Fin k → Bool) : Fin n → Bool :=
  match net with
  | .inputs => w
  | .add old _ => old.roots (prior w)

def Network.valid {n k : ℕ} (net : Network n k) (w : Fin k → Bool) : Prop :=
  match net with
  | .inputs => True
  | .add old gate =>
      old.valid (prior w) ∧ gate.op.clauses (gate.left.read (prior w))
        (gate.right.read (prior w)) (w (Fin.last _))

theorem Network.roots_eval {n k : ℕ} (net : Network n k) (x : Fin n → Bool) :
    net.roots (net.eval x) = x := by
  induction net with
  | inputs => rfl
  | add old gate ih => simpa [Network.roots,Network.eval] using ih

theorem Network.eval_valid {n k : ℕ} (net : Network n k) (x : Fin n → Bool) :
    net.valid (net.eval x) := by
  induction net with
  | inputs => trivial
  | add old gate ih => simpa only [Network.valid,Network.eval,prior_append,last_append,
      Op.clauses_iff,and_true,eq_self] using ih

theorem Network.valid_reconstruct {n k : ℕ} (net : Network n k) (w : Fin k → Bool)
    (h : net.valid w) : net.eval (net.roots w) = w := by
  induction net with
  | inputs => rfl
  | add old gate ih =>
      obtain ⟨ho,hg⟩ := h
      have eq := ih (prior w) ho
      simp only [Network.eval,Network.roots,eq]
      rw [← (Op.clauses_iff _ _ _ _).mp hg]
      exact append_prior w

/-- A forced circuit output has one satisfying Tseitin assignment per accepted
primary input, and every satisfying Tseitin assignment arises this way. -/
def Network.accepted_model_equiv {n k : ℕ} (net : Network n k) (output : Literal k) :
    {a : Fin n → Bool // output.read (net.eval a)=true} ≃
    {w : Fin k → Bool // net.valid w ∧ output.read w=true} where
  toFun a := ⟨net.eval a.1,net.eval_valid _,a.2⟩
  invFun w := ⟨net.roots w.1,by simpa only [net.valid_reconstruct w.1 w.2.1] using w.2.2⟩
  left_inv a := Subtype.ext (net.roots_eval _)
  right_inv w := Subtype.ext (net.valid_reconstruct _ w.2.1)

end AlgebraicMeta.FunctionalCNF
#print axioms AlgebraicMeta.FunctionalCNF.Op.clauses_iff
#print axioms AlgebraicMeta.FunctionalCNF.Network.accepted_model_equiv
