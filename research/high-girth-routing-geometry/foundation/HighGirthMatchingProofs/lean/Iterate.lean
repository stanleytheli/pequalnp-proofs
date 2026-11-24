import Degree
import CorePerm
import OddSubdivision

namespace SparsePermanent
open Finset

variable {I : Type*}

/-- The support of the physical three-edge replacement, expressed by adjacency
from input/left column x to output/right row y. -/
def divideAdj (E : I → I → Prop) (r c : I) : Option I → Option I → Prop
  | none,none => True
  | none,some y => y=r
  | some x,none => x=c
  | some x,some y => E x y ∧ ¬(x=c ∧ y=r)

theorem divideAdj_transpose (E : I → I → Prop) (r c : I) (x y : Option I) :
    divideAdj E r c x y ↔ divideAdj (fun a b=>E b a) c r y x := by
  cases x <;> cases y <;> simp [divideAdj,and_comm]

private def oldNeighbors (E : I → I → Prop) (r c x : I) (hit : E c r) :
    {y // divideAdj E r c (some x) y} ↪ {y // E x y} where
  toFun y := ⟨y.val.getD r,by
    rcases y with ⟨_|u,h⟩
    · change x=c at h
      subst x
      exact hit
    · exact h.1⟩
  inj' := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ eq
    have same := congrArg Subtype.val eq
    change a.getD r=b.getD r at same
    apply Subtype.ext
    rcases a with _|u <;> rcases b with _|v
    · rfl
    · exact False.elim (hb.2 ⟨ha,same.symm⟩)
    · exact False.elim (ha.2 ⟨hb,same⟩)
    · exact congrArg some same

private def newNeighbors (E : I → I → Prop) (r c : I) :
    {y // divideAdj E r c none y} ↪ Bool where
  toFun u := u.val.isSome
  inj' := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ eq
    apply Subtype.ext
    rcases a with _|u <;> rcases b with _|v
    · rfl
    · cases eq
    · cases eq
    · exact congrArg some (ha.trans hb.symm)

theorem divideAdj_left [Finite I] (E : I → I → Prop) (r c : I) (hit : E c r)
    (degree : ∀ x, Nat.card {y // E x y} ≤ 3) (x : Option I) :
    Nat.card {y // divideAdj E r c x y} ≤ 3 := by
  cases x with
  | none =>
    have b := Nat.card_le_card_of_injective _ (newNeighbors E r c).injective
    exact b.trans (by simp)
  | some x => exact (Nat.card_le_card_of_injective _ (oldNeighbors E r c x hit).injective).trans (degree x)

theorem divideAdj_right [Finite I] (E : I → I → Prop) (r c : I) (hit : E c r)
    (degree : ∀ y, Nat.card {x // E x y} ≤ 3) (y : Option I) :
    Nat.card {x // divideAdj E r c x y} ≤ 3 := by
  have eq := Nat.card_congr (Equiv.subtypeEquivRight (fun x => divideAdj_transpose E r c x y))
  exact eq.trans_le (divideAdj_left (fun u v => E v u) c r hit degree y)

structure Board (D I R : Type*) [Zero R] where
  adj : I → I → Prop
  matrix : Matrix I I R
  off : ∀ x y, ¬adj x y → matrix y x=0
  firstRow : D ↪ I
  firstCol : D ↪ I
  marked : ∀ e, adj (firstCol e) (firstRow e)

namespace Board
variable {D R : Type*} [DecidableEq D] [CommSemiring R]

private def bump (f : D ↪ I) (e : D) : D ↪ Option I where
  toFun d := if d=e then none else some (f d)
  inj' := by
    intro a b eq
    by_cases ha : a=e <;> by_cases hb : b=e <;> simp_all

def step [DecidableEq I] (B : Board D I R) (e : D) : Board D (Option I) R where
  adj := divideAdj B.adj (B.firstRow e) (B.firstCol e)
  matrix := divideEdge B.matrix (B.firstRow e) (B.firstCol e)
  off := by
    rintro (_|x) (_|y) h
    · exact False.elim (h trivial)
    · exact if_neg h
    · exact if_neg h
    · dsimp [divideEdge]
      by_cases same : y=B.firstRow e ∧ x=B.firstCol e
      · simp [same]
      · rw [if_neg same]
        exact B.off x y (fun hit => h ⟨hit,fun both=>same both.symm⟩)
  firstRow := bump B.firstRow e
  firstCol := ⟨fun d=>some (B.firstCol d),fun _ _ eq =>B.firstCol.injective (Option.some.inj eq)⟩
  marked d := by
    change divideAdj _ _ _ (some (B.firstCol d)) (if d=e then none else some (B.firstRow d))
    by_cases same : d=e
    · subst d
      rw [if_pos rfl]
      rfl
    · rw [if_neg same]
      exact ⟨B.marked d, fun both => same (B.firstCol.injective both.1)⟩

def Index (I : Type*) : ℕ → Type _
  | 0 => I
  | n+1 => Option (Index I n)

instance indexFin [Fintype I] : (n : ℕ) → Fintype (Index I n)
  | 0 => inferInstanceAs (Fintype I)
  | n+1 => letI := indexFin n
           inferInstanceAs (Fintype (Option (Index I n)))

instance indexDec [DecidableEq I] : (n : ℕ) → DecidableEq (Index I n)
  | 0 => inferInstanceAs (DecidableEq I)
  | n+1 => letI := indexDec n
           inferInstanceAs (DecidableEq (Option (Index I n)))

-- All operations below are combinatorial and need only finite equality decisions.
noncomputable def run [DecidableEq I] (B : Board D I R) :
    (ops : List D) → Board D (Index I ops.length) R
  | [] => B
  | d::ds => (run B ds).step d

theorem run_permanent [Fintype I] [DecidableEq I] (B : Board D I R) (ops : List D) :
    (B.run ops).matrix.permanent=B.matrix.permanent := by
  induction ops with
  | nil => rfl
  | cons d ds ih =>
    exact (permanent_divideEdge (B.run ds).matrix ((B.run ds).firstRow d) ((B.run ds).firstCol d)).trans ih

theorem run_degrees [Fintype I] [DecidableEq I] (B : Board D I R)
    (left : ∀ x, Nat.card {y // B.adj x y}≤3) (right : ∀ y, Nat.card {x // B.adj x y}≤3)
    (ops : List D) :
    (∀ x, Nat.card {y // (B.run ops).adj x y}≤3) ∧
    (∀ y, Nat.card {x // (B.run ops).adj x y}≤3) := by
  induction ops with
  | nil => exact ⟨left,right⟩
  | cons d ds ih =>
    exact ⟨divideAdj_left _ _ _ ((B.run ds).marked d) ih.1,
      divideAdj_right _ _ _ ((B.run ds).marked d) ih.2⟩

theorem index_card [Fintype I] (n : ℕ) : Nat.card (Index I n)=Nat.card I+n := by
  induction n with
  | zero => simp [Index]
  | succ n ih =>
    simp only [Nat.card_eq_fintype_card] at ih ⊢
    change Fintype.card (Option (Index I n)) = _
    rw [Fintype.card_option,ih]
    omega

end Board
end SparsePermanent

#print axioms SparsePermanent.Board.run_permanent
#print axioms SparsePermanent.Board.run_degrees
