import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Push

/-! A descending code on the Boolean lattice forces a wide upward window with
a constant code after fixing only a bounded number of points. -/
namespace LimitedNegation
open Finset

theorem find_window {A : Type*} [DecidableEq A] (code : Finset A → ℕ)
    (down : Antitone code) (step : ℕ) (start : Finset A) :
    ∃ base : Finset A, start ⊆ base ∧ base.card ≤ start.card + code start * step ∧
      ∀ z : Finset A, base ⊆ z → z.card ≤ base.card+step → code z = code base := by
  classical
  suffices go : ∀ n, ∀ s : Finset A, code s=n → ∃ b : Finset A, s ⊆ b ∧
      b.card ≤ s.card+n*step ∧ ∀ z : Finset A, b⊆z → z.card≤b.card+step → code z=code b by
    exact go _ _ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro s hs
    by_cases stable : ∀ z : Finset A, s⊆z → z.card≤s.card+step → code z=code s
    · exact ⟨s,by rfl,by omega,stable⟩
    push_neg at stable
    obtain ⟨z,sz,hsize,hchange⟩ := stable
    have lt : code z < n := by have := down sz; omega
    obtain ⟨b,zb,bc,good⟩ := ih (code z) lt z rfl
    have price := Nat.mul_le_mul_right step (show code z+1 ≤ n by omega)
    rw [Nat.add_mul,Nat.one_mul] at price
    exact ⟨b,sz.trans zb,by omega,good⟩

/-- A response tree records successive NOT outputs with all preceding NOTs
fixed along its branch. The Boolean input to the next NOT is monotone, hence
the returned bit is antitone in the original input. -/
inductive PinTree (A : Type*) [Preorder A] : ℕ → Type _
  | done : PinTree A 0
  | next {n : ℕ} (bit : A → Bool) (anti : Antitone bit)
      (branch : Bool → PinTree A n) : PinTree A (n+1)

def PinTree.word {A : Type*} [Preorder A] : {n : ℕ} → PinTree A n → A → List Bool
  | _,.done,_ => []
  | _,.next b _ rest,x => b x :: (rest (b x)).word x

def PinTree.code {A : Type*} [Preorder A] : {n : ℕ} → PinTree A n → A → ℕ
  | _,.done,_ => 0
  | n+1,.next b _ rest,x => (if b x then 2^n else 0) + (rest (b x)).code x

theorem PinTree.code_lt {A : Type*} [Preorder A] {n : ℕ} (T : PinTree A n) (x : A) :
    T.code x < 2^n := by
  induction T with
  | done => simp [code]
  | @next n b hab rest ih =>
    have bound := ih (b x)
    cases hb : b x <;> simp only [code,hb,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add,Nat.pow_succ] at * <;> omega

theorem PinTree.code_down {A : Type*} [Preorder A] {n : ℕ} (T : PinTree A n) : Antitone T.code := by
  induction T with
  | done => intro _ _ _; rfl
  | @next n b hab rest ih =>
    intro x y xy
    have bm := hab xy
    cases hx : b x <;> cases hy : b y
    · simpa [code,hx,hy] using ih false xy
    · rw [hx,hy] at bm
      exact False.elim (by exact (by decide : ¬ (true ≤ false)) bm)
    · have h := (rest false).code_lt y
      simp only [code,hx,hy,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add]
      omega
    · simpa [code,hx,hy] using ih true xy

theorem PinTree.word_of_code {A : Type*} [Preorder A] {n : ℕ} (T : PinTree A n) (x y : A)
    (h : T.code x = T.code y) : T.word x=T.word y := by
  induction T with
  | done => rfl
  | @next n b hab rest ih =>
    have lo := (rest false).code_lt x
    have lo' := (rest false).code_lt y
    cases hx : b x <;> cases hy : b y <;> simp [word,code,hx,hy] at h ⊢
    · exact ih false h
    · omega
    · omega
    · exact ih true h

theorem stable_pins {A : Type*} [DecidableEq A] {t : ℕ} (T : PinTree (Finset A) t) (d : ℕ) :
    ∃ b : Finset A, b.card ≤ (2^t-1)*d ∧
      ∀ z : Finset A, b⊆z → z.card≤b.card+d → T.word z=T.word b := by
  obtain ⟨b,_,hc,good⟩ := find_window T.code T.code_down d ∅
  refine ⟨b,?_,fun z hz hs => T.word_of_code z b (good z hz hs)⟩
  have m : T.code ∅ ≤ 2^t-1 := by have := T.code_lt ∅; omega
  simpa using hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right d m) (∅ : Finset A).card)

end LimitedNegation
#print axioms LimitedNegation.find_window
#print axioms LimitedNegation.stable_pins
