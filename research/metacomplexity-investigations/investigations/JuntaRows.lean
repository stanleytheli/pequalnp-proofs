import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! A legal two-bit partial row with individually fixed junta supports.
At every defined input one of its two supports certifies the entire row. -/
namespace MetaComplexity.JuntaRows
open Finset
variable {I : Type*} [DecidableEq I]
abbrev Point (I : Type*) := I → Bool
def Agree (S : Finset I) (x y : Point I) : Prop := ∀ i∈S, x i=y i
def Depends {D : Type*} (S : Finset I) (f : Point I → D) : Prop :=
  ∀ x y, Agree S x y → f x=f y
def Freezes (S : Finset I) (row : Point I → Option Bool) (x : Point I) : Prop :=
  ∀ y, Agree S y x → row y=row x

private lemma value_one {r : Option Bool} (h : r.getD false=true) : r=some true := by
  cases r with
  | none => cases h
  | some b => simpa using h

theorem row_support (A B : Finset I) (row : Point I → Option Bool)
    (presence : Depends A (fun y => (row y).isSome))
    (value : Depends B (fun y => (row y).getD false))
    (x : Point I) (b : Bool) (definedAt : row x = some b) :
    Freezes A row x ∨ Freezes B row x := by
  classical
  cases b with
  | true =>
    right
    intro y hy
    have h := value y x hy
    simp [definedAt] at h
    rw [definedAt]
    exact value_one h
  | false =>
    by_contra bad
    simp only [not_or] at bad
    obtain ⟨u, au, nu⟩ : ∃ u, Agree A u x ∧ row u≠row x := by
      simpa [Freezes] using bad.1
    obtain ⟨v, bv, nv⟩ : ∃ v, Agree B v x ∧ row v≠row x := by
      simpa [Freezes] using bad.2
    have pu := presence u x au
    have vv := value v x bv
    simp [definedAt] at pu vv nu nv
    have ru : row u=some true := by
      cases h : row u with
      | none => simp [h] at pu
      | some c => cases c <;> simp_all
    have rv : row v=none := by
      cases h : row v with
      | none => rfl
      | some c => cases c <;> simp_all
    let w : Point I := fun i => if i∈A then v i else u i
    have ap : Agree A w v := by intro i hi; simp [w,hi]
    have bp : Agree B w u := by
      intro i hi
      by_cases ha : i∈A
      · simpa [w,ha] using (bv i hi).trans (au i ha).symm
      · simp [w,ha]
    have zero := presence w v ap
    have one := value w u bp
    change (row w).isSome=(row v).isSome at zero
    change (row w).getD false=(row u).getD false at one
    rw [rv] at zero
    rw [ru] at one
    cases h : row w with
    | none => simp [h] at one
    | some c => simp [h] at zero

theorem inconsistent_support {Y : Type*} (row : Point I → Y → Option Bool)
    (A B : Y → Finset I) (q : ℕ) (cq : ∀y, (A y).card≤q ∧ (B y).card≤q)
    (hp : ∀y, Depends (A y) (fun x=>(row x y).isSome))
    (hv : ∀y, Depends (B y) (fun x=>(row x y).getD false))
    (witness : Y → Bool) (x : Point I)
    (bad : ∃ y b, row x y=some b ∧ witness y≠b) :
    ∃ S : Finset I, S.card≤q ∧ ∀ z, Agree S z x → ∃ y b, row z y=some b ∧ witness y≠b := by
  obtain ⟨y,b,hy,ne⟩ := bad
  rcases row_support (A y) (B y) (fun z=>row z y) (hp y) (hv y) x b hy with a|b'
  · exact ⟨A y,(cq y).1,fun z hz=>⟨y,b,(a z hz).trans hy,ne⟩⟩
  · exact ⟨B y,(cq y).2,fun z hz=>⟨y,b,(b' z hz).trans hy,ne⟩⟩
end MetaComplexity.JuntaRows
#print axioms MetaComplexity.JuntaRows.row_support
#print axioms MetaComplexity.JuntaRows.inconsistent_support
