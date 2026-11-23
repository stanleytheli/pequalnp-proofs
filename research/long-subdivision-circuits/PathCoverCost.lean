import Mathlib

/-! Exact vertex-cover costs of paths with specified endpoint choices. -/
namespace Subdivision.PathCover
open Finset

/-- The internal path vertices appear in order between a and b. -/
def Covered : Bool → List Bool → Bool → Prop
  | a, [], b => a=true ∨ b=true
  | a, z::zs, b => (a=true ∨ z=true) ∧ Covered z zs b

def Optimum (k : ℕ) (a b : Bool) (c : ℕ) : Prop :=
  (∃ xs : List Bool, xs.length=k ∧ Covered a xs b ∧ xs.count true=c) ∧
  ∀ xs : List Bool, xs.length=k → Covered a xs b → c≤xs.count true

private theorem one (a b : Bool) : Optimum 1 a b (if a && b then 0 else 1) := by
  constructor
  · cases a <;> cases b
    · exact ⟨[true],by decide,by simp [Covered],by decide⟩
    · exact ⟨[true],by decide,by simp [Covered],by decide⟩
    · exact ⟨[true],by decide,by simp [Covered],by decide⟩
    · exact ⟨[false],by decide,by simp [Covered],by decide⟩
  · intro xs len good
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp len
    cases v <;> cases a <;> cases b <;> simp_all [Covered]

private theorem step {k c₀ c₁ : ℕ} (a b : Bool)
    (h₀ : Optimum k false b c₀) (h₁ : Optimum k true b c₁) :
    Optimum (k+1) a b (if a then min c₀ (c₁+1) else c₁+1) := by
  constructor
  · obtain ⟨xs,l0,p0,c0⟩ := h₀.1
    obtain ⟨ys,l1,p1,c1⟩ := h₁.1
    cases a with
    | false => exact ⟨true::ys,by simp [l1],by simp [Covered,p1],by simp [c1]⟩
    | true =>
      by_cases le : c₀≤c₁+1
      · exact ⟨false::xs,by simp [l0],by simp [Covered,p0],by simp [c0,Nat.min_eq_left le]⟩
      · exact ⟨true::ys,by simp [l1],by simp [Covered,p1],
          by simp [c1,Nat.min_eq_right (by omega : c₁+1≤c₀)]⟩
  · intro zs len good
    cases zs with
    | nil => simp at len
    | cons z zs =>
      have sublen : zs.length=k := by simpa using len
      cases z with
      | false =>
        have p0 : Covered false zs b := good.2
        have pos : a=true := good.1.resolve_right (by decide)
        have h := h₀.2 zs sublen p0
        simpa [pos] using (Nat.min_le_left c₀ (c₁+1)).trans h
      | true =>
        have p1 : Covered true zs b := good.2
        have h := h₁.2 zs sublen p1
        cases a <;> simp <;> omega

private theorem next_even (h : ℕ)
    (odd : ∀ a b, Optimum (2*h+1) a b (h+if a && b then 0 else 1)) :
    ∀ a b, Optimum (2*h+2) a b (h+1+if a || b then 0 else 1) := by
  intro a b
  have st := step a b (odd false b) (odd true b)
  convert st using 1
  cases a <;> cases b <;> simp

private theorem counts (h : ℕ) :
    (∀ a b, Optimum (2*h+1) a b (h+if a && b then 0 else 1)) ∧
    (∀ a b, Optimum (2*h+2) a b (h+1+if a || b then 0 else 1)) := by
  induction h with
  | zero =>
    have hodd (a b : Bool) : Optimum (2*0+1) a b (0+if a && b then 0 else 1) := by
      simpa using one a b
    exact ⟨hodd,next_even _ hodd⟩
  | succ h ih =>
    have ho (a b : Bool) : Optimum (2*(h+1)+1) a b (h+1+if a && b then 0 else 1) := by
      have st := step a b (ih.2 false b) (ih.2 true b)
      convert st using 1
      cases a <;> cases b <;> simp
    exact ⟨ho,next_even _ ho⟩

/-- A path with 2h+2 edges has 2h+1 internal vertices. -/
theorem even_length (h : ℕ) (left right : Bool) :
    Optimum (2*h+1) left right (h+if left && right then 0 else 1) :=
  (counts h).1 left right

/-- A path with 2h+1 edges has 2h internal vertices. -/
theorem odd_length {h : ℕ} (nontrivial : 1≤h) (left right : Bool) :
    Optimum (2*h) left right (h+if left || right then 0 else 1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
  convert (counts j).2 left right using 1

/-- An endpoint set can be enlarged to hit every odd path without increasing the
total endpoint cost plus path penalties for previously missed endpoints. -/
theorem cover_odd {V E : Type*} [DecidableEq V] [Fintype E]
    (left right : E → V) (odd : E → Bool) (T : Finset V) :
    let missOdd (X : Finset V) := Finset.univ.filter (fun e => odd e=true ∧ left e∉X ∧ right e∉X)
    let missEven (X : Finset V) := Finset.univ.filter (fun e => odd e=false ∧ (left e∉X ∨ right e∉X))
    ∃ T' : Finset V, T⊆T' ∧ (∀ e, odd e=true → left e∈T' ∨ right e∈T') ∧
      T'.card+(missEven T').card ≤ T.card+(missOdd T).card+(missEven T).card := by
  classical
  intro O E
  let T' := T ∪ (O T).image left
  have sub : T⊆T' := Finset.subset_union_left
  refine ⟨T',sub,?_,?_⟩
  · intro e ho
    by_cases l : left e∈T
    · exact Or.inl (sub l)
    by_cases r : right e∈T
    · exact Or.inr (sub r)
    exact Or.inl (Finset.mem_union_right _ (Finset.mem_image_of_mem left
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho,l,r⟩)))
  · have mono : E T'⊆E T := by
      intro e he
      obtain ⟨_,ev,w⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ev, w.imp (fun x h => x (sub h)) (fun x h => x (sub h))⟩
    have card := Finset.card_union_le T ((O T).image left)
    have cap : ((O T).image left).card≤(O T).card := Finset.card_image_le
    have raw := Finset.card_le_card mono
    change T'.card≤T.card+((O T).image left).card at card
    omega

end Subdivision.PathCover

#print axioms Subdivision.PathCover.odd_length
#print axioms Subdivision.PathCover.even_length
#print axioms Subdivision.PathCover.cover_odd
