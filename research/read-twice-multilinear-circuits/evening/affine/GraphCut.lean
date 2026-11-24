import CutRank
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Flatten the actual graph edge predicate on an arbitrary division of its
vertex variables. A crossing induced matching supplies the disjointness minor. -/
namespace CutRank
open scoped BigOperators
noncomputable section
variable {I A B K : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B] [Field K]

def internalEdge (G : SimpleGraph (A ⊕ B)) (x : A → Bool) (y : B → Bool) : Prop :=
  ∃ a b, G.Adj a b ∧ Sum.elim x y a=true ∧ Sum.elim x y b=true

def truth (G : SimpleGraph (A ⊕ B)) : Matrix (A→Bool) (B→Bool) K := by
  classical
  exact fun x y => if internalEdge G x y then 0 else 1

def extendBits {U : Type*} (a : I ↪ U) (x : I → Bool) (u : U) : Bool := by
  classical
  exact decide (∃ i, a i=u ∧ x i=true)

lemma extendBits_iff {U : Type*} (a : I ↪ U) (x : I → Bool) (u : U) :
    extendBits a x u=true ↔ ∃ i, a i=u ∧ x i=true := by classical simp [extendBits]

theorem overlap_restriction (G : SimpleGraph (A ⊕ B)) (a : I ↪ A) (b : I ↪ B)
    (noLeft : ∀ i j, ¬ G.Adj (Sum.inl (a i)) (Sum.inl (a j)))
    (noRight : ∀ i j, ¬ G.Adj (Sum.inr (b i)) (Sum.inr (b j)))
    (across : ∀ i j, G.Adj (Sum.inl (a i)) (Sum.inr (b j)) ↔ i=j)
    (x y : I → Bool) :
    internalEdge G (extendBits a x) (extendBits b y) ↔ ∃ i, x i=true ∧ y i=true := by
  constructor
  · rintro ⟨p,q,he,hp,hq⟩
    cases p with
    | inl u =>
      obtain ⟨i,rfl,hx⟩ := (extendBits_iff a x u).mp hp
      cases q with
      | inl v =>
        obtain ⟨j,rfl,_⟩ := (extendBits_iff a x v).mp hq
        exact (noLeft i j he).elim
      | inr v =>
        obtain ⟨j,rfl,hy⟩ := (extendBits_iff b y v).mp hq
        exact ⟨i,hx,(across i j).mp he ▸ hy⟩
    | inr u =>
      obtain ⟨i,rfl,hy⟩ := (extendBits_iff b y u).mp hp
      cases q with
      | inr v =>
        obtain ⟨j,rfl,_⟩ := (extendBits_iff b y v).mp hq
        exact (noRight i j he).elim
      | inl v =>
        obtain ⟨j,rfl,hx⟩ := (extendBits_iff a x v).mp hq
        exact ⟨j,hx,(across j i).mp he.symm ▸ hy⟩
  · rintro ⟨i,hx,hy⟩
    exact ⟨_,_,(across i i).mpr rfl,(extendBits_iff a x _).mpr ⟨i,rfl,hx⟩,
      (extendBits_iff b y _).mpr ⟨i,rfl,hy⟩⟩

theorem product_value (x y : I → Bool) :
    disjointness I K x y = if ∃ i, x i=true ∧ y i=true then 0 else 1 := by
  classical
  by_cases h : ∃ i, x i=true ∧ y i=true
  · rw [if_pos h]
    obtain ⟨i,hx,hy⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [edge,hx,hy])
  · rw [if_neg h]
    apply Finset.prod_eq_one
    intro i _
    cases hx : x i <;> cases hy : y i <;> simp [edge,hx,hy]
    exact (h ⟨i,hx,hy⟩).elim

theorem induced_matching_ranks (G : SimpleGraph (A ⊕ B)) (a : I ↪ A) (b : I ↪ B)
    (noLeft : ∀ i j, ¬ G.Adj (Sum.inl (a i)) (Sum.inl (a j)))
    (noRight : ∀ i j, ¬ G.Adj (Sum.inr (b i)) (Sum.inr (b j)))
    (across : ∀ i j, G.Adj (Sum.inl (a i)) (Sum.inr (b j)) ↔ i=j) :
    2^Fintype.card I ≤ (truth (K:=K) G).rank ∧
    2^Fintype.card I ≤ Matrix.rank (fun x y => 1-truth (K:=K) G x y)+1 := by
  classical
  have w : (truth (K:=K) G).submatrix (extendBits a) (extendBits b) = disjointness I K := by
    ext x y
    simp only [Matrix.submatrix_apply,truth,product_value,overlap_restriction G a b noLeft noRight across]
  exact ⟨independent_cut_lower _ _ _ w,edge_cut_lower _ _ _ w⟩

end
end CutRank
#print axioms CutRank.induced_matching_ranks
