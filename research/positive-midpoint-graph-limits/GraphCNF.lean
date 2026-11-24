import AffinePins

namespace Midpoint
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {I L R : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

structure Clause (I : Type*) where
  constant : Prop
  positive : Finset I
  negative : Finset I

def Clause.holds (c : Clause I) (x : Finset I) : Prop :=
  c.constant ∨ (∃ i∈c.positive,i∈x) ∨ (∃ i∈c.negative,i∉x)

lemma clause_of_affine (f : Finset I→ℝ) (aff : AffineTable f) (pos : ∀ x,0≤f x) :
    ∃ c : Clause I, ∀ x, 0<f x ↔ c.holds x := by
  obtain ⟨b,p,n,h⟩ := positive_clause f aff pos
  exact ⟨⟨b,p,n⟩,h⟩

/-- The Boolean support of a midpoint-bounded positive bipartite graph limit
has one shared literal clause per vertex, with only unary and opposite-pair
requirements. A false global constant covers the identically zero case. -/
theorem graph_CNF (edge : L→R→Prop) (c : ℕ→ℝ) (a : ℕ→L→ℝ) (b : ℕ→R→ℝ)
    (u : ℕ→L→Finset I→ℝ) (v : ℕ→R→Finset I→ℝ) (f : Finset I→ℝ) (M : ℝ) (cs : ∀ j,0≤c j)
    (ba : ∀ j i,0≤a j i ∧ a j i≤1) (bb : ∀ j i,0≤b j i ∧ b j i≤1)
    (bu : ∀ j i x,0≤u j i x ∧ u j i x≤1) (bv : ∀ j i x,0≤v j i x ∧ v j i x≤1)
    (au : ∀ j i,AffineTable (u j i)) (av : ∀ j i,AffineTable (v j i))
    (hu : ∀ j i x,u j i x≤2*a j i) (hv : ∀ j i x,v j i x≤2*b j i)
    (bound : ∀ j,c j*prob edge (a j) (b j) ≤ M)
    (conv : ∀ x,Tendsto (fun j=>c j*prob edge (fun i=>u j i x) (fun i=>v j i x)) atTop (𝓝 (f x))) :
    ∃ ready : Prop, ∃ left : L→Prop, ∃ right : R→Prop, ∃ pair : L→R→Prop,
      ∃ A : L→Clause I, ∃ B : R→Clause I, ∀ x, 0<f x ↔
        ready ∧ (∀ l,left l → (A l).holds x) ∧ (∀ r,right r → (B r).holds x) ∧
          (∀ l r,pair l r → (A l).holds x ∨ (B r).holds x) := by
  classical
  obtain ⟨φ,mono,D,E,G,d0,e0,ld,le_,rep⟩ :=
    midpoint_pairs edge c a b u v f M cs ba bb bu bv hu hv bound conv
  have dl (i : L) : AffineTable (D i) :=
    affine_limit _ _ (fun j=>affine_ratio _ _ (au (φ j) i)) (ld i)
  have er (i : R) : AffineTable (E i) :=
    affine_limit _ _ (fun j=>affine_ratio _ _ (av (φ j) i)) (le_ i)
  choose A ha using fun i=>clause_of_affine (D i) (dl i) (d0 i)
  choose B hb using fun i=>clause_of_affine (E i) (er i) (e0 i)
  refine ⟨Feasible G ∅ ∅,(fun l=>¬Feasible G {l} ∅),(fun r=>¬Feasible G ∅ {r}),
    (fun l r=>¬Feasible G {l} {r}),A,B,?_⟩
  intro x
  rw [rep]
  have za (i : L) : D i x=0 ↔ ¬(A i).holds x := by rw [←ha,not_lt]; exact ⟨fun h=>h.le,fun h=>le_antisymm h (d0 i x)⟩
  have zb (i : R) : E i x=0 ↔ ¬(B i).holds x := by rw [←hb,not_lt]; exact ⟨fun h=>h.le,fun h=>le_antisymm h (e0 i x)⟩
  simp_rw [za,zb]
  constructor
  · rintro ⟨emp,l,r,lr⟩
    refine ⟨emp,fun i no=>by_contra (fun bad=>no (l i bad)),fun i no=>by_contra (fun bad=>no (r i bad)),?_⟩
    intro i j no
    by_cases h : (A i).holds x
    · exact Or.inl h
    · exact Or.inr (by_contra (fun bad=>no (lr i h j bad)))
  · rintro ⟨emp,l,r,lr⟩
    refine ⟨emp,fun i bad=>by_contra (fun no=>bad (l i no)),fun i bad=>by_contra (fun no=>bad (r i no)),?_⟩
    intro i hi j hj
    exact by_contra (fun no=>(lr i j no).elim hi hj)

end
end Midpoint
#print axioms Midpoint.graph_CNF
