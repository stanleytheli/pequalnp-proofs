import GraphCNF

namespace Midpoint
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {I L R : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

def middle (u : Finset I→ℝ) : ℝ := (u ∅+u Finset.univ)/2

lemma middle_bounds (u : Finset I→ℝ) (bound : ∀ x,0≤u x ∧ u x≤1) : 0≤middle u ∧ middle u≤1 := by
  unfold middle
  constructor <;> linarith [(bound ∅).1,(bound ∅).2,(bound Finset.univ).1,(bound Finset.univ).2]

lemma reflect (u : Finset I→ℝ) (aff : AffineTable u) (x : Finset I) :
    u x+u xᶜ=2*middle u := by
  let a := fun i : I=>u {i}-u ∅
  have law (z : Finset I) : u z=u ∅ + ∑ i∈z,a i := aff z
  have total := Finset.sum_add_sum_compl x a
  unfold middle
  rw [law x,law xᶜ,law Finset.univ]
  linarith

/-- Only assumptions are cube-preserving affine absence tables, a nonnegative
common scale, finite limits at the corners, and a bound at the actual midpoint. -/
theorem cube_graph_CNF (edge : L→R→Prop) (c : ℕ→ℝ)
    (u : ℕ→L→Finset I→ℝ) (v : ℕ→R→Finset I→ℝ) (f : Finset I→ℝ) (M : ℝ) (cs : ∀ j,0≤c j)
    (bu : ∀ j i x,0≤u j i x ∧ u j i x≤1) (bv : ∀ j i x,0≤v j i x ∧ v j i x≤1)
    (au : ∀ j i,AffineTable (u j i)) (av : ∀ j i,AffineTable (v j i))
    (bound : ∀ j,c j*prob edge (fun i=>middle (u j i)) (fun i=>middle (v j i))≤M)
    (conv : ∀ x,Tendsto (fun j=>c j*prob edge (fun i=>u j i x) (fun i=>v j i x)) atTop (𝓝 (f x))) :
    ∃ ready : Prop, ∃ left : L→Prop, ∃ right : R→Prop, ∃ pair : L→R→Prop,
      ∃ A : L→Clause I, ∃ B : R→Clause I, ∀ x, 0<f x ↔
        ready ∧ (∀ l,left l → (A l).holds x) ∧ (∀ r,right r → (B r).holds x) ∧
          (∀ l r,pair l r → (A l).holds x ∨ (B r).holds x) := by
  apply graph_CNF edge c (fun j i=>middle (u j i)) (fun j i=>middle (v j i)) u v f M cs
    (fun j i=>middle_bounds _ (bu j i)) (fun j i=>middle_bounds _ (bv j i)) bu bv au av _ _ bound conv
  · intro j i x; linarith [reflect _ (au j i) x,(bu j i xᶜ).1]
  · intro j i x; linarith [reflect _ (av j i) x,(bv j i xᶜ).1]

end
end Midpoint
#print axioms Midpoint.cube_graph_CNF
