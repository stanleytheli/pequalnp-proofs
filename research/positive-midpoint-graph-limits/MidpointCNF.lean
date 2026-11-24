import CompactPins

namespace Midpoint
open Filter
open scoped Topology BigOperators
noncomputable section

variable {L R X : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] [Fintype X]

/-- The same bank of failed singleton and opposite-side pair tests describes
the support on every sampled input, for arbitrary midpoint-controlled tables.
The hypothesis h is the coefficient-free affine reflection bound. -/
theorem midpoint_pairs (edge : L→R→Prop) (c : ℕ→ℝ) (a : ℕ→L→ℝ) (b : ℕ→R→ℝ)
    (u : ℕ→L→X→ℝ) (v : ℕ→R→X→ℝ) (f : X→ℝ) (M : ℝ) (cs : ∀ j,0≤c j)
    (ba : ∀ j i,0≤a j i ∧ a j i≤1) (bb : ∀ j i,0≤b j i ∧ b j i≤1)
    (bu : ∀ j i x,0≤u j i x ∧ u j i x≤1) (bv : ∀ j i x,0≤v j i x ∧ v j i x≤1)
    (hu : ∀ j i x,u j i x≤2*a j i) (hv : ∀ j i x,v j i x≤2*b j i)
    (bound : ∀ j,c j*prob edge (a j) (b j) ≤ M)
    (conv : ∀ x,Tendsto (fun j=>c j*prob edge (fun i=>u j i x) (fun i=>v j i x)) atTop (𝓝 (f x))) :
    ∃ φ : ℕ→ℕ, StrictMono φ ∧ ∃ D : L→X→ℝ, ∃ E : R→X→ℝ, ∃ G : Set (Omitted L R),
      (∀ i x,0≤D i x) ∧ (∀ i x,0≤E i x) ∧
      (∀ i x,Tendsto (fun j=>ratio (u (φ j) i x) (a (φ j) i)) atTop (𝓝 (D i x))) ∧
      (∀ i x,Tendsto (fun j=>ratio (v (φ j) i x) (b (φ j) i)) atTop (𝓝 (E i x))) ∧
      ∀ x, 0<f x ↔ Feasible G ∅ ∅ ∧
        (∀ l, D l x=0 → Feasible G {l} ∅) ∧ (∀ r,E r x=0 → Feasible G ∅ {r}) ∧
        (∀ l, D l x=0 → ∀ r,E r x=0 → Feasible G {l} {r}) := by
  classical
  obtain ⟨φ,mono,D,E,w,d0,e0,w0,ld,le_,lw⟩ := midpoint_extract edge c a b u v M cs ba bb
    (fun j i x=>⟨(bu j i x).1,hu j i x⟩) (fun j i x=>⟨(bv j i x).1,hv j i x⟩) bound
  let G : Set (Omitted L R) := {A | Legal edge A ∧ 0<w A}
  have closed : Closed G := positive_closed edge (c ∘ φ) (a ∘ φ) (b ∘ φ) w lw (fun i _=>w0 i)
  refine ⟨φ,mono,D,E,G,d0,e0,ld,le_,?_⟩
  intro x
  let d := fun j i => ratio (u (φ j) i x) (a (φ j) i)
  let e := fun j i => ratio (v (φ j) i x) (b (φ j) i)
  have eu (j i) : a (φ j) i*d j i=u (φ j) i x :=
    (ratio_bounds (bu _ _ _).1 (ba _ _).1 (hu _ _ _)).2.2
  have ev (j i) : b (φ j) i*e j i=v (φ j) i x :=
    (ratio_bounds (bv _ _ _).1 (bb _ _).1 (hv _ _ _)).2.2
  have lf := (conv x).comp mono.tendsto_atTop
  have spec := support_limit edge (c ∘ φ) (a ∘ φ) d (b ∘ φ) e (fun i=>D i x) (fun i=>E i x)
    w (f x) (fun _=>cs _) (fun _=>d0 _ _) (fun _=>e0 _ _) (fun i _=>w0 i)
    (by intro j i; simpa only [Function.comp_apply,eu] using bu (φ j) i x)
    (by intro j i; simpa only [Function.comp_apply,ev] using bv (φ j) i x)
    (fun i=>ld i x) (fun i=>le_ i x) lw (by simpa only [Function.comp_def,eu,ev] using lf)
  rw [spec, pair_helly closed]
  simp [forbidden]

end
end Midpoint
#print axioms Midpoint.midpoint_pairs
