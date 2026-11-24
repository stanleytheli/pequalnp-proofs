import Explicit
import Projection

namespace SparsePermanent
open MvPolynomial
universe u
variable {I : Type} [Fintype I] [DecidableEq I] {F : Type u} [CommSemiring F]

abbrev EdgeVar (E : I → I → Prop) := {z : I × I // E z.1 z.2}

/-- An independent indeterminate for every physical graph edge. -/
noncomputable def genericPermanent (F : Type u) [CommSemiring F] (E : I → I → Prop) :
    MvPolynomial (EdgeVar E) F := by
  classical
  exact Matrix.permanent (fun y x => if h : E x y then X (⟨(x,y),h⟩ : EdgeVar E) else 0)

noncomputable abbrev dense (F : Type u) [CommSemiring F] (k : ℕ) :
    Matrix (Node k) (Node k) (MvPolynomial (Join k) F) := fun i j => X (i,j)

noncomputable def familyGeneric (F : Type u) [CommSemiring F] (k h : ℕ) :=
  genericPermanent F (familyBoard h (dense F k)).adj

/-- Arbitrary edge-labelled semiring matrices result from evaluating the
independent edge indeterminates, provided the matrix vanishes off the graph. -/
theorem generic_eval {W : Type} (E : I → I → Prop) (A : Matrix I I (MvPolynomial W F))
    (off : ∀ x y, ¬E x y → A y x=0) (r : EdgeVar E → Leaf W)
    (labels : ∀ e : EdgeVar E,(r e).poly F=A e.val.2 e.val.1) :
    Leaf.projection F r (genericPermanent F E) = A.permanent := by
  classical
  unfold genericPermanent Matrix.permanent
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : E i (π i)
  · simp only [h,dif_pos,Leaf.projection,aeval_X]
    exact labels ⟨(i,π i),h⟩
  · simp [h,off _ _ h]

private theorem choice_label {W : Type} {p : MvPolynomial W F}
    (h : p=0 ∨ p=1 ∨ ∃ w,p=X w) : ∃ a : Leaf W, a.poly F=p := by
  rcases h with h|h|⟨w,h⟩
  · exact ⟨.zero,h.symm⟩
  · exact ⟨.one,h.symm⟩
  · exact ⟨.var w,h.symm⟩

/-- The generic graph polynomial has a gate-for-gate projection onto the dense
permanent at every subdivision depth. -/
theorem projects_to_perm (F : Type u) [CommSemiring F] (k h : ℕ) :
    ∃ r : EdgeVar (familyBoard h (dense F k)).adj → Leaf (Join k),
      Leaf.projection F r (familyGeneric F k h)=Statement.perm F (k+1) := by
  classical
  let B := familyBoard h (dense F k)
  have labels : ∀ e : EdgeVar B.adj, ∃ a : Leaf (Join k), a.poly F=B.matrix e.val.2 e.val.1 := by
    intro e
    apply choice_label
    rcases labels_family h (dense F k) e.val.2 e.val.1 with z|o|⟨i,j,hij⟩
    · exact Or.inl z
    · exact Or.inr (Or.inl o)
    · exact Or.inr (Or.inr ⟨(i,j),hij⟩)
  choose r label using labels
  exact ⟨r,(generic_eval _ B.matrix B.off r label).trans (permanent_family h (dense F k))⟩

theorem computes_perm {k h s : ℕ} (hc : Statement.Computes (familyGeneric F k h) s) :
    Statement.Computes (Statement.perm F (k+1)) s := by
  obtain ⟨r,eq⟩:=projects_to_perm F k h
  rw [←eq]
  exact Leaf.computes r hc

section Fields
variable {K : Type u} [Field K]

theorem approximates_perm {k h s : ℕ} (hc : Statement.Approximates (familyGeneric K k h) s) :
    Statement.Approximates (Statement.perm K (k+1)) s := by
  obtain ⟨r,eq⟩:=projects_to_perm K k h
  rw [←eq]
  exact Leaf.approximates r hc

/-- The proved upstream exact bound transfers to this specific family of graphs,
uniformly in the number of odd subdivisions. -/
theorem exact_lower (upstream : Statement.MainTheorem.{u}) :
    ∃ c : ℝ, 0<c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (K : Type u) [Field K] [CharP K p],
      ∀ k h s : ℕ, m₀≤k+1 → p≠2 →
        Statement.Computes (familyGeneric K k h) s → Statement.Beyond c (k+1) s := by
  obtain ⟨c,hc,lower⟩:=upstream
  refine ⟨c,hc,fun p => ?_⟩
  obtain ⟨m₀,hm₀⟩:=lower p
  exact ⟨m₀,fun K _ _ k _ s hm hp hcomp => (hm₀ K (k+1) hm s).2 hp (computes_perm hcomp)⟩

/-- The proved upstream Laurent-approximation bound transfers as well, with the
same number of gates and the same characteristic-specific threshold. -/
theorem approximate_lower (upstream : Statement.MainTheoremApprox.{u}) :
    ∃ c : ℝ, 0<c ∧ ∀ p : ℕ, ∃ m₀ : ℕ, ∀ (K : Type u) [Field K] [CharP K p],
      ∀ k h s : ℕ, m₀≤k+1 → p≠2 →
        Statement.Approximates (familyGeneric K k h) s → Statement.Beyond c (k+1) s := by
  obtain ⟨c,hc,lower⟩:=upstream
  refine ⟨c,hc,fun p => ?_⟩
  obtain ⟨m₀,hm₀⟩:=lower p
  exact ⟨m₀,fun K _ _ k _ s hm hp hcomp => (hm₀ K (k+1) hm s).2 hp (approximates_perm hcomp)⟩

end Fields
end SparsePermanent

#print axioms SparsePermanent.projects_to_perm
#print axioms SparsePermanent.exact_lower
#print axioms SparsePermanent.approximate_lower
