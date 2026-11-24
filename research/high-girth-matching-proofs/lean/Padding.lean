import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace SparsePermanent
open Finset
variable {I J R : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [CommSemiring R]

/-- Adjoin a block with a single chosen, unit-weight perfect matching. -/
def padded (A : Matrix I I R) (m : Equiv.Perm J) : Matrix (I⊕J) (I⊕J) R
  | .inl y,.inl x => A y x
  | .inr y,.inr x => if m x=y then 1 else 0
  | _,_ => 0

private def keep (m : Equiv.Perm J) (p : Equiv.Perm (I⊕J)) := ∀ j,p (.inr j)=.inr (m j)

private noncomputable def padPerm (m : Equiv.Perm J) : Equiv.Perm I ≃ {p : Equiv.Perm (I⊕J) // keep m p} := by
  let f : Equiv.Perm I → {p : Equiv.Perm (I⊕J) // keep m p} := fun a=>⟨Equiv.sumCongr a m,fun _=>rfl⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b eq
    ext i
    exact Sum.inl.inj (Equiv.congr_fun (congrArg Subtype.val eq) (.inl i))
  · rintro ⟨p,hp⟩
    have hr : Set.MapsTo p (Set.range Sum.inr) (Set.range Sum.inr) := by
      rintro _ ⟨j,rfl⟩; exact ⟨m j,(hp j).symm⟩
    obtain ⟨⟨a,b⟩,eq⟩:= Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr p).mpr hr)
    change Equiv.sumCongr a b=p at eq
    have bm : b=m := by
      ext j
      exact Sum.inr.inj ((Equiv.congr_fun eq (.inr j)).trans (hp j))
    refine ⟨a,Subtype.ext ?_⟩
    simpa only [bm] using eq

/-- Unselected edges in a surrounding graph can all be assigned zero. The
remaining complementary matching gives exactly one extension of each old matching. -/
theorem permanent_padded (A : Matrix I I R) (m : Equiv.Perm J) : (padded A m).permanent=A.permanent := by
  classical
  unfold Matrix.permanent
  rw [← Fintype.sum_subtype_add_sum_subtype (keep m)]
  have vanish : (∑ p : {p : Equiv.Perm (I⊕J) // ¬keep m p}, ∏ i, padded A m (p.val i) i)=0 := by
    apply sum_eq_zero
    intro p _
    have bad := p.prop
    unfold keep at bad
    push Not at bad
    obtain ⟨j,h⟩:=bad
    apply prod_eq_zero (mem_univ (.inr j))
    cases eq : p.val (.inr j) with
    | inl i => rfl
    | inr k =>
      have miss : m j≠k := fun e=>h (eq.trans (congrArg Sum.inr e.symm))
      simp [padded,miss]
  rw [vanish,add_zero]
  symm
  apply Fintype.sum_equiv (padPerm m) _ _
  intro p
  change (∏ i,A (p i) i)=∏ i,padded A m (Equiv.sumCongr p m i) i
  rw [Fintype.prod_sum_type]
  simp [padded]

end SparsePermanent
#print axioms SparsePermanent.permanent_padded
