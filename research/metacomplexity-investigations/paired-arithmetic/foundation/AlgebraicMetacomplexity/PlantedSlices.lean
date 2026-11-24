import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace AlgebraicMeta
open Finset MvPolynomial
variable {I V R:Type*} [Fintype I] [CommSemiring R]

/-- One baseline variable, two rails per witness bit, and target variables. -/
abbrev Vars (I V:Type*) := Option (I×Bool) ⊕ V

noncomputable def tag (a:I→Bool) : MvPolynomial (Vars I V) R :=
  ∏i,X (.inl (some (i,a i)))

noncomputable def plant (valid:Finset (I→Bool)) (h:MvPolynomial V R) : MvPolynomial (Vars I V) R :=
  X (.inl none)+(∑a∈valid,tag a)*rename Sum.inr h

noncomputable def pick (a:I→Bool) : Vars I V→MvPolynomial V R
  | .inl none=>0
  | .inl (some (i,b))=>if b=a i then 1 else 0
  | .inr v=>X v

theorem pick_tag [DecidableEq I] (a b:I→Bool) : aeval (pick (V:=V) (R:=R) a) (tag (V:=V) (R:=R) b)=if b=a then 1 else 0 := by
  classical
  simp only [tag,map_prod,aeval_X,pick]
  by_cases same:b=a
  · subst b;simp
  · have witness:∃i,b i≠a i:=by
      by_contra! all
      exact same (funext all)
    obtain ⟨i,bad⟩:=witness
    simp only [same,ite_false]
    exact prod_eq_zero (mem_univ i) (by simp [bad])

/-- A single satisfying witness exposes the entire target over every
commutative semiring, including positive characteristic. -/
theorem planted_projection [DecidableEq I] (valid:Finset (I→Bool)) (h:MvPolynomial V R) (a:I→Bool) :
    aeval (pick a) (plant valid h) = if a∈valid then h else 0 := by
  classical
  simp only [plant,map_add,aeval_X,pick,map_mul,map_sum,pick_tag,aeval_rename]
  change 0 + (∑b∈valid,if b=a then 1 else 0)*aeval (X (R:=R)) h = _
  rw [aeval_X_left_apply]
  by_cases hit:a∈valid <;> simp [hit]

theorem empty_baseline (h:MvPolynomial V R) :
    plant (I:=I) ∅ h=X (.inl none) := by simp [plant]

/-- A signed branch adds exactly the difference of its two witness counts. -/
theorem signed_count {A B S:Type*} [Fintype A] [Fintype B] [CommRing S] (h:S) :
    h+(∑_a:A,(1:S))+(∑_b:B,(-1:S)) = h+(Fintype.card A:S)-(Fintype.card B:S) := by
  simp [sub_eq_add_neg]

end AlgebraicMeta
#print axioms AlgebraicMeta.planted_projection
#print axioms AlgebraicMeta.empty_baseline
#print axioms AlgebraicMeta.signed_count
