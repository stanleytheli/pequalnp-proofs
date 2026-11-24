import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Fixed-format partial table codes use an asymmetric threshold on
one-bit neighbors. The two locality assumptions are certificate complexity
of the presence bit and the value bit, not global junta assumptions. -/
namespace MetaComplexity.LocalThreshold
open Finset
variable {I Y : Type*} [DecidableEq I]

def flip (x : I → Bool) (i : I) : I → Bool := Function.update x i (!(x i))

def LocalAt (q : ℕ) (f : (I → Bool) → Bool) (x : I → Bool) : Prop :=
  ∃ S : Finset I, S.card ≤ q ∧
    ∀ x', (∀ i ∈ S, x' i=x i) → f x'=f x

lemma avoid (x : I → Bool) (S : Finset I) {j : I} (h : j∉S) :
    ∀ i ∈ S, flip x j i = x i := by
  intro i hi
  have ne : i≠j := fun e => h (e ▸ hi)
  simp [flip,ne]

def present (r:Option Bool) : Bool := r.isSome
def value (r:Option Bool) : Bool := r.getD false

lemma decode_one {r:Option Bool} (h : value r=true) : r=some true := by
  cases r with
  | none => cases h
  | some b => cases b <;> simp_all [value]

lemma decode_zero {r:Option Bool} (h : present r=true) (v : value r=false) :
    r=some false := by
  cases r with
  | none => cases h
  | some b => cases b <;> simp_all [value]

theorem aggregate (q : ℕ) (J : Finset I) (count : J.card=3*q+1)
    (x : I→Bool) (row : (I→Bool)→Y→Option Bool)
    (lp : ∀ y, LocalAt q (fun z=>present (row z y)) x)
    (lv : ∀ y, LocalAt q (fun z=>value (row z y)) x)
    (vote : I→Y→Bool)
    (cert : ∀ i∈J, ∀ y b, row (flip x i) y=some b → vote i y=b)
    (y : Y) (b : Bool) (fixed : row x y=some b) :
    decide (2*q+1 ≤ (J.filter (fun i=>vote i y=true)).card)=b := by
  classical
  obtain ⟨S,sBound,ds⟩ := lv y
  cases b with
  | true =>
    apply decide_eq_true
    have includeGood : J \ S ⊆ J.filter (fun i=>vote i y=true) := by
      intro i hi
      obtain ⟨ij,out⟩ := mem_sdiff.mp hi
      refine mem_filter.mpr ⟨ij,cert i ij y true (decode_one ?_)⟩
      simpa [fixed,value] using ds (flip x i) (avoid x S out)
    have lower := card_le_card includeGood
    have split := card_sdiff_add_card_inter J S
    have inter := card_le_card (inter_subset_right (s₁:=J) (s₂:=S))
    omega
  | false =>
    apply decide_eq_false
    obtain ⟨T,tBound,dt⟩ := lp y
    have covered : J.filter (fun i=>vote i y=true) ⊆ S∪T := by
      intro i hi
      obtain ⟨ij,one⟩ := mem_filter.mp hi
      by_contra h
      have a : i∉S := fun k => h (mem_union_left T k)
      have b : i∉T := fun k => h (mem_union_right S k)
      have vp : present (row (flip x i) y)=true := by
        simpa [fixed,present] using dt (flip x i) (avoid x T b)
      have vv : value (row (flip x i) y)=false := by
        simpa [fixed,value] using ds (flip x i) (avoid x S a)
      have zero := cert i ij y false (decode_zero vp vv)
      simp_all
    have small := card_le_card covered
    have union := card_union_le S T
    omega
end MetaComplexity.LocalThreshold
#print axioms MetaComplexity.LocalThreshold.aggregate
