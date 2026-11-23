import Mathlib

/-! The signed two-by-two margin marker for rectangular injective permanents. -/

namespace MarginMarker

open Finset
open scoped Classical

noncomputable def rectPerm {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (A : I → J → R) : R := ∑ e : I ↪ J, ∏ i, A i (e i)

def marker {J R : Type*} [CommRing R] (b : Bool) : J ⊕ Bool → R :=
  Sum.elim (fun _ => 0) (fun c => if b = c then 1 else -1)

def bump {I J R : Type*} [CommRing R] (A : (I ⊕ Bool) → (J ⊕ Bool) → R) (w : R) :
    (I ⊕ Bool) → (J ⊕ Bool) → R :=
  Sum.elim (fun i j => A (.inl i) j) (fun b j => A (.inr b) j + w * marker b j)

theorem row_sum_bump {I J R : Type*} [Fintype J] [CommRing R]
    (A : (I ⊕ Bool) → (J ⊕ Bool) → R) (w : R) (i : I ⊕ Bool) :
    ∑ j, bump A w i j = ∑ j, A i j := by
  cases i with
  | inl i => rfl
  | inr b =>
    cases b <;> simp [Fintype.sum_sum_type, bump, marker] <;> ring

theorem col_sum_bump {I J R : Type*} [Fintype I] [CommRing R]
    (A : (I ⊕ Bool) → (J ⊕ Bool) → R) (w : R) (j : J ⊕ Bool) :
    ∑ i, bump A w i j = ∑ i, A i j := by
  cases j with
  | inl j => simp [Fintype.sum_sum_type, bump, marker]
  | inr b =>
    cases b <;> simp [Fintype.sum_sum_type, bump, marker] <;> ring

private def flip (b : Bool) : Bool ↪ Bool where
  toFun x := if b then !x else x
  inj' := by cases b <;> decide

private def extendMap {I J : Type*} (p : (I ↪ J) × Bool) : (I ⊕ Bool) ↪ (J ⊕ Bool) :=
  p.1.sumMap (flip p.2)

private theorem extends_inj {I J : Type*} : Function.Injective (@extendMap I J) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ h
  have he : e = f := Function.Embedding.ext fun i =>
    Sum.inl.inj (DFunLike.congr_fun h (.inl i))
  have hb : flip b false = flip c false := Sum.inr.inj (DFunLike.congr_fun h (.inr false))
  have hf (x : Bool) : flip x false = x := by cases x <;> rfl
  rw [hf,hf] at hb
  cases he
  cases hb
  rfl

private theorem extends_of_right {I J : Type*} (e : (I ⊕ Bool) ↪ (J ⊕ Bool))
    (b : Bool) (h : ∀ z, e (.inr z) = .inr (flip b z)) :
    ∃ p : (I ↪ J) × Bool, extendMap p = e := by
  classical
  have htop (i : I) : ∃ j : J, e (.inl i) = .inl j := by
    cases he : e (.inl i) with
    | inl j => exact ⟨j,rfl⟩
    | inr c =>
      have hc : ∃ z, flip b z = c := by cases b <;> cases c <;> decide
      obtain ⟨z,hz⟩ := hc
      have hh : e (.inl i) = e (.inr z) := by rw [he,h,hz]
      have hbad := e.injective hh
      cases hbad
  choose f hf using htop
  have hf' : Function.Injective f := by
    intro i j hij
    have hh : e (.inl i) = e (.inl j) := by rw [hf,hf,hij]
    exact Sum.inl.inj (e.injective hh)
  refine ⟨(⟨f,hf'⟩,b), Function.Embedding.ext ?_⟩
  intro x
  cases x with
  | inl i => exact (hf i).symm
  | inr z => exact (h z).symm

private theorem marker_vanishes {I J R : Type*} [CommRing R]
    (e : (I ⊕ Bool) ↪ (J ⊕ Bool)) (he : ¬ ∃ p, extendMap p = e) :
    (marker true (e (.inr true)) : R) * marker false (e (.inr false)) = 0 := by
  cases hf : e (.inr false) with
  | inl j => simp [marker]
  | inr a =>
    cases ht : e (.inr true) with
    | inl j => simp [marker]
    | inr c =>
      have hac : a ≠ c := by
        intro h
        have : e (.inr false) = e (.inr true) := by rw [hf,ht,h]
        exact Bool.false_ne_true (Sum.inr.inj (e.injective this))
      exfalso
      apply he
      apply extends_of_right e a
      intro z
      cases a <;> cases c <;> cases z <;> simp_all [flip]

private theorem weighted_sum {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (A : (I ⊕ Bool) → (J ⊕ Bool) → R) :
    (∑ e : (I ⊕ Bool) ↪ (J ⊕ Bool),
      (∏ i : I, A (.inl i) (e (.inl i))) *
      (marker true (e (.inr true)) * marker false (e (.inr false)))) =
      2 * rectPerm (fun i j => A (.inl i) (.inl j)) := by
  classical
  let f (e : (I ⊕ Bool) ↪ (J ⊕ Bool)) : R := (∏ i : I, A (.inl i) (e (.inl i))) *
    (marker true (e (.inr true)) * marker false (e (.inr false)))
  let inc : ((I ↪ J) × Bool) ↪ ((I ⊕ Bool) ↪ (J ⊕ Bool)) := ⟨extendMap,extends_inj⟩
  have hs : ∑ e ∈ univ.map inc, f e = ∑ e, f e := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have hh : ¬ ∃ p, extendMap p = e := by
      rintro ⟨p,rfl⟩
      exact he (Finset.mem_map.mpr ⟨p,Finset.mem_univ _,rfl⟩)
    simp [f,marker_vanishes e hh]
  change ∑ e, f e = _
  rw [← hs,Finset.sum_map,Fintype.sum_prod_type]
  simp [f,inc,extendMap,flip,Function.Embedding.sumMap,marker,rectPerm,two_mul,Finset.sum_add_distrib]

/-- The centered second finite difference of a rectangular permanent is exactly four
times the permanent of the deleted two-by-two row/column complement. -/
theorem second_difference {I J R : Type*} [Fintype I] [Fintype J] [CommRing R]
    (A : (I ⊕ Bool) → (J ⊕ Bool) → R) :
    rectPerm (bump A 1) + rectPerm (bump A (-1)) - 2 * rectPerm (bump A 0) =
    4 * rectPerm (fun i j => A (.inl i) (.inl j)) := by
  classical
  conv_lhs => unfold rectPerm
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  calc
    _ = ∑ e : (I ⊕ Bool) ↪ (J ⊕ Bool), 2 * ((∏ i : I, A (.inl i) (e (.inl i))) *
        (marker true (e (.inr true)) * marker false (e (.inr false)))) := by
      apply Fintype.sum_congr
      intro e
      simp only [Fintype.prod_sum_type, Fintype.prod_bool, bump, Sum.elim_inl, Sum.elim_inr]
      ring
    _ = _ := by rw [← Finset.mul_sum,weighted_sum]; ring

#print axioms second_difference
#print axioms row_sum_bump
#print axioms col_sum_bump

end MarginMarker
