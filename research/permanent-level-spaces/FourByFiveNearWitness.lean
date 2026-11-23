import Mathlib

namespace FourByFiveNearWitness

open Finset
open scoped Classical

private def splitEmb {A : Type*} (n : ℕ) :
    (Fin (n+1) ↪ A) ≃ (Σ e : Fin n ↪ A, {a : A // a ∉ Set.range e}) where
  toFun f := ⟨Fin.Embedding.tail f, f 0, by
    rintro ⟨i, hi⟩
    have he : f i.succ = f 0 := hi
    exact Fin.succ_ne_zero i (f.injective he)⟩
  invFun t := Fin.Embedding.cons t.1 t.2.property
  left_inv f := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv t := by
    obtain ⟨e,a,ha⟩ := t
    rfl

noncomputable def injectiveSum {A R : Type*} [Fintype A] [CommRing R]
    {n : ℕ} (f : Fin n → A → R) : R := by
  classical
  exact ∑ e : Fin n ↪ A, ∏ i, f i (e i)

private theorem sum_off_range {A R : Type*} [Fintype A] [CommRing R] {n : ℕ}
    (e : Fin n ↪ A) (f : A → R) :
    (∑ a : {a : A // a ∉ Set.range e}, f a) = (∑ a, f a) - ∑ i, f (e i) := by
  classical
  apply eq_sub_iff_add_eq.mpr
  let _ : Fintype (Set.range e) := Subtype.fintype _
  have eq := (Equiv.ofInjective e e.injective).sum_comp (fun a => f a.val)
  change (∑ a : {a : A // a ∉ Set.range e}, f a) + (∑ i, f (e i)) = _
  rw [add_comm]
  calc
    _ = (∑ a : Set.range e, f a.val) + ∑ a : {a : A // a ∉ Set.range e}, f a := by
      exact congrArg (· + _) eq
    _ = _ := Fintype.sum_subtype_add_sum_subtype (fun a => a ∈ Set.range e) f

private def mergeEntry {A R : Type*} [CommRing R] {n : ℕ} (f : Fin n → A → R)
    (g : A → R) (j : Fin n) (i : Fin n) (a : A) : R :=
  (if i = j then g a else 1) * f i a

private theorem merged_product {A R : Type*} [CommRing R] {n : ℕ} (f : Fin n → A → R)
    (g : A → R) (j : Fin n) (e : Fin n ↪ A) :
    (∏ i, mergeEntry f g j i (e i)) = g (e j) * ∏ i, f i (e i) := by
  classical
  simp only [mergeEntry,Finset.prod_mul_distrib]
  simp

theorem injectiveSum_succ {A R : Type*} [Fintype A] [CommRing R] {n : ℕ}
    (f : Fin n → A → R) (g : A → R) :
    injectiveSum (Fin.cons g f) = (∑ a, g a) * injectiveSum f -
      ∑ j, injectiveSum (mergeEntry f g j) := by
  classical
  rw [injectiveSum, ← (splitEmb (A := A) n).symm.sum_comp]
  rw [Fintype.sum_sigma]
  simp only [splitEmb, Equiv.coe_fn_symm_mk, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Fin.Embedding.coe_cons]
  simp_rw [← Finset.sum_mul, sum_off_range, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_congr rfl (fun e _ => (merged_product f g j e).symm)

set_option maxHeartbeats 12000000

/-- Coordinates of a seven-dimensional complex family in four rows and five columns. -/
def entry (u : Fin 7 → ℂ) (ij : Fin 4 × Fin 5) : ℂ :=
  let a : Fin 4 → ℂ := ![u 0, u 1, u 2, u 3]
  let b : Fin 4 → ℂ := ![u 4, u 5, u 6, -(u 4 + u 5 + u 6)]
  (![a ij.1, Complex.I * a ij.1, -(a ij.1), -(Complex.I * a ij.1), b ij.1] :
    Fin 5 → ℂ) ij.2

/-- The first four coordinates determine the amplitudes on the fourth roots of unity.
The final three determine a centered column. -/
def parameter : (Fin 7 → ℂ) →ₗ[ℂ] ((Fin 4 × Fin 5) → ℂ) where
  toFun := entry
  map_add' u v := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring
  map_smul' c u := by
    funext ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp [entry] <;> ring

theorem parameter_injective : Function.Injective parameter := by
  intro u v h
  funext i
  fin_cases i
  · exact congrFun h (0,0)
  · exact congrFun h (1,0)
  · exact congrFun h (2,0)
  · exact congrFun h (3,0)
  · exact congrFun h (0,4)
  · exact congrFun h (1,4)
  · exact congrFun h (2,4)

theorem dimension : Module.finrank ℂ (LinearMap.range parameter) = 7 := by
  rw [LinearMap.finrank_range_of_inj parameter_injective, Module.finrank_fin_fun]

private theorem inj_succ {n : ℕ} (f : Fin (n+1) → Fin 5 → ℂ) :
    injectiveSum f = (∑ a, f 0 a) * injectiveSum (Fin.tail f) -
      ∑ j, injectiveSum (mergeEntry (Fin.tail f) (f 0) j) := by
  simpa only [Fin.cons_self_tail] using injectiveSum_succ (Fin.tail f) (f 0)

private theorem inj_zero (f : Fin 0 → Fin 5 → ℂ) : injectiveSum f = 1 := by
  simp [injectiveSum]

/-- The affine rectangular permanent has a single quartic error on this seven-plane. -/
theorem exact_residual (u : Fin 7 → ℂ) :
    (∑ e : Fin 4 ↪ Fin 5, ∏ i, (1 + parameter u (i, e i))) =
    120 - 24 * u 0 * u 1 * u 2 * u 3 := by
  change injectiveSum (fun i j => 1 + entry u (i,j)) = _
  simp only [inj_succ, inj_zero, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty, Fin.tail, mergeEntry]
  norm_num [entry, Fin.succ]
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  ring

/-- The only maximal linear level spaces inside this family are its four
coordinate hyperplanes, each obtained by killing one row amplitude. -/
theorem level_subspace_iff (L : Submodule ℂ (Fin 7 → ℂ)) :
    (∀ u ∈ L, (∑ e : Fin 4 ↪ Fin 5, ∏ i, (1 + parameter u (i, e i))) = 120) ↔
    ∃ k : Fin 4, ∀ u ∈ L, u (k.castLE (by decide : 4 ≤ 7)) = 0 := by
  constructor
  · intro h
    by_contra! hn
    let f : Fin 4 → Module.Dual ℂ (Fin 7 → ℂ) :=
      fun k => LinearMap.proj (k.castLE (by decide : 4 ≤ 7))
    obtain ⟨u,hu,hne⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists L f hn
    have hh := h u hu
    rw [exact_residual] at hh
    have hz : 24 * u 0 * u 1 * u 2 * u 3 = 0 := by linear_combination -hh
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (hne 0)) (hne 1)) (hne 2)) (hne 3)) hz
  · rintro ⟨k,hk⟩ u hu
    rw [exact_residual]
    specialize hk u hu
    fin_cases k <;> norm_num at hk <;> simp [hk]

end FourByFiveNearWitness
