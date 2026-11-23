import Mathlib

namespace CenteredRowFive

open scoped Classical
open Finset

abbrev Square := Fin 5 × Fin 5 → ℂ
abbrev Upper := Fin 4 × Fin 5 → ℂ

def upper : Square →ₗ[ℂ] Upper where
  toFun x := fun ij => x (ij.1.succ, ij.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rowOnly (d : Fin 5 → ℂ) : Square :=
  fun ij => if ij.1 = 0 then d ij.2 else 0

noncomputable def cofactor (A : Upper) (j : Fin 5) : ℂ :=
  ∑ e : Equiv.Perm (Fin 4), ∏ i, (1 + A (i,j.succAbove (e i)))

noncomputable def permanent (x : Square) : ℂ :=
  ∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + x (i,e i))

theorem laplace (x : Square) :
    permanent x = ∑ j, (1 + x (0,j)) * cofactor (upper x) j := by
  classical
  let E := Equiv.embeddingEquivOfFinite (Fin 5)
  rw [permanent, ← E.symm.sum_comp,
    ← (Equiv.Perm.decomposeFin' (n := 3)).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [cofactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  change (∏ i, (1 + x (i, (Equiv.Perm.decomposeFin'Symm j e) i))) = _
  rw [Fin.prod_univ_succ, Equiv.Perm.decomposeFin'Symm_zero]
  rfl

private theorem upper_rowOnly (d : Fin 5 → ℂ) : upper (rowOnly d) = 0 := by
  funext ij
  simp [upper,rowOnly]

private theorem delta_mem (L : Submodule ℂ Square)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L) (i k : Fin 5) :
    rowOnly (fun j => (if j = i then 1 else 0) - (if j = k then 1 else 0)) ∈ L := by
  apply hrow
  simp [Finset.sum_sub_distrib]

theorem cofactor_eq (L : Submodule ℂ Square) (hlevel : ∀ x ∈ L, permanent x = 120)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L)
    {x : Square} (hx : x ∈ L) (i k : Fin 5) :
    cofactor (upper x) i = cofactor (upper x) k := by
  classical
  let d : Fin 5 → ℂ := fun j => (if j = i then 1 else 0) - (if j = k then 1 else 0)
  have h1 := hlevel (x + rowOnly d) (L.add_mem hx (delta_mem L hrow i k))
  have h2 := hlevel x hx
  rw [laplace] at h1 h2
  rw [map_add,upper_rowOnly,add_zero] at h1
  have h3 : (∑ j, ((1+x (0,j)) + d j) * cofactor (upper x) j) = 120 := by
    simpa [rowOnly,add_assoc] using h1
  simp_rw [show ∀ j, ((1 + x (0,j)) + d j) * cofactor (upper x) j =
      (1 + x (0,j)) * cofactor (upper x) j + d j * cofactor (upper x) j
    from fun _ => add_mul _ _ _] at h3
  rw [Finset.sum_add_distrib,h2] at h3
  have hh : (∑ j, d j * cofactor (upper x) j) =
      cofactor (upper x) i - cofactor (upper x) k := by
    simp [d,sub_mul,ite_mul,Finset.sum_sub_distrib]
  rw [hh] at h3
  linear_combination h3

private theorem factored (L : Submodule ℂ Square) (hlevel : ∀ x ∈ L, permanent x = 120)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L)
    {x : Square} (hx : x ∈ L) (k : Fin 5) :
    (5 + ∑ j, x (0,j)) * cofactor (upper x) k = 120 := by
  have h := hlevel x hx
  rw [laplace] at h
  simp_rw [cofactor_eq L hlevel hrow hx _ k] at h
  rw [← Finset.sum_mul, Finset.sum_add_distrib] at h
  simpa using h

/-- A full centered first row forces that row to remain centered throughout the space
and every complementary four-by-four minor to have constant affine permanent 24. -/
theorem centered_row_reduction (L : Submodule ℂ Square)
    (hlevel : ∀ x ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + x (i,e i))) = 120)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L)
    {x : Square} (hx : x ∈ L) :
    (∑ j, x (0,j)) = 0 ∧ ∀ k, cofactor (upper x) k = 24 := by
  have hs : (∑ j, x (0,j)) = 0 := by
    by_contra hn
    let c : ℂ := -5 / ∑ j, x (0,j)
    have h := factored L hlevel hrow (L.smul_mem c hx) 0
    simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum] at h
    have hc : c * (∑ j, x (0,j)) = -5 := by
      exact div_mul_cancel₀ _ hn
    rw [hc] at h
    norm_num at h
  refine ⟨hs,fun k => ?_⟩
  have h := factored L hlevel hrow hx k
  rw [hs,add_zero] at h
  linear_combination h / 5

end CenteredRowFive

namespace CenteredRowGram

open Module LinearMap

/-- Jointly injective maps into a nondegenerate three-space with the same Gram
form have a domain of dimension at most three when that form has rank at least two. -/
theorem three_dimensional_target {k V H I : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Nonempty I]
    (B : H →ₗ[k] H →ₗ[k] k) (hn : ∀ x, (∀ y, B x y = 0) → x = 0)
    (Q : V →ₗ[k] V →ₗ[k] k) (F : I → V →ₗ[k] H)
    (heq : ∀ i x y, B (F i x) (F i y) = Q x y)
    (hjoint : ∀ x, (∀ i, F i x = 0) → x = 0)
    (hH : finrank k H = 3) (hQ : 2 ≤ finrank k (range Q)) :
    finrank k V ≤ 3 := by
  have hk (i : I) : ker (F i) ≤ ker Q := by
    intro x hx
    apply mem_ker.mpr
    ext y
    rw [← heq i x y,mem_ker.mp hx,map_zero]
    rfl
  have hr (i : I) : finrank k (range Q) ≤ finrank k (range (F i)) := by
    have h := Submodule.finrank_mono (hk i)
    have h1 := (F i).finrank_range_add_finrank_ker
    have h2 := Q.finrank_range_add_finrank_ker
    omega
  have hsame (i : I) : ker Q ≤ ker (F i) := by
    by_cases hsurj : Function.Surjective (F i)
    · intro x hx
      apply mem_ker.mpr
      apply hn
      intro y
      obtain ⟨v,rfl⟩ := hsurj y
      rw [heq,mem_ker.mp hx]
      rfl
    · have hne : range (F i) ≠ ⊤ := fun e => hsurj (range_eq_top.mp e)
      have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
      rw [finrank_top,hH] at hlt
      have h1 := (F i).finrank_range_add_finrank_ker
      have h2 := Q.finrank_range_add_finrank_ker
      have eq := Submodule.eq_of_le_of_finrank_le (hk i) (by omega)
      exact eq.ge
  have hbot : ker Q = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact hjoint x (fun i => mem_ker.mp (hsame i hx))
  have hd := Q.finrank_range_add_finrank_ker
  rw [hbot,finrank_bot,add_zero] at hd
  obtain ⟨i⟩ := ‹Nonempty I›
  have hI := Submodule.finrank_le (range (F i))
  have hR := hr i
  omega

end CenteredRowGram

namespace SquareFourMoments

open Finset
open scoped Classical

abbrev Mat := Fin 4 → Fin 4 → ℂ

noncomputable def perm (A : Mat) (t : ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 4), ∏ i, (1+t*A i (σ i))

private def lin (u : Fin 4 → ℂ) : ℂ := u 0 + u 1 + u 2 + u 3
private def quad (u : Fin 4 → ℂ) : ℂ :=
  u 0 * u 1 + u 0 * u 2 + u 0 * u 3 + u 1 * u 2 + u 1 * u 3 + u 2 * u 3

private theorem firstRow (u : Fin 4 → ℂ) :
    (∏ i, (1 + 2 * u i)) - (∏ i, (1 - 2 * u i)) -
      8 * ((∏ i, (1 + u i)) - ∏ i, (1 - u i)) = -12 * lin u := by
  simp [Fin.prod_univ_succ,lin]
  ring

private theorem secondRow (u : Fin 4 → ℂ) :
    (∏ i, (1 + 2 * u i)) + (∏ i, (1 - 2 * u i)) -
      16 * ((∏ i, (1 + u i)) + ∏ i, (1 - u i)) + 30 =
      -24 * quad u := by
  simp [Fin.prod_univ_succ,quad]
  ring

private theorem firstVanishing (A : Mat) (h : ∀ t, perm A t = 24) :
    (∑ σ : Equiv.Perm (Fin 4), lin (fun i => A i (σ i))) = 0 := by
  have hh := congrArg (fun f : Equiv.Perm (Fin 4) → ℂ => ∑ σ, f σ)
      (funext fun σ => firstRow (fun i => A i (σ i)))
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hh
  have h1 := h 1
  have hn1 := h (-1)
  have h2 := h 2
  have hn2 := h (-2)
  simp only [perm,one_mul,neg_mul,one_mul,← sub_eq_add_neg] at h1 hn1 h2 hn2
  rw [h1,hn1,h2,hn2] at hh
  linear_combination hh / 12

private theorem secondVanishing (A : Mat) (h : ∀ t, perm A t = 24) :
    (∑ σ : Equiv.Perm (Fin 4), quad (fun i => A i (σ i))) = 0 := by
  have hh := congrArg (fun f : Equiv.Perm (Fin 4) → ℂ => ∑ σ, f σ)
      (funext fun σ => secondRow (fun i => A i (σ i)))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,← Finset.mul_sum] at hh
  have h1 := h 1
  have hn1 := h (-1)
  have h2 := h 2
  have hn2 := h (-2)
  simp only [perm,one_mul,neg_mul,one_mul,← sub_eq_add_neg] at h1 hn1 h2 hn2
  rw [h1,hn1,h2,hn2] at hh
  norm_num [Fintype.card_perm, Nat.factorial] at hh
  exact hh

private theorem sumPerm {n : ℕ} (g : Equiv.Perm (Fin (n+2)) → ℂ) :
    ∑ e, g e = ∑ j : Fin (n+2), ∑ e : Equiv.Perm (Fin (n+1)),
      g (Equiv.Perm.decomposeFin'Symm j e) := by
  rw [← (Equiv.Perm.decomposeFin' (n:=n)).symm.sum_comp g,Fintype.sum_prod_type]
  rfl

private theorem sumPermOne (g : Equiv.Perm (Fin 1) → ℂ) : ∑ e, g e = g (Equiv.refl _) := by
  rw [Fintype.sum_subsingleton _ (Equiv.refl _)]

theorem sum_four_permutations (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), f (σ 0) (σ 1) (σ 2) (σ 3)) =
      f 0 1 2 3 + f 0 1 3 2 + f 0 2 1 3 + f 0 2 3 1 +
      f 0 3 1 2 + f 0 3 2 1 + f 1 0 2 3 + f 1 0 3 2 +
      f 1 2 0 3 + f 1 2 3 0 + f 1 3 0 2 + f 1 3 2 0 +
      f 2 0 1 3 + f 2 0 3 1 + f 2 1 0 3 + f 2 1 3 0 +
      f 2 3 0 1 + f 2 3 1 0 + f 3 0 1 2 + f 3 0 2 1 +
      f 3 1 0 2 + f 3 1 2 0 + f 3 2 0 1 + f 3 2 1 0 := by
  rw [sumPerm (n:=2)]
  simp_rw [sumPerm (n:=1)]
  simp_rw [sumPerm (n:=0)]
  let P (i : Fin 4) (j : Fin 3) (k : Fin 2) (e : Equiv.Perm (Fin 1)) :=
    Equiv.Perm.decomposeFin'Symm i (Equiv.Perm.decomposeFin'Symm j
      (Equiv.Perm.decomposeFin'Symm k e))
  let F (e : Equiv.Perm (Fin 4)) := f (e 0) (e 1) (e 2) (e 3)
  change (∑ i, ∑ j, ∑ k, ∑ e, F (P i j k e)) = _
  have stop (i j k) : (∑ e, F (P i j k e)) = F (P i j k (Equiv.refl _)) :=
    sumPermOne _
  simp_rw [stop]
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change (((f 0 1 2 3 + f 0 1 3 2) + ((f 0 2 1 3 + f 0 2 3 1) + (f 0 3 1 2 + f 0 3 2 1))) + (((f 1 0 2 3 + f 1 0 3 2) + ((f 1 2 0 3 + f 1 2 3 0) + (f 1 3 0 2 + f 1 3 2 0))) + (((f 2 0 1 3 + f 2 0 3 1) + ((f 2 1 0 3 + f 2 1 3 0) + (f 2 3 0 1 + f 2 3 1 0))) + ((f 3 0 1 2 + f 3 0 2 1) + ((f 3 1 0 2 + f 3 1 2 0) + (f 3 2 0 1 + f 3 2 1 0)))))) = _
  ring

private theorem sumLinear (A : Mat) :
    (∑ σ : Equiv.Perm (Fin 4), lin (fun i => A i (σ i))) = 6 * ∑ j, ∑ i, A i j := by
  change (∑ σ : Equiv.Perm (Fin 4), (fun i j k l =>
    A 0 i + A 1 j + A 2 k + A 3 l) (σ 0) (σ 1) (σ 2) (σ 3)) = _
  rw [sum_four_permutations (fun i j k l => A 0 i + A 1 j + A 2 k + A 3 l)]
  simp [Fin.sum_univ_succ]
  ring

private theorem sumQuadratic (A : Mat) :
    (∑ σ : Equiv.Perm (Fin 4), quad (fun i => A i (σ i))) =
      (∑ j, ∑ i, A i j)^2 - (∑ i, (∑ j, A i j)^2) -
      (∑ j, (∑ i, A i j)^2) + (∑ i, ∑ j, (A i j)^2) := by
  change (∑ σ : Equiv.Perm (Fin 4), (fun i j k l =>
    A 0 i * A 1 j + A 0 i * A 2 k + A 0 i * A 3 l + A 1 j * A 2 k +
    A 1 j * A 3 l + A 2 k * A 3 l) (σ 0) (σ 1) (σ 2) (σ 3)) = _
  rw [sum_four_permutations (fun i j k l => A 0 i * A 1 j + A 0 i * A 2 k + A 0 i * A 3 l +
    A 1 j * A 2 k + A 1 j * A 3 l + A 2 k * A 3 l)]
  simp [Fin.sum_univ_succ]
  ring

theorem sum_entries_zero {A : Mat} (h : ∀ t, perm A t = 24) : (∑ j, ∑ i, A i j) = 0 := by
  have hh := firstVanishing A h
  rw [sumLinear] at hh
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

theorem row_square {A : Mat} (h : ∀ t, perm A t = 24) (hc : ∀ j, ∑ i, A i j = 0) :
    (∑ i, (∑ j, A i j)^2) = ∑ i, ∑ j, (A i j)^2 := by
  have hh := secondVanishing A h
  rw [sumQuadratic] at hh
  simp only [hc,Finset.sum_const_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
    zero_sub,sub_zero] at hh
  linear_combination -hh

/-- The four-column moment on two copies each of two centered column vectors. -/
theorem mixed_fourth {v w : Fin 4 → ℂ} (hv : ∑ i, v i = 0) (hw : ∑ i, w i = 0) :
    (∑ σ : Equiv.Perm (Fin 4), v (σ 0) * v (σ 1) * w (σ 2) * w (σ 3)) =
    (∑ i, (v i)^2) * (∑ i, (w i)^2) + 2 * (∑ i, v i * w i)^2 -
      6 * ∑ i, (v i)^2 * (w i)^2 := by
  have h3 (u : Fin 4 → ℂ) (hu : ∑ i, u i = 0) : u 3 = -(u 0 + u 1 + u 2) := by
    simp [Fin.sum_univ_succ] at hu
    linear_combination hu
  change (∑ σ : Equiv.Perm (Fin 4), (fun i j k l => v i * v j * w k * w l)
    (σ 0) (σ 1) (σ 2) (σ 3)) = _
  rw [sum_four_permutations (fun i j k l => v i * v j * w k * w l)]
  simp [Fin.sum_univ_succ,h3 v hv,h3 w hw]
  ring

private def rootFour : Fin 4 → ℂ := ![1,Complex.I,-1,-Complex.I]

theorem fourth_root_mixed_moment :
    (∑ σ : Equiv.Perm (Fin 4), rootFour (σ 0) * rootFour (σ 1) *
      (rootFour (σ 2))^3 * (rootFour (σ 3))^3) = 8 := by
  let w (i : Fin 4) := (rootFour i)^3
  have hv : ∑ i, rootFour i = 0 := by simp [Fin.sum_univ_succ,rootFour]
  have hw : ∑ i, w i = 0 := by
    norm_num [Fin.sum_univ_succ,rootFour,w,pow_succ,Complex.I_mul_I]
  have h := mixed_fourth hv hw
  change (∑ σ : Equiv.Perm (Fin 4), rootFour (σ 0) * rootFour (σ 1) *
    w (σ 2) * w (σ 3)) = 8
  rw [h]
  norm_num [Fin.sum_univ_succ,rootFour,w,pow_succ,Complex.I_mul_I]

end SquareFourMoments

namespace CenteredRowFive

private def rowParam (a : Fin 4 → ℂ) : Fin 5 → ℂ :=
  Fin.cons (-∑ j, a j) a

private theorem sum_rowParam (a : Fin 4 → ℂ) : (∑ j, rowParam a j) = 0 := by
  simp [rowParam,Fin.sum_univ_succ]

private def rowMap (L : Submodule ℂ Square)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L) : (Fin 4 → ℂ) →ₗ[ℂ] L where
  toFun a := ⟨rowOnly (rowParam a), hrow _ (sum_rowParam a)⟩
  map_add' a b := by
    apply Subtype.ext
    funext ⟨i,j⟩
    by_cases hi : i = 0
    · subst i
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [rowOnly,rowParam,Finset.sum_add_distrib,add_comm]
    · simp [rowOnly,hi]
  map_smul' c a := by
    apply Subtype.ext
    funext ⟨i,j⟩
    by_cases hi : i = 0
    · subst i
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [rowOnly,rowParam,smul_eq_mul,Finset.mul_sum]
    · simp [rowOnly,hi]

/-- Removing the distinguished row costs exactly four dimensions. -/
theorem centered_row_dimension (L : Submodule ℂ Square)
    (hlevel : ∀ x ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + x (i,e i))) = 120)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L) :
    Module.finrank ℂ L = Module.finrank ℂ (L.map upper) + 4 := by
  let f := upper.domRestrict L
  let g := rowMap L hrow
  have hg : Function.Injective g := by
    intro a b hab
    funext i
    exact congrArg (fun x : L => x.val (0,i.succ)) hab
  have hk : LinearMap.ker f = LinearMap.range g := by
    ext x
    constructor
    · intro hx
      have ht : upper x.val = 0 := hx
      have hs := (centered_row_reduction L hlevel hrow x.property).1
      rw [Fin.sum_univ_succ] at hs
      refine ⟨fun j => x.val (0,j.succ),?_⟩
      apply Subtype.ext
      funext ⟨i,j⟩
      refine Fin.cases ?_ (fun a => ?_) i
      · refine Fin.cases ?_ (fun k => ?_) j
        · change -(∑ k : Fin 4, x.val (0,k.succ)) = x.val (0,0)
          linear_combination -hs
        · rfl
      · have hh := congrFun ht (a,j)
        simpa [g,rowMap,rowOnly,upper] using hh.symm
    · rintro ⟨a,rfl⟩
      apply LinearMap.mem_ker.mpr
      funext ⟨i,j⟩
      simp [f,g,rowMap,rowOnly,upper]
  have h := f.finrank_range_add_finrank_ker
  rw [hk,LinearMap.finrank_range_of_inj hg,Module.finrank_fin_fun] at h
  have he : LinearMap.range f = L.map upper := by
    ext A
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  rw [he] at h
  exact h.symm

end CenteredRowFive

namespace CenteredRowFive

open scoped Classical
open Finset

private theorem deleted_level (K : Submodule ℂ Upper)
    (hK : ∀ A ∈ K, ∀ j, cofactor A j = 24) {A : Upper} (hA : A ∈ K) (j : Fin 5) :
    ∀ t, SquareFourMoments.perm (fun i k => A (i,j.succAbove k)) t = 24 := by
  intro t
  simpa [SquareFourMoments.perm,cofactor,Pi.smul_apply,smul_eq_mul] using
    hK (t • A) (K.smul_mem t hA) j

/-- Every column of the projected four-by-five matrix sums to zero. -/
theorem projected_columns_centered (K : Submodule ℂ Upper)
    (hK : ∀ A ∈ K, ∀ j, cofactor A j = 24) {A : Upper} (hA : A ∈ K) :
    ∀ j, ∑ i, A (i,j) = 0 := by
  let s (j : Fin 5) : ℂ := ∑ i, A (i,j)
  have hm (j : Fin 5) : (∑ k : Fin 4, s (j.succAbove k)) = 0 :=
    SquareFourMoments.sum_entries_zero (deleted_level K hK hA j)
  have ht (j : Fin 5) : (∑ k, s k) = s j := by
    rw [Fin.sum_univ_succAbove s j,hm,add_zero]
  have hx : (∑ k, s k) = ∑ _ : Fin 5, (∑ k, s k) :=
    Finset.sum_congr rfl fun k _ => (ht k).symm
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hx
  intro j
  change s j = 0
  rw [← ht j]
  linear_combination -hx / 4

/-- The five maps that subtract the row sum from twice a column all have the
same complex bilinear quadratic form on the projected space. -/
theorem projected_gram (K : Submodule ℂ Upper)
    (hK : ∀ A ∈ K, ∀ j, cofactor A j = 24) {A : Upper} (hA : A ∈ K) :
    ∀ j, (∑ i, (2 * A (i,j) - ∑ k, A (i,k))^2) = ∑ i, (∑ k, A (i,k))^2 := by
  let S i : ℂ := ∑ k, A (i,k)
  let R i : ℂ := ∑ k, (A (i,k))^2
  let q : ℂ := ∑ i, (S i)^2
  let r : ℂ := ∑ i, R i
  let D (j : Fin 5) : ℂ := ∑ i, ((A (i,j))^2 - S i * A (i,j))
  have missing (f : Fin 5 → ℂ) (j : Fin 5) : (∑ k : Fin 4, f (j.succAbove k)) =
      (∑ k, f k) - f j := by rw [Fin.sum_univ_succAbove f j]; ring
  have hm (j : Fin 5) : (∑ i, (S i - A (i,j))^2) = ∑ i, (R i - (A (i,j))^2) := by
    have hh := SquareFourMoments.row_square (deleted_level K hK hA j)
      (fun k => projected_columns_centered K hK hA (j.succAbove k))
    have h1 (i : Fin 4) : (∑ k : Fin 4, A (i,j.succAbove k)) = S i - A (i,j) :=
      missing (fun k => A (i,k)) j
    have h2 (i : Fin 4) : (∑ k : Fin 4, (A (i,j.succAbove k))^2) = R i - (A (i,j))^2 :=
      missing (fun k => (A (i,k))^2) j
    simp_rw [h1,h2] at hh
    exact hh
  have hd (j : Fin 5) : 2 * D j = r - q := by
    calc
      2 * D j = (∑ i, (S i - A (i,j))^2) - (∑ i, (R i - (A (i,j))^2)) + (r-q) := by
        simp only [D,r,q,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = r - q := by rw [hm]; ring
  have hall : (∑ j, D j) = r-q := by
    change (∑ j, ∑ i, ((A (i,j))^2 - S i * A (i,j))) = _
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,r,q,R,S,pow_two]
  have ht := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hd j)
  rw [← Finset.mul_sum,hall] at ht
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at ht
  have hrq : r - q = 0 := by linear_combination -ht / 3
  intro j
  have hdj := hd j
  rw [hrq] at hdj
  calc
    (∑ i, (2 * A (i,j) - S i)^2) = q + 2 * (2 * D j) := by
      simp only [D,q,Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = q := by rw [hdj]; ring

end CenteredRowFive

namespace CenteredRowFive

open Finset Module LinearMap
open scoped Classical

def center : Submodule ℂ (Fin 4 → ℂ) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' {x y} hx hy := by
    change (∑ i, (x i + y i)) = 0
    rw [Finset.sum_add_distrib,hx,hy,add_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    change (∑ i, c * x i) = 0
    rw [← Finset.mul_sum,hx,mul_zero]

private def centerEquiv : (Fin 3 → ℂ) ≃ₗ[ℂ] center where
  toFun a := ⟨Fin.cons (-∑ i, a i) a, by
    change (∑ i, Fin.cons (-∑ j, a j) a i) = 0
    simp [Fin.sum_univ_succ]⟩
  invFun a := Fin.tail a.val
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h : (∑ k, x.val k) = 0 := x.property
    rw [Fin.sum_univ_succ] at h
    change -(∑ k : Fin 3, x.val k.succ) = x.val 0
    linear_combination -h
  map_add' x y := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change -(∑ k, (x k + y k)) = -(∑ k, x k) + -(∑ k, y k)
    rw [Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    change -(∑ k, c * x k) = c * -(∑ k, x k)
    rw [← Finset.mul_sum,mul_neg]

private def D : center →ₗ[ℂ] center →ₗ[ℂ] ℂ :=
  ((dotProductBilin ℂ ℂ : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) →ₗ[ℂ] ℂ).compl₂
    center.subtype).comp center.subtype

private theorem nondegenerateD (x : center) (h : ∀ y, D x y = 0) : x = 0 := by
  have hm (j : Fin 4) : x.val j = x.val 0 := by
    let y : Fin 4 → ℂ := fun k => (if k = j then 1 else 0) - (if k = 0 then 1 else 0)
    have hy : y ∈ center := by
      change (∑ k, y k) = 0
      simp [y,Finset.sum_sub_distrib]
    have hh := h ⟨y,hy⟩
    change (∑ k, x.val k * y k) = 0 at hh
    apply sub_eq_zero.mp
    simpa [y,mul_sub,mul_ite,Finset.sum_sub_distrib] using hh
  have hz : (∑ k, x.val k) = 0 := x.property
  simp_rw [hm] at hz
  norm_num at hz
  apply Subtype.ext
  funext j
  exact (hm j).trans hz

private def total (K : Submodule ℂ Upper)
    (hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0) : K →ₗ[ℂ] center where
  toFun A := ⟨fun i => ∑ j, A.val (i,j),by
    change (∑ i, ∑ j, A.val (i,j)) = 0
    rw [Finset.sum_comm]
    simp [hz _ A.property]⟩
  map_add' _ _ := by ext i; simp [Finset.sum_add_distrib]
  map_smul' _ _ := by ext i; simp [Finset.mul_sum,smul_eq_mul]

private def col (K : Submodule ℂ Upper)
    (hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0) (j : Fin 5) : K →ₗ[ℂ] center where
  toFun A := ⟨fun i => A.val (i,j),hz _ A.property _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def dirs (K : Submodule ℂ Upper)
    (hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0) : Option (Fin 5) → K →ₗ[ℂ] center
  | none => total K hz
  | some j => (2 : ℂ) • col K hz j - total K hz

private theorem symmetricD (x y : center) : D x y = D y x := by
  change (∑ i, x.val i * y.val i) = ∑ i, y.val i * x.val i
  simp only [mul_comm]

private theorem polar {U : Type*} [AddCommGroup U] [Module ℂ U] (a b : U →ₗ[ℂ] center)
    (h : ∀ x, D (a x) (a x) = D (b x) (b x)) (x y : U) : D (a x) (a y) = D (b x) (b y) := by
  have hxy := h (x+y)
  simp only [map_add,LinearMap.add_apply] at hxy
  rw [symmetricD (a y) (a x),symmetricD (b y) (b x)] at hxy
  linear_combination (hxy - h x - h y) / 2

/-- The Gram form of the sum of the five columns, restricted to the projected space. -/
def totalGram (K : Submodule ℂ Upper)
    (hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0) : K →ₗ[ℂ] K →ₗ[ℂ] ℂ :=
  (D.compl₂ (total K hz)).comp (total K hz)

/-- A projected space of dimension at least four has sum-of-columns Gram rank at most one. -/
theorem gram_rank_of_identities (K : Submodule ℂ Upper)
    (hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0)
    (hgram : ∀ A ∈ K, ∀ j, (∑ i, (2 * A (i,j) - ∑ k, A (i,k))^2) =
      ∑ i, (∑ k, A (i,k))^2) :
    Module.finrank ℂ K ≤ 3 ∨ Module.finrank ℂ (range (totalGram K hz)) ≤ 1 := by
  by_cases h : Module.finrank ℂ (range (totalGram K hz)) ≤ 1
  · exact Or.inr h
  left
  apply CenteredRowGram.three_dimensional_target D nondegenerateD (totalGram K hz) (dirs K hz)
  · intro o x y
    change D (dirs K hz o x) (dirs K hz o y) = D (total K hz x) (total K hz y)
    apply polar
    intro A
    cases o with
    | none => rfl
    | some j =>
      change (∑ i, (2 * A.val (i,j) - ∑ k, A.val (i,k)) *
        (2 * A.val (i,j) - ∑ k, A.val (i,k))) =
        ∑ i, (∑ k, A.val (i,k)) * (∑ k, A.val (i,k))
      simpa only [pow_two] using hgram A.val A.property j
  · intro A hA
    apply Subtype.ext
    funext ⟨i,j⟩
    have ha := congrArg (fun v : center => v.val i) (hA none)
    have hb := congrArg (fun v : center => v.val i) (hA (some j))
    change (∑ k, A.val (i,k)) = 0 at ha
    change 2 * A.val (i,j) - (∑ k, A.val (i,k)) = 0 at hb
    change A.val (i,j) = 0
    linear_combination (ha+hb)/2
  · exact centerEquiv.finrank_eq.symm.trans (Module.finrank_fin_fun ℂ)
  · omega

end CenteredRowFive

namespace CenteredRowFive

/-- For an eight-dimensional candidate with a full centered row, the projected
four-by-five space has dimension at least four and its sum-of-columns Gram form
has rank at most one. Its five complementary permanents all equal 24. -/
theorem centered_row_high_dimensional_constraint (L : Submodule ℂ Square)
    (hlevel : ∀ x ∈ L, (∑ e : Fin 5 ↪ Fin 5, ∏ i, (1 + x (i,e i))) = 120)
    (hrow : ∀ d : Fin 5 → ℂ, ∑ j, d j = 0 → rowOnly d ∈ L)
    (hbig : 8 ≤ Module.finrank ℂ L) :
    let K := L.map upper
    ∃ hz : ∀ A ∈ K, ∀ j, (∑ i, A (i,j)) = 0,
      4 ≤ Module.finrank ℂ K ∧ (∀ A ∈ K, ∀ j, cofactor A j = 24) ∧
      Module.finrank ℂ (LinearMap.range (totalGram K hz)) ≤ 1 := by
  let K := L.map upper
  have hK (A : Upper) (hA : A ∈ K) : ∀ j, cofactor A j = 24 := by
    obtain ⟨x,hx,rfl⟩ := hA
    exact (centered_row_reduction L hlevel hrow hx).2
  have hz (A : Upper) (hA : A ∈ K) := projected_columns_centered K hK hA
  have hd := centered_row_dimension L hlevel hrow
  change Module.finrank ℂ L = Module.finrank ℂ K + 4 at hd
  have hdim : 4 ≤ Module.finrank ℂ K := by omega
  have hh := gram_rank_of_identities K hz (fun A hA => projected_gram K hK hA)
  exact ⟨hz,hdim,hK,hh.resolve_left (by omega)⟩

end CenteredRowFive
