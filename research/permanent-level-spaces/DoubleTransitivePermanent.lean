import Mathlib

-- The finite permutation extension count and Minc expansion are adapted from the project.
namespace PermanentMaximal.Expansion

open Finset


def res {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) : Fin k ↪ Fin n :=
  ⟨fun a => σ (e a), σ.injective.comp e.injective⟩

@[simp] theorem res_apply {n k : ℕ} (e : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin n)) (a : Fin k) :
    res e σ a = σ (e a) := rfl


def emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Fin k ↪ Fin n :=
  ⟨fun a => R.1.orderEmbOfFin R.2 (τ a), (R.1.orderEmbOfFin R.2).injective.comp τ.injective⟩

@[simp] theorem emb_apply {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k})
    (τ : Equiv.Perm (Fin k)) (a : Fin k) : emb R τ a = R.1.orderEmbOfFin R.2 (τ a) := rfl


theorem card_extend {n k : ℕ} (e f : Fin k ↪ Fin n)
    [Fintype {σ : Equiv.Perm (Fin n) // res e σ = f}] :
    Fintype.card {σ : Equiv.Perm (Fin n) // res e σ = f} = (n - k).factorial := by
  classical
  let φ : Set.range e ≃ Set.range f :=
    (Equiv.ofInjective e e.injective).symm.trans (Equiv.ofInjective f f.injective)
  let σ0 : Equiv.Perm (Fin n) := φ.extendSubtype
  have hσ0 : ∀ a, σ0 (e a) = f a := by
    intro a
    have h1 := φ.extendSubtype_apply_of_mem (e a) (Set.mem_range_self a)
    have h2 : (Equiv.ofInjective e e.injective).symm ⟨e a, Set.mem_range_self a⟩ = a :=
      Equiv.ofInjective_symm_apply e.injective a
    simp only [σ0, h1, φ, Equiv.trans_apply, h2, Equiv.ofInjective_apply]
  have hres : ∀ σ : Equiv.Perm (Fin n), res e σ = f ↔ ∀ a, σ (e a) = f a := by
    intro σ
    constructor
    · intro h a
      have := DFunLike.congr_fun h a
      simpa using this
    · intro h
      ext a
      simp [h a]
  let E : {σ : Equiv.Perm (Fin n) // res e σ = f} ≃
      {τ : Equiv.Perm (Fin n) // ∀ x, ¬ (x ∉ Set.range e) → τ x = x} :=
    { toFun := fun σ => ⟨σ0⁻¹ * σ.1, by
        intro x hx
        rw [not_not] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [Equiv.Perm.mul_apply, (hres σ.1).1 σ.2 a, ← hσ0 a]
        simp⟩
      invFun := fun τ => ⟨σ0 * τ.1, by
        rw [hres]
        intro a
        rw [Equiv.Perm.mul_apply, τ.2 (e a) (by simp), hσ0]⟩
      left_inv := fun σ => Subtype.ext (by simp)
      right_inv := fun τ => Subtype.ext (by simp) }
  rw [Fintype.card_congr E, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm _),
    Fintype.card_perm, Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin,
    Fintype.card_fin]


theorem sum_perm_res {n k : ℕ} (e : Fin k ↪ Fin n) (F : (Fin k ↪ Fin n) → ℂ) :
    ∑ σ : Equiv.Perm (Fin n), F (res e σ) = ((n - k).factorial : ℂ) * ∑ f, F f := by
  classical
  rw [← Fintype.sum_fiberwise' (fun σ : Equiv.Perm (Fin n) => res e σ) F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_const, Finset.card_univ, card_extend, nsmul_eq_mul]

theorem range_emb {n k : ℕ} (R : {R : Finset (Fin n) // R.card = k}) (τ : Equiv.Perm (Fin k)) :
    Set.range (emb R τ) = (R.1 : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact Finset.orderEmbOfFin_mem R.1 R.2 _
  · intro hx
    rw [← Finset.range_orderEmbOfFin R.1 R.2] at hx
    obtain ⟨b, rfl⟩ := hx
    exact ⟨τ⁻¹ b, by simp⟩

theorem emb_bijective {n k : ℕ} :
    Function.Bijective
      (fun x : (Σ _ : {R : Finset (Fin n) // R.card = k}, Equiv.Perm (Fin k)) => emb x.1 x.2) := by
  constructor
  · rintro ⟨R, τ⟩ ⟨R', τ'⟩ h
    have h' : emb R τ = emb R' τ' := h
    have hRR : R = R' := by
      have := congrArg (fun g : Fin k ↪ Fin n => Set.range g) h'
      simp only [range_emb, Finset.coe_inj] at this
      exact Subtype.ext this
    subst hRR
    have hττ : τ = τ' := by
      ext a
      have := DFunLike.congr_fun h' a
      simp only [emb_apply] at this
      rw [(R.1.orderEmbOfFin R.2).injective this]
    subst hττ
    rfl
  · intro f
    have hc : (univ.map f).card = k := by simp
    have hm : ∀ a, f a ∈ univ.map f := fun a => by simp
    let g : Fin k → Fin k := fun a => ((univ.map f).orderIsoOfFin hc).symm ⟨f a, hm a⟩
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at hab
      exact hab
    refine ⟨⟨⟨univ.map f, hc⟩, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)⟩, ?_⟩
    ext a
    simp only [emb_apply, Equiv.ofBijective_apply, g]
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]


theorem sum_embedding {n k : ℕ} (G : (Fin k ↪ Fin n) → ℂ) :
    ∑ f, G f = ∑ R : {R : Finset (Fin n) // R.card = k}, ∑ τ : Equiv.Perm (Fin k),
      G (emb R τ) := by
  rw [← (emb_bijective (n := n) (k := k)).sum_comp G]
  exact Fintype.sum_sigma _

theorem prod_orderEmb {n k : ℕ} (C : Finset (Fin n)) (hC : C.card = k) (h : Fin n → ℂ) :
    ∏ j ∈ C, h j = ∏ a, h (C.orderEmbOfFin hC a) := by
  rw [← Finset.prod_coe_sort]
  exact (Fintype.prod_equiv (C.orderIsoOfFin hC).toEquiv _ _
    (fun a => by simp [Finset.coe_orderIsoOfFin_apply])).symm


theorem sum_perm_cols {n k : ℕ} (t : Fin n × Fin n → ℂ) (C : Finset (Fin n)) (hC : C.card = k) :
    ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) =
      ((n - k).factorial : ℂ) * ∑ R : {R : Finset (Fin n) // R.card = k},
        Matrix.permanent (Matrix.of fun i j : Fin k =>
          t (R.1.orderEmbOfFin R.2 i, C.orderEmbOfFin hC j)) := by
  calc ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j)
      = ∑ σ : Equiv.Perm (Fin n), (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
          (res (C.orderEmbOfFin hC).toEmbedding σ) :=
        Finset.sum_congr rfl fun σ _ => prod_orderEmb C hC _
    _ = ((n - k).factorial : ℂ) * ∑ g : Fin k ↪ Fin n, ∏ a, t (g a, C.orderEmbOfFin hC a) :=
        sum_perm_res (C.orderEmbOfFin hC).toEmbedding
          (fun g : Fin k ↪ Fin n => ∏ a, t (g a, C.orderEmbOfFin hC a))
    _ = _ := by rw [sum_embedding]; rfl


theorem eval_one_add (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun i j => 1 + t (i,j)) =
      ∑ C : Finset (Fin n), ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ C, t (σ j, j) := by
  rw [Matrix.permanent]
  simp only [Matrix.of_apply]
  simp_rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [Finset.sum_comm]


theorem sum_by_card {n : ℕ} (G : Finset (Fin n) → ℂ) :
    ∑ C : Finset (Fin n), G C =
      ∑ k ∈ range (n + 1), ∑ C : {C : Finset (Fin n) // C.card = k}, G C.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
    (fun C _ => by
      have := Finset.card_le_univ C
      rw [Fintype.card_fin] at this
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le this))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (by simp) G


noncomputable def Mk (n k : ℕ) (t : Fin n × Fin n → ℂ) : ℂ :=
  ∑ S : {S : Finset (Fin n) // S.card = k}, ∑ T : {T : Finset (Fin n) // T.card = k},
    Matrix.permanent (Matrix.of fun i j : Fin k =>
      t (S.1.orderEmbOfFin S.2 i, T.1.orderEmbOfFin T.2 j))


theorem minc_Mk (n : ℕ) (t : Fin n × Fin n → ℂ) :
    Matrix.permanent (Matrix.of fun i j => 1 + t (i,j)) =
      ∑ k ∈ Finset.range (n + 1), ((n - k).factorial : ℂ) * Mk n k t := by
  rw [eval_one_add, sum_by_card]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [fun C : {C : Finset (Fin n) // C.card = k} => sum_perm_cols t C.1 C.2]
  rw [← Finset.mul_sum, Mk, Finset.sum_comm]

theorem Mk_zero (n : ℕ) (t : Fin n × Fin n → ℂ) : Mk n 0 t = 1 := by
  have hu : ∀ S : {S : Finset (Fin n) // S.card = 0}, S = ⟨∅, Finset.card_empty⟩ :=
    fun S => Subtype.ext (Finset.card_eq_zero.mp S.2)
  rw [Mk, Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Fintype.sum_eq_single ⟨∅, Finset.card_empty⟩ (fun S hS => absurd (hu S) hS),
    Matrix.permanent_isEmpty]
end PermanentMaximal.Expansion
namespace PermanentLevel

open Finset
open scoped Classical

private noncomputable def exponents {k : ℕ} (f : Fin k → Fin k) : Fin k →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

private theorem exponent_eq_iff {k : ℕ} (f : Fin k → Fin k) :
    exponents f = exponents id ↔ Function.Bijective f := by
  constructor
  · intro h
    apply Finite.surjective_iff_bijective.mp
    intro i
    by_contra! hmiss
    have he := DFunLike.congr_fun h i
    simp [exponents,Finsupp.single_apply,hmiss] at he
  · intro hf
    exact Equiv.sum_comp (Equiv.ofBijective f hf) (fun i => Finsupp.single i (1 : ℕ))

private theorem eval_term {k : ℕ} (z : Fin k → ℂ) (f : Fin k → Fin k) (v : ℂ) :
    MvPolynomial.eval z (MvPolynomial.monomial (exponents f) v) = v * ∏ i, z (f i) := by
  have he : (MvPolynomial.monomial (exponents f) v : MvPolynomial (Fin k) ℂ) =
      MvPolynomial.C v * ∏ i, MvPolynomial.X (f i) := by
    exact MvPolynomial.monomial_sum_index Finset.univ (fun i => Finsupp.single (f i) 1) v
  rw [he]
  simp

theorem diagonal_coefficient {k : ℕ} (v : (Fin k → Fin k) → ℂ)
    (hs : ∀ e : Equiv.Perm (Fin k), v e = v id)
    (hz : ∀ z : Fin k → ℂ, ∑ f : Fin k → Fin k, v f * ∏ i, z (f i) = 0) :
    v id = 0 := by
  let p : MvPolynomial (Fin k) ℂ := ∑ f : Fin k → Fin k, MvPolynomial.monomial (exponents f) (v f)
  have hp : p = 0 := by
    apply MvPolynomial.funext
    intro z
    simpa [p,eval_term] using hz z
  have hc := congrArg (fun s : MvPolynomial (Fin k) ℂ => s.coeff (exponents id)) hp
  simp only [p,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
  let good : Finset (Fin k → Fin k) := Finset.univ.filter Function.Bijective
  have ht : ∀ f, (if exponents f = exponents id then v f else 0) =
      (if f ∈ good then v id else 0) := by
    intro f
    simp only [exponent_eq_iff,good,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs with h
    · exact hs (Equiv.ofBijective f h)
    · rfl
  simp_rw [ht] at hc
  have hid : id ∈ good := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Function.bijective_id⟩
  have hn : 0 < good.card := Finset.card_pos.mpr ⟨id,hid⟩
  have hprod : (good.card : ℂ) * v id = 0 := by
    simpa [← Finset.sum_filter, Finset.filter_mem_eq_inter] using hc
  exact (mul_eq_zero.mp hprod).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))


noncomputable def mixedSum {G J : Type*} [Fintype G] [Fintype J] {k : ℕ}
    (v : Fin k → G × J → ℂ) : ℂ :=
  ∑ x : Fin k ↪ G, ∑ y : Fin k ↪ J, ∏ i, v i (x i,y i)

private def precomposeEmb {I A : Type*} (σ : Equiv.Perm I) : (I ↪ A) ≃ (I ↪ A) where
  toFun f := σ.toEmbedding.trans f
  invFun f := σ.symm.toEmbedding.trans f
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

private theorem mixed_permute {G J : Type*} [Fintype G] [Fintype J] {k : ℕ}
    (v : Fin k → G × J → ℂ) (e : Equiv.Perm (Fin k)) :
    mixedSum (v ∘ e) = mixedSum v := by
  have hterm (x : Fin k ↪ G) (y : Fin k ↪ J) :
      (∏ i, v (e i) (x i,y i)) = ∏ i, v i ((precomposeEmb e.symm x) i,(precomposeEmb e.symm y) i) := by
    simpa [precomposeEmb] using Equiv.prod_comp e
      (fun i => v i ((precomposeEmb e.symm x) i,(precomposeEmb e.symm y) i))
  unfold mixedSum
  simp_rw [Function.comp_apply, hterm]
  have hy (x : Fin k ↪ G) :
      (∑ y : Fin k ↪ J, ∏ i, v i (x i, precomposeEmb e.symm y i)) =
      ∑ y : Fin k ↪ J, ∏ i, v i (x i,y i) :=
    Equiv.sum_comp (precomposeEmb e.symm) (fun y : Fin k ↪ J => ∏ i, v i (x i,y i))
  simp_rw [hy]
  exact Equiv.sum_comp (precomposeEmb e.symm) (fun x : Fin k ↪ G => ∑ y : Fin k ↪ J, ∏ i, v i (x i,y i))
  
theorem polarize_mixed {G J : Type*} [Fintype G] [Fintype J] {k : ℕ}
    (L : Submodule ℂ (G × J → ℂ))
    (hdiag : ∀ t ∈ L, mixedSum (fun _ : Fin k => t) = 0)
    (t : Fin k → G × J → ℂ) (ht : ∀ i, t i ∈ L) : mixedSum t = 0 := by
  apply diagonal_coefficient (fun f => mixedSum (t ∘ f))
  · intro e
    exact mixed_permute t e
  · intro z
    have hm := hdiag (∑ i, z i • t i) (L.sum_mem fun i _ => L.smul_mem _ (ht i))
    unfold mixedSum at hm ⊢
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Fintype.prod_sum] at hm
    simp only [Function.comp_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Eq.trans _ hm
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib,mul_comm]

end PermanentLevel
namespace PermanentLevel
open Finset
open scoped Classical
abbrev CardSubset (k n : ℕ) := {s : Finset (Fin n) // s.card = k}

private def fromRange {k n : ℕ} (p : CardSubset k n × Equiv.Perm (Fin k)) : Fin k ↪ Fin n :=
  p.2.toEmbedding.trans (p.1.val.orderEmbOfFin p.1.property).toEmbedding

private theorem range_fromRange {k n : ℕ} (p : CardSubset k n × Equiv.Perm (Fin k)) :
    Set.range (fromRange p) = (p.1.val : Set (Fin n)) := by
  change Set.range (p.1.val.orderEmbOfFin p.1.property ∘ p.2) = _
  rw [Set.range_comp,Set.range_eq_univ.mpr p.2.surjective,Set.image_univ,Finset.range_orderEmbOfFin]

private theorem fromRange_bijective {k n : ℕ} : Function.Bijective (@fromRange k n) := by
  constructor
  · rintro ⟨⟨R,hR⟩,σ⟩ ⟨⟨S,hS⟩,τ⟩ h
    have sets := congrArg (fun e : Fin k ↪ Fin n => Set.range e) h
    rw [range_fromRange,range_fromRange] at sets
    have he : R = S := Finset.coe_injective sets
    subst S
    congr 1
    exact Equiv.ext fun i => (R.orderEmbOfFin hR).injective (DFunLike.congr_fun h i)
  · intro e
    let s := Finset.univ.map e
    have hs : s.card = k := by simp [s]
    let g : Fin k → s := fun i => ⟨e i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    have bij : Function.Bijective g := by
      refine ⟨fun i j h => e.injective (congrArg Subtype.val h),?_⟩
      intro y
      obtain ⟨i,_,hi⟩ := Finset.mem_map.mp y.property
      exact ⟨i,Subtype.ext hi⟩
    let iso := s.orderIsoOfFin hs
    let σ := (Equiv.ofBijective g bij).trans iso.toEquiv.symm
    refine ⟨(⟨s,hs⟩,σ),?_⟩
    exact Function.Embedding.ext fun i => congrArg Subtype.val (iso.apply_symm_apply (g i))

/-- An ordered injection is an increasing enumeration of its image, precomposed by a permutation. -/
noncomputable def rangePermEquiv (k n : ℕ) : (CardSubset k n × Equiv.Perm (Fin k)) ≃ (Fin k ↪ Fin n) :=
  Equiv.ofBijective fromRange fromRange_bijective

theorem sum_embeddings_by_range {k n : ℕ} (f : (Fin k ↪ Fin n) → ℂ) :
    ∑ e, f e = ∑ S : CardSubset k n, ∑ σ : Equiv.Perm (Fin k),
      f (σ.toEmbedding.trans (S.val.orderEmbOfFin S.property).toEmbedding) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp (rangePermEquiv k n) f).symm

theorem sum_embedding_prod {k n : ℕ} (a : Fin n → ℂ) :
    ∑ e : Fin k ↪ Fin n, ∏ i, a (e i) =
      (k.factorial : ℂ) * ∑ S : CardSubset k n, ∏ j ∈ S.val, a j := by
  rw [sum_embeddings_by_range,Finset.mul_sum]
  apply Fintype.sum_congr
  intro S
  have one (σ : Equiv.Perm (Fin k)) :
      (∏ i, a ((σ.toEmbedding.trans (S.val.orderEmbOfFin S.property).toEmbedding) i)) =
      ∏ j ∈ S.val, a j := by
    calc
      _ = ∏ i, a (S.val.orderEmbOfFin S.property i) := Equiv.prod_comp σ _
      _ = ∏ j : S.val, a j.val := Equiv.prod_comp (S.val.orderIsoOfFin S.property).toEquiv (fun i : S.val => a i.val)
      _ = _ := Finset.prod_coe_sort _ _
  simp_rw [one]
  simp [Fintype.card_perm]

private def changePerm {k : ℕ} (τ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin k) ≃ Equiv.Perm (Fin k) where
  toFun σ := τ.symm.trans σ
  invFun σ := τ.trans σ
  left_inv σ := by ext i; simp
  right_inv σ := by ext i; simp

private def minor {k m n : ℕ} (t : Fin m × Fin n → ℂ) (R : CardSubset k m) (C : CardSubset k n) : ℂ :=
  Matrix.permanent (Matrix.of fun i j => t (R.val.orderEmbOfFin R.property i,C.val.orderEmbOfFin C.property j))

private theorem sum_perm_minor {k m n : ℕ} (t : Fin m × Fin n → ℂ) (R : CardSubset k m) (C : CardSubset k n)
    (τ : Equiv.Perm (Fin k)) :
    (∑ σ : Equiv.Perm (Fin k), ∏ i, t (R.val.orderEmbOfFin R.property (σ i),C.val.orderEmbOfFin C.property (τ i))) = minor t R C := by
  let term (σ : Equiv.Perm (Fin k)) := ∏ i, t (R.val.orderEmbOfFin R.property (σ i),C.val.orderEmbOfFin C.property i)
  change _ = ∑ σ, term σ
  rw [← Equiv.sum_comp (changePerm τ) term]
  apply Fintype.sum_congr
  intro σ
  simpa [term,changePerm] using Equiv.prod_comp τ (fun i => t (R.val.orderEmbOfFin R.property (σ (τ.symm i)),C.val.orderEmbOfFin C.property i))

private theorem sum_dite_sub {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] (f : Subtype p → ℂ) :
    (∑ a, if h : p a then f ⟨a,h⟩ else 0) = ∑ a, f a := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  have yes (a : Subtype p) : (if h : p a.val then f ⟨a.val,h⟩ else 0) = f a := dite_eq_left a.property
  have no (a : Subtype (fun x => ¬ p x)) : (if h : p a.val then f ⟨a.val,h⟩ else 0) = 0 := dite_eq_right a.property
  simp only [yes,no,Finset.sum_const_zero,add_zero]

theorem subsums {k m n : ℕ} (t : Fin m × Fin n → ℂ) :
    (∑ R : Finset (Fin m), ∑ C : Finset (Fin n), if h : R.card=k ∧ C.card=k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b)) else 0) =
      ∑ R : CardSubset k m, ∑ C : CardSubset k n, minor t R C := by
  calc
    _ = ∑ R : Finset (Fin m), if hR : R.card=k then (∑ C : CardSubset k n, minor t ⟨R,hR⟩ C) else 0 := by
      apply Fintype.sum_congr
      intro R
      by_cases hR : R.card=k
      · rw [dite_eq_left hR]
        calc
          _ = ∑ C : Finset (Fin n), if hC : C.card = k then minor t ⟨R,hR⟩ ⟨C,hC⟩ else 0 := by
            apply Fintype.sum_congr
            intro C
            by_cases hC : C.card=k
            · rw [dite_eq_left (And.intro hR hC),dite_eq_left hC]; rfl
            · rw [dite_eq_right (fun h => hC h.2),dite_eq_right hC]
          _ = _ := sum_dite_sub (fun C : Finset (Fin n) => C.card=k) (fun C => minor t ⟨R,hR⟩ C)
      · rw [dite_eq_right hR]
        apply Finset.sum_eq_zero
        exact fun C _ => dite_eq_right (fun h => hR h.1)
    _ = _ := sum_dite_sub (fun R : Finset (Fin m) => R.card=k) (fun R => ∑ C : CardSubset k n, minor t R C)

theorem mixedSum_subpermanent {k m n : ℕ} (t : Fin m × Fin n → ℂ) :
    mixedSum (fun _ : Fin k => t) = (k.factorial : ℂ) *
    (∑ R : Finset (Fin m), ∑ C : Finset (Fin n), if h : R.card=k ∧ C.card=k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b)) else 0) := by
  rw [subsums,Finset.sum_comm (f := fun (R : CardSubset k m) (C : CardSubset k n) => minor t R C),Finset.mul_sum]
  unfold mixedSum
  rw [Finset.sum_comm,sum_embeddings_by_range]
  apply Fintype.sum_congr
  intro C
  have inner (τ : Equiv.Perm (Fin k)) :
      (∑ x : Fin k ↪ Fin m, ∏ i, t (x i,(τ.toEmbedding.trans (C.val.orderEmbOfFin C.property).toEmbedding) i)) =
      ∑ R : CardSubset k m, minor t R C := by
    rw [sum_embeddings_by_range]
    exact Fintype.sum_congr _ _ (fun R => sum_perm_minor t R C τ)
  simp_rw [inner]
  simp [Fintype.card_perm]

theorem mixedSum_zero_of_subpermanent {k m n : ℕ} (t : Fin m × Fin n → ℂ)
    (h : (∑ R : Finset (Fin m), ∑ C : Finset (Fin n), if h : R.card=k ∧ C.card=k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b)) else 0) = 0) :
    mixedSum (fun _ : Fin k => t) = 0 := by rw [mixedSum_subpermanent,h,mul_zero]

end PermanentLevel
namespace PermanentMaximal
open Finset
open scoped Classical

abbrev permAt {n : ℕ} (T : Fin n × Fin n → ℂ) :=
  Matrix.permanent (Matrix.of fun i j => 1 + T (i,j))

theorem moment_scale {n k : ℕ} (T : Fin n × Fin n → ℂ) (c : ℂ) :
    Expansion.Mk n k (c • T) = c^k * Expansion.Mk n k T := by
  unfold Expansion.Mk
  simp only [Finset.mul_sum]
  apply Fintype.sum_congr
  intro S
  apply Fintype.sum_congr
  intro U
  let M : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun i j =>
    T (S.val.orderEmbOfFin S.property i,U.val.orderEmbOfFin U.property j)
  change (c • M).permanent = c^k * M.permanent
  simp

theorem translate_moments {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, permAt t = n.factorial) (t : Fin n × Fin n → ℂ) (ht : t ∈ L)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) : Expansion.Mk n k t=0 := by
  let a := fun i => ((n-i).factorial:ℂ) * Expansion.Mk n i t
  let P : Polynomial ℂ := ∑ i ∈ range (n+1), Polynomial.C (a i) * Polynomial.X ^ i
  have he : P = Polynomial.C (n.factorial:ℂ) := by
    apply Polynomial.funext
    intro z
    have hz := hL (z • t) (L.smul_mem z ht)
    rw [permAt,Expansion.minc_Mk] at hz
    simp_rw [moment_scale] at hz
    simp only [P,a,Polynomial.eval_finsetSum,Polynomial.eval_C,Polynomial.eval_X,
      Polynomial.eval_pow,Polynomial.eval_mul]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk' := congrArg (fun p : Polynomial ℂ => p.coeff k) he
  simp only [P,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C] at hk'
  have ha : a k=0 := by
    simpa [ne_of_gt hk,show k<n+1 by omega,eq_comm] using hk'
  exact (mul_eq_zero.mp ha).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem translated_mixed_zero {n k : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, permAt t = n.factorial) (hk : 0 < k) (hkn : k ≤ n)
    (t : Fin k → Fin n × Fin n → ℂ) (ht : ∀ i, t i ∈ L) :
    PermanentLevel.mixedSum t = 0 := by
  apply PermanentLevel.polarize_mixed L _ t ht
  intro T hT
  rw [PermanentLevel.mixedSum_subpermanent,PermanentLevel.subsums]
  change (k.factorial:ℂ) * Expansion.Mk n k T = 0
  rw [translate_moments L hL _ hT hk hkn,mul_zero]

end PermanentMaximal



namespace DoubleTransitive
open Finset
open scoped Classical

noncomputable def elem {n : ℕ} (u : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, u i

def star {m : ℕ} (r i : Fin m) : ℂ := if i=r then (m:ℂ)-1 else -1

theorem elem_support {n : ℕ} (v : Fin n → ℂ) :
    let S := (univ : Finset (Fin n)).filter (fun i => v i ≠ 0)
    elem v S.card ≠ 0 := by
  classical
  let S := (univ : Finset (Fin n)).filter (fun i => v i ≠ 0)
  change elem v S.card ≠ 0
  rw [elem,Finset.sum_eq_single S]
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => (Finset.mem_filter.mp hi).2)
  · intro t ht hne
    have hcard := (Finset.mem_powersetCard.mp ht).2
    have hn : ¬ t ⊆ S := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge)
    obtain ⟨i,hi,hoff⟩ := Finset.not_subset.mp hn
    apply Finset.prod_eq_zero hi
    simpa [S] using hoff
  · simp [mem_powersetCard]

theorem elem_ones {m k : ℕ} : elem (fun _ : Fin m => (1:ℂ)) k = m.choose k := by
  simp [elem,Finset.card_powersetCard]

private theorem star_term {m : ℕ} (s : Finset (Fin m)) (r : Fin m) (hs : r∈s) :
    ∏ i ∈ s, star r i = ((m:ℂ)-1) * (-1)^((s.erase r).card) := by
  rw [← Finset.mul_prod_erase s (star r) hs]
  simp only [star]
  congr 1
  calc
    _ = ∏ _i ∈ s.erase r, (-1:ℂ) := prod_congr rfl (fun i hi => ite_eq_right (mem_erase.mp hi).1)
    _ = _ := Finset.prod_const _
    
theorem elem_star {m k : ℕ} (r : Fin m) (hk : 2 ≤ k) (hkm : k ≤ m) :
    elem (star r) k ≠ 0 := by
  classical
  let U := (univ : Finset (Fin m)).erase r
  have hu : U.card=m-1 := by simp [U]
  have hn : r ∉ U := notMem_erase _ _
  have he : elem (star r) k =
      (m-1).choose k * (-1:ℂ)^k + (m-1).choose (k-1) * (((m:ℂ)-1) * (-1:ℂ)^(k-1)) := by
    unfold elem
    have hsub : (univ : Finset (Fin m))=insert r U := (insert_erase (mem_univ _)).symm
    have hp : k=(k-1)+1 := by omega
    have hsplit : (univ : Finset (Fin m)).powersetCard k =
        U.powersetCard k ∪ (U.powersetCard (k-1)).image (insert r) := by
      conv_lhs => rw [hsub,hp]
      simpa only [Nat.succ_eq_add_one,←hp] using powersetCard_succ_insert hn (k-1)
    rw [hsplit,Finset.sum_union]
    · apply congrArg₂ (·+·)
      · calc
          _ = ∑ _s ∈ U.powersetCard k, (-1:ℂ)^k := by
            apply Finset.sum_congr rfl
            intro s hs
            have H := mem_powersetCard.mp hs
            have hr : ∀ i ∈ s, i ≠ r := fun i hi => (mem_erase.mp (H.1 hi)).1
            calc
              _ = ∏ _i ∈ s, (-1:ℂ) := prod_congr rfl fun i hi => ite_eq_right (hr i hi)
              _ = _ := by rw [Finset.prod_const,H.2]
          _ = _ := by simp [nsmul_eq_mul,card_powersetCard,hu]
      · rw [Finset.sum_image]
        · calc
            _ = ∑ _s ∈ U.powersetCard (k-1), (((m:ℂ)-1) * (-1:ℂ)^(k-1)) := by
              apply Finset.sum_congr rfl
              intro s hs
              have H := mem_powersetCard.mp hs
              have hr : r∉s := fun h => hn (H.1 h)
              rw [star_term _ _ (mem_insert_self ..),erase_insert hr,H.2]
            _ = _ := by simp [nsmul_eq_mul,card_powersetCard,hu]
        · intro s hs t ht he
          have es := congrArg (fun a : Finset (Fin m) => a.erase r) he
          have hsr : r∉s := fun h => hn ((mem_powersetCard.mp hs).1 h)
          have htr : r∉t := fun h => hn ((mem_powersetCard.mp ht).1 h)
          simpa [erase_insert hsr,erase_insert htr] using es
    · rw [disjoint_left]
      rintro s hs hi
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hi
      exact hn ((mem_powersetCard.mp hs).1 (mem_insert_self ..))
  have hbig : (m-1).choose k < (m-1)*(m-1).choose (k-1) := by
    have hpos := Nat.choose_pos (show k-1 ≤ m-1 by omega)
    have hpas := Nat.choose_succ_right_eq (m-1) (k-1)
    rw [show k-1+1=k by omega,show m-1-(k-1)=m-k by omega] at hpas
    calc
      _ ≤ (m-1).choose k*k := Nat.le_mul_of_pos_right _ (by omega)
      _ = (m-1).choose (k-1)*(m-k) := hpas
      _ < (m-1).choose (k-1)*(m-1) := Nat.mul_lt_mul_of_pos_left (by omega) hpos
      _ = _ := Nat.mul_comm _ _
  rw [he]
  have hpow : (-1:ℂ)^k = -((-1:ℂ)^(k-1)) := by
    conv_lhs => rw [show k=(k-1)+1 by omega,pow_succ]
    ring
  rw [hpow]
  intro h
  have hnz : (-1:ℂ)^(k-1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hz : (((m-1).choose (k-1):ℂ)*((m:ℂ)-1)-(m-1).choose k) * (-1:ℂ)^(k-1)=0 := by
    linear_combination h
  have final := (mul_eq_zero.mp hz).resolve_right hnz
  have hc : ((m-1:ℕ):ℂ)=(m:ℂ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have eq : (m-1)*(m-1).choose (k-1) = (m-1).choose k := by
    exact_mod_cast (show ((m-1:ℕ):ℂ)*(m-1).choose (k-1)=(m-1).choose k by rw [hc]; linear_combination final)
  omega

end DoubleTransitive


namespace DoubleTransitive
open Finset
open scoped Classical

def rowAction {m q : ℕ} (g : Equiv.Perm (Fin m)) (T : Fin m × Fin q → ℂ) (x : Fin m × Fin q) : ℂ :=
  T (g x.1,x.2)

def Stable {m q : ℕ} (G : Subgroup (Equiv.Perm (Fin m))) (L : Submodule ℂ (Fin m × Fin q → ℂ)) :=
  ∀ T ∈ L, ∀ g ∈ G, rowAction g T ∈ L

def Doubly {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m))) :=
  ∀ r i s j : Fin m, r ≠ i → s ≠ j → ∃ g ∈ G, g r=s ∧ g i=j

private theorem another {m : ℕ} (hm : 2 ≤ m) (r : Fin m) : ∃ i : Fin m, r ≠ i := by
  by_cases h : r.val=0
  · exact ⟨⟨1,by omega⟩, fun e => by have := congrArg Fin.val e; dsimp at this; omega⟩
  · exact ⟨⟨0,by omega⟩,fun e => h (congrArg Fin.val e)⟩

theorem transitive {m : ℕ} (hm : 2 ≤ m) (G : Subgroup (Equiv.Perm (Fin m)))
    (hG : Doubly G) (r s : Fin m) : ∃ g ∈ G, g r=s := by
  obtain ⟨i,hi⟩ := another hm r
  obtain ⟨j,hj⟩ := another hm s
  obtain ⟨g,hg,hrs,_⟩ := hG _ _ _ _ hi hj
  exact ⟨g,hg,hrs⟩

def fix {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m))) (r : Fin m) : Subgroup (Equiv.Perm (Fin m)) where
  carrier := {g | g ∈ G ∧ g r=r}
  one_mem' := ⟨G.one_mem,rfl⟩
  mul_mem' := fun ha hb => ⟨G.mul_mem ha.1 hb.1,by simp [Equiv.Perm.mul_apply,ha.2,hb.2]⟩
  inv_mem' := by
    intro g h
    refine ⟨G.inv_mem h.1,?_⟩
    exact (congrArg g.symm h.2.symm).trans (g.symm_apply_apply r)

noncomputable def rowSum {m q : ℕ} (H : Subgroup (Equiv.Perm (Fin m))) (T : Fin m × Fin q → ℂ) :
    Fin m × Fin q → ℂ := ∑ g : H, rowAction g.val T

theorem rowSum_mem {m q : ℕ} {G H : Subgroup (Equiv.Perm (Fin m))} (hle : H ≤ G)
    {L : Submodule ℂ (Fin m × Fin q → ℂ)} (hs : Stable G L) (T : Fin m × Fin q → ℂ) (hT : T∈L) :
    rowSum H T ∈ L := L.sum_mem (fun g _ => hs T hT g.val (hle g.property))

theorem rowSum_move {m q : ℕ} (H : Subgroup (Equiv.Perm (Fin m))) (T : Fin m × Fin q → ℂ)
    (g : H) (r : Fin m) (j : Fin q) : rowSum H T (g.val r,j)=rowSum H T (r,j) := by
  simp only [rowSum,Finset.sum_apply,rowAction]
  exact Equiv.sum_comp (Equiv.mulRight g) (fun h : H => T (h.val r,j))

private theorem sum_rowSum {m q : ℕ} (H : Subgroup (Equiv.Perm (Fin m))) (T : Fin m × Fin q → ℂ)
    (j : Fin q) : (∑ i, rowSum H T (i,j)) = (Fintype.card H:ℂ) * ∑ i, T (i,j) := by
  simp only [rowSum,Finset.sum_apply,rowAction]
  rw [Finset.sum_comm]
  simp_rw [fun g : H => Equiv.sum_comp g.val (fun i => T (i,j))]
  simp [nsmul_eq_mul]

theorem centred {m q : ℕ} (hm : 2 ≤ m) (G : Subgroup (Equiv.Perm (Fin m))) (hG : Doubly G)
    (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hs : Stable G L)
    (hrep : ∀ a : Fin q → ℂ, (fun p : Fin m × Fin q => a p.2) ∈ L → ∀ j, a j=0)
    (T : Fin m × Fin q → ℂ) (hT : T∈L) (j : Fin q) : ∑ i, T (i,j)=0 := by
  let r : Fin m := ⟨0,by omega⟩
  let a := fun z : Fin q => rowSum G T (r,z)
  have eq : rowSum G T = (fun p : Fin m × Fin q => a p.2) := by
    funext p
    obtain ⟨g,hg,he⟩ := transitive hm G hG r p.1
    change rowSum G T (p.1,p.2)=rowSum G T (r,p.2)
    exact he ▸ rowSum_move G T (⟨g,hg⟩ : G) r p.2
  have hr := rowSum_mem le_rfl hs T hT
  rw [eq] at hr
  have h := sum_rowSum G T j
  rw [eq] at h
  simp only [hrep a hr j,Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

theorem stabilizer_star {m q : ℕ} (hm : 2 ≤ m) (G : Subgroup (Equiv.Perm (Fin m))) (hG : Doubly G)
    (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hs : Stable G L)
    (hcen : ∀ T ∈ L, ∀ j, ∑ i, T (i,j)=0)
    (T : Fin m × Fin q → ℂ) (hT : T∈L) (r : Fin m) :
    (fun p : Fin m × Fin q => (if p.1=r then (m:ℂ)-1 else -1)*T (r,p.2)) ∈ L := by
  classical
  let H := fix G r
  let W := rowSum H T
  have hW : W ∈ L := rowSum_mem (show H ≤ G from fun _ hx => hx.1) hs _ hT
  let c : ℂ := Fintype.card H
  have hc : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have base (j : Fin q) : W (r,j)=c*T (r,j) := by
    have fixs (g : H) : g.val r=r := g.property.2
    simp [W,rowSum,rowAction,fixs,c,nsmul_eq_mul]
  have others (j : Fin q) {i l : Fin m} (hi : i ≠ r) (hl : l ≠ r) : W (i,j)=W (l,j) := by
    obtain ⟨g,hg,hr,hil⟩ := hG r i r l hi.symm hl.symm
    have move := rowSum_move H T (⟨g,hg,hr⟩ : H) i j
    simpa [W,hil] using move.symm
  have off (i : Fin m) (j : Fin q) (hi : i ≠ r) : ((m:ℂ)-1)*W (i,j) = -c*T (r,j) := by
    have sum := hcen W hW j
    rw [← Finset.add_sum_erase _ _ (mem_univ r),base] at sum
    have rem : (∑ z ∈ univ.erase r, W (z,j))=((m:ℂ)-1)*W (i,j) := by
      calc
        _ = ∑ _z ∈ univ.erase r, W (i,j) := sum_congr rfl (fun z hz => others j (mem_erase.mp hz).1 hi)
        _ = _ := by simp [nsmul_eq_mul,Nat.cast_sub (show 1 ≤ m by omega)]
    rw [rem] at sum
    linear_combination sum
  have eq : (((m:ℂ)-1)/c) • W =
      (fun p : Fin m × Fin q => (if p.1=r then (m:ℂ)-1 else -1)*T (r,p.2)) := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul]
    by_cases h : p.1=r
    · obtain ⟨i,j⟩ := p
      dsimp at h ⊢
      subst i
      rw [ite_eq_left rfl,base]
      field_simp
    · obtain ⟨i,j⟩ := p
      dsimp at h ⊢
      rw [ite_eq_right h]
      field_simp [hc]
      linear_combination off i j h
  exact eq ▸ L.smul_mem _ hW

end DoubleTransitive

namespace DoubleTransitive
open Finset
open scoped Classical

def pair {m q : ℕ} (u : Fin m → ℂ) (v : Fin q → ℂ) (p : Fin m × Fin q) : ℂ :=
  u p.1*v p.2

def Level {m q : ℕ} (L : Submodule ℂ (Fin m × Fin q → ℂ)) : Prop :=
  ∀ T ∈ L, ∀ k, 1 ≤ k → k ≤ min m q → PermanentLevel.mixedSum (fun _ : Fin k => T) = 0

theorem pair_moment {m q k : ℕ} (u : Fin m → ℂ) (v : Fin q → ℂ) :
    PermanentLevel.mixedSum (fun _ : Fin k => pair u v) =
    ((k.factorial:ℂ)*elem u k) * ((k.factorial:ℂ)*elem v k) := by
  have one {n : ℕ} (w : Fin n → ℂ) : (∑ e : Fin k ↪ Fin n, ∏ i, w (e i)) = (k.factorial:ℂ)*elem w k := by
    rw [PermanentLevel.sum_embedding_prod]
    congr 1
    exact (Finset.sum_subtype (univ.powersetCard k) (p := fun s : Finset (Fin n) => s.card=k)
      (fun s => by simp [Finset.mem_powersetCard]) (fun s => ∏ i ∈ s, w i)).symm
  simp only [PermanentLevel.mixedSum,pair,Finset.prod_mul_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [one,one]

theorem repeated_vanish {m q : ℕ} (hq : q ≤ m) (L : Submodule ℂ (Fin m × Fin q → ℂ))
    (hL : Level L) (a : Fin q → ℂ) (ha : (fun p : Fin m × Fin q => a p.2) ∈ L) (j : Fin q) :
    a j=0 := by
  classical
  by_contra hj
  let s := univ.filter (fun i => a i ≠ 0)
  have hm : s.card ≤ q := by simpa using card_le_univ s
  have hl : 1 ≤ s.card := Finset.card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
  have hmem : pair (fun _ : Fin m => 1) a ∈ L := by
    have e : pair (fun _ : Fin m => 1) a = (fun p : Fin m × Fin q => a p.2) := funext fun _ => one_mul _
    rwa [e]
  have he := hL _ hmem s.card hl (le_min (hm.trans hq) hm)
  rw [pair_moment,elem_ones] at he
  have e := elem_support a
  change elem a s.card ≠ 0 at e
  exact (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    (Nat.cast_ne_zero.mpr (Nat.choose_pos (hm.trans hq)).ne'))
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) e)) he

theorem sparse {m q : ℕ} (hm : 2 ≤ m) (hq : q ≤ m) (G : Subgroup (Equiv.Perm (Fin m))) (hG : Doubly G)
    (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hL : Level L) (hs : Stable G L)
    (T : Fin m × Fin q → ℂ) (hT : T∈L) (r : Fin m) (j l : Fin q)
    (hj : T (r,j) ≠ 0) (hl : T (r,l) ≠ 0) : j=l := by
  classical
  by_contra hn
  let a := fun j => T (r,j)
  let s := univ.filter (fun i => a i ≠ 0)
  have hcard : s.card ≤ q := by simpa using card_le_univ s
  have hi : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨j,by simpa [s,a],l,by simpa [s,a],hn⟩
  have hmem : pair (star r) a ∈ L := stabilizer_star hm G hG L hs
    (centred hm G hG L hs (repeated_vanish hq L hL)) T hT r
  have he := hL _ hmem s.card (by omega) (le_min (hcard.trans hq) hcard)
  rw [pair_moment] at he
  have ev : elem a s.card ≠ 0 := elem_support _
  have hnz : (s.card.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact (mul_ne_zero (mul_ne_zero hnz (elem_star r hi (hcard.trans hq))) (mul_ne_zero hnz ev)) he

def column {m q : ℕ} (j : Fin q) : Submodule ℂ (Fin m × Fin q → ℂ) where
  carrier := {T | (∀ r l, l ≠ j → T (r,l)=0) ∧ ∑ r, T (r,j)=0}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨fun r l h => by simp [ha r l h,hb r l h],by simp [Finset.sum_add_distrib,ha',hb']⟩
  smul_mem' := by
    rintro c a ⟨ha,ha'⟩
    exact ⟨fun r l h => by simp [ha r l h],by simp [←Finset.mul_sum,ha']⟩

theorem contains_stars {m q : ℕ} (hm : 2 ≤ m) (hq : q ≤ m) (G : Subgroup (Equiv.Perm (Fin m))) (hG : Doubly G)
    (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hL : Level L) (hs : Stable G L)
    (T : Fin m × Fin q → ℂ) (hT : T∈L) (r : Fin m) (j : Fin q) (hj : T (r,j) ≠ 0) (i : Fin m) :
    (fun p : Fin m × Fin q => if p.2=j then star i p.1 else 0) ∈ L := by
  obtain ⟨g,hg,he⟩ := transitive hm G hG i r
  have hact := hs T hT g hg
  have hmem := stabilizer_star hm G hG L hs (centred hm G hG L hs (repeated_vanish hq L hL))
    _ hact i
  have eq : (T (r,j))⁻¹ • (fun p : Fin m × Fin q => star i p.1 * rowAction g T (i,p.2)) =
      (fun p : Fin m × Fin q => if p.2=j then star i p.1 else 0) := by
    funext p
    simp only [Pi.smul_apply,smul_eq_mul,rowAction,he]
    by_cases h : p.2=j
    · rw [ite_eq_left h,h]; field_simp
    · have z : T (r,p.2)=0 := by
        by_contra hn
        exact h (sparse hm hq G hG L hL hs T hT r p.2 j hn hj)
      simp [h,z]
  exact eq ▸ L.smul_mem _ hmem

theorem level_classification {m q : ℕ} (hm : 2 ≤ m) (hq : q ≤ m) (G : Subgroup (Equiv.Perm (Fin m)))
    (hG : Doubly G) (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hL : Level L) (hs : Stable G L) :
    L=⊥ ∨ ∃ j : Fin q, L=column j := by
  classical
  by_cases h : L=⊥
  · exact Or.inl h
  obtain ⟨T,hT,hne⟩ := L.ne_bot_iff.mp h
  obtain ⟨r,j,hj⟩ : ∃ r j, T (r,j) ≠ 0 := by
    by_contra! z
    exact hne (funext fun p => z p.1 p.2)
  right
  refine ⟨j,le_antisymm ?_ ?_⟩
  · intro V hV
    refine ⟨?_,centred hm G hG L hs (repeated_vanish hq L hL) V hV j⟩
    intro i l hl
    by_contra hv
    obtain ⟨g,hg,he⟩ := transitive hm G hG r i
    let W := rowAction g V
    have hW : W∈L := hs _ hV _ hg
    have hwl : W (r,l) ≠ 0 := by simpa [W,rowAction,he] using hv
    have hwj : W (r,j)=0 := by
      by_contra! hn
      exact hl (sparse hm hq G hG L hL hs W hW r l j hwl hn)
    have htl : T (r,l)=0 := by
      by_contra! hn
      exact hl (sparse hm hq G hG L hL hs T hT r l j hn hj)
    exact hl (sparse hm hq G hG L hL hs _ (L.add_mem hT hW) r l j
      (by simpa [htl] using hwl) (by simpa [hwj] using hj))
  · intro V hV
    obtain ⟨ho,hc⟩ := hV
    have hgen := contains_stars hm hq G hG L hL hs T hT r j hj
    have hmz : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have eq : ∑ i : Fin m, (V (i,j)/m) • (fun p : Fin m × Fin q => if p.2=j then star i p.1 else 0) = V := by
      funext p
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      by_cases hp : p.2=j
      · simp only [ite_eq_left hp]
        have form (i : Fin m) : (V (i,j)/m)*star i p.1 =
            (if i=p.1 then V (i,j) else 0) - V (i,j)/m := by
          by_cases hi : i=p.1
          · simp [star,hi]; field_simp [hmz]
          · simp [star,hi,Ne.symm hi]
        simp_rw [form]
        rw [Finset.sum_sub_distrib,← Finset.sum_div,hc]
        simp only [Finset.sum_ite_eq',mem_univ,ite_true,zero_div,sub_zero]
        exact congrArg V (Prod.ext rfl hp.symm)
      · simp [hp,ho p.1 p.2 hp]
    rw [← eq]
    exact L.sum_mem (fun i _ => L.smul_mem _ (hgen i))

end DoubleTransitive

namespace RectangularPermanent
open Finset
open scoped Classical

def includeCol {m q : ℕ} (h : q ≤ m) : Fin q ↪ Fin m := ⟨fun j => ⟨j.val,by omega⟩,fun i j e => Fin.ext (congrArg (fun x : Fin m => x.val) e)⟩

def liveCols {m q : ℕ} (h : q ≤ m) : Fin q ≃ {i : Fin m // i.val<q} where
  toFun j := ⟨includeCol h j,j.isLt⟩
  invFun j := ⟨j.val.val,j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pad {m q : ℕ} (_h : q ≤ m) : (Fin m × Fin q → ℂ) →ₗ[ℂ] (Fin m × Fin m → ℂ) where
  toFun t := fun p => if b : p.2.val<q then t (p.1,⟨p.2.val,b⟩) else 0
  map_add' t u := by funext p; by_cases b : p.2.val<q <;> simp [b]
  map_smul' c t := by funext p; by_cases b : p.2.val<q <;> simp [b]

theorem pad_live {m q : ℕ} (h : q ≤ m) (t : Fin m × Fin q → ℂ) (r : Fin m) (j : Fin q) :
    pad h t (r,includeCol h j)=t (r,j) := by
  change (if b : j.val<q then t (r,⟨j.val,b⟩) else 0)=t (r,j)
  rw [dite_eq_left j.isLt]

noncomputable def value {m q : ℕ} (t : Fin m × Fin q → ℂ) : ℂ :=
  ∑ f : Fin q ↪ Fin m, ∏ i, (1+t (f i,i))

theorem pad_permanent {m q : ℕ} (h : q ≤ m) (t : Fin m × Fin q → ℂ) :
    PermanentMaximal.permAt (pad h t) = ((m-q).factorial:ℂ)*value t := by
  classical
  unfold PermanentMaximal.permAt Matrix.permanent value
  rw [← PermanentMaximal.Expansion.sum_perm_res (includeCol h) (fun f => ∏ i, (1+t (f i,i)))]
  apply Fintype.sum_congr
  intro σ
  let w := fun i : Fin m => 1+(pad h t) (σ i,i)
  change (∏ i, w i) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin m => i.val<q) w]
  have off (i : {i : Fin m // ¬i.val<q}) : w i.val = 1 := by simp [w,pad,i.property]
  simp_rw [off]
  rw [Finset.prod_const_one,mul_one,← Equiv.prod_comp (liveCols h)]
  apply Fintype.prod_congr
  intro j
  change 1+pad h t (σ (includeCol h j),includeCol h j)=1+t (σ (includeCol h j),j)
  rw [pad_live]

theorem mixed_pad {m q k : ℕ} (h : q ≤ m) (t : Fin m × Fin q → ℂ) :
    PermanentLevel.mixedSum (fun _ : Fin k => pad h t) = PermanentLevel.mixedSum (fun _ : Fin k => t) := by
  classical
  unfold PermanentLevel.mixedSum
  apply Fintype.sum_congr
  intro x
  let embed := fun d : Fin k ↪ Fin q => d.trans (includeCol h)
  have hinj : Function.Injective embed := by
    intro p d he
    exact Function.Embedding.ext (fun i => (includeCol h).injective (DFunLike.congr_fun he i))
  let term := fun a : Fin k ↪ Fin m => ∏ i, (pad h t) (x i,a i)
  have outside (a : Fin k ↪ Fin m) (ha : a ∉ univ.image embed) : term a = 0 := by
    obtain ⟨i,hi⟩ : ∃ i, ¬(a i).val<q := by
      by_contra! hall
      let z : Fin k ↪ Fin q := ⟨fun i => ⟨(a i).val,hall i⟩,
        fun i j he => a.injective (Fin.ext (congrArg (fun x : Fin q => x.val) he))⟩
      exact ha (mem_image.mpr ⟨z,mem_univ _,Function.Embedding.ext fun i => rfl⟩)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [pad,hi])
  change (∑ a, term a)=_
  calc
    _ = ∑ a ∈ univ.image embed, term a := (Finset.sum_subset (subset_univ _) (fun a _ ha => outside a ha)).symm
    _ = ∑ a : Fin k ↪ Fin q, term (embed a) := Finset.sum_image hinj.injOn
    _ = _ := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.prod_congr
      intro i
      exact pad_live h t (x i) (a i)

theorem mixed_of_translated {m q : ℕ} (h : q ≤ m) (L : Submodule ℂ (Fin m × Fin q → ℂ))
    (hL : ∀ T ∈ L, value T = value (0 : Fin m × Fin q → ℂ))
    {k : ℕ} (hk : 0<k) (hkm : k ≤ m) (T : Fin m × Fin q → ℂ) (hT : T∈L) :
    PermanentLevel.mixedSum (fun _ : Fin k => T) = 0 := by
  let W := L.map (pad h)
  have square0 : PermanentMaximal.permAt (0 : Fin m × Fin m → ℂ) = m.factorial := by
    simp [PermanentMaximal.permAt,Matrix.permanent,Fintype.card_perm]
  have square : ∀ U ∈ W, PermanentMaximal.permAt U=m.factorial := by
    rintro _ ⟨A,hA,rfl⟩
    rw [pad_permanent h A,hL A hA,← pad_permanent h (0 : Fin m × Fin q → ℂ),map_zero,square0]
  rw [← mixed_pad h]
  exact PermanentMaximal.translated_mixed_zero W square hk hkm _ (fun _ => ⟨T,hT,rfl⟩)

end RectangularPermanent

namespace DoubleTransitive
open Finset
open scoped Classical

private def evalFiberSwap {m q : ℕ} (j : Fin q) (a b : Fin m) :
    {f : Fin q ↪ Fin m // f j=a} ≃ {f : Fin q ↪ Fin m // f j=b} where
  toFun f := ⟨f.val.trans (Equiv.swap a b).toEmbedding,by simp [f.property]⟩
  invFun f := ⟨f.val.trans (Equiv.swap a b).toEmbedding,by simp [f.property]⟩
  left_inv f := Subtype.ext (Function.Embedding.ext fun i => Equiv.swap_apply_self a b (f.val i))
  right_inv f := Subtype.ext (Function.Embedding.ext fun i => Equiv.swap_apply_self a b (f.val i))

theorem column_level {m q : ℕ} (hm : 0 < m) (j : Fin q) (T : Fin m × Fin q → ℂ) (hT : T ∈ column j) :
    RectangularPermanent.value T=RectangularPermanent.value (0 : Fin m × Fin q → ℂ) := by
  classical
  have one (f : Fin q ↪ Fin m) : (∏ k, (1+T (f k,k)))=1+T (f j,j) := by
    rw [Finset.prod_eq_single j]
    · intro k _ h
      simp [hT.1 _ _ h]
    · simp
  let r : Fin m := ⟨0,hm⟩
  have size (i : Fin m) : Fintype.card {f : Fin q ↪ Fin m // f j=i} =
      Fintype.card {f : Fin q ↪ Fin m // f j=r} := Fintype.card_congr (evalFiberSwap j i r)
  have zero : (∑ f : Fin q ↪ Fin m, T (f j,j)) = 0 := by
    rw [← Fintype.sum_fiberwise' (fun f : Fin q ↪ Fin m => f j) (fun i => T (i,j))]
    simp only [Finset.sum_const,Finset.card_univ,size,nsmul_eq_mul,← Finset.mul_sum,hT.2,mul_zero]
  simp only [RectangularPermanent.value,one,Finset.sum_add_distrib,zero,add_zero,Pi.zero_apply,
    Finset.prod_const_one]

theorem column_stable {m q : ℕ} (G : Subgroup (Equiv.Perm (Fin m))) (j : Fin q) :
    Stable G (column j) := by
  intro T hT g _
  exact ⟨fun r l h => hT.1 (g r) l h,(Equiv.sum_comp g (fun r => T (r,j))).trans hT.2⟩

end DoubleTransitive

namespace DoubleTransitive
open Finset
open scoped Classical

noncomputable def sumForm (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i, LinearMap.proj i

theorem sumForm_apply {m : ℕ} (v : Fin m → ℂ) : sumForm m v = ∑ i, v i := by
  simp [sumForm,LinearMap.sum_apply]

noncomputable def columnEquiv {m q : ℕ} (j : Fin q) :
    column (m:=m) j ≃ₗ[ℂ] LinearMap.ker (sumForm m) where
  toFun t := ⟨fun r => t.val (r,j),by rw [LinearMap.mem_ker,sumForm_apply]; exact t.property.2⟩
  invFun v := ⟨fun p => if p.2=j then v.val p.1 else 0, by
    refine ⟨fun r k h => by simp [h],?_⟩
    simpa only [ite_true,reduceIte] using (sumForm_apply v.val).symm.trans v.property⟩
  left_inv t := by
    apply Subtype.ext
    funext x
    by_cases h : x.2=j
    · simp only [ite_eq_left h]
      exact congrArg t.val (Prod.ext rfl h.symm)
    · simp [h,t.property.1 x.1 x.2 h]
  right_inv v := by apply Subtype.ext; funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem column_dimension {m q : ℕ} (hm : 1 ≤ m) (j : Fin q) :
    Module.finrank ℂ (column (m:=m) j) = m-1 := by
  have hn : sumForm m ≠ 0 := by
    intro h
    have hv := LinearMap.congr_fun h (fun _ : Fin m => (1:ℂ))
    rw [sumForm_apply] at hv
    simp at hv
    omega
  have e := Module.Dual.finrank_ker_add_one_of_ne_zero hn
  rw [Module.finrank_pi,Fintype.card_fin] at e
  rw [(columnEquiv (m:=m) j).finrank_eq]
  omega

theorem classify_translated_permanent {m q : ℕ} (hm : 2 ≤ m) (hq : q ≤ m)
    (G : Subgroup (Equiv.Perm (Fin m))) (hG : Doubly G)
    (L : Submodule ℂ (Fin m × Fin q → ℂ)) (hs : Stable G L)
    (hL : ∀ T ∈ L, RectangularPermanent.value T=RectangularPermanent.value (0 : Fin m × Fin q → ℂ)) :
    L=⊥ ∨ ∃ j : Fin q, L=column j ∧ Module.finrank ℂ L=m-1 := by
  have hl : Level L := fun T hT k hk hkm =>
    RectangularPermanent.mixed_of_translated hq L hL hk (le_trans hkm (min_le_left _ _)) T hT
  rcases level_classification hm hq G hG L hl hs with e | ⟨j,e⟩
  · exact Or.inl e
  · subst L
    exact Or.inr ⟨j,rfl,column_dimension (by omega) j⟩

end DoubleTransitive
