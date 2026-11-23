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


namespace PermanentMaximal
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

def elem (s : Finset α) (u : α → ℂ) (k : ℕ) : ℂ :=
  ∑ t ∈ s.powersetCard k, ∏ i ∈ t, u i

theorem elem_insert (s : Finset α) (r : α) (u : α → ℂ) (k : ℕ) (hr : r ∉ s) :
    elem (insert r s) u (k+1) = elem s u (k+1) + u r*elem s u k := by
  have off {a : Finset α} (ha : a ∈ s.powersetCard k) : r ∉ a :=
    fun h => hr ((mem_powersetCard.mp ha).1 h)
  have dis : Disjoint (s.powersetCard (k+1)) ((s.powersetCard k).image (insert r)) := by
    rw [disjoint_left]
    rintro a ha hb
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hb
    exact hr ((mem_powersetCard.mp ha).1 (mem_insert_self ..))
  have inj : Set.InjOn (insert r) (s.powersetCard k : Set (Finset α)) := by
    intro a ha b hb h
    have e := congrArg (fun t : Finset α => t.erase r) h
    simpa [erase_insert (off ha),erase_insert (off hb)] using e
  rw [elem,powersetCard_succ_insert hr,sum_union dis,Finset.sum_image inj]
  congr 1
  exact (sum_congr rfl fun _ h => prod_insert (off h)).trans (Finset.mul_sum ..).symm

theorem elem_omit [Fintype α] (u : α → ℂ) (r : α) (k : ℕ) (hk : k < Fintype.card α)
    (hf : ∀ d, 1 ≤ d → d < Fintype.card α → elem univ u d=0) :
    elem (univ.erase r) u k = (-u r)^k := by
  induction k with
  | zero => simp [elem]
  | succ k ih =>
    have he := elem_insert (univ.erase r) r u k (notMem_erase r univ)
    rw [insert_erase (mem_univ _),hf _ (by omega) hk,ih (by omega)] at he
    rw [pow_succ]
    linear_combination -he

theorem elem_change_zero (s : Finset α) (u : α → ℂ) (r : α) (k : ℕ) :
    elem s (fun i => if i=r then 0 else u i) k = elem (s.erase r) u k := by
  unfold elem
  have sub : (s.erase r).powersetCard k ⊆ s.powersetCard k := fun t ht =>
    mem_powersetCard.mpr ⟨(mem_powersetCard.mp ht).1.trans (erase_subset ..),(mem_powersetCard.mp ht).2⟩
  calc
    _ = ∑ t ∈ (s.erase r).powersetCard k, ∏ i ∈ t, (if i=r then 0 else u i) := by
      symm
      apply Finset.sum_subset sub
      intro t ht ho
      have hr : r ∈ t := by
        by_contra h
        apply ho
        have hh := mem_powersetCard.mp ht
        exact mem_powersetCard.mpr ⟨fun i hi => mem_erase.mpr ⟨fun h' => h (h' ▸ hi),hh.1 hi⟩,hh.2⟩
      exact Finset.prod_eq_zero hr (ite_eq_left rfl)
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      apply prod_congr rfl
      intro i hi
      exact ite_eq_right (mem_erase.mp ((mem_powersetCard.mp ht).1 hi)).1

end PermanentMaximal


namespace PermanentMaximal
open Finset
open scoped Classical

theorem vanish_on_subsets {α : Type*} [DecidableEq α] (s : Finset α) (m : ℕ)
    (hm : 1 ≤ m) (hlt : m < s.card) (f : α → ℂ)
    (hyp : ∀ t ⊆ s, t.card=m → ∑ i ∈ t, f i = 0) :
    ∀ i ∈ s, f i=0 := by
  have eq (i j : α) (hi : i ∈ s) (hj : j ∈ s) : f i = f j := by
    by_cases hij : i = j
    · rw [hij]
    have hj' : j ∈ s.erase i := mem_erase.mpr ⟨Ne.symm hij,hj⟩
    have hsize : m-1 ≤ ((s.erase i).erase j).card := by
      rw [card_erase_of_mem hj',card_erase_of_mem hi]
      omega
    obtain ⟨a,ha,hc⟩ := exists_subset_card_eq hsize
    have hsub : a ⊆ s := fun k hk => mem_of_mem_erase (mem_of_mem_erase (ha hk))
    have hni : i ∉ a := fun h => notMem_erase _ _ (mem_of_mem_erase (ha h))
    have hnj : j ∉ a := fun h => notMem_erase _ _ (ha h)
    have ei := hyp (insert i a) (insert_subset hi hsub) (by rw [card_insert_of_notMem hni,hc]; omega)
    have ej := hyp (insert j a) (insert_subset hj hsub) (by rw [card_insert_of_notMem hnj,hc]; omega)
    rw [sum_insert hni] at ei
    rw [sum_insert hnj] at ej
    linear_combination ei-ej
  intro i hi
  obtain ⟨a,ha,hc⟩ := exists_subset_card_eq hlt.le
  have e := hyp a ha hc
  have rep : (∑ j ∈ a, f j) = (m:ℂ)*f i := by
    calc
      _ = ∑ j ∈ a, f i := Finset.sum_congr rfl (fun j hj => eq j i (ha hj) hi)
      _ = _ := by simp [hc,nsmul_eq_mul]
  rw [rep] at e
  exact (mul_eq_zero.mp e).resolve_left (Nat.cast_ne_zero.mpr (by omega))

theorem two_modes {n : ℕ} (hn : 2 ≤ n) (u w : Fin n → ℂ)
    (hu : Function.Injective u) (hroot : ∀ i, u i^n = 1)
    (hp : ∀ k, 1 ≤ k → k < n → ∑ r, u r^k = 0)
    (hw : ∀ k, 1 ≤ k → k+1 < n → ∑ r, w r*u r^k = 0) :
    ∃ c a : ℂ, ∀ i, w i = c + u i*a := by
  let c := (∑ r, w r) / n
  let a := (∑ r, w r*u r^(n-1)) / n
  let v := fun r => w r - c - a*u r
  have hnc : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h0 : ∀ k : Fin n, ∑ r, v r * u r^k.val = 0 := by
    intro k
    have split (r : Fin n) : v r*u r^k.val =
        w r*u r^k.val - c*u r^k.val - a*u r^(k.val+1) := by
      dsimp [v]
      rw [pow_succ]
      ring
    simp_rw [split]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
    by_cases hz : k.val=0
    · have h1 : ∑ r, u r = 0 := by simpa only [pow_one] using hp 1 (by omega) (by omega)
      simp [hz,h1,c,hnc]
    by_cases he : k.val+1=n
    · rw [hp _ (by omega) k.isLt,he]
      have hlast : k.val=n-1 := by omega
      simp [hlast,hroot,a,hnc]
    · rw [hw _ (by omega) (by omega),hp _ (by omega) k.isLt,hp _ (by omega) (by omega)]
      ring
  have zero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hu h0
  refine ⟨c,a,fun i => ?_⟩
  have hi : v i = 0 := congrFun zero i
  dsimp [v] at hi
  linear_combination hi

end PermanentMaximal

namespace PermanentMaximal
open Finset Polynomial
open scoped Classical

def roots {n : ℕ} (ζ : ℂ) (i : Fin n) := ζ^i.val

theorem roots_period {n : ℕ} {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) (i : Fin n) :
    roots ζ i ^ n = 1 := by
  rw [roots,← pow_mul,Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]

theorem roots_power_sum {n : ℕ} {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k<n) : ∑ i : Fin n, roots ζ i ^ k = 0 := by
  have hn := hz.pow_ne_one_of_pos_of_lt (by omega : k≠0) hkn
  have hpow : (ζ^k)^n = 1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]
  have he := geom_sum_mul (ζ^k) n
  rw [hpow,sub_self] at he
  have hsum := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hn)
  calc
    _ = ∑ i : Fin n, (ζ^k)^i.val := by
      apply Fintype.sum_congr
      intro i
      rw [roots,← pow_mul,← pow_mul,Nat.mul_comm]
    _ = _ := (Fin.sum_univ_eq_sum_range _ n).trans hsum

theorem roots_elem {n : ℕ} {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k<n) : elem (univ : Finset (Fin n)) (roots ζ) k = 0 := by
  have hp := X_pow_sub_C_eq_prod hz (by omega : 0<n) (rfl : (-1:ℂ)^n=(-1:ℂ)^n)
  have hp' : (∏ i : Fin n, (X+C (roots ζ i))) = X^n-C ((-1:ℂ)^n) := by
    rw [hp]
    simpa [roots] using Fin.prod_univ_eq_prod_range (fun k => X+C (ζ^k)) n
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (n-k)) hp'
  rw [Finset.prod_X_add_C_coeff] at hcoeff
  · have hs : n-(n-k)=k := by omega
    simp only [card_univ,Fintype.card_fin,hs,Polynomial.coeff_sub,Polynomial.coeff_X_pow,
      Polynomial.coeff_C,ite_eq_right (show n-k≠0 by omega),
      ite_eq_right (show n-k≠n by omega),sub_zero] at hcoeff
    exact hcoeff
  · simp

end PermanentMaximal

namespace PermanentMaximal
open Finset
open scoped Classical

private def uncons (A : Type*) (k : ℕ) :
    (Fin (k+1) ↪ A) ≃ (Σ e : Fin k ↪ A, {a : A // a ∉ Set.range e}) where
  toFun f := ⟨Fin.Embedding.tail f, f 0, by
    rintro ⟨j,hj⟩
    exact Fin.succ_ne_zero j (f.injective hj)⟩
  invFun p := Fin.Embedding.cons p.1 p.2.property
  left_inv f := by
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by rcases p with ⟨e,r,hr⟩; rfl

private theorem sum_off {A : Type*} [Fintype A] [DecidableEq A] {k : ℕ} (e : Fin k ↪ A) (f : A → ℂ) :
    (∑ a : {a : A // a ∉ Set.range e}, f a) = ∑ a : A, if a ∈ Set.range e then 0 else f a := by
  classical
  calc
    _ = ∑ a ∈ univ.filter (fun a => a ∉ Set.range e), f a := (Finset.sum_subtype _ (by simp) f).symm
    _ = _ := by simp only [Finset.sum_filter,ite_not]

def special {n k : ℕ} (u : Fin n → ℂ) (T : Fin n × Fin n → ℂ) (v : Fin k ↪ Fin n) :
    Fin (k+1) → Fin n × Fin n → ℂ :=
  Fin.cons T (fun i p => if p.2=v i then u p.1 else 0)

private theorem tails {n k : ℕ} (u : Fin n → ℂ) (e d v : Fin k ↪ Fin n) :
    (∏ i, if d i=v i then u (e i) else 0) = if d=v then ∏ i, u (e i) else 0 := by
  classical
  by_cases h : d=v
  · simp [h]
  rw [ite_eq_right h]
  obtain ⟨i,hi⟩ : ∃ i, d i ≠ v i := by
    by_contra! he
    exact h (Function.Embedding.ext he)
  exact Finset.prod_eq_zero (mem_univ i) (ite_eq_right hi)

noncomputable def avoid {n : ℕ} (k : ℕ) (u : Fin n → ℂ) (r : Fin n) : ℂ := by
  classical
  exact ∑ e : Fin k ↪ Fin n, if r ∈ Set.range e then 0 else ∏ i, u (e i)

theorem mixed_special {n k : ℕ} (u : Fin n → ℂ) (T : Fin n × Fin n → ℂ)
    (v : Fin k ↪ Fin n) :
    PermanentLevel.mixedSum (special u T v) =
    ∑ j : {j : Fin n // j ∉ Set.range v}, ∑ r : Fin n, T (r,j.val) * avoid k u r := by
  classical
  unfold PermanentLevel.mixedSum
  rw [← (uncons (Fin n) k).symm.sum_comp,Fintype.sum_sigma]
  have col (e : Fin k ↪ Fin n) (r : {r : Fin n // r ∉ Set.range e}) :
      (∑ y : Fin (k+1) ↪ Fin n, ∏ i, special u T v i (((uncons (Fin n) k).symm ⟨e,r⟩) i,y i)) =
      ∑ j : {j : Fin n // j ∉ Set.range v}, T (r.val,j.val) * ∏ i, u (e i) := by
    rw [← (uncons (Fin n) k).symm.sum_comp,Fintype.sum_sigma]
    simp only [uncons,Equiv.coe_fn_symm_mk,Fin.prod_univ_succ,special,Fin.cons_zero,
      Fin.cons_succ,Fin.Embedding.coe_cons]
    simp_rw [tails u e _ v]
    rw [Finset.sum_eq_single v]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  simp_rw [col]
  conv_lhs => enter [2,e]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro j
  have convert_off (e : Fin k ↪ Fin n) :
      (∑ r : {r : Fin n // r ∉ Set.range e}, T (r.val,j.val) * ∏ i, u (e i)) =
      ∑ r : Fin n, if r ∈ Set.range e then 0 else T (r,j.val) * ∏ i, u (e i) :=
    sum_off e (fun r => T (r,j.val) * ∏ i, u (e i))
  calc
    _ = ∑ e : Fin k ↪ Fin n, ∑ r : Fin n, if r ∈ Set.range e then 0 else T (r,j.val) * ∏ i, u (e i) :=
      Fintype.sum_congr _ _ convert_off
    _ = _ := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro r
      unfold avoid
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro e
      split_ifs <;> simp

theorem avoid_eq_elem {n k : ℕ} (u : Fin n → ℂ) (r : Fin n) :
    avoid k u r = (k.factorial:ℂ) * elem (univ.erase r) u k := by
  classical
  let w := fun i => if i=r then 0 else u i
  have term (e : Fin k ↪ Fin n) :
      (if r ∈ Set.range e then 0 else ∏ i, u (e i)) = ∏ i, w (e i) := by
    by_cases h : r ∈ Set.range e
    · rw [ite_eq_left h]
      obtain ⟨i,hi⟩ := h
      exact (Finset.prod_eq_zero (mem_univ i) (by simp [w,hi])).symm
    · rw [ite_eq_right h]
      exact Finset.prod_congr rfl (fun i _ => (ite_eq_right fun hi => h ⟨i,hi⟩).symm)
  unfold avoid
  simp_rw [term]
  rw [PermanentLevel.sum_embedding_prod,← elem_change_zero univ u r k]
  congr 1
  exact (Finset.sum_subtype (univ.powersetCard k) (p := fun s : Finset (Fin n) => s.card=k)
    (fun s => by simp [Finset.mem_powersetCard]) (fun s => ∏ i ∈ s, w i)).symm

end PermanentMaximal

namespace PermanentMaximal
open Finset
open scoped Classical

def columnFamily {n : ℕ} (u : Fin n → ℂ) (a : Fin n → ℂ) (x : Fin n × Fin n) : ℂ :=
  u x.1 * a x.2

theorem column_forced {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, permAt t=n.factorial) (u : Fin n → ℂ) (hu : ∀ i, u i ≠ 0)
    (b : Fin n) (hP : ∀ a : Fin n → ℂ, a b=0 → columnFamily u a ∈ L)
    (T : Fin n × Fin n → ℂ) (hT : T ∈ L) (r : Fin n) : T (r,b)=0 := by
  classical
  by_contra hn
  let c := -(T (r,b))⁻¹
  let a := fun j : Fin n => if j=b then 0 else -(1+c*T (r,j))/u r
  have h := hL _ (L.add_mem (L.smul_mem c hT) (hP a (by simp [a])))
  have row (j : Fin n) : 1 + (c • T + columnFamily u a) (r,j)=0 := by
    change 1+(c*T (r,j)+u r*a j)=0
    by_cases he : j=b
    · subst j; simp [a,c,hn]
    · simp only [a,ite_eq_right he]
      field_simp [hu r]
      ring
  have hz : permAt (c • T + columnFamily u a) = 0 := by
    unfold permAt Matrix.permanent
    apply Finset.sum_eq_zero
    intro σ _
    apply Finset.prod_eq_zero (mem_univ (σ.symm r))
    simpa only [Matrix.of_apply,Equiv.apply_symm_apply] using row (σ.symm r)
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) : (n.factorial:ℂ)≠0) (h.symm.trans hz)

theorem repeated_zero {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, permAt t=n.factorial) (a : Fin n → ℂ)
    (ha : (fun x : Fin n × Fin n => a x.2) ∈ L) (j : Fin n) : a j=0 := by
  by_contra h
  let c := -(a j)⁻¹
  let W := fun x : Fin n × Fin n => a x.2
  have hp := hL (c • W) (L.smul_mem c ha)
  have hz : permAt (c • W) = 0 := by
    unfold permAt Matrix.permanent
    apply Finset.sum_eq_zero
    intro σ _
    apply Finset.prod_eq_zero (mem_univ j)
    simp [W,c,h]
  exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) : (n.factorial:ℂ)≠0) (hp.symm.trans hz)

theorem column_moments {n : ℕ} (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, permAt t=n.factorial) (u : Fin n → ℂ)
    (hu : ∀ i, u i≠0) (helem : ∀ k, 1≤k → k<n → elem univ u k=0)
    (b : Fin n) (hP : ∀ a : Fin n → ℂ, a b=0 → columnFamily u a ∈ L)
    (T : Fin n × Fin n → ℂ) (hT : T ∈ L) {k : ℕ} (hp : 1≤k) (hk : k+1<n)
    (j : Fin n) : ∑ r, T (r,j)*u r^k = 0 := by
  classical
  let D := (univ : Finset (Fin n)).erase b
  let m := n-1-k
  let B := fun j : Fin n => ∑ r, T (r,j)*u r^k
  have hb : B b=0 := by simp [B,column_forced L hL u hu b hP T hT]
  by_cases hj : j=b
  · simpa [hj] using hb
  have hcard : D.card=n-1 := by simp [D]
  apply vanish_on_subsets D m (by dsimp [m]; omega) (by dsimp [m]; omega) B _ j (by simp [D,hj])
  intro U hU hc
  let S := D \ U
  have hs : S.card=k := by change (D \ U).card=k; rw [card_sdiff_of_subset hU,hcard,hc]; dsimp [m]; omega
  let f := (S.orderEmbOfFin hs).toEmbedding
  have rangef : Set.range f = (S : Set (Fin n)) := Finset.range_orderEmbOfFin _ _
  have hfb (i : Fin k) : f i ≠ b := by
    have hm : f i ∈ S := by change f i ∈ (S : Set (Fin n)); rw [← rangef]; exact ⟨i,rfl⟩
    exact (mem_erase.mp (mem_sdiff.mp hm).1).1
  have hx (i : Fin (k+1)) : special u T f i ∈ L := by
    refine Fin.cases hT (fun q => ?_) i
    let a := fun c : Fin n => if c=f q then (1:ℂ) else 0
    have he : special u T f q.succ = columnFamily u a := by
      funext z
      simp [special,columnFamily,a,mul_ite]
    rw [he]
    exact hP a (by simp [a,(hfb q).symm])
  have hmixed := translated_mixed_zero L hL (by omega : 0<k+1) (by omega) _ hx
  rw [mixed_special] at hmixed
  have hav (r : Fin n) : avoid k u r = ((k.factorial:ℂ)*(-1)^k) * u r^k := by
    rw [avoid_eq_elem,elem_omit u r k (by simp;omega) (by simpa using helem)]
    rw [← neg_one_mul (u r),mul_pow]; ring
  let K : ℂ := k.factorial * (-1)^k
  have hf (j : Fin n) : (∑ r, T (r,j) * avoid k u r) = K*B j := by
    change _ = K * ∑ r, T (r,j)*u r^k
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro r
    rw [hav]; dsimp [K]; ring
  simp_rw [hf,← Finset.mul_sum] at hmixed
  have sum0 := (mul_eq_zero.mp hmixed).resolve_left (show K≠0 by exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))
  have bout : b ∉ U := fun hb => notMem_erase _ _ (hU hb)
  have mem (i : Fin n) : i ∈ insert b U ↔ i ∉ Set.range f := by
    rw [rangef]
    simp only [S,D,mem_insert,Finset.mem_coe,mem_sdiff,mem_erase,mem_univ,and_true]
    tauto
  have eq : (∑ i ∈ insert b U, B i) = ∑ i : {i : Fin n // i ∉ Set.range f}, B i.val :=
    Finset.sum_subtype (insert b U) mem B
  rw [sum_insert bout,hb,zero_add] at eq
  exact eq.trans sum0

end PermanentMaximal

namespace PermanentMaximal
open Finset
open scoped Classical

theorem rank_one_moment {n k : ℕ} (u a : Fin n → ℂ) :
    Expansion.Mk n k (columnFamily u a) = (k.factorial:ℂ)*elem univ u k*elem univ a k := by
  classical
  have one (w : Fin n → ℂ) : (∑ e : Fin k ↪ Fin n, ∏ i, w (e i)) = (k.factorial:ℂ)*elem univ w k := by
    rw [PermanentLevel.sum_embedding_prod]
    congr 1
    exact (Finset.sum_subtype (univ.powersetCard k) (p := fun s : Finset (Fin n) => s.card=k)
      (fun s => by simp [Finset.mem_powersetCard]) (fun s => ∏ i ∈ s, w i)).symm
  have ht := PermanentLevel.mixedSum_subpermanent (k:=k) (columnFamily u a)
  rw [PermanentLevel.subsums] at ht
  change _ = (k.factorial:ℂ)*Expansion.Mk n k (columnFamily u a) at ht
  simp only [PermanentLevel.mixedSum,columnFamily,Finset.prod_mul_distrib,← Finset.mul_sum,← Finset.sum_mul] at ht
  rw [one,one] at ht
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k) : (k.factorial:ℂ)≠0)
  linear_combination -ht

theorem roots_level {n : ℕ} {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) (b : Fin n) (a : Fin n → ℂ)
    (ha : a b=0) : permAt (columnFamily (roots ζ) a) = n.factorial := by
  classical
  rw [permAt,Expansion.minc_Mk,Finset.sum_eq_single 0]
  · simp [Expansion.Mk_zero]
  · intro k hk hn
    have hl : k≤n := by simpa using hk
    rw [rank_one_moment]
    by_cases he : k=n
    · subst k
      have e : elem univ a n = 0 := by
        have hc : (univ : Finset (Fin n)).card = n := by simp
        have he : (univ : Finset (Fin n)).powersetCard n = {univ} := by simpa only [hc] using Finset.powersetCard_self (univ : Finset (Fin n))
        rw [elem,he,Finset.sum_singleton]
        exact Finset.prod_eq_zero (mem_univ b) ha
      simp [e]
    · rw [roots_elem hz (by omega) (by omega)]
      ring
  · simp

theorem roots_maximal {n : ℕ} (hn : 2≤n) {ζ : ℂ} (hz : IsPrimitiveRoot ζ n)
    (b : Fin n) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ T ∈ L, permAt T=n.factorial)
    (hP : ∀ a : Fin n → ℂ, a b=0 → columnFamily (roots ζ) a ∈ L)
    (T : Fin n × Fin n → ℂ) (hT : T ∈ L) :
    ∃ a : Fin n → ℂ, a b=0 ∧ T = columnFamily (roots ζ) a := by
  let u : Fin n → ℂ := roots ζ
  have hu (i : Fin n) : u i ≠ 0 := by
    exact pow_ne_zero _ ((hz.isUnit (by omega)).ne_zero)
  have hi : Function.Injective u := fun i j h => Fin.ext (hz.pow_inj i.isLt j.isLt h)
  have split (j : Fin n) : ∃ c a : ℂ, ∀ i, T (i,j)=c+u i*a :=
    two_modes hn u (fun r => T (r,j)) hi (roots_period hz) (fun _ => roots_power_sum hz)
      (fun _ hp hk => column_moments L hL u hu (fun _ => roots_elem hz) b hP _ hT hp hk j)
  choose c a h using split
  let v := fun j => if j=b then 0 else a j
  let w := fun j => if j=b then 0 else c j
  have hv : v b=0 := by simp [v]
  have he : T - columnFamily u v = (fun x => w x.2) := by
    funext x
    change T (x.1,x.2) - u x.1*v x.2 = w x.2
    by_cases hx : x.2=b
    · rw [hx,column_forced L hL u hu b hP _ hT]
      simp [v,w]
    · simp [v,w,hx,h x.2 x.1]
  have hm := L.sub_mem hT (hP v hv)
  rw [he] at hm
  refine ⟨v,hv,?_⟩
  have hzero : (fun x : Fin n × Fin n => w x.2) = 0 := funext fun x => repeated_zero L hL w hm x.2
  exact sub_eq_zero.mp (he.trans hzero)

end PermanentMaximal

namespace PermanentMaximal
open Finset
open scoped Classical

noncomputable def familyMap {n : ℕ} (u : Fin n → ℂ) (b : Fin n) :
    ({j : Fin n // j≠b} → ℂ) →ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun a := fun x => if h : x.2=b then 0 else u x.1*a ⟨x.2,h⟩
  map_add' a c := by funext x; by_cases h : x.2=b <;> simp [h,mul_add]
  map_smul' c a := by funext x; by_cases h : x.2=b <;> simp [h,mul_left_comm]

theorem mem_family_iff {n : ℕ} (u : Fin n → ℂ) (b : Fin n) (T : Fin n × Fin n → ℂ) :
    T ∈ LinearMap.range (familyMap u b) ↔ ∃ a : Fin n → ℂ, a b=0 ∧ T=columnFamily u a := by
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨fun i => if h : i=b then 0 else a ⟨i,h⟩,by simp,?_⟩
    funext x
    by_cases h : x.2=b <;> simp [familyMap,columnFamily,h]
  · rintro ⟨a,ha,rfl⟩
    refine ⟨fun i => a i.val,?_⟩
    funext x
    by_cases h : x.2=b <;> simp [familyMap,columnFamily,h,ha]

theorem family_dimension {n : ℕ} (u : Fin n → ℂ) (b : Fin n) (hu : u b≠0) :
    Module.finrank ℂ (LinearMap.range (familyMap u b))=n-1 := by
  have hinj : Function.Injective (familyMap u b) := by
    intro a c h
    funext i
    have he := congrFun h (b,i.val)
    simpa [familyMap,i.property,hu] using he
  rw [LinearMap.finrank_range_of_inj hinj,Module.finrank_pi]
  simp

theorem maximal_root_family {n : ℕ} (hn : 2≤n) {ζ : ℂ} (hz : IsPrimitiveRoot ζ n) (b : Fin n) :
    let P := LinearMap.range (familyMap (roots ζ) b)
    Module.finrank ℂ P=n-1 ∧ (∀ T ∈ P, permAt T=n.factorial) ∧
    ∀ L : Submodule ℂ (Fin n × Fin n → ℂ), P≤L → (∀ T ∈ L, permAt T=n.factorial) → L=P := by
  dsimp only
  constructor
  · exact family_dimension _ _ (pow_ne_zero _ ((hz.isUnit (by omega)).ne_zero))
  constructor
  · intro T hT
    obtain ⟨a,ha,rfl⟩ := (mem_family_iff _ _ _).mp hT
    exact roots_level hz b a ha
  · intro L hP hL
    apply le_antisymm _ hP
    intro T hT
    apply (mem_family_iff _ _ _).mpr
    apply roots_maximal hn hz b L hL _ T hT
    exact fun a ha => hP ((mem_family_iff _ _ _).mpr ⟨a,ha,rfl⟩)

end PermanentMaximal
