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

namespace BoundedFrequency
open Finset PermanentLevel
open scoped Classical
noncomputable def elem {A : Type*} [Fintype A] (u : A → ℂ) (k : ℕ) : ℂ :=
  ∑ s ∈ (univ : Finset A).powersetCard k, ∏ i ∈ s, u i

theorem elem_reindex {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (u : B → ℂ) (k : ℕ) :
    elem (fun i => u (e i)) k = elem u k := by
  classical
  have full : (univ : Finset A).map e.toEmbedding = univ := by ext x; simp
  unfold elem
  conv_rhs => rw [← full,Finset.powersetCard_map,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _
  exact (Finset.prod_map s e.toEmbedding u).symm

noncomputable def injectiveMoment {A : Type*} [Fintype A] (u : A → ℂ) (k : ℕ) : ℂ :=
  ∑ f : Fin k ↪ A, ∏ i, u (f i)

theorem injectiveMoment_eq {A : Type*} [Fintype A] (u : A → ℂ) (k : ℕ) :
    injectiveMoment u k = (k.factorial:ℂ)*elem u k := by
  classical
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let a := fun i : Fin n => u (e i)
  have ins : injectiveMoment u k=injectiveMoment a k := by
    unfold injectiveMoment
    rw [← (Equiv.embeddingCongr (Equiv.refl (Fin k)) e).sum_comp]
    simp [a,Equiv.embeddingCongr_apply,Function.Embedding.congr]
  rw [ins,injectiveMoment,PermanentLevel.sum_embedding_prod,← elem_reindex e u k]
  congr 1
  exact (Finset.sum_subtype (univ.powersetCard k) (p:=fun s : Finset (Fin n) => s.card=k)
    (fun s => by simp [Finset.mem_powersetCard]) (fun s => ∏ i ∈ s, a i)).symm


end BoundedFrequency

namespace CoefficientSpace
open Finset
open scoped Classical

/-- A d-dimensional coordinate projection can prescribe d independent entries. -/
theorem interpolation {J : Type*} (d : ℕ) {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (E : W →ₗ[ℂ] (J → ℂ))
    (hE : Function.Injective E) (hd : d ≤ Module.finrank ℂ W) :
    ∃ f : Fin d → J, ∀ y : Fin d → ℂ, ∃ v : W, ∀ k, E v (f k)=y k := by
  induction d generalizing W with
  | zero => exact ⟨Fin.elim0,fun _ => ⟨0,fun k => Fin.elim0 k⟩⟩
  | succ d ih =>
    have dimpos : 0<Module.finrank ℂ W := by omega
    let : Nontrivial W := Module.nontrivial_of_finrank_pos dimpos
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    obtain ⟨j,hj⟩ : ∃ j, E w j ≠ 0 := by
      by_contra! h
      exact hw (hE (by ext i; simpa using h i))
    let e : W →ₗ[ℂ] ℂ := (LinearMap.proj j).comp E
    have he : e ≠ 0 := by
      intro h
      exact hj (LinearMap.congr_fun h w)
    have dim := Module.Dual.finrank_ker_add_one_of_ne_zero he
    let K := LinearMap.ker e
    obtain ⟨f,hf⟩ := ih (E.comp K.subtype) (hE.comp Subtype.val_injective) (by dsimp [K]; omega)
    refine ⟨Fin.cases j f,fun y => ?_⟩
    let base := (y 0 / E w j) • w
    have eb : E base j=y 0 := by simp [base,hj]
    obtain ⟨v,hv⟩ := hf (fun k => y k.succ - E base (f k))
    refine ⟨base + v.val,?_⟩
    intro k
    refine Fin.cases ?_ (fun h => ?_) k
    · have z : E v.val j=0 := v.property
      simp [map_add,eb,z]
    · have z : E v.val (f h)=y h.succ-E base (f h) := hv h
      simp [map_add,z]

end CoefficientSpace

namespace SupportWeights
open Finset
open scoped Classical

noncomputable def support {J : Type*} [Fintype J] (v : J → ℂ) : Finset J :=
  univ.filter fun j => v j ≠ 0

noncomputable def active {J : Type*} [Fintype J] (V : Submodule ℂ (J → ℂ)) : Finset J :=
  univ.filter fun j => ∃ v ∈ V, v j ≠ 0

theorem generic {J : Type*} [Fintype J] (V : Submodule ℂ (J → ℂ)) :
    ∃ v ∈ V, support v=active V := by
  classical
  obtain ⟨v,hv,all⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists V
    (fun j : ↥(active V) => (LinearMap.proj j.val : (J → ℂ) →ₗ[ℂ] ℂ))
    (fun j => by simpa [active] using j.property)
  refine ⟨v,hv,?_⟩
  ext j
  constructor
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,v,hv,(mem_filter.mp h).2⟩
  · intro h
    exact mem_filter.mpr ⟨mem_univ _,all ⟨j,h⟩⟩

def stage {J : Type*} {d : ℕ} (V : Submodule ℂ (J → ℂ)) (f : Fin d → J) (k : ℕ) :
    Submodule ℂ (J → ℂ) where
  carrier := {v | v ∈ V ∧ ∀ j : Fin d, k ≤ j.val → v (f j) = 0}
  zero_mem' := ⟨V.zero_mem, by simp⟩
  add_mem' := by rintro v w ⟨hv,h1⟩ ⟨hw,h2⟩; exact ⟨V.add_mem hv hw,fun j hj => by simp [h1 j hj,h2 j hj]⟩
  smul_mem' := by rintro c v ⟨hv,h1⟩; exact ⟨V.smul_mem c hv,fun j hj => by simp [h1 j hj]⟩

/-- A complex coordinate space realizes at least its dimension in distinct positive Hamming weights. -/
theorem dimension_le_weights {J : Type*} [Fintype J] (V : Submodule ℂ (J → ℂ))
    (A : Finset ℕ) (allowed : ∀ v ∈ V, v≠0 → (support v).card ∈ A) :
    Module.finrank ℂ V ≤ A.card := by
  classical
  let d := Module.finrank ℂ V
  obtain ⟨f,allows⟩ := CoefficientSpace.interpolation d V.subtype Subtype.val_injective (le_refl _)
  let U := stage V f
  have mono {k l : ℕ} (hkl : k ≤ l) : active (U k) ⊆ active (U l) := by
    intro j hj
    obtain ⟨_,v,hm,hn⟩ := mem_filter.mp hj
    refine mem_filter.mpr ⟨mem_univ _,v,?_,hn⟩
    exact ⟨hm.1,fun a ha => hm.2 a (hkl.trans ha)⟩
  have grow (j : Fin d) : (active (U j.val)).card < (active (U (j.val+1))).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_of_subset (mono (Nat.le_succ _)) |>.mpr ?_
    obtain ⟨v,hv⟩ := allows (fun i => if i=j then (1:ℂ) else 0)
    refine ⟨f j,?_,?_⟩
    · refine mem_filter.mpr ⟨mem_univ _,v,?_,?_⟩
      · exact ⟨v.property,fun i hi => by
          have ne : i ≠ j := by rintro rfl; omega
          simpa [ne] using hv i⟩
      · have hj : v.val (f j) = 1 := by simpa using hv j
        exact hj.trans_ne one_ne_zero
    · intro mem
      obtain ⟨_,w,hw,hn⟩ := mem_filter.mp mem
      exact hn (hw.2 j (le_refl _))
  let weight (j : Fin d) := (active (U (j.val+1))).card
  have increasing : StrictMono weight := by
    intro i j hij
    exact (Finset.card_le_card (mono (Nat.succ_le_of_lt hij))).trans_lt (grow j)
  have belongs (j : Fin d) : weight j ∈ A := by
    obtain ⟨v,hv,eq⟩ := generic (U (j.val+1))
    rw [show weight j = (support v).card by rw [eq]]
    apply allowed _ hv.1
    intro h
    have hn : 0<(active (U (j.val+1))).card := Nat.zero_lt_of_lt (grow j)
    simp [←eq,h,support] at hn
  simpa [d] using Fintype.card_le_of_injective (fun j : Fin d => (⟨weight j, belongs j⟩ : ↥A))
    (fun i j h => increasing.injective (congrArg Subtype.val h))

end SupportWeights


namespace SupportWeights
open Finset
open scoped Classical

theorem card_missing_two {m a b : ℕ} (ha : a ∈ Icc 1 m) (hb : b ∈ Icc 1 m) (hne : b≠a) :
    (((Icc 1 m).erase a).erase b).card+2=m := by
  have hba : b ∈ (Icc 1 m).erase a := mem_erase.mpr ⟨hne,hb⟩
  have hm : 1 ≤ a ∧ a ≤ m := mem_Icc.mp ha
  have hm' : 1 ≤ b ∧ b ≤ m := mem_Icc.mp hb
  rw [card_erase_of_mem hba,card_erase_of_mem ha,Nat.card_Icc]
  omega

theorem weight_positive {n : ℕ} {v : Fin n → ℂ} (h : v≠0) : 0<(support v).card := by
  classical
  apply Finset.card_pos.mpr
  by_contra! zero
  apply h
  funext i
  by_contra hi
  have hm : i ∈ support v := mem_filter.mpr ⟨mem_univ _,hi⟩
  simp [zero] at hm

theorem weight_le {n : ℕ} (v : Fin n → ℂ) : (support v).card ≤ n := by
  simpa using Finset.card_le_univ (support v)

/-- Every complex hyperplane of n coordinates realizes each support size strictly between 1 and n. -/
theorem intermediate_weight {n k : ℕ} (hk : 1<k) (hkn : k<n)
    (V : Submodule ℂ (Fin n → ℂ)) (hd : n-1 ≤ Module.finrank ℂ V) :
    ∃ v ∈ V, (support v).card=k := by
  classical
  by_contra nowhere
  push Not at nowhere
  have one : ∃ u ∈ V, (support u).card=1 := by
    by_contra absent
    push Not at absent
    let A := ((Icc 1 n).erase k).erase 1
    have rank := dimension_le_weights V A (by
      intro v hv hn
      exact mem_erase.mpr ⟨absent v hv,mem_erase.mpr ⟨nowhere v hv,mem_Icc.mpr ⟨weight_positive hn,weight_le v⟩⟩⟩)
    have cap : A.card+2=n := card_missing_two (mem_Icc.mpr (by omega)) (mem_Icc.mpr (by omega)) (by omega)
    omega
  obtain ⟨u,hu,h1⟩ := one
  obtain ⟨i,si⟩ := Finset.card_eq_one.mp h1
  have atI : u i ≠ 0 := (mem_filter.mp (show i ∈ support u by rw [si]; simp)).2
  have outside {j : Fin n} (hne : j≠i) : u j=0 := by
    by_contra h
    have hm : j ∈ support u := mem_filter.mpr ⟨mem_univ _,h⟩
    simp [si,hne] at hm
  let f : V →ₗ[ℂ] ℂ := (LinearMap.proj i).domRestrict V
  have fn : f≠0 := fun eq => atI (LinearMap.congr_fun eq (⟨u,hu⟩:V))
  let K := (LinearMap.ker f).map V.subtype
  have dim : Module.finrank ℂ K + 1 = Module.finrank ℂ V := by
    simpa [K,Submodule.finrank_map_subtype_eq] using Module.Dual.finrank_ker_add_one_of_ne_zero fn
  let A := ((Icc 1 (n-1)).erase k).erase (k-1)
  have rank := dimension_le_weights K A (by
    rintro v ⟨v',hv',rfl⟩ ne
    change (support v'.val).card ∈ A
    change v'.val ≠ 0 at ne
    have z : v'.val i=0 := hv'
    have notI : i ∉ support v'.val := by simp [support,z]
    have proper : support v'.val ⊂ (univ : Finset (Fin n)) :=
      (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr ⟨i,mem_univ _,notI⟩
    have lt : (support v'.val).card<n := by simpa using Finset.card_lt_card proper
    have eq : support (v'.val+u)=insert i (support v'.val) := by
      ext j
      by_cases same : j=i
      · subst j; simp [support,z,atI]
      · simp [support,same,outside same]
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨nowhere _ v'.property,mem_Icc.mpr ⟨weight_positive ne,by omega⟩⟩⟩
    intro off
    apply nowhere (v'.val+u) (V.add_mem v'.property hu)
    rw [eq,card_insert_of_notMem notI,off]
    omega)
  have cap : A.card+2=n-1 := card_missing_two (mem_Icc.mpr (by omega)) (mem_Icc.mpr (by omega)) (by omega)
  omega

end SupportWeights


namespace RankOneLevels
open Finset BoundedFrequency SupportWeights PermanentLevel
open scoped Classical

def outer {m q : ℕ} (u : Fin m → ℂ) : (Fin q → ℂ) →ₗ[ℂ] (Fin m × Fin q → ℂ) where
  toFun v := fun p => u p.1 * v p.2
  map_add' _ _ := by funext p; simp [mul_add]
  map_smul' _ _ := by funext p; simp [mul_left_comm]

theorem elementary_constraint {m q k : ℕ} (hq : q ≤ m) (u : Fin m → ℂ)
    (V : Submodule ℂ (Fin q → ℂ))
    (hl : ∀ v ∈ V, RectangularPermanent.value (outer u v)=RectangularPermanent.value (0 : Fin m × Fin q → ℂ))
    (hk : 0<k) (hkq : k≤q) (v : Fin q → ℂ) (hv : v ∈ V) : elem u k * elem v k = 0 := by
  let L := V.map (outer u)
  have level : ∀ T ∈ L, RectangularPermanent.value T=RectangularPermanent.value (0 : Fin m × Fin q → ℂ) := by
    rintro _ ⟨w,hw,rfl⟩
    exact hl w hw
  have h := RectangularPermanent.mixed_of_translated hq L level hk (hkq.trans hq)
      (outer u v) (show outer u v ∈ L from ⟨v,hv,rfl⟩)
  have factor : mixedSum (fun _ : Fin k => outer u v)=injectiveMoment u k * injectiveMoment v k := by
    simp only [mixedSum,injectiveMoment,outer,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.prod_mul_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [factor,injectiveMoment_eq,injectiveMoment_eq] at h
  have hn : (k.factorial : ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rcases mul_eq_zero.mp h with a | b
  · exact mul_eq_zero_of_left ((mul_eq_zero.mp a).resolve_left hn) _
  · exact mul_eq_zero_of_right _ ((mul_eq_zero.mp b).resolve_left hn)

theorem elem_weight {n : ℕ} (v : Fin n → ℂ) : elem v (support v).card ≠ 0 := by
  classical
  let S := support v
  change elem v S.card ≠ 0
  rw [elem,Finset.sum_eq_single S]
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => (mem_filter.mp hi).2)
  · intro t ht hne
    have hcard : t.card = S.card := (mem_powersetCard.mp ht).2
    have hn : ¬ t ⊆ S := fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge)
    obtain ⟨i,hi,hoff⟩ := Finset.not_subset.mp hn
    apply Finset.prod_eq_zero hi
    simpa [S,support] using hoff
  · simp [mem_powersetCard]

/-- Limit the dimension of an arbitrary common-factor family by the zero coefficients
of the elementary-symmetric polynomial of the fixed row profile. -/
theorem spectral_dimension {m q : ℕ} (hq : q ≤ m) (u : Fin m → ℂ)
    (V : Submodule ℂ (Fin q → ℂ))
    (hl : ∀ v ∈ V, RectangularPermanent.value (outer u v)=RectangularPermanent.value (0 : Fin m × Fin q → ℂ)) :
    Module.finrank ℂ V ≤ ((Icc 1 q).filter (fun k => elem u k=0)).card := by
  apply dimension_le_weights
  intro v hv hn
  have hp := weight_positive hn
  have hq' := weight_le v
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hq'⟩,?_⟩
  exact (mul_eq_zero.mp (elementary_constraint hq u V hl hp hq' v hv)).resolve_right (elem_weight v)

noncomputable def sumL (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ := ∑ i, LinearMap.proj i

theorem sumL_apply {n : ℕ} (v : Fin n → ℂ) : sumL n v = ∑ i, v i := by simp [sumL,LinearMap.sum_apply]

theorem elem_one {n : ℕ} (v : Fin n → ℂ) : elem v 1 = ∑ i, v i := by
  classical
  simp [elem,Finset.powersetCard_one]

theorem codim_one {n : ℕ} {V : Submodule ℂ (Fin n → ℂ)}
    (f : (Fin n → ℂ) →ₗ[ℂ] ℂ) (hf : f≠0) (h : V ≤ LinearMap.ker f)
    (rank : n-1 ≤ Module.finrank ℂ V) : V=LinearMap.ker f := by
  have d := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have dn : Module.finrank ℂ (Fin n → ℂ) = n := by simp
  exact Submodule.eq_of_le_of_finrank_le h (by omega)

/-- The two possible shapes of a largest square rank-one level family with fixed row profile. -/
theorem extremal_profiles {n : ℕ} (hn : 2≤n) (u : Fin n → ℂ) (hu : u≠0)
    (V : Submodule ℂ (Fin n → ℂ))
    (hl : ∀ v ∈ V, RectangularPermanent.value (outer u v)=RectangularPermanent.value (0 : Fin n × Fin n → ℂ))
    (rank : n-1 ≤ Module.finrank ℂ V) :
    ((support u).card=1 ∧ V=LinearMap.ker (sumL n)) ∨
    ((support u).card=n ∧ ∃ j : Fin n, V=LinearMap.ker (LinearMap.proj j) ∧
      ∀ k, 0<k → k<n → elem u k=0) := by
  classical
  let s := (support u).card
  have es : elem u s≠0 := elem_weight u
  have pos : 0<s := weight_positive hu
  have bound : s≤n := weight_le u
  have forbidden (v : Fin n → ℂ) (hv : v∈V) : (support v).card ≠ s := by
    intro eq
    have h := elementary_constraint (le_refl n) u V hl pos bound v hv
    exact (elem_weight v) (eq ▸ (mul_eq_zero.mp h).resolve_left es)
  by_cases one : s=1
  · left
    refine ⟨one,?_⟩
    have l : sumL n≠0 := by
      intro zero
      have H := LinearMap.congr_fun zero (fun _ : Fin n => (1:ℂ))
      simp [sumL_apply] at H
      omega
    apply codim_one _ l _ rank
    intro v hv
    change sumL n v=0
    rw [sumL_apply,←elem_one]
    have h := elementary_constraint (le_refl n) u V hl (k:=s) pos bound v hv
    simpa [one] using (mul_eq_zero.mp h).resolve_left es
  have full : s=n := by
    by_contra h
    obtain ⟨v,hv,eq⟩ := intermediate_weight (n:=n) (k:=s) (by omega) (by omega) V rank
    exact forbidden v hv eq
  right
  refine ⟨full,?_⟩
  obtain ⟨v,hv,gen⟩ := generic V
  have sub : active V ≠ univ := by
    intro eq
    apply forbidden v hv
    simp [gen,eq,full]
  obtain ⟨j,hj⟩ : ∃ j : Fin n, j ∉ active V := by
    by_contra! all
    exact sub (Finset.eq_univ_of_forall all)
  have pj : (LinearMap.proj j : (Fin n → ℂ) →ₗ[ℂ] ℂ) ≠ 0 := by
    intro eq
    have h := LinearMap.congr_fun eq (fun _ : Fin n => (1:ℂ))
    simp at h
  have equal : V=LinearMap.ker (LinearMap.proj j) := by
    apply codim_one _ pj _ rank
    intro w hw
    change w j=0
    by_contra h
    exact hj (mem_filter.mpr ⟨mem_univ _,w,hw,h⟩)
  refine ⟨j,equal,?_⟩
  intro k hk hkn
  have cap : k ≤ (univ.erase j).card := by simp; omega
  obtain ⟨S,subS,hS⟩ := Finset.exists_subset_card_eq cap
  let w : Fin n → ℂ := fun i => if i∈S then 1 else 0
  have wm : w∈V := by
    rw [equal]
    change w j=0
    simp [w,show j∉S from fun a => Finset.notMem_erase _ _ (subS a)]
  have ws : support w=S := by ext i; simp [support,w]
  have ew := elem_weight w
  rw [ws,hS] at ew
  exact (mul_eq_zero.mp (elementary_constraint (le_refl n) u V hl hk hkn.le w wm)).resolve_right ew

end RankOneLevels


namespace RankOneFactors
open Matrix

theorem minors {n : ℕ} {K : Type*} [Field K] (A : Matrix (Fin n) (Fin n) K) (h : A.rank≤1)
    (i r j c : Fin n) : A i j * A r c = A i c * A r j := by
  classical
  let B := A.submatrix ![i,r] ![j,c]
  have le : B.rank≤1 := (Matrix.rank_submatrix_le A _ _).trans h
  have zero : B.det=0 := by
    by_contra nz
    have two := Matrix.rank_of_det_ne_zero nz
    simp at two
    omega
  rw [Matrix.det_fin_two] at zero
  simpa [B,sub_eq_zero] using zero

/-- A linear space of matrices with vanishing two-by-two minors has a common
left factor or a common right factor. The nonzero hypothesis excludes the empty case. -/
theorem common {K I J : Type*} [Field K] (L : Submodule K (I × J → K))
    (nonzero : ∃ A ∈ L, ∃ i j, A (i,j)≠0)
    (minors : ∀ A ∈ L, ∀ i r j c, A (i,j)*A (r,c)=A (i,c)*A (r,j)) :
    (∃ u : I → K, u≠0 ∧ ∀ T ∈ L, ∃ w : J → K, T=fun p => u p.1*w p.2) ∨
    (∃ v : J → K, v≠0 ∧ ∀ T ∈ L, ∃ w : I → K, T=fun p => w p.1*v p.2) := by
  classical
  obtain ⟨A0,h0,i,j,nz⟩ := nonzero
  let A := (A0 (i,j))⁻¹ • A0
  have hm : A∈L := L.smul_mem _ h0
  have pivot : A (i,j)=1 := by simp [A,nz]
  let u := fun r => A (r,j)
  let v := fun c => A (i,c)
  have base (r : I) (c : J) : A (r,c)=u r*v c := by
    simpa [pivot,u,v,mul_comm] using minors A hm i r j c
  have linear (T : I × J → K) (hT : T∈L) (r : I) (c : J) :
      T (r,c) = u r*T (i,c) + v c*T (r,j) - u r*v c*T (i,j) := by
    have mixed := minors (A+T) (L.add_mem hm hT) i r j c
    simp only [Pi.add_apply,pivot,base r c] at mixed
    change (1+T (i,j))*(u r*v c+T (r,c))=(v c+T (i,c))*(u r+T (r,j)) at mixed
    linear_combination mixed - minors T hT i r j c
  let rd := fun (T : I × J → K) (r : I) => T (r,j)-u r*T (i,j)
  let cd := fun (T : I × J → K) (c : J) => T (i,c)-v c*T (i,j)
  have zero (T : I × J → K) (hT : T∈L) (r : I) (c : J) : rd T r*cd T c=0 := by
    dsimp only [rd,cd]
    linear_combination -(minors T hT i r j c) + T (i,j)*(linear T hT r c)
  have un : u≠0 := by
    intro eq
    have := congrFun eq i
    simp [u,pivot] at this
  have vn : v≠0 := by
    intro eq
    have := congrFun eq j
    simp [v,pivot] at this
  by_cases all : ∀ T∈L, ∀ r, rd T r=0
  · left
    refine ⟨u,un,?_⟩
    intro T hT
    refine ⟨fun c => T (i,c),?_⟩
    funext p
    have h : T (p.1,j)=u p.1*T (i,j) := sub_eq_zero.mp (all T hT p.1)
    rw [linear T hT p.1 p.2,h]
    ring
  · push Not at all
    obtain ⟨S,hS,r,hr⟩ := all
    right
    refine ⟨v,vn,?_⟩
    intro T hT
    have allC (c : J) : cd T c=0 := by
      by_contra no
      have s := (mul_eq_zero.mp (zero S hS r c)).resolve_left hr
      have t := (mul_eq_zero.mp (zero T hT r c)).resolve_right no
      have comb := zero (S+T) (L.add_mem hS hT) r c
      have left : rd (S+T) r=rd S r+rd T r := by simp [rd]; ring
      have right : cd (S+T) c=cd S c+cd T c := by simp [cd]; ring
      rw [left,right,s,t,zero_add,add_zero] at comb
      exact mul_ne_zero hr no comb
    refine ⟨fun i => T (i,j),?_⟩
    funext p
    have h : T (i,p.2)=v p.2*T (i,j) := sub_eq_zero.mp (allC p.2)
    rw [linear T hT p.1 p.2,h]
    ring

end RankOneFactors


namespace RankOneLevels
open Finset BoundedFrequency SupportWeights
open scoped Classical

abbrev Space (n : ℕ) := Fin n × Fin n → ℂ

def transposeL (n : ℕ) : Space n ≃ₗ[ℂ] Space n where
  toFun T := fun p => T (p.2,p.1)
  invFun T := fun p => T (p.2,p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem value_square {n : ℕ} (T : Space n) : RectangularPermanent.value T=PermanentMaximal.permAt T := by
  have H := RectangularPermanent.pad_permanent (le_refl n) T
  have id : RectangularPermanent.pad (le_refl n) T=T := by
    funext p
    simp [RectangularPermanent.pad]
  simpa [id] using H.symm

theorem value_transpose {n : ℕ} (T : Space n) : RectangularPermanent.value (transposeL n T) = RectangularPermanent.value T := by
  rw [value_square,value_square]
  exact Matrix.permanent_transpose (Matrix.of fun i j => 1+T (i,j))

theorem profile_bound {m : ℕ} (u : Fin m → ℂ) (V : Submodule ℂ (Fin m → ℂ))
    (hl : ∀ v ∈ V, RectangularPermanent.value (outer u v)=RectangularPermanent.value (0 : Space m)) (hu : u≠0) :
    Module.finrank ℂ V ≤ m-1 := by
  let s := (support u).card
  have hs : s ∈ Icc 1 m := mem_Icc.mpr ⟨weight_positive hu,weight_le u⟩
  have es : elem u s≠0 := elem_weight u
  have sub : ((Icc 1 m).filter fun k => elem u k=0) ⊆ (Icc 1 m).erase s := by
    intro k hk
    obtain ⟨hi,eq⟩ := mem_filter.mp hk
    exact mem_erase.mpr ⟨fun he => es (he ▸ eq),hi⟩
  exact (spectral_dimension (le_refl m) u V hl).trans (by
    simpa [card_erase_of_mem hs,Nat.card_Icc] using card_le_card sub)

noncomputable def extreme {n : ℕ} (L : Submodule ℂ (Space n)) : Prop :=
  ∃ (u : Fin n → ℂ) (V : Submodule ℂ (Fin n → ℂ)), u≠0 ∧ L=V.map (outer u) ∧
    (((support u).card=1 ∧ V=LinearMap.ker (sumL n)) ∨
     ((support u).card=n ∧ ∃ j : Fin n, V=LinearMap.ker (LinearMap.proj j) ∧
       ∀ k, 0<k → k<n → elem u k=0))

theorem of_common {n : ℕ} (hn : 2≤n) (L : Submodule ℂ (Space n))
    (hl : ∀ T∈L, RectangularPermanent.value T=RectangularPermanent.value (0 : Space n))
    (common : ∃ u : Fin n → ℂ, u≠0 ∧ ∀ T∈L, ∃ w : Fin n → ℂ, T=fun p => u p.1*w p.2) :
    Module.finrank ℂ L ≤ n-1 ∧ (n-1 ≤ Module.finrank ℂ L → extreme L) := by
  classical
  obtain ⟨u,hu,common⟩ := common
  let V := L.comap (outer u)
  have image : L=V.map (outer u) := by
    apply le_antisymm _ (Submodule.map_comap_le _ _)
    intro T hT
    obtain ⟨w,eq⟩ := common T hT
    refine ⟨w,?_,eq.symm⟩
    change (fun p => u p.1*w p.2) ∈ L
    rw [←eq]
    exact hT
  obtain ⟨i,hi⟩ : ∃ i, u i≠0 := by
    by_contra! h
    exact hu (funext h)
  have inj : Function.Injective (outer u : (Fin n → ℂ) →ₗ[ℂ] Space n) := by
    intro v w eq
    funext j
    exact mul_left_cancel₀ hi (congrFun eq (i,j))
  have rank : Module.finrank ℂ L=Module.finrank ℂ V := by
    rw [image]
    exact (Submodule.equivMapOfInjective (outer u) inj V).finrank_eq.symm
  have hv : ∀ v∈V, RectangularPermanent.value (outer u v)=RectangularPermanent.value (0 : Space n) :=
    fun v h => hl _ h
  rw [rank]
  exact ⟨profile_bound u V hv hu,
    fun h => ⟨u,V,hu,image,extremal_profiles hn u hu V hv h⟩⟩

/-- Complete maximal-dimension classification among all rank-at-most-one square matrix spaces. -/
theorem square_rank_one_classification {n : ℕ} (hn : 2≤n) (L : Submodule ℂ (Space n))
    (level : ∀ T∈L, PermanentMaximal.permAt T=(n.factorial:ℂ))
    (small : ∀ T∈L, (Matrix.of fun i j => T (i,j)).rank ≤ 1) :
    Module.finrank ℂ L ≤ n-1 ∧
      (n-1 ≤ Module.finrank ℂ L → extreme L ∨ extreme (L.map (transposeL n).toLinearMap)) := by
  classical
  have l : ∀ T∈L, RectangularPermanent.value T=RectangularPermanent.value (0 : Space n) := by
    intro T hT
    rw [value_square,value_square,level T hT,level 0 L.zero_mem]
  by_cases empty : L=⊥
  · have zero : Module.finrank ℂ L=0 := by rw [empty]; exact finrank_bot ℂ _
    rw [zero]
    exact ⟨Nat.zero_le _,fun h => False.elim (by omega)⟩
  have nonzero : ∃ A∈L, ∃ i j, A (i,j)≠0 := by
    by_contra! h
    apply empty
    apply le_antisymm _ bot_le
    intro T hT
    change T=0
    funext p
    exact h T hT p.1 p.2
  rcases RankOneFactors.common L nonzero (fun T hT => RankOneFactors.minors _ (small T hT)) with H | H
  · obtain ⟨b,c⟩ := of_common hn L l H
    exact ⟨b,fun h => Or.inl (c h)⟩
  · let P := transposeL n
    let L' := L.map P.toLinearMap
    have hL' : ∀ T∈L', RectangularPermanent.value T=RectangularPermanent.value (0 : Space n) := by
      rintro _ ⟨T,hT,rfl⟩
      exact (value_transpose T).trans (l T hT)
    obtain ⟨v,hv,all⟩ := H
    have common : ∃ u : Fin n → ℂ, u≠0 ∧ ∀ T∈L', ∃ w : Fin n → ℂ, T=fun p => u p.1*w p.2 := by
      refine ⟨v,hv,?_⟩
      rintro _ ⟨T,hT,rfl⟩
      obtain ⟨w,eq⟩ := all T hT
      refine ⟨w,?_⟩
      funext p
      simp [P,transposeL,eq,mul_comm]
    obtain ⟨b,c⟩ := of_common hn L' hL' common
    have rank : Module.finrank ℂ L'=Module.finrank ℂ L := P.finrank_map_eq L
    rw [rank] at b c
    exact ⟨b,fun h => Or.inr (c h)⟩

end RankOneLevels
