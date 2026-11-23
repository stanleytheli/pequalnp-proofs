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




namespace PermanentLevel

open Finset
open scoped Classical

variable {G J : Type*} [AddCommGroup G] [Fintype G]

private noncomputable def component (t : G × J → ℂ) (ψ : AddChar G ℂ) (x : G × J) : ℂ :=
  ∑ h, ψ (-h) * t (x.1+h,x.2)

private theorem component_mem (L : Submodule ℂ (G × J → ℂ)) (t : G × J → ℂ)
    (hshift : ∀ a : G, (fun x : G × J => t (x.1+a,x.2)) ∈ L) (ψ : AddChar G ℂ) :
    component t ψ ∈ L := by
  have he : component t ψ = ∑ h : G, ψ (-h) • (fun x : G × J => t (x.1+h,x.2)) := by
    ext x
    simp [component,Finset.sum_apply]
  rw [he]
  exact L.sum_mem fun h _ => L.smul_mem _ (hshift h)

private theorem component_separates (t : G × J → ℂ) (ψ : AddChar G ℂ) (g : G) (j : J) :
    component t ψ (g,j) = ψ g * component t ψ (0,j) := by
  simp only [component,zero_add,Finset.mul_sum]
  calc
    _ = ∑ h : G, ψ g * (ψ (-(g+h)) * t (g+h,j)) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [← mul_assoc, ← ψ.map_add_eq_mul]
      abel_nf
    _ = _ := Equiv.sum_comp (Equiv.addLeft g) (fun h : G => ψ g * (ψ (-h)*t (h,j)))

private theorem component_sum (t : G × J → ℂ) (x : G × J) :
    (∑ ψ : AddChar G ℂ, component t ψ x) = (Fintype.card G : ℂ) * t x := by
  simp only [component]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,AddChar.sum_apply_eq_ite]
  simp

theorem row_character_decomposition (L : Submodule ℂ (G × J → ℂ)) (t : G × J → ℂ)
    (hshift : ∀ a : G, (fun x : G × J => t (x.1+a,x.2)) ∈ L) :
    ∃ u : AddChar G ℂ → J → ℂ,
      (∀ ψ : AddChar G ℂ, (fun x : G × J => ψ x.1 * u ψ x.2) ∈ L) ∧
      ∀ x : G × J, t x = ∑ ψ : AddChar G ℂ, ψ x.1 * u ψ x.2 := by
  let q : ℂ := Fintype.card G
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun ψ j => q⁻¹ * component t ψ (0,j),?_,?_⟩
  · intro ψ
    have he : (fun x : G × J => ψ x.1 * (q⁻¹ * component t ψ (0,x.2))) =
        q⁻¹ • component t ψ := by
      funext x
      rw [Pi.smul_apply,smul_eq_mul,component_separates t ψ x.1 x.2]
      ring
    rw [he]
    exact L.smul_mem _ (component_mem L t hshift ψ)
  · intro x
    calc
      t x = q⁻¹ * (q * t x) := by field_simp
      _ = q⁻¹ * ∑ ψ : AddChar G ℂ, component t ψ x := by rw [component_sum]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ψ _
        rw [component_separates t ψ x.1 x.2]
        ring

end PermanentLevel



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

noncomputable def bandMap {G : Type*} [AddCommGroup G] {q : ℕ} (χ : AddChar G ℂ) :
    (Fin q → ℂ) →ₗ[ℂ] (G × Fin q → ℂ) where
  toFun v := fun p => χ p.1*v p.2
  map_add' v w := by funext p; simp [mul_add]
  map_smul' c v := by funext p; simp [mul_left_comm]


end BoundedFrequency

namespace BoundedFrequency
open Finset PermanentLevel
open scoped Classical

theorem elem_full {A : Type*} [Fintype A] (v : A → ℂ) :
    elem v (Fintype.card A) = ∏ i, v i := by
  classical
  simp [elem, ← Finset.card_univ]

/-- A nonzero band of column vectors has a common nonvanishing point if it is
stable under a transitive system of column permutations. -/
theorem full_column_support {G : Type*} [AddCommGroup G] {q : ℕ}
    (L : Submodule ℂ (G × Fin q → ℂ)) (χ : AddChar G ℂ)
    (cols : ∀ j k : Fin q, ∃ σ : Equiv.Perm (Fin q), σ j=k ∧
      ∀ t ∈ L, (fun x : G × Fin q => t (x.1,σ x.2)) ∈ L)
    {v : Fin q → ℂ} (hv : bandMap χ v ∈ L) {i : Fin q} (hi : v i ≠ 0) :
    ∃ w : Fin q → ℂ, bandMap χ w ∈ L ∧ ∀ j, w j ≠ 0 := by
  classical
  let V := L.comap (bandMap χ)
  have each (j : Fin q) : ∃ w ∈ V, (LinearMap.proj j : (Fin q → ℂ) →ₗ[ℂ] ℂ) w ≠ 0 := by
    obtain ⟨σ,hσ,stable⟩ := cols j i
    refine ⟨fun z => v (σ z),stable _ hv,?_⟩
    simpa [hσ] using hi
  exact Module.Dual.exists_forall_mem_ne_zero_of_forall_exists V
    (fun j => (LinearMap.proj j : (Fin q → ℂ) →ₗ[ℂ] ℂ)) each

theorem two_sided_vanish {G : Type*} [AddCommGroup G] [Fintype G] {n : ℕ}
    (card : Fintype.card G=n) (L : Submodule ℂ (G × Fin n → ℂ))
    (rows : ∀ t ∈ L, ∀ a : G, (fun x : G × Fin n => t (x.1+a,x.2)) ∈ L)
    (cols : ∀ j k : Fin n, ∃ σ : Equiv.Perm (Fin n), σ j=k ∧
      ∀ t ∈ L, (fun x : G × Fin n => t (x.1,σ x.2)) ∈ L)
    (top : ∀ t ∈ L, mixedSum (fun _ : Fin n => t)=0) : L=⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro t ht
  obtain ⟨v,mem,decomp⟩ := row_character_decomposition L t (rows t ht)
  have nonzero (χ : AddChar G ℂ) (g : G) : χ g ≠ 0 := by
    intro h
    have z := χ.map_add_eq_mul g (-g)
    simp [h] at z
  have vanish (χ : AddChar G ℂ) (i : Fin n) : v χ i=0 := by
    by_contra hi
    obtain ⟨w,hw,all⟩ := full_column_support L χ cols (v:=v χ) (mem χ) hi
    have row : injectiveMoment (fun g => χ g) n ≠ 0 := by
      rw [injectiveMoment_eq,← card,elem_full]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr (fun g _ => nonzero χ g))
    have column : injectiveMoment w n ≠ 0 := by
      rw [injectiveMoment_eq]
      have hwfull : elem w n = ∏ i, w i := by simpa using elem_full w
      rw [hwfull]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
        (Finset.prod_ne_zero_iff.mpr (fun g _ => all g))
    apply mul_ne_zero row column
    simpa [mixedSum,injectiveMoment,bandMap,Finset.prod_mul_distrib,← Finset.mul_sum,← Finset.sum_mul]
      using top _ hw
  change t=0
  funext x
  simp [decomp x,vanish]

end BoundedFrequency


namespace TransitiveColumns
open Finset PermanentLevel BoundedFrequency
open scoped Classical

private def changeRows {I G J : Type*} (e : I ≃ G) : (I × J → ℂ) ≃ₗ[ℂ] (G × J → ℂ) where
  toFun t := fun x => t (e.symm x.1,x.2)
  invFun t := fun x => t (e x.1,x.2)
  left_inv := by intro t; funext x; simp
  right_inv := by intro t; funext x; simp
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private theorem change_mixed {I G J : Type*} [Fintype I] [Fintype G] [Fintype J]
    (e : I ≃ G) {k : ℕ} (t : I × J → ℂ) :
    mixedSum (fun _ : Fin k => changeRows (J := J) e t) = mixedSum (fun _ : Fin k => t) := by
  classical
  unfold mixedSum
  rw [← (Equiv.embeddingCongr (Equiv.refl (Fin k)) e).sum_comp]
  simp [changeRows,Equiv.embeddingCongr_apply,Function.Embedding.congr]

/-- A transitive column symmetry together with regular abelian row symmetry
forces a square translated permanent level space to be zero. -/
theorem translated_square_vanish {G : Type*} [Fintype G] [AddCommGroup G] {n : ℕ}
    (e : Fin n ≃ G) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (rows : ∀ T ∈ L, ∀ a : G, (fun x : Fin n × Fin n =>
        T (e.symm (e x.1 + a), x.2)) ∈ L)
    (cols : ∀ j k : Fin n, ∃ σ : Equiv.Perm (Fin n), σ j=k ∧
        ∀ T ∈ L, (fun x : Fin n × Fin n => T (x.1, σ x.2)) ∈ L)
    (level : ∀ T ∈ L, RectangularPermanent.value T=RectangularPermanent.value (0 : Fin n × Fin n → ℂ)) :
    L=⊥ := by
  let R := changeRows (J:=Fin n) e
  let V := L.map R.toLinearMap
  have card : Fintype.card G=n := by simpa using Fintype.card_congr e.symm
  have rowV : ∀ t ∈ V, ∀ a : G, (fun x : G × Fin n => t (x.1+a,x.2)) ∈ V := by
    rintro _ ⟨T,hT,rfl⟩ a
    refine ⟨_,rows T hT a,?_⟩
    funext x
    simp [R,changeRows]
  have colV : ∀ j k : Fin n, ∃ σ : Equiv.Perm (Fin n), σ j=k ∧
        ∀ t ∈ V, (fun x : G × Fin n => t (x.1,σ x.2)) ∈ V := by
    intro j k
    obtain ⟨σ,hσ,stable⟩ := cols j k
    refine ⟨σ,hσ,?_⟩
    rintro _ ⟨T,hT,rfl⟩
    exact ⟨_,stable T hT,rfl⟩
  have hn : 0<n := by simpa [←card] using Fintype.card_pos (α:=G)
  have top : ∀ t ∈ V, mixedSum (fun _ : Fin n => t)=0 := by
    rintro _ ⟨T,hT,rfl⟩
    exact (change_mixed e T).trans (RectangularPermanent.mixed_of_translated (le_refl n) L level hn (le_refl n) T hT)
  have zero := two_sided_vanish card V rowV colV top
  apply le_antisymm _ bot_le
  intro t ht
  have mem : R t ∈ V := ⟨_,ht,rfl⟩
  rw [zero] at mem
  exact R.injective (show R t=R 0 by simpa using mem)

end TransitiveColumns
