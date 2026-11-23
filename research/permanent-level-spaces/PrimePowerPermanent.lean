import Mathlib

/-!
# The permanent level-space bound under a regular abelian row action

The column-product dimension bound and its linear form of Rado's theorem below
are adapted from the project's checked L-gct-171 and L-gct-175 and their dependencies.
The finite partition, character, homogenization and transfer arguments use Mathlib.
The two main theorems appear at the end of this file.
-/

namespace PermanentLevel.ProjectCore.RadoLinear

open Submodule Module

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] {ι : Type*}


def un (A : ι → Finset W) (s : Finset ι) : Set W := ⋃ j ∈ s, (A j : Set W)

lemma un_finite (A : ι → Finset W) (s : Finset ι) : (un A s).Finite :=
  s.finite_toSet.biUnion fun j _ => (A j).finite_toSet

lemma un_insert [DecidableEq ι] (A : ι → Finset W) (i : ι) (s : Finset ι) :
    un A (insert i s) = (A i : Set W) ∪ un A s := by
  simp only [un, Finset.set_biUnion_insert]

lemma un_union [DecidableEq ι] (A : ι → Finset W) (s t : Finset ι) :
    un A (s ∪ t) = un A s ∪ un A t := by
  simp only [un, Finset.set_biUnion_union]

lemma un_mono (A : ι → Finset W) {s t : Finset ι} (h : s ⊆ t) : un A s ⊆ un A t :=
  Set.biUnion_subset_biUnion_left (fun _ hx => h hx)

lemma un_update_of_not_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∉ s) : un (Function.update A i B) s = un A s := by
  unfold un
  refine Set.iUnion₂_congr fun j hj => ?_
  rw [Function.update_of_ne (by rintro rfl; exact h hj)]

lemma un_update_of_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∈ s) :
    un (Function.update A i B) s = (B : Set W) ∪ un A (s.erase i) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [un_insert, un_update_of_not_mem _ _ _ _ (Finset.notMem_erase i s),
    Function.update_self]



def Good (K : Type*) [Field K] [Module K W] (A : ι → Finset W) : Prop :=
  ∀ s : Finset ι, s.card ≤ finrank K (span K (un A s))

lemma finrank_span_mono {X Y : Set W} (hY : Y.Finite) (h : X ⊆ Y) :
    finrank K (span K X) ≤ finrank K (span K Y) := by
  haveI := FiniteDimensional.span_of_finite K hY
  exact Submodule.finrank_mono (span_mono h)



lemma bad_erase [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    (c : W) (h : ¬ Good K (Function.update A i ((A i).erase c))) :
    ∃ t : Finset ι, i ∉ t ∧
      finrank K (span K ((((A i).erase c : Finset W) : Set W) ∪ un A t)) ≤ t.card := by
  simp only [Good, not_forall, not_le] at h
  obtain ⟨s, hs⟩ := h
  by_cases hi : i ∈ s
  · refine ⟨s.erase i, Finset.notMem_erase i s, ?_⟩
    rw [un_update_of_mem _ _ _ _ hi] at hs
    have := Finset.card_erase_add_one hi
    omega
  · rw [un_update_of_not_mem _ _ _ _ hi] at hs
    exact absurd (hA s) (not_le.mpr hs)



lemma erase_good [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    {a b : W} (ha : a ∈ A i) (hb : b ∈ A i) (hab : a ≠ b) :
    Good K (Function.update A i ((A i).erase a)) ∨
      Good K (Function.update A i ((A i).erase b)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨t1, hi1, h1⟩ := bad_erase A hA i a hcon.1
  obtain ⟨t2, hi2, h2⟩ := bad_erase A hA i b hcon.2
  set X : Set W := (((A i).erase a : Finset W) : Set W) ∪ un A t1 with hX
  set Y : Set W := (((A i).erase b : Finset W) : Set W) ∪ un A t2 with hY
  have hXf : X.Finite := ((A i).erase a).finite_toSet.union (un_finite A t1)
  have hYf : Y.Finite := ((A i).erase b).finite_toSet.union (un_finite A t2)
  haveI : FiniteDimensional K (span K X) := FiniteDimensional.span_of_finite K hXf
  haveI : FiniteDimensional K (span K Y) := FiniteDimensional.span_of_finite K hYf
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span K X) (span K Y)
  
  have hU : un A (insert i (t1 ∪ t2)) ⊆ X ∪ Y := by
    rw [un_insert, un_union]
    intro x hx
    rcases hx with hx | hx | hx
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr (Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab, ha⟩)))
      · exact Or.inl (Or.inl (by simp [Finset.mem_erase, hxa, hx]))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  have hi12 : i ∉ t1 ∪ t2 := by simp [hi1, hi2]
  have hcardU := hA (insert i (t1 ∪ t2))
  rw [Finset.card_insert_of_notMem hi12] at hcardU
  have hsup : finrank K (span K (un A (insert i (t1 ∪ t2)))) ≤ finrank K ↥(span K X ⊔ span K Y) := by
    rw [← Submodule.span_union]
    exact finrank_span_mono (hXf.union hYf) hU
  
  have hinf : finrank K (span K (un A (t1 ∩ t2))) ≤ finrank K ↥(span K X ⊓ span K Y) := by
    haveI : FiniteDimensional K ↥(span K X ⊓ span K Y) :=
      Submodule.finiteDimensional_inf_left _ _
    refine Submodule.finrank_mono (le_inf (span_mono ?_) (span_mono ?_))
    · exact (un_mono A Finset.inter_subset_left).trans Set.subset_union_right
    · exact (un_mono A Finset.inter_subset_right).trans Set.subset_union_right
  have hcardI := hA (t1 ∩ t2)
  have hc := Finset.card_union_add_card_inter t1 t2
  omega


theorem rado_aux [Fintype ι] [DecidableEq ι] [DecidableEq W] :
    ∀ n : ℕ, ∀ A : ι → Finset W, ∑ j, (A j).card = n → Good K A →
      ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hA
  by_cases hbig : ∃ i, 1 < (A i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
    have key : ∃ c ∈ A i, Good K (Function.update A i ((A i).erase c)) := by
      rcases erase_good A hA i ha hb hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    obtain ⟨c, hc, hgood⟩ := key
    set A' := Function.update A i ((A i).erase c) with hA'
    have hlt : ∑ j, (A' j).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [hA', Function.update_self]
          exact Finset.card_erase_le
        · simp only [hA', Function.update_of_ne hj, le_refl]
      · simp only [hA', Function.update_self]
        exact Finset.card_erase_lt_of_mem hc
    obtain ⟨f, hf, hli⟩ := ih _ hlt A' rfl hgood
    refine ⟨f, fun j => ?_, hli⟩
    have := hf j
    by_cases hj : j = i
    · subst hj; simp only [hA', Function.update_self] at this
      exact Finset.mem_of_mem_erase this
    · simpa only [hA', Function.update_of_ne hj] using this
  · push_neg at hbig
    have hone : ∀ j, ∃ v, A j = {v} := by
      intro j
      refine Finset.card_eq_one.mp (le_antisymm (hbig j) ?_)
      have h1 := hA {j}
      have hunj : un A {j} = (A j : Set W) := by simp [un]
      rw [hunj, Finset.card_singleton] at h1
      rw [Nat.one_le_iff_ne_zero] at h1 ⊢
      intro h0
      rw [Finset.card_eq_zero] at h0
      apply h1
      simp [h0]
    choose f hf using hone
    refine ⟨f, fun j => by simp [hf j], ?_⟩
    rw [linearIndependent_iff_card_le_finrank_span]
    have h := hA Finset.univ
    have hr : un A Finset.univ = Set.range f := by
      ext x; simp [un, hf, eq_comm]
    rw [hr, Finset.card_univ] at h
    exact h

end PermanentLevel.ProjectCore.RadoLinear

theorem PermanentLevel.ProjectCore.L171 :
    ∀ (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Finset W), (∀ U : Finset ι, U.card ≤ Module.finrank K (Submodule.span K (⋃ j ∈ U, (A j : Set W)))) → ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro K _ W _ _ ι _ _ A hA
  classical
  exact PermanentLevel.ProjectCore.RadoLinear.rado_aux _ A rfl hA

namespace PermanentLevel.ProjectCore.Helpers.ColumnCore

open Module

variable {ρ κ : Type} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]


def Good (V : Submodule ℂ (ρ × κ → ℂ)) (C : Finset κ) : Prop :=
  ∀ x ∈ V, (∀ i, ∀ j ∉ C, x (i, j) = 0) ∧
    ∀ c : ℂ, ∑ j ∈ C, ∏ i, (c + x (i, j)) = (C.card : ℂ) * c ^ Fintype.card ρ


def g (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) : Module.Dual ℂ V :=
  (LinearMap.proj (R := ℂ) (φ := fun _ : ρ × κ => ℂ) (i, j)).comp V.subtype

@[simp] theorem g_apply (V : Submodule ℂ (ρ × κ → ℂ)) (i : ρ) (j : κ) (x : V) :
    g V i j x = (x : ρ × κ → ℂ) (i, j) := rfl


def S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) : Set (Module.Dual ℂ V) :=
  {φ | ∃ i, ∃ j ∈ U, φ = g V i j}

theorem mem_coann_span_iff {V : Type} [AddCommGroup V] [Module ℂ V] (T : Set (Module.Dual ℂ V))
    (x : V) : x ∈ (Submodule.span ℂ T).dualCoannihilator ↔ ∀ φ ∈ T, φ x = 0 := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h φ hφ
    exact h φ (Submodule.subset_span hφ)
  · intro h φ hφ
    have hle : Submodule.span ℂ T ≤ LinearMap.ker (Module.Dual.eval ℂ V x) := by
      rw [Submodule.span_le]
      intro ψ hψ
      simp [h ψ hψ]
    have := hle hφ
    simpa using this

theorem mem_coann_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) (x : V) :
    x ∈ (Submodule.span ℂ (S V U)).dualCoannihilator ↔
      ∀ i, ∀ j ∈ U, (x : ρ × κ → ℂ) (i, j) = 0 := by
  rw [mem_coann_span_iff]
  constructor
  · intro h i j hj
    exact h (g V i j) ⟨i, j, hj, rfl⟩
  · rintro h φ ⟨i, j, hj, rfl⟩
    simpa using h i j hj

theorem finrank_span_S (V : Submodule ℂ (ρ × κ → ℂ)) (U : Finset κ) :
    finrank ℂ (Submodule.span ℂ (S V U)) =
      finrank ℂ V - finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (S V U))
  omega


theorem sum_sdiff_of_zero (C U : Finset κ) (hUC : U ⊆ C) (x : ρ × κ → ℂ)
    (hx : ∀ i, ∀ j ∈ U, x (i, j) = 0) (c : ℂ)
    (h : ∑ j ∈ C, ∏ i, (c + x (i, j)) = (C.card : ℂ) * c ^ Fintype.card ρ) :
    ∑ j ∈ C \ U, ∏ i, (c + x (i, j)) = ((C \ U).card : ℂ) * c ^ Fintype.card ρ := by
  have hU : ∑ j ∈ U, ∏ i, (c + x (i, j)) = (U.card : ℂ) * c ^ Fintype.card ρ := by
    have : ∀ j ∈ U, ∏ i, (c + x (i, j)) = c ^ Fintype.card ρ := by
      intro j hj
      simp [hx _ j hj, Finset.prod_const]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hs := Finset.sum_sdiff (f := fun j => ∏ i, (c + x (i, j))) hUC
  rw [Finset.card_sdiff_of_subset hUC, Nat.cast_sub (Finset.card_le_card hUC)]
  rw [h, hU] at hs
  linear_combination hs

theorem bound : ∀ (n : ℕ) (C : Finset κ) (V : Submodule ℂ (ρ × κ → ℂ)),
    C.card = n → C.Nonempty → Good V C → finrank ℂ V < n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C V hCn hCne hV
  by_contra hcon
  push_neg at hcon
  
  have step1 : ∀ U : Finset κ, U ⊆ C → U.Nonempty →
      finrank ℂ (Submodule.span ℂ (S V U)).dualCoannihilator ≤ C.card - U.card := by
    intro U hUC hUne
    set Kc := (Submodule.span ℂ (S V U)).dualCoannihilator with hKc
    by_cases hUeq : U = C
    · have : Kc = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [hKc, mem_coann_S] at hx
        rw [Submodule.mem_bot]
        apply Subtype.ext
        funext ⟨i, j⟩
        by_cases hj : j ∈ C
        · exact hx i j (hUeq ▸ hj)
        · exact (hV x.1 x.2).1 i j hj
      rw [this, finrank_bot]
      exact Nat.zero_le _
    · set K := Kc.map V.subtype with hK
      have hKr : finrank ℂ K = finrank ℂ Kc :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective V.subtype V.injective_subtype Kc)).symm
      have hgood : Good K (C \ U) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        rw [hKc, mem_coann_S] at hy
        obtain ⟨h0, hc⟩ := hV y.1 y.2
        refine ⟨?_, fun c => sum_sdiff_of_zero C U hUC y.1 hy c (hc c)⟩
        intro i j hj
        rw [Finset.mem_sdiff, not_and_or, not_not] at hj
        rcases hj with hj | hj
        · exact h0 i j hj
        · exact hy i j hj
      have hlt : (C \ U).card < n := by
        rw [← hCn]
        exact Finset.card_lt_card (Finset.sdiff_ssubset hUC hUne)
      have hne : (C \ U).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro h
        exact hUeq (Finset.Subset.antisymm hUC h)
      have := ih _ hlt (C \ U) K rfl hne hgood
      rw [Finset.card_sdiff_of_subset hUC] at this
      omega
  
  let ι := {j // j ∈ C}
  let A : ι → Finset (Module.Dual ℂ V) := fun j => Finset.univ.image (fun i => g V i j.1)
  have hcond : ∀ U : Finset ι, U.card ≤ finrank ℂ
      (Submodule.span ℂ (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V)))) := by
    intro U
    set U' : Finset κ := U.map (Function.Embedding.subtype _) with hU'
    have hset : (⋃ j ∈ U, (A j : Set (Module.Dual ℂ V))) = S V U' := by
      ext φ
      simp only [Set.mem_iUnion, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_range, S, Set.mem_setOf_eq, hU', Finset.mem_map, Function.Embedding.coe_subtype,
        A]
      constructor
      · rintro ⟨j, hj, i, rfl⟩
        exact ⟨i, j.1, ⟨j, hj, rfl⟩, rfl⟩
      · rintro ⟨i, _, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨j, hj, i, rfl⟩
    rw [hset, finrank_span_S]
    have hcard : U'.card = U.card := Finset.card_map _
    have hsub : U' ⊆ C := by
      intro j hj
      rw [hU', Finset.mem_map] at hj
      obtain ⟨a, _, rfl⟩ := hj
      exact a.2
    have hUle : U'.card ≤ C.card := Finset.card_le_card hsub
    rcases U'.eq_empty_or_nonempty with he | hne
    · have : U.card = 0 := by rw [← hcard, he, Finset.card_empty]
      omega
    · have := step1 U' hsub hne
      omega
  obtain ⟨f, hfA, hfind⟩ := PermanentLevel.ProjectCore.L171 ℂ (Module.Dual ℂ V) ι A hcond
  have hσ : ∀ j : ι, ∃ i : ρ, g V i j.1 = f j := by
    intro j
    have := hfA j
    simpa [A] using this
  choose σ hσ using hσ
  
  let Ψ : V →ₗ[ℂ] (ι → ℂ) := LinearMap.pi (fun j => f j)
  have hker : LinearMap.ker Ψ = (Submodule.span ℂ (Set.range f)).dualCoannihilator := by
    ext x
    rw [mem_coann_span_iff, LinearMap.mem_ker]
    constructor
    · rintro h φ ⟨j, rfl⟩
      exact congrFun h j
    · intro h
      funext j
      exact h (f j) ⟨j, rfl⟩
  have hspan : finrank ℂ (Submodule.span ℂ (Set.range f)) = Fintype.card ι :=
    finrank_span_eq_card hfind
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℂ (Set.range f))
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  have hfun : finrank ℂ (ι → ℂ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℂ
  have htop : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hker] at hrn
    omega
  obtain ⟨y, hy⟩ : (fun _ => (-1 : ℂ)) ∈ LinearMap.range Ψ := htop ▸ Submodule.mem_top
  have hyσ : ∀ j : ι, (y : ρ × κ → ℂ) (σ j, j.1) = -1 := by
    intro j
    have := congrFun hy j
    simp only [Ψ, LinearMap.pi_apply] at this
    rw [← hσ j] at this
    simpa [Ψ] using this
  
  obtain ⟨_, hy1⟩ := hV y.1 y.2
  have hzero : ∀ j ∈ C, ∏ i, ((1 : ℂ) + (y : ρ × κ → ℂ) (i, j)) = 0 := by
    intro j hj
    apply Finset.prod_eq_zero (Finset.mem_univ (σ ⟨j, hj⟩))
    rw [hyσ ⟨j, hj⟩]
    ring
  have hsum := hy1 1
  rw [Finset.sum_eq_zero hzero, one_pow, mul_one] at hsum
  have hc : (C.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hCne).ne'
  exact hc hsum.symm


theorem finrank_map_add_finrank_inf_ker {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) (p : Submodule ℂ E) :
    finrank ℂ (p.map f) + finrank ℂ (p ⊓ LinearMap.ker f : Submodule ℂ E) = finrank ℂ p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h, (Submodule.equivSubtypeMap p _).finrank_eq, Submodule.map_comap_subtype]


theorem column_core : ∀ (p q : ℕ) (V : Submodule ℂ (Fin p × Fin q → ℂ))
    (lam : (Fin p × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V →
    lam (fun _ => (1 : ℂ)) = 1 → (∀ x ∈ V, (∑ j, ∏ i, x (i, j)) = (q : ℂ) * lam x ^ p) →
    Module.finrank ℂ V ≤ q := by
  intro p q V lam hJ hlam hN
  set W : Submodule ℂ (Fin p × Fin q → ℂ) := V ⊓ LinearMap.ker lam with hWdef
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0
      have : (fun _ => (1 : ℂ) : Fin p × Fin 0 → ℂ) = 0 := funext fun x => isEmptyElim x.2
      rw [this, map_zero] at hlam
      exact absurd hlam zero_ne_one
    · exact h0
  have hW : Good W (Finset.univ : Finset (Fin q)) := by
    intro w hw
    refine ⟨fun i j hj => absurd (Finset.mem_univ j) hj, fun c => ?_⟩
    obtain ⟨hwV, hwk⟩ := Submodule.mem_inf.mp hw
    have hx : w + c • (fun _ => (1 : ℂ)) ∈ V := V.add_mem hwV (V.smul_mem c hJ)
    have := hN _ hx
    rw [map_add, map_smul, LinearMap.mem_ker.mp hwk, hlam, smul_eq_mul, mul_one, zero_add] at this
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => ?_
    simp [add_comm]
  have hne : (Finset.univ : Finset (Fin q)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hq⟩⟩
  have h1 := bound q Finset.univ W (by simp) hne hW
  change finrank ℂ ↥(V ⊓ LinearMap.ker lam) < q at h1
  have h2 := finrank_map_add_finrank_inf_ker lam V
  have h3 := Submodule.finrank_le (V.map lam)
  rw [Module.finrank_self] at h3
  omega

end PermanentLevel.ProjectCore.Helpers.ColumnCore

theorem PermanentLevel.ProjectCore.L175 :
    ∀ (p q : ℕ) (V : Submodule ℂ (Fin p × Fin q → ℂ)) (lam : (Fin p × Fin q → ℂ) →ₗ[ℂ] ℂ), (fun _ => (1 : ℂ)) ∈ V → lam (fun _ => (1 : ℂ)) = 1 → (∀ x ∈ V, (∑ j, ∏ i, x (i, j)) = (q : ℂ) * lam x ^ p) → Module.finrank ℂ V ≤ q :=
  PermanentLevel.ProjectCore.Helpers.ColumnCore.column_core

namespace PermanentLevel

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

def mergeWeight {B : Type*} [AddCommMonoid B] {n : ℕ} (f : Fin n → B) (b : B)
    (j i : Fin n) : B := (if i = j then b else 0) + f i

private theorem sum_mergeWeight {B : Type*} [AddCommMonoid B] {n : ℕ} (f : Fin n → B)
    (b : B) (j : Fin n) : ∑ i, mergeWeight f b j i = b + ∑ i, f i := by
  simp only [mergeWeight,Finset.sum_add_distrib]
  simp

noncomputable def coefficient {B : Type*} [AddCommMonoid B] (q : ℤ) :
    (n : ℕ) → (Fin n → B) → ℤ
  | 0, _ => 1
  | n+1, f => (if f 0 = 0 then q else 0) * coefficient q n (Fin.tail f) -
      ∑ j, coefficient q n (mergeWeight (Fin.tail f) (f 0) j)

theorem coefficient_dvd {B : Type*} [AddCommMonoid B] (q : ℤ) (n : ℕ)
    (f : Fin (n+1) → B) : q ∣ coefficient q (n+1) f := by
  induction n with
  | zero => by_cases h : f 0 = 0 <;> simp [coefficient,h]
  | succ n ih =>
    rw [coefficient]
    apply dvd_sub
    · by_cases h : f 0 = 0 <;> simp [h]
    · exact Finset.dvd_sum fun j _ => ih _

theorem coefficient_congruence {B : Type*} [AddCommMonoid B] (q : ℤ) (k : ℕ)
    (f : Fin (k+1) → B) : ∃ t : ℤ,
    coefficient q (k+1) f =
      (if ∑ i, f i = 0 then (-1 : ℤ)^k * k.factorial * q else 0) + q^2*t := by
  induction k with
  | zero =>
    refine ⟨0,?_⟩
    simp [coefficient]
  | succ k ih =>
    let fs := Fin.tail f
    let w := if ∑ i, f i = 0 then (-1 : ℤ)^k*k.factorial*q else 0
    obtain ⟨u,hu⟩ := coefficient_dvd q k fs
    have hmerge (j : Fin (k+1)) : ∃ v : ℤ,
        coefficient q (k+1) (mergeWeight fs (f 0) j) = w+q^2*v := by
      obtain ⟨v,hv⟩ := ih (mergeWeight fs (f 0) j)
      have hsum : ∑ i, mergeWeight fs (f 0) j i = ∑ i, f i := by
        rw [sum_mergeWeight, Fin.sum_univ_succ f]
        rfl
      exact ⟨v, by simpa only [hsum,w] using hv⟩
    choose v hv using hmerge
    refine ⟨(if f 0 = 0 then u else 0) - ∑ j, v j,?_⟩
    rw [coefficient]
    change (if f 0 = 0 then q else 0) * coefficient q (k+1) fs -
      ∑ j, coefficient q (k+1) (mergeWeight fs (f 0) j) = _
    simp_rw [hv]
    rw [hu, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    by_cases h : ∑ i, f i = 0 <;> by_cases h0 : f 0 = 0 <;>
      simp [w,h,h0,pow_succ,Nat.factorial_succ] <;> ring

theorem injectiveSum_character {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    [IsDomain R] (n : ℕ) (f : Fin n → AddChar A R) :
    injectiveSum (fun i a => f i a) = ((coefficient (Fintype.card A) n f : ℤ) : R) := by
  induction n with
  | zero =>
    simp [coefficient,injectiveSum]
  | succ n ih =>
    let fs := Fin.tail f
    have hf : (fun (i : Fin (n+1)) (a : A) => f i a) =
        Fin.cons (fun a => f 0 a) (fun i a => fs i a) := by
      funext i a
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    have hm (j : Fin n) : mergeEntry (fun i a => fs i a) (fun a => f 0 a) j =
        (fun i a => mergeWeight fs (f 0) j i a) := by
      funext i a
      by_cases h : i=j <;> simp [mergeEntry,mergeWeight,h]
    rw [hf,injectiveSum_succ,AddChar.sum_eq_ite,coefficient]
    simp only [hm, ih, Int.cast_sub,Int.cast_mul,Int.cast_sum]
    by_cases h : f 0 = 0 <;> simp [h,fs]

theorem prime_nonzero {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    [IsDomain R] [CharZero R] {p k : ℕ} (hc : Fintype.card A = p) (hp : p.Prime)
    (hk : k < p) (f : Fin (k+1) → AddChar A R) (hs : ∑ i, f i = 0) :
    injectiveSum (fun i a => f i a) ≠ 0 := by
  rw [injectiveSum_character,hc,Int.cast_ne_zero]
  obtain ⟨t,ht⟩ := coefficient_congruence (p : ℤ) k f
  rw [ite_eq_left hs] at ht
  intro hz
  rw [hz] at ht
  have hprod : (p : ℤ) * ((-1 : ℤ)^k * k.factorial + p*t) = 0 := by linarith
  have hl := (mul_eq_zero.mp hprod).resolve_left (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hd : (p : ℤ) ∣ (-1 : ℤ)^k * k.factorial := ⟨-t,by linarith⟩
  have hunit : IsUnit ((-1 : ℤ)^k) := isUnit_neg_one.pow k
  have hfac : (p : ℤ) ∣ (k.factorial : ℤ) := by
    exact (hunit.dvd_mul_left).mp hd
  exact (Nat.not_le.mpr hk) (hp.dvd_factorial.mp (Int.natCast_dvd_natCast.mp hfac))

theorem coefficient_zero_if_off {B : Type*} [AddCommMonoid B] (q : ℤ) (n : ℕ)
    (f : Fin n → B) (hf : ∑ i, f i ≠ 0) : coefficient q n f = 0 := by
  induction n with
  | zero => simp at hf
  | succ n ih =>
    rw [coefficient]
    let fs := Fin.tail f
    have hs : ∑ i, f i = f 0 + ∑ i, fs i := Fin.sum_univ_succ _
    have hmerge (j : Fin n) : ∑ i, mergeWeight fs (f 0) j i ≠ 0 := by
      rwa [sum_mergeWeight,← hs]
    change (if f 0 = 0 then q else 0)*coefficient q n fs -
      ∑ j, coefficient q n (mergeWeight fs (f 0) j) = _
    simp_rw [fun j => ih _ (hmerge j)]
    by_cases h0 : f 0 = 0
    · have hfs : ∑ i, fs i ≠ 0 := by simpa [hs,h0] using hf
      simp [ih _ hfs]
    · simp [h0]

theorem injectiveSum_ne_zero_iff {A R : Type*} [AddCommGroup A] [Fintype A] [CommRing R]
    [IsDomain R] [CharZero R] {p k : ℕ} (hq : Fintype.card A ≠ 0) (hp : p.Prime)
    (hd : p ∣ Fintype.card A) (hk : k < p) (f : Fin (k+1) → AddChar A R) :
    injectiveSum (fun i a => f i a) ≠ 0 ↔ ∑ i, f i = 0 := by
  let q := Fintype.card A
  constructor
  · contrapose!
    intro hf
    rw [injectiveSum_character,coefficient_zero_if_off _ _ f hf,Int.cast_zero]
  · intro hs
    rw [injectiveSum_character,Int.cast_ne_zero]
    obtain ⟨t,ht⟩ := coefficient_congruence (q : ℤ) k f
    rw [ite_eq_left hs] at ht
    intro hz
    rw [hz] at ht
    have hprod : (q : ℤ) * ((-1 : ℤ)^k * k.factorial + q*t) = 0 := by linarith
    have hl := (mul_eq_zero.mp hprod).resolve_left (Int.natCast_ne_zero.mpr hq)
    have ha : (q : ℤ) ∣ (-1 : ℤ)^k * k.factorial := ⟨-t,by linarith⟩
    have hd' : (p : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr hd
    have hfac : (p : ℤ) ∣ (k.factorial : ℤ) :=
      ((isUnit_neg_one.pow k).dvd_mul_left).mp (hd'.trans ha)
    exact (Nat.not_le.mpr hk) (hp.dvd_factorial.mp (Int.natCast_dvd_natCast.mp hfac))

end PermanentLevel

namespace PermanentLevel

private theorem floor_join (r s m : ℕ) (hm : 0 < m) :
    (r+s+1)/m ≤ r/m + s/m + 1 := by
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hm]
  have hr := Nat.mod_add_div r m
  have hs := Nat.mod_add_div s m
  nlinarith [Nat.mod_lt r hm, Nat.mod_lt s hm]

theorem factorial_join {p a r s : ℕ} (hp : p.Prime) (ha : 0 < a)
    (h : r+s+1 < p^a) :
    (r+s+1).factorial.factorization p ≤
      r.factorial.factorization p + s.factorial.factorization p + (a-1) := by
  have hl (k : ℕ) (hk : k ≤ r+s+1) : Nat.log p k < a := by
    by_cases h0 : k = 0
    · simpa [h0] using ha
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt h0).mpr (hk.trans_lt h)
  rw [Nat.factorization_factorial hp (hl _ (le_refl _)),
    Nat.factorization_factorial hp (hl r (by omega)),
    Nat.factorization_factorial hp (hl s (by omega))]
  calc
    _ ≤ ∑ i ∈ Finset.Ico 1 a, (r / p^i + s / p^i + 1) :=
      Finset.sum_le_sum (fun i _ => floor_join r s _ (pow_pos hp.pos i))
    _ = _ := by simp [Finset.sum_add_distrib]

def blockVal (p n : ℕ) := (n-1).factorial.factorization p

theorem partition_factorial_bound {p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (parts : List ℕ) (hpos : ∀ v ∈ parts, 0 < v) (hb : parts.sum ≤ p^a) :
    blockVal p parts.sum ≤ (parts.map (blockVal p)).sum + (parts.length-1)*(a-1) := by
  induction parts with
  | nil => simp [blockVal]
  | cons x xs ih =>
    have hx := hpos x List.mem_cons_self
    cases xs with
    | nil => simp
    | cons y ys =>
      have hy := hpos y (by simp)
      have ht : 0 < (y::ys).sum := by simp; omega
      have htB : (y::ys).sum ≤ p^a := by simp at hb ⊢; omega
      have htP : ∀ v ∈ y::ys, 0 < v := fun v hv => hpos v (List.mem_cons_of_mem _ hv)
      have hi := ih htP htB
      have hj := factorial_join (r := x-1) (s := (y::ys).sum-1) hp ha (by
        change x + (y::ys).sum ≤ p^a at hb
        omega)
      change (x+(y::ys).sum-1).factorial.factorization p ≤ _
      rw [show x+(y::ys).sum-1 = (x-1)+((y::ys).sum-1)+1 by omega]
      change _ ≤ blockVal p x + (List.map (blockVal p) (y::ys)).sum +
        (ys.length+1)*(a-1)
      rw [Nat.add_mul,one_mul]
      simp only [List.length_cons, Nat.add_one_sub_one] at hi
      change blockVal p ((y::ys).sum) ≤ _ at hi
      change _ ≤ blockVal p x + blockVal p ((y::ys).sum) + (a-1) at hj
      omega


def unsignedTerm (q : ℕ) : List ℕ → ℕ
  | [] => 1
  | b::bs => (q * (b-1).factorial) * unsignedTerm q bs

private theorem term_ne_zero {q : ℕ} (hq : q ≠ 0) (bs : List ℕ) :
    unsignedTerm q bs ≠ 0 := by
  induction bs with
  | nil => simp [unsignedTerm]
  | cons b bs ih => simp [unsignedTerm,hq,Nat.factorial_ne_zero,ih]

private theorem term_val {q p : ℕ} (hq : q ≠ 0) (bs : List ℕ) :
    (unsignedTerm q bs).factorization p =
      bs.length * q.factorization p + (bs.map (blockVal p)).sum := by
  induction bs with
  | nil => simp [unsignedTerm]
  | cons b bs ih =>
    simp only [unsignedTerm, Nat.factorization_mul (mul_ne_zero hq (Nat.factorial_ne_zero _))
      (term_ne_zero hq _), Nat.factorization_mul hq (Nat.factorial_ne_zero _),
      Finsupp.coe_add, Pi.add_apply, ih,List.length_cons,List.map_cons,List.sum_cons]
    simp only [Nat.add_mul,one_mul,blockVal]
    omega

theorem nontrivial_partition_dvd {p q : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    (ha : 0 < q.factorization p) (bs : List ℕ) (hpos : ∀ v ∈ bs, 0 < v)
    (hs : bs.sum ≤ p ^ q.factorization p) (hm : 2 ≤ bs.length) :
    p ^ (q.factorization p + blockVal p bs.sum + 1) ∣ unsignedTerm q bs := by
  rw [hp.pow_dvd_iff_le_factorization (term_ne_zero hq bs),term_val hq]
  have hj := partition_factorial_bound hp ha bs hpos hs
  obtain ⟨k,hk⟩ : ∃ k, bs.length = k+2 := ⟨bs.length-2,by omega⟩
  obtain ⟨v,hv⟩ : ∃ v, q.factorization p = v+1 := ⟨q.factorization p-1,by omega⟩
  rw [hk,hv] at hj ⊢
  simp only [show k+2-1=k+1 by omega, Nat.add_sub_cancel, Nat.add_mul,
    Nat.mul_add, one_mul, mul_one] at hj ⊢
  omega

theorem single_partition_not_dvd {p q : ℕ} (hp : p.Prime) (hq : q ≠ 0) (d : ℕ) :
    ¬ p ^ (q.factorization p + blockVal p d + 1) ∣ q * (d-1).factorial := by
  rw [hp.pow_dvd_iff_le_factorization (mul_ne_zero hq (Nat.factorial_ne_zero _)),
    Nat.factorization_mul hq (Nat.factorial_ne_zero _)]
  simp [blockVal]

theorem signed_partition_sum_ne_zero {p q d : ℕ} (hp : p.Prime) (hq : q ≠ 0)
    (ha : 0 < q.factorization p) (hs : d ≤ p ^ q.factorization p)
    (bs : List (List ℕ)) (valid : ∀ b ∈ bs, b.sum = d ∧ 2 ≤ b.length ∧ ∀ v ∈ b, 0 < v)
    (sgn : List ℕ → ℤ) :
    (q * (d-1).factorial : ℕ) + (bs.map (fun b => sgn b * (unsignedTerm q b : ℤ))).sum ≠ (0 : ℤ) := by
  let m := p ^ (q.factorization p + blockVal p d + 1)
  have allDvd (b) (hb : b ∈ bs) : (m : ℤ) ∣ sgn b * (unsignedTerm q b : ℤ) := by
    obtain ⟨hsum,hlen,hpos⟩ := valid b hb
    apply dvd_mul_of_dvd_right
    apply Int.natCast_dvd_natCast.mpr
    simpa [m,hsum] using nontrivial_partition_dvd hp hq ha b hpos (hsum ▸ hs) hlen
  have ds : (m : ℤ) ∣ (bs.map (fun b => sgn b * (unsignedTerm q b : ℤ))).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    exact allDvd b hb
  intro e
  have hv : (q * (d-1).factorial : ℕ) = - (bs.map (fun b => sgn b * (unsignedTerm q b : ℤ))).sum := by
    linarith
  apply single_partition_not_dvd hp hq d
  apply Int.natCast_dvd_natCast.mp
  rw [hv]
  exact dvd_neg.mpr ds

end PermanentLevel

namespace PermanentLevel

open Finset
open scoped Classical

namespace PartitionBridge

/-- A labelled partition with no empty block. The labels are created by inserting indices. -/
structure Blocks (n : ℕ) where
  num : ℕ
  tag : Fin n → Fin num
  onto : Function.Surjective tag

private def empty : Blocks 0 := ⟨0,Fin.elim0,fun h => h.elim0⟩

private def newBlock {n : ℕ} (P : Blocks n) : Blocks (n+1) where
  num := P.num+1
  tag := Fin.cons 0 (fun i => (P.tag i).succ)
  onto := by
    intro h
    refine Fin.cases ⟨0,rfl⟩ (fun a => ?_) h
    obtain ⟨i,rfl⟩ := P.onto a
    exact ⟨i.succ,by simp⟩

private def enterBlock {n : ℕ} (P : Blocks n) (h : Fin P.num) : Blocks (n+1) where
  num := P.num
  tag := Fin.cons h P.tag
  onto := by
    intro a
    obtain ⟨i,rfl⟩ := P.onto a
    exact ⟨i.succ,by simp⟩

private def refinements {n : ℕ} (P : Blocks n) : List (Blocks (n+1)) :=
  newBlock P :: List.ofFn (enterBlock P)

def catalogue : (n : ℕ) → List (Blocks n)
  | 0 => [empty]
  | n+1 => (catalogue n).flatMap refinements

def size {n : ℕ} (P : Blocks n) (h : Fin P.num) : ℕ :=
  ∑ i, if P.tag i = h then 1 else 0

def weight {B : Type*} [AddCommMonoid B] {n : ℕ} (P : Blocks n) (f : Fin n → B)
    (h : Fin P.num) : B := ∑ i, if P.tag i = h then f i else 0

private theorem size_pos {n : ℕ} (P : Blocks n) (h : Fin P.num) : 0 < size P h := by
  obtain ⟨j,hj⟩ := P.onto h
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨j,Finset.mem_univ _,by simp [hj]⟩

private theorem size_sum {n : ℕ} (P : Blocks n) : ∑ h, size P h = n := by
  unfold size
  rw [Finset.sum_comm]
  simp

private theorem sum_by_tag {n : ℕ} (P : Blocks n) (g : Fin P.num → ℤ) :
    (∑ j, g (P.tag j)) = ∑ h, (size P h : ℤ) * g h := by
  simp only [size,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

private theorem weight_merge {B : Type*} [AddCommMonoid B] {n : ℕ} (P : Blocks n)
    (f : Fin n → B) (b : B) (j : Fin n) (h : Fin P.num) :
    weight P (mergeWeight f b j) h =
      (if P.tag j = h then b else 0) + weight P f h := by
  unfold weight
  have each (i : Fin n) : (if P.tag i = h then mergeWeight f b j i else 0) =
      (if i=j then (if P.tag j=h then b else 0) else 0) +
      (if P.tag i=h then f i else 0) := by
    by_cases hij : i=j
    · subst j
      by_cases hh : P.tag i=h <;> simp [hh,mergeWeight]
    · by_cases hh : P.tag i=h <;> simp [hh,hij,mergeWeight]
  simp_rw [each]
  simp [Finset.sum_add_distrib]

private noncomputable def factor {B : Type*} [AddCommMonoid B] (q : ℤ) (k : ℕ) (v : B) : ℤ :=
  if v=0 then (-1 : ℤ)^(k-1) * (k-1).factorial * q else 0

private theorem factor_succ {B : Type*} [AddCommMonoid B] (q : ℤ) (k : ℕ)
    (hk : 0 < k) (v : B) : factor q (k+1) v = -(k : ℤ) * factor q k v := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  by_cases h : v=0 <;> simp [factor,h,pow_succ,Nat.factorial_succ]; ring

private noncomputable def termOn {B : Type*} [AddCommMonoid B] {n : ℕ} (q : ℤ) (P : Blocks n)
    (u : Fin P.num → B) : ℤ := ∏ h, factor q (size P h) (u h)

noncomputable def term {B : Type*} [AddCommMonoid B] {n : ℕ} (q : ℤ) (P : Blocks n)
    (f : Fin n → B) : ℤ := termOn q P (weight P f)

private theorem term_new {B : Type*} [AddCommMonoid B] {n : ℕ} (q : ℤ) (P : Blocks n)
    (f : Fin (n+1) → B) :
    term q (newBlock P) f = (if f 0 = 0 then q else 0) * term q P (Fin.tail f) := by
  unfold term termOn
  change (∏ h : Fin (P.num+1), factor q _ _) = _
  rw [Fin.prod_univ_succ]
  have hn (a : Fin P.num) : (0 : Fin (P.num+1)) ≠ a.succ := Ne.symm (Fin.succ_ne_zero a)
  by_cases hz : f 0=0 <;> simp [size,weight,newBlock,Fin.sum_univ_succ,Fin.tail,factor,hn,hz]

private def shifted {B : Type*} [AddCommMonoid B] {n : ℕ} (P : Blocks n)
    (f : Fin n → B) (b : B) (h a : Fin P.num) : B :=
  (if h=a then b else 0) + weight P f a

private theorem term_enter {B : Type*} [AddCommMonoid B] {n : ℕ} (q : ℤ) (P : Blocks n)
    (h : Fin P.num) (f : Fin (n+1) → B) :
    term q (enterBlock P h) f =
      -(size P h : ℤ) * termOn q P (shifted P (Fin.tail f) (f 0) h) := by
  unfold term termOn
  change (∏ a : Fin P.num, factor q _ _) = _
  calc
    _ = ∏ a : Fin P.num, (if a=h then -(size P h : ℤ) else 1) *
        factor q (size P a) (shifted P (Fin.tail f) (f 0) h a) := by
      apply Finset.prod_congr rfl
      intro a _
      have hc : size (enterBlock P h) a = (if h=a then 1 else 0) + size P a := by
        simp [size,enterBlock,Fin.sum_univ_succ]
      have hw : weight (enterBlock P h) f a = shifted P (Fin.tail f) (f 0) h a := by
        simp [weight,shifted,enterBlock,Fin.sum_univ_succ,Fin.tail]
      rw [hc,hw]
      by_cases eq : a=h
      · subst a
        simp [Nat.add_comm 1,factor_succ q _ (size_pos P h)]
      · simp [eq,Ne.symm eq]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

private def tally {α : Type*} (l : List α) (f : α → ℤ) : ℤ := (l.map f).sum

private theorem tally_flat {α β : Type*} (l : List α) (g : α → List β) (f : β → ℤ) :
    tally (l.flatMap g) f = tally l (fun a => tally (g a) f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [tally,List.flatMap_cons] at ih ⊢; exact ih

private theorem tally_sub {α : Type*} (l : List α) (f g : α → ℤ) :
    tally l (fun a => f a - g a) = tally l f - tally l g := by
  induction l with
  | nil => simp [tally]
  | cons a l ih => simp [tally] at ih ⊢; omega

private theorem tally_mul {α : Type*} (l : List α) (c : ℤ) (f : α → ℤ) :
    tally l (fun a => c*f a) = c * tally l f := by
  induction l with
  | nil => simp [tally]
  | cons a l ih => simp [tally,mul_add] at ih ⊢; exact ih

private theorem tally_sum {α : Type*} {n : ℕ} (l : List α) (g : Fin n → α → ℤ) :
    tally l (fun a => ∑ j, g j a) = ∑ j, tally l (g j) := by
  induction l with
  | nil => simp [tally]
  | cons a l ih => simp [tally,Finset.sum_add_distrib] at ih ⊢; exact ih

private theorem tally_refine {B : Type*} [AddCommMonoid B] {n : ℕ} (q : ℤ)
    (f : Fin (n+1) → B) (P : Blocks n) :
    tally (refinements P) (fun R => term q R f) =
      (if f 0=0 then q else 0) * term q P (Fin.tail f) -
        ∑ j, term q P (mergeWeight (Fin.tail f) (f 0) j) := by
  simp only [refinements,tally,List.map_cons,List.sum_cons,List.map_ofFn,List.sum_ofFn,term_new]
  let g := fun h => termOn q P (shifted P (Fin.tail f) (f 0) h)
  have hmerge (j : Fin n) : term q P (mergeWeight (Fin.tail f) (f 0) j) = g (P.tag j) := by
    apply congrArg (termOn q P)
    funext a
    exact weight_merge P _ _ j a
  simp_rw [hmerge]
  rw [sum_by_tag]
  have he (h : Fin P.num) : term q (enterBlock P h) f = -((size P h : ℤ)*g h) := by
    simpa [g] using term_enter q P h f
  simp only [Function.comp_apply,he,Finset.sum_neg_distrib,sub_eq_add_neg]

theorem coefficient_eq_partitions {B : Type*} [AddCommMonoid B] (q : ℤ)
    (n : ℕ) (f : Fin n → B) :
    coefficient q n f = ((catalogue n).map (fun P => term q P f)).sum := by
  change coefficient q n f = tally (catalogue n) _
  induction n with
  | zero => simp [coefficient,catalogue,empty,tally,term,termOn]
  | succ n ih =>
    rw [coefficient,catalogue,tally_flat]
    simp_rw [tally_refine]
    rw [tally_sub,tally_mul,tally_sum]
    simp_rw [ih]

private def singletonMark {n : ℕ} (P : Blocks n) : ℤ := if P.num=1 then 1 else 0

private theorem tally_refine_mark {n : ℕ} (P : Blocks (n+1)) :
    tally (refinements P) singletonMark = singletonMark P := by
  have hp : P.num ≠ 0 := Nat.ne_zero_of_lt (P.tag 0).isLt
  simp only [refinements, tally, List.map_cons,List.sum_cons,List.map_ofFn,List.sum_ofFn,
    Function.comp_apply,singletonMark,newBlock,enterBlock]
  by_cases h : P.num = 1 <;> simp [h,hp]

private theorem tally_mark (k : ℕ) : tally (catalogue (k+1)) singletonMark = 1 := by
  induction k with
  | zero => simp [catalogue,refinements,empty,tally,singletonMark,newBlock]
  | succ k ih => rw [catalogue,tally_flat]; simp_rw [tally_refine_mark]; exact ih

private theorem term_single {B : Type*} [AddCommMonoid B] {k : ℕ} (q : ℕ)
    (P : Blocks (k+1)) (hn : P.num=1) (f : Fin (k+1) → B) (hs : ∑ i, f i=0) :
    term q P f = (-1 : ℤ)^k * ((q * k.factorial : ℕ) : ℤ) := by
  rcases P with ⟨m,tag,onto⟩
  change m=1 at hn
  subst m
  have ht (i : Fin (k+1)) : tag i=0 := Subsingleton.elim _ _
  simp [term,termOn,size,weight,ht,factor,hs]
  ring

private theorem unsigned_as_prod (q : ℕ) (l : List ℕ) :
    (unsignedTerm q l : ℤ) =
      (l.map (fun b => (q : ℤ) * (b-1).factorial)).prod := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [unsignedTerm,ih]

private theorem term_many_dvd {B : Type*} [AddCommMonoid B] {n p q : ℕ}
    (hp : p.Prime) (hq : q ≠ 0) (ha : 0 < q.factorization p)
    (hd : n ≤ p ^ q.factorization p) (P : Blocks n) (hm : 2 ≤ P.num) (f : Fin n → B) :
    ((p ^ (q.factorization p + blockVal p n + 1) : ℕ) : ℤ) ∣ term q P f := by
  let bs := List.ofFn (size P)
  have hs : bs.sum=n := by simp [bs,List.sum_ofFn,size_sum]
  have hl : 2 ≤ bs.length := by simpa [bs] using hm
  have hb : ∀ v ∈ bs, 0<v := by
    intro v hv
    obtain ⟨h,rfl⟩ := List.mem_ofFn.mp hv
    exact size_pos P h
  have hdvd := nontrivial_partition_dvd hp hq ha bs hb (hs ▸ hd) hl
  rw [hs] at hdvd
  have hh : ((p ^ (q.factorization p + blockVal p n + 1) : ℕ) : ℤ) ∣
      ∏ h, (q : ℤ) * (size P h-1).factorial := by
    have hdvd' := Int.natCast_dvd_natCast.mpr hdvd
    rw [unsigned_as_prod] at hdvd'
    simpa [bs,List.map_ofFn,List.prod_ofFn] using hdvd'
  have ff (h : Fin P.num) : factor (q : ℤ) (size P h) (weight P f h) =
      (if weight P f h=0 then (-1 : ℤ)^(size P h-1) else 0) *
      ((q : ℤ) * (size P h-1).factorial) := by
    by_cases hb : weight P f h=0 <;> simp [factor,hb]; ring
  unfold term termOn
  simp_rw [ff]
  rw [Finset.prod_mul_distrib]
  exact dvd_mul_of_dvd_right hh _

theorem coefficient_not_zero {B : Type*} [AddCommMonoid B] {k p q : ℕ}
    (hp : p.Prime) (hq : q ≠ 0) (ha : 0 < q.factorization p)
    (hd : k+1 ≤ p ^ q.factorization p) (f : Fin (k+1) → B) (hs : ∑ i, f i=0) :
    coefficient q (k+1) f ≠ 0 := by
  let modl := p ^ (q.factorization p + blockVal p (k+1) + 1)
  let main : ℤ := (-1 : ℤ)^k * ((q * k.factorial : ℕ) : ℤ)
  have per (P : Blocks (k+1)) : (modl : ℤ) ∣ term q P f - main * singletonMark P := by
    by_cases him : P.num=1
    · simp [term_single q P him f hs,singletonMark,him,main]
    · have hp0 : 0 < P.num := Nat.zero_lt_of_lt (P.tag 0).isLt
      simpa [singletonMark,him,modl] using term_many_dvd hp hq ha hd P (by omega) f
  have hsum : (modl : ℤ) ∣ tally (catalogue (k+1))
      (fun P => term q P f - main * singletonMark P) := by
    apply List.dvd_sum
    intro z hz
    obtain ⟨P,_,rfl⟩ := List.mem_map.mp hz
    exact per P
  rw [tally_sub,tally_mul,tally_mark,mul_one] at hsum
  have hcoef := coefficient_eq_partitions (q : ℤ) _ f
  change coefficient q (k+1) f = tally (catalogue (k+1)) _ at hcoef
  rw [←hcoef] at hsum
  intro hz
  rw [hz,zero_sub,dvd_neg] at hsum
  have hbare : (modl : ℤ) ∣ ((q * k.factorial : ℕ) : ℤ) :=
    ((isUnit_neg_one.pow k).dvd_mul_left).mp hsum
  exact single_partition_not_dvd hp hq (k+1) (Int.natCast_dvd_natCast.mp hbare)

end PartitionBridge

theorem injectiveSum_ne_zero_iff_primePower {A R : Type*} [AddCommGroup A] [Fintype A]
    [CommRing R] [IsDomain R] [CharZero R] {p k : ℕ} (hp : p.Prime)
    (hd : p ∣ Fintype.card A) (hk : k+1 ≤ p ^ (Fintype.card A).factorization p)
    (f : Fin (k+1) → AddChar A R) :
    injectiveSum (fun i a => f i a) ≠ 0 ↔ ∑ i, f i=0 := by
  have hq : Fintype.card A ≠ 0 := Fintype.card_ne_zero
  have ha : 0 < (Fintype.card A).factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hp hq hd)
  rw [injectiveSum_character,Int.cast_ne_zero]
  constructor
  · contrapose!
    intro hs
    exact coefficient_zero_if_off _ _ f hs
  · exact PartitionBridge.coefficient_not_zero hp hq ha hk f

end PermanentLevel

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

variable {G J : Type*} [AddCommGroup G] [Fintype G] [Fintype J]

noncomputable def sameRowSum {k : ℕ} (t : Fin k → G × J → ℂ) : ℂ :=
  ∑ g : G, ∑ y : Fin k ↪ J, ∏ i, t i (g,y i)

private theorem separate_mixed {k : ℕ} (φ : Fin k → AddChar G ℂ) (u : Fin k → J → ℂ) :
    mixedSum (fun i x => φ i x.1 * u i x.2) =
    injectiveSum (fun i g => φ i g) * injectiveSum u := by
  simp only [mixedSum,injectiveSum,Finset.prod_mul_distrib,←Finset.mul_sum,←Finset.sum_mul]

private theorem separate_row {k : ℕ} (φ : Fin k → AddChar G ℂ) (u : Fin k → J → ℂ) :
    sameRowSum (fun i x => φ i x.1 * u i x.2) =
    (∑ g : G, (∑ i, φ i) g) * injectiveSum u := by
  simp only [sameRowSum,injectiveSum,AddChar.sum_apply,Finset.prod_mul_distrib,
    ←Finset.mul_sum,←Finset.sum_mul]

theorem transfer_to_rows_primePower {p k : ℕ} (hd : p ∣ Fintype.card G) (hp : p.Prime) (hk : k+1 ≤ p ^ (Fintype.card G).factorization p)
    (L : Submodule ℂ (G × J → ℂ))
    (hshift : ∀ t ∈ L, ∀ a : G, (fun x : G × J => t (x.1+a,x.2)) ∈ L)
    (hdiag : ∀ t ∈ L, mixedSum (fun _ : Fin (k+1) => t) = 0)
    (t : Fin (k+1) → G × J → ℂ) (ht : ∀ i, t i ∈ L) : sameRowSum t = 0 := by
  choose u hu hrec using fun i => row_character_decomposition L (t i) (hshift _ (ht i))
  have has (φ : Fin (k+1) → AddChar G ℂ) :
      sameRowSum (fun i x => φ i x.1 * u i (φ i) x.2) = 0 := by
    rw [separate_row,AddChar.sum_eq_ite]
    split_ifs with h
    · have hm := polarize_mixed L hdiag (fun i x => φ i x.1 * u i (φ i) x.2)
          (fun i => hu i (φ i))
      rw [separate_mixed] at hm
      have hn := (injectiveSum_ne_zero_iff_primePower hp hd hk φ).mpr h
      rw [(mul_eq_zero.mp hm).resolve_left hn,mul_zero]
    · exact zero_mul _
  calc
    sameRowSum t = ∑ φ : Fin (k+1) → AddChar G ℂ,
        sameRowSum (fun i x => φ i x.1 * u i (φ i) x.2) := by
      unfold sameRowSum
      simp only [hrec,Fintype.prod_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = 0 := Finset.sum_eq_zero (fun φ _ => has φ)

end PermanentLevel

namespace PermanentLevel

open Finset
open scoped Classical

private theorem subset_size_sum {n k : ℕ} (a : Finset (Fin n) → ℂ) :
    (∑ S : {S : Finset (Fin n) // S.card = k}, a S.val) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, a S := by
  rw [← Finset.sum_subtype _ (p := fun S : Finset (Fin n) => S.card = k)]
  intro S
  simp

theorem row_product_of_injective {G : Type*} [Fintype G] {n : ℕ}
    (hsum : ∀ (k : ℕ) (a : Fin n → ℂ),
      (∑ e : Fin k ↪ Fin n, ∏ i, a (e i)) =
        (k.factorial : ℂ) * ∑ S : {S : Finset (Fin n) // S.card=k}, ∏ j ∈ S.val, a j)
    (t : G × Fin n → ℂ)
    (hs : ∀ k, 1 ≤ k → k ≤ n → sameRowSum (fun _ : Fin k => t) = 0) :
    (∑ g : G, ∏ j : Fin n, (1+t (g,j))) = (Fintype.card G : ℂ) := by
  let term (g : G) (k : ℕ) :=
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ j ∈ S, t (g,j)
  have hz (k : ℕ) (hpos : 1≤k) (hle : k≤n) : ∑ g, term g k = 0 := by
    have ht := hs k hpos hle
    change (∑ g : G, ∑ e : Fin k ↪ Fin n, ∏ i, t (g,e i)) = 0 at ht
    have he (g : G) : (∑ e : Fin k ↪ Fin n, ∏ i, t (g,e i)) = (k.factorial : ℂ) * term g k := by
      rw [hsum k (fun j => t (g,j))]
      exact congrArg (fun x : ℂ => (k.factorial : ℂ) * x)
        (subset_size_sum (k := k) (fun S => ∏ j ∈ S, t (g,j)))
    simp_rw [he] at ht
    rw [←Finset.mul_sum] at ht
    exact (mul_eq_zero.mp ht).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have expanded (g : G) : (∏ j : Fin n, (1+t (g,j))) = ∑ k ∈ Finset.range (n+1), term g k := by
    rw [Finset.prod_one_add, Finset.sum_powerset]
    simp [term]
  simp_rw [expanded]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single 0]
  · simp [term]
  · intro k hk hne
    apply hz k (Nat.pos_of_ne_zero hne)
    simpa using Finset.mem_range.mp hk
  · simp

theorem row_product_transfer_primePower {G : Type*} [AddCommGroup G] [Fintype G] {p n : ℕ}
    (hd : p ∣ Fintype.card G) (hp : p.Prime) (hn : n ≤ p ^ (Fintype.card G).factorization p)
    (hsum : ∀ (k : ℕ) (a : Fin n → ℂ), (∑ e : Fin k ↪ Fin n, ∏ i, a (e i)) =
      (k.factorial : ℂ) * ∑ S : {S : Finset (Fin n) // S.card=k}, ∏ j ∈ S.val, a j)
    (L : Submodule ℂ (G × Fin n → ℂ))
    (hshift : ∀ t ∈ L, ∀ a : G, (fun x : G × Fin n => t (x.1+a,x.2)) ∈ L)
    (hdiag : ∀ k, 1≤k → k≤n → ∀ t ∈ L, mixedSum (fun _ : Fin k => t) = 0)
    (t : G × Fin n → ℂ) (ht : t ∈ L) :
    (∑ g : G, ∏ j : Fin n, (1+t (g,j))) = (Fintype.card G : ℂ) := by
  apply row_product_of_injective hsum
  intro k hk hkn
  obtain ⟨j,rfl⟩ : ∃ j, k = j+1 := ⟨k-1,by omega⟩
  exact transfer_to_rows_primePower hd hp (by omega) L hshift (hdiag _ hk hkn) _ (fun _ => ht)

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

private theorem subsums {k m n : ℕ} (t : Fin m × Fin n → ℂ) :
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

namespace PermanentLevel

/-- The checked L-gct-175 hypothesis, with the products indexed by columns. -/
def ColumnProductDimensionBound : Prop :=
  ∀ (p q : ℕ) (V : Submodule ℂ (Fin p × Fin q → ℂ))
    (lam : (Fin p × Fin q → ℂ) →ₗ[ℂ] ℂ),
    (fun _ => (1 : ℂ)) ∈ V → lam (fun _ => (1 : ℂ)) = 1 →
    (∀ x ∈ V, (∑ j, ∏ i, x (i,j)) = (q : ℂ) * lam x ^ p) →
    Module.finrank ℂ V ≤ q

private theorem homogeneous_column_identity {p q : ℕ}
    (L : Submodule ℂ (Fin p × Fin q → ℂ))
    (hl : ∀ t ∈ L, (∑ j, ∏ i, (1 + t (i,j))) = (q : ℂ))
    (t : Fin p × Fin q → ℂ) (ht : t ∈ L) (c : ℂ) :
    (∑ j, ∏ i, (c + t (i,j))) = (q : ℂ) * c ^ p := by
  classical
  let f (z : ℂ) := ∑ j, ∏ i, (z + t (i,j))
  let g (z : ℂ) := (q : ℂ) * z ^ p
  have he : Set.EqOn f g ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hn : z ≠ 0 := hz
    have hentry (i : Fin p) (j : Fin q) :
        z + t (i,j) = z * (1 + (z⁻¹ • t) (i,j)) := by
      simp [Pi.smul_apply, smul_eq_mul, mul_add, hn]
    simp only [f,g,hentry,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
      Fintype.card_fin,←Finset.mul_sum,hl _ (L.smul_mem z⁻¹ ht),mul_comm]
  exact he.closure (by dsimp [f]; fun_prop) (by dsimp [g]; fun_prop)
    ((dense_compl_singleton (0 : ℂ)) c)

theorem column_level_dimension (bound : ColumnProductDimensionBound) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (L : Submodule ℂ (Fin p × Fin q → ℂ))
    (hl : ∀ t ∈ L, (∑ j, ∏ i, (1 + t (i,j))) = (q : ℂ)) :
    Module.finrank ℂ L ≤ q - 1 := by
  classical
  let J : Fin p × Fin q → ℂ := fun _ => 1
  have hJ : J ∉ L := by
    intro hin
    have hzero := hl (-J) (L.neg_mem hin)
    have hn : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    exact hn (by simpa [J, zero_pow hp.ne'] using hzero.symm)
  obtain ⟨lam,hlam,hJlam⟩ := LinearMap.exists_extend_of_notMem (0 : L →ₗ[ℂ] ℂ) hJ 1
  let V := L ⊔ Submodule.span ℂ {J}
  have hJV : J ∈ V := Submodule.mem_sup_right (Submodule.mem_span_singleton_self J)
  have hv : ∀ x ∈ V, (∑ j, ∏ i, x (i,j)) = (q : ℂ) * lam x ^ p := by
    intro x hx
    obtain ⟨t,ht,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hllt : lam t = 0 := by
      exact LinearMap.congr_fun hlam (⟨t,ht⟩ : L)
    simpa [J, Pi.smul_apply, smul_eq_mul, hllt, hJlam, add_comm] using
      homogeneous_column_identity L hl t ht c
  have hdim := bound p q V lam hJV hJlam hv
  have hrank : Module.finrank ℂ V = Module.finrank ℂ L + 1 :=
    Submodule.finrank_sup_span_singleton hJ
  omega

private def matrixTranspose (p q : ℕ) :
    (Fin p × Fin q → ℂ) ≃ₗ[ℂ] (Fin q × Fin p → ℂ) where
  toFun t := fun ij => t (ij.2,ij.1)
  invFun t := fun ij => t (ij.2,ij.1)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem row_level_dimension (bound : ColumnProductDimensionBound) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (L : Submodule ℂ (Fin m × Fin n → ℂ))
    (hl : ∀ t ∈ L, (∑ i, ∏ j, (1 + t (i,j))) = (m : ℂ)) :
    Module.finrank ℂ L ≤ m - 1 := by
  let e := matrixTranspose m n
  have ht : ∀ y ∈ L.map e.toLinearMap,
      (∑ i, ∏ j, (1 + y (j,i))) = (m : ℂ) := by
    rintro _ ⟨x,hx,rfl⟩
    exact hl x hx
  have hd := column_level_dimension bound hn hm _ ht
  rwa [e.finrank_map_eq] at hd

end PermanentLevel

namespace PermanentLevel

open Fin.NatCast

theorem row_translations_of_rotation {n : ℕ} [NeZero n] {J : Type*}
    (L : Submodule ℂ (Fin n × J → ℂ))
    (hrot : ∀ t ∈ L, (fun x : Fin n × J => t (finRotate n x.1, x.2)) ∈ L) :
    ∀ t ∈ L, ∀ a : Fin n, (fun x : Fin n × J => t (x.1 + a, x.2)) ∈ L := by
  intro t ht a
  have shift (k : ℕ) : (fun x : Fin n × J => t (x.1 + (k : Fin n), x.2)) ∈ L := by
    induction k with
    | zero => simpa using ht
    | succ k ih =>
      have h := hrot (fun x : Fin n × J => t (x.1 + (k : Fin n), x.2)) ih
      simpa only [finRotate_apply, Nat.cast_succ, add_assoc, add_comm (1 : Fin n)] using h
  simpa using shift a.val

end PermanentLevel

namespace PermanentLevel

/-- Reindexing the rows of a rectangular matrix by a bijection. -/
private def reindexRows {I G J : Type*} (e : I ≃ G) : (I × J → ℂ) ≃ₗ[ℂ] (G × J → ℂ) where
  toFun t := fun x => t (e.symm x.1,x.2)
  invFun t := fun x => t (e x.1,x.2)
  left_inv := by intro t; funext x; simp
  right_inv := by intro t; funext x; simp
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

private theorem mixed_reindex {I G J : Type*} [Fintype I] [Fintype G] [Fintype J]
    (e : I ≃ G) {k : ℕ} (t : I × J → ℂ) :
    mixedSum (fun _ : Fin k => reindexRows (J := J) e t) =
    mixedSum (fun _ : Fin k => t) := by
  classical
  unfold mixedSum
  rw [← (Equiv.embeddingCongr (Equiv.refl (Fin k)) e).sum_comp]
  simp [reindexRows, Equiv.embeddingCongr_apply, Function.Embedding.congr]

/-- Every positive degree in the translated rectangular permanent vanishes. -/
def SubpermanentLevel {m n : ℕ} (L : Submodule ℂ (Fin m × Fin n → ℂ)) : Prop :=
  ∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (∑ R : Finset (Fin m), ∑ C : Finset (Fin n), if h : R.card=k ∧ C.card=k then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b))
      else 0) = 0

/-- A regular abelian group of row permutations in the prime-power coefficient range. -/
theorem regular_abelian_subpermanent_dimension {G : Type*} [Fintype G] [AddCommGroup G]
    {m n p : ℕ} (e : Fin m ≃ G) (hp : p.Prime) (hd : p ∣ m) (hn : 0 < n)
    (hrange : n ≤ p ^ m.factorization p) (L : Submodule ℂ (Fin m × Fin n → ℂ))
    (hshift : ∀ t ∈ L, ∀ a : G, (fun x : Fin m × Fin n => t (e.symm (e x.1+a),x.2)) ∈ L)
    (hlevel : SubpermanentLevel L) : Module.finrank ℂ L ≤ m-1 := by
  classical
  have hcard : Fintype.card G = m := by simpa using Fintype.card_congr e.symm
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  let E := reindexRows (J := Fin n) e
  let L' := L.map E.toLinearMap
  have hshift' : ∀ t ∈ L', ∀ a : G, (fun x : G × Fin n => t (x.1+a,x.2)) ∈ L' := by
    rintro _ ⟨t,ht,rfl⟩ a
    refine ⟨_, hshift t ht a, ?_⟩
    funext x
    simp [E,reindexRows]
  have hdiag : ∀ k, 1≤k → k≤n → ∀ v ∈ L', mixedSum (fun _ : Fin k => v)=0 := by
    rintro k hk hkn _ ⟨t,ht,rfl⟩
    exact (mixed_reindex e t).trans (mixedSum_zero_of_subpermanent t (hlevel t ht k hk hkn))
  apply row_level_dimension ProjectCore.L175 hm hn L
  intro t ht
  have hEt : E t ∈ L' := ⟨t,ht,rfl⟩
  have h0 := row_product_transfer_primePower (hcard ▸ hd) hp (hcard ▸ hrange)
    (fun k a => sum_embedding_prod (k := k) a) L' hshift' hdiag (E t) hEt
  calc
    _ = ∑ g : G, ∏ j : Fin n, (1+t (e.symm g,j)) :=
      (e.symm.sum_comp (fun i => ∏ j : Fin n, (1+t (i,j)))).symm
    _ = _ := by simpa [hcard,E,reindexRows] using h0

/-- Square matrices over a prime-power cyclic row orbit only need generator invariance. -/
theorem cyclic_prime_power_square_dimension {p a n : ℕ} (hp : p.Prime) (ha : 0 < a)
    (heq : n=p^a) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hrot : ∀ t ∈ L, (fun x : Fin n × Fin n => t (finRotate n x.1,x.2)) ∈ L)
    (hlevel : SubpermanentLevel L) : Module.finrank ℂ L ≤ n-1 := by
  have hn : 0 < n := heq ▸ pow_pos hp.pos _
  let : NeZero n := ⟨hn.ne'⟩
  apply regular_abelian_subpermanent_dimension (Equiv.refl (Fin n)) hp
    (heq ▸ dvd_pow_self p ha.ne') hn (by simp only [heq,Nat.factorization_pow_self hp,le_refl]) L
    (row_translations_of_rotation L hrot) hlevel

end PermanentLevel

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

theorem subpermanent_of_translated {m q : ℕ} (hq : q ≤ m)
    (L : Submodule ℂ (Fin m × Fin q → ℂ))
    (hL : ∀ T ∈ L, RectangularPermanent.value T=RectangularPermanent.value (0 : Fin m × Fin q → ℂ)) :
    SubpermanentLevel L := by
  intro T hT k hk hkm
  have h := RectangularPermanent.mixed_of_translated hq L hL hk (hkm.trans hq) T hT
  rw [mixedSum_subpermanent] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

theorem regular_abelian_translated_dimension {G : Type*} [Fintype G] [AddCommGroup G]
    {m q p : ℕ} (e : Fin m ≃ G) (hp : p.Prime) (hd : p ∣ m) (hn : 0 < q) (hq : q ≤ m)
    (hrange : q ≤ p ^ m.factorization p) (L : Submodule ℂ (Fin m × Fin q → ℂ))
    (hshift : ∀ t ∈ L, ∀ a : G, (fun x : Fin m × Fin q => t (e.symm (e x.1+a),x.2)) ∈ L)
    (hL : ∀ T ∈ L, RectangularPermanent.value T=RectangularPermanent.value (0 : Fin m × Fin q → ℂ)) :
    Module.finrank ℂ L ≤ m-1 :=
  regular_abelian_subpermanent_dimension e hp hd hn hrange L hshift (subpermanent_of_translated hq L hL)

theorem cyclic_prime_power_permanent {p a n : ℕ} (hp : p.Prime) (ha : 0 < a)
    (heq : n=p^a) (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hrot : ∀ T ∈ L, (fun x : Fin n × Fin n => T (finRotate n x.1,x.2)) ∈ L)
    (hL : ∀ T ∈ L, Matrix.permanent (Matrix.of fun i j => 1+T (i,j))=(n.factorial:ℂ)) :
    Module.finrank ℂ L ≤ n-1 := by
  apply cyclic_prime_power_square_dimension hp ha heq L hrot
  intro T hT k hk hkn
  have h := PermanentMaximal.translated_mixed_zero L hL hk hkn (fun _ : Fin k => T) (fun _ => hT)
  rw [mixedSum_subpermanent] at h
  exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end PermanentLevel
