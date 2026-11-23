import FrobeniusPermanent
namespace PermanentMargins
open Finset PermanentLevel

noncomputable def fieldMargins (K : Type*) [Field K] (m n : ℕ) :
    (Fin (m+1) × Fin (n+1) → K) →ₗ[K] (Fin m → K) × (Fin n → K) where
  toFun x := (fun i => ∑ j, x (i.succ,j),fun j => ∑ i, x (i,j.succ))
  map_add' x y := by ext k <;> simp [Finset.sum_add_distrib]
  map_smul' c x := by ext k <;> simp [Finset.mul_sum]

theorem ordered_coefficients {K R : Type*} [Field K] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (ι : K →+* ℂ) (ρ : K →+* R) {m n : ℕ}
    (L : Submodule ℂ (Fin (m+1) × Fin (n+1) → ℂ))
    (U : Submodule K (Fin (m+1) × Fin (n+1) → K))
    (contained : ∀ x∈U, (fun ij => ι (x ij))∈L)
    (first : ∀ x∈L, mixedSum (fun _ : Fin 1 => x)=0)
    (second : ∀ x∈L, ∀ y∈L, mixedSum ![x,y]=0) :
    Module.finrank K U ≤ m+n := by
  classical
  let f := (fieldMargins K m n).comp U.subtype
  have zero (x : U) (hx : f x=0) : x=0 := by
    let y : L := ⟨fun ij => ι (x.val ij),contained x.val x.property⟩
    have rs (i : Fin m) : (∑ j, x.val (i.succ,j))=0 := congrFun (congrArg Prod.fst hx) i
    have cs (j : Fin n) : (∑ i, x.val (i,j.succ))=0 := congrFun (congrArg Prod.snd hx) j
    have hy : y ∈ LinearMap.ker ((margins m n).comp L.subtype) := by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · funext i
        change (∑ j, ι (x.val (i.succ,j)))=0
        rw [←map_sum,rs,map_zero]
      · funext j
        change (∑ i, ι (x.val (i,j.succ)))=0
        rw [←map_sum,cs,map_zero]
    have rad := LinearMap.mem_ker.mp (marginal_radical L first second hy)
    have sumC := DFunLike.congr_fun rad y
    change (∑ i, ∑ j, ι (x.val (i,j)) * ι (x.val (i,j)))=0 at sumC
    have sumK : (∑ i, ∑ j, x.val (i,j) * x.val (i,j))=0 := by
      apply ι.injective
      simpa only [map_sum,map_mul,map_zero] using sumC
    have sumR := congrArg ρ sumK
    simp only [map_sum,map_mul,map_zero] at sumR
    have rows (i : Fin (m+1)) : (∑ j, ρ (x.val (i,j)) * ρ (x.val (i,j)))=0 :=
      (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => mul_self_nonneg _))).mp sumR i (mem_univ _)
    apply Subtype.ext
    funext ij
    apply ρ.injective
    change ρ (x.val (ij.1,ij.2))=ρ 0
    rw [map_zero]
    have h := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mp (rows ij.1) ij.2 (mem_univ _)
    exact mul_self_eq_zero.mp h
  have inj : Function.Injective f := by
    intro x y he
    exact sub_eq_zero.mp (zero (x-y) (by rw [map_sub,he,sub_self]))
  simpa using LinearMap.finrank_le_finrank_of_injective inj

theorem five_ordered_coefficients {K R : Type*} [Field K] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (ι : K →+* ℂ) (ρ : K →+* R) (L : Submodule ℂ (Fin 5 × Fin 5 → ℂ))
    (U : Submodule K (Fin 5 × Fin 5 → K)) (contained : ∀ x∈U, (fun ij => ι (x ij))∈L)
    (level : ∀ t∈L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1+t (i,f i)))=120) :
    Module.finrank K U ≤ 8 := by
  have perm (T) (hT : T∈L) : PermanentMaximal.permAt T = (Nat.factorial 5 : ℕ) := by
    rw [permAt_eq_posted,level T hT]; norm_num [Nat.factorial]
  apply ordered_coefficients ι ρ (m:=4) (n:=4) L U contained
  · intro x hx
    exact PermanentMaximal.translated_mixed_zero L perm (k:=1) (by decide) (by decide) _ (fun _ => hx)
  · intro x hx y hy
    apply PermanentMaximal.translated_mixed_zero L perm (k:=2) (by decide) (by decide)
    intro i
    fin_cases i <;> first | exact hx | exact hy
end PermanentMargins
#print axioms PermanentMargins.ordered_coefficients
#print axioms PermanentMargins.five_ordered_coefficients
