import NormalizedPath

namespace SparseAffine
open Polynomial
noncomputable section

private theorem map_cont {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : R) (i : ℕ) : f (cont x i) = cont (f x) i := by
  induction i using Nat.twoStepInduction with
  | zero => simp [cont]
  | one => simp [cont]
  | more i ih ih' => simp [cont,ih,ih']

private theorem cont_at_zero {K : Type*} [CommRing K] (i : ℕ) : cont (0 : K) i = 1 := by
  induction i using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [cont]
  | more i ih ih' => simp [cont,ih']

/-- The continuants are nonzero in every characteristic: they all take value 1
at the origin. -/
theorem cont_variable_ne_zero (F : Type*) [Field F] (i : ℕ) :
    cont (RatFunc.X : RatFunc F) i ≠ 0 := by
  have hp : cont (X : F[X]) i ≠ 0 := by
    intro h
    have he := congrArg (evalRingHom (0 : F)) h
    simp only [map_zero,map_cont,coe_evalRingHom,eval_X,cont_at_zero,one_ne_zero] at he
  have ne := RatFunc.algebraMap_ne_zero hp
  simpa only [map_cont,RatFunc.algebraMap_X] using ne

private theorem const_plus_linear {k : Type*} [Field k] (a b : k) (ha : a ≠ 0) :
    RatFunc.C a + (RatFunc.X : RatFunc k)*RatFunc.C b ≠ 0 := by
  have h : (C a + X * C b : k[X]) ≠ 0 := by
    intro bad
    have z := congrArg (evalRingHom (0 : k)) bad
    exact ha (by simpa using z)
  simpa only [map_add,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X] using
    RatFunc.algebraMap_ne_zero h

theorem root_denom_ne_zero {k : Type*} [Field k] (c : k) (d : ℕ) (hd : d ≠ 0) :
    (RatFunc.X : RatFunc k)^d + RatFunc.C c ≠ 0 := by
  have h : ((X : k[X])^d + C c) ≠ 0 := by
    intro bad
    have hc := congrArg (fun P : k[X] => P.coeff d) bad
    simpa [coeff_C,hd,Ne.symm hd] using hc
  simpa only [map_add,map_pow,RatFunc.algebraMap_C,RatFunc.algebraMap_X] using
    RatFunc.algebraMap_ne_zero h

/-- Base-layer activities. -/
def activityList {K : Type*} [Field K] (t r s : K) : List K :=
  let B := cont t 6
  let C := cont t 5
  let A := t^6/C
  let a := (1-r-s)*B/(r*C)
  let b := (1-r-s)*A/(s*C)
  a :: (middle t (-B/C) ++ [b])

def pathScale {K : Type*} [Field K] (t r s : K) : K :=
  let B := cont t 6
  let C := cont t 5
  let A := t^6/C
  ((activityList t r s).map normFactor).prod * ((1-r-s)*A*B/(r*s*C))

private theorem const_ne {k : Type*} [Field k] {a : k} (h : a ≠ 0) :
    RatFunc.C a ≠ 0 := by
  exact (map_ne_zero_iff _ RatFunc.C_injective).mpr h

/-- Denominators and both path scalars are nonzero in the two parameter
families used by the global reduction. -/
theorem generic_activities {k : Type*} [Field k] (t : k)
    (ht : t ≠ 0) (hp : 1+t ≠ 0) (h4 : cont t 4 ≠ 0)
    (h5 : cont t 5 ≠ 0) (h6 : cont t 6 ≠ 0) (data : Bool) :
    let T : RatFunc k := RatFunc.C t
    let U : RatFunc k := RatFunc.X
    let S := if data then 1 else U
    (∀ z ∈ activityList T U S, 1+z ≠ 0) ∧ pathScale T U S ≠ 0 := by
  classical
  dsimp only
  let U : RatFunc k := RatFunc.X
  let T : RatFunc k := RatFunc.C t
  let c := cont t 5
  let b := cont t 6
  let a := t^6/c
  let C : RatFunc k := RatFunc.C c
  let B : RatFunc k := RatFunc.C b
  let A : RatFunc k := RatFunc.C a
  have hC : C ≠ 0 := const_ne h5
  have hB : B ≠ 0 := const_ne h6
  have ha : a ≠ 0 := div_ne_zero (pow_ne_zero _ ht) h5
  have hA : A ≠ 0 := const_ne ha
  have hU : U ≠ 0 := RatFunc.X_ne_zero
  have hm5 : cont T 5 = C := (map_cont RatFunc.C t 5).symm
  have hm6 : cont T 6 = B := (map_cont RatFunc.C t 6).symm
  have hAm : T^6/C = A := by simp [T,A,C,a,map_div₀]
  have hpb : 1+T ≠ 0 := by simpa [T] using const_ne hp
  have hcb : c-b ≠ 0 := by
    change cont t 5 - (cont t 5+t*cont t 4) ≠ 0
    simpa using mul_ne_zero ht h4
  have hCB : C-B ≠ 0 := by simpa [C,B] using const_ne hcb
  have hmid : 1 + -B/C ≠ 0 := by
    intro he
    apply hCB
    field_simp at he
    linear_combination he
  have hl (z : k) (nz : z ≠ 0) :
      U*C + (1-U-U) * RatFunc.C z ≠ 0 := by
    have h := const_plus_linear z (c-z-z) nz
    convert h using 1 <;> simp [C,U] <;> ring
  have hd0 : 1-U-U ≠ 0 := by
    have h := const_plus_linear (1 : k) (-1-1) one_ne_zero
    convert h using 1 <;> simp [U] <;> ring
  have hd1 : 1-U-1 ≠ 0 := by simpa using neg_ne_zero.mpr hU
  have hr1 : C-U*A ≠ 0 := by
    have h := const_plus_linear c (-a) h5
    simpa [C,U,A,sub_eq_add_neg] using h
  have hproper (s : RatFunc k) (hs : s ≠ 0) (delta : 1-U-s ≠ 0)
      (hlft : 1+(1-U-s)*B/(U*C) ≠ 0) (hrgt : 1+(1-U-s)*A/(s*C) ≠ 0) :
      (∀ z ∈ activityList T U s, 1+z ≠ 0) ∧ pathScale T U s ≠ 0 := by
    have good : ∀ z ∈ activityList T U s, 1+z ≠ 0 := by
      intro z hz
      simp only [activityList,hm6,hm5,hAm,middle,List.mem_cons,List.mem_append,
        List.mem_singleton,List.not_mem_nil,or_false] at hz
      aesop
    refine ⟨good,?_⟩
    simp only [pathScale, hm5, hm6, hAm]
    apply mul_ne_zero
    · apply List.prod_ne_zero
      intro hz
      obtain ⟨v,hv,he⟩ := List.mem_map.mp hz
      exact (inv_ne_zero (good v hv)) he
    · exact div_ne_zero (mul_ne_zero (mul_ne_zero delta hA) hB)
        (mul_ne_zero (mul_ne_zero hU hs) hC)
  cases data with
  | false =>
    apply hproper U hU hd0
    · intro he; apply hl b h6; field_simp at he; linear_combination he
    · intro he; apply hl a ha; field_simp at he; linear_combination he
  | true =>
    apply hproper 1 one_ne_zero hd1
    · intro he
      apply hCB
      field_simp at he
      apply mul_left_cancel₀ hU
      linear_combination he
    · intro he; apply hr1; field_simp at he; linear_combination he

end
end SparseAffine
#print axioms SparseAffine.cont_variable_ne_zero
#print axioms SparseAffine.root_denom_ne_zero
#print axioms SparseAffine.generic_activities
