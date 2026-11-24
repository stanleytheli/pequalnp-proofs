import Mathlib
namespace PositiveCornerClosure
open Finset MvPolynomial
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

noncomputable def cornerBasis (b : I→Bool) : MvPolynomial I R :=
  ∏ i,(if b i then X i else 1-X i)

noncomputable def interpolant (f : (I→Bool)→R) : MvPolynomial I R :=
  ∑ b, C (f b) * cornerBasis b

theorem eval_cornerBasis (b x : I→Bool) :
    eval (fun i=>if x i then 1 else 0) (cornerBasis b : MvPolynomial I R) =
      if b=x then 1 else 0 := by
  classical
  unfold cornerBasis
  rw [map_prod]
  by_cases same : b=x
  · subst b
    simp only [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _
    cases hx : x i <;> simp [hx]
  · rw [if_neg same]
    have witness : ∃ i,b i≠x i := Function.ne_iff.mp same
    obtain ⟨i,ne⟩:=witness
    apply Finset.prod_eq_zero (mem_univ i)
    cases hb : b i <;> cases hx : x i <;> simp_all

theorem eval_interpolant (f : (I→Bool)→R) (x : I→Bool) :
    eval (fun i=>if x i then 1 else 0) (interpolant f) = f x := by
  classical
  unfold interpolant
  simp [map_sum,eval_cornerBasis]

theorem map_interpolant (h : R→+*S) (f : (I→Bool)→R) :
    MvPolynomial.map h (interpolant f)=interpolant (fun b=>h (f b)) := by
  classical
  simp only [interpolant,map_sum,map_mul,map_C]
  apply sum_congr rfl
  intro b _
  congr 1
  unfold cornerBasis
  rw [map_prod]
  apply prod_congr rfl
  intro i _
  cases hb : b i <;> simp [hb]

theorem scalar_interpolant (r : R) (f : (I→Bool)→R) :
    interpolant (fun b=>r*f b) = C r * interpolant f := by
  classical
  simp [interpolant,Finset.mul_sum,mul_assoc]

/-- A simultaneous corner factor gives a regular normalized canonical
multilinear representative, with the expected constant polynomial at t=0. -/
theorem regular_interpolant {K : Type*} [CommRing K] (B : ℕ)
    (f g : (I→Bool)→Polynomial K) (atCorners : ∀ b,f b=Polynomial.X^B*g b) :
    ∃ P : MvPolynomial I (Polynomial K),
      interpolant f = C (Polynomial.X^B)*P ∧
      MvPolynomial.map (Polynomial.evalRingHom 0) P=interpolant (fun b=>(g b).eval 0) := by
  refine ⟨interpolant g,?_,?_⟩
  · rw [show f=(fun b=>Polynomial.X^B*g b) from funext atCorners,scalar_interpolant]
  · exact map_interpolant _ _

end PositiveCornerClosure
#print axioms PositiveCornerClosure.eval_interpolant
#print axioms PositiveCornerClosure.regular_interpolant
