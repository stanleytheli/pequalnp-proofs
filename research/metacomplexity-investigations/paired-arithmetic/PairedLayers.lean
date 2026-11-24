import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace AlgebraicMeta.Paired
open Finset MvPolynomial

/-- Ports (primary, mate) are locally forbidden to be simultaneously one.
The next constraint connects each mate to the next primary under a permutation. -/
def TwoMatchings {A : Type*} (τ : Equiv.Perm A) (p q : A → Bool) : Prop :=
  ∀ i, (p i=true → q i=false) ∧ (q i=true ∨ p (τ i)=true)

/-- Across any finite permutation, the two binary matching layers force one
high bit per positional pair and make the logical primary constant on cycles. -/
theorem two_matchings_iff {A : Type*} [Finite A] (τ : Equiv.Perm A) (p q : A → Bool) :
    TwoMatchings τ p q ↔ (∀ i, q i=(!p i)) ∧ (∀ i, p (τ i)=p i) := by
  classical
  constructor
  · intro h
    have forward (i) (hi : p i=true) : p (τ i)=true := by
      rcases (h i).2 with yes|yes
      · rw [(h i).1 hi] at yes
        contradiction
      · exact yes
    let step (x : {i // p i=true}) : {i // p i=true} := ⟨τ x.1,forward x.1 x.2⟩
    have inject : Function.Injective step := fun _ _ e => Subtype.ext (τ.injective (congrArg Subtype.val e))
    have onto := Finite.surjective_of_injective inject
    have backward (i) (hi : p (τ i)=true) : p i=true := by
      obtain ⟨j,hj⟩ := onto ⟨τ i,hi⟩
      have e : j.1=i := τ.injective (congrArg Subtype.val hj)
      exact e ▸ j.2
    have same (i) : p (τ i)=p i := by
      cases e : p i <;> cases f : p (τ i) <;> first | rfl | simp_all
    refine ⟨fun i=>?_,same⟩
    rcases h i with ⟨neg,other⟩
    rw [same] at other
    cases eq : p i <;> simp_all
  · rintro ⟨mate,stable⟩ i
    rw [mate,stable]
    cases p i <;> simp

noncomputable def mono {I R : Type*} [Fintype I] [CommSemiring R] (a : I → Bool) :
    MvPolynomial (I × Bool) R := ∏ i, X (i,a i)

noncomputable def pairedPoly {I R : Type*} [Fintype I] [CommSemiring R] (valid : Finset (I → Bool)) :
    MvPolynomial (I × Bool) R := ∑ a ∈ valid, mono a

def selected {I R : Type*} [Zero R] [One R] (a : I → Bool) (j : I × Bool) : R :=
  if j.2=a j.1 then 1 else 0

open Classical in
theorem selected_mono {I R : Type*} [Fintype I] [CommSemiring R] (a b : I → Bool) :
    eval (selected (R:=R) a) (mono b) = if b=a then 1 else 0 := by
  classical
  simp only [mono,map_prod,eval_X,selected]
  by_cases same : b=a
  · subst b
    simp
  · have bad : ∃i, b i ≠ a i := by
      by_contra! all
      exact same (funext all)
    obtain ⟨i,hi⟩ := bad
    simp only [same,ite_false]
    exact prod_eq_zero (mem_univ i) (by simp [hi])

open Classical in
theorem selected_sum {I R : Type*} [Fintype I] [CommSemiring R] (valid : Finset (I → Bool)) (a : I → Bool) :
    eval (selected (R:=R) a) (pairedPoly valid) = if a∈valid then 1 else 0 := by
  classical
  simp only [pairedPoly,map_sum,selected_mono]
  by_cases h : a∈valid <;> simp [h]

def Essential {I R : Type*} [CommSemiring R] (f : MvPolynomial I R) (v : I) : Prop :=
  ∃ x y : I → R, (∀ j, j≠v → x j=y j) ∧ eval x f ≠ eval y f

theorem selected_essential {I R : Type*} [Fintype I] [CommSemiring R] [Nontrivial R]
    (valid : Finset (I → Bool)) {a : I → Bool} (h : a∈valid) (i : I) :
    Essential (pairedPoly (R:=R) valid) (i,a i) := by
  classical
  let cut (j : I × Bool) : R := if j.1=i then 0 else selected a j
  refine ⟨selected a,cut,?_,?_⟩
  · rintro ⟨j,b⟩ ne
    by_cases e : j=i
    · subst j
      have bn : b≠a i := by intro eq; exact ne (by rw [eq])
      simp [cut,selected,bn]
    · simp [cut,e]
  · have vanish (b : I → Bool) : eval cut (mono (R:=R) b) = 0 := by
      simp only [mono,map_prod,eval_X]
      exact prod_eq_zero (mem_univ i) (by simp [cut])
    rw [selected_sum]
    simp [h,pairedPoly,vanish]

/-- Two distinct accepted exponent vectors force strictly more than the
ordinary one-monomial minimum number of essential variables. -/
theorem two_models_essential {I R : Type*} [Fintype I] [CommSemiring R] [Nontrivial R]
    (valid : Finset (I → Bool)) {a b : I → Bool} (ha : a∈valid) (hb : b∈valid) (ne : a≠b) :
    Nonempty (Option I ↪ {w // Essential (pairedPoly (R:=R) valid) w}) := by
  classical
  have diff : ∃ i, b i ≠ a i := by
    by_contra! all
    exact ne (funext all).symm
  obtain ⟨i,hi⟩ := diff
  let f : Option I → {w // Essential (pairedPoly (R:=R) valid) w}
    | none => ⟨(i,b i),selected_essential valid hb i⟩
    | some j => ⟨(j,a j),selected_essential valid ha j⟩
  refine ⟨⟨f,?_⟩⟩
  intro u w e
  have e1 := congrArg (fun s => s.1.1) e
  have e2 := congrArg (fun s => s.1.2) e
  cases u <;> cases w <;> simp_all [f]

end AlgebraicMeta.Paired
#print axioms AlgebraicMeta.Paired.two_matchings_iff
#print axioms AlgebraicMeta.Paired.selected_essential
#print axioms AlgebraicMeta.Paired.two_models_essential
