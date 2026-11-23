import AffineObstruction
import PermutationTour
namespace GraphProbability.Hamiltonian
open Finset
/-- Any cube-preserving affine Bernoulli graph representation of the positive
support of directed Hamiltonicity has at least 2^m-2 physical edges. -/
private theorem cuts_lower {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    {m : ℕ} (hm : 2 ≤ m) (left right : E→W) (constant : W→ℝ) (weight : W→(Fin m×Fin m)→ℝ)
    (range : ∀ v M, 0≤affine (constant v) (weight v) M ∧ affine (constant v) (weight v) M≤1)
    (fail : ∀ S : Finset (Fin m), S.Nonempty → (∃ i,i∉S) →
      ¬0<probability left right (fun v=>affine (constant v) (weight v) (cutEdges S)))
    (pass : ∀ M, HasTour M → 0<probability left right (fun v=>affine (constant v) (weight v) M)) :
    2^m-2 ≤ Fintype.card E := by
  classical
  let C : Finset (Finset (Fin m)) := (univ.erase ∅).erase univ
  have ce (S : C) : S.val≠univ ∧ S.val≠∅ := by
    have h : S.val∈(univ.erase ∅).erase univ := S.property
    exact ⟨(mem_erase.mp h).1,(mem_erase.mp (mem_erase.mp h).2).1⟩
  have some (S : C) := Finset.nonempty_iff_ne_empty.mpr (ce S).2
  have out (S : C) : ∃ v,v∉S.val := by
    by_contra! all
    exact (ce S).1 (eq_univ_of_forall all)
  have bound := lower_of_join_family left right constant weight (fun S : C=>cutEdges S.val) range
    (fun S=>fail S.val (some S) (out S))
    (fun S T ne=>pass _ (tour_union S.val T.val (some S) (out S) (fun h=>ne (Subtype.ext h))))
  have hn : (univ : Finset (Fin m))≠∅ := by
    intro empty
    have h : (⟨0,by omega⟩ : Fin m)∈univ:=mem_univ _
    rw [empty] at h
    simpa using h
  have un : (univ : Finset (Fin m))∈(univ : Finset (Finset (Fin m))).erase ∅ := by simp [hn]
  have card : C.card=2^m-2 := by
    rw [show C=(univ.erase ∅).erase univ from rfl,card_erase_of_mem un,card_erase_of_mem (mem_univ _)]
    simp
    omega
  simpa only [Fintype.card_coe,card] using bound

theorem two_pow_sub_two {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    {m : ℕ} (hm : 2 ≤ m) (left right : E→W) (constant : W→ℝ) (weight : W→(Fin m×Fin m)→ℝ)
    (range : ∀ v M, 0≤affine (constant v) (weight v) M ∧ affine (constant v) (weight v) M≤1)
    (models : ∀ M, HasTour M ↔ 0<probability left right (fun v=>affine (constant v) (weight v) M)) :
    2^m-2 ≤ Fintype.card E :=
  cuts_lower hm left right constant weight range
    (fun S h1 h2 h=>cut_has_no_tour S h1 h2 ((models _).mpr h)) (fun M=>(models M).mp)

/-- Same physical-edge lower bound using the transitive-permutation definition. -/
theorem permutation_two_pow_sub_two {W E : Type*} [Fintype W] [DecidableEq W] [Fintype E]
    {m : ℕ} (hm : 2 ≤ m) (left right : E→W) (constant : W→ℝ) (weight : W→(Fin m×Fin m)→ℝ)
    (range : ∀ v M, 0≤affine (constant v) (weight v) M ∧ affine (constant v) (weight v) M≤1)
    (models : ∀ M, HasCyclePermutation M ↔ 0<probability left right (fun v=>affine (constant v) (weight v) M)) :
    2^m-2 ≤ Fintype.card E :=
  cuts_lower hm left right constant weight range
    (fun S h1 h2 h=>no_perm_on_cut S h1 h2 ((models _).mpr h))
    (fun M h=>(models M).mp (permutation_of_tour _ h))
end GraphProbability.Hamiltonian
#print axioms GraphProbability.Hamiltonian.two_pow_sub_two
#print axioms GraphProbability.Hamiltonian.permutation_two_pow_sub_two
