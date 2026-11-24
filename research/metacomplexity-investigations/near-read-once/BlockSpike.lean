import Overlap

namespace NearReadOnce

open Finset

/-- Adjoin a single positive term `M` to a read-once disjunction of disjoint
block conjunctions. If `M` contains at least one but omits at least one input
of every block, the excess over the ordinary baseline is at least `t-1`. -/
theorem block_spike_gate_bound {n g t : Nat} {C : Circuit n g} (E : Eval C)
    (ht : 0 < t) (block : Fin t → Finset (Fin n)) (M : Finset (Fin n))
    (separate : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (selected omitted : Fin t → Fin n)
    (sel_block : ∀ i, selected i ∈ block i) (sel_M : ∀ i, selected i ∈ M)
    (omit_block : ∀ i, omitted i ∈ block i) (omit_M : ∀ i, omitted i ∉ M)
    (computes : ∀ x : Finset (Fin n), E.val x C.root = true ↔
      (∃ i, block i ⊆ x) ∨ M ⊆ x) :
    n + t ≤ g + 2 := by
  classical
  let Z : Finset (Fin n) := univ.image selected
  have hsel (i : Fin t) : selected i ∈ Z := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have unique_sel : Function.Injective selected := by
    intro i j hij
    by_contra hne
    exact (disjoint_left.mp (separate i j hne)) (sel_block i) (hij ▸ sel_block j)
  have hMZ : Z ⊆ M := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact sel_M i
  have hfalse (x : Finset (Fin n))
      (no : ¬ ((∃ i, block i ⊆ x) ∨ M ⊆ x)) : E.val x C.root = false := by
    cases h : E.val x C.root with
    | false => rfl
    | true => exact False.elim (no ((computes x).mp h))
  have home : E.val M C.root = true := (computes M).mpr (Or.inr (Subset.rfl))
  have min_one (k : Fin n) (hk : k ∈ M) : E.val (M.erase k) C.root = false := by
    apply hfalse
    rintro (⟨i,hi⟩ | allM)
    · exact omit_M i (mem_of_mem_erase (hi (omit_block i)))
    · exact (notMem_erase k M) (allM hk)
  have zero : E.val (univ \ Z) C.root = false := by
    apply hfalse
    rintro (⟨i,hi⟩ | allM)
    · exact (mem_sdiff.mp (hi (sel_block i))).2 (hsel i)
    · let i : Fin t := ⟨0, ht⟩
      exact (mem_sdiff.mp (allM (sel_M i))).2 (hsel i)
  have min_zero (k : Fin n) (hk : k ∈ Z) : E.val (insert k (univ \ Z)) C.root = true := by
    obtain ⟨i,_,rfl⟩ := mem_image.mp hk
    apply (computes _).mpr
    apply Or.inl
    refine ⟨i,?_⟩
    intro v hv
    by_cases hvi : v = selected i
    · simp [hvi]
    · apply mem_insert_of_mem
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro hvZ
      obtain ⟨j,_,rfl⟩ := mem_image.mp hvZ
      by_cases hji : j = i
      · exact hvi (hji ▸ rfl)
      · exact (disjoint_left.mp (separate j i hji)) (sel_block j) hv
  have h := minterm_maxterm_gate_bound E M Z home min_one zero min_zero
  have cardZ : Z.card = t := by
    simpa [Z] using card_image_of_injective (Finset.univ : Finset (Fin t)) unique_sel
  rwa [Finset.inter_eq_right.mpr hMZ, cardZ] at h

end NearReadOnce

#print axioms NearReadOnce.block_spike_gate_bound
