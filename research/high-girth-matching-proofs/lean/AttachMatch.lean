import AttachDegree
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace SparsePermanent.Attach
open Finset
variable {I : Type} [Fintype I]

/-- Removing one chosen edge from a finite cubic bipartite graph leaves a
perfect matching. Hall's inequalities survive since the old degrees are three
on both sides and just one incidence is lost. -/
theorem matching_avoids (K : I→I→Prop) (x y : I)
    (L : ∀ i,leftDeg K i=3) (R : ∀ j,rightDeg K j=3) :
    ∃ p : Equiv.Perm I, (∀ i,K i (p i)) ∧ p x≠y := by
  classical
  let row (a : I) := univ.filter (K a)
  let col (b : I) := univ.filter (K · b)
  let t (a : I) := if a=x then (row a).erase y else row a
  have rc (a : I) : (row a).card=3 := by
    simpa [row,leftDeg,Nat.card_eq_fintype_card,Fintype.card_subtype] using L a
  have cc (b : I) : (col b).card=3 := by
    simpa [col,rightDeg,Nat.card_eq_fintype_card,Fintype.card_subtype] using R b
  have tt (a b : I) (hb : b∈t a) : K a b := by
    by_cases h : a=x
    · have z : b∈(row a).erase y := by simpa [t,h] using hb
      exact (mem_filter.mp (mem_of_mem_erase z)).2
    · exact (mem_filter.mp (by simpa [t,h] using hb : b∈row a)).2
  have hall (S : Finset I) : S.card≤(S.biUnion t).card := by
    let N:=S.biUnion t
    have one (a : I) : 3≤(t a).card+(if x=a then 1 else 0) := by
      by_cases h : a=x
      · subst a
        rw [if_pos rfl,show t x=(row x).erase y by simp [t]]
        have hi:=rc x
        by_cases hy : y∈row x
        · rw [card_erase_of_mem hy]; omega
        · rw [erase_eq_of_notMem hy]; omega
      · simp [t,h,Ne.symm h,rc]
    have loss : 3*S.card≤(∑ a∈S,(t a).card)+1 := by
      calc
        _ = ∑ _a∈S,3 := by simp [Nat.mul_comm]
        _ ≤ ∑ a∈S,((t a).card+(if x=a then 1 else 0)) := sum_le_sum (fun a _=>one a)
        _ ≤ _ := by rw [sum_add_distrib]; simp only [sum_ite_eq]; split <;> omega
    have maxN : (∑ a∈S,(t a).card)≤3*N.card := by
      calc
        _ = ∑ a∈S, ∑ b∈N, if b∈t a then 1 else 0 := by
          apply sum_congr rfl
          intro a ha
          rw [sum_boole]
          have eq : N.filter (·∈t a)=t a := by
            ext b
            simp only [mem_filter]
            exact ⟨And.right,fun hb=>⟨mem_biUnion.mpr ⟨a,ha,hb⟩,hb⟩⟩
          simp [eq]
        _ = ∑ b∈N, ∑ a∈S, if b∈t a then 1 else 0 := sum_comm
        _ ≤ ∑ _b∈N,3 := by
          apply sum_le_sum
          intro b _
          rw [sum_boole,←cc b]
          apply card_le_card
          intro a ha
          exact mem_filter.mpr ⟨mem_univ _,tt a b (mem_filter.mp ha).2⟩
        _ = _ := by simp [Nat.mul_comm]
    change S.card≤N.card
    omega
  obtain ⟨f,hf,hmem⟩:= (all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨Equiv.ofBijective f hf.bijective_of_finite,fun a=>tt _ _ (hmem a),?_⟩
  intro bad
  change f x=y at bad
  have tab:=hmem x
  simpa [t,bad] using tab

end SparsePermanent.Attach
#print axioms SparsePermanent.Attach.matching_avoids
