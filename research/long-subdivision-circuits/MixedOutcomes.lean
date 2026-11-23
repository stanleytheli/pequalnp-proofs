import Mathlib
namespace Subdivision.MixedOutcomes
open Finset
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

def owners (O K : Finset E) (pick l r : E → V) := O.image pick ∪ K.image l ∪ K.image r
def miss (P : Finset E) (l r : E → V) (T : Finset V) :=
  P.filter (fun e => l e ∉ T ∨ r e ∉ T)

/-- The optimal terminal choice from the two physical path reductions equals
the endpoint charge in the mixed-parity vertex-cover calculation. -/
theorem terminal_iff (O P : Finset E) (l r : E → V) (k : ℕ) :
    (∃ (pick : E → V) (K : Finset E), K ⊆ P ∧
      (∀ e ∈ O,pick e=l e ∨ pick e=r e) ∧
      (owners O K pick l r).card + (P \ K).card ≤ k) ↔
    ∃ T : Finset V, (∀ e ∈ O,l e ∈ T ∨ r e ∈ T) ∧
      T.card + (miss P l r T).card ≤ k := by
  classical
  constructor
  · rintro ⟨pick,K,_,good,small⟩
    let T := owners O K pick l r
    have inc (e) (h : e ∈ O) : pick e ∈ T :=
      mem_union_left _ (mem_union_left _ (mem_image_of_mem pick h))
    have both (e) (h : e ∈ K) : l e ∈ T ∧ r e ∈ T :=
      ⟨mem_union_left _ (mem_union_right _ (mem_image_of_mem l h)),
       mem_union_right _ (mem_image_of_mem r h)⟩
    have sub : miss P l r T ⊆ P \ K := by
      intro e he
      obtain ⟨hp,hm⟩ := mem_filter.mp he
      exact mem_sdiff.mpr ⟨hp,fun h => hm.elim (fun hn => hn (both e h).1) (fun hn => hn (both e h).2)⟩
    refine ⟨T,?_,(Nat.add_le_add_left (card_le_card sub) _).trans small⟩
    intro e he
    rcases good e he with h|h
    · exact Or.inl (h ▸ inc e he)
    · exact Or.inr (h ▸ inc e he)
  · rintro ⟨T,meet,small⟩
    let pick (e : E) := if l e ∈ T then l e else r e
    let K := P.filter (fun e => l e ∈ T ∧ r e ∈ T)
    have hit (e) (h : e ∈ O) : pick e ∈ T := by
      by_cases hl : l e ∈ T
      · simpa [pick,hl] using hl
      · simpa [pick,hl] using (meet e h).resolve_left hl
    have sub : owners O K pick l r ⊆ T := by
      intro v hv
      rcases mem_union.mp hv with h|h
      · rcases mem_union.mp h with a|a
        · obtain ⟨e,he,rfl⟩ := mem_image.mp a
          exact hit e he
        · obtain ⟨e,he,rfl⟩ := mem_image.mp a
          exact (mem_filter.mp he).2.1
      · obtain ⟨e,he,rfl⟩ := mem_image.mp h
        exact (mem_filter.mp he).2.2
    have same : P \ K = miss P l r T := by ext e; simp [K,miss]; tauto
    refine ⟨pick,K,filter_subset _ _,?_,?_⟩
    · intro e _
      unfold pick
      split <;> simp_all
    · rw [same]
      exact (Nat.add_le_add_right (card_le_card sub) _).trans small

/-- Gate accounting after appending the two-gate disjoint anchor. Here K is
the set of even paths that left two pendants and the other even paths left none. -/
theorem anchor_lower (h odd even kept heads s terminal k : ℕ) (subset : kept ≤ even)
    (savings : 3*h+3*(even-kept)+terminal ≤ s+2)
    (essential : 2+odd+2*kept+heads ≤ terminal+1)
    (endpointCharge : k ≤ heads+(even-kept)) :
    3*h+odd+2*even+k ≤ s+1 := by omega
end Subdivision.MixedOutcomes
#print axioms Subdivision.MixedOutcomes.terminal_iff
#print axioms Subdivision.MixedOutcomes.anchor_lower
