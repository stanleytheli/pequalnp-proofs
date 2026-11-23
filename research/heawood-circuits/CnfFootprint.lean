import Mathlib
namespace CnfFootprint
open Finset
section Generic
variable {V E N : Type*}

/-- Every selected positive pair hits every clause, and each supplied negative row misses a clause. -/
def separates (u v : E → V) (negative : N → Set V) {k : ℕ} (clause : Fin k → Set V) : Prop :=
  (∀ e c, u e∈clause c ∨ v e∈clause c) ∧ (∀ n, ∃ c, Disjoint (clause c) (negative n))

/-- Coloring the incompatibility graph on the negative rows. -/
theorem clauses_iff_coloring (u v : E → V) (negative : N → Set V) (k : ℕ) :
    (∃ clause : Fin k → Set V, separates u v negative clause) ↔
    ∃ color : N → Fin k, ∀ i j e, color i=color j → u e∈negative i → v e∉negative j := by
  classical
  constructor
  · rintro ⟨clause,hits,misses⟩
    choose color hc using misses
    refine ⟨color,?_⟩
    intro i j e hij hi hj
    rcases hits e (color i) with h|h
    · exact Set.disjoint_left.mp (hc i) h hi
    · rw [hij] at h
      exact Set.disjoint_left.mp (hc j) h hj
  · rintro ⟨color,hc⟩
    let clause (c : Fin k) : Set V := {w | ∀ n, color n=c → w∉negative n}
    refine ⟨clause,?_,?_⟩
    · intro e c
      by_contra! bad
      obtain ⟨a,ha,ua⟩ : ∃ a, color a=c ∧ u e∈negative a := by
        simpa [clause] using bad.1
      obtain ⟨b,hb,vb⟩ : ∃ b, color b=c ∧ v e∈negative b := by
        simpa [clause] using bad.2
      exact hc a b e (ha.trans hb.symm) ua vb
    · intro n
      exact ⟨color n,Set.disjoint_left.mpr (fun _ h hn => h n rfl hn)⟩

end Generic

namespace Heawood
abbrev V := Fin 14
abbrev E := Fin 21
abbrev N := Fin 37
def u (i : E) : V := ([0,1,3,0,2,6,1,5,6,0,4,5,3,4,6,2,3,5,1,2,4] : List V).getD i.val 0
def v (i : E) : V := ([7,7,7,8,8,8,9,9,9,10,10,10,11,11,11,12,12,12,13,13,13] : List V).getD i.val 0
def row (i : N) : ℕ := ([127,244,314,432,541,660,792,1102,1220,1290,1548,2087,2212,2338,2565,3078,3716,4179,4304,4370,4625,5008,5186,6147,7426,8297,8416,8488,8713,9288,9992,10273,10656,12353,13504,14849,16256] : List ℕ).getD i.val 0
def neg (i : N) : Set V := {w | (row i).testBit w.val=true}
instance (i : N) (w : V) : Decidable (w∈neg i) := inferInstanceAs (Decidable ((row i).testBit w.val=true))
def cross (i j : N) (e : E) : Prop := (u e∈neg i ∧ v e∈neg j) ∨ (u e∈neg j ∧ v e∈neg i)
instance (i j : N) (e : E) : Decidable (cross i j e) := by unfold cross; infer_instance
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem rows_independent : ∀ i e, ¬(u e∈neg i ∧ v e∈neg i) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rows_separated : ∀ i j : N, i≠j → 2 ≤ (Finset.univ.filter (cross i j)).card := by decide +kernel

def accepts {k : ℕ} (clause : Fin k → Set V) (s : Set V) : Prop :=
  ∀ c, ∃ w, w∈clause c ∧ w∈s

theorem twenty_require_thirtyseven {k : ℕ} (clause : Fin k → Set V) (skip : E)
    (safe : ∀ s, accepts clause s → ∃ e, u e∈s ∧ v e∈s)
    (complete : ∀ e, e≠skip → accepts clause {u e,v e}) : 37≤k := by
  classical
  let P := {e : E // e≠skip}
  have data : separates (fun e : P => u e.val) (fun e : P => v e.val) neg clause := by
    constructor
    · intro e c
      obtain ⟨w,hw,hmem⟩ := complete e.val e.property c
      rcases Set.mem_insert_iff.mp hmem with h|h
      · exact Or.inl (by simpa only [← h] using hw)
      · have he := Set.mem_singleton_iff.mp h
        exact Or.inr (by simpa only [← he] using hw)
    · intro n
      by_contra! h
      have accepted : accepts clause (neg n) := by
        intro c
        exact Set.not_disjoint_iff.mp (h c)
      obtain ⟨e,he⟩ := safe (neg n) accepted
      exact rows_independent n e he
  obtain ⟨color,hc⟩ := (clauses_iff_coloring _ _ _ k).mp ⟨clause,data⟩
  have inj : Function.Injective color := by
    intro i j same
    by_contra distinct
    have h := rows_separated i j distinct
    have pair : ∃ e, e≠skip ∧ cross i j e := by
      by_contra! hh
      have sub : univ.filter (cross i j) ⊆ {skip} := by
        intro e he
        by_contra hne
        exact hh e (by simpa using hne) (Finset.mem_filter.mp he).2
      have lim := Finset.card_le_card sub
      simp at lim
      omega
    obtain ⟨e,he,ha|hb⟩ := pair
    · exact hc i j ⟨e,he⟩ same ha.1 ha.2
    · exact hc j i ⟨e,he⟩ same.symm hb.1 hb.2
  simpa [N] using Fintype.card_le_of_injective color inj
end Heawood
end CnfFootprint
#print axioms CnfFootprint.clauses_iff_coloring
#print axioms CnfFootprint.Heawood.twenty_require_thirtyseven
