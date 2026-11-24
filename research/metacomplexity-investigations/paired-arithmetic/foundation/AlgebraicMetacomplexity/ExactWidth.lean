import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic

namespace AlgebraicMeta.ExactWidth
open Finset

/-- Positions store an underlying variable and the bit value making them true. -/
def Satisfies {V C : Type*} {d : ℕ} (var : C → Fin d → V) (sign : C → Fin d → Bool)
    (a : V → Bool) : Prop := ∀ c, ∃ i, a (var c i) = sign c i

/-- If clauses are no more numerous than variables and each uses at least
two distinct variables, every satisfying assignment has a different mate. -/
theorem other_model_of_card {V C : Type*} {d : ℕ} [Fintype V] [Fintype C] [Nonempty V]
    (var : C → Fin d → V) (sign : C → Fin d → Bool)
    (distinct : ∀ c v, ∃ i, var c i ≠ v) (size : Fintype.card C ≤ Fintype.card V)
    (a : V → Bool) (ha : Satisfies var sign a) :
    ∃ b, Satisfies var sign b ∧ b ≠ a := by
  classical
  by_contra no
  have unique (b : V → Bool) (hb : Satisfies var sign b) : b = a := by
    by_contra ne
    exact no ⟨b,hb,ne⟩
  have critical (v : V) : ∃ c, ∀ i, a (var c i) = sign c i → var c i = v := by
    let flip (j : V) := if j=v then !(a j) else a j
    have banned : ¬ Satisfies var sign flip := by
      intro yes
      have h := congrFun (unique flip yes) v
      change (if v=v then !(a v) else a v)=a v at h
      simp at h
    change ¬(∀ c, ∃ i, flip (var c i)=sign c i) at banned
    push Not at banned
    obtain ⟨c, hc⟩ := banned
    refine ⟨c,fun i hi => ?_⟩
    by_contra ne
    exact hc i (by simpa [flip,ne] using hi)
  choose owner howner using critical
  have inj : Function.Injective owner := by
    intro v w e
    obtain ⟨i,hi⟩ := ha (owner v)
    have first := howner v i hi
    rw [e] at hi first
    exact first.symm.trans (howner w i hi)
  have allOwners := ((Fintype.bijective_iff_injective_and_card owner).mpr
    ⟨inj,le_antisymm (Fintype.card_le_of_injective _ inj) size⟩).2
  have hc : Satisfies var sign (fun i => !(a i)) := by
    intro c
    obtain ⟨v,rfl⟩ := allOwners c
    obtain ⟨i,hi⟩ := distinct (owner v) v
    refine ⟨i,Bool.not_eq_iff.mpr ?_⟩
    exact fun h => hi (howner v i h)
  have e := congrFun (unique _ hc) (Classical.choice ‹Nonempty V›)
  simp at e

/-- Exact width three and maximum occurrence three imply the cardinal
hypothesis of the preceding theorem. Counts include literal positions. -/
theorem width_three_occurrence_three {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [Nonempty V] (var : C → Fin 3 → V) (sign : C → Fin 3 → Bool)
    (distinct : ∀ c v, ∃ i, var c i ≠ v)
    (occ : ∀ v, ((univ : Finset (C × Fin 3)).filter (fun e => var e.1 e.2=v)).card ≤ 3)
    (a : V → Bool) (ha : Satisfies var sign a) :
    ∃ b, Satisfies var sign b ∧ b ≠ a := by
  classical
  have count := Finset.card_le_mul_card_image_of_maps_to
    (f:=fun e : C × Fin 3 => var e.1 e.2) (s:=univ) (t:=univ)
    (fun e _ => mem_univ _) 3 (fun v _ => occ v)
  simp only [card_univ,Fintype.card_prod,Fintype.card_fin] at count
  exact other_model_of_card var sign distinct (by omega) a ha

end AlgebraicMeta.ExactWidth
#print axioms AlgebraicMeta.ExactWidth.other_model_of_card
#print axioms AlgebraicMeta.ExactWidth.width_three_occurrence_three
