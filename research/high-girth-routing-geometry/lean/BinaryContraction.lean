import GirthForest
import ContractionGirth
import PhysicalExpansion

namespace SparsePermanent.Contract
open Finset DirectedGrowth SimpleGraph
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Distinct reciprocal arcs and their two diagonal matching edges would
already give a physical four-cycle. -/
theorem antireciprocal (E : I→I→Prop) (matching : ∀x,E x x) (long : 4<(bipGraph E).egirth) :
    ∀ ⦃x y⦄,arc E x y→¬arc E y x := by
  intro x y xy yx
  let f : Bool↪I:=
    ⟨fun b=>if b then y else x,by rintro (a|a) (b|b) h <;> simp_all [arc]⟩
  let entries : Bool×Bool ↪ Bool×Bool:=Function.Embedding.refl _
  have valid (z : Bool×Bool) : E (f (entries z).1) (f (entries z).2) := by
    rcases z with ⟨(_|_),(_|_)⟩ <;> first | exact matching _ | exact xy.1 | exact yx.1
  have g:=dense_patch f E entries valid (by decide)
  exact (not_le_of_gt long) (by simpa using g)

private theorem filter_degree (E : I→I→Prop) [DecidableRel E] (x : I) :
    (univ.filter (E x)).card=∑y,DirectedGrowth.weight E x y := by
  classical
  rw [card_filter]
  apply sum_congr rfl
  intro y _
  by_cases e : E x y <;> simp [DirectedGrowth.weight,e]

private noncomputable def branches (G : SimpleGraph I) (D : I→I→Prop)
    (adjacent:∀⦃x y⦄,D x y→G.Adj x y) (degree : ∀ x,(∑y,DirectedGrowth.weight D x y)=2) :
    Branches G D := by
  classical
  have avail (x : I) : ∃f : Bool→I,Function.Injective f ∧ ∀b,D x (f b) := by
    obtain ⟨u,v,ne,eq⟩:=card_eq_two.mp ((filter_degree D x).trans (degree x))
    have legal (y : I) (h:y∈({u,v} : Finset I)) : D x y := (mem_filter.mp (eq ▸ h)).2
    exact ⟨fun b=>if b then v else u,by rintro (_|_) (_|_) h <;> simp_all,
      by rintro (_|_) <;> exact legal _ (by simp)⟩
  choose f inject edge using avail
  exact ⟨f,inject,fun x b=>adjacent (edge x b),edge⟩

noncomputable def outgoing_tree (E : I→I→Prop) (matching : ∀x,E x x) (degree : ∀x,(∑y,DirectedGrowth.weight E x y)=3) :
    Branches (underlying E) (arc E) :=
  branches _ _ (fun ⦃_ _⦄ h=>⟨h.2,Or.inl h.1⟩) (outgoing E matching degree)

noncomputable def incoming_tree (E : I→I→Prop) (matching : ∀x,E x x) (degree : ∀y,(∑x,DirectedGrowth.weight E x y)=3) :
    Branches (underlying E) (fun x y=>arc E y x) :=
  branches _ _ (fun ⦃_ _⦄ h=>⟨h.2.symm,Or.inr h.1⟩) (incoming E matching degree)

open Classical in
theorem max_degree (E : I→I→Prop) (matching : ∀x,E x x)
    (left : ∀x,(∑y,DirectedGrowth.weight E x y)=3) (right : ∀y,(∑x,DirectedGrowth.weight E x y)=3) (x : I) :
    (univ.filter ((underlying E).Adj x)).card≤4 := by
  classical
  let a:=univ.filter (arc E x)
  let b:=univ.filter (fun y=>arc E y x)
  have ca:a.card=2:=(filter_degree (arc E) x).trans (outgoing E matching left x)
  have cb:b.card=2:=(filter_degree (fun x y=>arc E y x) x).trans (incoming E matching right x)
  have eq : univ.filter ((underlying E).Adj x)=a∪b := by
    ext y
    simp only [a,b,mem_filter,mem_univ,true_and,mem_union]
    change (x≠y ∧ (E x y ∨ E y x)) ↔ (E x y ∧ x≠y) ∨ (E y x ∧ y≠x)
    rw [show (y≠x) ↔ (x≠y) from ne_comm]
    tauto
  rw [eq]
  exact (card_union_le ..).trans (by omega)

end SparsePermanent.Contract
#print axioms SparsePermanent.Contract.antireciprocal
#print axioms SparsePermanent.Contract.max_degree
