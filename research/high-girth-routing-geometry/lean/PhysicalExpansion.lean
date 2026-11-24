import EulerExpansion
import FlowCycle

namespace SparsePermanent.Contract
open Finset DirectedGrowth
variable {I : Type} [Fintype I] [DecidableEq I]

def arc (E : I→I→Prop) (i j : I) : Prop := E i j ∧ i≠j

private theorem strip (E : I→I→Prop) (matching : ∀x,E x x) (x : I) :
    (∑ y,DirectedGrowth.weight E x y)=(∑ y,DirectedGrowth.weight (arc E) x y)+1 := by
  classical
  calc
    _ = ∑y, (DirectedGrowth.weight (arc E) x y + (if x=y then 1 else 0)) := by
      apply sum_congr rfl
      intro y _
      by_cases eq:x=y <;> simp [DirectedGrowth.weight,arc,eq,matching]
    _ = _ := by simp [sum_add_distrib]

theorem outgoing (E : I→I→Prop) (matching : ∀x,E x x)
    (degree : ∀ x,(∑ y,DirectedGrowth.weight E x y)=3) (x : I) : (∑ y,DirectedGrowth.weight (arc E) x y)=2 := by
  have h:=strip E matching x
  rw [degree] at h
  omega

theorem incoming (E : I→I→Prop) (matching : ∀x,E x x)
    (degree : ∀ y,(∑ x,DirectedGrowth.weight E x y)=3) (y : I) : (∑ x,DirectedGrowth.weight (arc E) x y)=2 := by
  have h:=outgoing (fun x y=>E y x) matching degree y
  rw [←h]
  apply sum_congr rfl
  intro x _
  have same : arc E x y ↔ arc (fun u v=>E v u) y x :=
    ⟨fun h=>⟨h.1,h.2.symm⟩,fun h=>⟨h.1,h.2.symm⟩⟩
  by_cases ok : arc E x y
  · simp [DirectedGrowth.weight,ok,same.mp ok]
  · simp [DirectedGrowth.weight,ok]
    exact fun h=>ok (same.mpr h)

private theorem off_cross (E : I→I→Prop) (S : Finset I) :
    cross E S Sᶜ=cross (arc E) S Sᶜ := by
  classical
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  have ne:x≠y:=fun e=>(mem_compl.mp hy) (e ▸ hx)
  simp [DirectedGrowth.weight,arc,ne]

/-- On a union of matching pairs the physical edge boundary is the sum of
the forward and backward directed cut sizes after contraction. -/
theorem physical_cut (E : I→I→Prop) (S : Finset I) :
    cross (bipGraph E).Adj (S.disjSum S) (S.disjSum S)ᶜ=
      cross (arc E) S Sᶜ + cross (arc E) Sᶜ S := by
  classical
  have comp : (S.disjSum S)ᶜ = Sᶜ.disjSum Sᶜ := by ext (i|j) <;> simp
  rw [comp,←off_cross E S]
  have b:=off_cross E Sᶜ
  rw [compl_compl] at b
  rw [←b]
  have ll (x y : I) : DirectedGrowth.weight (bipGraph E).Adj (.inl x) (.inl y)=0:=by simp [DirectedGrowth.weight,bipGraph,bipAdj]
  have rr (x y : I) : DirectedGrowth.weight (bipGraph E).Adj (.inr x) (.inr y)=0:=by simp [DirectedGrowth.weight,bipGraph,bipAdj]
  have lr (x y : I) : DirectedGrowth.weight (bipGraph E).Adj (.inl x) (.inr y)=DirectedGrowth.weight E x y:=rfl
  have rl (x y : I) : DirectedGrowth.weight (bipGraph E).Adj (.inr x) (.inl y)=DirectedGrowth.weight E y x:=rfl
  simp only [cross,sum_disjSum,ll,rr,lr,rl,sum_const_zero,zero_add,add_zero]
  congr 1
  exact sum_comm

/-- Expand the two directions of the contracted graph from a physical
undirected edge-expansion denominator K on a cubic bipartite graph. -/
theorem directed_expansion (E : I→I→Prop) (matching : ∀x,E x x)
    (left : ∀x,(∑y,DirectedGrowth.weight E x y)=3) (right : ∀y,(∑x,DirectedGrowth.weight E x y)=3)
    (K : ℕ) (expand : ∀S : Finset (I⊕I),2*S.card≤Fintype.card (I⊕I)→
      S.card≤K*cross (bipGraph E).Adj S Sᶜ) :
    Expands (arc E) (K*2) ∧ Expands (fun x y=>arc E y x) (K*2) := by
  apply expands_contraction _ _ _ (fun x=>(outgoing E matching left x).trans (incoming E matching right x).symm)
    (fun x=>(incoming E matching right x).le)
  intro S half
  have h:=expand (S.disjSum S) (by simp;omega)
  rw [physical_cut,card_disjSum] at h
  simpa [two_mul] using h

end SparsePermanent.Contract
#print axioms SparsePermanent.Contract.directed_expansion
