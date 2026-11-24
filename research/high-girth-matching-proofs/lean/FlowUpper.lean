import FlowCycle
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace SparsePermanent
open Finset
namespace CycleFlow
variable {I : Type} [Fintype I] [DecidableEq I] {E : I→I→Prop}

private theorem other {J : Type} [Fintype J] (f : J→ℤ) (zero : ∑ i,f i=0)
    (a : J) (ha : f a≠0) : ∃ b,b≠a ∧ f b≠0 := by
  classical
  by_contra! h
  exact ha ((Fintype.sum_eq_single a (fun b hb=>h b hb)).symm.trans zero)

private noncomputable def active (f : I→I→ℤ) : Finset I := by
  classical exact univ.filter (fun x=>∃ y,f x y≠0)

private theorem active_iff (f : I→I→ℤ) (x : I) : x∈active f ↔ ∃ y,f x y≠0 := by
  classical simp [active]

private theorem active_cost (f : I→I→ℤ) (balance : ∀ x,∑ y,f x y=0) :
    2*(active f).card ≤ ∑ x,∑ y,(f x y).natAbs := by
  classical
  calc
    _ = ∑ _x∈active f, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ x∈active f, ∑ y,(f x y).natAbs := by
      apply sum_le_sum
      intro x hx
      obtain ⟨y,hy⟩:=(active_iff f x).mp hx
      obtain ⟨v,hv,hz⟩:=other (f x) (balance x) y hy
      have c := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({v,y} : Finset I))
        (fun i _ _=>Nat.zero_le (f x i).natAbs)
      have one:=Int.natAbs_pos.mpr hy
      have two:=Int.natAbs_pos.mpr hz
      simp [hv] at c
      omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>Nat.zero_le _)

private theorem cycle_of_neighbors {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (neighbors : ∀ v,∃ a b,a≠b ∧ G.Adj v a ∧ G.Adj v b) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle := by
  classical
  have deg (v : V) : 2≤G.degree v := by
    obtain ⟨a,b,ne,ha,hb⟩:=neighbors v
    have H : ({a,b} : Finset V)⊆G.neighborFinset v := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|h
      · exact (G.mem_neighborFinset v _).mpr ha
      · have := Finset.mem_singleton.mp h
        exact (G.mem_neighborFinset v _).mpr (this ▸ hb)
    simpa [ne] using card_le_card H
  have bound : 2*Fintype.card V≤2*G.edgeFinset.card := calc
    _ = ∑ _v:V,2 := by simp [Nat.mul_comm]
    _ ≤ ∑ v,G.degree v := sum_le_sum (fun v _=>deg v)
    _ = _ := G.sum_degrees_eq_twice_card_edges
  apply G.exists_isCycle_of_card_le
  rw [Nat.card_eq_fintype_card,←G.coe_edgeFinset,Set.ncard_coe_finset]
  omega

/-- The support of a nonzero integral circulation contains a simple cycle of
length at most the circulation's total absolute edge count. -/
theorem egirth_le_mass (Z : Flow E) {x y : I} (live : Z.val x y≠0) :
    (bipGraph E).egirth ≤ (Z.mass : ℕ∞) := by
  classical
  let L := active Z.val
  let R := active (fun v u=>Z.val u v)
  let V := L ⊕ R
  let forget : V → I⊕I := Sum.map Subtype.val Subtype.val
  have inj : Function.Injective forget := Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  let S := bipGraph (fun i j=>Z.val i j≠0)
  let G := S.comap forget
  have leftmem {i j} (h : Z.val i j≠0) : i∈L := (active_iff Z.val _).mpr ⟨j,h⟩
  have rightmem {i j} (h : Z.val i j≠0) : j∈R := (active_iff _ _).mpr ⟨i,h⟩
  letI : Nonempty V := ⟨.inl ⟨x,leftmem live⟩⟩
  have neighbors (v:V) : ∃ a b,a≠b ∧ G.Adj v a ∧ G.Adj v b := by
    rcases v with ⟨u,hu⟩|⟨w,hw⟩
    · obtain ⟨i,hi⟩:=(active_iff _ _).mp hu
      obtain ⟨j,diff,hj⟩:=other (Z.val u) (Z.leftZero u) i hi
      refine ⟨.inr ⟨j,rightmem hj⟩,.inr ⟨i,rightmem hi⟩,?_,hj,hi⟩
      exact fun e=>diff (congrArg Subtype.val (Sum.inr.inj e))
    · obtain ⟨i,hi⟩:=(active_iff _ _).mp hw
      obtain ⟨j,diff,hj⟩:=other (fun u=>Z.val u w) (Z.rightZero w) i hi
      refine ⟨.inl ⟨j,leftmem hj⟩,.inl ⟨i,leftmem hi⟩,?_,hj,hi⟩
      exact fun e=>diff (congrArg Subtype.val (Sum.inl.inj e))
  obtain ⟨v,p,hp⟩:=cycle_of_neighbors G neighbors
  let inc : G →g bipGraph E := by
    refine ⟨forget,?_⟩
    rintro (⟨i,_⟩|⟨i,_⟩) (⟨j,_⟩|⟨j,_⟩) h
    · exact h.elim
    · by_contra miss; exact h (Z.off _ _ miss)
    · by_contra miss; exact h (Z.off _ _ miss)
    · exact h.elim
  have lift := (hp.map (f:=inc) inj).egirth_le_length
  have a:=active_cost Z.val Z.leftZero
  have b:=active_cost (fun v u => Z.val u v) Z.rightZero
  rw [sum_comm] at b
  have bound : Nat.card V≤Z.mass := by
    change Nat.card (L⊕R) ≤ ∑ x,∑ y,(Z.val x y).natAbs
    simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_coe]
    change (active Z.val).card+(active (fun v u=>Z.val u v)).card≤_
    omega
  refine lift.trans ?_
  rw [SimpleGraph.Walk.length_map]
  exact_mod_cast hp.length_le_natCard.trans bound

end CycleFlow
end SparsePermanent
#print axioms SparsePermanent.CycleFlow.egirth_le_mass
