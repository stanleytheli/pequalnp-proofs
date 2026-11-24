import FlowCore
import FlowIterate

namespace SparsePermanent
open Finset
namespace CoreFlow
variable {k : ℕ}

def joinMass (Z : Flow (@edge k)) : ℕ := ∑ e : Join k,(mark Z e.1 e.2).natAbs

def rowMass (Z : Flow (@edge k)) : ℕ := ∑ r, ∑ c, ∑ j,(arm Z r c j).natAbs

theorem dualJoinMass (Z : Flow (@edge k)) : joinMass (dual Z)=joinMass Z := by
  simp only [joinMass,Fintype.sum_prod_type]
  exact sum_comm

private theorem lower_row (Z : Flow (@edge k)) : joinMass Z≤rowMass Z := by
  unfold joinMass rowMass
  rw [Fintype.sum_prod_type]
  apply sum_le_sum
  intro r _
  apply sum_le_sum
  intro c _
  have norm := Int.natAbs_sum_le Finset.univ (arm Z r c)
  have eq : (∑ j, arm Z r c j) = -mark Z r c := by have hh:=port_zero Z r c; omega
  rwa [eq,Int.natAbs_neg] at norm

private theorem left_gap_sum (Z : Flow (@edge k)) (c : Node k) (j : Fin k) :
    (∑ y,(Z.val (.inr (c,j)) y).natAbs)=∑ u,(arm (dual Z) c u j).natAbs := by
  have eq := swap.sum_comp (fun y=> (Z.val (.inr (c,j)) y).natAbs)
  exact eq.symm.trans (gap_sum Int.natAbs rfl (dual Z) c j)

theorem mass_parts (Z : Flow (@edge k)) : Z.mass=joinMass Z + rowMass Z + rowMass (dual Z) := by
  unfold Flow.mass joinMass rowMass
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp only [port_sum Int.natAbs rfl,left_gap_sum,sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro c _
  exact sum_comm

theorem core_cost (Z : Flow (@edge k)) : 3*joinMass Z≤Z.mass := by
  have r:=lower_row Z
  have c:=lower_row (dual Z)
  rw [dualJoinMass] at c
  rw [mass_parts]
  omega

private theorem second_entry {I : Type} [Fintype I] (f : I→ℤ) (zero : ∑ i,f i=0)
    (a : I) (ha : f a≠0) : ∃ b,b≠a ∧ f b≠0 := by
  classical
  by_contra! h
  exact ha ((Fintype.sum_eq_single a (fun b hb=>h b hb)).symm.trans zero)

private theorem two_sum {I : Type} [Fintype I] (f : I→ℕ) {a b : I} (diff : a≠b) :
    f a+f b ≤ ∑ i,f i := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({a,b} : Finset I))
    (fun i _ _=>Nat.zero_le (f i))
  simpa [diff] using h

private theorem two_in_row (Z : Flow (@edge k)) {r c : Node k} (h : mark Z r c≠0) :
    2≤∑ j,(mark Z r j).natAbs := by
  obtain ⟨d,hd,hn⟩:=second_entry (mark Z r) (mark_row Z r) c h
  have sum := two_sum (fun j=>(mark Z r j).natAbs) hd
  have a := Int.natAbs_pos.mpr h
  have b := Int.natAbs_pos.mpr hn
  omega

theorem four_joins (Z : Flow (@edge k)) {r c : Node k} (h : mark Z r c≠0) : 4≤joinMass Z := by
  obtain ⟨s,hs,hn⟩:=second_entry (fun i=>mark Z i c) (mark_col Z c) r h
  have a:=two_in_row Z h
  have b:=two_in_row Z hn
  have bound:=two_sum (fun i=> ∑ j,(mark Z i j).natAbs) hs
  rw [joinMass,Fintype.sum_prod_type]
  change 4≤ ∑ i, ∑ j, (mark Z i j).natAbs
  omega

end CoreFlow

/-- Every positive-mass integral circulation in the actual subdivided graph
has at least four marked crossings and two internal edges per crossing. -/
theorem family_flow_lower {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node k) (Node k) R) (Z : Flow (familyBoard h A).adj) (live : 0<Z.mass) :
    4*(2*h+3)≤Z.mass := by
  obtain ⟨X,hm⟩:=family_flow h A Z
  change Z.mass=X.mass+2*h*CoreFlow.joinMass X at hm
  have active : ∃ r c,CoreFlow.mark X r c≠0 := by
    by_contra! hz
    have all := CoreFlow.all_zero X hz
    have xm : X.mass=0 := by simp [Flow.mass,all]
    have jm : CoreFlow.joinMass X=0 := by simp [CoreFlow.joinMass,hz]
    rw [xm,jm] at hm
    omega
  obtain ⟨r,c,m⟩:=active
  have four:=CoreFlow.four_joins X m
  have base:=CoreFlow.core_cost X
  calc
    4*(2*h+3) ≤ CoreFlow.joinMass X*(2*h+3) := Nat.mul_le_mul_right _ four
    _ ≤ Z.mass := by
      rw [hm,Nat.mul_add,Nat.mul_comm (CoreFlow.joinMass X) (2*h),Nat.mul_comm (CoreFlow.joinMass X) 3]
      omega

end SparsePermanent
#print axioms SparsePermanent.family_flow_lower
