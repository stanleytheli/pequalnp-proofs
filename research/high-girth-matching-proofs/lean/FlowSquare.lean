import FlowCost
import FlowLift

namespace SparsePermanent
open Finset
namespace Square
variable {k : ℕ}

private def sign (i : Node (k+1)) : ℤ := (if i=0 then 1 else 0)-(if i=1 then 1 else 0)
private abbrev tile (r c : Node (k+1)) : ℤ := sign r*sign c

private theorem sum_sign : (∑ i : Node (k+1),sign i)=0 := by
  simp [sign,sum_sub_distrib]

private theorem norm_sign (i : Node (k+1)) : (sign i).natAbs =
    (if i=0 then 1 else 0)+(if i=1 then 1 else 0) := by
  have ne : (0 : Node (k+1))≠1 := Fin.zero_ne_one
  by_cases a : i=0 <;> by_cases b : i=1 <;> simp_all [sign]

private theorem sum_norm_sign : (∑ i : Node (k+1),(sign i).natAbs)=2 := by
  simp [norm_sign,sum_add_distrib]

private theorem sum_tile (c : Node (k+1)) : (∑ u,tile u c)=0 := by
  rw [←sum_mul,sum_sign,zero_mul]

private theorem sum_norm_tile : (∑ r,∑ c,(tile (k:=k) r c).natAbs)=4 := by
  simp only [Int.natAbs_mul,←mul_sum,sum_norm_sign,←sum_mul]
  norm_num [sum_norm_sign]

private theorem outside {i : Node (k+1)} (h : ¬near (0 : Fin (k+1)) i) : sign i=0 := by
  have a : i≠0 := fun e=>h (Or.inl (by simpa only [Fin.castSucc_zero] using e))
  have b : i≠1 := fun e=>h (Or.inr (by simpa only [Fin.succ_zero_eq_one] using e))
  simp [sign,a,b]

private def entry : Position (k+1) → Position (k+1) → ℤ
  | .inl (r,c),.inl q => if q=(r,c) then tile r c else 0
  | .inl (r,c),.inr q => if q=(r,0) then -tile r c else 0
  | .inr (c,j),.inl (u,v) => if (v,0)=(c,j) then -tile u v else 0
  | .inr _,.inr _ => 0

private theorem entry_dual (x y : Position (k+1)) : entry x y=entry (CoreFlow.swap y) (CoreFlow.swap x) := by
  rcases x with ⟨a,b⟩|⟨a,b⟩ <;> rcases y with ⟨c,d⟩|⟨c,d⟩
  · change (if (c,d)=(a,b) then tile a b else 0)=(if (b,a)=(d,c) then tile d c else 0)
    by_cases h : c=a ∧ d=b
    · rcases h with ⟨rfl,rfl⟩; simp [tile,mul_comm]
    · simp only [Prod.mk.injEq,ite_eq_right_iff,ite_eq_left_iff]
      simp [h,show ¬(b=d ∧ a=c) from fun ⟨s,t⟩=>h ⟨t.symm,s.symm⟩]
  · change (if (c,d)=(a,0) then -tile a b else 0)=(if (a,0)=(c,d) then -tile b a else 0)
    simp [tile,eq_comm,mul_comm]
  · change (if (d,0)=(a,b) then -tile c d else 0)=(if (a,b)=(d,0) then -tile d c else 0)
    simp [tile,eq_comm,mul_comm]
  · rfl

private theorem entry_left (x : Position (k+1)) : ∑ y,entry x y=0 := by
  rw [Fintype.sum_sum_type]
  rcases x with ⟨r,c⟩|⟨c,j⟩
  · change (∑ q : Node (k+1)×Node (k+1),if q=(r,c) then tile r c else 0)+
      (∑ q : Node (k+1)×Fin (k+1),if q=(r,0) then -tile r c else 0)=0
    simp
  · rw [Fintype.sum_prod_type]
    change (∑ u,∑ v,if (v,0)=(c,j) then -tile u v else 0)+(∑ _ : Node (k+1)×Fin (k+1),0)=0
    by_cases h : j=0
    · subst j; simp [sum_tile]
    · simp [Ne.symm h]

private theorem entry_off (x y : Position (k+1)) (h : ¬edge x y) : entry x y=0 := by
  rcases x with ⟨a,b⟩|⟨a,b⟩ <;> rcases y with ⟨c,d⟩|⟨c,d⟩
  · have no : (c,d)≠(a,b) := fun e=>h ⟨(Prod.mk.inj e).1.symm,(Prod.mk.inj e).2.symm⟩
    simp [entry,no]
  · by_cases eq : (c,d)=(a,0)
    · obtain ⟨rfl,rfl⟩:=Prod.mk.inj eq
      have z := outside (i:=b) (fun p=>h ⟨rfl,p⟩)
      simp [entry,tile,z]
    · simp [entry,eq]
  · by_cases eq : (d,0)=(a,b)
    · obtain ⟨rfl,rfl⟩:=Prod.mk.inj eq
      have z := outside (i:=c) (fun p=>h ⟨rfl,p⟩)
      simp [entry,tile,z]
    · simp [entry,eq]
  · rfl

/-- The two adjacent rows and columns, signed around their unique twelve-edge cycle. -/
def square (k : ℕ) : Flow (@edge (k+1)) where
  val := entry
  off := entry_off
  leftZero := entry_left
  rightZero y := by
    calc
      _ = ∑ x,entry (CoreFlow.swap y) (CoreFlow.swap x) := sum_congr rfl fun x _=>entry_dual x y
      _ = _ := (CoreFlow.swap.sum_comp _).trans (entry_left _)

private theorem norm_arm (r c : Node (k+1)) :
    (∑ j,(CoreFlow.arm (square k) r c j).natAbs)=(tile r c).natAbs := by
  change (∑ j,(if (r,j)=(r,0) then -tile r c else 0).natAbs)=(tile r c).natAbs
  simp [apply_ite Int.natAbs]

private theorem dual_square : CoreFlow.dual (square k)=square k := by
  apply Flow.ext
  intro x y
  exact (entry_dual x y).symm

theorem joins (k : ℕ) : CoreFlow.joinMass (square k)=4 := by
  simp only [CoreFlow.joinMass,Fintype.sum_prod_type]
  change (∑ r,∑ c,(if (r,c)=(r,c) then tile (k:=k) r c else 0).natAbs)=4
  simpa using (sum_norm_tile (k:=k))

theorem mass (k : ℕ) : (square k).mass=12 := by
  have r : CoreFlow.rowMass (square k)=4 := by
    simpa only [CoreFlow.rowMass,norm_arm] using (sum_norm_tile (k:=k))
  rw [CoreFlow.mass_parts,joins,r,dual_square,r]

end Square
end SparsePermanent
#print axioms SparsePermanent.Square.mass
