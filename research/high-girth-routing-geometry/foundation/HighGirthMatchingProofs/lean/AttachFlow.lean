import Attach
import FlowUpper

namespace SparsePermanent
namespace Attach
open Finset
variable {I B D : Type} [Fintype I] [Fintype B] [Fintype D]
    [DecidableEq I] [DecidableEq B] [DecidableEq D]
variable {E : I→I→Prop} {K : B→B→Prop} {U V : D→I} {x y : B}

private abbrev Cir := Flow (attach E K U V x y)
private abbrev inner (Z : Cir (E:=E) (K:=K) (U:=U) (V:=V) (x:=x) (y:=y)) (d : D) (a b : B) :=
  Z.val (.inr (d,a)) (.inr (d,b))
private abbrev outgoing (Z : Cir (E:=E) (K:=K) (U:=U) (V:=V) (x:=x) (y:=y)) (d:D) :=
  Z.val (.inr (d,x)) (.inl (V d))
private abbrev incoming (Z : Cir (E:=E) (K:=K) (U:=U) (V:=V) (x:=x) (y:=y)) (d:D) :=
  Z.val (.inl (U d)) (.inr (d,y))

variable (Z : Flow (attach E K U V x y))

private def transpose : Flow (attach (fun a b=>E b a) (fun a b=>K b a) V U y x) where
  val i j := Z.val j i
  off i j h := Z.off _ _ (fun e=>h ((flip E K U V x y j i).mp e))
  leftZero := Z.rightZero
  rightZero := Z.leftZero

private theorem newRow {M : Type} [AddCommMonoid M] (f : ℤ→M) (zero : f 0=0) (d : D) (a : B) :
    (∑ j,f (Z.val (.inr (d,a)) j))=(if a=x then f (outgoing Z d) else 0)+∑ b,f (inner Z d a b) := by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  congr 1
  · rw [Fintype.sum_eq_single (V d) (fun j miss=>(congrArg f (Z.off (.inr (d,a)) (.inl j)
        (fun e=>miss e.1.symm))).trans zero)]
    by_cases e : a=x
    · subst a; simp
    · simp [e,Z.off (.inr (d,a)) (.inl (V d)) (fun h=>e h.2),zero]
  · apply Fintype.sum_eq_single d
    intro e miss
    apply sum_eq_zero
    intro b _
    exact (congrArg f (Z.off (.inr (d,a)) (.inr (e,b)) (fun h=>miss h.1.symm))).trans zero

private theorem outBalance (d : D) (a : B) : (if a=x then outgoing Z d else 0)+∑ b,inner Z d a b=0 :=
  (newRow Z id rfl d a).symm.trans (Z.leftZero _)

private theorem inBalance (d : D) (b : B) : (if b=y then incoming Z d else 0)+∑ a,inner Z d a b=0 :=
  outBalance (transpose Z) d b

private theorem equal_ports (d : D) : outgoing Z d=incoming Z d := by
  have o : (∑ a, ((if a=x then outgoing Z d else 0)+∑ b,inner Z d a b))=0 := sum_eq_zero (fun a _=>outBalance Z d a)
  have i : (∑ b, ((if b=y then incoming Z d else 0)+∑ a,inner Z d a b))=0 := sum_eq_zero (fun b _=>inBalance Z d b)
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at o i
  rw [sum_comm (f:=fun b a=>inner Z d a b)] at i
  omega

/-- Sew the two terminals of an individual copy back together. The signed flow
on the removed reservoir edge is recovered from either attachment. -/
private def repaired (hit : K x y) (d : D) : Flow K where
  val a b := inner Z d a b + if a=x ∧ b=y then outgoing Z d else 0
  off a b h := by
    have old:=Z.off (.inr (d,a)) (.inr (d,b)) (fun e=>h e.2.1)
    have bad : ¬(a=x ∧ b=y) := fun eq=>h (eq.1 ▸ eq.2 ▸ hit)
    simp [inner,old,bad]
  leftZero a := by
    rw [sum_add_distrib]
    by_cases e : a=x
    · simpa [e,add_comm] using outBalance Z d a
    · simpa [e] using outBalance Z d a
  rightZero b := by
    rw [sum_add_distrib]
    by_cases e : b=y
    · simpa [e,equal_ports Z d,add_comm] using inBalance Z d b
    · simpa [e] using inBalance Z d b

private theorem repair_mark (hit : K x y) (d : D) : (repaired Z hit d).val x y=outgoing Z d := by
  have old:=Z.off (.inr (d,x)) (.inr (d,y)) (fun e=>e.2.2 ⟨rfl,rfl⟩)
  simp [repaired,inner,old]

private theorem subset_rows (d : D) :
    (∑ a,∑ j,(Z.val (.inr (d,a)) j).natAbs)≤Z.mass := by
  unfold Flow.mass
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  exact (single_le_sum (f:=fun e=>∑ a,∑ j,(Z.val (.inr (e,a)) j).natAbs)
      (fun _ _=>Nat.zero_le _) (mem_univ d)).trans (Nat.le_add_left ..)

private theorem repair_bound (hit : K x y) (d : D) : (repaired Z hit d).mass≤Z.mass := by
  apply le_trans _ (subset_rows Z d)
  unfold Flow.mass
  apply sum_le_sum
  intro a _
  rw [newRow Z Int.natAbs rfl]
  calc
    _ ≤ ∑ b, ((inner Z d a b).natAbs+(if a=x ∧ b=y then outgoing Z d else (0:ℤ)).natAbs) :=
      sum_le_sum (fun b _=>Int.natAbs_add_le ..)
    _ = _ := by by_cases e : a=x <;> simp [e,sum_add_distrib,apply_ite Int.natAbs,add_comm]

private theorem quiet_out {j} {d:D} {a:B} (all : ∀ d,outgoing Z d=0) : Z.val (.inr (d,a)) (.inl j)=0 := by
  by_cases e:V d=j ∧ a=x
  · rcases e with ⟨rfl,rfl⟩; exact all _
  · exact Z.off _ _ e

private theorem quiet_in {i} {d:D} {b:B} (all : ∀ d,outgoing Z d=0) : Z.val (.inl i) (.inr (d,b))=0 := by
  by_cases e:U d=i ∧ b=y
  · rcases e with ⟨rfl,rfl⟩; exact (equal_ports Z d).symm.trans (all _)
  · exact Z.off _ _ e

private def unmarked (all : ∀ d,outgoing Z d=0) : Flow E where
  val i j := Z.val (.inl i) (.inl j)
  off i j h := Z.off _ _ h
  leftZero i := by
    have h:=Z.leftZero (.inl i)
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type] at h
    simpa [quiet_in Z all] using h
  rightZero j := by
    have h:=Z.rightZero (.inl j)
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type] at h
    simpa [quiet_out Z all] using h

private theorem old_mass (hit : K x y) (quiet : ∀ d a b,(repaired Z hit d).val a b=0)
    (all : ∀ d,outgoing Z d=0) : (unmarked Z all).mass=Z.mass := by
  have inside (d : D) (a b : B) : inner Z d a b=0 := by
    simpa [repaired,all] using quiet d a b
  unfold Flow.mass
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  have empty (i:I) : (∑ j,(Z.val (.inl i) j).natAbs)=∑ j,(Z.val (.inl i) (.inl j)).natAbs := by
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    simp [quiet_in Z all]
  simp [newRow Z Int.natAbs rfl,all,inside,empty,unmarked]

/-- Any split-edge reservoir of girth at least g can regularize a base of
that girth without introducing a shorter cycle, for any pairing of deficits. -/
theorem girth_preserved {g : ℕ} (hit : K x y) (base : (g:ℕ∞)≤(bipGraph E).egirth)
    (res : (g:ℕ∞)≤(bipGraph K).egirth) : (g:ℕ∞)≤(bipGraph (attach E K U V x y)).egirth := by
  apply CycleFlow.le_egirth
  intro F positive
  by_cases any : ∃ d a b,(repaired F hit d).val a b≠0
  · obtain ⟨d,a,b,nonzero⟩:=any
    have h := res.trans (CycleFlow.egirth_le_mass (repaired F hit d) nonzero)
    exact (ENat.coe_le_coe.mp h).trans (repair_bound F hit d)
  · push Not at any
    have all (d) : outgoing F d=0 := (repair_mark F hit d).symm.trans (any d x y)
    let old:=unmarked F all
    have mass : old.mass=F.mass := old_mass F hit any all
    have anyOld : ∃ i j,old.val i j≠0 := by
      by_contra! zero
      have empty : old.mass=0 := by simp [Flow.mass,zero]
      omega
    obtain ⟨i,j,h⟩:=anyOld
    rw [←mass]
    exact ENat.coe_le_coe.mp (base.trans (CycleFlow.egirth_le_mass old h))

end Attach
end SparsePermanent
#print axioms SparsePermanent.Attach.girth_preserved
