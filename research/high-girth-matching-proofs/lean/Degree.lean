import Core
import Mathlib.Data.Fintype.Sum
import Mathlib.SetTheory.Cardinal.Finite

namespace SparsePermanent
variable {k : ℕ}

private def color : Position k → Position k → Fin 3
  | .inl _, .inl _ => 0
  | .inl (_,c), .inr (_,j) => if c=j.castSucc then 1 else 2
  | .inr (_,j), .inl (r,_) => if r=j.castSucc then 1 else 2
  | .inr _, .inr _ => 0

private theorem near_cast_or_succ {j : Fin k} {u : Node k} (h : near j u) :
    (u=j.castSucc ∨ u=j.succ) := h

private theorem same_slot {c : Node k} {i j : Fin k} (hi : near i c) (hj : near j c)
    (hc : (if c=i.castSucc then (1 : Fin 3) else 2)=(if c=j.castSucc then 1 else 2)) : i=j := by
  by_cases a : c=i.castSucc <;> by_cases b : c=j.castSucc
  · exact Fin.castSucc_injective _ (a.symm.trans b)
  · exact False.elim (by rw [if_pos a,if_neg b] at hc; exact (by decide : (1 : Fin 3)≠2) hc)
  · exact False.elim (by simp only [ite_eq_right a,ite_eq_left b] at hc; exact (by decide : (2 : Fin 3)≠1) hc)
  · exact Fin.succ_injective _ (((near_cast_or_succ hi).resolve_left a).symm.trans
      ((near_cast_or_succ hj).resolve_left b))

private theorem same_port {j : Fin k} {r t : Node k} (hr : near j r) (ht : near j t)
    (hc : (if r=j.castSucc then (1 : Fin 3) else 2)=(if t=j.castSucc then 1 else 2)) : r=t := by
  by_cases a : r=j.castSucc <;> by_cases b : t=j.castSucc
  · exact a.trans b.symm
  · simp [a,b] at hc
  · simp [a,b] at hc
  · exact ((near_cast_or_succ hr).resolve_left a).trans ((near_cast_or_succ ht).resolve_left b).symm

private theorem color_injective (x : Position k) :
    Function.Injective (fun y : {v // edge x v} => color x y.val) := by
  rintro ⟨y,hy⟩ ⟨z,hz⟩ h
  apply Subtype.ext
  change color x y=color x z at h
  rcases x with ⟨r,c⟩|⟨c,i⟩ <;> rcases y with ⟨u,v⟩|⟨u,j⟩ <;> rcases z with ⟨a,b⟩|⟨a,l⟩
  · obtain ⟨rfl,rfl⟩:=hy
    obtain ⟨rfl,rfl⟩:=hz
    rfl
  · simp only [color] at h
    split at h <;> contradiction
  · simp only [color] at h
    split at h <;> contradiction
  · obtain ⟨rfl,hy⟩:=hy
    obtain ⟨rfl,hz⟩:=hz
    obtain rfl:=same_slot hy hz h
    rfl
  · obtain ⟨rfl,hy⟩:=hy
    obtain ⟨rfl,hz⟩:=hz
    obtain rfl:=same_port hy hz h
    rfl
  · exact False.elim hz
  · exact False.elim hy
  · exact False.elim hy

/-- Each left vertex of the sparse board has at most three neighbors. -/
theorem left_degree (x : Position k) : Nat.card {v // edge x v} ≤ 3 := by
  classical
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ (color_injective x)

def mirror : Position k ≃ Position k := (Equiv.prodComm _ _).sumCongr (Equiv.refl _)

theorem mirror_edge (x y : Position k) : edge x y ↔ edge (mirror y) (mirror x) := by
  rcases x with ⟨r,c⟩|⟨c,i⟩ <;> rcases y with ⟨u,v⟩|⟨u,j⟩ <;> simp [edge,mirror,eq_comm,and_comm]

theorem mirror_twice (x : Position k) : mirror (mirror x)=x := by
  rcases x with ⟨r,c⟩|⟨c,i⟩ <;> rfl

/-- Each right vertex likewise has at most three neighbors. -/
theorem right_degree (y : Position k) : Nat.card {u // edge u y} ≤ 3 := by
  classical
  let f : {u // edge u y} → {v // edge (mirror y) v} :=
    fun x => ⟨mirror x.val, (mirror_edge _ _).mp x.prop⟩
  have inj : Function.Injective f := by
    intro x z eq
    exact Subtype.ext (mirror.injective (congrArg Subtype.val eq))
  exact (Nat.card_le_card_of_injective _ inj).trans (left_degree _)

end SparsePermanent

#print axioms SparsePermanent.left_degree
#print axioms SparsePermanent.right_degree
