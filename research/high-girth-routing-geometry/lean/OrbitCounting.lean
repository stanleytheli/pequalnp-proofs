import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace SparsePermanent.OrbitCounting
open Finset
variable {Γ V : Type*} [Group Γ] [Fintype Γ] [Fintype V]
variable [MulAction Γ V] [MulAction.IsPretransitive Γ V] [DecidableEq V]

private def fiberEquiv (a x y : V) (g h : Γ) (gx:g•a=x) (hy:h•a=y) :
    {u : Γ // u•x=y} ≃ {u : Γ // u•a=a} where
  toFun u:=⟨h⁻¹*u.val*g,by simp [mul_smul,gx,u.prop,←hy]⟩
  invFun u:=⟨h*u.val*g⁻¹,by rw [←gx];simp [mul_smul,u.prop,hy]⟩
  left_inv u:=Subtype.ext (by simp [mul_assoc])
  right_inv u:=Subtype.ext (by simp [mul_assoc])

/-- Every source-target pair has the same positive number of group elements
carrying the source to the target. -/
theorem uniform (a : V) : ∃ c : ℕ,0<c ∧ ∀x y : V,(univ.filter (fun g : Γ=>g•x=y)).card=c := by
  classical
  let c:=Fintype.card {g : Γ // g•a=a}
  have pos : 0<c:=Fintype.card_pos_iff.mpr ⟨⟨1,one_smul _ _⟩⟩
  refine ⟨c,pos,?_⟩
  intro x y
  obtain ⟨g,gx⟩:=MulAction.exists_smul_eq Γ a x
  obtain ⟨h,hy⟩:=MulAction.exists_smul_eq Γ a y
  have f:=Fintype.card_congr (fiberEquiv a x y g h gx hy)
  simpa [c,Fintype.card_subtype] using f

variable {J : Type*} [Fintype J]

theorem indicator (act : J→Equiv.Perm V) {c : ℕ}
    (equal : ∀x y,(univ.filter (fun g : J=>act g x=y)).card=c) (x : V) (T : Finset V) :
    (∑g : J,if act g x∈T then 1 else 0)=T.card*c := by
  classical
  have f:=sum_card_fiberwise_eq_card_filter (univ : Finset J) T (fun g=>act g x)
  simp only [equal,sum_const,nsmul_eq_mul] at f
  rw [←card_filter]
  exact f.symm

end SparsePermanent.OrbitCounting
#print axioms SparsePermanent.OrbitCounting.uniform
