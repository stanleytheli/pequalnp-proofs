import Explicit

namespace SparsePermanent
open Finset
variable {I D : Type} [Fintype I] [DecidableEq I]

/-- Signed integral flow with zero divergence at every vertex. The fixed
orientation directs each edge from its left endpoint to its right endpoint. -/
structure Flow (E : I → I → Prop) where
  val : I → I → ℤ
  off : ∀ x y, ¬E x y → val x y=0
  leftZero : ∀ x, ∑ y, val x y=0
  rightZero : ∀ y, ∑ x, val x y=0

namespace Flow
variable {E : I → I → Prop}

def mass (Z : Flow E) : ℕ := ∑ x, ∑ y, (Z.val x y).natAbs

section Divide
variable {r c : I} (Z : Flow (divideAdj E r c))

theorem newLeftZero {y : I} (h : y≠r) : Z.val none (some y)=0 := Z.off _ _ h

theorem newRightZero {x : I} (h : x≠c) : Z.val (some x) none=0 := Z.off _ _ h

theorem cuts : Z.val none (some r) = -Z.val none none ∧
    Z.val (some c) none = -Z.val none none := by
  have l:=Z.leftZero none
  have r':=Z.rightZero none
  rw [Fintype.sum_option] at l r'
  have la : ∑ y, Z.val none (some y) = Z.val none (some r) :=
    Fintype.sum_eq_single r (fun _ h=>Z.newLeftZero h)
  have ra : ∑ x, Z.val (some x) none = Z.val (some c) none :=
    Fintype.sum_eq_single c (fun _ h=>Z.newRightZero h)
  rw [la] at l
  rw [ra] at r' 
  constructor <;> omega

theorem killed : Z.val (some c) (some r)=0 :=
  Z.off _ _ (fun h=>h.2 ⟨rfl,rfl⟩)

def reduced (x y : I) : ℤ := Z.val (some x) (some y) +
  if y=r then Z.val (some x) none else 0

theorem reduced_col (x y : I) : Z.reduced x y = Z.val (some x) (some y) +
    if x=c then Z.val none (some y) else 0 := by
  simp only [reduced]
  by_cases hx : x=c <;> by_cases hy : y=r <;> simp [hx,hy,Z.newLeftZero,Z.newRightZero,Z.cuts.1,Z.cuts.2]

def contract (hit : E c r) : Flow E where
  val := Z.reduced
  off x y h := by
    have a := Z.off (some x) (some y) (fun e=>h e.1)
    by_cases he : y=r ∧ x=c
    · exfalso; exact h (he.1 ▸ he.2 ▸ hit)
    · simp only [reduced,a,zero_add]
      by_cases hy : y=r
      · rw [if_pos hy]; exact Z.off _ _ (fun hc=>he ⟨hy,hc⟩)
      · rw [if_neg hy]
  leftZero x := by
    have h := Z.leftZero (some x)
    rw [Fintype.sum_option] at h
    simpa [reduced,sum_add_distrib,add_comm] using h
  rightZero y := by
    have h := Z.rightZero (some y)
    rw [Fintype.sum_option] at h
    simpa [Z.reduced_col,sum_add_distrib,add_comm] using h

@[simp] theorem reduced_mark : Z.reduced c r=Z.val (some c) none := by
  simp [reduced,Z.killed]

theorem reduced_old {x y : I} (different : x≠c ∨ y≠r) : Z.reduced x y=Z.val (some x) (some y) := by
  rcases different with h|h
  · simp [reduced,Z.newRightZero,h]
  · simp [reduced,h]

private theorem abs_reduced (x y : I) : (Z.reduced x y).natAbs =
    (Z.val (some x) (some y)).natAbs + if y=r then (Z.val (some x) none).natAbs else 0 := by
  by_cases hx : x=c
  · subst x
    by_cases hy : y=r
    · subst y; simp [Z.killed]
    · simp [Z.reduced_old (Or.inr hy),hy]
  · simp [Z.reduced_old (Or.inl hx),Z.newRightZero,hx]

theorem mass_contract (hit : E c r) : Z.mass=(Z.contract hit).mass +
    2*(Z.reduced c r).natAbs := by
  have a : ∑ y, (Z.val none (some y)).natAbs = (Z.val none (some r)).natAbs := by
    apply Fintype.sum_eq_single r
    intro y hy; simp [Z.newLeftZero,hy]
  have b : ∑ x, (Z.val (some x) none).natAbs = (Z.val (some c) none).natAbs := by
    apply Fintype.sum_eq_single c
    intro x hx; simp [Z.newRightZero,hx]
  unfold mass
  rw [Fintype.sum_option]
  simp only [Fintype.sum_option,a,sum_add_distrib,b,contract,abs_reduced,sum_ite_eq',mem_univ,ite_true,
    reduced_mark,Z.cuts.1,Z.cuts.2,Int.natAbs_neg]
  omega

end Divide
end Flow
end SparsePermanent

#print axioms SparsePermanent.Flow.mass_contract
