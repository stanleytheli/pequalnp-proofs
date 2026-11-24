import FlowStep

namespace SparsePermanent
open Finset
namespace CoreFlow
variable {k : ℕ}

abbrev mark (Z : Flow (@edge k)) (r c : Node k) := Z.val (.inl (r,c)) (.inl (r,c))
abbrev arm (Z : Flow (@edge k)) (r u : Node k) (j : Fin k) := Z.val (.inl (r,u)) (.inr (r,j))

def swap : Position k ≃ Position k where
  toFun | .inl (a,b) => .inl (b,a) | .inr v => .inr v
  invFun | .inl (a,b) => .inl (b,a) | .inr v => .inr v
  left_inv := by rintro (⟨_,_⟩|_) <;> rfl
  right_inv := by rintro (⟨_,_⟩|_) <;> rfl

theorem swap_edge (x y : Position k) : edge x y ↔ edge (swap y) (swap x) := by
  rcases x with ⟨a,b⟩|⟨a,b⟩ <;> rcases y with ⟨c,d⟩|⟨c,d⟩ <;> simp [edge,swap,eq_comm,and_comm]

def dual (Z : Flow (@edge k)) : Flow (@edge k) where
  val x y := Z.val (swap y) (swap x)
  off x y h := Z.off _ _ (fun a=>h ((swap_edge x y).mpr a))
  leftZero x := (swap.sum_comp _).trans (Z.rightZero (swap x))
  rightZero y := (swap.sum_comp _).trans (Z.leftZero (swap y))

private theorem by_first {U V M : Type*} [Fintype U] [Fintype V] [AddCommMonoid M]
    (f : U×V → M) (i : U) (vanish : ∀ a b,a≠i → f (a,b)=0) :
    ∑ p, f p=∑ b, f (i,b) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_eq_single i
  intro a ha
  exact sum_eq_zero (fun b _=>vanish a b ha)

theorem port_sum {M : Type*} [AddCommMonoid M] (f : ℤ → M) (zero : f 0=0)
    (Z : Flow (@edge k)) (r c : Node k) : ∑ y,f (Z.val (.inl (r,c)) y)=
      f (mark Z r c) + ∑ j,f (arm Z r c j) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Fintype.sum_eq_single (r,c)
    rintro ⟨a,b⟩ h
    exact (congrArg f (Z.off (.inl (r,c)) (.inl (a,b)) (fun e=>h (Prod.ext e.1.symm e.2.symm)))).trans zero
  · apply by_first
    intro a b h
    exact (congrArg f (Z.off (.inl (r,c)) (.inr (a,b)) (fun e=>h e.1.symm))).trans zero

theorem gap_sum {M : Type*} [AddCommMonoid M] (f : ℤ → M) (zero : f 0=0)
    (Z : Flow (@edge k)) (r : Node k) (j : Fin k) : ∑ x,f (Z.val x (.inr (r,j)))=
      ∑ c,f (arm Z r c j) := by
  rw [Fintype.sum_sum_type]
  have second : (∑ p : Node k × Fin k, f (Z.val (.inr p) (.inr (r,j))))=0 := by
    apply sum_eq_zero
    rintro ⟨a,b⟩ _
    exact (congrArg f (Z.off _ _ id)).trans zero
  rw [second,add_zero]
  apply by_first
  intro a b h
  exact (congrArg f (Z.off (.inl (a,b)) (.inr (r,j)) (fun e=>h e.1))).trans zero

theorem port_zero (Z : Flow (@edge k)) (r c : Node k) : mark Z r c + ∑ j,arm Z r c j=0 :=
  (port_sum id rfl Z r c).symm.trans (Z.leftZero _)

theorem gap_zero (Z : Flow (@edge k)) (r : Node k) (j : Fin k) : ∑ c,arm Z r c j=0 :=
  (gap_sum id rfl Z r j).symm.trans (Z.rightZero _)

theorem mark_row (Z : Flow (@edge k)) (r : Node k) : ∑ c,mark Z r c=0 := by
  have row : (∑ c,(mark Z r c+∑ j,arm Z r c j))=0 := sum_eq_zero (fun c _=>port_zero Z r c)
  rw [sum_add_distrib,sum_comm (f:=fun c j=>arm Z r c j)] at row
  simpa [gap_zero] using row

theorem mark_col (Z : Flow (@edge k)) (c : Node k) : ∑ r,mark Z r c=0 := mark_row (dual Z) c

/-- The incidence matrix of a path has zero integer circulation. -/
private theorem path_zero (a : Node k → Fin k → ℤ)
    (off : ∀ u j,¬near j u → a u j=0) (row : ∀ u,∑ j,a u j=0) (col : ∀ j,∑ u,a u j=0) :
    ∀ u j, a u j=0 := by
  have go : ∀ n (u : Node k), u.val=n → ∀ j,a u j=0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro u hu j
      have prev (i : Fin k) (eq : u=i.succ) : a u i=0 := by
        have bound : i.val<n := by rw [←hu,eq]; exact Nat.lt_succ_self _
        have left := ih i.val bound i.castSucc rfl i
        have only : (∑ v, a v i)=a u i := by
          apply Fintype.sum_eq_single u
          intro v nv
          by_cases vv : v=i.castSucc
          · simpa [vv] using left
          · exact off v i (fun e=>e.elim vv (fun hi=>nv (hi.trans eq.symm)))
        exact only.symm.trans (col i)
      by_cases eq : u=j.castSucc
      · have only : (∑ i, a u i)=a u j := by
          apply Fintype.sum_eq_single j
          intro i ni
          by_cases p : u=i.succ
          · exact prev i p
          · exact off u i (fun e=>e.elim (fun v=>ni (Fin.castSucc_injective _ (v.symm.trans eq))) p)
        exact only.symm.trans (row u)
      · by_cases p : u=j.succ
        · exact prev j p
        · exact off u j (fun e=>e.elim eq p)
  exact fun u=>go u.val u rfl

private theorem arm_zero (Z : Flow (@edge k)) (r : Node k) (zero : ∀ c,mark Z r c=0) :
    ∀ c j,arm Z r c j=0 := by
  apply path_zero
  · intro u j h; exact Z.off _ _ (fun e=>h e.2)
  · intro u; simpa [zero u] using port_zero Z r u
  · exact gap_zero Z r

theorem all_zero (Z : Flow (@edge k)) (zero : ∀ r c,mark Z r c=0) (x y) : Z.val x y=0 := by
  rcases x with ⟨a,b⟩|⟨a,b⟩ <;> rcases y with ⟨c,d⟩|⟨c,d⟩
  · by_cases e : a=c ∧ b=d
    · obtain ⟨rfl,rfl⟩:=e; exact zero _ _
    · exact Z.off _ _ e
  · by_cases e : a=c
    · subst c; exact arm_zero Z a (zero a) b d
    · exact Z.off _ _ (fun h=>e h.1)
  · by_cases e : a=d
    · subst d; exact arm_zero (dual Z) a (fun u=>zero u a) c b
    · exact Z.off _ _ (fun h=>e h.1)
  · exact Z.off _ _ id

end CoreFlow
end SparsePermanent

#print axioms SparsePermanent.CoreFlow.all_zero
