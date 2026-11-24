import FlowStep

namespace SparsePermanent
namespace Board
variable {D I R : Type} [Fintype I] [DecidableEq I] [DecidableEq D] [CommSemiring R]

def charge (B : Board D I R) (Z : Flow B.adj) (d : D) := (Z.val (B.firstCol d) (B.firstRow d)).natAbs

private theorem step_charge (B : Board D I R) (d e : D) (Z : Flow (B.step d).adj) :
    (B.step d).charge Z e=B.charge (Z.contract (B.marked d)) e := by
  change (Z.val (some (B.firstCol e)) (if e=d then none else some (B.firstRow e))).natAbs =
    (Z.reduced (B.firstCol e) (B.firstRow e)).natAbs
  by_cases same : e=d
  · subst e; rw [if_pos rfl,Z.reduced_mark]
  · rw [if_neg same,Z.reduced_old (Or.inl (fun eq=>same (B.firstCol.injective eq)))]

/-- Contract all marked subdivisions of a circulation. Every split increases its
absolute edge count by twice the absolute flow on the corresponding marked edge. -/
theorem contract_all (B : Board D I R) (ops : List D) (Z : Flow (B.run ops).adj) :
    ∃ X : Flow B.adj, (∀ d, (B.run ops).charge Z d=B.charge X d) ∧
      Z.mass = X.mass + 2*(ops.map (B.charge X)).sum := by
  induction ops with
  | nil => exact ⟨Z,fun _=>rfl,by simp; rfl⟩
  | cons d rest ih =>
    let B' := B.run rest
    change Flow (B'.step d).adj at Z
    let Y := Z.contract (B'.marked d)
    obtain ⟨X,hx,hm⟩:=ih Y
    refine ⟨X,fun e => (step_charge B' d e Z).trans (hx e),?_⟩
    have mass := Z.mass_contract (B'.marked d)
    change Z.mass = Y.mass + 2*B'.charge Y d at mass
    rw [hx d] at mass
    change Z.mass = X.mass + 2*((d::rest).map (B.charge X)).sum
    rw [mass,hm]
    simp only [List.map_cons,List.sum_cons]
    omega

end Board

private theorem total_operations {k : ℕ} (h : ℕ) (f : Join k → ℕ) :
    ((operations k h).map f).sum = h * ∑ e, f e := by
  induction h with
  | zero => simp [operations]
  | succ h ih =>
    have once : (Finset.univ.toList.map f).sum = ∑ e, f e := by
      rw [← List.sum_toFinset f (Finset.nodup_toList _)]
      simp
    simp [operations,ih,once,Nat.succ_mul,Nat.add_comm]

theorem family_flow {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node k) (Node k) R) (Z : Flow (familyBoard h A).adj) :
    ∃ X : Flow (@edge k), Z.mass = X.mass+2*h* ∑ e : Join k, (X.val (.inl e) (.inl e)).natAbs := by
  obtain ⟨X,_,hm⟩ := (coreBoard A).contract_all (operations k h) Z
  refine ⟨X,?_⟩
  rw [total_operations] at hm
  rw [Nat.mul_assoc]
  convert! hm using 1 <;> rfl

end SparsePermanent
#print axioms SparsePermanent.family_flow
