import FlowIterate

namespace SparsePermanent
open Finset
namespace Flow
variable {I : Type} [Fintype I] [DecidableEq I] {E : I→I→Prop}

def extended (X : Flow E) (r c : I) : Option I→Option I→ℤ
  | none,none => -X.val c r
  | none,some y => if y=r then X.val c r else 0
  | some x,none => if x=c then X.val c r else 0
  | some x,some y => if x=c ∧ y=r then 0 else X.val x y

private theorem old_left (X : Flow E) (r c x y : I) : X.val x y =
    X.extended r c (some x) (some y) + if y=r then X.extended r c (some x) none else 0 := by
  by_cases hx : x=c <;> by_cases hy : y=r <;> simp [extended,hx,hy]

private theorem old_right (X : Flow E) (r c x y : I) : X.val x y =
    X.extended r c (some x) (some y) + if x=c then X.extended r c none (some y) else 0 := by
  by_cases hx : x=c <;> by_cases hy : y=r <;> simp [extended,hx,hy]

def expand (X : Flow E) (r c : I) : Flow (divideAdj E r c) where
  val := X.extended r c
  off := by
    rintro (_|x) (_|y) h
    · exact (h trivial).elim
    · simp [extended,show y≠r from h]
    · simp [extended,show x≠c from h]
    · by_cases eq : x=c ∧ y=r
      · simp [extended,eq]
      · simp [extended,eq,X.off x y (fun a=>h ⟨a,eq⟩)]
  leftZero := by
    rintro (_|x)
    · simp [Fintype.sum_option,extended]
    · have eq : (∑ y,X.val x y) = ∑ y,(X.extended r c (some x) (some y) +
          if y=r then X.extended r c (some x) none else 0) := sum_congr rfl (fun y _=>old_left X r c x y)
      rw [X.leftZero,sum_add_distrib] at eq
      simpa [Fintype.sum_option,add_comm] using eq.symm
  rightZero := by
    rintro (_|y)
    · simp [Fintype.sum_option,extended]
    · have eq : (∑ x,X.val x y) = ∑ x,(X.extended r c (some x) (some y) +
          if x=c then X.extended r c none (some y) else 0) := sum_congr rfl (fun x _=>old_right X r c x y)
      rw [X.rightZero,sum_add_distrib] at eq
      simpa [Fintype.sum_option,add_comm] using eq.symm

@[ext] theorem ext (X Y : Flow E) (val : ∀ x y,X.val x y=Y.val x y) : X=Y := by
  rcases X with ⟨f,_,_,_⟩
  rcases Y with ⟨g,_,_,_⟩
  have h : f=g := funext (fun x=>funext (val x))
  cases h
  rfl

@[simp] theorem contract_expand (X : Flow E) {r c : I} (hit : E c r) :
    (X.expand r c).contract hit=X := by
  ext x y
  exact (old_left X r c x y).symm

end Flow
namespace Board
variable {D I R : Type} [Fintype I] [DecidableEq I] [DecidableEq D] [CommSemiring R]

private theorem extend_charge (B : Board D I R) (d e : D) (X : Flow B.adj) :
    (B.step d).charge (X.expand (B.firstRow d) (B.firstCol d)) e=B.charge X e := by
  change ((X.extended _ _) (some (B.firstCol e)) (if e=d then none else some (B.firstRow e))).natAbs =
    (X.val (B.firstCol e) (B.firstRow e)).natAbs
  by_cases same : e=d
  · subst e; simp [Flow.extended]
  · have diff := fun eq=>same (B.firstCol.injective eq)
    simp [same,Flow.extended,diff]

/-- Extend any circulation through the designated subdivisions. Its increase
in mass is exactly twice the accumulated marked-edge weight. -/
theorem extend_all (B : Board D I R) (ops : List D) (X : Flow B.adj) :
    ∃ Z : Flow (B.run ops).adj, (∀ d,(B.run ops).charge Z d=B.charge X d) ∧
      Z.mass=X.mass+2*(ops.map (B.charge X)).sum := by
  induction ops with
  | nil => exact ⟨X,fun _=>rfl,by simp; rfl⟩
  | cons d rest ih =>
    obtain ⟨Y,marks,mass⟩:=ih
    let B' := B.run rest
    let Z := Y.expand (B'.firstRow d) (B'.firstCol d)
    refine ⟨Z,fun e=>(extend_charge B' d e Y).trans (marks e),?_⟩
    have hc := Z.mass_contract (B'.marked d)
    have m : (Z.reduced (B'.firstCol d) (B'.firstRow d)).natAbs = B'.charge Y d := by
      rw [Z.reduced_mark]
      change (if B'.firstCol d=B'.firstCol d then Y.val (B'.firstCol d) (B'.firstRow d) else (0:ℤ)).natAbs= _
      simp [charge]
    change Z.mass=X.mass+2*((d::rest).map (B.charge X)).sum
    rw [show Z.contract (B'.marked d)=Y from Y.contract_expand _,m,marks d,mass] at hc
    simp only [List.map_cons,List.sum_cons]
    omega

end Board

theorem lift_family_flow {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node k) (Node k) R) (X : Flow (@edge k)) :
    ∃ Z : Flow (familyBoard h A).adj, Z.mass=X.mass+2*h*∑ e : Join k,(X.val (.inl e) (.inl e)).natAbs := by
  have sum_ops (f : Join k→ℕ) : ((operations k h).map f).sum=h * ∑ e,f e := by
    induction h with
    | zero => simp [operations]
    | succ h ih =>
      have once : (univ.toList.map f).sum=∑ e,f e := by rw [←List.sum_toFinset f (nodup_toList _)]; simp
      simp [operations,ih,once,Nat.succ_mul,Nat.add_comm]
  obtain ⟨Z,_,hm⟩:=(coreBoard A).extend_all (operations k h) X
  refine ⟨Z,?_⟩
  rw [sum_ops] at hm
  rw [Nat.mul_assoc]
  convert! hm using 1

end SparsePermanent
#print axioms SparsePermanent.lift_family_flow
