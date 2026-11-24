import FamilyShape
import AttachDegree

namespace SparsePermanent
namespace Edges
abbrev Inc {I : Type*} (E : I→I→Prop) := {z : I×I // E z.1 z.2}

private noncomputable def subdivide {I : Type*} [DecidableEq I] (E : I→I→Prop) (r c : I) (hit : E c r) :
    Inc (divideAdj E r c) ≃ (Inc E⊕Bool) where
  toFun
    | ⟨(none,none),_⟩ => .inr false
    | ⟨(none,some _),_⟩ => .inr true
    | ⟨(some i,none),h⟩ => .inl ⟨(i,r),show E i r from h ▸ hit⟩
    | ⟨(some i,some j),h⟩ => .inl ⟨(i,j),h.1⟩
  invFun
    | .inr false=> ⟨(none,none),trivial⟩
    | .inr true=> ⟨(none,some r),rfl⟩
    | .inl ⟨(i,j),h⟩=>if e : i=c ∧ j=r then ⟨(some i,none),e.1⟩
      else ⟨(some i,some j),h,e⟩
  left_inv := by
    rintro ⟨⟨_|i,_|j⟩,adj⟩
    · rfl
    · apply Subtype.ext
      change j=r at adj
      change (none,some r)=(none,some j)
      exact congrArg (fun z=>(none,some z)) adj.symm
    · change i=c at adj
      simp [adj]
    · simp [adj.2]
  right_inv := by
    rintro (⟨⟨i,j⟩,h⟩|b)
    · by_cases yes : i=c ∧ j=r
      · obtain ⟨rfl,rfl⟩:=yes; simp
      · simp [yes]
    · cases b <;> rfl

theorem count_run {I D R : Type*} [Fintype I] [DecidableEq I] [DecidableEq D] [CommSemiring R]
    (B : Board D I R) (ops : List D) : Nat.card (Inc (B.run ops).adj)=Nat.card (Inc B.adj)+2*ops.length := by
  induction ops with
  | nil => exact (Nat.add_zero _).symm
  | cons d ds ih =>
    change Nat.card (Inc (divideAdj (B.run ds).adj _ _))=_
    rw [Nat.card_congr (subdivide _ _ _ ((B.run ds).marked d)),Nat.card_sum,ih]
    simp; omega

private def selected {k : ℕ} (j : Fin k) (b : Bool) : Node k := if b then j.succ else j.castSucc

private theorem selectedNear {k : ℕ} (j : Fin k) (b : Bool) : near j (selected j b) := by
  cases b <;> simp [selected,near]

private theorem chosen {k : ℕ} {j : Fin k} {u : Node k} (h : near j u) :
    selected j (decide (u=j.succ))=u := by
  rcases h with rfl|rfl
  · simp [selected,Fin.ne_of_lt j.castSucc_lt_succ]
  · simp [selected]

private theorem resolved {k : ℕ} (j : Fin k) (b : Bool) : decide (selected j b=j.succ)=b := by
  cases b <;> simp [selected,Fin.ne_of_lt j.castSucc_lt_succ]

private def original (k : ℕ) : Inc (@edge k) ≃
    ((Node k×Node k)⊕((Node k×Fin k×Bool)⊕(Node k×Fin k×Bool))) where
  toFun
    | ⟨(.inl (r,c),.inl _),_⟩ => .inl (r,c)
    | ⟨(.inl (r,c),.inr (_,j)),_⟩ => .inr (.inl (r,j,decide (c=j.succ)))
    | ⟨(.inr (c,j),.inl (r,_)),_⟩ => .inr (.inr (c,j,decide (r=j.succ)))
    | ⟨(.inr _,.inr _),h⟩ => False.elim h
  invFun
    | .inl (r,c)=>⟨(.inl (r,c),.inl (r,c)),rfl,rfl⟩
    | .inr (.inl (r,j,b))=>⟨(.inl (r,selected j b),.inr (r,j)),rfl,selectedNear ..⟩
    | .inr (.inr (c,j,b))=>⟨(.inr (c,j),.inl (selected j b,c)),rfl,selectedNear ..⟩
  left_inv := by
    rintro ⟨⟨⟨r,c⟩|⟨c,j⟩,⟨u,v⟩|⟨u,i⟩⟩,h⟩
    · obtain ⟨rfl,rfl⟩:=h; rfl
    · obtain ⟨rfl,h⟩:=h
      apply Subtype.ext
      simp [chosen h]
    · obtain ⟨rfl,h⟩:=h
      apply Subtype.ext
      simp [chosen h]
    · exact False.elim h
  right_inv := by
    rintro (⟨r,c⟩|⟨r,j,b⟩|⟨c,j,b⟩) <;> simp [resolved]

/-- Exact number of physical edges of the port graph and its long subdivisions. -/
theorem family (k h : ℕ) : Nat.card (Inc (physical k h))=
    (2*h+1)*(k+1)^2+4*(k+1)*k := by
  rw [physical,familyBoard,count_run]
  change Nat.card (Inc (@edge k))+_=_
  rw [Nat.card_congr (original k),length_operations]
  simp [Node,Nat.card_eq_fintype_card]
  ring

theorem deficit (k h : ℕ) :
    Nat.card (Attach.Slots (Attach.leftDeg (physical k h)))=(h+1)*(k+1)^2+(k+1) := by
  classical
  let E:=physical k h
  have hs : ∀ i,Attach.leftDeg E i≤3 := (degree_family h (0 : Matrix (Node k) (Node k) ℕ)).1
  have eq : (∑ i,Attach.leftDeg E i)=Nat.card (Inc E) := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr
      {toFun:=fun ⟨i,j,h⟩=>⟨(i,j),h⟩,invFun:=fun ⟨(i,j),h⟩=>⟨i,j,h⟩,
       left_inv:=fun _=>rfl,right_inv:=fun _=>rfl}
  have slots : Nat.card (Attach.Slots (Attach.leftDeg E))+Nat.card (Inc E)=3*Nat.card (Side k h) := by
    change Nat.card (Σ i,Fin (3-Attach.leftDeg E i))+_=_
    rw [Nat.card_sigma,←eq]
    simp only [Nat.card_fin,←Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Side k h,3 := Finset.sum_congr rfl (fun i _=>Nat.sub_add_cancel (hs i))
      _ = _ := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  rw [card_side,family] at slots
  have id : 3*((k+1)^2+(k+1)*k+h*(k+1)^2)=
      ((h+1)*(k+1)^2+(k+1))+((2*h+1)*(k+1)^2+4*(k+1)*k) := by ring
  change Nat.card (Attach.Slots (Attach.leftDeg E))=_
  omega

end Edges
end SparsePermanent
#print axioms SparsePermanent.Edges.family
#print axioms SparsePermanent.Edges.deficit
