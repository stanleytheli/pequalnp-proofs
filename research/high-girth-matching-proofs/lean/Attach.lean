import FlowCycle

namespace SparsePermanent

/-- A fresh punctured bipartite reservoir per paired unit of degree deficit.
U and V select original vertices on the left and right; x and y form the
removed edge in each reservoir copy. -/
def attach {I B D : Type} (E : I→I→Prop) (K : B→B→Prop) (U V : D→I) (x y : B) :
    (I⊕(D×B))→(I⊕(D×B))→Prop
  | .inl i,.inl j => E i j
  | .inl i,.inr (d,b) => U d=i ∧ b=y
  | .inr (d,a),.inl j => V d=j ∧ a=x
  | .inr (d,a),.inr (e,b) => d=e ∧ K a b ∧ ¬(a=x ∧ b=y)

namespace Attach
variable {I B D : Type} (E : I→I→Prop) (K : B→B→Prop) (U V : D→I) (x y : B)

theorem flip (i j : I⊕(D×B)) : attach E K U V x y i j ↔
    attach (fun a b=>E b a) (fun a b=>K b a) V U y x j i := by
  rcases i with i|⟨d,a⟩ <;> rcases j with j|⟨e,b⟩ <;> simp [attach,eq_comm,and_comm]

private def oldLeft (i : I) : {j // attach E K U V x y (.inl i) j} ≃ {j // E i j} ⊕ {d // U d=i} where
  toFun
    | ⟨.inl j,h⟩ => .inl ⟨j,h⟩
    | ⟨.inr (d,_),h⟩ => .inr ⟨d,h.1⟩
  invFun
    | .inl ⟨j,h⟩ => ⟨.inl j,h⟩
    | .inr ⟨d,h⟩ => ⟨.inr (d,y),⟨h,rfl⟩⟩
  left_inv := by
    rintro ⟨j|⟨d,b⟩,h⟩
    · rfl
    · apply Subtype.ext
      exact congrArg (fun z=>Sum.inr (d,z)) h.2.symm
  right_inv := by rintro (⟨j,h⟩|⟨j,h⟩) <;> rfl

private noncomputable def copyLeft (hit : K x y) (d : D) (a : B) :
    {j // attach E K U V x y (.inr (d,a)) j} ≃ {b // K a b} := by
  classical
  refine { toFun := fun v=> match v with
            | ⟨.inl _,h⟩ => ⟨y,h.2 ▸ hit⟩
            | ⟨.inr (_,b),h⟩ => ⟨b,h.2.1⟩
           invFun := fun b=>if eq : a=x ∧ b.val=y then ⟨.inl (V d),⟨rfl,eq.1⟩⟩
             else ⟨.inr (d,b.val),⟨rfl,b.prop,eq⟩⟩
           left_inv := ?_, right_inv := ?_ }
  · rintro ⟨j|⟨e,b⟩,h⟩
    · apply Subtype.ext
      simp [h.2,h.1]
    · apply Subtype.ext
      have eq : d=e := h.1
      simp [h.2.2,eq]
  · rintro ⟨b,hb⟩
    by_cases eq : a=x ∧ b=y
    · apply Subtype.ext; simp [eq,eq.2]
    · apply Subtype.ext; simp [eq]

variable [Finite I] [Finite B] [Finite D]

theorem left_old_degree (i : I) : Nat.card {j // attach E K U V x y (.inl i) j}=
    Nat.card {j // E i j}+Nat.card {d // U d=i} :=
  (Nat.card_congr (oldLeft E K U V x y i)).trans Nat.card_sum

theorem left_copy_degree (hit : K x y) (d : D) (a : B) :
    Nat.card {j // attach E K U V x y (.inr (d,a)) j}=Nat.card {b // K a b} :=
  Nat.card_congr (copyLeft E K U V x y hit d a)

theorem right_old_degree (j : I) : Nat.card {i // attach E K U V x y i (.inl j)}=
    Nat.card {i // E i j}+Nat.card {d // V d=j} := by
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun i=>flip E K U V x y i (.inl j)))).trans
    (left_old_degree (fun a b=>E b a) (fun a b=>K b a) V U y x j)

theorem right_copy_degree (hit : K x y) (d : D) (b : B) :
    Nat.card {i // attach E K U V x y i (.inr (d,b))}=Nat.card {a // K a b} := by
  exact (Nat.card_congr (Equiv.subtypeEquivRight (fun i=>flip E K U V x y i (.inr (d,b))))).trans
    (left_copy_degree (fun a b=>E b a) (fun a b=>K b a) V U y x hit d b)

/-- The displayed completion is genuinely cubic when U,V enumerate the missing
degree units of the physical base and K is a cubic reservoir. -/
theorem cubic (hit : K x y)
    (L : ∀ i,Nat.card {j // E i j}+Nat.card {d // U d=i}=3)
    (R : ∀ j,Nat.card {i // E i j}+Nat.card {d // V d=j}=3)
    (KL : ∀ a,Nat.card {b // K a b}=3) (KR : ∀ b,Nat.card {a // K a b}=3) :
    (∀ a,Nat.card {b // attach E K U V x y a b}=3) ∧
    (∀ b,Nat.card {a // attach E K U V x y a b}=3) := by
  constructor
  · rintro (i|⟨d,a⟩)
    · exact (left_old_degree E K U V x y i).trans (L i)
    · exact (left_copy_degree E K U V x y hit d a).trans (KL a)
  · rintro (j|⟨d,b⟩)
    · exact (right_old_degree E K U V x y j).trans (R j)
    · exact (right_copy_degree E K U V x y hit d b).trans (KR b)

end Attach
end SparsePermanent
#print axioms SparsePermanent.Attach.cubic
