import Attach

namespace SparsePermanent
namespace Attach
open Finset
variable {I : Type} [Fintype I]

noncomputable abbrev leftDeg (E : I→I→Prop) (i : I) := Nat.card {j // E i j}
noncomputable abbrev rightDeg (E : I→I→Prop) (j : I) := Nat.card {i // E i j}

def Slots (degree : I→ℕ) := Σ i,Fin (3-degree i)

noncomputable instance (degree : I→ℕ) : Fintype (Slots degree) := inferInstanceAs (Fintype (Σ i,Fin (3-degree i)))

instance (degree : I→ℕ) [DecidableEq I] : DecidableEq (Slots degree) :=
  inferInstanceAs (DecidableEq (Σ i,Fin (3-degree i)))

private def fiber (f : I→ℕ) (i : I) : {d : Slots f // d.1=i} ≃ Fin (3-f i) where
  toFun := fun ⟨⟨j,a⟩,eq⟩=>eq ▸ a
  invFun := fun a=>⟨⟨i,a⟩,rfl⟩
  left_inv := by rintro ⟨⟨j,a⟩,rfl⟩; rfl
  right_inv := fun _=>rfl

private def flipInc (E : I→I→Prop) : (Σ i,{j // E i j}) ≃ (Σ j,{i // E i j}) where
  toFun := fun ⟨i,j,h⟩=>⟨j,i,h⟩
  invFun := fun ⟨j,i,h⟩=>⟨i,j,h⟩
  left_inv := by rintro ⟨i,j,h⟩; rfl
  right_inv := by rintro ⟨j,i,h⟩; rfl

private theorem balances (E : I→I→Prop) : (∑ i,leftDeg E i) = ∑ j,rightDeg E j := by
  classical
  have h:=Fintype.card_congr (flipInc E)
  simpa [leftDeg,rightDeg,Nat.card_eq_fintype_card,Fintype.card_sigma] using h

private theorem slotCard (f : I→ℕ) (bound : ∀ i, f i≤3) :
    Fintype.card (Slots f)+∑ i,f i=3*Fintype.card I := by
  change Fintype.card (Σ i,Fin (3-f i))+_=_
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin,←sum_add_distrib]
  calc
    _ = ∑ _i : I,3 := sum_congr rfl (fun i _=>Nat.sub_add_cancel (bound i))
    _ = _ := by simp [Nat.mul_comm]

/-- A balanced bipartite subcubic base automatically admits a pairing of all
missing left and right degree units, including repeated incidents at a vertex. -/
theorem pair_deficits (E : I→I→Prop) (L : ∀ i,leftDeg E i≤3) (R : ∀ j,rightDeg E j≤3) :
    ∃ V : Slots (leftDeg E)→I,
      (∀ i,leftDeg E i + Nat.card {d : Slots (leftDeg E) // d.1=i}=3) ∧
      (∀ j,rightDeg E j+Nat.card {d : Slots (leftDeg E) // V d=j}=3) := by
  classical
  have a:=slotCard _ L
  have b:=slotCard _ R
  have sums:=balances E
  have card : Fintype.card (Slots (leftDeg E))=Fintype.card (Slots (rightDeg E)) := by omega
  let e:=Fintype.equivOfCardEq card
  refine ⟨fun d=>(e d).1,fun i=>?_,fun j=>?_⟩
  · rw [Nat.card_congr (fiber _ i),Nat.card_fin]
    have hi:=L i
    omega
  · let pull : {d : Slots (leftDeg E) // (e d).1=j} ≃ {d : Slots (rightDeg E) // d.1=j} :=
      Equiv.subtypeEquiv e (fun _=>Iff.rfl)
    rw [Nat.card_congr (pull.trans (fiber _ j)),Nat.card_fin]
    have hj:=R j
    omega

end Attach
end SparsePermanent
#print axioms SparsePermanent.Attach.pair_deficits
