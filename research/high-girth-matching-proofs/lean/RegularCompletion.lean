import AttachFlow
import AttachMatch
import PaddingProjection
import FamilyShape
import GirthExact

namespace SparsePermanent
universe u

namespace Attach
variable {I B : Type} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B]

/-- The type of physical vertices on one side of the regularization. Each
missing degree unit on the original left side gets a private reservoir. -/
abbrev Side (E : I→I→Prop) (B : Type) := I⊕(Slots (leftDeg E)×B)

theorem order_bound (E : I→I→Prop) :
    Nat.card (Side E B) ≤ Nat.card I*(1+3*Nat.card B) := by
  classical
  change Nat.card (I⊕(Slots (leftDeg E)×B))≤_
  rw [Nat.card_sum,Nat.card_prod]
  have bound : Nat.card (Slots (leftDeg E))≤3*Nat.card I := by
    change Nat.card (Σ i,Fin (3-leftDeg E i))≤_
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    simp only [Fintype.card_fin]
    calc
      _ ≤ ∑ _i : I,3 := Finset.sum_le_sum (fun _ _=>Nat.sub_le ..)
      _ = _ := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  calc
    _ ≤ Nat.card I + 3*Nat.card I * Nat.card B := Nat.add_le_add_left (Nat.mul_le_mul_right _ bound) _
    _ = _ := by ring

/-- One graph simultaneously works for all coefficient semirings. Its degree
is exactly three on both sides, its girth is at least the common lower bound,
and its generic permanent projects onto that of the initial graph. -/
theorem complete (E : I→I→Prop) (K : B→B→Prop) (x y : B) (g : ℕ)
    (hit : K x y) (L : ∀ i,leftDeg E i≤3) (R : ∀ j,rightDeg E j≤3)
    (KL : ∀ i,leftDeg K i=3) (KR : ∀ j,rightDeg K j=3)
    (base : (g:ℕ∞)≤(bipGraph E).egirth) (res : (g:ℕ∞)≤(bipGraph K).egirth) :
    ∃ H : Side E B→Side E B→Prop,
      (∀ i,leftDeg H i=3) ∧ (∀ j,rightDeg H j=3) ∧
      (g:ℕ∞)≤(bipGraph H).egirth ∧
      ∀ (F : Type u) [CommSemiring F],∃ r : EdgeVar H→Leaf (EdgeVar E),
        Leaf.projection F r (genericPermanent F H)=genericPermanent F E := by
  classical
  obtain ⟨V,lu,rv⟩:=pair_deficits E L R
  let U : Slots (leftDeg E)→I := Sigma.fst
  let H:= attach E K U V x y
  obtain ⟨hl,hr⟩:=cubic E K U V x y hit lu rv KL KR
  refine ⟨H,hl,hr,girth_preserved hit base res,?_⟩
  intro F _
  obtain ⟨p,valid,avoid⟩:=matching_avoids K x y KL KR
  let q:=Equiv.prodCongr (Equiv.refl (Slots (leftDeg E))) p
  apply padded_projection F E H q (fun _ _ h=>h)
  rintro ⟨d,a⟩
  exact ⟨rfl,valid a,fun ⟨e,h⟩=>avoid (e ▸ h)⟩

end Attach

private theorem generic_transport {I : Type} (F : Type u) [CommSemiring F]
    (E : I→I→Prop) (Q : MvPolynomial (EdgeVar E) F→Prop)
    {f₁ f₂ : Fintype I} {d₁ d₂ : DecidableEq I}
    (h : Q (@genericPermanent I f₁ d₁ F _ E)) : Q (@genericPermanent I f₂ d₂ F _ E) := by
  cases Subsingleton.elim f₁ f₂
  cases Subsingleton.elim d₁ d₂
  exact h

open Classical in
/-- A separate field-independent cubic graph exists for each admissible
reservoir and dense dimension. Computing its generic permanent, exactly or
with formal Laurent approximation, computes the dense permanent at the same
budget. The girth guarantee holds for the very same physical graph. -/
theorem cubic_hard_family {B : Type} [Fintype B] [DecidableEq B] (k h g : ℕ)
    (K : B→B→Prop) (x y : B) (hit : K x y)
    (KL : ∀ i,Attach.leftDeg K i=3) (KR : ∀ j,Attach.rightDeg K j=3)
    (res : (g:ℕ∞)≤(bipGraph K).egirth) (height : g≤4*(2*h+3)) :
    ∃ H : Attach.Side (physical k h) B→Attach.Side (physical k h) B→Prop,
      (∀ i,Attach.leftDeg H i=3) ∧ (∀ j,Attach.rightDeg H j=3) ∧
      (g:ℕ∞)≤(bipGraph H).egirth ∧ ∀ (F : Type u) [Field F] (s : ℕ),
      (Statement.Computes (genericPermanent F H) s → Statement.Computes (Statement.perm F (k+1)) s) ∧
      (Statement.Approximates (genericPermanent F H) s → Statement.Approximates (Statement.perm F (k+1)) s) := by
  classical
  let A:= (0 : Matrix (Node k) (Node k) ℕ)
  have deg:=degree_family h A
  have giro : (g:ℕ∞)≤(bipGraph (physical k h)).egirth :=
    (ENat.coe_le_coe.mpr height).trans (family_egirth_lower h A)
  obtain ⟨H,l,r,gr,proj⟩:=Attach.complete (physical k h) K x y g hit deg.1 deg.2 KL KR giro res
  refine ⟨H,l,r,gr,fun F _ s=>?_⟩
  obtain ⟨p,eq⟩:=proj F
  have shape : physical k h=(familyBoard h (dense F k)).adj:=family_shape h A (dense F k)
  constructor
  · intro hc
    apply computes_perm (h:=h)
    unfold familyGeneric
    rw [←shape]
    apply generic_transport F (physical k h) (fun z=>Statement.Computes z s)
    apply (congrArg (fun z=>Statement.Computes z s) eq).mp
    apply Leaf.computes p
    exact generic_transport F H (fun z=>Statement.Computes z s) hc
  · intro hc
    apply approximates_perm (h:=h)
    unfold familyGeneric
    rw [←shape]
    apply generic_transport F (physical k h) (fun z=>Statement.Approximates z s)
    apply (congrArg (fun z=>Statement.Approximates z s) eq).mp
    apply Leaf.approximates p
    exact generic_transport F H (fun z=>Statement.Approximates z s) hc

end SparsePermanent
#print axioms SparsePermanent.Attach.order_bound
#print axioms SparsePermanent.Attach.complete
#print axioms SparsePermanent.cubic_hard_family
