import PairedLayers
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace AlgebraicMeta.GateLeaves
open Finset MvPolynomial Function
open AlgebraicMeta.Paired

inductive Gate (V R W : Type*) where
  | var : V → Gate V R W
  | scalar : R → Gate V R W
  | add : W → W → Gate V R W
  | mul : W → W → Gate V R W

def Gate.child {V R W : Type*} : Gate V R W → W → Prop
  | .var _, _ | .scalar _, _ => False
  | .add a b, w | .mul a b, w => w=a ∨ w=b

def Gate.binary {V R W : Type*} : Gate V R W → Bool
  | .var _ | .scalar _ => false
  | .add _ _ | .mul _ _ => true

def Gate.operand {V R W : Type*} (fallback : W) : Gate V R W → Bool → W
  | .var _, _ | .scalar _, _ => fallback
  | .add a b, t | .mul a b, t => if t then b else a

noncomputable def Gate.polynomial {V R W : Type*} [CommSemiring R]
    (values : W → MvPolynomial V R) : Gate V R W → MvPolynomial V R
  | .var v => X v
  | .scalar r => C r
  | .add a b => values a + values b
  | .mul a b => values a * values b

abbrev Reach {V R W : Type*} (net : W → Gate V R W) :=
  Relation.ReflTransGen (fun x y => (net x).child y)

private theorem child_operand {V R W : Type*} (fallback : W) (g : Gate V R W) (x : W)
    (hx : g.child x) : g.binary=true ∧ ∃ b, g.operand fallback b=x := by
  cases g with
  | var _ | scalar _ => cases hx
  | add a b | mul a b =>
    refine ⟨rfl,?_⟩
    rcases hx with rfl|rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩

theorem essential_leaf {V R W : Type*} [CommSemiring R] (net : W → Gate V R W)
    (rank : W → ℕ) (acyclic : ∀ w z, (net w).child z → rank z<rank w)
    (values : W → MvPolynomial V R) (correct : ∀ w, values w=(net w).polynomial values)
    (root : W) (v : V) (need : Essential (values root) v) :
    ∃ w, Reach net root w ∧ net w=.var v := by
  classical
  obtain ⟨x,y,away,diff⟩ := need
  by_contra! absent
  apply diff
  have go (m : ℕ) : ∀ w, rank w=m → Reach net root w → eval x (values w)=eval y (values w) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro w eq reach
      have below (z) (hz : (net w).child z) :=
        ih (rank z) (eq ▸ acyclic w z hz) z rfl (reach.tail hz)
      rw [correct w]
      cases kg : net w with
      | var j =>
        have hv : j≠v := by rintro rfl;exact absent w reach kg
        simpa [Gate.polynomial] using away j hv
      | scalar k => simp [Gate.polynomial]
      | add a b =>
        have ha := below a (by rw [kg];exact Or.inl rfl)
        have hb := below b (by rw [kg];exact Or.inr rfl)
        simp [Gate.polynomial,ha,hb]
      | mul a b =>
        have ha := below a (by rw [kg];exact Or.inl rfl)
        have hb := below b (by rw [kg];exact Or.inr rfl)
        simp [Gate.polynomial,ha,hb]
  exact go _ root rfl .refl

/-- With counted scalar and variable leaves, d essential variables need at
least 2d−1 gates, even if arbitrary subexpressions are shared. -/
theorem essential_size {I V R W : Type*} [Fintype I] [Fintype W] [CommSemiring R]
    (net : W → Gate V R W) (rank : W → ℕ) (acyclic : ∀ w z, (net w).child z → rank z<rank w)
    (values : W → MvPolynomial V R) (correct : ∀ w, values w=(net w).polynomial values)
    (root : W) (labels : I ↪ V) (need : ∀i, Essential (values root) (labels i)) :
    2*Fintype.card I ≤ Fintype.card W+1 := by
  classical
  let live := univ.filter (Reach net root)
  let bins := live.filter (fun w => (net w).binary)
  let leaves := live \ bins
  have hb : bins ⊆ live := filter_subset _ _
  have liveRoot : root∈live := by simp [live,Relation.ReflTransGen.refl]
  choose pick hp using fun i => essential_leaf net rank acyclic values correct root (labels i) (need i)
  have leavesPick (i) : pick i∈leaves := by
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,(hp i).1⟩,?_⟩
    intro bad
    have e := (mem_filter.mp bad).2
    rw [(hp i).2] at e
    contradiction
  let pick' (i : I) : {w // w∈leaves} := ⟨pick i,leavesPick i⟩
  have inj : Injective pick' := by
    intro a b e
    have e' : pick a=pick b := congrArg Subtype.val e
    apply labels.injective
    exact Gate.var.inj ((hp a).2.symm.trans (e' ▸ (hp b).2))
  have lbound : Fintype.card I ≤ leaves.card := by simpa using Fintype.card_le_of_injective pick' inj
  let ports := bins ×ˢ (univ : Finset Bool)
  let atPort (x : W × Bool) := (net x.1).operand root x.2
  have cover : live.erase root ⊆ ports.image atPort := by
    intro w hw
    obtain ⟨ne,hw⟩ := mem_erase.mp hw
    have reach := (mem_filter.mp hw).2
    cases reach with
    | refl => exact (ne rfl).elim
    | tail lead step =>
      obtain ⟨bin,b,eq⟩ := child_operand root _ _ step
      apply mem_image.mpr
      exact ⟨⟨_,b⟩,by simp [ports,bins,live,lead,bin],eq⟩
  have cb := (card_le_card cover).trans (card_image_le (s:=ports) (f:=atPort))
  have decomp : leaves.card + bins.card=live.card := card_sdiff_add_card_eq_card hb
  have big : live.card ≤ Fintype.card W := card_le_univ _
  simp only [card_erase_of_mem liveRoot,ports,card_product,card_univ,Fintype.card_bool] at cb
  omega

end AlgebraicMeta.GateLeaves
#print axioms AlgebraicMeta.GateLeaves.essential_leaf
#print axioms AlgebraicMeta.GateLeaves.essential_size
