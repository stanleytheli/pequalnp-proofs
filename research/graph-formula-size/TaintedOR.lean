import Mathlib

/-! OR query counting when every desired set has at most four labels. -/
namespace TaintedOR
open Finset
open scoped Classical

structure Queries (V I : Type*) [DecidableEq V] where
  need : I → Finset V
  supply : I → Finset V
  sub : ∀ i, need i ⊆ supply i
  small : ∀ i, (need i).card ≤ 4
  linear : ∀ i j, i≠j → ((need i)∩(need j)).card ≤ 1

namespace Queries
variable {V I : Type*} [DecidableEq V] (Q : Queries V I)

def err (i : I) := (Q.supply i \ Q.need i).card

def useful (i : I) (A B : Finset V) : Prop :=
  A∪B ⊆ Q.supply i ∧
    (∃ x∈A\B, x∈Q.need i) ∧ (∃ y∈B\A, y∈Q.need i)

def minor (i : I) (A B : Finset V) : Prop :=
  Q.err i≤1 ∧ Q.useful i A B

def major (i : I) (A B : Finset V) : Prop :=
  ((Q.need i).card=4 ∧ Q.err i=2 ∧ A∪B=Q.supply i) ∨
    (Q.minor i A B ∧ (Q.err i=0 ∨ 3≤((A∪B)∩Q.need i).card))

private theorem overlap {i j : I} (ne : i≠j) (W : Finset V) (hi : W⊆Q.need i)
    (hj : W⊆Q.supply j) : W.card ≤ 1+Q.err j := by
  have sub : W ⊆ (Q.need i∩Q.need j)∪(Q.supply j\Q.need j) := by
    intro x hx
    by_cases h : x∈Q.need j
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi hx,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hj hx,h⟩)
  exact (Finset.card_le_card sub).trans ((Finset.card_union_le ..).trans
    (Nat.add_le_add_right (Q.linear i j ne) _))

private theorem useful_wide {i : I} {A B : Finset V} (h : Q.useful i A B) :
    2≤((A∪B)∩Q.need i).card := by
  obtain ⟨_,⟨x,hx,xq⟩,⟨y,hy,yq⟩⟩ := h
  apply Finset.one_lt_card.mpr
  refine ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1,xq⟩,
    y,Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hy).1,yq⟩,?_⟩
  rintro rfl
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

private theorem across {i j : I} {A B : Finset V} (ne : i≠j)
    (h : Q.major i A B) : ¬(Q.major j A B ∨ Q.minor j A B) := by
  intro hj
  let W := A∪B
  have allj : W⊆Q.supply j ∧ Q.err j≤2 := by
    rcases hj with hm | hm
    · rcases hm with ⟨_,err,eq⟩ | ⟨hm,_⟩
      · exact ⟨eq.le,by omega⟩
      · exact ⟨hm.2.1,by have := hm.1; omega⟩
    · exact ⟨hm.2.1,by have := hm.1; omega⟩
  rcases h with ⟨four,_,eq⟩ | ⟨hminor,hstrong⟩
  · have H := Q.overlap ne (Q.need i) Finset.Subset.rfl ((Q.sub i).trans (eq ▸ allj.1))
    omega
  · obtain ⟨hi,ui⟩ := hminor
    have wideJ : 2≤(W∩Q.need j).card ∧ Q.err j≤1 := by
      rcases hj with hm | hm
      · rcases hm with ⟨four,_,eq⟩ | ⟨hm,_⟩
        · have hbad := Q.overlap ne.symm (Q.need j) Finset.Subset.rfl
              ((Q.sub j).trans (eq ▸ ui.1))
          omega
        · exact ⟨Q.useful_wide hm.2,hm.1⟩
      · exact ⟨Q.useful_wide hm.2,hm.1⟩
    rcases hstrong with hz | hw
    · have H := Q.overlap ne.symm (W∩Q.need j) Finset.inter_subset_right
          (Finset.inter_subset_left.trans ui.1)
      omega
    · have H := Q.overlap ne (W∩Q.need i) Finset.inter_subset_right
          (Finset.inter_subset_left.trans allj.1)
      change 3≤(W∩Q.need i).card at hw
      omega

private theorem triple_width {i j : I} {A B : Finset V} (neq : i≠j)
    (hi : Q.minor i A B) (hj : Q.minor j A B) : (A∪B).card≤3 := by
  let W := A∪B
  have wi := hi.2.1
  have lim := Q.overlap neq (W∩Q.need i) Finset.inter_subset_right
    (Finset.inter_subset_left.trans hj.2.1)
  have rem : W\Q.need i ⊆ Q.supply i\Q.need i :=
    fun _ h => Finset.mem_sdiff.mpr ⟨wi (Finset.mem_sdiff.mp h).1,(Finset.mem_sdiff.mp h).2⟩
  have add := Finset.card_sdiff_add_card_inter W (Q.need i)
  have smallR := Finset.card_le_card rem
  change (W\Q.need i).card≤Q.err i at smallR
  have si := hi.1
  have sj := hj.1
  change W.card≤3
  omega

theorem gate_budget [Fintype I] (A B : Finset V) :
    let big := Finset.univ.filter (fun i => Q.major i A B)
    let little := Finset.univ.filter (fun i => Q.minor i A B ∧ ¬Q.major i A B)
    2 * big.card + little.card ≤ 2 := by
  classical
  dsimp only
  let big := Finset.univ.filter (fun i => Q.major i A B)
  let little := Finset.univ.filter (fun i => Q.minor i A B ∧ ¬Q.major i A B)
  change 2*big.card+little.card≤2
  by_cases hb : big.Nonempty
  · obtain ⟨i,im⟩ := hb
    have hi : Q.major i A B := (Finset.mem_filter.mp im).2
    have one : big⊆{i} := by
      intro j hj
      rw [Finset.mem_singleton]
      by_contra ne
      exact Q.across (Ne.symm ne) hi (Or.inl (Finset.mem_filter.mp hj).2)
    have emp : little=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨jm,jn⟩ := (Finset.mem_filter.mp hj).2
      by_cases ij : i=j
      · exact jn (ij ▸ hi)
      · exact Q.across ij hi (Or.inr jm)
    have bc := Finset.card_le_card one
    simp only [Finset.card_singleton] at bc
    simp [emp,show big.card=1 by have := Finset.card_pos.mpr ⟨i,im⟩; omega]
  · have be := Finset.not_nonempty_iff_eq_empty.mp hb
    simp only [be,Finset.card_empty,Nat.mul_zero,Nat.zero_add]
    by_contra fail
    obtain ⟨i,im,j,jm,k,km,ij,ik,jk⟩ := Finset.two_lt_card.mp (by omega : 2<little.card)
    have get (i : I) (h : i∈little) : Q.minor i A B := (Finset.mem_filter.mp h).2.1
    have size := Q.triple_width ij (get i im) (get j jm)
    have disjoint : Disjoint (A\B) (B\A) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
    have cardAB := Finset.card_union_of_disjoint disjoint
    have sub : (A\B)∪(B\A)⊆A∪B := by
      intro x h
      rcases Finset.mem_union.mp h with l | r
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp l).1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp r).1
    have cc := Finset.card_le_card sub
    have bound : (A\B).card*(B\A).card ≤ 2 := by
      have : (A\B).card+(B\A).card≤3 := by omega
      have upper : (A\B).card≤3 := by omega
      interval_cases hA : (A\B).card <;> omega
    have witness (i : little) : ∃ p∈(A\B)×ˢ(B\A), p.1∈Q.need i ∧ p.2∈Q.need i := by
      obtain ⟨_,⟨x,hx,xq⟩,⟨y,hy,yq⟩⟩ := (get _ i.property).2
      exact ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,xq,yq⟩
    choose pair pairIn pairL pairR using witness
    have inject : Function.Injective (fun i : little => (⟨pair i,pairIn i⟩ : ↥((A\B)×ˢ(B\A)))) := by
      intro a b eq
      have pp : pair a = pair b := congrArg Subtype.val eq
      apply Subtype.ext
      by_contra ne
      have hh := Finset.card_le_one.mp (Q.linear a b ne) (pair a).1
        (Finset.mem_inter.mpr ⟨pairL a,pp ▸ pairL b⟩) (pair a).2
        (Finset.mem_inter.mpr ⟨pairR a,pp ▸ pairR b⟩)
      have first := (Finset.mem_sdiff.mp (Finset.mem_product.mp (pairIn a)).1).2
      have second := (Finset.mem_sdiff.mp (Finset.mem_product.mp (pairIn a)).2).1
      exact first (hh ▸ second)
    have count := Fintype.card_le_of_injective _ inject
    simp only [Fintype.card_coe,Finset.card_product] at count
    omega

end Queries
end TaintedOR

#print axioms TaintedOR.Queries.gate_budget
