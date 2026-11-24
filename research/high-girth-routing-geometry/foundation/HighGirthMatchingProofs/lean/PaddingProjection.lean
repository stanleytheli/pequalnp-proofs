import Consequence
import Padding

namespace SparsePermanent
open MvPolynomial
universe u
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A graph containing all old edges and a fixed complementary perfect matching
has an edge-variable projection onto the old graph. All attachments and all
unchosen complementary edges are assigned zero. -/
theorem padded_projection (F : Type u) [CommSemiring F]
    (E : I→I→Prop) (H : (I⊕J)→(I⊕J)→Prop) (p : Equiv.Perm J)
    (old : ∀ i j,E i j→H (.inl i) (.inl j)) (fresh : ∀ a,H (.inr a) (.inr (p a))) :
    ∃ r : EdgeVar H→Leaf (EdgeVar E),
      Leaf.projection F r (genericPermanent F H)=genericPermanent F E := by
  classical
  let A : Matrix I I (MvPolynomial (EdgeVar E) F) := fun y x=>
    if h : E x y then X (⟨(x,y),h⟩ : EdgeVar E) else 0
  let B := padded A p
  have off : ∀ x y, ¬H x y → B y x=0 := by
    rintro (i|a) (j|b) bad
    · have no : ¬E i j := fun h=>bad (old i j h)
      simp [B,padded,A,no]
    · rfl
    · rfl
    · have no : p a≠b := by rintro rfl; exact bad (fresh a)
      simp [B,padded,no]
  have valid (e : EdgeVar H) : ∃ l : Leaf (EdgeVar E),l.poly F=B e.val.2 e.val.1 := by
    rcases e with ⟨⟨i|a,j|b⟩,he⟩
    · by_cases h : E i j
      · exact ⟨.var ⟨(i,j),h⟩,by simp [B,padded,A,h,Leaf.poly]⟩
      · exact ⟨.zero,by simp [B,padded,A,h,Leaf.poly]⟩
    · exact ⟨.zero,rfl⟩
    · exact ⟨.zero,rfl⟩
    · by_cases h : p a=b
      · exact ⟨.one,by simp [B,padded,h,Leaf.poly]⟩
      · exact ⟨.zero,by simp [B,padded,h,Leaf.poly]⟩
  choose r labels using valid
  exact ⟨r,(generic_eval H B off r labels).trans (permanent_padded A p)⟩

end SparsePermanent
#print axioms SparsePermanent.padded_projection
