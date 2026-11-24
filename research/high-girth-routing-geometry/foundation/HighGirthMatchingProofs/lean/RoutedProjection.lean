import RoutedModel
import PaddingProjection

namespace SparsePermanent
namespace Leaf
variable {U V W : Type}

def bind (s : V→Leaf W) : Leaf V→Leaf W
  | .zero=>.zero
  | .one=>.one
  | .var v=>s v

theorem projection_bind (F : Type*) [CommSemiring F] (r : U→Leaf V) (s : V→Leaf W)
    (f : MvPolynomial U F) : projection F (fun u=>bind s (r u)) f=projection F s (projection F r f) := by
  induction f using MvPolynomial.induction_on with
  | C c=>simp [projection]
  | add p q hp hq=>simp [map_add,hp,hq]
  | mul_X p u hp=>
    simp only [map_mul,hp]
    congr 1
    cases h : r u <;> simp [projection,bind,poly,h]
end Leaf

namespace RoutedModel
open MvPolynomial
universe u

/-- A signature for checking concrete routing witnesses. Supply the sequence of
incoming/outgoing vertex splits, verify their nonzero positions in the active
subgraph and retain one specified matching on the complement. -/
theorem projects {m n : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (F : Type u) [CommSemiring F] (B : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m×Fin m) F))
    (model : Generated (fun i j : Fin m=>X (i,j)) B) (H : (Fin n⊕J)→(Fin n⊕J)→Prop)
    (cover : ∀ i j,B j i≠0→H (.inl i) (.inl j)) (p : Equiv.Perm J)
    (fresh : ∀ a,H (.inr a) (.inr (p a))) :
    ∃ r : EdgeVar H→Leaf (Fin m×Fin m),
      Leaf.projection F r (genericPermanent F H)=Statement.perm F m := by
  classical
  let E:=fun i j=>B j i≠0
  obtain ⟨r,hs⟩:=padded_projection F E H p cover fresh
  let accepts (v : MvPolynomial (Fin m×Fin m) F) := ∃ l : Leaf (Fin m×Fin m),l.poly F=v
  have all := model.labels accepts ⟨.zero,rfl⟩ ⟨.one,rfl⟩ (fun i j=>⟨.var (i,j),rfl⟩)
  have valid (e : EdgeVar E) : ∃ l : Leaf (Fin m×Fin m),l.poly F=B e.val.2 e.val.1:=all _ _
  choose s labels using valid
  have hs' := generic_eval E B (fun i j h=>Classical.not_not.mp h) s labels
  refine ⟨fun u=>Leaf.bind s (r u),?_⟩
  rw [Leaf.projection_bind,hs,hs',model.permanent]
  rfl

end RoutedModel
end SparsePermanent
#print axioms SparsePermanent.RoutedModel.projects
