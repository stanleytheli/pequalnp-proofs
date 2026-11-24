import OddSubdivision

namespace SparsePermanent
open Finset
namespace DirectedSplit
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

/-- Split a vertex's outgoing arcs, moving the selected targets P to a fresh
unit-loop vertex reached by a single unit-weight arc from the original source. -/
def outgoing (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P] : Matrix (Option I) (Option I) R
  | none,none=>1
  | none,some x=>if x=v then 1 else 0
  | some y,none=>if P y then A y v else 0
  | some y,some x=>if x=v ∧ P y then 0 else A y x

private def lift (j : Option I) (p : Equiv.Perm I) := Equiv.Perm.decomposeOption.symm (j,p)
private theorem source (j : Option I) (p : Equiv.Perm I) : lift j p none=j := by simp [lift]
private theorem plain (i : I) (p : Equiv.Perm I) : lift none p (some i)=some (p i) := by simp [lift]
private theorem used {p : Equiv.Perm I} {i j : I} (e : p i=j) :
    lift (some j) p (some i)=none := by simp [lift,e]
private theorem free {p : Equiv.Perm I} {i j : I} (e : p i≠j) :
    lift (some j) p (some i)=some (p i) := by simp [lift,Equiv.swap_apply_of_ne_of_ne,e]

private def term (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P]
    (p : Equiv.Perm I) (j : Option I) := ∏ i,outgoing A v P (lift j p i) i

private theorem plain_term (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P]
    (p : Equiv.Perm I) : term A v P p none=if P (p v) then 0 else ∏ i,A (p i) i := by
  by_cases yes : P (p v)
  · rw [if_pos yes]
    exact prod_eq_zero (mem_univ (some v)) (by simp [plain,outgoing,yes])
  · rw [if_neg yes]
    simp only [term,Fintype.prod_option,source,plain,outgoing,one_mul]
    apply prod_congr rfl
    intro i _
    have no : ¬(i=v ∧ P (p i)):=by rintro ⟨rfl,h⟩; exact yes h
    simp [no]

private theorem wrong (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P]
    (p : Equiv.Perm I) (j : I) (miss : j≠p v) : term A v P p (some j)=0 := by
  have inv : p.symm j ≠ v := fun e=>miss (by rw [←e];simp)
  exact prod_eq_zero (mem_univ (some (p.symm j))) (by rw [used (p.apply_symm_apply j)]; simp [outgoing,inv])

private theorem moved_term (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P]
    (p : Equiv.Perm I) : term A v P p (some (p v))=if P (p v) then ∏ i,A (p i) i else 0 := by
  by_cases yes : P (p v)
  · rw [if_pos yes]
    simp only [term,Fintype.prod_option,source]
    rw [show outgoing A v P (some (p v)) none=A (p v) v by simp [outgoing,yes]]
    rw [←mul_prod_erase univ (fun i=>A (p i) i) (mem_univ v),
      ←mul_prod_erase univ (fun i=>outgoing A v P (lift (some (p v)) p (some i)) (some i)) (mem_univ v),
      used (rfl : p v=p v)]
    simp only [outgoing,ite_true,one_mul]
    congr 1
    apply prod_congr rfl
    intro i hi
    have ne : i≠v := (mem_erase.mp hi).1
    rw [free (fun e=>ne (p.injective e))]
    simp [outgoing,ne]
  · rw [if_neg yes]
    exact prod_eq_zero (mem_univ none) (by simp [source,outgoing,yes])

/-- Splitting a set of outgoing arcs preserves the permanent over every
commutative semiring, including when the loop itself is selected. -/
theorem permanent_outgoing (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P] :
    (outgoing A v P).permanent=A.permanent := by
  classical
  unfold Matrix.permanent
  calc
    _ = ∑ q : Option I×Equiv.Perm I,term A v P q.2 q.1 := by
      apply Fintype.sum_equiv Equiv.Perm.decomposeOption
      intro p
      change _=∏ i,outgoing A v P (Equiv.Perm.decomposeOption.symm (Equiv.Perm.decomposeOption p) i) i
      rw [Equiv.symm_apply_apply]
    _ = ∑ j,∑ p,term A v P p j := Fintype.sum_prod_type _
    _ = ∑ p,∑ j,term A v P p j := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p _
      rw [Fintype.sum_option,Finset.sum_eq_single (p v)
        (fun j _ h=>wrong A v P p j h) (by simp),plain_term,moved_term]
      split <;> simp

def incoming (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P] :=
  (outgoing A.transpose v P).transpose

theorem permanent_incoming (A : Matrix I I R) (v : I) (P : I→Prop) [DecidablePred P] :
    (incoming A v P).permanent=A.permanent := by
  rw [incoming,Matrix.permanent_transpose,permanent_outgoing,Matrix.permanent_transpose]

end DirectedSplit
end SparsePermanent
#print axioms SparsePermanent.DirectedSplit.permanent_outgoing
#print axioms SparsePermanent.DirectedSplit.permanent_incoming
