import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace SparsePermanent
open Finset
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

/-- Replace the edge from c to r by a path of three edges. Its first edge
carries the original weight. The two new vertices occupy a new row and column. -/
def divideEdge (A : Matrix I I R) (r c : I) : Matrix (Option I) (Option I) R
  | none, none => 1
  | some u, none => if u=r then 1 else 0
  | none, some v => if v=c then A r c else 0
  | some u, some v => if u=r ∧ v=c then 0 else A u v

private def extend (p : Equiv.Perm I) (j : Option I) : Equiv.Perm (Option I) :=
  Equiv.swap none j * p.optionCongr

private theorem extend_none (p : Equiv.Perm I) (j : Option I) : extend p j none=j := by
  simp [extend]

private theorem extend_some_free (p : Equiv.Perm I) (j i : I) (h : p i≠j) :
    extend p (some j) (some i)=some (p i) := by
  simp [extend,Equiv.swap_apply_of_ne_of_ne, h]

private theorem extend_some_used (p : Equiv.Perm I) (j i : I) (h : p i=j) :
    extend p (some j) (some i)=none := by
  simp [extend,h]

private theorem extend_none_some (p : Equiv.Perm I) (i : I) :
    extend p none (some i)=some (p i) := by simp [extend]

private def term (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) (j : Option I) :=
  ∏ x, divideEdge A r c (extend p j x) x

private theorem none_term_free (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) (h : p c≠r) :
    term A r c p none=∏ i, A (p i) i := by
  unfold term
  rw [Fintype.prod_option]
  simp only [extend_none, divideEdge,one_mul,extend_none_some]
  apply Finset.prod_congr rfl
  intro i _
  have hn : ¬(p i=r ∧ i=c) := by rintro ⟨e,rfl⟩; exact h e
  simp [divideEdge,hn]

private theorem none_term_used (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) (h : p c=r) :
    term A r c p none=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ (some c))
  simp [extend_none_some,divideEdge,h]

private theorem some_term_outside (A : Matrix I I R) (r c : I) (p : Equiv.Perm I)
    (u : I) (h : u≠r) : term A r c p (some u)=0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ none)
  simp [extend_none,divideEdge,h]

private theorem some_term_free (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) (h : p c≠r) :
    term A r c p (some r)=0 := by
  have ne : p.symm r≠c := fun H => h (by rw [←H]; simp)
  apply Finset.prod_eq_zero (Finset.mem_univ (some (p.symm r)))
  simp [extend_some_used p r _ (p.apply_symm_apply r),divideEdge,ne]

private theorem some_term_used (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) (h : p c=r) :
    term A r c p (some r)=∏ i, A (p i) i := by
  unfold term
  rw [Fintype.prod_option]
  simp only [extend_none, divideEdge,ite_true,one_mul]
  apply Finset.prod_congr rfl
  intro i _
  by_cases e : i=c
  · subst i
    rw [extend_some_used _ _ _ h]
    simp [divideEdge,h]
  · have hn : p i≠r := fun E => e (p.injective (E.trans h.symm))
    rw [extend_some_free _ _ _ hn]
    simp [divideEdge,hn]

private theorem fiber_term (A : Matrix I I R) (r c : I) (p : Equiv.Perm I) :
    ∑ j, term A r c p j = ∏ i, A (p i) i := by
  rw [Fintype.sum_option]
  rw [Finset.sum_eq_single r (fun u _ hu => some_term_outside A r c p u hu) (by simp)]
  by_cases h : p c=r
  · simp [none_term_used A r c p h,some_term_used A r c p h]
  · simp [none_term_free A r c p h,some_term_free A r c p h]

/-- Odd subdivision of any one edge preserves the weighted perfect-matching
generating function over every commutative semiring. -/
theorem permanent_divideEdge (A : Matrix I I R) (r c : I) :
    (divideEdge A r c).permanent=A.permanent := by
  classical
  unfold Matrix.permanent
  calc
    _ = ∑ q : Option I × Equiv.Perm I, term A r c q.2 q.1 := by
      apply Fintype.sum_equiv Equiv.Perm.decomposeOption
      intro p
      change _=∏ x,divideEdge A r c (Equiv.Perm.decomposeOption.symm (Equiv.Perm.decomposeOption p) x) x
      rw [Equiv.symm_apply_apply]
    _ = ∑ j, ∑ p, term A r c p j := Fintype.sum_prod_type _
    _ = ∑ p, ∑ j, term A r c p j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun p _ => fiber_term A r c p)

end SparsePermanent

#print axioms SparsePermanent.permanent_divideEdge
