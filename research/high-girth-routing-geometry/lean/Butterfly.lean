import DirectedSplit

namespace SparsePermanent.Butterfly
open Finset
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

/-- Remove a unit-loop vertex with just one possible nonloop predecessor v.
Its two-step transition is added to each old transition at v; labels may
coincide and may be arbitrary semiring elements. -/
def compress (B : Matrix (Option I) (Option I) R) (v : I) : Matrix I I R :=
  fun y x=>if x=v then B (some y) (some x)+B (some y) none*B none (some x) else B (some y) (some x)

private def lift (j : Option I) (p : Equiv.Perm I) := Equiv.Perm.decomposeOption.symm (j,p)

private theorem used {p : Equiv.Perm I} {i j : I} (e : p i=j) :
    lift (some j) p (some i)=none := by simp [lift,e]

private theorem free {p : Equiv.Perm I} {i j : I} (e : p i≠j) :
    lift (some j) p (some i)=some (p i) := by simp [lift,Equiv.swap_apply_of_ne_of_ne,e]

private def term (B : Matrix (Option I) (Option I) R) (p : Equiv.Perm I) (j : Option I) :=
  ∏ i,B (lift j p i) i

theorem permanent (B : Matrix (Option I) (Option I) R) (v : I) (unit : B none none=1)
    (single : ∀i,i≠v→B none (some i)=0) :
    B.permanent=(compress B v).permanent := by
  classical
  have plain (p : Equiv.Perm I) : term B p none=∏i,B (some (p i)) (some i) := by
    simp [term,Fintype.prod_option,lift,unit]
  have wrong (p : Equiv.Perm I) (j : I) (h:j≠p v) : term B p (some j)=0 := by
    apply prod_eq_zero (mem_univ (some (p.symm j)))
    rw [used (p.apply_symm_apply j)]
    exact single _ (fun e=>h (by rw [←e];simp))
  have taken (p : Equiv.Perm I) : term B p (some (p v))=
      (B (some (p v)) none*B none (some v))*(∏i∈univ.erase v,B (some (p i)) (some i)) := by
    rw [term,Fintype.prod_option,←mul_prod_erase univ _ (mem_univ v),used rfl]
    rw [show lift (some (p v)) p none=some (p v) by simp [lift]]
    rw [mul_assoc];congr 1;congr 1
    apply prod_congr rfl
    intro i hi
    rw [show lift (some (p v)) p (some i)=some (p i) from
      free (fun e=>(mem_erase.mp hi).1 (p.injective e))]
  unfold Matrix.permanent
  calc
    _ = ∑ q : Option I×Equiv.Perm I,term B q.2 q.1 := by
      apply Fintype.sum_equiv Equiv.Perm.decomposeOption
      intro p
      change _=∏ i,B (Equiv.Perm.decomposeOption.symm (Equiv.Perm.decomposeOption p) i) i
      rw [Equiv.symm_apply_apply]
    _ = ∑ j,∑ p,term B p j := Fintype.sum_prod_type _
    _ = ∑ p,∑ j,term B p j := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p _
      rw [Fintype.sum_option,sum_eq_single (p v) (fun j _ hj=>wrong p j hj) (by simp),taken,plain]
      rw [←mul_prod_erase univ (fun i=>B (some (p i)) (some i)) (mem_univ v),
        ←mul_prod_erase univ (fun i=>compress B v (p i) i) (mem_univ v),←add_mul]
      simp only [compress,ite_true]
      congr 1
      apply prod_congr rfl
      intro i hi
      simp [(mem_erase.mp hi).1]

theorem permanent_transpose (B : Matrix (Option I) (Option I) R) (v : I) (unit:B none none=1)
    (single : ∀i,i≠v→B (some i) none=0) :
    B.permanent=(compress B.transpose v).transpose.permanent := by
  rw [Matrix.permanent_transpose,←permanent B.transpose v unit single,Matrix.permanent_transpose]

end SparsePermanent.Butterfly
#print axioms SparsePermanent.Butterfly.permanent
