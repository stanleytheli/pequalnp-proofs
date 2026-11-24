import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite acyclic occurrence flows. Local support inequalities telescope even
with shared gates. A deterministic maximizing policy always realizes equality.
At an assignment oracle, a scaled doubly stochastic matrix provides the local
inequality from the perfect-matching bound. -/
namespace PositivePermanent.Flow
open Finset Matrix
open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def balance (root : V) (m : V→ℝ) (f : V→V→ℝ) : Prop :=
  ∀ v, m v=(if v=root then 1 else 0)+∑ u,f u v

lemma account (root : V) (m : V→ℝ) (f : V→V→ℝ) (ok : balance root m f) (h : V→ℝ) :
    ∑ v,m v*h v = h root+∑ v,∑ u,f v u*h u := by
  calc
    _ = ∑ v, ((if v=root then h v else 0) + (∑ u,f u v*h v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [ok v,add_mul,Finset.sum_mul]
      by_cases e : v=root <;> simp [e]
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_comm (f:=fun v u=>f u v*h v)]; simp

theorem envelope (root : V) (m : V→ℝ) (f : V→V→ℝ) (ok : balance root m f) (h b : V→ℝ)
    (loc : ∀ v,m v*b v+∑ u,f v u*h u ≤ m v*h v) : ∑ v,m v*b v ≤ h root := by
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>loc i)
  rw [Finset.sum_add_distrib,account root m f ok h] at sum
  linarith

theorem tight (root : V) (m : V→ℝ) (f : V→V→ℝ) (ok : balance root m f) (h b : V→ℝ)
    (loc : ∀ v,m v*b v+∑ u,f v u*h u = m v*h v) : ∑ v,m v*b v = h root := by
  have sum := Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _=>loc i)
  rw [Finset.sum_add_distrib,account root m f ok h] at sum
  linarith

variable {n : ℕ}
def mass (root : Fin n) (k : Fin n→Fin n→ℝ) : ℕ→Fin n→ℝ
  | 0,v=>if v=root then 1 else 0
  | d+1,v=>∑ p,mass root k d p*k p v

lemma mass_nonneg (root : Fin n) (k : Fin n→Fin n→ℝ) (nn : ∀ p v,0≤k p v) (d : ℕ) (v : Fin n) :
    0≤mass root k d v := by
  induction d generalizing v with
  | zero => simp only [mass]; split <;> norm_num
  | succ d ih => exact Finset.sum_nonneg (fun p _=>mul_nonneg (ih _) (nn _ _))

lemma level_zero (root : Fin n) (k : Fin n→Fin n→ℝ) (earlier : ∀ p v,k p v≠0 → v<p)
    (d : ℕ) (v : Fin n) (too_deep : n≤d+v.val) : mass root k d v=0 := by
  induction d generalizing v with
  | zero => have := v.isLt; omega
  | succ d ih =>
    apply Finset.sum_eq_zero
    intro p _
    by_cases z : k p v=0
    · rw [z,mul_zero]
    · have h : v.val<p.val := earlier p v z
      rw [ih p (by omega),zero_mul]

def visits (root : Fin n) (k : Fin n→Fin n→ℝ) (v : Fin n) := ∑ d∈Finset.range n,mass root k d v

theorem policy_balance (root : Fin n) (k : Fin n→Fin n→ℝ) (earlier : ∀ p v,k p v≠0 → v<p) :
    balance root (visits root k) (fun p v=>visits root k p*k p v) := by
  intro v
  have pushed : (∑ p,visits root k p*k p v) = ∑ d∈Finset.range n,mass root k (d+1) v := by
    simp only [visits,Finset.sum_mul,mass]
    rw [Finset.sum_comm]
  have last := level_zero root k earlier n v (by omega)
  have eq := Finset.sum_range_succ' (f:=fun d=>mass root k d v) n
  rw [Finset.sum_range_succ,last,add_zero] at eq
  rw [pushed]
  simpa [visits,mass,add_comm] using eq

/-- A local choice reaching its support value at every gate reaches the output
value on an explicit feasible occurrence flow. -/
theorem policy_exact (root : Fin n) (k : Fin n→Fin n→ℝ) (earlier : ∀ p v,k p v≠0 → v<p)
    (nn : ∀ p v,0≤k p v) (h b : Fin n→ℝ) (policy : ∀ v,h v=b v+∑ u,k v u*h u) :
    ∃ m : Fin n→ℝ, (∀ v,0≤m v) ∧ balance root m (fun p v=>m p*k p v) ∧
      (∑ v,m v*b v)=h root := by
  let m := visits root k
  have ok := policy_balance root k earlier
  refine ⟨m,fun v=>Finset.sum_nonneg (fun d _=>mass_nonneg root k nn d v),ok,?_⟩
  apply tight root m _ ok h b
  intro v
  conv_rhs => rw [policy v,mul_add,Finset.mul_sum]
  simp [m,mul_assoc]

variable {I : Type*} [Fintype I] [DecidableEq I]

def score (lift : Matrix I I ℝ) (a : I→I→ℝ) := ∑ i,∑ j,lift i j*a i j

lemma score_perm (p : Equiv.Perm I) (a : I→I→ℝ) :
    score (p.permMatrix ℝ) a=∑ i,a i (p i) := by
  unfold score
  apply Finset.sum_congr rfl
  intro i _
  simp [Equiv.toPEquiv_apply,PEquiv.toMatrix_apply,Option.mem_def,ite_mul,Finset.sum_ite_eq]

lemma assignment_upper (P : Matrix I I ℝ) (hP : P∈doublyStochastic ℝ I)
    (a : I→I→ℝ) (H : ℝ) (bound : ∀ p : Equiv.Perm I,(∑ i,a i (p i))≤H) : score P a≤H := by
  obtain ⟨w,nn,one,rep⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  have combine : score P a = ∑ p,w p*score (p.permMatrix ℝ) a := by
    rw [←rep]
    have lin (S : Finset (Equiv.Perm I)) :
        score (∑ p ∈ S,w p • p.permMatrix ℝ) a = ∑ p ∈ S,w p*score (p.permMatrix ℝ) a := by
      induction S using Finset.induction_on with
      | empty => simp [score]
      | @insert p S hp ih =>
        rw [Finset.sum_insert hp,Finset.sum_insert hp]
        have add (A B : Matrix I I ℝ) : score (A+B) a=score A a+score B a := by
          simp [score,Matrix.add_apply,add_mul,Finset.sum_add_distrib]
        have smul (A : Matrix I I ℝ) (r : ℝ) : score (r • A) a=r*score A a := by
          simp [score,Matrix.smul_apply,Finset.mul_sum,mul_assoc]
        rw [add,smul,ih]
    exact lin Finset.univ
  rw [combine]
  calc
    _ ≤ ∑ p,w p*H := Finset.sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (by rw [score_perm]; exact bound p) (nn _))
    _ = H := by rw [←Finset.sum_mul,one,one_mul]

end
end PositivePermanent.Flow
#print axioms PositivePermanent.Flow.envelope
#print axioms PositivePermanent.Flow.policy_exact
#print axioms PositivePermanent.Flow.assignment_upper
