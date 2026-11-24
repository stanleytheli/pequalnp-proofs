import OracleFlow
import Mathlib.Data.Finset.Lattice.Fold

/-! Parse trees of an acyclic monotone circuit. A physical node has finitely
many alternatives; its chosen alternative invokes a finite list of child slots.
In a permanent these alternatives are allowed perfect matchings. -/
namespace PositivePermanent.Flow
open Finset
open scoped BigOperators
noncomputable section

structure Rules (n : ℕ) where
  lastAction : Fin n → ℕ
  slots : (v : Fin n) → Fin (lastAction v+1) → ℕ
  child : (v : Fin n) → (a : Fin (lastAction v+1)) → Fin (slots v a) → Fin n
  earlier : ∀ v a j,(child v a j).val<v.val

variable {n : ℕ}
abbrev Act (G : Rules n) (v : Fin n) := Fin (G.lastAction v+1)

inductive Parse (G : Rules n) : Fin n → Type where
  | node (v : Fin n) (a : Act G v) (parts : (j : Fin (G.slots v a)) → Parse G (G.child v a j)) : Parse G v

def Parse.score {G : Rules n} (b : Fin n→ℝ) {v : Fin n} (tree : Parse G v) : ℝ :=
  match tree with
  | .node v a parts => b v + ∑ j,(parts j).score b

def support (G : Rules n) (b : Fin n→ℝ) (v : Fin n) : ℝ :=
  b v + Finset.univ.sup' Finset.univ_nonempty (fun a : Act G v=>∑ j,support G b (G.child v a j))
termination_by v.val
decreasing_by exact G.earlier _ _ _

lemma branch_upper (G : Rules n) (b : Fin n→ℝ) (v : Fin n) (a : Act G v) :
    b v + ∑ j,support G b (G.child v a j) ≤ support G b v := by
  conv_rhs => rw [support]
  exact add_le_add_right (Finset.le_sup' (fun a : Act G v=>∑ j,support G b (G.child v a j)) (Finset.mem_univ a)) _

lemma best_branch (G : Rules n) (b : Fin n→ℝ) (v : Fin n) :
    ∃ a : Act G v,support G b v=b v+∑ j,support G b (G.child v a j) := by
  obtain ⟨a,_,eq⟩ := Finset.exists_mem_eq_sup' (s:=Finset.univ) Finset.univ_nonempty
    (fun a : Act G v=>∑ j,support G b (G.child v a j))
  exact ⟨a,by conv_lhs => rw [support]; rw [eq]⟩

theorem parse_upper {G : Rules n} (b : Fin n→ℝ) {v} (tree : Parse G v) :
    tree.score b≤support G b v := by
  induction tree with
  | node v a parts ih =>
    exact (add_le_add_right (Finset.sum_le_sum (fun j _=>ih j)) _).trans (branch_upper G b v a)

theorem parse_attains (G : Rules n) (b : Fin n→ℝ) (v : Fin n) :
    ∃ t : Parse G v,t.score b=support G b v := by
  obtain ⟨a,eq⟩ := best_branch G b v
  have child (j : Fin (G.slots v a)) := parse_attains G b (G.child v a j)
  choose parts ih using child
  exact ⟨.node v a parts,by simp only [Parse.score,ih,eq]⟩
termination_by v.val
decreasing_by exact G.earlier _ _ _

/-- Multiplicity counts slots, so the same child can receive several demands. -/
def copies (G : Rules n) (v : Fin n) (a : Act G v) (u : Fin n) : ℝ :=
  ∑ j : Fin (G.slots v a), if G.child v a j=u then 1 else 0

lemma copies_nonneg (G : Rules n) (v : Fin n) (a : Act G v) (u : Fin n) : 0≤copies G v a u :=
  Finset.sum_nonneg (fun j _=>by split <;> norm_num)

lemma copies_sum (G : Rules n) (v : Fin n) (a : Act G v) (h : Fin n→ℝ) :
    (∑ u,copies G v a u*h u) = ∑ j,h (G.child v a j) := by
  simp only [copies,Finset.sum_mul,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

lemma copies_early (G : Rules n) (v : Fin n) (a : Act G v) (u : Fin n)
    (h : copies G v a u≠0) : u<v := by
  by_contra late
  apply h
  apply Finset.sum_eq_zero
  intro j _
  have ne : G.child v a j ≠ u := fun eq=>late (eq ▸ G.earlier v a j)
  simp [ne]

def push (G : Rules n) (x : (v : Fin n)→Act G v→ℝ) (v u : Fin n) :=
  ∑ a,x v a*copies G v a u

def feasible (G : Rules n) (root : Fin n) (m : Fin n→ℝ) (x : (v : Fin n)→Act G v→ℝ) : Prop :=
  (∀ v a,0≤x v a) ∧ (∀ v,(∑ a,x v a)=m v) ∧ balance root m (push G x)

lemma push_score (G : Rules n) (x : (v : Fin n)→Act G v→ℝ) (v : Fin n) (h : Fin n→ℝ) :
    (∑ u,push G x v u*h u)=∑ a,x v a*∑ j,h (G.child v a j) := by
  simp only [push,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_assoc,←Finset.mul_sum,copies_sum]

theorem formulation_upper (G : Rules n) (root : Fin n) (b : Fin n→ℝ)
    (m : Fin n→ℝ) (x : (v : Fin n)→Act G v→ℝ) (ok : feasible G root m x) :
    (∑ v,m v*b v)≤support G b root := by
  obtain ⟨nn,masssum,balanced⟩ := ok
  apply envelope root m _ balanced (support G b) b
  intro v
  rw [push_score,←masssum v,Finset.sum_mul,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [←mul_add]
  exact mul_le_mul_of_nonneg_left (branch_upper G b v a) (nn v a)

theorem formulation_attains (G : Rules n) (root : Fin n) (b : Fin n→ℝ) :
    ∃ m x, feasible G root m x ∧ (∑ v,m v*b v)=support G b root := by
  classical
  choose act best using best_branch G b
  let k := fun v u=>copies G v (act v) u
  obtain ⟨m,nn,bal,tight⟩ := policy_exact root k
    (fun v u=>copies_early G v (act v) u) (fun v u=>copies_nonneg G v (act v) u)
    (support G b) b (fun v=>by simpa [k,copies_sum] using best v)
  let x := fun v (a : Act G v)=>if a=act v then m v else 0
  refine ⟨m,x,⟨?_,?_,?_⟩,tight⟩
  · intro v a; dsimp only [x]; split <;> simp [nn]
  · intro v; simp [x]
  · have eq : push G x = fun v u=>m v*k v u := by
      funext v u
      simp [push,x,k,ite_mul]
    rwa [eq]

/-- The explicit physical-node flow program and the actual parse-tree scores
have exactly the same attained optimum in every real direction. -/
theorem parse_flow_maximum (G : Rules n) (root : Fin n) (b : Fin n→ℝ) :
    IsGreatest {z : ℝ | ∃ t : Parse G root,t.score b=z} (support G b root) ∧
    IsGreatest {z : ℝ | ∃ m x,feasible G root m x ∧ (∑ v,m v*b v)=z} (support G b root) := by
  refine ⟨⟨parse_attains G b root,?_⟩,⟨formulation_attains G root b,?_⟩⟩
  · rintro z ⟨t,rfl⟩; exact parse_upper b t
  · rintro z ⟨m,x,ok,rfl⟩; exact formulation_upper G root b m x ok


end
end PositivePermanent.Flow
#print axioms PositivePermanent.Flow.parse_attains
#print axioms PositivePermanent.Flow.parse_upper
#print axioms PositivePermanent.Flow.parse_flow_maximum
