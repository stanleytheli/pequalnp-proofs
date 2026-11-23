import Mathlib

/-! Fibonacci endpoint kernels and their common-modulus contraction. -/
namespace SparseHamiltonian.FibonacciTransfer

open Matrix Finset

def edge (R : Type*) [CommSemiring R] : Matrix (Fin 2) (Fin 2) R := !![1,1;1,0]

/-- The power has summed all spins internal to a path. -/
theorem path_kernel {R : Type*} [CommSemiring R] (d : ℕ) :
    (edge R)^(d+1) = (Nat.fib (d+1) : R) • edge R + (Nat.fib d : R) • 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [edge, Nat.fib_add_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem stretched {R : Type*} [CommSemiring R] (d k : ℕ)
    (h : (Nat.fib (d+1) : R) = 0) :
    (edge R)^((d+1)*k+1) = (Nat.fib d : R)^k • edge R := by
  rw [pow_succ, pow_mul, path_kernel, h, zero_smul, zero_add]
  simp [smul_pow, Matrix.smul_mul]

/-- A two-spin partition sum with one unary factor per marked site and one
binary factor per edge. Repeated endpoints and isolated vertices are allowed. -/
noncomputable def partition {R V M E : Type*} [CommSemiring R]
    [Fintype V] [Fintype M] [Fintype E]
    (marked : M → V) (left right : E → V) (unary : Fin 2 → R)
    (binary : Matrix (Fin 2) (Fin 2) R) : R := by
  classical
  exact ∑ x : V → Fin 2, (∏ m, unary (x (marked m))) *
    ∏ e, binary (x (left e)) (x (right e))

theorem scale_partition {R V M E : Type*} [CommSemiring R]
    [Fintype V] [Fintype M] [Fintype E]
    (marked : M → V) (left right : E → V) (w : Fin 2 → R)
    (b : Matrix (Fin 2) (Fin 2) R) (a c : R) :
    partition marked left right (fun t => a*w t) (c • b) =
      (a^Fintype.card M * c^Fintype.card E) * partition marked left right w b := by
  classical
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  ring

/-- Attaching a t-vertex unweighted tail at every marked site and then stretching
each edge to (t+3)*k+1 edges recovers signed activity minus one when F_(t+3)=0. -/
theorem common_modulus {R V M E : Type*} [CommRing R]
    [Fintype V] [Fintype M] [Fintype E]
    (marked : M → V) (left right : E → V) (t k : ℕ)
    (h : (Nat.fib (t+3) : R) = 0) :
    partition marked left right
      (fun x => if x = 0 then (Nat.fib (t+2) : R) else (Nat.fib (t+1) : R))
      ((edge R)^((t+3)*k+1)) =
      (Nat.fib (t+2) : R)^(Fintype.card M + k*Fintype.card E) *
        partition marked left right (fun x => if x = 0 then 1 else -1) (edge R) := by
  have neg : (Nat.fib (t+1) : R) = -(Nat.fib (t+2) : R) := by
    rw [eq_neg_iff_add_eq_zero]
    simpa [Nat.fib_add_two, add_assoc, add_comm, add_left_comm] using h
  have hw (x : Fin 2) :
      (if x=0 then (Nat.fib (t+2) : R) else (Nat.fib (t+1) : R)) =
      (Nat.fib (t+2) : R) * (if x=0 then 1 else -1) := by
    split_ifs <;> simp [neg]
  rw [funext hw, stretched (t+2) k h, scale_partition, pow_add, pow_mul]
end SparseHamiltonian.FibonacciTransfer

#print axioms SparseHamiltonian.FibonacciTransfer.common_modulus
