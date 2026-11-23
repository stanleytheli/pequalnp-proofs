import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace TraceBudget

/-- Grouping n into r blocks proves exponential absorption with an explicit constant. -/
theorem polynomial (n r : Nat) : (n+1)^r ≤ max 1 (r^r) * 2^n := by
  cases r with
  | zero => simpa using (Nat.one_le_two_pow (n := n))
  | succ r =>
    let d := r+1
    have hd : 0 < d := Nat.zero_lt_succ _
    have hm := Nat.mod_lt n hd
    have hs := Nat.div_add_mod n d
    have hlinear : n+1 ≤ d*(n/d+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    have hpow : n/d+1 ≤ 2^(n/d) := Nat.lt_two_pow_self
    have hdn : (n/d)*d ≤ n := Nat.div_mul_le_self _ _
    change (n+1)^d ≤ max 1 (d^d) * 2^n
    calc
      (n+1)^d ≤ (d*(n/d+1))^d := Nat.pow_le_pow_left hlinear _
      _ = d^d*(n/d+1)^d := Nat.mul_pow ..
      _ ≤ d^d*(2^(n/d))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _)
      _ = d^d*2^((n/d)*d) := by rw [Nat.pow_mul]
      _ ≤ _ := Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by decide) hdn)

/-- The input-length and address overhead in an indexed trace fit within one exponential gap.
Here 1/(a+1) is the hypothetical circuit exponent saving, q = 5a+5 and p = 5a+4. -/
theorem index_bound (a n c m : Nat) (hm : m ≤ (5*a+7)*n+c) :
    a*m/(a+1) ≤ (5*a+3)*n+c := by
  have hcoef : a*(5*a+7) ≤ (a+1)*(5*a+3) := by nlinarith
  apply Nat.div_le_of_le_mul
  calc
    a*m ≤ a*((5*a+7)*n+c) := Nat.mul_le_mul_left _ hm
    _ = (a*(5*a+7))*n+a*c := by ring
    _ ≤ ((a+1)*(5*a+3))*n+(a+1)*c := Nat.add_le_add
      (Nat.mul_le_mul_right _ hcoef) (Nat.mul_le_mul_right _ (Nat.le_succ _))
    _ = _ := by ring

theorem padded_size (a n c r H m : Nat) (hm : m ≤ (5*a+7)*n+c) :
    H*(n+1)^r*2^(a*m/(a+1)) ≤ (H*max 1 (r^r)*2^c)*2^((5*a+4)*n) := by
  have he := index_bound a n c m hm
  calc
    H*(n+1)^r*2^(a*m/(a+1)) ≤ H*(max 1 (r^r)*2^n)*2^((5*a+3)*n+c) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (polynomial n r)) (Nat.pow_le_pow_right (by decide) he)
    _ = (H*max 1 (r^r)*2^c)*(2^n*2^((5*a+3)*n)) := by rw [Nat.pow_add]; ring
    _ = _ := by rw [←Nat.pow_add]; congr 2; ring

end TraceBudget

#print axioms TraceBudget.padded_size
