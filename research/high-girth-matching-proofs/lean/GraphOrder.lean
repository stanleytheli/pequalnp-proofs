import Girth
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SparsePermanent

noncomputable def order (k h : ℕ) := 2 * Nat.card (Side k h)

theorem order_positive (k h : ℕ) : 0<order k h := by
  rw [order,card_side]
  positivity

/-- For arbitrary fixed q, the number of vertices at h=m^q is polynomial in m. -/
theorem order_poly (k q : ℕ) (hm : 2≤k+1) : order k ((k+1)^q) ≤ (k+1)^(q+5) := by
  let m := k+1
  have one : 1≤m^q := Nat.one_le_pow _ _ (by omega)
  have base : m^2≤m^q*m^2 := by simpa using Nat.mul_le_mul_right (m^2) one
  have arm : m*k≤m^2 := by simpa [pow_two] using Nat.mul_le_mul_left m (Nat.le_succ k)
  have six : 6≤m^3 := (show 6≤2^3 by decide).trans (Nat.pow_le_pow_left hm _)
  rw [order,card_side]
  change 2*(m^2+m*k+m^q*m^2)≤m^(q+5)
  calc
    _ ≤ 6*(m^q*m^2) := by omega
    _ ≤ m^3*(m^q*m^2) := Nat.mul_le_mul_right _ six
    _ = m^(q+5) := by rw [←pow_add,←pow_add]; congr 1; omega

/-- Integer-power version of the girth bound N^(q/(q+5)); no logarithmic
or real-power conventions are needed for this inequality. -/
theorem order_girth_power (k q : ℕ) (hm : 2≤k+1) :
    (order k ((k+1)^q))^q ≤ (4*(2*(k+1)^q+3))^(q+5) := by
  calc
    _ ≤ ((k+1)^(q+5))^q := Nat.pow_le_pow_left (order_poly k q hm) _
    _ = ((k+1)^q)^(q+5) := by rw [←pow_mul,←pow_mul,Nat.mul_comm (q+5) q]
    _ ≤ _ := Nat.pow_le_pow_left (by omega) _

/-- Polynomial changes of the size parameter preserve the 4/3 logarithmic
exponent. Dividing the leading constant by d² is sufficient. -/
theorem rate_rescale {c : ℝ} {n m d : ℕ} (hc : 0≤c) (hd : 1≤d)
    (hn : 1≤n) (hm : 1≤m) (size : n≤m^d) :
    (n:ℝ) ^ ((c / (d:ℝ)^2) * (Real.logb 2 n)^(1/3:ℝ)) ≤
      (m:ℝ) ^ (c*(Real.logb 2 m)^(1/3:ℝ)) := by
  have d1 : (1:ℝ)≤d := by exact_mod_cast hd
  have m1 : (1:ℝ)≤m := by exact_mod_cast hm
  have n1 : (1:ℝ)≤n := by exact_mod_cast hn
  have nd : (n:ℝ)≤(m:ℝ)^d := by exact_mod_cast size
  have hnlog := Real.logb_nonneg (b:=2) (by norm_num) n1
  have hmlog := Real.logb_nonneg (b:=2) (by norm_num) m1
  have log_bound := Real.logb_le_logb_of_le (b:=2) (by norm_num) (zero_lt_one.trans_le n1) nd
  rw [Real.logb_pow] at log_bound
  have lbound : (Real.logb 2 n)^(1/3:ℝ) ≤ (d:ℝ)*(Real.logb 2 m)^(1/3:ℝ) := calc
    _ ≤ ((d:ℝ)*Real.logb 2 m)^(1/3:ℝ) := Real.rpow_le_rpow hnlog log_bound (by norm_num)
    _ = (d:ℝ)^(1/3:ℝ)*(Real.logb 2 m)^(1/3:ℝ) := Real.mul_rpow (by positivity) hmlog
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le d1 (by norm_num)) (by positivity)
  let a := c/(d:ℝ)^2
  have ha : 0≤a := by dsimp [a]; positivity
  calc
    _ ≤ ((m:ℝ)^d) ^ (a*(Real.logb 2 n)^(1/3:ℝ)) := Real.rpow_le_rpow (by positivity) nd (by positivity)
    _ = (m:ℝ) ^ ((d:ℝ)*(a*(Real.logb 2 n)^(1/3:ℝ))) := (Real.rpow_natCast_mul (by positivity) _ _).symm
    _ ≤ (m:ℝ) ^ ((d:ℝ)*(a*((d:ℝ)*(Real.logb 2 m)^(1/3:ℝ)))) :=
      Real.rpow_le_rpow_of_exponent_le m1 (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left lbound ha) (by positivity))
    _ = _ := by
      congr 1
      dsimp [a]
      field_simp
      <;> ring

end SparsePermanent
#print axioms SparsePermanent.order_girth_power
#print axioms SparsePermanent.rate_rescale
