import Mathlib
namespace GraphProbability.PositiveOdd
/-- Score and count of configurations attaining that score. The input always
describes a nonempty conditional family. -/
def best (a b : ℕ×ℕ) := if a.1<b.1 then b else if b.1<a.1 then a else (a.1,a.2+b.2)
def give (k : ℕ) (a : ℕ×ℕ) := (a.1+k,a.2)
/-- First-pair recurrence. One pair at the beginning is 00, 10 or 01.
The 00 option is strictly dominated by 10 when the left root is absent. -/
def path (B : ℕ) : ℕ→Bool→Bool→ℕ×ℕ
  | 0,false,_ => (B+1,1)
  | 0,true,false => (B,1)
  | 0,true,true => (0,1)
  | h+1,x,y =>
      let tail0 := path B h false y
      let tail1 := path B h true y
      best (if x then tail0 else give (B+1) tail0) (give B tail1)

/-- At h+1 private pairs the conditional maximum is unique in all four endpoint
states. One reward unit resolves the ties of the unweighted path. -/
theorem profile (h B : ℕ) (large : h+1<B) (x y : Bool) :
    path B h x y =
      (if x then (if y then h*(B+1) else (h+1)*B) else (h+1)*(B+1),1) := by
  induction h generalizing x y with
  | zero => cases x <;> cases y <;> simp [path]
  | succ h ih =>
    have prev : h+1<B := by omega
    cases x <;> cases y <;> simp only [path,ih prev,Bool.false_eq_true,ite_false,ite_true,give,best]
    all_goals simp only [Nat.succ_mul,Nat.mul_add,Nat.mul_one] at *
    all_goals split <;> simp_all <;> omega

/-- The weighted optimum and the total reward give the claimed absence
exponent when each edge has h pairs of private vertices. -/
theorem exponent (h D r k M : ℕ) (hk : k≤r) :
    (4*D+r+h*M+h*(2*(h+4)+1)*M) -
        (2*D+k+h*(h+5)*M) = 2*D+r-k+h*(h+5)*M := by
  have eq : 4*D+r+h*M+h*(2*(h+4)+1)*M =
      (2*D+k+h*(h+5)*M)+(2*D+r-k+h*(h+5)*M) := by
    zify [show k≤2*D+r by omega]
    ring
  rw [eq]
  omega
end GraphProbability.PositiveOdd
#print axioms GraphProbability.PositiveOdd.profile
#print axioms GraphProbability.PositiveOdd.exponent
