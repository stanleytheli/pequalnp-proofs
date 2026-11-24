import Mathlib
namespace PositiveCornerClosure

/-- Minimum cost and number of optimizers of a nonempty finite collection. -/
def choose (a b : ℕ × ℕ) : ℕ × ℕ :=
  if a.1 < b.1 then a else if b.1 < a.1 then b else (a.1,a.2+b.2)

def pay (k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ := (s.1+k,s.2)

/-- Extend a path by two private positions, costing C and C+1 respectively.
If the first is omitted the left endpoint and second private vertex must be
covered. If both are covered, that case is dominated when the left endpoint
was already covered (the cheaper option is to omit the first private vertex). -/
def extend (C : ℕ) (prev : Bool → Bool → ℕ × ℕ) (x y : Bool) : ℕ × ℕ :=
  choose (pay C (prev false y)) (pay (if x then C+1 else 2*C+1) (prev true y))

/-- n=0 describes a two-edge path (even) or a three-edge path (odd). -/
def path (odd : Bool) (C : ℕ) : ℕ → Bool → Bool → ℕ × ℕ
  | 0,x,y => if odd then
      ((if x then (if y then C else C+1) else (if y then C else 2*C+1)),1)
    else ((if x && y then 0 else C),1)
  | n+1,x,y => extend C (path odd C n) x y

theorem even_profile (n C : ℕ) (large : n+1<C) (x y : Bool) :
    path false C n x y = ((if x && y then n*(C+1) else (n+1)*C),1) := by
  induction n generalizing x y with
  | zero => cases x <;> cases y <;> simp [path]
  | succ n ih =>
    have h : n+1<C := by omega
    cases x <;> cases y <;> simp only [path,extend,ih h,pay,choose,Bool.false_eq_true,ite_false,ite_true,
      Bool.false_and,Bool.true_and,Bool.and_false,Bool.and_true]
    all_goals simp only [Nat.succ_mul,Nat.mul_add,Nat.mul_one] at *
    all_goals split <;> simp_all <;> try omega
    all_goals split <;> simp_all <;> omega

theorem odd_profile (n C : ℕ) (large : n+1<C) (x y : Bool) :
    path true C n x y =
      ((if x then (if y then (n+1)*C else (n+1)*(C+1)) else
        (if y then (n+1)*C else (n+2)*C+1)),1) := by
  induction n generalizing x y with
  | zero => cases x <;> cases y <;> simp [path]
  | succ n ih =>
    have h : n+1<C := by omega
    cases x <;> cases y <;> simp only [path,extend,ih h,pay,choose,Bool.false_eq_true,ite_false,ite_true]
    all_goals simp only [Nat.succ_mul,Nat.mul_add,Nat.mul_one] at *
    all_goals split <;> simp_all <;> try omega
    all_goals split <;> simp_all <;> omega

/-- At most one truth-table row may fire. If it fires its output rail must
also fire. The fixed optimum is independent of the gate truth table. -/
theorem row_minimum (rows rails : ℕ) (hr : rows≤1) (hg : rails≤2)
    (required : rows≤rails) :
    7≤2*(4-rows)+rails ∧
    (2*(4-rows)+rails=7 ↔ rows=1 ∧ rails=1) := by omega

end PositiveCornerClosure
#print axioms PositiveCornerClosure.even_profile
#print axioms PositiveCornerClosure.odd_profile
#print axioms PositiveCornerClosure.row_minimum
