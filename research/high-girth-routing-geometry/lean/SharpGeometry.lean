import GraphOrder
import GirthExact

namespace SparsePermanent

/-- Exact dimensional exponent, including constants: at height m^q the two
bipartition classes together have between 2m^(q+2) and 6m^(q+2) vertices. -/
theorem order_sharp (k q : ℕ) :
    2*(k+1)^(q+2)≤order k ((k+1)^q) ∧ order k ((k+1)^q)≤6*(k+1)^(q+2) := by
  let m:=k+1
  have pos:0<m:=by omega
  have one:1≤m^q:=Nat.one_le_pow _ _ pos
  have b:m^2≤m^q*m^2:=by simpa using Nat.mul_le_mul_right (m^2) one
  have a:m*k≤m^2:=by simpa [pow_two] using Nat.mul_le_mul_left m (Nat.le_succ k)
  rw [order,card_side,pow_add]
  change 2*(m^q*m^2)≤2*(m^2+m*k+m^q*m^2) ∧ 2*(m^2+m*k+m^q*m^2)≤6*(m^q*m^2)
  omega

/-- Removing the coefficient loss in the exponent gives N^q ≤ girth^(q+2).
For positive q the girth has order N^(q/(q+2)) on this family. -/
theorem order_girth_sharp (k q : ℕ) :
    (order k ((k+1)^q))^q ≤ (4*(2*(k+1)^q+3))^(q+2) := by
  let m:=k+1
  let h:=m^q
  have p : 0<h:=pow_pos (by omega) _
  have coeff : 6^q≤8^(q+2) :=
    (Nat.pow_le_pow_left (by decide : 6≤8) q).trans (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ (6*m^(q+2))^q := Nat.pow_le_pow_left (order_sharp k q).2 _
    _ = 6^q*h^(q+2) := by dsimp [h];rw [mul_pow,←pow_mul,←pow_mul];rw [Nat.mul_comm (q+2) q]
    _ ≤ 8^(q+2)*h^(q+2) := Nat.mul_le_mul_right _ coeff
    _ = (8*h)^(q+2) := (mul_pow ..).symm
    _ ≤ _ := Nat.pow_le_pow_left (by change 8*h≤4*(2*h+3);omega) _

end SparsePermanent
#print axioms SparsePermanent.order_girth_sharp
