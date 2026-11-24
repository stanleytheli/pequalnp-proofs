import Mathlib.Tactic

namespace SparsePermanent.DirectedGrowth

/-- With m² demands, maximum route size m, c·m⁶ protected vertices and m⁴
groups of m⁴ leaves per port, all stages of the greedy routing fit. -/
theorem polynomial_capacity {m c k p B L W : ℕ}
    (large : 2*c+3≤m) (expand : k≤m) (core : p≤c*m^6) (used : B≤m^3)
    (groups : m^4≤L) (leaves : m^4≤W) : 2*k*(p+B)≤(L-B)*W ∧ 0<(L-B)*W := by
  have positive : 0<m := by omega
  have p3 : 0<m^3 := pow_pos positive _
  have p4 : 0<m^4 := pow_pos positive _
  have m36 : m^3≤m^6 := Nat.pow_le_pow_right positive (by decide)
  have upper : 2*k*(p+B)≤2*(c+1)*m^7 := by
    calc
      _ ≤ (2*m)*(c*m^6+m^6) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ expand) (Nat.add_le_add core (used.trans m36))
      _ = _ := by ring
  have split : m^4=(m-1)*m^3+m^3 := by
    have h : m-1+1=m:=by omega
    calc
      _ = m*m^3 := by ring
      _ = (m-1+1)*m^3 := by rw [h]
      _ = _ := by ring
  have budget : (m-1)*m^3≤L-B := by omega
  have lower : (m-1)*m^7≤(L-B)*W := by
    calc
      _ = ((m-1)*m^3)*m^4 := by ring
      _ ≤ _ := Nat.mul_le_mul budget leaves
  have coef : 2*(c+1)≤m-1 := by omega
  have pos : 0<(m-1)*m^7 := Nat.mul_pos (by omega) (pow_pos positive _)
  exact ⟨(upper.trans (Nat.mul_le_mul_right _ coef)).trans lower,pos.trans_le lower⟩

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.polynomial_capacity
