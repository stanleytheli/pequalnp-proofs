import Mathlib
namespace Subdivision

/-- Polynomially long private paths allow the shortest-cycle bound to grow
as a power of the total input count. The two inequalities avoid real exponents. -/
theorem growing_girth_sizes (M v q : ℕ) (noIsolates : v ≤ 2*M) :
    let L := (2*M)^q+7
    let N := v+(L-1)*M
    N^q ≤ L^(q+1) ∧ 2^q*M^(q+1) ≤ N := by
  intro L N
  have big : (2*M)^q ≤ L := by dsimp [L]; omega
  have previous : (2*M)^q ≤ L-1 := by dsimp [L]; omega
  have len : 2 ≤ L := by dsimp [L]; omega
  have smaller : (L-1)*M ≤ L*M := Nat.mul_le_mul_right M (Nat.sub_le _ _)
  have vertices : v ≤ L*M := noIsolates.trans (Nat.mul_le_mul_right M len)
  have total : N ≤ L*(2*M) := by dsimp [N]; nlinarith
  constructor
  · calc
      N^q ≤ (L*(2*M))^q := Nat.pow_le_pow_left total q
      _ = L^q*(2*M)^q := mul_pow _ _ _
      _ ≤ L^q*L := Nat.mul_le_mul_left _ big
      _ = L^(q+1) := (pow_succ _ _).symm
  · calc
      2^q*M^(q+1) = (2*M)^q*M := by rw [mul_pow,pow_succ]; ring
      _ ≤ (L-1)*M := Nat.mul_le_mul_right _ previous
      _ ≤ N := by dsimp [N]; omega

end Subdivision
#print axioms Subdivision.growing_girth_sizes
