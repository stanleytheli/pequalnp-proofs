import ForestRouting
import ResourceBounds

namespace SparsePermanent.DirectedGrowth.Forest
open Finset BinaryWords
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : V→V→Prop} {m R l k : ℕ} (T : Forest (@oriented V E m) R)

private theorem protected_card (size : 2^l≤2*m) : (T.core (l+4*l)).card≤128*m^6 := by
  have ex : 2^(l+4*l+1)=(2^l)^5*2 := by rw [←pow_mul,←pow_succ];congr 1;omega
  have c:=T.core_card (l+4*l)
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,ex] at c
  calc
    _ ≤ (m*2)*((2^l)^5*2) := c
    _ ≤ (m*2)*((2*m)^5*2) := by gcongr
    _ = _ := by ring

/-- With a logarithmic port depth and a polynomially bounded inverse
expansion denominator and route length, m² routes fit in the stated volume. -/
theorem all_pairs (mature : 259≤m) (width : m≤2^l) (size : 2^l≤2*m)
    (lp : 0<l) (depth : l+2*(4*l)≤R) (hk : 0<k) (denom : k≤m)
    (fwd : Expands E k) (bwd : Expands (fun x y=>E y x) k)
    {M : ℕ} (time : M=4*(4*l)+4*k*(Nat.log 2 (Fintype.card V)+1)) (short : M+1≤m) :
    ∃U,Packed E (T.core (l+4*l)) (2^(4*l)) (2^(4*l)) (2*(4*l)) M
      (T.demands width (by omega) depth) U := by
  let B:=m^2*(M+1)
  have b : B≤m^3 := by
    calc
      _ ≤ m^2*m := Nat.mul_le_mul_left _ short
      _ = _ := by ring
  have avail : m^4≤2^(4*l) := by rw [Nat.mul_comm 4 l,pow_mul];gcongr
  obtain ⟨cap,pos⟩:=polynomial_capacity (c:=128) (by omega) denom (T.protected_card size) b avail avail
  exact T.pack_pairs width (by omega) depth lp hk fwd bwd time rfl cap pos

end SparsePermanent.DirectedGrowth.Forest
#print axioms SparsePermanent.DirectedGrowth.Forest.all_pairs
