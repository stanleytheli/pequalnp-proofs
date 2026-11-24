import TightForest
import BinaryContraction

namespace SparsePermanent.Contract
open Finset DirectedGrowth SimpleGraph
variable {I : Type} [Fintype I] [DecidableEq I]

open Classical in
private theorem card_out (E : I→I→Prop) (matching : ∀x,E x x) (degree : ∀x,(∑y,DirectedGrowth.weight E x y)=3)
    (x:I) : (univ.filter (arc E x)).card≤2 := by
  classical
  rw [card_filter,←outgoing E matching degree x]
  apply le_of_eq
  apply sum_congr rfl
  intro y _
  by_cases h:arc E x y <;> simp [DirectedGrowth.weight,h]

open Classical in
private theorem card_in (E : I→I→Prop) (matching : ∀x,E x x) (degree : ∀y,(∑x,DirectedGrowth.weight E x y)=3)
    (x:I) : (univ.filter (fun y=>arc E y x)).card≤2 := by
  classical
  rw [card_filter,←incoming E matching degree x]
  apply le_of_eq
  apply sum_congr rfl
  intro y _
  by_cases h:arc E y x <;> simp [DirectedGrowth.weight,h]

/-- The finite form of the polynomial-dimension refinement for sextets:
center packing costs m·2^(2R+4), while the number of private terminal
groups required is only m²(M+1+18k), with k twice the edge-expansion inverse. -/
theorem tight_routes (E : I→I→Prop) (matching : ∀x,E x x)
    (left : ∀x,(∑y,DirectedGrowth.weight E x y)=3) (right : ∀y,(∑x,DirectedGrowth.weight E x y)=3)
    (m l s K M : ℕ) (hk:0<K) (w:m≤2^l) (close:2^l≤2*m) (lp:0<l) (sp:0<s)
    (expand : ∀S : Finset (I⊕I),2*S.card≤Fintype.card (I⊕I)→S.card≤K*cross (bipGraph E).Adj S Sᶜ)
    (long : ((2*(2*(l+2*s)+1) : ℕ) : ℕ∞)<(bipGraph E).egirth)
    (space : m*2^(2*(l+2*s)+4)<Fintype.card I)
    (time : M=4*s+4*(K*2)*(Nat.log 2 (Fintype.card I)+1))
    (room : m^2*(M+1+18*(K*2))≤2^s) :
    ∃ center : Fin m→I,∃T : Forest (@oriented I (arc E) m) (l+2*s),
      (∀i b,T.node (i,b) []=center i) ∧
      (∀i j,i≠j→Disjoint (twoWays (arc E) (l+2*s) (center i)) (twoWays (arc E) (l+2*s) (center j))) ∧
      ∃U,Packed (arc E) (T.core (l+s)) (2^s) (2^s) (2*s) M (T.demands w sp le_rfl) U := by
  classical
  obtain ⟨fwd,bwd⟩:=directed_expansion E matching left right K expand
  obtain ⟨center,apart⟩:=pack_twoWays (arc E) (card_out E matching left) (card_in E matching right) m (l+2*s) space
  have high : (4:ℕ∞)<(bipGraph E).egirth:=lt_of_le_of_lt (by exact_mod_cast (by omega : 4≤2*(2*(l+2*s)+1))) long
  let T:=Forest.from_boxes center (outgoing_tree E matching left) (incoming_tree E matching right)
    (antireciprocal E matching high) (girth E matching _ long) apart
  refine ⟨center,T,?_,apart,T.tight_pairs w close lp sp le_rfl (by omega) fwd bwd time room⟩
  rintro i (_|_) <;> rfl

end SparsePermanent.Contract
#print axioms SparsePermanent.Contract.tight_routes
