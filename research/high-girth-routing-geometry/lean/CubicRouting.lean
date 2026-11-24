import BinaryContraction
import SeparatedCenters
import ForestScaling

namespace SparsePermanent.Contract
open Finset DirectedGrowth SimpleGraph
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

private theorem route_reachable {E : I→I→Prop} {G : SimpleGraph I} (adj : ∀ ⦃x y⦄,E x y→G.Adj x y)
    {A : Finset I} {x y : I} {t : ℕ} (walk : Route E A x y t) : G.Reachable x y := by
  induction walk with
  | nil=>exact .refl _
  | snoc _ step _ ih=>exact ih.trans (adj step).reachable

private theorem connected {E : I→I→Prop} {k : ℕ} (hk:0<k) (fwd : Expands (arc E) k)
    (bwd : Expands (fun x y=>arc E y x) k) : (underlying E).Connected := by
  classical
  refine ⟨fun x y=>?_⟩
  obtain ⟨a,ha,b,hb,t,_,route⟩:=connect (arc E) ∅ {x} {y} hk fwd bwd
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  rw [mem_singleton.mp ha,mem_singleton.mp hb] at route
  exact route_reachable (G:=underlying E) (fun ⦃_ _⦄ e=>⟨e.2,Or.inl e.1⟩) route

/-- An original cubic bipartite graph, numbered along a perfect matching,
has a simultaneous directed model with two private ports for every ordered
pair of m centers under explicit finite girth, volume and expansion bounds.
The output lists all m² demands, mutually disjoint route supports, their
lengths, and ownership inside the protected binary trees. -/
theorem all_routes (E : I→I→Prop) (matching : ∀x,E x x)
    (left : ∀x,(∑y,DirectedGrowth.weight E x y)=3) (right : ∀y,(∑x,DirectedGrowth.weight E x y)=3)
    (m l K : ℕ) (hk : 0<K) (large : 259≤m) (w : m≤2^l) (close : 2^l≤2*m) (lp : 0<l)
    (expand : ∀S : Finset (I⊕I),2*S.card≤Fintype.card (I⊕I)→S.card≤K*cross (bipGraph E).Adj S Sᶜ)
    (long : ((2*(2*(9*l)+1) : ℕ) : ℕ∞)<(bipGraph E).egirth)
    (space : m*4^(2*(9*l)+1)<Fintype.card I)
    (speed : 4*(4*l)+4*(K*2)*(Nat.log 2 (Fintype.card I)+1)+1≤m) :
    ∃ center : Fin m→I, ∃ T : Forest (@oriented I (arc E) m) (9*l),
      (∀ i b,T.node (i,b) []=center i) ∧ (∀i j,i≠j→2*(9*l)<(underlying E).dist (center i) (center j)) ∧
      ∃U,Packed (arc E) (T.core (l+4*l)) (2^(4*l)) (2^(4*l)) (2*(4*l))
        (4*(4*l)+4*(K*2)*(Nat.log 2 (Fintype.card I)+1)) (T.demands w (by omega) (by omega)) U := by
  classical
  obtain ⟨forward,backward⟩:=directed_expansion E matching left right K expand
  have kpos:0<K*2:=by omega
  let G:=underlying E
  obtain ⟨center,far⟩:=SeparatedCenters.exists_far G (connected kpos forward backward)
    (max_degree E matching left right) m (2*(9*l)) space
  have high : (4:ℕ∞)<(bipGraph E).egirth := lt_of_le_of_lt (by exact_mod_cast (by omega : 4≤2*(2*(9*l)+1))) long
  let T:=Forest.from_girth center (outgoing_tree E matching left) (incoming_tree E matching right)
    (antireciprocal E matching high) (girth E matching _ long) far
  refine ⟨center,T,?_,far,?_⟩
  · rintro i (_|_) <;> rfl
  · have denom : K*2≤m := by
      have c : 1≤Nat.log 2 (Fintype.card I)+1:=by omega
      have h := Nat.mul_le_mul_left (4*(K*2)) c
      simp at h;omega
    exact T.all_pairs large w close lp (by omega) kpos denom forward backward rfl speed

end SparsePermanent.Contract
#print axioms SparsePermanent.Contract.all_routes
