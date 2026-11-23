import ProjectivePlane650
import StandaloneOneSided

namespace ProjectivePlane650
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers PEqualNP.Outside.Chain588
open PEqualNP.Outside.Rectangles624 PEqualNP.Outside.Charging624

theorem bipartition : ∀ u v : V, v∈N u → (u∈allPoints ↔ v∉allPoints) := by decide +kernel

def collision (C : Circuit) (side : Finset V) : Prop :=
  ∃ u∈side, ∃ r, G.Adj u r ∧ ∃ p i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ ∧
    vl C.gates (rightRow side) (26+p)=false ∧ vl C.gates (two u r) (26+p)=true ∧
    atGate 26 p (vl C.gates (one r)) i=false ∧ atGate 26 p (vl C.gates (one r)) j=false

theorem small_circuit_collides (C : Circuit) (mono : Monotone2 C)
    (short : C.size≤63) (correct : ∀ x : V→Bool, C.eval (List.ofFn x)=true ↔ accepts x) :
    collision C allPoints ∧ collision C (Finset.univ \ allPoints) := by
  classical
  have edgeCount : G.edgeSet.ncard=52 := by
    rw [← G.coe_edgeFinset, Set.ncard_coe_finset, num_edges]
  have sem (x : V→Bool) :
      circuitFun 26 C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true :=
    (correct x).trans (accepts_iff x)
  have cut (S : Finset V) (hs : ∀ u v, G.Adj u v → (u∈S ↔ v∉S)) : collision C S :=
    collision_of_counterexample G C (fun _ _ _ _ => square) mono S hs sem 13 min_cover (by omega)
  exact ⟨cut allPoints bipartition,cut _ (by
    intro u v h
    have H := bipartition u v h
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not]
    tauto)⟩

end ProjectivePlane650

#print axioms ProjectivePlane650.small_circuit_collides
