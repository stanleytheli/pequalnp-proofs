import FlowCost
import FlowCycle

namespace SparsePermanent

/-- Every ordinary simple cycle of the canonically subdivided bipartite graph
uses at least four joins and at least two internal port-gadget edges per join. -/
theorem family_egirth_lower {R : Type} [CommSemiring R] {k : ℕ} (h : ℕ)
    (A : Matrix (Node k) (Node k) R) :
    ((4*(2*h+3) : ℕ) : ℕ∞)≤(bipGraph (familyBoard h A).adj).egirth :=
  CycleFlow.le_egirth (fun Z live=>family_flow_lower h A Z live)

end SparsePermanent
#print axioms SparsePermanent.family_egirth_lower
