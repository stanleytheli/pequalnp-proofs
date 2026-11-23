import Mathlib
import PEqualNP.Defs

namespace TriangularPrism

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [11, 14]⟩]
  output := 15

def edges : List (ℕ × ℕ) :=
  [(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem ten_gate_witness :
    Monotone2 circuit ∧ circuit.size = 10 ∧
    ∀ x : Fin 6 → Bool, circuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  refine ⟨?_,rfl,?_⟩
  · simp [Monotone2,circuit]
  · decide +kernel

end TriangularPrism
