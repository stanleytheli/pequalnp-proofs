import PinTransport

namespace LimitedNegation.Project
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.Window997

def inputVector (n : ℕ) : Finset (Fin n) →o Wires where
  toFun b := vector (List.ofFn (bits b))
  monotone' := by
    intro a b ab i
    change vector (List.ofFn (bits a)) i ≤ vector (List.ofFn (bits b)) i
    by_cases hi : i<n
    · have eq (y : Finset (Fin n)) : vector (List.ofFn (bits y)) i = bits y ⟨i,hi⟩ := by
        unfold vector
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [eq a,eq b,Bool.le_iff_imp]
      exact fun h => decide_eq_true (ab (of_decide_eq_true h))
    · have eq (y : Finset (Fin n)) : vector (List.ofFn (bits y)) i = false :=
        List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt hi))
      rw [eq a,eq b]

def legal (C : Circuit) := ∀ g∈C.gates, allowed g ∧ g.inputs.length≤2

lemma constGate_mono (b : Bool) :
    ((constGate b).op=.and ∨ (constGate b).op=.or) ∧ (constGate b).inputs.length≤2 := by
  cases b <;> simp [constGate]

lemma frozen_mono (gs : List Gate) (valid : ∀ g∈gs, allowed g ∧ g.inputs.length≤2)
    (bs : List Bool) : ∀ e∈frozen gs bs, (e.op=.and ∨ e.op=.or) ∧ e.inputs.length≤2 := by
  induction gs generalizing bs with
  | nil => simp [frozen]
  | cons g gs ih =>
    have v := valid g (by simp)
    have tail : ∀ e∈gs, allowed e ∧ e.inputs.length≤2 := fun e he => valid _ (by simp [he])
    intro e he
    by_cases h : isNot g.op=true
    · simp only [frozen,ite_eq_left h,List.mem_cons] at he
      rcases he with rfl|hm
      · exact constGate_mono _
      · exact ih tail _ _ hm
    · simp only [frozen,ite_eq_right h,List.mem_cons] at he
      rcases he with rfl|hm
      · refine ⟨?_,v.2⟩
        rcases v.1 with c|c|c
        · exact Or.inl c
        · exact Or.inr c
        · exfalso; apply h; rw [c]; rfl
      · exact ih tail _ _ hm

/-- For some small base, one physical AND/OR list of the same size computes
all outputs throughout the whole upward Hamming ball. -/
theorem freeze_window (n : ℕ) (C : Circuit) (valid : legal C) (h : ℕ) :
    let t := C.gates.countP (fun g => isNot g.op)
    ∃ base : Finset (Fin n), ∃ P : Circuit,
      base.card≤(2^t-1)*h ∧ monoG P ∧ P.size=C.size ∧
      ∀ z : Finset (Fin n), base⊆z → z.card≤base.card+h → ∀ o,
        value P (bits z) o = value C (bits z) o := by
  dsimp only
  let gs := stages n C.gates
  obtain ⟨base,bound,ball⟩ := circuit_window gs (inputVector n) h
  let bs := choices gs (inputVector n base)
  let P := {C with gates := frozen C.gates bs}
  have allowedG : ∀ g∈C.gates, allowed g := fun g hg => (valid g hg).1
  refine ⟨base,P,?_,frozen_mono _ valid bs,?_,?_⟩
  · simpa [gs,translated_count] using bound
  · exact frozen_len _ _
  · intro z sub cap o
    have hwin := ball z sub cap
    let xs := List.ofFn (bits z)
    have hl : xs.length=n := by simp [xs]
    have eq1 := pin_list C.gates allowedG xs bs
    have eq2 := run_list C.gates allowedG xs
    rw [hl] at eq1 eq2
    change LimitedNegation.pin (stages n C.gates) bs (vector xs) =
      LimitedNegation.run (stages n C.gates) (vector xs) at hwin
    rw [eq1,eq2] at hwin
    exact congrFun hwin o

end LimitedNegation.Project
#print axioms LimitedNegation.Project.freeze_window
