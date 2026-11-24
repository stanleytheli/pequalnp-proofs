import Mathlib
namespace PositiveCornerClosure
open Finset
variable {V E : Type*} [DecidableEq V]

private def addVertices (s : Finset V) : List V → Finset V
  | [] => s
  | v::vs => insert v (addVertices s vs)

private theorem mem_addVertices {s : Finset V} {v : V} (vs : List V) :
    v∈addVertices s vs ↔ v∈s ∨ v∈vs := by
  induction vs with
  | nil => simp [addVertices]
  | cons a as ih => simp [addVertices,ih]; tauto

private theorem cost_addVertices (s : Finset V) (c : V→ℕ) (vs : List V) :
    (∑ v∈addVertices s vs, c v) ≤ (∑ v∈s, c v)+(vs.map c).sum := by
  induction vs with
  | nil => simp [addVertices]
  | cons a as ih =>
    by_cases h : a∈addVertices s as
    · simp only [addVertices,insert_eq_of_mem h,List.map_cons,List.sum_cons]
      omega
    · rw [addVertices,Finset.sum_insert h]
      simp only [List.map_cons,List.sum_cons]
      omega

private theorem sum_below (c : V→ℕ) (limit : ℕ) (h : ∀ v,c v<limit) (vs : List V) :
    (vs.map c).sum≤limit*vs.length ∧ (vs≠[] → (vs.map c).sum<limit*vs.length) := by
  induction vs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,List.cons_ne_nil,
      not_false_eq_true,true_implies]
    have ha:=h a
    omega

/-- If a proposed cover misses an edge, adding one endpoint per missed edge
strictly improves a per-edge penalty dominating every vertex cost. The graph
may have loops or indexed parallel edges. -/
theorem repair_uncovered [DecidableEq E] (edges : Finset E) (left right : E→V)
    (cost : V→ℕ) (penalty : ℕ) (dom : ∀ v, cost v<penalty) (s : Finset V)
    (bad : (edges.filter (fun e=>left e∉s ∧ right e∉s)).Nonempty) :
    ∃ cover : Finset V, s⊆cover ∧
      (∀ e∈edges, left e∈cover ∨ right e∈cover) ∧
      (∑ v∈cover,cost v) < (∑ v∈s,cost v)+penalty*(edges.filter (fun e=>left e∉s ∧ right e∉s)).card := by
  classical
  let miss := edges.filter (fun e=>left e∉s ∧ right e∉s)
  let fixes := miss.toList.map left
  have length : fixes.length=miss.card := by simp [fixes]
  have size : 0<fixes.length := by rw [length]; exact Finset.card_pos.mpr bad
  have ne : fixes≠[] := by intro empty; simp [empty] at size
  refine ⟨addVertices s fixes,fun v hv=>(mem_addVertices fixes).mpr (.inl hv),?_,?_⟩
  · intro e he
    by_cases l : left e∈s
    · exact .inl ((mem_addVertices fixes).mpr (.inl l))
    · by_cases r : right e∈s
      · exact .inr ((mem_addVertices fixes).mpr (.inl r))
      · exact .inl ((mem_addVertices fixes).mpr (.inr (List.mem_map.mpr
          ⟨e,by simpa [miss,he,l,r],rfl⟩)))
  · have hc:=cost_addVertices s cost fixes
    have hl:=(sum_below cost penalty dom fixes).2 ne
    rw [length] at hl
    change _ < _+penalty*miss.card
    omega

/-- The scalar closed row cost when the first inconsistent gate is strictly
more expensive than all following faithful stages and the reject bit. -/
theorem first_error (prefixCost tailFaithful tailActual charged priority reject : ℕ)
    (dominates : 1+tailFaithful<priority) (wrong : 8*priority≤charged) :
    prefixCost+7*priority+tailFaithful+1 < prefixCost+charged+tailActual+reject := by omega

end PositiveCornerClosure
#print axioms PositiveCornerClosure.repair_uncovered
#print axioms PositiveCornerClosure.first_error
