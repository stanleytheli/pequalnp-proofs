import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_523_aux
open PEqualNP.CircuitLowerBounds

def Reads (N : ℕ) (gs : List Gate) (u v : ℕ) : Prop :=
  ∃ g : Gate, gs[u]? = some g ∧ N+v ∈ g.inputs

def IsAnd (gs : List Gate) (u : ℕ) : Prop :=
  ∃ g : Gate, gs[u]? = some g ∧ g.op = GateOp.and

def Ordered (N : ℕ) (gs : List Gate) :=
  ∀ u g, gs[u]? = some g → ∀ i ∈ g.inputs, i < N+u

def orderB (N : ℕ) (gs : List Gate) : Bool :=
  (List.range gs.length).all (fun u => (gs[u]?).all (fun g => g.inputs.all (· < N+u)))

theorem ordered_of_orderB {N : ℕ} {gs : List Gate} (h : orderB N gs=true) : Ordered N gs := by
  intro u g atU i hi
  have inside := (List.getElem?_eq_some_iff.mp atU).1
  have all := (List.all_eq_true.mp h) u (List.mem_range.mpr inside)
  simp only [atU,Option.all_some] at all
  exact of_decide_eq_true (List.all_eq_true.mp all i hi)

def directB (N : ℕ) (gs : List Gate) (u v : ℕ) : Bool :=
  (gs[u]?).any (fun g => g.inputs.contains (N+v))

def andB (gs : List Gate) (u : ℕ) : Bool :=
  (gs[u]?).any (fun g => match g.op with | .and => true | _ => false)

theorem directB_iff (N : ℕ) (gs : List Gate) (u v : ℕ) :
    directB N gs u v=true ↔ Reads N gs u v := by
  cases h : gs[u]? with
  | none => simp [directB,Reads,h]
  | some g => simp [directB,Reads,h]

theorem andB_iff (gs : List Gate) (u : ℕ) : andB gs u=true ↔ IsAnd gs u := by
  cases h : gs[u]? with
  | none => simp [andB,IsAnd,h]
  | some g => cases op : g.op <;> simp [andB,IsAnd,h,op]

def directSet (N : ℕ) (gs : List Gate) (u : ℕ) : Finset ℕ :=
  (Finset.range u).filter (directB N gs u · = true)

def reachSet (N : ℕ) (gs : List Gate) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | t+1, u => let d := directSet N gs u; d ∪ d.biUnion (reachSet N gs t)

theorem reads_lt {N : ℕ} {gs : List Gate} (order : Ordered N gs) {u v : ℕ}
    (r : Reads N gs u v) : v<u := by
  obtain ⟨g,hg,mem⟩ := r
  have := order u g hg _ mem
  omega

theorem directSet_iff {N : ℕ} {gs : List Gate} (order : Ordered N gs) (u v : ℕ) :
    v ∈ directSet N gs u ↔ Reads N gs u v := by
  simp only [directSet,Finset.mem_filter,Finset.mem_range,directB_iff]
  exact ⟨And.right, fun h => ⟨reads_lt order h,h⟩⟩

theorem reach_sound {N : ℕ} {gs : List Gate} (order : Ordered N gs) (t u v : ℕ)
    (h : v∈reachSet N gs t u) : Relation.TransGen (Reads N gs) u v := by
  induction t generalizing u with
  | zero => simp [reachSet] at h
  | succ t ih =>
    simp only [reachSet,Finset.mem_union,Finset.mem_biUnion,directSet_iff order] at h
    rcases h with step | ⟨w,step,rest⟩
    · exact .single step
    · exact (ih w rest).head step

theorem reach_complete {N : ℕ} {gs : List Gate} (order : Ordered N gs) {u v : ℕ}
    (h : Relation.TransGen (Reads N gs) u v) :
    ∀ t, u ≤ t → v∈reachSet N gs t u := by
  induction h using Relation.TransGen.head_induction_on with
  | @single a h =>
    intro t enough
    have lt := reads_lt order h
    cases t with
    | zero => omega
    | succ t => exact Finset.mem_union_left _ ((directSet_iff order a v).mpr h)
  | @head a c h rest ih =>
    intro t enough
    have lt := reads_lt order h
    cases t with
    | zero => omega
    | succ t =>
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨c,(directSet_iff order a c).mpr h,ih t (by omega)⟩)

def andPairs (N : ℕ) (gs : List Gate) : Finset (ℕ × ℕ) :=
  ((Finset.range gs.length).filter (andB gs · = true)).biUnion (fun a =>
    ((reachSet N gs a a).filter (fun b => a ≠ b ∧ andB gs b=true)).image (Prod.mk a))

theorem mem_andPairs {N : ℕ} {gs : List Gate} (order : Ordered N gs) (q : ℕ×ℕ) :
    q ∈ andPairs N gs ↔ q.1 ≠ q.2 ∧ IsAnd gs q.1 ∧ IsAnd gs q.2 ∧
      Relation.TransGen (Reads N gs) q.1 q.2 := by
  rcases q with ⟨a,b⟩
  simp only [andPairs,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_range,
    Finset.mem_image,andB_iff,Prod.mk.injEq]
  constructor
  · rintro ⟨c,⟨_,hc⟩,d,⟨hd,cd,hda⟩,rfl,rfl⟩
    exact ⟨cd,hc,hda,reach_sound order _ _ _ hd⟩
  · rintro ⟨ne,ha,hb,hr⟩
    have inside : a < gs.length := by
      obtain ⟨g,hg,_⟩ := ha
      exact (List.getElem?_eq_some_iff.mp hg).1
    exact ⟨a,⟨inside,ha⟩,
      b,⟨reach_complete order hr a (by rfl),ne,hb⟩,rfl,rfl⟩

theorem ncard_andPairs {N : ℕ} {gs : List Gate} (order : Ordered N gs) :
    Set.ncard {q : ℕ×ℕ | q.1 ≠ q.2 ∧ IsAnd gs q.1 ∧ IsAnd gs q.2 ∧
      Relation.TransGen (Reads N gs) q.1 q.2} = (andPairs N gs).card := by
  have eq : {q : ℕ×ℕ | q.1 ≠ q.2 ∧ IsAnd gs q.1 ∧ IsAnd gs q.2 ∧
      Relation.TransGen (Reads N gs) q.1 q.2} = (andPairs N gs : Set (ℕ×ℕ)) := by
    ext q
    exact (mem_andPairs order q).symm
  rw [eq, Set.ncard_coe_finset]

/-- Form exactly matching the unbundled natural-number relation in the desk statement. -/
theorem ncard_raw {N : ℕ} {gs : List Gate} (order : Ordered N gs) :
    Set.ncard {q : ℕ×ℕ | q.1 ≠ q.2 ∧
      (∃ g : Gate, gs[q.1]?=some g ∧ g.op=GateOp.and) ∧
      (∃ g : Gate, gs[q.2]?=some g ∧ g.op=GateOp.and) ∧
      Relation.TransGen (fun u v : ℕ => ∃ g : Gate, gs[u]?=some g ∧ N+v∈g.inputs) q.1 q.2}
      = (andPairs N gs).card := ncard_andPairs order

end PEqualNP.Outside.L_meta_523_aux

namespace PEqualNP.Outside.L_meta_523_control
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_523_aux

def exampleCircuit : Circuit := ⟨[
  ⟨.or,[3,1]⟩, ⟨.and,[8,2]⟩, ⟨.or,[3,5]⟩, ⟨.and,[10,4]⟩,
  ⟨.or,[9,11]⟩, ⟨.and,[1,7]⟩, ⟨.or,[13,0]⟩, ⟨.or,[1,6]⟩,
  ⟨.or,[15,5]⟩, ⟨.and,[14,16]⟩, ⟨.or,[12,17]⟩], 18⟩

def lifted : Circuit := ⟨exampleCircuit.gates.set 6 ⟨.or,[0,0]⟩ ++ [⟨.or,[18,13]⟩], 19⟩

def edgeFunction (x : Fin 8 → Bool) :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)

def nestedPairs (C : Circuit) : Set (ℕ×ℕ) :=
  {q | q.1≠q.2 ∧ (∃ g : Gate, C.gates[q.1]?=some g ∧ g.op=GateOp.and) ∧
    (∃ g : Gate, C.gates[q.2]?=some g ∧ g.op=GateOp.and) ∧
    Relation.TransGen (fun u v : ℕ => ∃ g : Gate, C.gates[u]?=some g ∧ 8+v∈g.inputs)
      q.1 q.2}

theorem example_pairs : (nestedPairs exampleCircuit).ncard=1 ∧ (nestedPairs lifted).ncard=0 := by
  unfold nestedPairs
  rw [ncard_raw (N:=8) (gs:=exampleCircuit.gates) (ordered_of_orderB (by decide)),
    ncard_raw (N:=8) (gs:=lifted.gates) (ordered_of_orderB (by decide))]
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem example_lift : ∀ x : Fin 8 → Bool,
    exampleCircuit.eval (List.ofFn x)=edgeFunction x ∧ lifted.eval (List.ofFn x)=edgeFunction x ∧
    ((exampleCircuit.wires (List.ofFn x)).getD 13 false=true → edgeFunction x=true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_523_control
