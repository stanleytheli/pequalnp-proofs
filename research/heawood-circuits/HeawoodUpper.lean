import Mathlib
import PEqualNP.Defs

namespace HeawoodBound
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)

def atGate (N p : ℕ) (v : ℕ → Bool) (w : ℕ) := if w < N+p then v w else false

theorem raw_gate {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]?=some g) : vl gs x (N+p) = g.op.eval (g.inputs.map (atGate N p (vl gs x))) := by
  obtain ⟨pre,post,rfl,rfl⟩ := split_at gs p g hp
  have len : (wiresFrom pre (List.ofFn x)).length = N+pre.length := by rw [length_wiresFrom]; simp
  have ext : wiresFrom (pre++g::post) (List.ofFn x) = wiresFrom post (wiresFrom pre (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun j => (wiresFrom pre (List.ofFn x)).getD j false)]) := by
    rw [wiresFrom_append]; rfl
  unfold vl
  rw [ext,getD_wiresFrom _ _ _ (by simp [len]),getD_snoc_len _ _ _ _ len]
  congr 1
  apply List.map_congr_left
  intro w _
  by_cases lt : w<N+pre.length
  · simp only [atGate,ite_eq_left lt]
    rw [getD_wiresFrom post _ w (by simp [len]; omega),getD_snoc_ne (wiresFrom pre (List.ofFn x)) _ _ w (by omega)]
  · simp only [atGate,ite_eq_right lt]
    exact List.getD_eq_default _ _ (by omega)

theorem trace_unique {N : ℕ} (gs : List Gate) (x : Fin N → Bool) (v : ℕ → Bool)
    (raw : ∀ i : Fin N, v i.val=x i) (beyond : ∀ w, N+gs.length ≤ w → v w=false)
    (step : ∀ p g, gs[p]?=some g → v (N+p)=g.op.eval (g.inputs.map (atGate N p v))) :
    ∀ w, vl gs x w=v w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h : w<N
    · exact (vl_input gs x w h).trans (raw ⟨w,h⟩).symm
    obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
    cases hp : gs[p]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp hp
      rw [vl_beyond _ _ _ (by omega),beyond _ (by omega)]
    | some g =>
      rw [raw_gate gs x p g hp,step p g hp]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j<N+p <;> simp [atGate,hj,ih j]



def table (x : Fin 14→Bool) : List Bool :=
  [x 0,
   x 1,
   x 2,
   x 3,
   x 4,
   x 5,
   x 6,
   x 7,
   x 8,
   x 9,
   x 10,
   x 11,
   x 12,
   x 13,
   (x 8 || x 10),
   (x 7 || (x 8 || x 10)),
   (x 0 && (x 7 || (x 8 || x 10))),
   (x 9 || x 13),
   (x 7 || (x 9 || x 13)),
   (x 1 && (x 7 || (x 9 || x 13))),
   (x 12 || x 13),
   (x 8 || (x 12 || x 13)),
   (x 2 && (x 8 || (x 12 || x 13))),
   (x 11 || x 12),
   (x 7 || (x 11 || x 12)),
   (x 3 && (x 7 || (x 11 || x 12))),
   (x 11 || x 13),
   (x 10 || (x 11 || x 13)),
   (x 4 && (x 10 || (x 11 || x 13))),
   (x 10 || x 12),
   (x 9 || (x 10 || x 12)),
   (x 5 && (x 9 || (x 10 || x 12))),
   (x 9 || x 11),
   (x 8 || (x 9 || x 11)),
   (x 6 && (x 8 || (x 9 || x 11))),
   ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11)))),
   ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11))))),
   ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11)))))),
   ((x 2 && (x 8 || (x 12 || x 13))) || ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11))))))),
   ((x 1 && (x 7 || (x 9 || x 13))) || ((x 2 && (x 8 || (x 12 || x 13))) || ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11)))))))),
   ((x 0 && (x 7 || (x 8 || x 10))) || ((x 1 && (x 7 || (x 9 || x 13))) || ((x 2 && (x 8 || (x 12 || x 13))) || ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11)))))))))]

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [7, 14]⟩,
    ⟨GateOp.and, [0, 15]⟩,
    ⟨GateOp.or, [9, 13]⟩,
    ⟨GateOp.or, [7, 17]⟩,
    ⟨GateOp.and, [1, 18]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [8, 20]⟩,
    ⟨GateOp.and, [2, 21]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [7, 23]⟩,
    ⟨GateOp.and, [3, 24]⟩,
    ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [10, 26]⟩,
    ⟨GateOp.and, [4, 27]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [9, 29]⟩,
    ⟨GateOp.and, [5, 30]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [8, 32]⟩,
    ⟨GateOp.and, [6, 33]⟩,
    ⟨GateOp.or, [31, 34]⟩,
    ⟨GateOp.or, [28, 35]⟩,
    ⟨GateOp.or, [25, 36]⟩,
    ⟨GateOp.or, [22, 37]⟩,
    ⟨GateOp.or, [19, 38]⟩,
    ⟨GateOp.or, [16, 39]⟩]
  output := 40
def edges : List (ℕ × ℕ) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
def finEdges : List (Fin 14 × Fin 14) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]

theorem edges_cast (u v : Fin 14) : (u.val,v.val)∈edges ↔ (u,v)∈finEdges := by
  revert u v
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem upper : Monotone2 circuit ∧ circuit.size=27 ∧
    ∀ x : Fin 14 → Bool, circuit.eval (List.ofFn x)=true ↔
      ∃ u v : Fin 14, (u.val,v.val)∈edges ∧ x u=true ∧ x v=true := by
  refine ⟨?_,rfl,?_⟩
  · simp [Monotone2,circuit]
  · intro x
    have agree : ∀ w, vl circuit.gates x w=(table x).getD w false := by
      apply trace_unique
      · intro i; fin_cases i <;> rfl
      · intro w hw
        exact List.getD_eq_default _ _ (by simpa [circuit,table] using hw)
      · intro p g h
        have bound := (List.getElem?_eq_some_iff.mp h).1
        change p<27 at bound
        interval_cases p <;> simp [circuit] at h <;> subst g <;>
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
            List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true] <;> rfl
    have val : circuit.eval (List.ofFn x) = ((x 0 && (x 7 || (x 8 || x 10))) || ((x 1 && (x 7 || (x 9 || x 13))) || ((x 2 && (x 8 || (x 12 || x 13))) || ((x 3 && (x 7 || (x 11 || x 12))) || ((x 4 && (x 10 || (x 11 || x 13))) || ((x 5 && (x 9 || (x 10 || x 12))) || (x 6 && (x 8 || (x 9 || x 11))))))))) := by
      exact agree 40
    have factors : circuit.eval (List.ofFn x)=(finEdges.any fun e => x e.1 && x e.2) := by
      rw [val]
      simp only [finEdges,List.any_cons,List.any_nil,Bool.or_false,Bool.and_or_distrib_left,
        Bool.or_assoc]
    rw [factors,List.any_eq_true]
    constructor
    · rintro ⟨⟨u,v⟩,mem,lit⟩
      exact ⟨u,v,(edges_cast u v).mpr mem,(Bool.and_eq_true_iff.mp lit)⟩
    · rintro ⟨u,v,mem,hu,hv⟩
      exact ⟨(u,v),(edges_cast u v).mp mem,Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
end HeawoodBound
