import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Chain588.Helpers
open PEqualNP.CircuitLowerBounds

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate]

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

end PEqualNP.Outside.Chain588.Helpers



namespace PEqualNP.Outside.Chain588
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers

/-- Reading a forward reference in the circuit semantics returns false. -/
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

/-- A Boolean labelling under which OR edges propagate truth. -/
def ORLabel (N : ℕ) (C : Circuit) (v : ℕ → Bool) : Prop :=
  ∀ j : Fin C.gates.length, (C.gates.get j).op=GateOp.or → ∀ w ∈ (C.gates.get j).inputs,
    v w=true → v (N+j.val)=true

/-- Gates surviving compaction, in their original order. -/
private abbrev emb {m : ℕ} (K : Finset (Fin m)) : Fin K.card ↪o Fin m := K.orderEmbOfFin rfl

/-- Give a surviving wire its compact index. Deleted wires denote a fixed invalid wire. -/
noncomputable def number {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (w : ℕ) : ℕ :=
  if w < N then w else if h : ∃ j : Fin K.card, N+(emb K j).val=w then N+(Classical.choose h).val else N+K.card

/-- Read a labelling of the old circuit using the compact wire indices. -/
def label {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (v : ℕ → Bool) (w : ℕ) : Bool :=
  if w < N then v w else if h : w-N<K.card then v (N+(emb K ⟨w-N,h⟩).val) else false

theorem emb_mem {m : ℕ} (K : Finset (Fin m)) (i : Fin K.card) : emb K i ∈ K := by
  have h := K.range_orderEmbOfFin rfl
  rw [←Finset.mem_coe,←h]; exact ⟨i,rfl⟩

theorem emb_onto {m : ℕ} (K : Finset (Fin m)) {j : Fin m} (hj : j∈K) : ∃ i, emb K i=j := by
  have h := K.range_orderEmbOfFin rfl
  exact (show j ∈ Set.range (K.orderEmbOfFin rfl) by rw [h]; exact hj)

theorem label_raw {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (v : ℕ → Bool) (w : ℕ) (h : w<N) :
    label N K v w=v w := by simp [label,h]

theorem label_gate {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (v : ℕ → Bool) (i : Fin K.card) :
    label N K v (N+i.val)=v (N+(emb K i).val) := by simp [label,i.isLt]

theorem label_invalid {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (v : ℕ → Bool) {w : ℕ} (hw : N+K.card ≤ w) :
    label N K v w=false := by unfold label; split_ifs <;> first | rfl | omega

theorem number_raw {m : ℕ} (N : ℕ) (K : Finset (Fin m)) {w : ℕ} (hw : w<N) :
    number N K w=w := by simp [number,hw]

theorem number_gate {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (i : Fin K.card) :
    number N K (N+(emb K i).val) = N+i.val := by
  classical
  have h : ∃ j : Fin K.card, N+(emb K j).val=N+(emb K i).val := ⟨i,rfl⟩
  have id : Classical.choose h=i := (emb K).injective (Fin.ext (Nat.add_left_cancel (Classical.choose_spec h)))
  unfold number
  rw [ite_eq_right (by omega),dite_eq_left h,id]

theorem number_gone {m : ℕ} (N : ℕ) (K : Finset (Fin m)) {w : ℕ} (hw : N ≤ w)
    (no : ∀ i : Fin K.card, N+(emb K i).val ≠ w) : number N K w=N+K.card := by
  simp [number,show ¬w<N by omega,not_exists.mpr no]

/-- Rewire each retained gate to specified original wire IDs, preserving the gate operation. -/
noncomputable def pack {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (gate : Fin m → Gate)
    (source : Fin m → ℕ → ℕ) (out : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin K.card =>
    let g := gate (emb K i)
    ⟨g.op,g.inputs.map (fun w => number N K (source (emb K i) w))⟩),number N K out⟩

@[simp] theorem pack_len {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (g : Fin m → Gate)
    (a : Fin m → ℕ → ℕ) (o : ℕ) : (pack N K g a o).gates.length=K.card := by simp [pack]

private theorem pack_get {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (g : Fin m → Gate)
    (a : Fin m → ℕ → ℕ) (o : ℕ) (i : Fin K.card) :
    (pack N K g a o).gates[i.val]?=some ⟨(g (emb K i)).op,(g (emb K i)).inputs.map
      (fun w => number N K (a (emb K i) w))⟩ := by simp [pack,i.isLt]

theorem pack_fan {m : ℕ} (N : ℕ) (K : Finset (Fin m)) (g : Fin m → Gate)
    (a : Fin m → ℕ → ℕ) (o : ℕ) (h : ∀ i, Ok (g i)) : FanInTwo (pack N K g a o) := by
  intro gg hg
  simp only [pack,List.mem_ofFn] at hg
  obtain ⟨i,rfl⟩ := hg
  exact ⟨(h _).1,by simpa using (h (emb K i)).2⟩

end PEqualNP.Outside.Chain588

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588

private theorem bool_gate_mono (g : Gate) (ops : g.op=GateOp.and ∨ g.op=GateOp.or)
    (a b : ℕ → Bool) (le : ∀ w∈g.inputs, a w=true → b w=true) :
    g.op.eval (g.inputs.map a)=true → g.op.eval (g.inputs.map b)=true := by
  rcases ops with op|op <;> rw [op]
  · intro yes
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact le w hw ((List.all_eq_true.mp yes) _ (List.mem_map.mpr ⟨w,hw,rfl⟩))
  · intro yes
    obtain ⟨v,hv,h⟩ := List.any_eq_true.mp yes
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨w,hw,rfl⟩,le w hw h⟩

private theorem monotone_wires {N : ℕ} (gs : List Gate) (ops : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
    (x y : Fin N → Bool) (le : ∀ v, x v=true → y v=true) :
    ∀ w, vl gs x w=true → vl gs y w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w<N
    · rw [vl_input gs x w raw,vl_input gs y w raw]; exact le _
    obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
    cases hp : gs[p]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp hp
      rw [vl_beyond gs x _ (by omega)]; simp
    | some g =>
      rw [raw_gate gs x p g hp,raw_gate gs y p g hp]
      obtain ⟨h,eq⟩ := List.getElem?_eq_some_iff.mp hp
      apply bool_gate_mono g (ops g (eq ▸ List.getElem_mem h))
      intro u _ hu
      by_cases lt : u<N+p
      · simp only [atGate,ite_eq_left lt] at hu ⊢; exact ih u lt hu
      · simp [atGate,lt] at hu

private def forced (gs : List Gate) (p : ℕ) := gs.set p ⟨GateOp.and,[]⟩

private theorem force_ops (gs : List Gate) (ops : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or) (p : ℕ) :
    ∀ g ∈ forced gs p, g.op=GateOp.and ∨ g.op=GateOp.or := by
  intro g hg
  obtain ⟨j,eq⟩ := List.get_of_mem hg
  have bound := j.isLt
  simp [forced] at bound
  have atj : (forced gs p)[j.val]?=some g := (List.getElem?_eq_getElem j.isLt).trans (congrArg some eq)
  by_cases jp : j.val=p
  · have hp : p<gs.length := jp ▸ bound
    have eqp : (forced gs p)[j.val]? = some ⟨GateOp.and,[]⟩ := by simp [forced,jp,hp]
    have gg := Option.some.inj (atj.symm.trans eqp)
    exact Or.inl (congrArg Gate.op gg)
  · have hg' : gs[j.val]?=some g := by simpa [forced,Ne.symm jp] using atj
    obtain ⟨lt,eq'⟩ := List.getElem?_eq_some_iff.mp hg'
    exact ops g (eq' ▸ List.getElem_mem lt)

private theorem force_agrees {N : ℕ} (gs : List Gate) (p : ℕ) (x : Fin N → Bool)
    (yes : vl gs x (N+p)=true) : ∀ w, vl (forced gs p) x w=vl gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w<N
    · rw [vl_input _ _ _ raw,vl_input _ _ _ raw]
    obtain ⟨q,rfl⟩ : ∃ q, w=N+q := ⟨w-N,by omega⟩
    by_cases inside : q<gs.length
    · by_cases qp : q=p
      · subst q
        have hg : (forced gs p)[p]?=some ⟨GateOp.and,[]⟩ := by simp [forced,inside]
        rw [raw_gate _ _ p _ hg,yes]; rfl
      · let g := gs[q]
        have og : gs[q]?=some g := List.getElem?_eq_getElem inside
        have ng : (forced gs p)[q]?=some g := by simpa [forced,Ne.symm qp] using og
        rw [raw_gate _ _ q g ng,raw_gate _ _ q g og]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases lt : i<N+q <;> simp [atGate,lt,ih i]
    · have len : (forced gs p).length=gs.length := by simp [forced]
      rw [vl_beyond _ x _ (by omega),vl_beyond gs x _ (by omega)]

def one {N : ℕ} (a : Fin N) : Fin N → Bool := fun i => decide (i=a)

def Singletons {N : ℕ} (C : Circuit) (p : ℕ) := {a : Fin N | vl C.gates (one a) (N+p)=true}
def Context {N : ℕ} (C : Circuit) (p : ℕ) := {a : Fin N | vl (forced C.gates p) (one a) C.output=true}

/-- Every single vertex lighting a wire forms a real edge with each single vertex that can
accept with the same wire clamped true. The circuit may share that wire arbitrarily. -/
theorem gate_rectangle {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (mono : Monotone2 C) (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) (p : ℕ) {a b : Fin N}
    (ha : a∈Singletons C p) (hb : b∈Context C p) : G.Adj a b := by
  let x : Fin N → Bool := fun i => decide (i=a ∨ i=b)
  have ops : ∀ g∈C.gates, g.op=GateOp.and ∨ g.op=GateOp.or := fun g hg => (mono g hg).1
  have A : ∀ v, one a v=true → x v=true := by intro v hv; simpa [one,x] using Or.inl (of_decide_eq_true hv)
  have B : ∀ v, one b v=true → x v=true := by intro v hv; simpa [one,x] using Or.inr (of_decide_eq_true hv)
  have sat := monotone_wires C.gates ops (one a) x A (N+p) ha
  have ctx := monotone_wires (forced C.gates p) (force_ops _ ops p) (one b) x B C.output hb
  have yes : circuitFun N C x=true := (force_agrees C.gates p x sat C.output).symm.trans ctx
  obtain ⟨u,v,adj,xu,xv⟩ := (sem x).mp yes
  simp only [x,decide_eq_true_eq] at xu xv
  rcases xu with rfl|rfl <;> rcases xv with rfl|rfl
  · exact (G.loopless.irrefl _ adj).elim
  · exact adj
  · exact adj.symm
  · exact (G.loopless.irrefl _ adj).elim

theorem narrow_context_of_wide {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) (p : ℕ) {a b : Fin N} (ab : a≠b)
    (ha : a∈Singletons C p) (hb : b∈Singletons C p) : (Context (N:=N) C p).Subsingleton := by
  intro u hu v hv
  have edge := fun a b => @gate_rectangle N G C mono sem p a b
  exact (c4 a u b v (edge a u ha hu) (edge b u hb hu).symm (edge b v hb hv) (edge a v ha hv).symm).resolve_left ab

/-- A wire clamped true at the singleton u cannot genuinely combine two other vertices
outside its neighborhood unless those two vertices themselves form an edge. -/
theorem and_outside_rectangle {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (mono : Monotone2 C) (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) (p i j : ℕ)
    (gate : C.gates[p]?=some ⟨GateOp.and,[i,j]⟩) {u a b : Fin N}
    (ctx : u∈Context C p) (aLit : atGate N p (vl C.gates (one a)) i=true)
    (bLit : atGate N p (vl C.gates (one b)) j=true)
    (au : ¬ G.Adj u a) (bu : ¬ G.Adj u b) : G.Adj a b := by
  let x : Fin N → Bool := fun v => decide (v=u ∨ v=a ∨ v=b)
  have ops : ∀ g∈C.gates, g.op=GateOp.and ∨ g.op=GateOp.or := fun g hg => (mono g hg).1
  have le (z : Fin N) (hz : z=u ∨ z=a ∨ z=b) : ∀ v, one z v=true → x v=true := by
    intro v h; have vz : v=z := of_decide_eq_true h; subst v; exact decide_eq_true hz
  have iLt : i<N+p := by by_contra h; simp [atGate,h] at aLit
  have jLt : j<N+p := by by_contra h; simp [atGate,h] at bLit
  simp only [atGate,ite_eq_left iLt] at aLit
  simp only [atGate,ite_eq_left jLt] at bLit
  have iYes := monotone_wires C.gates ops (one a) x (le a (Or.inr (Or.inl rfl))) i aLit
  have jYes := monotone_wires C.gates ops (one b) x (le b (Or.inr (Or.inr rfl))) j bLit
  have yes : vl C.gates x (N+p)=true := by
    rw [raw_gate C.gates x p _ gate]
    simp [GateOp.eval,atGate,iLt,jLt,iYes,jYes]
  have old := monotone_wires (forced C.gates p) (force_ops _ ops p) (one u) x
    (le u (Or.inl rfl)) C.output ctx
  have out : circuitFun N C x=true := (force_agrees C.gates p x yes C.output).symm.trans old
  obtain ⟨c,d,adj,hc,hd⟩ := (sem x).mp out
  simp only [x,decide_eq_true_eq] at hc hd
  rcases hc with rfl|rfl|rfl <;> rcases hd with rfl|rfl|rfl
  all_goals first
    | exact (G.loopless.irrefl _ adj).elim
    | exact (au adj).elim
    | exact (au adj.symm).elim
    | exact (bu adj).elim
    | exact (bu adj.symm).elim
    | exact adj
    | exact adj.symm

/-- In a graph with no four-cycle, at a fixed singleton context u one operand has
at most one independently lighting vertex outside the neighborhood of u. -/
theorem and_outside_narrow {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) (p i j : ℕ)
    (gate : C.gates[p]?=some ⟨GateOp.and,[i,j]⟩) {u : Fin N} (ctx : u∈Context C p) :
    {a : Fin N | atGate N p (vl C.gates (one a)) i=true ∧ ¬G.Adj u a}.Subsingleton ∨
    {a : Fin N | atGate N p (vl C.gates (one a)) j=true ∧ ¬G.Adj u a}.Subsingleton := by
  classical
  by_cases left : {a : Fin N | atGate N p (vl C.gates (one a)) i=true ∧ ¬G.Adj u a}.Subsingleton
  · exact Or.inl left
  apply Or.inr
  unfold Set.Subsingleton at left
  push Not at left
  obtain ⟨a,ha,b,hb,ab⟩ := left
  intro c hc d hd
  have edge := fun a b => @and_outside_rectangle N G C mono sem p i j gate u a b ctx
  exact (c4 a c b d (edge a c ha.1 hc.1 ha.2 hc.2) (edge b c hb.1 hc.1 hb.2 hc.2).symm
    (edge b d hb.1 hd.1 hb.2 hd.2) (edge a d ha.1 hd.1 ha.2 hd.2).symm).resolve_left ab

end PEqualNP.Outside.Rectangles624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588

private theorem lift_binary_pos (g : Gate) (op : g.op=GateOp.and ∨ g.op=GateOp.or)
    (len : g.inputs.length≤2) (pair left right : ℕ → Bool)
    (lift : ∀ i∈g.inputs, pair i=true → left i=true ∨ right i=true)
    (noCross : ∀ i j, g=⟨GateOp.and,[i,j]⟩ →
      ¬((left i=true ∧ right j=true) ∨ (right i=true ∧ left j=true))) :
    g.op.eval (g.inputs.map pair)=true →
      g.op.eval (g.inputs.map left)=true ∨ g.op.eval (g.inputs.map right)=true := by
  obtain ⟨op',ins⟩ := g
  simp only at op len lift ⊢
  rcases op with rfl|rfl
  · cases ins with
    | nil => simp [GateOp.eval]
    | cons i rest =>
      cases rest with
      | nil => simpa [GateOp.eval] using lift i (by simp)
      | cons j rest =>
        cases rest with
        | cons k more => simp at len
        | nil =>
          intro hp
          have both : pair i=true ∧ pair j=true := by simpa [GateOp.eval] using hp
          rcases lift i (by simp) both.1 with il|ir <;> rcases lift j (by simp) both.2 with jl|jr
          · simp [GateOp.eval,il,jl]
          · exact (noCross i j rfl (Or.inl ⟨il,jr⟩)).elim
          · exact (noCross i j rfl (Or.inr ⟨ir,jl⟩)).elim
          · simp [GateOp.eval,ir,jr]
  · intro hp
    obtain ⟨_,hv,h⟩ := List.any_eq_true.mp hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
    rcases lift i hi h with hl|hr
    · exact Or.inl (List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,hl⟩)
    · exact Or.inr (List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,hr⟩)

def two {N : ℕ} (a b : Fin N) : Fin N → Bool := fun i => decide (i=a ∨ i=b)

def Crosses {N : ℕ} (gs : List Gate) (p i j : ℕ) (a b : Fin N) : Prop :=
  (atGate N p (vl gs (one a)) i=true ∧ atGate N p (vl gs (one b)) j=true) ∨
  (atGate N p (vl gs (one b)) i=true ∧ atGate N p (vl gs (one a)) j=true)

/-- Every pair rejected on both single vertices first separates at some two-input AND
whose operands light on the two opposite singleton inputs. -/
theorem pair_crosses_and {N : ℕ} (C : Circuit) (mono : Monotone2 C) (a b : Fin N)
    (yes : vl C.gates (two a b) C.output=true)
    (noA : vl C.gates (one a) C.output=false) (noB : vl C.gates (one b) C.output=false) :
    ∃ p i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ ∧ Crosses C.gates p i j a b := by
  classical
  by_contra no
  have lift : ∀ w, vl C.gates (two a b) w=true →
      vl C.gates (one a) w=true ∨ vl C.gates (one b) w=true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases raw : w<N
      · rw [vl_input _ _ _ raw,vl_input _ _ _ raw,vl_input _ _ _ raw]
        simp [one,two]
      obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
      cases atP : C.gates[p]? with
      | none =>
        have := List.getElem?_eq_none_iff.mp atP
        rw [vl_beyond _ (two a b) _ (by omega)]; simp
      | some g =>
        have info := List.getElem?_eq_some_iff.mp atP
        have h := mono g (info.2 ▸ List.getElem_mem info.1)
        rw [raw_gate _ _ _ _ atP,raw_gate _ _ _ _ atP,raw_gate _ _ _ _ atP]
        apply lift_binary_pos g h.1 h.2
        · intro i _ hi
          by_cases inside : i<N+p
          · simp only [atGate,ite_eq_left inside] at hi ⊢
            exact ih i inside hi
          · simp [atGate,inside] at hi
        · intro i j shape cross
          exact no ⟨p,i,j,shape ▸ atP,cross⟩
  rcases lift C.output yes with h|h <;> simp_all

/-- Safety on pairs alone makes both singleton supports of an AND span a biclique.
In particular each such AND can be assigned one star in a C4-free output graph. -/
def PairSafe {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) :=
  ∀ p g, C.gates[p]?=some g → g.op=GateOp.and → ∀ a b : Fin N,
    vl C.gates (two a b) (N+p)=true → G.Adj a b

theorem safe_rect {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (safe : PairSafe G C) (p i j : ℕ) (gate : C.gates[p]?=some ⟨GateOp.and,[i,j]⟩)
    {a b : Fin N} (left : atGate N p (vl C.gates (one a)) i=true)
    (right : atGate N p (vl C.gates (one b)) j=true) : G.Adj a b := by
  let x := two a b
  have ops : ∀ g∈C.gates, g.op=GateOp.and ∨ g.op=GateOp.or := fun g hg => (mono g hg).1
  have le (v : Fin N) (which : v=a ∨ v=b) : ∀ z, one v z=true → x z=true := by
    intro z hz; have vz : z=v := of_decide_eq_true hz; subst z; exact decide_eq_true which
  have iLt : i<N+p := by by_contra h; simp [atGate,h] at left
  have jLt : j<N+p := by by_contra h; simp [atGate,h] at right
  simp only [atGate,ite_eq_left iLt] at left
  simp only [atGate,ite_eq_left jLt] at right
  have iYes := monotone_wires C.gates ops (one a) x (le _ (Or.inl rfl)) i left
  have jYes := monotone_wires C.gates ops (one b) x (le _ (Or.inr rfl)) j right
  apply safe p _ gate rfl a b
  rw [raw_gate _ _ _ _ gate]
  change GateOp.and.eval ([i,j].map (atGate N p (vl C.gates x)))=true
  simp [GateOp.eval,atGate,iLt,jLt,iYes,jYes]

end PEqualNP.Outside.Rectangles624


namespace PEqualNP.Outside.Charging624

def Wide {V : Type*} (s : Finset V) := ∃ a∈s, ∃ b∈s, a≠b

private noncomputable def root {V : Type*} [LinearOrder V] [Inhabited V] (s : Finset V) : V :=
  if h : s.Nonempty then s.min' h else default

private theorem root_mem {V : Type*} [LinearOrder V] [Inhabited V] {s : Finset V}
    (h : s.Nonempty) : root s ∈ s := by
  simpa [root,h] using Finset.min'_mem s h

private theorem root_le {V : Type*} [LinearOrder V] [Inhabited V] {s : Finset V} {t : V}
    (h : t∈s) : root s ≤ t := by
  have ne : s.Nonempty := ⟨t,h⟩
  simpa [root,ne] using Finset.min'_le s t h

private theorem root_subset {V : Type*} [LinearOrder V] [Inhabited V] {s t : Finset V}
    (inc : s⊆t) (inside : root t∈s) : root t=root s :=
  le_antisymm (root_le (inc (root_mem ⟨_,inside⟩))) (root_le inside)

/-- In a table of singleton supports, an OR combining two earlier rows can introduce at
most one new marked vertex besides the representative inherited from its operands. The
same mark works simultaneously for every later root that contains this OR's support. -/
theorem exists_markers {V : Type*} [LinearOrder V] [Inhabited V]
    (S : ℕ → Finset V) (paid : Finset ℕ)
    (split : ∀ w, Wide (S w) → (∃ j<w, S w=S j) ∨ (w∈paid ∧
      ∃ k : ℕ×ℕ, k.1<w ∧ k.2<w ∧ S w = S k.1 ∪ S k.2)) :
    ∃ representative mark : ℕ → V, ∀ w t, t∈S w → t=representative w ∨
      ∃ j∈paid, S j ⊆ S w ∧ mark j=t := by
  classical
  let good (w : ℕ) (k : ℕ×ℕ) := k.1<w ∧ k.2<w ∧ S w = S k.1 ∪ S k.2
  let cut (w : ℕ) : ℕ×ℕ := if h : ∃ k, good w k then h.choose else (0,0)
  let anchor (w : ℕ) := root (S w)
  let mark (w : ℕ) := if anchor (cut w).1=anchor w then anchor (cut w).2 else anchor (cut w).1
  refine ⟨anchor, mark, ?_⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro t ht
    by_cases eq : t=anchor w
    · exact Or.inl eq
    apply Or.inr
    have hr : anchor w∈S w := root_mem ⟨t,ht⟩
    rcases split w ⟨t,ht,anchor w,hr,eq⟩ with ⟨j,lt,same⟩ | ⟨wp,ex⟩
    · rcases ih j lt t (same ▸ ht) with e | ⟨k,hk,sk,mk⟩
      · exact (eq (e.trans (congrArg root same).symm)).elim
      · exact ⟨k,hk,by simpa [same] using sk,mk⟩
    have goodCut : good w (cut w) := by
      have ex' : ∃ k, good w k := ex
      simp only [cut,dite_eq_left ex']; exact ex'.choose_spec
    obtain ⟨li,ri,union⟩ := goodCut
    have left : S (cut w).1 ⊆ S w := union ▸ Finset.subset_union_left
    have right : S (cut w).2 ⊆ S w := union ▸ Finset.subset_union_right
    have roots : anchor w = anchor (cut w).1 ∨ anchor w = anchor (cut w).2 := by
      rcases Finset.mem_union.mp (union ▸ hr) with hl | hr'
      · exact Or.inl (root_subset left hl)
      · exact Or.inr (root_subset right hr')
    rcases Finset.mem_union.mp (union ▸ ht) with htl | htr
    · rcases ih _ li t htl with eqt | ⟨j,hj,sj,mj⟩
      · have diff : anchor (cut w).1 ≠ anchor w := fun same => eq (eqt.trans same)
        exact ⟨w,wp,Finset.Subset.rfl,by simp [mark,diff,eqt]⟩
      · exact ⟨j,hj,sj.trans left,mj⟩
    · rcases ih _ ri t htr with eqt | ⟨j,hj,sj,mj⟩
      · have diff : anchor w ≠ anchor (cut w).2 := fun same => eq (eqt.trans same.symm)
        have same := (roots.resolve_right diff).symm
        exact ⟨w,wp,Finset.Subset.rfl,by simp [mark,same,eqt]⟩
      · exact ⟨j,hj,sj.trans right,mj⟩

/-- Consequently a single root has at most one more distinct leaves than the total
number of branching unions, even when nodes have repeated external readers. -/
theorem root_card_le {V : Type*} [LinearOrder V] [Inhabited V]
    (S : ℕ → Finset V) (paid : Finset ℕ)
    (split : ∀ w, Wide (S w) → (∃ j<w, S w=S j) ∨ (w∈paid ∧
      ∃ k : ℕ×ℕ, k.1<w ∧ k.2<w ∧ S w = S k.1 ∪ S k.2)) (w : ℕ) :
    (S w).card ≤ paid.card+1 := by
  classical
  obtain ⟨rep,mark,describe⟩ := exists_markers S paid split
  have subset : S w ⊆ insert (rep w) (paid.image mark) := by
    intro t ht
    rcases describe w t ht with rfl | ⟨j,hj,_,rfl⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)
  calc
    (S w).card ≤ (insert (rep w) (paid.image mark)).card := Finset.card_le_card subset
    _ ≤ (paid.image mark).card+1 := Finset.card_insert_le _ _
    _ ≤ paid.card+1 := Nat.add_le_add_right Finset.card_image_le 1

end PEqualNP.Outside.Charging624

namespace PEqualNP.Outside.Charging624
open Sym2

/-- Two distinct vertices have at most one common neighbor. -/
theorem same_center {V : Type*} (G : SimpleGraph V)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (S : Finset V) (wide : ∃ p ∈ S, ∃ q ∈ S, p ≠ q) {u v : V}
    (hu : ∀ t∈S, G.Adj u t) (hv : ∀ t∈S, G.Adj v t) : u=v := by
  obtain ⟨p,hp,q,hq,ne⟩ := wide
  exact (c4 u p v q (hu p hp) (hv p hp).symm (hv q hq) (hu q hq).symm).resolve_right ne

/-- A cover by stars may share OR gates. A wide OR gate whose singleton support
fits into a star determines its center uniquely, so its marked leaf can be counted once. -/
theorem count_stars {V A B : Type*} [Fintype V] [Inhabited V] (G : SimpleGraph V)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (ands : Finset A) (ors : Finset B) (center anchor : A → V)
    (leaves : A → Finset V) (mark : B → V) (support : B → Finset V)
    (neighbors : ∀ k ∈ ands, ∀ t∈leaves k, G.Adj (center k) t)
    (wide : ∀ j∈ors, ∃ p∈support j, ∃ q∈support j, p≠q)
    (trace : ∀ k∈ands, ∀ t∈leaves k, t=anchor k ∨
      ∃ j∈ors, support j ⊆ leaves k ∧ mark j=t)
    (cover : ∀ u v, G.Adj u v → ∃ k∈ands,
      (u=center k ∧ v∈leaves k) ∨ (v=center k ∧ u∈leaves k)) :
    G.edgeSet.ncard ≤ ands.card + ors.card := by
  classical
  let client (j : B) : V := if h : ∃ k∈ands, support j ⊆ leaves k
    then center h.choose else default
  have client_eq {j k} (hj : j∈ors) (hk : k∈ands) (sk : support j ⊆ leaves k) :
      client j = center k := by
    have e : ∃ k∈ands, support j ⊆ leaves k := ⟨k,hk,sk⟩
    simp only [client,dite_eq_left e]
    exact same_center G c4 (support j) (wide j hj)
      (fun t ht => neighbors _ e.choose_spec.1 t (e.choose_spec.2 ht))
      (fun t ht => neighbors k hk t (sk ht))
  let fromA := ands.image (fun k => s(center k, anchor k))
  let fromB := ors.image (fun j => s(client j, mark j))
  have covered {k t} (hk : k∈ands) (ht : t∈leaves k) :
      s(center k,t) ∈ fromA ∪ fromB := by
    rcases trace k hk t ht with rfl | ⟨j,hj,sk,eq⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,hk,rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,by rw [client_eq hj hk sk,eq]⟩)
  have inc : G.edgeFinset ⊆ fromA ∪ fromB := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨k,hk,uv|vu⟩ := cover u v (SimpleGraph.mem_edgeFinset.mp he)
      · rw [uv.1]
        exact covered hk uv.2
      · rw [Sym2.eq_swap,vu.1]
        exact covered hk vu.2
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  calc
    G.edgeFinset.card ≤ (fromA ∪ fromB).card := Finset.card_le_card inc
    _ ≤ fromA.card + fromB.card := Finset.card_union_le _ _
    _ ≤ ands.card + ors.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le

end PEqualNP.Outside.Charging624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

def wireSet (N : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun a => vl C.gates (one a) w=true)

@[simp] theorem wireSet_mem {N : ℕ} (C : Circuit) (w : ℕ) (a : Fin N) :
    a∈wireSet N C w ↔ vl C.gates (one a) w=true := by simp [wireSet]

def operand (N : ℕ) (C : Circuit) (p i : ℕ) : Finset (Fin N) :=
  if i<N+p then wireSet N C i else ∅

@[simp] theorem operand_mem {N : ℕ} (C : Circuit) (p i : ℕ) (a : Fin N) :
    a∈operand N C p i ↔ atGate N p (vl C.gates (one a)) i=true := by
  by_cases inside : i<N+p <;> simp [operand,atGate,inside]

private theorem or_support {N : ℕ} (C : Circuit) (p : ℕ) (ins : List ℕ)
    (gate : C.gates[p]?=some ⟨GateOp.or,ins⟩) :
    wireSet N C (N+p) = ins.toFinset.biUnion (operand N C p) := by
  ext a
  rw [wireSet_mem,raw_gate _ _ _ _ gate]
  simp only [Finset.mem_biUnion,List.mem_toFinset,operand_mem]
  constructor
  · intro yes
    obtain ⟨_,hi,h⟩ := List.any_eq_true.mp yes
    obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hi
    exact ⟨i,mem,h⟩
  · rintro ⟨i,mem,h⟩
    exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,mem,rfl⟩,h⟩

private theorem and_support {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (safe : PairSafe G C)
    (p : ℕ) (g : Gate) (gate : C.gates[p]?=some g) (op : g.op=GateOp.and) :
    wireSet N C (N+p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have eq : two a a = one a := by funext i; simp [two,one]
  have on : vl C.gates (two a a) (N+p)=true := by simpa only [eq] using (wireSet_mem _ _ _).mp ha
  exact G.loopless.irrefl _ (safe p g gate op a a on)

private theorem not_wide_empty {V : Type*} : ¬Wide (∅ : Finset V) := by simp [Wide]

theorem singleton_unions {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (safe : PairSafe G C) (paid : Finset ℕ)
    (pays : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ → Wide (wireSet N C (N+p)) → N+p∈paid)
    (w : ℕ) (wide : Wide (wireSet N C w)) :
    (∃ j<w, wireSet N C w=wireSet N C j) ∨ (w∈paid ∧
      ∃ k : ℕ×ℕ, k.1<w ∧ k.2<w ∧ wireSet N C w = wireSet N C k.1 ∪ wireSet N C k.2) := by
  by_cases raw : w<N
  · obtain ⟨a,ha,b,hb,ne⟩ := wide
    simp only [wireSet_mem,vl_input _ _ _ raw,one,decide_eq_true_eq] at ha hb
    exact (ne (ha.symm.trans hb)).elim
  obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
  cases gate : C.gates[p]? with
  | none =>
    have beyond := List.getElem?_eq_none_iff.mp gate
    obtain ⟨a,ha,_⟩ := wide
    have lit := (wireSet_mem _ _ _).mp ha
    rw [vl_beyond _ _ _ (by omega)] at lit
    contradiction
  | some g =>
    obtain ⟨h,eq⟩ := List.getElem?_eq_some_iff.mp gate
    have hg := mono g (eq ▸ List.getElem_mem h)
    obtain ⟨op,ins⟩ := g
    rcases hg.1 with hand|hor
    · exact (not_wide_empty ((and_support G C safe p _ gate hand) ▸ wide)).elim
    · change op=GateOp.or at hor
      subst op
      have all := or_support (N:=N) C p ins gate
      have len := hg.2
      cases ins with
      | nil => simp at all; exact (not_wide_empty (all ▸ wide)).elim
      | cons i rest =>
        cases rest with
        | nil =>
          simp at all
          by_cases inside : i<N+p
          · exact Or.inl ⟨i,inside,by simpa [operand,inside] using all⟩
          · simp [operand,inside] at all
            exact (not_wide_empty (all ▸ wide)).elim
        | cons j rest =>
          cases rest with
          | cons _ _ => simp at len
          | nil =>
            simp only [List.toFinset_cons,List.toFinset_nil,Finset.biUnion_insert,Finset.biUnion_empty,
              Finset.union_empty] at all
            by_cases ilt : i<N+p <;> by_cases jlt : j<N+p
            · exact Or.inr ⟨pays p _ gate wide,(i,j),ilt,jlt,by simpa [operand,ilt,jlt] using all⟩
            · exact Or.inl ⟨i,ilt,by simpa [operand,ilt,jlt] using all⟩
            · exact Or.inl ⟨j,jlt,by simpa [operand,ilt,jlt] using all⟩
            · simp [operand,ilt,jlt] at all
              exact (not_wide_empty (all ▸ wide)).elim

end PEqualNP.Outside.Rectangles624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

def Covers {N : ℕ} (C : Circuit) (p : ℕ) (a b : Fin N) :=
  ∃ i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ ∧ Crosses C.gates p i j a b

private theorem gate_star {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (safe : PairSafe G C)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    {p i j : ℕ} (gate : C.gates[p]?=some ⟨GateOp.and,[i,j]⟩)
    (pi : (operand N C p i).Nonempty) (pj : (operand N C p j).Nonempty) :
    ∃ c : Fin N, ∃ w : ℕ, (∀ t∈wireSet N C w, G.Adj c t) ∧ ∀ a b,
      Crosses C.gates p i j a b →
      (a=c ∧ b∈wireSet N C w) ∨ (b=c ∧ a∈wireSet N C w) := by
  classical
  have ilt : i<N+p := by
    by_contra hi
    simp [operand,hi] at pi
  have jlt : j<N+p := by
    by_contra hj
    simp [operand,hj] at pj
  have plit (a : Fin N) : a∈wireSet N C i ↔ atGate N p (vl C.gates (one a)) i=true := by
    simp [atGate,ilt]
  have qlit (a : Fin N) : a∈wireSet N C j ↔ atGate N p (vl C.gates (one a)) j=true := by
    simp [atGate,jlt]
  have edge {a b} (ha : a ∈ wireSet N C i) (hb : b ∈ wireSet N C j) : G.Adj a b :=
    safe_rect G C mono safe p i j gate ((plit _).mp ha) ((qlit _).mp hb)
  obtain ⟨a0,h0⟩ := pi
  obtain ⟨b0,k0⟩ := pj
  simp only [operand,ite_eq_left ilt] at h0
  simp only [operand,ite_eq_left jlt] at k0
  by_cases small : ∀ a∈wireSet N C i, a=a0
  · use a0,j
    refine ⟨fun _ ht => edge h0 ht,?_⟩
    rintro a b (⟨la,rb⟩|⟨lb,ra⟩)
    · exact Or.inl ⟨small a ((plit _).mpr la),(qlit _).mpr rb⟩
    · exact Or.inr ⟨small b ((plit _).mpr lb),(qlit _).mpr ra⟩
  · push Not at small
    obtain ⟨a1,h1,ne⟩ := small
    have uniq {b} (hb : b∈wireSet N C j) : b=b0 :=
      (c4 a1 b a0 b0 (edge h1 hb) (edge h0 hb).symm (edge h0 k0) (edge h1 k0).symm).resolve_left ne
    use b0,i
    refine ⟨fun _ ht => (edge ht k0).symm,?_⟩
    rintro a b (⟨la,rb⟩|⟨lb,ra⟩)
    · exact Or.inr ⟨uniq ((qlit _).mpr rb),(plit _).mpr la⟩
    · exact Or.inl ⟨uniq ((qlit _).mpr ra),(plit _).mpr lb⟩

private theorem star_at {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (safe : PairSafe G C)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    {p : ℕ} (somePair : ∃ a b : Fin N, Covers C p a b) :
    ∃ z : Fin N × ℕ, (∀ t∈wireSet N C z.2, G.Adj z.1 t) ∧ ∀ a b, Covers C p a b →
      (a=z.1 ∧ b∈wireSet N C z.2) ∨ (b=z.1 ∧ a∈wireSet N C z.2) := by
  obtain ⟨a,b,i,j,g,cross⟩ := somePair
  have nonempty : (operand N C p i).Nonempty ∧ (operand N C p j).Nonempty := by
    rcases cross with ⟨l,r⟩|⟨l,r⟩
    · exact ⟨⟨a,(operand_mem _ _ _ _).mpr l⟩,⟨b,(operand_mem _ _ _ _).mpr r⟩⟩
    · exact ⟨⟨b,(operand_mem _ _ _ _).mpr l⟩,⟨a,(operand_mem _ _ _ _).mpr r⟩⟩
  obtain ⟨c,w,near,cover⟩ := gate_star G C mono safe c4 g nonempty.1 nonempty.2
  use (c,w),near
  rintro u v ⟨k,l,g',cross'⟩
  have indices := congrArg Gate.inputs (Option.some.inj (g.symm.trans g'))
  simp only [List.cons.injEq, and_true] at indices
  obtain ⟨rfl,rfl⟩ := indices
  exact cover u v cross'

private theorem singleton_rejected {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔
      ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) (a : Fin N) :
    vl C.gates (one a) C.output=false := by
  cases yes : vl C.gates (one a) C.output with
  | false => rfl
  | true =>
    obtain ⟨u,v,adj,xu,xv⟩ := (sem _).mp yes
    have ueq : u=a := of_decide_eq_true xu
    have veq : v=a := of_decide_eq_true xv
    subst u; subst v
    exact (G.loopless.irrefl _ adj).elim

theorem safe_edge_count {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (safe : PairSafe G C)
    (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
    (A B : Finset ℕ)
    (andPaid : ∀ p g, C.gates[p]?=some g → g.op=GateOp.and → p∈A)
    (orPaid : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ → Wide (wireSet N C (N+p)) → p∈B) :
    G.edgeSet.ncard ≤ A.card+B.card := by
  classical
  let good (p : ℕ) := ∃ a b : Fin N, Covers C p a b
  let stars := A.filter good
  let contributing := B.filter (fun p => Wide (wireSet N C (N+p)))
  let paid := contributing.image (N+·)
  have pays (p ins) (gate : C.gates[p]?=some ⟨GateOp.or,ins⟩) (wide : Wide (wireSet N C (N+p))) :
      N+p∈paid := Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨orPaid p ins gate wide,wide⟩,rfl⟩
  obtain ⟨rep,mark,trace⟩ := exists_markers (wireSet N C) paid (singleton_unions G C mono safe paid pays)
  let z (p : ℕ) : Fin N × ℕ := if h : good p then (star_at G C mono safe c4 h).choose else default
  have spec (p : ℕ) (h : p∈stars) : (∀ t∈wireSet N C (z p).2, G.Adj (z p).1 t) ∧
      ∀ a b, Covers C p a b → (a=(z p).1 ∧ b∈wireSet N C (z p).2) ∨
        (b=(z p).1 ∧ a∈wireSet N C (z p).2) := by
    have hg : good p := (Finset.mem_filter.mp h).2
    simp only [z,dite_eq_left hg]
    exact (star_at G C mono safe c4 hg).choose_spec
  have cover (a b : Fin N) (adj : G.Adj a b) : ∃ p∈stars,
      (a=(z p).1 ∧ b∈wireSet N C (z p).2) ∨ (b=(z p).1 ∧ a∈wireSet N C (z p).2) := by
    have on : circuitFun N C (two a b)=true := (sem _).mpr ⟨a,b,adj,by simp [two],by simp [two]⟩
    obtain ⟨p,i,j,g,cross⟩ := pair_crosses_and C mono a b on (singleton_rejected G C sem a)
      (singleton_rejected G C sem b)
    have has : Covers C p a b := ⟨i,j,g,cross⟩
    have mem : p∈stars := Finset.mem_filter.mpr ⟨andPaid _ _ g rfl,⟨a,b,has⟩⟩
    exact ⟨p,mem,(spec p mem).2 a b has⟩
  have widePaid (w) (hw : w∈paid) : Wide (wireSet N C w) := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hp).2
  have result := count_stars G c4 stars paid (fun p => (z p).1) (fun p => rep (z p).2)
    (fun p => wireSet N C (z p).2) mark (wireSet N C)
    (fun p hp => (spec p hp).1) widePaid (fun p _ => trace (z p).2) cover
  exact result.trans (Nat.add_le_add (Finset.card_filter_le _ _)
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)))

end PEqualNP.Outside.Rectangles624
namespace PEqualNP.Outside.Charging624

/-- A zero certificate traces one predecessor at an AND and both at a narrow OR. -/
inductive KillStep (V : Type*) (w : ℕ)
  | empty
  | input (v : V)
  | copy (a : Fin w)
  | both (a b : Fin w)

def killLeaves {V : Type*} [DecidableEq V] (steps : ∀ w, KillStep V w) (w : ℕ) : Finset V :=
  match steps w with
  | .empty => ∅
  | .input v => {v}
  | .copy a => killLeaves steps a.val
  | .both a b => killLeaves steps a.val ∪ killLeaves steps b.val
termination_by w
decreasing_by all_goals exact Fin.isLt _

theorem kill_card {V : Type*} [LinearOrder V] [Inhabited V] (steps : ∀ w, KillStep V w)
    (paid : Finset ℕ) (pays : ∀ w a b, steps w=KillStep.both a b → w∈paid)
    (w : ℕ) : (killLeaves steps w).card ≤ paid.card+1 := by
  apply root_card_le (killLeaves steps) paid _ w
  intro u h
  rw [killLeaves] at h
  cases hs : steps u with
  | empty => simp [hs,Wide] at h
  | input v => simp [hs,Wide] at h
  | copy a =>
    exact Or.inl ⟨a.val,a.isLt,by rw [killLeaves,hs]⟩
  | both a b =>
    exact Or.inr ⟨pays u a b hs,(a.val,b.val),a.isLt,b.isLt,by rw [killLeaves,hs]⟩

def KillRule {V : Type*} (value : (V→Bool) → ℕ → Bool) (narrow : ℕ → Prop)
    (w : ℕ) : KillStep V w → Prop
  | .empty => ∀ x, value x w=false
  | .input v => ∀ x, x v=false → value x w=false
  | .copy a => narrow a.val ∧ ∀ x, value x a.val=false → value x w=false
  | .both a b => narrow a.val ∧ narrow b.val ∧
      ∀ x, value x a.val=false → value x b.val=false → value x w=false

theorem kill_sound {V : Type*} [DecidableEq V] (steps : ∀ w, KillStep V w)
    (value : (V→Bool) → ℕ → Bool) (narrow : ℕ → Prop)
    (rule : ∀ w, narrow w → KillRule value narrow w (steps w)) (w : ℕ) (wn : narrow w)
    (x : V→Bool) (off : ∀ t∈killLeaves steps w, x t=false) : value x w=false := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have good := rule w wn
    rw [killLeaves] at off
    cases hs : steps w with
    | empty => rw [hs] at good; exact good x
    | input v =>
      rw [hs] at good off
      exact good x (off v (by simp))
    | copy a =>
      rw [hs] at good off
      exact good.2 x (ih a.val a.isLt good.1 off)
    | both a b =>
      rw [hs] at good off
      exact good.2.2 x (ih a.val a.isLt good.1 (fun _ ht => off _ (Finset.mem_union_left _ ht)))
        (ih b.val b.isLt good.2.1 (fun _ ht => off _ (Finset.mem_union_right _ ht)))

end PEqualNP.Outside.Charging624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

def complementRow {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun i => decide (i∉S)

private def TraceLabels {N : ℕ} (C : Circuit) (negative : Fin N→Bool) (w : ℕ) :
    KillStep (Fin N) w → Prop
  | .empty => wireSet N C w = ∅
  | .input i => wireSet N C w ⊆ {i}
  | .copy a => vl C.gates negative a.val=false ∧ wireSet N C w ⊆ wireSet N C a.val
  | .both a b => vl C.gates negative a.val=false ∧ vl C.gates negative b.val=false ∧
      wireSet N C w ⊆ wireSet N C a.val ∪ wireSet N C b.val

private theorem label_step {N : ℕ} (C : Circuit) (mono : Monotone2 C)
    (negative : Fin N→Bool) (paid : Finset ℕ)
    (pays : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ → Wide (wireSet N C (N+p)) →
      vl C.gates negative (N+p)=false → N+p∈paid)
    (w : ℕ) (off : vl C.gates negative w=false) : ∃ s : KillStep (Fin N) w,
      TraceLabels C negative w s ∧ ∀ a b, s=.both a b → w∈paid := by
  classical
  by_cases em : wireSet N C w=∅
  · exact ⟨.empty,em,by simp⟩
  obtain ⟨i0,hi⟩ := Finset.nonempty_iff_ne_empty.mpr em
  by_cases wide : Wide (wireSet N C w)
  swap
  · refine ⟨.input i0,?_,by simp⟩
    intro t ht
    exact Finset.mem_singleton.mpr (by
      by_contra ne
      exact wide ⟨t,ht,i0,hi,ne⟩)
  by_cases raw : w<N
  · obtain ⟨a,ha,b,hb,ne⟩ := wide
    simp only [wireSet_mem,vl_input _ _ _ raw,one,decide_eq_true_eq] at ha hb
    exact (ne (ha.symm.trans hb)).elim
  obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
  cases gate : C.gates[p]? with
  | none =>
    have beyond := List.getElem?_eq_none_iff.mp gate
    have lit := (wireSet_mem _ _ _).mp hi
    rw [vl_beyond _ _ _ (by omega)] at lit
    contradiction
  | some g =>
    have h := List.getElem?_eq_some_iff.mp gate
    obtain ⟨op,ins⟩ := g
    have facts := mono _ (h.2 ▸ List.getElem_mem h.1)
    rcases facts.1 with isAnd|isOr
    · change op=GateOp.and at isAnd
      subst op
      have allLit {a : Fin N} (on : a∈wireSet N C (N+p)) : ∀ j∈ins,
          atGate N p (vl C.gates (one a)) j=true := by
        have yes := (wireSet_mem _ _ _).mp on
        rw [raw_gate _ _ _ _ gate] at yes
        intro j hj
        exact List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨j,hj,rfl⟩)
      have existsOff : ∃ j∈ins, atGate N p (vl C.gates negative) j=false := by
        by_contra! no
        have yes : vl C.gates negative (N+p)=true := by
          rw [raw_gate _ _ _ _ gate]
          apply List.all_eq_true.mpr
          rintro b hb
          obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
          simpa using no j hj
        simp_all
      obtain ⟨j,hj,unlit⟩ := existsOff
      have valid : j<N+p := by
        by_contra inv
        simpa [atGate,inv] using allLit hi j hj
      refine ⟨.copy ⟨j,valid⟩,⟨by simpa [atGate,valid] using unlit,?_⟩,by simp⟩
      intro a yes
      exact (wireSet_mem _ _ _).mpr (by simpa [atGate,valid] using allLit yes j hj)
    · change op=GateOp.or at isOr
      subst op
      have union := or_support (N:=N) C p ins gate
      have childDark {j : ℕ} (hmem : j∈ins) (valid : j<N+p) : vl C.gates negative j=false := by
        cases eq : vl C.gates negative j with
        | false => rfl
        | true =>
          have yes : vl C.gates negative (N+p)=true := by
            rw [raw_gate _ _ _ _ gate]
            exact List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨j,hmem,rfl⟩,by simpa [atGate,valid] using eq⟩
          simp_all
      have len := facts.2
      cases ins with
      | nil => simp at union; exact (em union).elim
      | cons i rest =>
        cases rest with
        | nil =>
          by_cases ilt : i<N+p
          · exact ⟨.copy ⟨i,ilt⟩,⟨childDark (by simp) ilt,by
              have eq : wireSet N C (N+p) = wireSet N C i := by simpa [operand,ilt] using union
              exact eq.subset⟩,by simp⟩
          · simp [operand,ilt] at union
            exact (em union).elim
        | cons j rest =>
          cases rest with
          | cons _ _ => simp at len
          | nil =>
            by_cases ilt : i<N+p <;> by_cases jlt : j<N+p
            · exact ⟨.both ⟨i,ilt⟩ ⟨j,jlt⟩,⟨childDark (by simp) ilt,childDark (by simp) jlt,by
                have eq : wireSet N C (N+p)=wireSet N C i ∪ wireSet N C j := by
                  simpa [operand,ilt,jlt] using union
                exact eq.subset⟩,fun _ _ _ => pays p _ gate wide off⟩
            · exact ⟨.copy ⟨i,ilt⟩,⟨childDark (by simp) ilt,by
                have eq : wireSet N C (N+p)=wireSet N C i := by simpa [operand,ilt,jlt] using union
                exact eq.subset⟩,by simp⟩
            · exact ⟨.copy ⟨j,jlt⟩,⟨childDark (by simp) jlt,by
                have eq : wireSet N C (N+p)=wireSet N C j := by simpa [operand,ilt,jlt] using union
                exact eq.subset⟩,by simp⟩
            · simp [operand,ilt,jlt] at union; exact (em union).elim

theorem local_or_lower {N : ℕ} [Inhabited (Fin N)] (C : Circuit) (mono : Monotone2 C)
    (negative : Fin N→Bool) (paid : Finset ℕ)
    (pays : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ → Wide (wireSet N C (N+p)) →
      vl C.gates negative (N+p)=false → N+p∈paid) (w : ℕ) (off : vl C.gates negative w=false) :
    (wireSet N C w).card ≤ paid.card+1 := by
  classical
  let choose (w : ℕ) : KillStep (Fin N) w := if h : vl C.gates negative w=false then
    (label_step C mono negative paid pays w h).choose else .empty
  have rule (w : ℕ) (dark : vl C.gates negative w=false) : TraceLabels C negative w (choose w) := by
    simp only [choose,dite_eq_left dark]
    exact (label_step C mono negative paid pays w dark).choose_spec.1
  have charges (w : ℕ) (a b : Fin w) (eq : choose w=.both a b) : w∈paid := by
    by_cases h : vl C.gates negative w=false
    · simp only [choose,dite_eq_left h] at eq
      exact (label_step C mono negative paid pays w h).choose_spec.2 a b eq
    · simp [choose,h] at eq
  have bound (v : ℕ) (dark : vl C.gates negative v=false) : wireSet N C v ⊆ killLeaves choose v := by
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      have r := rule v dark
      rw [killLeaves]
      cases step : choose v with
      | empty => rw [step] at r; exact (show wireSet N C v=∅ from r).subset
      | input i => rw [step] at r; exact r
      | copy a => rw [step] at r; exact r.2.trans (ih _ a.isLt r.1)
      | both a b =>
        rw [step] at r
        exact r.2.2.trans (Finset.union_subset_union (ih _ a.isLt r.1) (ih _ b.isLt r.2.1))
  exact (Finset.card_le_card (bound w off)).trans (kill_card choose paid charges w)

end PEqualNP.Outside.Rectangles624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

noncomputable def orIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun p => ∃ g : Gate, C.gates[p]?=some g ∧ g.op=GateOp.or)

/-- Joint Boolean sums with pairwise intersections of size at most one require their
individual OR-gate costs additively, even in a circuit containing arbitrary AND gates. -/
theorem linear_family_or_lower {N : ℕ} [Inhabited (Fin N)] {I : Type*}
    (C : Circuit) (mono : Monotone2 C) (lines : Finset I) (S : I→Finset (Fin N)) (out : I→ℕ)
    (linear : ∀ i∈lines, ∀ j∈lines, i≠j → ∀ a∈S i, a∈S j → ∀ b∈S i, b∈S j → a=b)
    (zero : ∀ i∈lines, vl C.gates (complementRow (S i)) (out i)=false)
    (positive : ∀ i∈lines, ∀ a∈S i, vl C.gates (one a) (out i)=true) :
    ∑ i∈lines, (S i).card ≤ (orIndices C).card + lines.card := by
  classical
  let O := (orIndices C).image (N+·)
  let owned (i : I) := O.filter (fun w => Wide (wireSet N C w) ∧ vl C.gates (complementRow (S i)) w=false)
  have row (i : I) (hi : i∈lines) : (S i).card ≤ (owned i).card+1 := by
    have light : S i ⊆ wireSet N C (out i) := fun a ha => (wireSet_mem _ _ _).mpr (positive i hi a ha)
    apply (Finset.card_le_card light).trans
    apply local_or_lower C mono _ (owned i) _ (out i) (zero i hi)
    intro p ins gate wide neg
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨p,?_,rfl⟩,wide,neg⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp gate).1,⟨_,gate,rfl⟩⟩
  have inside {i w} (hw : w∈owned i) : wireSet N C w ⊆ S i := by
    intro a ha
    by_contra no
    have inc (j : Fin N) (hj : one a j=true) : complementRow (S i) j=true := by
      have eq : j=a := of_decide_eq_true hj
      subst j
      exact decide_eq_true no
    have on := monotone_wires C.gates (fun g hg => (mono g hg).1) (one a) _ inc w
      ((wireSet_mem _ _ _).mp ha)
    have off := (Finset.mem_filter.mp hw).2.2
    simp_all
  have pair : (lines : Set I).PairwiseDisjoint owned := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro w wi wj
    obtain ⟨a,ha,b,hb,ab⟩ := (Finset.mem_filter.mp wi).2.1
    exact ab (linear i hi j hj ne a (inside wi ha) (inside wj ha) b (inside wi hb) (inside wj hb))
  have covered : lines.biUnion owned ⊆ O := by
    intro w hw
    obtain ⟨i,_,mem⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp mem).1
  have use : ∑ i∈lines, (owned i).card ≤ (orIndices C).card := by
    rw [← Finset.card_biUnion pair]
    exact (Finset.card_le_card covered).trans Finset.card_image_le
  have total := Finset.sum_le_sum row
  rw [Finset.sum_add_distrib] at total
  simpa using total.trans (Nat.add_le_add_right use _)

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Transpose602

/-- ANDs have zero charge and each OR costs one. The base can contain input signals
or scalars already provided by an earlier computation. -/
inductive Pool {X : Type*} (base : Set (Set X)) : ℕ → Set (Set X) → Prop
  | start : Pool base 0 base
  | mul {n S a b} : Pool base n S → a∈S → b∈S → Pool base n (insert (a∩b) S)
  | add {n S a b} : Pool base n S → a∈S → b∈S → Pool base (n+1) (insert (a∪b) S)

private theorem pool_base {X : Type*} {base S : Set (Set X)} {n} (h : Pool base n S) : base⊆S := by
  induction h with
  | start => exact Set.Subset.rfl
  | mul _ _ _ ih | add _ _ _ ih => exact ih.trans (Set.subset_insert _ _)

structure Front (X : Type*) where
  keys : Finset ℕ
  weight : ℕ → Set X

def Ready {X : Type*} (S : Set (Set X)) (F : Front X) := ∀ j∈F.keys, F.weight j∈S

def mix {X U : Type*} (F : Front X) (P : ℕ → U → Set X) (u : U) (x : X) :=
  ∃ j∈F.keys, x∈P j u ∧ x∈F.weight j

private def push {X : Type*} (F : Front X) (j : ℕ) (s : Set X) : Front X :=
  ⟨insert j F.keys,Function.update F.weight j (if j∈F.keys then s∪F.weight j else s)⟩

private theorem push_mix {X U : Type*} (F : Front X) (P : ℕ → U → Set X)
    (j : ℕ) (s : Set X) (u : U) (x : X) :
    mix (push F j s) P u x ↔ mix F P u x ∨ x∈P j u ∧ x∈s := by
  constructor
  · rintro ⟨k,hk,on,wt⟩
    by_cases eq : k=j
    · subst k
      by_cases mem : j∈F.keys
      · simp [push,mem] at wt
        rcases wt with h|h
        · exact Or.inr ⟨on,h⟩
        · exact Or.inl ⟨j,mem,on,h⟩
      · exact Or.inr ⟨on,by simpa [push,mem] using wt⟩
    · exact Or.inl ⟨k,(Finset.mem_insert.mp hk).resolve_left eq,on,by
        simpa [push,Function.update_of_ne eq] using wt⟩
  · rintro (⟨k,hk,on,wt⟩|⟨on,wt⟩)
    · refine ⟨k,Finset.mem_insert_of_mem hk,on,?_⟩
      by_cases eq : k=j
      · subst k; simpa [push,hk] using (Or.inr wt : x∈s ∨ x∈F.weight j)
      · simpa [push,Function.update_of_ne eq] using wt
    · exact ⟨j,Finset.mem_insert_self _ _,on,by by_cases mem : j∈F.keys <;> simp [push,mem,wt]⟩

private theorem push_ready {X : Type*} {base S : Set (Set X)} {n : ℕ}
    (pool : Pool base n S) (F : Front X) (ready : Ready S F) (j : ℕ) (s : Set X) (hs : s∈S) :
    ∃ m T, Pool base m T ∧ S⊆T ∧ Ready T (push F j s) ∧
      m+(push F j s).keys.card=n+F.keys.card+1 := by
  by_cases mem : j∈F.keys
  · refine ⟨n+1,insert (s∪F.weight j) S,.add pool hs (ready j mem),Set.subset_insert _ _,?_,?_⟩
    · intro k hk
      by_cases eq : k=j
      · subst k; simp [push,mem]
      · apply Set.mem_insert_of_mem
        simpa [push,Function.update_of_ne eq] using ready k ((Finset.mem_insert.mp hk).resolve_left eq)
    · simp [push,mem]; omega
  · refine ⟨n,S,pool,Set.Subset.rfl,?_,?_⟩
    · intro k hk
      by_cases eq : k=j
      · subst k; simpa [push,mem] using hs
      · simpa [push,Function.update_of_ne eq] using ready k ((Finset.mem_insert.mp hk).resolve_left eq)
    · simp [push,Finset.card_insert_of_notMem mem]; omega

private def drop {X : Type*} (F : Front X) (j : ℕ) : Front X := ⟨F.keys.erase j,F.weight⟩

private theorem contributions {X U : Type*} {base S : Set (Set X)} {n : ℕ}
    (pool : Pool base n S) (F : Front X) (ready : Ready S F) (P : ℕ→U→Set X)
    (coeff : Set X) (hc : coeff∈S) (terms : List (ℕ×Set X))
    (supply : ∀ t∈terms, t.2∈base) :
    ∃ m T G, Pool base m T ∧ S⊆T ∧ Ready T G ∧
      m+G.keys.card=n+F.keys.card+terms.length ∧
      (∀ j∈G.keys, j∈F.keys ∨ ∃ t∈terms, j=t.1) ∧
      ∀ u x, mix G P u x ↔ mix F P u x ∨
        ∃ t∈terms, x∈P t.1 u ∧ x∈t.2 ∧ x∈coeff := by
  induction terms generalizing n S F with
  | nil => exact ⟨n,S,F,pool,Set.Subset.rfl,ready,by simp,by simp,by simp⟩
  | cons t rest ih =>
    let U₀ := insert (t.2∩coeff) S
    have inc : S⊆U₀ := Set.subset_insert _ _
    have pool' : Pool base n U₀ := .mul pool (pool_base pool (supply t (by simp))) hc
    obtain ⟨n',S',pn,inc',rn,cost⟩ := push_ready pool' F (fun j hj => inc (ready j hj)) t.1
      (t.2∩coeff) (Set.mem_insert _ _)
    obtain ⟨m,T,G,pt,iT,rT,cT,kT,eT⟩ := ih pn _ rn (inc' (inc hc))
      (fun q hq => supply q (List.mem_cons_of_mem _ hq))
    refine ⟨m,T,G,pt,inc.trans (inc'.trans iT),rT,?_,?_,?_⟩
    · simp only [List.length_cons]; omega
    · intro j hj
      rcases kT j hj with old|⟨q,qm,eq⟩
      · rcases Finset.mem_insert.mp old with eq|held
        · exact Or.inr ⟨t,by simp,eq⟩
        · exact Or.inl held
      · exact Or.inr ⟨q,List.mem_cons_of_mem _ qm,eq⟩
    · intro u x
      rw [eT,push_mix]
      simp only [Set.mem_inter_iff,List.mem_cons]
      constructor
      · rintro ((h|h)|⟨q,hq,z⟩)
        · exact Or.inl h
        · exact Or.inr ⟨t,Or.inl rfl,h⟩
        · exact Or.inr ⟨q,Or.inr hq,z⟩
      · rintro (h|⟨q,rfl|qm,z⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr z)
        · exact Or.inr ⟨q,qm,z⟩

end PEqualNP.Outside.Transpose602

namespace PEqualNP.Outside.Transpose602

private theorem mix_drop {X U : Type*} (F : Front X) (P : ℕ→U→Set X) (w : ℕ) (held : w∈F.keys)
    (u : U) (x : X) : mix F P u x ↔ mix (drop F w) P u x ∨ x∈P w u ∧ x∈F.weight w := by
  constructor
  · rintro ⟨j,hj,pj,cj⟩
    by_cases eq : j=w
    · subst j; exact Or.inr ⟨pj,cj⟩
    · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨eq,hj⟩,pj,cj⟩
  · rintro (⟨j,hj,pj,cj⟩|⟨pw,cw⟩)
    · exact ⟨j,Finset.mem_of_mem_erase hj,pj,cj⟩
    · exact ⟨w,held,pw,cw⟩

/-- Transpose a finite acyclic linear system over the Boolean semiring. Weight
sets are arbitrary truth sets. The reverse construction counts an OR exactly
when two partial contributions reach the same frontier key. -/
theorem reverse_system {X U : Type*} (base : Set (Set X)) (P : ℕ→U→Set X)
    (N : ℕ) (terms : ℕ→List (ℕ×Set X)) (budget : ℕ→ℕ) (t : ℕ)
    (src : ∀ k<t, ∀ z∈terms k, z.1<N+k ∧ z.2∈base)
    (size : ∀ k<t, (terms k).length≤budget k+1)
    (eq : ∀ k<t, ∀ u x, x∈P (N+k) u ↔ ∃ z∈terms k, x∈P z.1 u ∧ x∈z.2)
    {n S} (pool : Pool base n S) (F : Front X) (ready : Ready S F)
    (valid : ∀ w∈F.keys, w<N+t) :
    ∃ m T G, Pool base m T ∧ Ready T G ∧ (∀ w∈G.keys,w<N) ∧
      m+G.keys.card≤n+F.keys.card+∑ k∈Finset.range t, budget k ∧
      ∀ u x, mix G P u x ↔ mix F P u x := by
  induction t generalizing n S F with
  | zero => exact ⟨n,S,F,pool,ready,by simpa using valid,by simp,by simp⟩
  | succ k ih =>
    have psrc := fun j (h : j<k) => src j (Nat.lt_succ_of_lt h)
    have psz := fun j (h : j<k) => size j (Nat.lt_succ_of_lt h)
    have peq := fun j (h : j<k) => eq j (Nat.lt_succ_of_lt h)
    by_cases live : N+k∈F.keys
    · let w := N+k
      let F₀ := drop F w
      have ready₀ : Ready S F₀ := fun j hj => ready j (Finset.mem_of_mem_erase hj)
      obtain ⟨nn,SS,FF,pn,_,rn,cost,keys,sem⟩ := contributions pool F₀ ready₀ P
        (F.weight w) (ready w live) (terms k) (fun z hz => (src k (Nat.lt_succ_self _) z hz).2)
      have bound (j : ℕ) (hj : j∈FF.keys) : j<N+k := by
        rcases keys j hj with old|⟨z,hz,rfl⟩
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp old
          have hi := valid j mem
          dsimp [w] at ne
          omega
        · exact (src k (Nat.lt_succ_self _) z hz).1
      obtain ⟨m,T,G,pm,rg,raw,acc,doneSem⟩ := ih psrc psz peq pn FF rn bound
      refine ⟨m,T,G,pm,rg,raw,?_,?_⟩
      · have erase : F₀.keys.card+1=F.keys.card := Finset.card_erase_add_one live
        have span := size k (Nat.lt_succ_self _)
        rw [Finset.sum_range_succ]
        omega
      · intro u x
        rw [doneSem,sem,mix_drop F P w live]
        apply or_congr_right
        change (∃ z∈terms k, x∈P z.1 u ∧ x∈z.2 ∧ x∈F.weight w) ↔ x∈P (N+k) u ∧ x∈F.weight w
        rw [eq k (Nat.lt_succ_self _)]
        constructor
        · rintro ⟨z,hz,zp,zq,fw⟩
          exact ⟨⟨z,hz,zp,zq⟩,fw⟩
        · rintro ⟨⟨z,hz,zp,zq⟩,fw⟩
          exact ⟨z,hz,zp,zq,fw⟩
    · have bound (j : ℕ) (hj : j∈F.keys) : j<N+k := by
        have hi := valid j hj
        have ne : j≠N+k := fun h => live (h ▸ hj)
        omega
      obtain ⟨m,T,G,pm,rg,raw,acc,sem⟩ := ih psrc psz peq pool F ready bound
      refine ⟨m,T,G,pm,rg,raw,?_,sem⟩
      rw [Finset.sum_range_succ]
      omega

end PEqualNP.Outside.Transpose602

namespace PEqualNP.Outside.Transpose602

theorem pool_extend {X : Type*} {base middle target : Set (Set X)} {n m : ℕ}
    (before : Pool base n middle) (after : Pool middle m target) : Pool base (n+m) target := by
  induction after with
  | start => simpa using before
  | mul _ ha hb ih => exact .mul ih ha hb
  | add _ ha hb ih => simpa [Nat.add_assoc] using Pool.add ih ha hb

theorem pool_contains {X : Type*} {a b : Set (Set X)} {n : ℕ} (h : Pool a n b) : a⊆b := pool_base h

end PEqualNP.Outside.Transpose602

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

def inputPool (N : ℕ) : Set (Set (Fin N→Bool)) :=
  {s | s=Set.univ ∨ s=∅ ∨ ∃ i : Fin N, s={x | x i=true}}

private theorem append_value {N : ℕ} (g h : List Gate) (x : Fin N→Bool) (i : ℕ)
    (old : i<N+g.length) : vl (g++h) x i=vl g x i := by
  unfold vl
  rw [wiresFrom_append,getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; simpa)]

private theorem or_snoc (gs : List Gate) (g : Gate) [Decidable (g.op=GateOp.or)] :
    orIndices ⟨gs++[g],0⟩=if g.op=GateOp.or then insert gs.length (orIndices ⟨gs,0⟩)
      else orIndices ⟨gs,0⟩ := by
  classical
  ext p
  by_cases low : p<gs.length
  · have ne : p≠gs.length := Nat.ne_of_lt low
    have smaller : p<gs.length+1 := by omega
    by_cases op : g.op=GateOp.or <;>
      simp [orIndices,low,smaller,op,ne]
  by_cases eq : p=gs.length
  · subst p
    by_cases op : g.op=GateOp.or <;> simp [orIndices,op]
  · have notin : ¬p<gs.length+1 := by omega
    by_cases op : g.op=GateOp.or <;> simp [orIndices,op,low,eq,notin]

private def Implements {N : ℕ} (gs : List Gate) (S : Set (Set (Fin N→Bool))) :=
  ∀ s∈S, ∃ i<N+gs.length, ∀ x, vl gs x i=true ↔ x∈s

/-- Convert Boolean set-union/intersection steps into physical binary AND/OR gates.
The two free Boolean constants use AND gates, hence no new OR charge. -/
theorem pool_physical {N : ℕ} {n S} (pool : Pool (inputPool N) n S) :
    ∃ gs : List Gate, Monotone2 ⟨gs,0⟩ ∧ (orIndices ⟨gs,0⟩).card≤n ∧ Implements gs S := by
  classical
  induction pool with
  | start =>
    let gs : List Gate := [⟨.and,[]⟩,⟨.and,[N+1]⟩]
    have truth (x : Fin N→Bool) : vl gs x N=true := by
      have v := raw_gate gs x 0 ⟨.and,[]⟩ (by simp [gs])
      simpa [GateOp.eval] using v
    have zero (x : Fin N→Bool) : vl gs x (N+1)=false := by
      have v := raw_gate gs x 1 ⟨.and,[N+1]⟩ (by simp [gs])
      simpa [GateOp.eval,atGate] using v
    refine ⟨gs,?_,?_,?_⟩
    · intro g hg
      simp only [gs,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl|rfl <;> simp
    · have empty : orIndices ⟨gs,0⟩=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨inside,g,hg,op⟩ := Finset.mem_filter.mp hp
        have some := List.getElem?_eq_some_iff.mp hg
        have mem := some.2 ▸ List.getElem_mem some.1
        change g∈gs at mem
        simp only [gs,List.mem_cons,List.not_mem_nil,or_false] at mem
        rcases mem with rfl|rfl <;> cases op
      simp [empty]
    · rintro s (rfl|rfl|⟨i,rfl⟩)
      · exact ⟨N,by simp [gs],by simp [truth]⟩
      · exact ⟨N+1,by simp [gs],by simp [zero]⟩
      · exact ⟨i.val,by simp [gs]; omega,fun x => by rw [vl_input gs x i.val i.isLt]; simp⟩
  | @mul n S a b before ha hb ih =>
      obtain ⟨gs,mono,nor,real⟩ := ih
      obtain ⟨i,il,ai⟩ := real a ha
      obtain ⟨j,jl,bj⟩ := real b hb
      let g : Gate := ⟨.and,[i,j]⟩
      refine ⟨gs++[g],?_,?_,?_⟩
      · intro h hh
        rcases List.mem_append.mp hh with orig|last
        · exact mono h orig
        · obtain rfl : h=g := by simpa using last
          simp [g]
      · simpa [or_snoc,g] using nor
      · rintro s (rfl|old)
        · refine ⟨N+gs.length,by simp,?_⟩
          intro x
          rw [raw_gate (gs++[g]) x gs.length g (by simp)]
          simp [g,GateOp.eval,atGate,il,jl,append_value gs _ x i il,append_value gs _ x j jl,ai,bj]
        · obtain ⟨w,wl,ws⟩ := real s old
          exact ⟨w,by simp; omega,fun x => by rw [append_value gs _ x w wl]; exact ws x⟩
  | @add n S a b before ha hb ih =>
      obtain ⟨gs,mono,nor,real⟩ := ih
      obtain ⟨i,il,ai⟩ := real a ha
      obtain ⟨j,jl,bj⟩ := real b hb
      let g : Gate := ⟨.or,[i,j]⟩
      refine ⟨gs++[g],?_,?_,?_⟩
      · intro h hh
        rcases List.mem_append.mp hh with orig|last
        · exact mono h orig
        · obtain rfl : h=g := by simpa using last
          simp [g]
      · rw [or_snoc,ite_eq_left (show g.op=GateOp.or from rfl)]
        exact (Finset.card_insert_le gs.length (orIndices ⟨gs,0⟩)).trans (Nat.add_le_add_right nor 1)
      · rintro s (rfl|old)
        · refine ⟨N+gs.length,by simp,?_⟩
          intro x
          rw [raw_gate (gs++[g]) x gs.length g (by simp)]
          simp [g,GateOp.eval,atGate,il,jl,append_value gs _ x i il,append_value gs _ x j jl,ai,bj]
        · obtain ⟨w,wl,ws⟩ := real s old
          exact ⟨w,by simp; omega,fun x => by rw [append_value gs _ x w wl]; exact ws x⟩

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

/-- A linear family of Boolean coefficient wires costs at least one OR per
incidence after allowing an arbitrary scalar circuit and arbitrary sharing. -/
theorem linear_network_cost {N : ℕ} [Inhabited (Fin N)] (base : Set (Set (Fin N→Bool)))
    (t cost : ℕ) (scalar : Pool (inputPool N) cost base)
    (P : ℕ→Fin N→Set (Fin N→Bool)) (inputs : ∀ i<N, ∀ u, P i u=if i=u.val then Set.univ else ∅)
    (terms : ℕ→List (ℕ×Set (Fin N→Bool))) (budget : ℕ→ℕ)
    (src : ∀ k<t, ∀ z∈terms k, z.1<N+k ∧ z.2∈base)
    (size : ∀ k<t, (terms k).length≤budget k+1)
    (eq : ∀ k<t, ∀ u x, x∈P (N+k) u ↔ ∃ z∈terms k, x∈P z.1 u ∧ x∈z.2)
    (output : ℕ) (outputValid : output<N+t) (L : Finset (Fin N)) (D : Fin N→Finset (Fin N))
    (linear : ∀ i∈L, ∀ j∈L, i≠j → ∀ a∈D i, a∈D j → ∀ b∈D i, b∈D j → a=b)
    (positive : ∀ u∈L, ∀ a∈D u, one a∈P output u)
    (negative : ∀ u∈L, complementRow (D u)∉P output u) (nonempty : ∀ u∈L, (D u).Nonempty) :
    ∑ u∈L, (D u).card ≤ cost+(∑ k∈Finset.range t, budget k)+1 := by
  classical
  let F : Front (Fin N→Bool) := ⟨{output},fun _ => Set.univ⟩
  have ready : Ready base F := fun _ _ => pool_contains scalar (Or.inl rfl)
  have good : ∀ w∈F.keys, w<N+t := by simpa [F] using outputValid
  obtain ⟨m,T,G,pool,rg,raw,costG,effects⟩ := reverse_system base P N terms budget t src size eq
    Pool.start F ready good
  have eqG (u : Fin N) (x : Fin N→Bool) : x∈P output u ↔ u.val∈G.keys ∧ x∈G.weight u.val := by
    have oneKey : mix F P u x ↔ x∈P output u := by simp [mix,F]
    rw [←oneKey,←effects]
    constructor
    · rintro ⟨j,hj,jp,jq⟩
      rw [inputs j (raw j hj) u] at jp
      by_cases isU : j=u.val
      · simpa [isU] using And.intro hj jq
      · simp [isU] at jp
    · rintro ⟨inG,hit⟩
      exact ⟨u.val,inG,by simp [inputs u.val u.isLt u],hit⟩
  have has (u) (hu : u∈L) : u.val∈G.keys := by
    obtain ⟨a,ha⟩ := nonempty u hu
    exact ((eqG u (one a)).mp (positive u hu a ha)).1
  have rawCount : L.card≤G.keys.card := by
    have inc : L.image Fin.val ⊆ G.keys := by
      intro i hi
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
      exact has u hu
    simpa [Finset.card_image_of_injective _ Fin.val_injective] using Finset.card_le_card inc
  obtain ⟨gs,mono,paid,impl⟩ := pool_physical (pool_extend scalar pool)
  let out u := if h : u∈L then (impl (G.weight (u : Fin N).val) (rg u.val (has u h))).choose else 0
  have eval (u) (hu : u∈L) (x : Fin N→Bool) : vl gs x (out u)=true ↔ x∈P output u := by
    have rule := (impl (G.weight u.val) (rg u.val (has u hu))).choose_spec.2 x
    simp only [out,dite_eq_left hu]
    exact rule.trans ⟨fun on => (eqG u x).mpr ⟨has u hu,on⟩,fun on => ((eqG u x).mp on).2⟩
  have counts := linear_family_or_lower ⟨gs,0⟩ mono L D out linear (by
    intro u hu
    cases h : vl gs (complementRow (D u)) (out u) with
    | false => rfl
    | true => exact (negative u hu ((eval u hu _).mp h)).elim)
    (fun u hu a ha => (eval u hu _).mpr (positive u hu a ha))
  simp only [F,Finset.card_singleton,Nat.zero_add] at costG
  omega

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

/-- An individual binary AND separates a pair of rejecting rows in opposite input slots. -/
private def Flip (x y z : ℕ→Bool) (i j : ℕ) :=
  x i=true ∧ x j=true ∧ y i=false ∧ z i=true ∧ y j=true ∧ z j=false

private theorem local_flip (g : Gate) (op : g.op=GateOp.and ∨ g.op=GateOp.or)
    (len : g.inputs.length≤2) (x y z : ℕ→Bool)
    (one : g.op.eval (g.inputs.map x)=true)
    (noneY : g.op.eval (g.inputs.map y)=false) (noneZ : g.op.eval (g.inputs.map z)=false) :
    (∃ i∈g.inputs, x i=true ∧ y i=false ∧ z i=false) ∨
    ∃ i j, g=⟨GateOp.and,[i,j]⟩ ∧ (Flip x y z i j ∨ Flip x y z j i) := by
  classical
  by_cases prev : ∃ i∈g.inputs, x i=true ∧ y i=false ∧ z i=false
  · exact Or.inl prev
  right
  obtain ⟨op',ins⟩ := g
  simp only at len op one noneY noneZ prev
  rcases op with rfl|rfl
  · cases ins with
    | nil => simp [GateOp.eval] at noneY
    | cons i rest =>
      cases rest with
      | nil =>
        simp [GateOp.eval] at one noneY noneZ
        exact (prev ⟨i,by simp,one,noneY,noneZ⟩).elim
      | cons j rest =>
        cases rest with
        | cons _ _ => simp at len
        | nil =>
          refine ⟨i,j,rfl,?_⟩
          have pair : x i=true ∧ x j=true := by simpa [GateOp.eval] using one
          have first := fun (h : y i=false ∧ z i=false) => prev ⟨i,by simp,pair.1,h⟩
          have second := fun (h : y j=false ∧ z j=false) => prev ⟨j,by simp,pair.2,h⟩
          cases a : y i <;> cases b : z i <;> cases c : y j <;> cases d : z j <;>
            simp_all [Flip,GateOp.eval]
  · obtain ⟨_,mem,h⟩ := List.any_eq_true.mp one
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have left : y i=false := by
      cases hy : y i with
      | false => rfl
      | true =>
        have on : GateOp.or.eval (ins.map y)=true :=
          List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,hy⟩
        simp_all
    have right : z i=false := by
      cases hz : z i with
      | false => rfl
      | true =>
        have on : GateOp.or.eval (ins.map z)=true :=
          List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,hz⟩
        simp_all
    exact (prev ⟨i,hi,h,left,right⟩).elim

private theorem separating_gate {N : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x y z : Fin N→Bool) (raw : ∀ i, x i=true → y i=true ∨ z i=true)
    (w : ℕ) (active : vl C.gates x w=true) (darkY : vl C.gates y w=false)
    (darkZ : vl C.gates z w=false) : ∃ p i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ ∧
      let A := atGate N p (vl C.gates x)
      let B := atGate N p (vl C.gates y)
      let D := atGate N p (vl C.gates z)
      Flip A B D i j ∨ Flip A B D j i := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · rw [vl_input _ _ _ low] at active darkY darkZ
      rcases raw _ active with h|h <;> simp_all
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    cases eq : C.gates[p]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp eq
      rw [vl_beyond _ _ _ (by omega)] at active
      contradiction
    | some g =>
      have info := List.getElem?_eq_some_iff.mp eq
      have facts := mono g (info.2 ▸ List.getElem_mem info.1)
      rw [raw_gate _ _ _ _ eq] at active darkY darkZ
      rcases local_flip g facts.1 facts.2 _ _ _ active darkY darkZ with ⟨j,_,yes,dy,dz⟩ | ⟨i,j,eg,fl⟩
      · have lt : j<N+p := by by_contra h; simp [atGate,h] at yes
        simp only [atGate,ite_eq_left lt] at yes dy dz
        exact ih j lt yes dy dz
      · exact ⟨p,i,j,eg ▸ eq,fl⟩

def ClosedMarks (N : ℕ) (C : Circuit) (M : Set ℕ) := ∀ p g, C.gates[p]?=some g →
  ∀ i∈g.inputs, i<N+p → i∈M → N+p∈M

def OneMarked (N : ℕ) (C : Circuit) (M : Set ℕ) := ∀ p i j,
  C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ → i<N+p → j<N+p → ¬(i∈M ∧ j∈M)

private theorem unmarked_equal {N : ℕ} (C : Circuit) (M : Set ℕ) (closed : ClosedMarks N C M)
    (x y : Fin N→Bool) (base : ∀ i : Fin N, i.val∉M → x i=y i) (w : ℕ) (wm : w∉M) :
    vl C.gates x w=vl C.gates y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · rw [vl_input _ _ _ low,vl_input _ _ _ low]
      exact base ⟨w,low⟩ wm
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    cases e : C.gates[p]? with
    | none =>
      have := List.getElem?_eq_none_iff.mp e
      rw [vl_beyond _ _ _ (by omega),vl_beyond _ _ _ (by omega)]
    | some g =>
      rw [raw_gate _ _ _ _ e,raw_gate _ _ _ _ e]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases lt : i<N+p
      · simp only [atGate,ite_eq_left lt]
        exact ih i lt (fun m => wm (closed p g e i hi lt m))
      · simp [atGate,lt]

private theorem covered_by_scalar_sets {V J : Type*} [Inhabited V] (G : SimpleGraph V)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (paid : Finset J) (S : J→Finset V)
    (hit : ∀ a b, G.Adj a b → ∃ j∈paid,
      (b∈S j ∧ ∀ t∈S j, G.Adj a t) ∨ (a∈S j ∧ ∀ t∈S j, G.Adj b t)) :
    ∃ T : Finset V, (∀ a b, G.Adj a b → a∈T ∨ b∈T) ∧ T.card≤paid.card := by
  classical
  let eligible j := ∃ a, ∀ t∈S j, G.Adj a t
  let select (j : J) : V := if Wide (S j) then
      (if h : eligible j then h.choose else default)
    else if h : (S j).Nonempty then h.choose else default
  use paid.image select
  refine ⟨?_,Finset.card_image_le⟩
  have picked {j a b} (hj : j∈paid) (hb : b∈S j) (near : ∀ t∈S j, G.Adj a t) :
      a∈paid.image select ∨ b∈paid.image select := by
    by_cases hw : Wide (S j)
    · left
      have e : eligible j := ⟨a,near⟩
      exact Finset.mem_image.mpr ⟨j,hj,by
        simp only [select,ite_eq_left hw,dite_eq_left e]
        exact same_center G c4 (S j) hw e.choose_spec near⟩
    · right
      have ne : (S j).Nonempty := ⟨b,hb⟩
      exact Finset.mem_image.mpr ⟨j,hj,by
        simp only [select,ite_eq_right hw,dite_eq_left ne]
        by_contra d
        exact hw ⟨ne.choose,ne.choose_spec,b,hb,d⟩⟩
  intro a b ab
  obtain ⟨j,hj,⟨hb,near⟩|⟨ha,near⟩⟩ := hit a b ab
  · exact picked hj hb near
  · exact (picked hj ha near).symm

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

noncomputable def andIndices (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun p => ∃ g : Gate, C.gates[p]?=some g ∧ g.op=GateOp.and)

private noncomputable def supply (C : Circuit) (M : Set ℕ) (p : ℕ) : ℕ := by
  classical
  exact match C.gates[p]? with
  | some ⟨_,[i,j]⟩ => if i∈M then j else i
  | _ => 0

private noncomputable def scalarSupport {N : ℕ} (C : Circuit) (M : Set ℕ)
    (L : Finset (Fin N)) (p : ℕ) := (operand N C p (supply C M p)).filter (· ∉ L)

/-- With at most one marked input per AND, each bipartite graph edge has a scalar
multiplier whose right singleton support is contained in its left endpoint's neighborhood. -/
private theorem scalar_hit {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
    (L : Finset (Fin N)) (bip : ∀ u v, G.Adj u v → (u∈L ↔ v∉L))
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M)
    (u r : Fin N) (ul : u∈L) (edge : G.Adj u r) : ∃ p ∈ andIndices C,
      r∈scalarSupport C M L p ∧ ∀ t∈scalarSupport C M L p, G.Adj u t := by
  classical
  have rR := (bip u r edge).mp ul
  let neg : Fin N→Bool := fun t => decide (t=u ∨ (t∉L ∧ ¬G.Adj u t))
  have reject : vl C.gates neg C.output=false := by
    cases h : vl C.gates neg C.output with
    | false => rfl
    | true =>
      obtain ⟨a,b,ab,pa,pb⟩ := (sem neg).mp h
      simp only [neg,decide_eq_true_eq] at pa pb
      rcases pa with rfl|⟨ar,na⟩ <;> rcases pb with rfl|⟨br,nb⟩
      · exact (G.loopless.irrefl _ ab).elim
      · exact (nb ab).elim
      · exact (na ab.symm).elim
      · exact (ar ((bip a b ab).mpr br)).elim
  have yes : vl C.gates (two u r) C.output=true := (sem _).mpr ⟨u,r,edge,by simp [two],by simp [two]⟩
  have init (t : Fin N) (ht : two u r t=true) : neg t=true ∨ one r t=true := by
    rcases (of_decide_eq_true ht : t=u ∨ t=r) with rfl|rfl
    · exact Or.inl (by simp [neg])
    · exact Or.inr (by simp [one])
  obtain ⟨p,i,j,gate,fl⟩ := separating_gate C mono (two u r) neg (one r) init C.output yes reject
    (singleton_rejected G C sem r)
  have ap : p∈andIndices C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
    (List.getElem?_eq_some_iff.mp gate).1,⟨_,gate,rfl⟩⟩
  refine ⟨p,ap,?_⟩
  let A := atGate N p (vl C.gates (two u r))
  let B := atGate N p (vl C.gates neg)
  let Z := atGate N p (vl C.gates (one r))
  have solve (s h : ℕ) (orientation : (i=s ∧ j=h) ∨ (i=h ∧ j=s)) (flip : Flip A B Z s h) :
      r∈scalarSupport C M L p ∧ ∀ t∈scalarSupport C M L p, G.Adj u t := by
    obtain ⟨as',ah,bs,zs,_,zh⟩ := flip
    have slt : s<N+p := by by_contra no; simp [A,atGate,no] at as'
    have hlt : h<N+p := by by_contra no; simp [A,atGate,no] at ah
    have marked : h∈M := by
      by_contra hm
      have same := unmarked_equal C M closed (two u r) (one r) (fun t tm => by
        have ne : t≠u := fun eq => tm (eq ▸ mark u ul)
        simp [two,one,ne]) h hm
      simp only [A,Z,atGate,ite_eq_left hlt] at ah zh
      simp_all
    have selected : supply C M p=s := by
      rcases orientation with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · have unmarked : i∉M := fun im => linear p i j gate slt hlt ⟨im,marked⟩
        simp [supply,gate,unmarked]
      · simp [supply,gate,marked]
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨(operand_mem _ _ _ _).mpr (selected ▸ zs),rR⟩
    · intro t ht
      obtain ⟨on,notL⟩ := Finset.mem_filter.mp ht
      rw [selected] at on
      have singleton := (operand_mem _ _ _ _).mp on
      simp only [atGate,ite_eq_left slt] at singleton
      by_contra outsider
      have incl (a : Fin N) (ha : one t a=true) : neg a=true := by
        have eq : a=t := of_decide_eq_true ha
        subst a
        exact decide_eq_true (Or.inr ⟨notL,outsider⟩)
      have lit := monotone_wires C.gates (fun g hg => (mono g hg).1) (one t) neg incl s singleton
      simp [B,atGate,slt,lit] at bs
  rcases fl with ij|ji
  · exact solve i j (Or.inl ⟨rfl,rfl⟩) ij
  · exact solve j i (Or.inr ⟨rfl,rfl⟩) ji

/-- A C4-free bipartite edge function in a one-sided-linear circuit requires at least
the vertex-cover number of AND gates, regardless of all intermediate false positives. -/
theorem one_sided_and_cover {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C)
    (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
    (L : Finset (Fin N)) (bip : ∀ u v, G.Adj u v → (u∈L ↔ v∉L))
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M) :
    ∃ T : Finset (Fin N), (∀ a b, G.Adj a b → a∈T ∨ b∈T) ∧ T.card≤(andIndices C).card := by
  classical
  apply covered_by_scalar_sets G c4 (andIndices C) (scalarSupport C M L)
  intro a b ab
  by_cases al : a∈L
  · obtain ⟨p,hp,h⟩ := scalar_hit G C mono sem L bip M mark closed linear a b al ab
    exact ⟨p,hp,Or.inl h⟩
  · have bl := (bip b a ab.symm).mpr al
    obtain ⟨p,hp,h⟩ := scalar_hit G C mono sem L bip M mark closed linear b a bl ab.symm
    exact ⟨p,hp,Or.inr h⟩

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

def wireTruth (N : ℕ) (C : Circuit) (w : ℕ) : Set (Fin N→Bool) := {x | vl C.gates x w=true}

def slotTruth (N : ℕ) (C : Circuit) (p i : ℕ) : Set (Fin N→Bool) :=
  if i<N+p then wireTruth N C i else ∅

private theorem slot_truth {N : ℕ} (C : Circuit) (p i : ℕ) (x : Fin N→Bool) :
    x∈slotTruth N C p i ↔ atGate N p (vl C.gates x) i=true := by
  by_cases valid : i<N+p <;> simp [slotTruth,wireTruth,atGate,valid]

def orCharge (C : Circuit) (p : ℕ) : ℕ :=
  match C.gates[p]? with
  | some ⟨.or,_⟩ => 1
  | _ => 0

private theorem physical_scalar_step {N : ℕ} (C : Circuit) (mono : Monotone2 C) (p : ℕ) (g : Gate)
    (gate : C.gates[p]?=some g) {n S} (pool : Pool (inputPool N) n S)
    (available : ∀ i∈g.inputs, slotTruth N C p i∈S) :
    ∃ m T, Pool (inputPool N) m T ∧ S⊆T ∧ wireTruth N C (N+p)∈T ∧ m≤n+orCharge C p := by
  classical
  obtain ⟨op,ins⟩ := g
  have info := List.getElem?_eq_some_iff.mp gate
  have facts := mono _ (info.2 ▸ List.getElem_mem info.1)
  have value (x : Fin N→Bool) : x∈wireTruth N C (N+p) ↔ op.eval (ins.map (atGate N p (vl C.gates x)))=true :=
    (raw_gate C.gates x p _ gate) ▸ Iff.rfl
  have constant {f : Set (Fin N→Bool)} (h : f∈S) (eq : wireTruth N C (N+p)=f) :
      ∃ m T, Pool (inputPool N) m T ∧ S⊆T ∧ wireTruth N C (N+p)∈T ∧ m≤n+orCharge C p :=
    ⟨n,S,pool,Set.Subset.rfl,eq ▸ h,Nat.le_add_right _ _⟩
  rcases facts.1 with andOp|orOp
  · change op=GateOp.and at andOp
    subst op
    cases ins with
    | nil => exact constant (pool_contains pool (Or.inl rfl)) (by ext x; simp [value,GateOp.eval])
    | cons i tail =>
      cases tail with
      | nil => exact constant (available i (by simp)) (by ext x; simp [value,slot_truth,GateOp.eval])
      | cons j tail =>
        cases tail with
        | cons _ _ => simp at facts
        | nil =>
          let z := slotTruth N C p i ∩ slotTruth N C p j
          have eq : wireTruth N C (N+p)=z := by ext x; simp [z,value,slot_truth,GateOp.eval]
          exact ⟨n,insert z S,.mul pool (available i (by simp)) (available j (by simp)),
            Set.subset_insert _ _,eq ▸ Set.mem_insert _ _,Nat.le_add_right _ _⟩
  · change op=GateOp.or at orOp
    subst op
    cases ins with
    | nil => exact constant (pool_contains pool (Or.inr (Or.inl rfl))) (by ext x; simp [value,GateOp.eval])
    | cons i tail =>
      cases tail with
      | nil => exact constant (available i (by simp)) (by ext x; simp [value,slot_truth,GateOp.eval])
      | cons j tail =>
        cases tail with
        | cons _ _ => simp at facts
        | nil =>
          let z := slotTruth N C p i ∪ slotTruth N C p j
          have eq : wireTruth N C (N+p)=z := by ext x; simp [z,value,slot_truth,GateOp.eval]
          exact ⟨n+1,insert z S,.add pool (available i (by simp)) (available j (by simp)),
            Set.subset_insert _ _,eq ▸ Set.mem_insert _ _,by simp [orCharge,gate]⟩

noncomputable def scalarCharge (N : ℕ) (C : Circuit) (M : Set ℕ) (p : ℕ) : ℕ := by
  classical
  exact if N+p∈M then 0 else orCharge C p

/-- The right-only scalar wires of a one-sided circuit can be evaluated once,
charging only OR gates outside the marked part of its data-flow graph. -/
theorem prepare_scalars (N : ℕ) (C : Circuit) (mono : Monotone2 C) (M : Set ℕ)
    (closed : ClosedMarks N C M) (t : ℕ) (within : t≤C.gates.length) :
    ∃ n S, Pool (inputPool N) n S ∧ n≤∑ k∈Finset.range t, scalarCharge N C M k ∧
      ∀ w<N+t, w∉M → wireTruth N C w∈S := by
  classical
  induction t with
  | zero =>
    refine ⟨0,inputPool N,.start,by simp,?_⟩
    intro j lt _
    have raw : j<N := by omega
    apply Or.inr; apply Or.inr; use ⟨j,raw⟩
    ext x
    simp [wireTruth,vl_input _ _ _ raw]
  | succ k ih =>
    obtain ⟨n,S,pool,paid,available⟩ := ih (by omega)
    have valid : k<C.gates.length := by omega
    let g := C.gates[k]
    have gate : C.gates[k]?=some g := List.getElem?_eq_getElem valid
    have supply (j : ℕ) (jm : j∈g.inputs) (clear : N+k∉M) : slotTruth N C k j∈S := by
      by_cases low : j<N+k
      · have no : j∉M := fun mark => clear (closed k g gate j jm low mark)
        simpa [slotTruth,low] using available j low no
      · simp [slotTruth,low]
        exact pool_contains pool (Or.inr (Or.inl rfl))
    by_cases mark : N+k∈M
    · refine ⟨n,S,pool,?_,?_⟩
      · simpa [Finset.sum_range_succ,scalarCharge,mark] using paid
      · intro j lt no
        have ne : j≠N+k := fun e => no (e ▸ mark)
        exact available j (by omega) no
    · obtain ⟨m,T,pnew,inc,ok,bound⟩ := physical_scalar_step C mono k g gate pool (fun j jm => supply j jm mark)
      refine ⟨m,T,pnew,?_,?_⟩
      · simp only [Finset.sum_range_succ,scalarCharge,ite_eq_right mark]
        exact bound.trans (Nat.add_le_add_right paid _)
      · intro j lt no
        by_cases here : j=N+k
        · simpa [here] using ok
        · exact inc (available j (by omega) no)

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

private def markedSlot (N : ℕ) (M : Set ℕ) (p i : ℕ) := i<N+p ∧ i∈M

private noncomputable def admit (N : ℕ) (M : Set ℕ) (p i : ℕ) (s : Set (Fin N→Bool)) :
    List (ℕ×Set (Fin N→Bool)) := by
  classical
  exact if markedSlot N M p i then [(i,s)] else []

noncomputable def circuitTerms (N : ℕ) (C : Circuit) (M : Set ℕ) (p : ℕ) :
    List (ℕ×Set (Fin N→Bool)) :=
  match C.gates[p]? with
  | some ⟨.or,ins⟩ => ins.flatMap (fun i => admit N M p i Set.univ)
  | some ⟨.and,[i]⟩ => admit N M p i Set.univ
  | some ⟨.and,[i,j]⟩ => admit N M p i (slotTruth N C p j) ++ admit N M p j (slotTruth N C p i)
  | _ => []

noncomputable def reverseCharge (N : ℕ) (C : Circuit) (M : Set ℕ) (p : ℕ) : ℕ := by
  classical
  exact if N+p∈M then orCharge C p else 0

private theorem term_facts (N : ℕ) (C : Circuit) (mono : Monotone2 C) (M : Set ℕ)
    (closed : ClosedMarks N C M) (linear : OneMarked N C M) (base : Set (Set (Fin N→Bool)))
    (top : Set.univ∈base) (bot : ∅∈base)
    (availability : ∀ w<N+C.gates.length, w∉M → wireTruth N C w∈base)
    (p : ℕ) (lt : p<C.gates.length) :
    (∀ z∈circuitTerms N C M p, z.1<N+p ∧ z.2∈base) ∧
    (circuitTerms N C M p).length≤reverseCharge N C M p+1 := by
  classical
  let g := C.gates[p]
  have atp : C.gates[p]?=some g := List.getElem?_eq_getElem lt
  have facts := mono g (List.getElem_mem lt)
  have ready (i : ℕ) (hm : ¬markedSlot N M p i) : slotTruth N C p i∈base := by
    by_cases hi : i<N+p
    · simpa [slotTruth,hi] using availability i (by omega) (fun h => hm ⟨hi,h⟩)
    · simpa [slotTruth,hi] using bot
  generalize eq : g=g' at atp facts
  obtain ⟨op,ins⟩ := g'
  rcases facts.1 with a|o
  · change op=GateOp.and at a
    subst op
    have free : reverseCharge N C M p=0 := by simp [reverseCharge,orCharge,atp]
    cases ins with
    | nil => simp [circuitTerms,atp,free]
    | cons i rest =>
      cases rest with
      | nil =>
        by_cases mi : markedSlot N M p i
        · simp [circuitTerms,atp,admit,mi,top,mi.1,free]
        · simp [circuitTerms,atp,admit,mi,free]
      | cons j rest =>
        cases rest with
        | cons _ _ => simp at facts
        | nil =>
          have exclusive (mi : markedSlot N M p i) (mj : markedSlot N M p j) : False :=
            linear p i j atp mi.1 mj.1 ⟨mi.2,mj.2⟩
          by_cases mi : markedSlot N M p i <;> by_cases mj : markedSlot N M p j
          · exact (exclusive mi mj).elim
          · simp [circuitTerms,atp,admit,mi,mj,free,mi.1,ready j mj]
          · simp [circuitTerms,atp,admit,mi,mj,free,mj.1,ready i mi]
          · simp [circuitTerms,atp,admit,mi,mj,free]
  · change op=GateOp.or at o
    subst op
    have cost (i : ℕ) (mem : i∈ins) (mark : markedSlot N M p i) : reverseCharge N C M p=1 := by
      have active := closed p ⟨.or,ins⟩ atp i mem mark.1 mark.2
      simp [reverseCharge,active,orCharge,atp]
    constructor
    · intro z hz
      simp only [circuitTerms,atp,List.mem_flatMap] at hz
      obtain ⟨i,_,hi⟩ := hz
      by_cases mi : markedSlot N M p i
      · obtain rfl : z=(i,Set.univ) := by simpa [admit,mi] using hi
        exact ⟨mi.1,top⟩
      · simp [admit,mi] at hi
    · cases ins with
      | nil => simp [circuitTerms,atp]
      | cons i rest =>
        cases rest with
        | nil =>
          by_cases mi : markedSlot N M p i <;> simp [circuitTerms,atp,admit,mi]
        | cons j rest =>
          cases rest with
          | cons _ _ => simp at facts
          | nil =>
            by_cases mi : markedSlot N M p i <;> by_cases mj : markedSlot N M p j
            · simp [circuitTerms,atp,admit,mi,mj,cost i (by simp) mi]
            · simp [circuitTerms,atp,admit,mi,mj]
            · simp [circuitTerms,atp,admit,mi,mj]
            · simp [circuitTerms,atp,admit,mi,mj]

def wave {N : ℕ} (terms : ℕ→List (ℕ×Set (Fin N→Bool))) (w : ℕ) (u : Fin N) :
    Set (Fin N→Bool) :=
  if w<N then (if w=u.val then Set.univ else ∅)
  else {x | ∃ z∈terms (w-N), ∃ _h : z.1<w, x∈wave terms z.1 u ∧ x∈z.2}
termination_by w
decreasing_by assumption

private theorem wave_raw {N : ℕ} (terms : ℕ→List (ℕ×Set (Fin N→Bool))) {w : ℕ} (lt : w<N) (u : Fin N) :
    wave terms w u=if w=u.val then Set.univ else ∅ := by rw [wave,ite_eq_left lt]

private theorem wave_step {N : ℕ} (terms : ℕ→List (ℕ×Set (Fin N→Bool))) (p : ℕ)
    (small : ∀ z∈terms p, z.1<N+p) (u : Fin N) (x : Fin N→Bool) :
    x∈wave terms (N+p) u ↔ ∃ z∈terms p, x∈wave terms z.1 u ∧ x∈z.2 := by
  rw [wave,ite_eq_right (by omega),Nat.add_sub_cancel_left]
  constructor
  · rintro ⟨z,hz,_,eq⟩; exact ⟨z,hz,eq⟩
  · rintro ⟨z,hz,eq⟩; exact ⟨z,hz,small z hz,eq⟩

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

def clearSide {N : ℕ} (L : Finset (Fin N)) (x : Fin N→Bool) (i : Fin N) : Bool :=
  if i∈L then false else x i

def addPoint {N : ℕ} (L : Finset (Fin N)) (u : Fin N) (x : Fin N→Bool) (i : Fin N) : Bool :=
  if i∈L then decide (i=u) else x i

/-- Each root value with a single left input set is the right-side baseline OR
its forward linear coefficient. This identity permits redundant marked gates. -/
theorem physical_coefficient {N : ℕ} (C : Circuit) (mono : Monotone2 C) (L : Finset (Fin N))
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M)
    (small : ∀ p, ∀ z∈circuitTerms N C M p, z.1<N+p) (u : Fin N) (ul : u∈L)
    (x : Fin N→Bool) (w : ℕ) :
    vl C.gates (addPoint L u x) w=true ↔ vl C.gates (clearSide L x) w=true ∨
      x∈wave (circuitTerms N C M) w u := by
  classical
  let terms := circuitTerms N C M
  have eqRaw (v : Fin N) (vm : v.val∉M) : v∉L := fun h => vm (mark v h)
  have noMark (i : ℕ) (im : i∉M) :
      vl C.gates (addPoint L u x) i=vl C.gates (clearSide L x) i :=
    unmarked_equal C M closed _ _ (fun v vm => by simp [addPoint,clearSide,eqRaw v vm]) i im
  have scalarRaw (i : ℕ) (im : i∉M) : vl C.gates (clearSide L x) i=vl C.gates x i :=
    unmarked_equal C M closed _ _ (fun v vm => by simp [clearSide,eqRaw v vm]) i im
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · let i : Fin N := ⟨w,low⟩
      have inw : w=u.val ↔ i=u := ⟨fun e => Fin.ext e,fun e => congrArg Fin.val e⟩
      rw [vl_input _ _ _ low,vl_input _ _ _ low,wave_raw _ low]
      change addPoint L u x i=true ↔ clearSide L x i=true ∨ x∈(if w=u.val then Set.univ else ∅)
      by_cases h : i=u
      · simp [inw.mpr h,h,addPoint,clearSide,ul]
      · have ne := mt inw.mp h
        by_cases li : i∈L <;> simp [addPoint,clearSide,li,h,ne]
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    rw [wave_step _ p (small p)]
    cases atp : C.gates[p]? with
    | none =>
      have bound := List.getElem?_eq_none_iff.mp atp
      rw [vl_beyond _ _ _ (by omega),vl_beyond _ _ _ (by omega)]
      simp [circuitTerms,atp]
    | some g =>
      let A := atGate N p (vl C.gates (addPoint L u x))
      let B := atGate N p (vl C.gates (clearSide L x))
      have signal (i : ℕ) : A i=true ↔ B i=true ∨ markedSlot N M p i ∧ x∈wave terms i u := by
        by_cases lt : i<N+p
        · by_cases im : i∈M
          · simpa [A,B,atGate,markedSlot,lt,im,terms] using ih i lt
          · simp [A,B,atGate,markedSlot,lt,im,noMark i im]
        · simp [A,B,atGate,markedSlot,lt]
      have scalar (i : ℕ) (hm : ¬markedSlot N M p i) : B i=true ↔ x∈slotTruth N C p i := by
        by_cases lt : i<N+p
        · have im : i∉M := fun h => hm ⟨lt,h⟩
          simp [B,atGate,slotTruth,wireTruth,lt,scalarRaw i im]
        · simp [B,atGate,slotTruth,lt]
      rw [raw_gate _ _ _ _ atp,raw_gate _ _ _ _ atp]
      change g.op.eval (g.inputs.map A)=true ↔ g.op.eval (g.inputs.map B)=true ∨
        ∃ z∈terms p, x∈wave terms z.1 u ∧ x∈z.2
      obtain ⟨op,ins⟩ := g
      obtain ⟨lt,atg⟩ := List.getElem?_eq_some_iff.mp atp
      have monoOp := mono _ (atg ▸ List.getElem_mem lt)
      rcases monoOp.1 with hand|hor
      · change op=GateOp.and at hand
        subst op
        cases ins with
        | nil => simp [GateOp.eval,terms,circuitTerms,atp]
        | cons i rest =>
          cases rest with
          | nil => by_cases mi : markedSlot N M p i <;>
              simpa [GateOp.eval,terms,circuitTerms,atp,admit,mi] using signal i
          | cons j rest =>
            cases rest with
            | cons _ _ => simp at monoOp
            | nil =>
              have exclusive (mi : markedSlot N M p i) (mj : markedSlot N M p j) : False :=
                linear p i j atp mi.1 mj.1 ⟨mi.2,mj.2⟩
              by_cases mi : markedSlot N M p i <;> by_cases mj : markedSlot N M p j
              · exact (exclusive mi mj).elim
              · simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
                  Bool.and_true,Bool.and_eq_true]
                simp [terms,circuitTerms,atp,admit,mi,mj,←scalar j mj]
                rw [signal i,signal j]
                simp only [mi,mj,true_and,false_and,or_false,terms]
                tauto
              · simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,
                  Bool.and_true,Bool.and_eq_true]
                simp [terms,circuitTerms,atp,admit,mi,mj,←scalar i mi]
                rw [signal i,signal j]
                simp only [mi,mj,true_and,false_and,or_false,terms]
                tauto
              · simp [GateOp.eval,terms,circuitTerms,atp,admit,mi,mj,signal]
      · change op=GateOp.or at hor
        subst op
        cases ins with
        | nil => simp [GateOp.eval,terms,circuitTerms,atp]
        | cons i rest =>
          cases rest with
          | nil => by_cases mi : markedSlot N M p i <;>
              simpa [GateOp.eval,terms,circuitTerms,atp,admit,mi] using signal i
          | cons j rest =>
            cases rest with
            | cons _ _ => simp at monoOp
            | nil =>
              by_cases mi : markedSlot N M p i <;> by_cases mj : markedSlot N M p j <;>
                simp [GateOp.eval,terms,circuitTerms,atp,admit,mi,mj,signal] <;> tauto

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

private theorem total_charges (N : ℕ) (C : Circuit) (M : Set ℕ) :
    (∑ p∈Finset.range C.gates.length, scalarCharge N C M p) +
    (∑ p∈Finset.range C.gates.length, reverseCharge N C M p)=(orIndices C).card := by
  classical
  let R := Finset.range C.gates.length
  let flag (p : ℕ) := ∃ g : Gate, C.gates[p]?=some g ∧ g.op=GateOp.or
  have eq (p : ℕ) : scalarCharge N C M p + reverseCharge N C M p=if flag p then 1 else 0 := by
    have datum : orCharge C p=if flag p then 1 else 0 := by
      by_cases f : flag p
      · rw [ite_eq_left f]
        obtain ⟨⟨op,ins⟩,atp,eq⟩ := f
        change op=GateOp.or at eq
        subst op
        simp [orCharge,atp]
      · rw [ite_eq_right f]
        cases atp : C.gates[p]? with
        | none => simp [orCharge,atp]
        | some g =>
          obtain ⟨op,ins⟩ := g
          cases op <;> simp_all [orCharge,flag]
    by_cases mem : N+p∈M <;> simpa [scalarCharge,reverseCharge,mem] using datum
  rw [← Finset.sum_add_distrib]
  change ∑ p∈R, _=(R.filter flag).card
  simp_rw [eq]
  simp

private theorem zero_on_right {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (L : Finset (Fin N))
    (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (x : Fin N→Bool) : vl C.gates (clearSide L x) C.output=false := by
  cases result : vl C.gates (clearSide L x) C.output with
  | false => rfl
  | true =>
    obtain ⟨a,b,ab,onA,onB⟩ := (sem _).mp result
    by_cases al : a∈L
    · simp [clearSide,al] at onA
    · have bl := (bip b a ab.symm).mpr al
      simp [clearSide,bl] at onB

private theorem graph_coefficient {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (mono : Monotone2 C)
    (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M)
    (small : ∀ p, ∀ z∈circuitTerms N C M p, z.1<N+p) (u : Fin N) (ul : u∈L) (x : Fin N→Bool) :
    x∈wave (circuitTerms N C M) C.output u ↔ ∃ r, G.Adj u r ∧ x r=true := by
  have result := physical_coefficient C mono L M mark closed linear small u ul x C.output
  rw [zero_on_right G C L bip sem x] at result
  simp only [Bool.false_eq_true,false_or] at result
  rw [←result]
  change circuitFun N C (addPoint L u x)=true ↔ _
  rw [sem]
  constructor
  · rintro ⟨a,b,ab,onA,onB⟩
    by_cases al : a∈L
    · have br := (bip a b ab).mp al
      obtain rfl : a=u := by simpa [addPoint,al] using onA
      exact ⟨b,ab,by simpa [addPoint,br] using onB⟩
    · have bl := (bip b a ab.symm).mpr al
      obtain rfl : b=u := by simpa [addPoint,bl] using onB
      exact ⟨a,ab.symm,by simpa [addPoint,al] using onA⟩
  · rintro ⟨r,edge,xr⟩
    have rr := (bip u r edge).mp ul
    exact ⟨u,r,edge,by simp [addPoint,ul],by simpa [addPoint,rr] using xr⟩

private theorem count_bipartite_edges {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (D : Fin N→Finset (Fin N)) (neighbor : ∀ u r, r∈D u ↔ G.Adj u r) :
    G.edgeSet.ncard≤∑ u∈L.filter (fun u => (D u).Nonempty), (D u).card := by
  classical
  let live := L.filter (fun u => (D u).Nonempty)
  let star u := (D u).image (fun r => s(u,r))
  have covers {u r : Fin N} (ul : u∈L) (adj : G.Adj u r) : s(u,r)∈live.biUnion star := by
    have mem := (neighbor u r).mpr adj
    exact Finset.mem_biUnion.mpr ⟨u,Finset.mem_filter.mpr ⟨ul,⟨r,mem⟩⟩,Finset.mem_image.mpr ⟨r,mem,rfl⟩⟩
  have bound : G.edgeFinset⊆live.biUnion star := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u r =>
      have a := SimpleGraph.mem_edgeFinset.mp he
      by_cases ul : u∈L
      · exact covers ul a
      · rw [Sym2.eq_swap]
        exact covers ((bip r u a.symm).mpr ul) a.symm
  rw [←G.coe_edgeFinset,Set.ncard_coe_finset]
  exact ((Finset.card_le_card bound).trans Finset.card_biUnion_le).trans
    (Finset.sum_le_sum (fun _ _ => Finset.card_image_le))

/-- Every one-sided-linear monotone circuit for a bipartite C4-free graph needs
at least one less OR than the number of edges. No degree or depth bound is used. -/
theorem one_sided_or_count {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M) :
    G.edgeSet.ncard≤(orIndices C).card+1 := by
  classical
  let D (u : Fin N) := Finset.univ.filter (fun r => G.Adj u r)
  have neighbor (u r : Fin N) : r∈D u ↔ G.Adj u r := by simp [D]
  let live := L.filter (fun u => (D u).Nonempty)
  have edges := count_bipartite_edges G L bip D neighbor
  by_cases output : C.output<N+C.gates.length
  swap
  · have em : live=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨_,r,hr⟩ := Finset.mem_filter.mp hu
      have yes : vl C.gates (two u r) C.output=true :=
        (sem _).mpr ⟨u,r,(neighbor u r).mp hr,by simp [two],by simp [two]⟩
      rw [vl_beyond _ _ _ (by omega)] at yes
      contradiction
    change G.edgeSet.ncard≤∑ u∈live, (D u).card at edges
    have zeroBound : G.edgeSet.ncard≤0 := by simpa only [em,Finset.sum_empty] using edges
    omega
  obtain ⟨cost,base,pool,scalarBound,available⟩ := prepare_scalars N C mono M closed C.gates.length (by omega)
  have top : Set.univ∈base := pool_contains pool (Or.inl rfl)
  have bot : ∅∈base := pool_contains pool (Or.inr (Or.inl rfl))
  have facts := term_facts N C mono M closed linear base top bot available
  have small (p : ℕ) (z) (hz : z∈circuitTerms N C M p) : z.1<N+p := by
    by_cases h : p<C.gates.length
    · exact ((facts p h).1 z hz).1
    · have no := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt h)
      simp [circuitTerms,no] at hz
  have eff := graph_coefficient G C mono L bip sem M mark closed linear small
  let terms := circuitTerms N C M
  have need := linear_network_cost base C.gates.length cost pool (wave terms)
    (fun _ lt u => wave_raw _ lt u) terms (reverseCharge N C M)
    (fun k hk => (facts k hk).1) (fun k hk => (facts k hk).2)
    (fun k _ u x => wave_step terms k (small k) u x) C.output output live D
    (fun i _ j _ ij a ai aj b bi bj =>
      (c4 i a j b ((neighbor i a).mp ai) ((neighbor j a).mp aj).symm
        ((neighbor j b).mp bj) ((neighbor i b).mp bi).symm).resolve_left ij)
    (fun u hu a ha => (eff u (Finset.mem_filter.mp hu).1 (one a)).mpr ⟨a,(neighbor u a).mp ha,by simp [one]⟩)
    (fun u hu on => by
      obtain ⟨r,ur,lit⟩ := (eff u (Finset.mem_filter.mp hu).1 _).mp on
      exact of_decide_eq_true lit ((neighbor u r).mpr ur))
    (fun _ hu => (Finset.mem_filter.mp hu).2)
  have total := total_charges N C M
  change G.edgeSet.ncard≤∑ u∈live, (D u).card at edges
  omega

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

/-- This Boolean mask tests which wires can be lit with all left variables off. -/
def rightRow {N : ℕ} (L : Finset (Fin N)) (i : Fin N) := decide (i∉L)

def twoDark (V : ℕ→Bool) (g : Gate) : Prop :=
  g.op=GateOp.and ∧ g.inputs.length=2 ∧ ∀ i∈g.inputs, V i=false

private noncomputable def rewire (N : ℕ) (V : ℕ→Bool) (p : ℕ) (g : Gate) (i : ℕ) := by
  classical
  exact if (V (N+p)=true ∧ V i=false) ∨ (V (N+p)=false ∧ twoDark V g) then N+p else i

private noncomputable def rewireGate (N : ℕ) (V : ℕ→Bool) (p : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (rewire N V p g)⟩

noncomputable def linearize (N : ℕ) (V : ℕ→Bool) (C : Circuit) : Circuit :=
  ⟨C.gates.mapIdx (rewireGate N V),C.output⟩

private theorem at_linearize (N : ℕ) (V : ℕ→Bool) (C : Circuit) (p : ℕ) :
    (linearize N V C).gates[p]?=(C.gates[p]?).map (rewireGate N V p) := by
  simp [linearize]

private theorem rewire_eval {N : ℕ} (V : ℕ→Bool) (C : Circuit) (x : Fin N→Bool)
    {p : ℕ} {g : Gate} (atp : C.gates[p]?=some g) :
    vl (linearize N V C).gates x (N+p)=g.op.eval
      (g.inputs.map (fun i => atGate N p (vl (linearize N V C).gates x) (rewire N V p g i))) := by
  have hp : (linearize N V C).gates[p]?=some (rewireGate N V p g) := by
    simp [at_linearize,atp]
  rw [raw_gate _ _ _ _ hp]
  simp [rewireGate,List.map_map,Function.comp_def]

private theorem rewire_alt (N : ℕ) (V : ℕ→Bool) (p : ℕ) (g : Gate) (i : ℕ) :
    rewire N V p g i=N+p ∨ rewire N V p g i=i := by
  classical
  unfold rewire
  split <;> simp_all

private theorem linearize_below {N : ℕ} (V : ℕ→Bool) (C : Circuit) (mono : Monotone2 C)
    (x : Fin N→Bool) (w : ℕ) :
    vl (linearize N V C).gates x w=true → vl C.gates x w=true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · rw [vl_input _ _ _ low,vl_input _ _ _ low]; exact id
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    cases gate : C.gates[p]? with
    | none =>
      have pos := List.getElem?_eq_none_iff.mp gate
      have size : (linearize N V C).gates.length=C.gates.length := by simp [linearize]
      rw [vl_beyond _ _ _ (by omega)]; simp
    | some g =>
      rw [rewire_eval V C x gate,raw_gate _ _ _ _ gate]
      have atp := List.getElem?_eq_some_iff.mp gate
      apply bool_gate_mono g (mono g (atp.2 ▸ List.getElem_mem atp.1)).1
      intro i _ on
      rcases rewire_alt N V p g i with bad|keep
      · simp [bad,atGate] at on
      rw [keep] at on
      by_cases lt : i<N+p
      · simp only [atGate,ite_eq_left lt] at on ⊢
        exact ih i lt on
      · simp [atGate,lt] at on

private theorem linearize_mono (N : ℕ) (V : ℕ→Bool) (C : Circuit) (mono : Monotone2 C) :
    Monotone2 (linearize N V C) := by
  intro g hg
  obtain ⟨j,eq⟩ := List.get_of_mem hg
  have atj : (linearize N V C).gates[j.val]?=some g :=
    (List.getElem?_eq_getElem j.isLt).trans (congrArg some eq)
  rw [at_linearize] at atj
  cases old : C.gates[j.val]? with
  | none => simp [old] at atj
  | some g' =>
    have eq' : rewireGate N V j.val g'=g := by simpa [old] using atj
    have atp := List.getElem?_eq_some_iff.mp old
    simpa [←eq',rewireGate] using mono g' (atp.2 ▸ List.getElem_mem atp.1)

private theorem linearize_marks (N : ℕ) (V : ℕ→Bool) (C : Circuit) :
    ClosedMarks N (linearize N V C) {i | V i=false} ∧
    OneMarked N (linearize N V C) {i | V i=false} := by
  classical
  constructor
  · intro p g gate j hj lt dark
    simp only [Set.mem_ofPred_eq] at dark ⊢
    rw [at_linearize] at gate
    cases old : C.gates[p]? with
    | none => simp [old] at gate
    | some g' =>
      have eq : rewireGate N V p g'=g := by simpa [old] using gate
      rw [←eq] at hj
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      rcases rewire_alt N V p g' i with bad|keep
      · omega
      rw [keep] at dark
      cases base : V (N+p) with
      | false => rfl
      | true => simp [rewire,base,dark] at lt
  · intro p i j gate ilt jlt dark
    simp only [Set.mem_ofPred_eq] at dark
    rw [at_linearize] at gate
    cases old : C.gates[p]? with
    | none => simp [old] at gate
    | some g =>
      have eq : rewireGate N V p g=⟨GateOp.and,[i,j]⟩ := by simpa [old] using gate
      have op := congrArg Gate.op eq
      have ins := congrArg Gate.inputs eq
      change g.inputs.map (rewire N V p g)=[i,j] at ins
      have len : g.inputs.length=2 := by simpa using congrArg List.length ins
      obtain ⟨a,b,ab⟩ : ∃ a b, g.inputs=[a,b] := List.length_eq_two.mp len
      simp only [ab,List.map_cons,List.map_nil,List.cons.injEq, and_true] at ins
      obtain ⟨hi,hj⟩ := ins
      have ia : i=a := by rcases rewire_alt N V p g a with h|h <;> omega
      have jb : j=b := by rcases rewire_alt N V p g b with h|h <;> omega
      subst a; subst b
      have both : twoDark V g := ⟨op,len,by simpa [ab] using dark⟩
      cases hv : V (N+p) <;> simp [rewire,hv,both,dark.1] at hi <;> omega

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

/-- A finite mask condition. In a gate dark on the complete right side, a live
operand needed by a positive edge is already lit by its right endpoint alone. -/
def ScalarEdges {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (L : Finset (Fin N)) :=
  let V := vl C.gates (rightRow L)
  ∀ u∈L, ∀ r, G.Adj u r → ∀ p g, C.gates[p]?=some g → V (N+p)=false →
    vl C.gates (two u r) (N+p)=true →
    ¬twoDark V g ∧ ∀ i∈g.inputs, i<N+p → V i=true → vl C.gates (one r) i=true

private theorem linearize_right {N : ℕ} (C : Circuit) (mono : Monotone2 C)
    (L : Finset (Fin N)) (u r : Fin N) (right : r∉L) (w : ℕ) :
    vl C.gates (one r) w=true →
    vl (linearize N (vl C.gates (rightRow L)) C).gates (two u r) w=true := by
  let V := vl C.gates (rightRow L)
  have monot (i : ℕ) : vl C.gates (one r) i=true → V i=true := by
    apply monotone_wires C.gates (fun g hg => (mono g hg).1)
    intro t ht
    have eq : t=r := of_decide_eq_true ht
    exact decide_eq_true (eq ▸ right)
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · rw [vl_input _ _ _ low,vl_input _ _ _ low]
      exact fun h => decide_eq_true (Or.inr (of_decide_eq_true h))
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    intro input
    have live := monot (N+p) input
    cases gate : C.gates[p]? with
    | none =>
      have len := List.getElem?_eq_none_iff.mp gate
      rw [vl_beyond _ _ _ (by omega)] at input
      contradiction
    | some g =>
      rw [rewire_eval V C _ gate]
      rw [raw_gate _ _ _ _ gate] at input
      have eq := List.getElem?_eq_some_iff.mp gate
      apply bool_gate_mono g (mono g (eq.2 ▸ List.getElem_mem eq.1)).1 _ _ _ input
      intro j _ lit
      have lt : j<N+p := by by_contra high; simp [atGate,high] at lit
      simp only [atGate,ite_eq_left lt] at lit
      have active := monot j lit
      have kept : rewire N V p g j=j := by simp [rewire,live,active]
      simpa only [kept,atGate,ite_eq_left lt] using ih j lt lit

private theorem linearize_edge {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (mono : Monotone2 C) (L : Finset (Fin N)) (hyp : ScalarEdges G C L)
    (u r : Fin N) (left : u∈L) (right : r∉L) (edge : G.Adj u r) (w : ℕ)
    (dark : vl C.gates (rightRow L) w=false) :
    vl C.gates (two u r) w=true →
      vl (linearize N (vl C.gates (rightRow L)) C).gates (two u r) w=true := by
  let V := vl C.gates (rightRow L)
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w<N
    · rw [vl_input _ _ _ low,vl_input _ _ _ low]; exact id
    obtain ⟨p,rfl⟩ : ∃p,w=N+p := ⟨w-N,by omega⟩
    intro input
    cases gate : C.gates[p]? with
    | none =>
      have len := List.getElem?_eq_none_iff.mp gate
      rw [vl_beyond _ _ _ (by omega)] at input
      contradiction
    | some g =>
      obtain ⟨notBoth, useScalar⟩ := hyp u left r edge p g gate dark input
      rw [rewire_eval V C _ gate]
      rw [raw_gate _ _ _ _ gate] at input
      have eq := List.getElem?_eq_some_iff.mp gate
      apply bool_gate_mono g (mono g (eq.2 ▸ List.getElem_mem eq.1)).1 _ _ _ input
      intro j jm lit
      have lt : j<N+p := by by_contra high; simp [atGate,high] at lit
      have dark' : V (N+p)=false := dark
      change ¬twoDark V g at notBoth
      have kept : rewire N V p g j=j := by simp [rewire,dark',notBoth]
      simp only [kept,atGate,ite_eq_left lt] at lit ⊢
      cases base : V j with
      | false => exact ih j lt base lit
      | true => exact linearize_right C mono L u r right j (useScalar j jm lt base)

/-- Rewire an arbitrary circuit satisfying the finite scalar-edge condition into
a syntactically one-sided circuit at the identical indices and with the same gate
operations. Its correctness on the entire cube follows from monotonicity. -/
theorem scalar_edges_linearization {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit)
    (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L)) (mono : Monotone2 C)
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (hyp : ScalarEdges G C L) :
    let V := vl C.gates (rightRow L)
    let D := linearize N V C
    let M := {i | V i=false}
    D.size=C.size ∧ Monotone2 D ∧ ClosedMarks N D M ∧ OneMarked N D M ∧ (∀ u∈L, u.val∈M) ∧
    ∀ x : Fin N→Bool, circuitFun N D x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true := by
  let V := vl C.gates (rightRow L)
  let D := linearize N V C
  have md := linearize_mono N V C mono
  obtain ⟨closed,one⟩ := linearize_marks N V C
  refine ⟨by simp [linearize,Circuit.size],md,closed,one,?_,?_⟩
  · intro u hu
    change V u.val=false
    simp [V,vl_input _ _ _ u.isLt,rightRow,hu]
  intro x
  constructor
  · intro yes
    exact (sem x).mp (linearize_below V C mono x C.output yes)
  · rintro ⟨a,b,ab,xa,xb⟩
    have base : V C.output=false := by
      cases val : V C.output with
      | false => rfl
      | true =>
        obtain ⟨i,j,ij,ri,rj⟩ := (sem _).mp val
        exact (of_decide_eq_true ri ((bip i j ij).mpr (of_decide_eq_true rj))).elim
    have go (u r : Fin N) (ul : u∈L) (edge : G.Adj u r) (xu : x u=true) (xr : x r=true) :
        circuitFun N D x=true := by
      have yes : vl C.gates (two u r) C.output=true := (sem _).mpr
        ⟨u,r,edge,by simp [two],by simp [two]⟩
      have good := linearize_edge G C mono L hyp u r ul ((bip u r edge).mp ul) edge _ base yes
      apply monotone_wires D.gates (fun g hg => (md g hg).1) (two u r) x _ D.output good
      intro t ht
      rcases (of_decide_eq_true ht : t=u ∨ t=r) with rfl|rfl <;> assumption
    by_cases al : a∈L
    · exact go a b al ab xa xb
    · exact go b a ((bip b a ab.symm).mpr al) ab.symm xb xa

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

/-- Only three input rows per edge are inspected. Failure witnesses a binary AND
whose two operands both change from zero to one when the left endpoint is added. -/
def NoEdgeCollision {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (L : Finset (Fin N)) :=
  ∀ u∈L, ∀ r, G.Adj u r → ∀ p i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ →
    vl C.gates (rightRow L) (N+p)=false → vl C.gates (two u r) (N+p)=true →
    atGate N p (vl C.gates (one r)) i=true ∨ atGate N p (vl C.gates (one r)) j=true

theorem no_collision_scalar {N : ℕ} (G : SimpleGraph (Fin N)) (C : Circuit) (L : Finset (Fin N))
    (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L)) (mono : Monotone2 C)
    (clean : NoEdgeCollision G C L) : ScalarEdges G C L := by
  intro u ul r edge p g gate base yes
  let V := vl C.gates (rightRow L)
  let X := vl C.gates (two u r)
  let Y := vl C.gates (one r)
  have all (i : ℕ) : Y i=true → V i=true := by
    apply monotone_wires C.gates (fun g hg => (mono g hg).1)
    intro t ht
    have eq : t=r := of_decide_eq_true ht
    exact decide_eq_true (eq ▸ (bip u r edge).mp ul)
  obtain ⟨op,ins⟩ := g
  have info := List.getElem?_eq_some_iff.mp gate
  have facts := mono _ (info.2 ▸ List.getElem_mem info.1)
  have back := (raw_gate C.gates (rightRow L) p _ gate).symm.trans base
  change op.eval (ins.map (atGate N p V))=false at back
  rcases facts.1 with isAnd|isOr
  · change op=GateOp.and at isAnd
    subst op
    cases ins with
    | nil => simp [GateOp.eval] at back
    | cons i rest =>
      cases rest with
      | nil =>
        refine ⟨by simp [twoDark],?_⟩
        intro t ht lt lit
        obtain rfl : t=i := by simpa using ht
        simp [GateOp.eval,atGate,lt,lit,V] at back
      | cons j rest =>
        cases rest with
        | cons k rem => simp at facts
        | nil =>
          obtain ⟨il,jl⟩ : i<N+p ∧ j<N+p := by
            have h := (raw_gate C.gates (two u r) p _ gate).symm.trans yes
            have active : atGate N p X i=true ∧ atGate N p X j=true := by simpa [GateOp.eval,X] using h
            constructor <;> by_contra no <;> simp [atGate,no] at active
          have dy := clean u ul r edge p i j gate base yes
          change atGate N p Y i=true ∨ atGate N p Y j=true at dy
          simp only [atGate,ite_eq_left il,ite_eq_left jl] at dy
          have blk : (V i && V j)=false := by simpa [GateOp.eval,atGate,il,jl] using back
          have enable : (V i=true → Y i=true) ∧ (V j=true → Y j=true) := by
            rcases dy with h|h
            · have l := all i h
              simp_all
            · have l := all j h
              simp_all
          refine ⟨?_,?_⟩
          · intro d
            have di : V i=false := d.2.2 i (by simp)
            have dj : V j=false := d.2.2 j (by simp)
            rcases dy with h|h <;> simp_all
          · intro t ht _ active
            rcases (List.mem_cons.mp ht) with rfl|ht
            · exact enable.1 active
            · obtain rfl : t=j := by simpa using ht
              exact enable.2 active
  · change op=GateOp.or at isOr
    subst op
    refine ⟨by simp [twoDark],?_⟩
    intro i hi lt active
    have contradiction : GateOp.or.eval (ins.map (atGate N p V))=true :=
      List.any_eq_true.mpr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,by simpa [atGate,lt] using active⟩
    simp_all

end PEqualNP.Outside.Rectangles624

namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Chain588.Helpers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624 PEqualNP.Outside.Transpose602

private theorem operation_counts (C : Circuit) :
    (andIndices C).card+(orIndices C).card≤C.size := by
  classical
  have disj : Disjoint (andIndices C) (orIndices C) := by
    apply Finset.disjoint_left.mpr
    intro p ha ho
    obtain ⟨g,hg,op⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨j,hj,op'⟩ := (Finset.mem_filter.mp ho).2
    have equal := Option.some.inj (hg.symm.trans hj)
    simp_all
  have within : andIndices C ∪ orIndices C⊆Finset.range C.gates.length := by
    intro p hp
    rcases Finset.mem_union.mp hp with h|h <;> exact (Finset.mem_filter.mp h).1
  rw [← Finset.card_union_of_disjoint disj]
  simpa [Circuit.size] using Finset.card_le_card within

/-- The exact edge-plus-cover lower bound for C4-free bipartite graph circuits
that are syntactically linear in one side. Both gate types have separate bounds. -/
theorem one_sided_graph {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (M : Set ℕ) (mark : ∀ u∈L, u.val∈M) (closed : ClosedMarks N C M) (linear : OneMarked N C M) :
    ∃ T : Finset (Fin N), (∀ a b, G.Adj a b → a∈T ∨ b∈T) ∧ G.edgeSet.ncard+T.card≤C.size+1 := by
  obtain ⟨T,cover,ands⟩ := one_sided_and_cover G C c4 mono sem L bip M mark closed linear
  have ors := one_sided_or_count G C c4 mono L bip sem M mark closed linear
  have total := operation_counts C
  exact ⟨T,cover,by omega⟩

/-- It suffices to inspect three rows for each edge. A counterexample must have a
binary AND off on the entire right side that sees both operands turn on when the
left endpoint is added to its right singleton. -/
theorem collision_free_graph {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (hyp : NoEdgeCollision G C L) :
    ∃ T : Finset (Fin N), (∀ a b, G.Adj a b → a∈T ∨ b∈T) ∧ G.edgeSet.ncard+T.card≤C.size+1 := by
  obtain ⟨same,md,closed,linear,marked,sd⟩ := scalar_edges_linearization G C L bip mono sem
    (no_collision_scalar G C L bip mono hyp)
  obtain ⟨T,cov,lower⟩ := one_sided_graph G _ c4 md L bip sd _ marked closed linear
  exact ⟨T,cov,by simpa only [same] using lower⟩

theorem collision_of_counterexample {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N)) (C : Circuit)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (mono : Monotone2 C) (L : Finset (Fin N)) (bip : ∀ a b, G.Adj a b → (a∈L ↔ b∉L))
    (sem : ∀ x : Fin N→Bool, circuitFun N C x=true ↔ ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true)
    (k : ℕ) (cover : ∀ T : Finset (Fin N), (∀ a b, G.Adj a b → a∈T ∨ b∈T) → k≤T.card)
    (short : C.size+1<G.edgeSet.ncard+k) :
    ∃ u∈L, ∃ r, G.Adj u r ∧ ∃ p i j, C.gates[p]?=some ⟨GateOp.and,[i,j]⟩ ∧
      vl C.gates (rightRow L) (N+p)=false ∧ vl C.gates (two u r) (N+p)=true ∧
      atGate N p (vl C.gates (one r)) i=false ∧ atGate N p (vl C.gates (one r)) j=false := by
  classical
  have bad : ¬NoEdgeCollision G C L := by
    intro clean
    obtain ⟨T,cov,need⟩ := collision_free_graph G C c4 mono L bip sem clean
    have := cover T cov
    omega
  unfold NoEdgeCollision at bad
  push Not at bad
  obtain ⟨u,ul,r,edge,p,i,j,gate,baseline,active,both⟩ := bad
  exact ⟨u,ul,r,edge,p,i,j,gate,baseline,active,by simpa using both⟩

end PEqualNP.Outside.Rectangles624

#print axioms PEqualNP.Outside.Rectangles624.collision_free_graph
#print axioms PEqualNP.Outside.Rectangles624.collision_of_counterexample
