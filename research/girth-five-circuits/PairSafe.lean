import PEqualNP.Outside.L_meta_575

namespace PEqualNP.Outside.Chain588
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers

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
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers
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
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers
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
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers
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
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers
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
open PEqualNP.MetaComplexity.L575Proof.Helpers PEqualNP.MetaComplexity.L575Proof.Helpers.Readers
open PEqualNP.Outside.Chain588 PEqualNP.Outside.Charging624

private theorem dark_and {N : ℕ} (C : Circuit) (p : ℕ) (ins : List ℕ) (x : Fin N → Bool)
    (gate : C.gates[p]?=some ⟨GateOp.and,ins⟩) (i : ℕ) (mem : i∈ins)
    (dark : atGate N p (vl C.gates x) i=false) : vl C.gates x (N+p)=false := by
  cases yes : vl C.gates x (N+p) with
  | false => rfl
  | true =>
    rw [raw_gate _ _ _ _ gate] at yes
    have on := List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨i,mem,rfl⟩)
    simp_all

private theorem dark_or {N : ℕ} (C : Circuit) (p : ℕ) (ins : List ℕ) (x : Fin N → Bool)
    (gate : C.gates[p]?=some ⟨GateOp.or,ins⟩)
    (dark : ∀ i∈ins, atGate N p (vl C.gates x) i=false) : vl C.gates x (N+p)=false := by
  cases yes : vl C.gates x (N+p) with
  | false => rfl
  | true =>
    rw [raw_gate _ _ _ _ gate] at yes
    obtain ⟨_,mem,h⟩ := List.any_eq_true.mp yes
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
    have := dark i hi
    simp_all

private theorem narrow_operand {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N))
    (C : Circuit) (mono : Monotone2 C) (safe : PairSafe G C)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (p : ℕ) (ins : List ℕ) (gate : C.gates[p]?=some ⟨GateOp.and,ins⟩) :
    ∃ i∈ins, ¬Wide (operand N C p i) := by
  classical
  have h := List.getElem?_eq_some_iff.mp gate
  have len := (mono _ (h.2 ▸ List.getElem_mem h.1)).2
  have empty := and_support G C safe p _ gate rfl
  cases ins with
  | nil =>
    have on : vl C.gates (one (default : Fin N)) (N+p)=true := by rw [raw_gate _ _ _ _ gate]; rfl
    have mem := (wireSet_mem C (N+p) default).mpr on
    simp [empty] at mem
  | cons i rest =>
    cases rest with
    | nil =>
      use i, by simp
      rintro ⟨a,ha,_⟩
      have on : vl C.gates (one a) (N+p)=true := by
        rw [raw_gate _ _ _ _ gate]
        simpa [GateOp.eval] using (operand_mem C p i a).mp ha
      have mem := (wireSet_mem C (N+p) a).mpr on
      simp [empty] at mem
    | cons j rest =>
      cases rest with
      | cons _ _ => simp at len
      | nil =>
        by_cases small : ¬Wide (operand N C p i)
        · exact ⟨i,by simp,small⟩
        · push Not at small
          obtain ⟨a,ha,b,hb,ne⟩ := small
          refine ⟨j,by simp,?_⟩
          rintro ⟨c,hc,d,hd,cd⟩
          have edge {u v} (hu : u∈operand N C p i) (hv : v∈operand N C p j) : G.Adj u v :=
            safe_rect G C mono safe p i j gate ((operand_mem _ _ _ _).mp hu) ((operand_mem _ _ _ _).mp hv)
          exact cd ((c4 a c b d (edge ha hc) (edge hb hc).symm (edge hb hd)
            (edge ha hd).symm).resolve_left ne)

private theorem narrow_rule {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N))
    (C : Circuit) (mono : Monotone2 C) (safe : PairSafe G C)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (paid : Finset ℕ) (pays : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ →
      ¬Wide (wireSet N C (N+p)) → N+p∈paid)
    (w : ℕ) (nw : ¬Wide (wireSet N C w)) : ∃ s : KillStep (Fin N) w,
      KillRule (vl C.gates) (fun j => ¬Wide (wireSet N C j)) w s ∧
      ∀ a b, s=.both a b → w∈paid := by
  classical
  by_cases raw : w<N
  · refine ⟨.input ⟨w,raw⟩,?_,by simp⟩
    intro x dark
    simpa [vl_input _ _ _ raw] using dark
  obtain ⟨p,rfl⟩ : ∃ p, w=N+p := ⟨w-N,by omega⟩
  cases gate : C.gates[p]? with
  | none =>
    have beyond := List.getElem?_eq_none_iff.mp gate
    exact ⟨.empty,fun x => vl_beyond _ _ _ (by omega),by simp⟩
  | some g =>
    have h := List.getElem?_eq_some_iff.mp gate
    obtain ⟨op,ins⟩ := g
    have facts := mono _ (h.2 ▸ List.getElem_mem h.1)
    rcases facts.1 with isAnd|isOr
    · change op=GateOp.and at isAnd
      subst op
      obtain ⟨i,hi,small⟩ := narrow_operand G C mono safe c4 p ins gate
      by_cases valid : i<N+p
      · refine ⟨.copy ⟨i,valid⟩,⟨by simpa [operand,valid] using small,?_⟩,by simp⟩
        intro x dark
        exact dark_and C p ins x gate i hi (by simpa [atGate,valid] using dark)
      · refine ⟨.empty,?_,by simp⟩
        exact fun x => dark_and C p ins x gate i hi (by simp [atGate,valid])
    · change op=GateOp.or at isOr
      subst op
      have support := or_support (N:=N) C p ins gate
      have small {i} (hi : i∈ins) (valid : i<N+p) : ¬Wide (wireSet N C i) := by
        intro isWide
        have subset : wireSet N C i ⊆ wireSet N C (N+p) := by
          intro v hv
          rw [support]
          exact Finset.mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr hi,by simpa [operand,valid] using hv⟩
        obtain ⟨a,ha,b,hb,ne⟩ := isWide
        exact nw ⟨a,subset ha,b,subset hb,ne⟩
      have len := facts.2
      cases ins with
      | nil =>
        exact ⟨.empty,fun x => dark_or C p [] x gate (by simp),by simp⟩
      | cons i rest =>
        cases rest with
        | nil =>
          by_cases goodI : i<N+p
          · refine ⟨.copy ⟨i,goodI⟩,⟨small (by simp) goodI,?_⟩,by simp⟩
            intro x di
            exact dark_or C p [i] x gate (by simpa [atGate,goodI] using di)
          · exact ⟨.empty,fun x => dark_or C p [i] x gate (by simp [atGate,goodI]),by simp⟩
        | cons j rest =>
          cases rest with
          | cons _ _ => simp at len
          | nil =>
            by_cases goodI : i<N+p <;> by_cases goodJ : j<N+p
            · refine ⟨.both ⟨i,goodI⟩ ⟨j,goodJ⟩,
                ⟨small (by simp) goodI,small (by simp) goodJ,?_⟩,
                fun _ _ _ => pays p _ gate nw⟩
              intro x di dj
              apply dark_or C p [i,j] x gate
              intro k hk
              simp at hk
              rcases hk with rfl|rfl <;> simp [atGate,goodI,goodJ,di,dj]
            · refine ⟨.copy ⟨i,goodI⟩,⟨small (by simp) goodI,?_⟩,by simp⟩
              intro x di
              apply dark_or C p [i,j] x gate
              intro k hk
              simp at hk
              rcases hk with rfl|rfl <;> simp [atGate,goodI,goodJ,di]
            · refine ⟨.copy ⟨j,goodJ⟩,⟨small (by simp) goodJ,?_⟩,by simp⟩
              intro x dj
              apply dark_or C p [i,j] x gate
              intro k hk
              simp at hk
              rcases hk with rfl|rfl <;> simp [atGate,goodI,goodJ,dj]
            · refine ⟨.empty,?_,by simp⟩
              intro x
              apply dark_or C p [i,j] x gate
              intro k hk
              simp at hk
              rcases hk with rfl|rfl <;> simp [atGate,goodI,goodJ]

theorem narrow_or_cover {N : ℕ} [Inhabited (Fin N)] (G : SimpleGraph (Fin N))
    (C : Circuit) (mono : Monotone2 C) (safe : PairSafe G C)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (sem : ∀ x : Fin N → Bool, circuitFun N C x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true)
    (paid : Finset ℕ) (pays : ∀ p ins, C.gates[p]?=some ⟨GateOp.or,ins⟩ →
      ¬Wide (wireSet N C (N+p)) → N+p∈paid) :
    ∃ T : Finset (Fin N), (∀ i j, G.Adj i j → i∈T ∨ j∈T) ∧ T.card ≤ paid.card+1 := by
  classical
  let narrow (j : ℕ) := ¬Wide (wireSet N C j)
  let chooseStep (w : ℕ) : KillStep (Fin N) w := if h : narrow w then
    (narrow_rule G C mono safe c4 paid pays w h).choose else .empty
  have rule (w : ℕ) (h : narrow w) : KillRule (vl C.gates) narrow w (chooseStep w) := by
    simp only [chooseStep,dite_eq_left h]
    exact (narrow_rule G C mono safe c4 paid pays w h).choose_spec.1
  have charges (w : ℕ) (a b : Fin w) (eq : chooseStep w=.both a b) : w∈paid := by
    by_cases h : narrow w
    · simp only [chooseStep,dite_eq_left h] at eq
      exact (narrow_rule G C mono safe c4 paid pays w h).choose_spec.2 a b eq
    · simp [chooseStep,h] at eq
  have out : narrow C.output := by
    rintro ⟨a,ha,_⟩
    have on := (wireSet_mem _ _ _).mp ha
    have off := singleton_rejected G C sem a
    simp_all
  let T := killLeaves chooseStep C.output
  refine ⟨T,?_,kill_card chooseStep paid charges C.output⟩
  intro i j edge
  by_contra bad
  push Not at bad
  have on : circuitFun N C (two i j)=true := (sem _).mpr ⟨i,j,edge,by simp [two],by simp [two]⟩
  have off := kill_sound chooseStep (vl C.gates) narrow rule C.output out (two i j) (by
    intro t ht
    have ti : t≠i := fun e => bad.1 (e ▸ ht)
    have tj : t≠j := fun e => bad.2 (e ▸ ht)
    simp [two,ti,tj])
  exact Bool.noConfusion (on.symm.trans off)

end PEqualNP.Outside.Rectangles624
namespace PEqualNP.Outside.Rectangles624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Charging624

theorem no_square_of_girth {V : Type*} (G : SimpleGraph V)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (a b c d : V) (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a) :
    a=c ∨ b=d := by
  by_contra bad
  push Not at bad
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  have cyc : p.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).mpr
    refine ⟨?_,by simp [p]⟩
    simp [p,SimpleGraph.Walk.isPath_def]
    grind [ab.ne,bc.ne,cd.ne,da.ne]
  have := girth a p cyc
  simp [p] at this

/-- The exact girth-five circuit bound for circuits in which every AND output is
safe on inputs of Hamming weight at most two, with unrestricted depth and fanout. -/
theorem conditional608 (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (C : Circuit) (mono : Monotone2 C) (safe : PairSafe G C)
    (computes : circuitFun N C = (fun x => decide (∃ i j : Fin N, G.Adj i j ∧ x i=true ∧ x j=true))) :
    ∃ T : Finset (Fin N), (∀ i j, G.Adj i j → i∈T ∨ j∈T) ∧
      G.edgeFinset.card + T.card ≤ C.size+1 := by
  classical
  cases N with
  | zero =>
    use ∅
    refine ⟨fun i => Fin.elim0 i,?_⟩
    have no : G.edgeFinset=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e
      induction e using Sym2.inductionOn with
      | _ i j => exact Fin.elim0 i
    simp [no]
  | succ n =>
    let N := n+1
    let all := Finset.range C.gates.length
    let isAnd (p : ℕ) := ∃ g : Gate, C.gates[p]?=some g ∧ g.op=GateOp.and
    let A := all.filter isAnd
    let others := all.filter (fun p => ¬isAnd p)
    let broad (p : ℕ) := Wide (wireSet N C (N+p))
    let B := others.filter broad
    let S := others.filter (fun p => ¬broad p)
    have and_member (p) (g : Gate) (atP : C.gates[p]?=some g) (op : g.op=GateOp.and) :
        p∈A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp atP).1,⟨g,atP,op⟩⟩
    have or_member (p) (ins : List ℕ) (atP : C.gates[p]?=some ⟨GateOp.or,ins⟩) : p∈others := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp atP).1,?_⟩
      rintro ⟨g,hg,op⟩
      have := congrArg Gate.op (Option.some.inj (hg.symm.trans atP))
      simp_all
    have sem (x : Fin N → Bool) : circuitFun N C x=true ↔
        ∃ i j : Fin N, G.Adj i j ∧ x i=true ∧ x j=true := by
      rw [congrFun computes x]
      simp only [decide_eq_true_eq]
      rfl
    have c4 := no_square_of_girth G girth
    have edgeBound := safe_edge_count G C c4 mono safe sem A B and_member (fun p ins gate wide =>
      Finset.mem_filter.mpr ⟨or_member p ins gate,wide⟩)
    obtain ⟨T,cover,coverBound⟩ := narrow_or_cover G C mono safe c4 sem (S.image (N+·)) (fun p ins gate nw =>
      Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨or_member p ins gate,nw⟩,rfl⟩)
    have eq1 : A.card + others.card = all.card := Finset.card_filter_add_card_filter_not isAnd
    have eq2 : B.card + S.card = others.card := Finset.card_filter_add_card_filter_not broad
    have img : (S.image (N+·)).card≤S.card := Finset.card_image_le
    have used : all.card=C.size := by simp [all,Circuit.size]
    have edges : G.edgeSet.ncard=G.edgeFinset.card := by rw [← G.coe_edgeFinset,Set.ncard_coe_finset]
    use T,cover
    omega

end PEqualNP.Outside.Rectangles624
