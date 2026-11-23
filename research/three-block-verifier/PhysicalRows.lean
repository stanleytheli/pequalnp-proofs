import PEqualNP.Defs.TimeAlt
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.DependsOn

namespace StackTrace

variable {K A Q : Type} [DecidableEq K]

inductive Command (K A : Type) where
  | idle
  | push (k : K) (a : A)
  | pop (k : K)

structure Config (K A Q : Type) where
  state : Q
  stackContents : K → List A

structure Row (K A Q : Type) where
  state : Q
  action : Command K A
  top : K → Option Nat

abbrev Program (K A Q : Type) := Nat → Q → (K → Option A) → Q × Command K A
abbrev Trace (K A Q : Type) := Nat → Row K A Q

def pushPop (op : Command K A) (h : K → List A) : K → List A :=
  match op with
  | .idle => h
  | .push k a => Function.update h k (a :: h k)
  | .pop k => Function.update h k (h k).tail

def advance (M : Program K A Q) (t : Nat) (c : Config K A Q) : Config K A Q :=
  let op := M t c.state (fun k => (c.stackContents k).head?)
  ⟨op.1, pushPop op.2 c.stackContents⟩

def run (M : Program K A Q) (start : Q) : Nat → Config K A Q
  | 0 => ⟨start, fun _ => []⟩
  | t+1 => advance M t (run M start t)

def rank : Option Nat → Nat
  | none => 0
  | some j => j+1

/-- Dereferencing a persistent stack node inspects just the row at its push time. -/
def node (r : Trace K A Q) (k : K) : Option Nat → Option (A × Option Nat)
  | none => none
  | some j =>
    match (r j).action with
    | .push k' a =>
      if k = k' ∧ rank ((r j).top k) < j+1 then some (a,(r j).top k) else none
    | _ => none

private theorem node_older {r : Trace K A Q} {k : K} {p q : Option Nat} {a : A}
    (h : node r k p = some (a,q)) : rank q < rank p := by
  cases p with
  | none => simp [node] at h
  | some t =>
    cases ho : (r t).action with
    | idle | pop => simp [node,ho] at h
    | push k' a' =>
      simp only [node,ho] at h
      split at h
      next hp => cases h; exact hp.2
      next => contradiction

def decode (r : Trace K A Q) (k : K) (p : Option Nat) : List A :=
  match _hn : node r k p with
  | none => []
  | some (a,q) => a :: decode r k q
termination_by rank p
decreasing_by exact node_older _hn

@[simp] private theorem decode_none (r : Trace K A Q) (k : K) : decode r k none = [] := by
  rw [decode]; rfl

private theorem decode_head (r : Trace K A Q) (k : K) (p : Option Nat) :
    (decode r k p).head? = (node r k p).map Prod.fst := by
  rw [decode]
  cases h : node r k p <;> simp

private theorem decode_tail (r : Trace K A Q) (k : K) (p : Option Nat) :
    (decode r k p).tail = decode r k ((node r k p).bind Prod.snd) := by
  rw [decode]
  cases h : node r k p <;> simp

def pointerAdvance (r : Trace K A Q) (t : Nat) : K → Option Nat :=
  match (r t).action with
  | .idle => (r t).top
  | .push k _ => Function.update (r t).top k (some t)
  | .pop k => Function.update (r t).top k ((node r k ((r t).top k)).bind Prod.snd)

def Meets (r : Trace K A Q) (M : Program K A Q) (t : Nat) : Prop :=
  let op := M t (r t).state (fun k => (node r k ((r t).top k)).map Prod.fst)
  (∀ k, rank ((r t).top k) < t+1) ∧ (r t).action = op.2 ∧
    (r (t+1)).state = op.1 ∧ (r (t+1)).top = pointerAdvance r t

def configAt (r : Trace K A Q) (t : Nat) : Config K A Q :=
  ⟨(r t).state,fun k => decode r k ((r t).top k)⟩

theorem local_implies_step {r : Trace K A Q} {M : Program K A Q} {t : Nat}
    (h : Meets r M t) : configAt r (t+1) = advance M t (configAt r t) := by
  obtain ⟨older,hop,hs,hp⟩ := h
  simp only [configAt,advance,decode_head,←hop]
  congr 1
  funext k
  rw [hp]
  cases ha : (r t).action with
  | idle => simp [pointerAdvance,ha,pushPop]
  | push j a =>
    by_cases hh : k = j
    · subst j
      simp only [pointerAdvance,ha,Function.update_self,pushPop]
      have hn : node r k (some t) = some (a,(r t).top k) := by simp [node,ha,older]
      exact (by rw [decode]; generalize hh : node r k (some t) = xx; cases xx <;> simp_all)
    · simp [pointerAdvance,ha,pushPop,Function.update_of_ne hh]
  | pop j =>
    by_cases hh : k = j
    · subst j
      simp [pointerAdvance,ha,pushPop,decode_tail]
    · simp [pointerAdvance,ha,pushPop,Function.update_of_ne hh]

/-- Exact local checks determine the true terminal state and stacks. -/
theorem correct {r : Trace K A Q} {M : Program K A Q} {T : Nat} {start : Q}
    (initial : (r 0).state = start) (empty : ∀ k, (r 0).top k = none)
    (h : ∀ t < T, Meets r M t) : configAt r T = run M start T := by
  induction T with
  | zero => simp [configAt,run,initial,empty]
  | succ T ih =>
    rw [local_implies_step (h T (Nat.lt_succ_self T))]
    exact congrArg (advance M T) (ih (fun t ht => h t (Nat.lt_succ_of_lt ht)))


private def tag (t : Nat) : Command K A → Command K (A × Nat)
  | .idle => .idle
  | .push k a => .push k (a,t)
  | .pop k => .pop k

private def values (xs : List (A × Nat)) : Option A := xs.head?.map Prod.fst
private def topId (xs : List (A × Nat)) : Option Nat := xs.head?.map Prod.snd

private def tagged (M : Program K A Q) (start : Q) : Nat → Config K (A × Nat) Q
  | 0 => ⟨start,fun _ => []⟩
  | t+1 =>
    let c := tagged M start t
    let op := M t c.state (fun k => values (c.stackContents k))
    ⟨op.1,pushPop (tag t op.2) c.stackContents⟩

private def opAt (M : Program K A Q) (start : Q) (t : Nat) :=
  let c := tagged M start t
  M t c.state (fun k => values (c.stackContents k))

def canonical (M : Program K A Q) (start : Q) (t : Nat) : Row K A Q :=
  let c := tagged M start t
  ⟨c.state,(opAt M start t).2,fun k => topId (c.stackContents k)⟩

private theorem tagged_next (M : Program K A Q) (start : Q) (t : Nat) :
    (tagged M start (t+1)).stackContents =
      pushPop (tag t (opAt M start t).2) (tagged M start t).stackContents := rfl

private def Linked (r : Trace K A Q) (k : K) : List (A × Nat) → Prop
  | [] => True
  | (a,j) :: rest => node r k (some j) = some (a,topId rest) ∧ Linked r k rest

private theorem oldTop {xs : List (A × Nat)} {t : Nat} (h : ∀ e ∈ xs, e.2 < t) :
    rank (topId xs) < t+1 := by
  cases xs with
  | nil => simp [rank,topId]
  | cons e es => simpa [rank,topId] using Nat.succ_lt_succ (h e (by simp))

private theorem tagged_correct (M : Program K A Q) (start : Q) (t : Nat) : ∀ k,
    Linked (canonical M start) k ((tagged M start t).stackContents k) ∧
      ∀ e ∈ (tagged M start t).stackContents k, e.2 < t := by
  induction t with
  | zero => simp [tagged,Linked]
  | succ t ih =>
    intro k
    obtain ⟨hlink,hold⟩ := ih k
    have old : ∀ e ∈ (tagged M start t).stackContents k, e.2 < t+1 :=
      fun e he => Nat.lt_succ_of_lt (hold e he)
    rw [tagged_next]
    cases ho : (opAt M start t).2 with
    | idle => exact ⟨hlink,old⟩
    | push j a =>
      by_cases h : k = j
      · subst j
        simp only [tag,pushPop,Function.update_self,Linked,List.mem_cons,forall_eq_or_imp]
        refine ⟨⟨?_,hlink⟩,Nat.lt_succ_self _,old⟩
        simp [node,canonical,ho,oldTop hold]
      · simpa [tag,pushPop,Function.update_of_ne h] using And.intro hlink old
    | pop j =>
      by_cases h : k = j
      · subst j
        simp only [tag,pushPop,Function.update_self]
        cases he : (tagged M start t).stackContents k with
        | nil => simp [Linked]
        | cons e es =>
          rw [he] at hlink old
          exact ⟨hlink.2, fun b hb => old b (List.mem_cons_of_mem _ hb)⟩
      · simpa [tag,pushPop,Function.update_of_ne h] using And.intro hlink old

private theorem linked_head {r : Trace K A Q} {k : K} {xs : List (A × Nat)}
    (h : Linked r k xs) : (node r k (topId xs)).map Prod.fst = values xs := by
  cases xs with
  | nil => rfl
  | cons e es => simp [topId,values,h.1]

private theorem linked_tail {r : Trace K A Q} {k : K} {xs : List (A × Nat)}
    (h : Linked r k xs) : (node r k (topId xs)).bind Prod.snd = topId xs.tail := by
  cases xs with
  | nil => rfl
  | cons e es => simp [topId,h.1]

theorem canonical_meets (M : Program K A Q) (start : Q) (t : Nat) :
    Meets (canonical M start) M t := by
  have get (k : K) := tagged_correct M start t k
  have equivalent (k : K) :
      (node (canonical M start) k ((canonical M start t).top k)).map Prod.fst =
        values ((tagged M start t).stackContents k) := linked_head (get k).1
  simp only [Meets,equivalent]
  refine ⟨fun k => oldTop (get k).2,rfl,rfl,?_⟩
  funext k
  change topId ((tagged M start (t+1)).stackContents k) = _
  rw [tagged_next]
  cases ho : (opAt M start t).2 with
  | idle => simp [tag,pushPop,pointerAdvance,canonical,ho]
  | push j a =>
    by_cases h : k = j
    · subst j; simp [tag,pushPop,pointerAdvance,canonical,ho,topId]
    · simp [tag,pushPop,pointerAdvance,canonical,ho,Function.update_of_ne h]
  | pop j =>
    by_cases h : k = j
    · subst j
      simp only [tag,pushPop,Function.update_self,pointerAdvance,canonical,ho]
      exact (linked_tail (get k).1).symm
    · simp [tag,pushPop,pointerAdvance,canonical,ho,Function.update_of_ne h]

theorem accepts_iff_trace (M : Program K A Q) (start : Q) (T : Nat) (accept : Q → Prop) :
    accept (run M start T).state ↔
      ∃ r : Trace K A Q, (r 0).state = start ∧ (∀ k, (r 0).top k = none) ∧
        accept (r T).state ∧ ∀ t < T, Meets r M t := by
  constructor
  · intro ha
    let r := canonical M start
    have hs : (r 0).state = start := rfl
    have he : ∀ k, (r 0).top k = none := fun _ => rfl
    have hm : ∀ i < T, Meets r M i := fun i _ => canonical_meets M start i
    have hcfg := correct hs he hm
    have hv : (r T).state = (run M start T).state := congrArg Config.state hcfg
    exact ⟨r,hs,he,by rwa [hv],hm⟩
  · rintro ⟨r,hs,he,ha,hm⟩
    exact congrArg Config.state (correct hs he hm) ▸ ha


theorem observed_iff_trace (M : Program K A Q) (start : Q) (T : Nat)
    (accept : Q → (K → Option A) → Prop) :
    accept (run M start T).state (fun k => ((run M start T).stackContents k).head?) ↔
      ∃ r : Trace K A Q, (r 0).state = start ∧ (∀ k, (r 0).top k = none) ∧
        accept (r T).state (fun k => (node r k ((r T).top k)).map Prod.fst) ∧
        ∀ t < T, Meets r M t := by
  let Test (c : Config K A Q) := accept c.state (fun k => (c.stackContents k).head?)
  have obs (r : Trace K A Q) : Test (configAt r T) ↔
      accept (r T).state (fun k => (node r k ((r T).top k)).map Prod.fst) := by
    simp only [Test,configAt,decode_head]
  constructor
  · intro ha
    let r := canonical M start
    have hs : (r 0).state = start := rfl
    have he : ∀ k, (r 0).top k = none := fun _ => rfl
    have hm : ∀ i < T, Meets r M i := fun i _ => canonical_meets M start i
    exact ⟨r,hs,he,(obs r).mp ((correct hs he hm).symm ▸ (show Test (run M start T) from ha)),hm⟩
  · rintro ⟨r,hs,he,ha,hm⟩
    exact (correct hs he hm) ▸ (obs r).mpr ha

end StackTrace
namespace StackTrace.Atomic

open Turing
variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

private abbrev Control (Γ : K → Type) (Λ σ : Type) := Option (TM2.Stmt Γ Λ σ) × σ
private abbrev Stk (Γ : K → Type) := (k : K) → List (Γ k)
private abbrev ACfg (Γ : K → Type) (Λ σ : Type) := Config K (Sigma Γ) (Control Γ Λ σ)

def castSymbol (k : K) : Option (Sigma Γ) → Option (Γ k)
  | none => none
  | some ⟨j,a⟩ => if h : j = k then some (h ▸ a) else none

def compile (m : Λ → TM2.Stmt Γ Λ σ) : Program K (Sigma Γ) (Control Γ Λ σ) :=
  fun _ ⟨pc,v⟩ head =>
    match pc with
    | none => ((none,v),.idle)
    | some (.push k f q) => ((some q,v),.push k ⟨k,f v⟩)
    | some (.peek k f q) => ((some q,f v (castSymbol k (head k))),.idle)
    | some (.pop k f q) => ((some q,f v (castSymbol k (head k))),.pop k)
    | some (.load f q) => ((some q,f v),.idle)
    | some (.branch f q q') => ((some (if f v then q else q'),v),.idle)
    | some (.goto f) => ((some (m (f v)),v),.idle)
    | some .halt => ((none,v),.idle)

def encodeStacks (s : Stk Γ) (k : K) : List (Sigma Γ) := (s k).map (Sigma.mk k)

def inside (q : TM2.Stmt Γ Λ σ) (v : σ) (S : Stk Γ) : ACfg Γ Λ σ :=
  ⟨(some q,v),encodeStacks S⟩

def encodeConfig (m : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : ACfg Γ Λ σ :=
  ⟨(c.l.map m,c.var),encodeStacks c.stk⟩

private theorem encUpdate (S : Stk Γ) (k : K) (xs : List (Γ k)) :
    encodeStacks (Function.update S k xs) =
      Function.update (encodeStacks S) k (xs.map (Sigma.mk k)) := by
  funext j
  by_cases he : j = k
  · subst j; simp [encodeStacks]
  · simp [encodeStacks,Function.update_of_ne he]

private theorem encHead (S : Stk Γ) (k : K) :
    castSymbol k (encodeStacks S k).head? = (S k).head? := by
  cases h : S k <;> simp [encodeStacks,h,castSymbol]

private theorem castMapHead (k : K) (o : Option (Γ k)) :
    castSymbol k (o.map (Sigma.mk k)) = o := by
  cases o <;> simp [castSymbol]

def depth : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => depth q + 1
  | .branch _ q q' => max (depth q) (depth q') + 1
  | .goto _ | .halt => 1

abbrev micro (m : Λ → TM2.Stmt Γ Λ σ) : ACfg Γ Λ σ → ACfg Γ Λ σ := advance (compile m) 0

/-- One Mathlib TM2 label executes a finite syntax tree. Each atomic instruction of this tree
requires one of the pointer-trace ticks, independent of the contents of the stacks. -/
theorem compile_stmt (m : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : Stk Γ) :
    ∃ ticks ≤ depth q, (micro m)^[ticks] (inside q v S) = encodeConfig m (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    obtain ⟨n,hn,he⟩ := ih v (Function.update S k (f v :: S k))
    refine ⟨n+1,Nat.succ_le_succ hn,?_⟩
    rw [Function.iterate_succ_apply]
    simpa [micro,advance,compile,inside,encUpdate,encodeStacks,pushPop] using he
  | peek k f q ih =>
    obtain ⟨n,hn,he⟩ := ih (f v (S k).head?) S
    refine ⟨n+1,Nat.succ_le_succ hn,?_⟩
    rw [Function.iterate_succ_apply]
    simpa [micro,advance,compile,inside,pushPop,encHead] using he
  | pop k f q ih =>
    obtain ⟨n,hn,he⟩ := ih (f v (S k).head?) (Function.update S k (S k).tail)
    refine ⟨n+1,Nat.succ_le_succ hn,?_⟩
    rw [Function.iterate_succ_apply]
    simpa [micro,advance,compile,inside,encUpdate,pushPop,encHead,encodeStacks,castMapHead] using he
  | load f q ih =>
    obtain ⟨n,hn,he⟩ := ih (f v) S
    exact ⟨n+1,Nat.succ_le_succ hn,he⟩
  | branch f q q' ih ih' =>
    cases hh : f v with
    | true =>
      obtain ⟨n,hn,he⟩ := ih v S
      refine ⟨n+1,Nat.succ_le_succ (hn.trans (le_max_left _ _)),?_⟩
      rw [Function.iterate_succ_apply]
      simpa [micro,advance,compile,inside,hh,pushPop] using he
    | false =>
      obtain ⟨n,hn,he⟩ := ih' v S
      refine ⟨n+1,Nat.succ_le_succ (hn.trans (le_max_right _ _)),?_⟩
      rw [Function.iterate_succ_apply]
      simpa [micro,advance,compile,inside,hh,pushPop] using he
  | goto f => exact ⟨1,le_rfl,rfl⟩
  | halt => exact ⟨1,le_rfl,rfl⟩


private theorem compile_step (m : Λ → TM2.Stmt Γ Λ σ) (B : Nat)
    (budget : ∀ l, depth (m l) ≤ B) (a b : TM2.Cfg Γ Λ σ) (h : TM2.step m a = some b) :
    ∃ n ≤ B, (micro m)^[n] (encodeConfig m a) = encodeConfig m b := by
  obtain ⟨l,v,S⟩ := a
  cases l with
  | none => simp at h
  | some l =>
    have he : TM2.stepAux (m l) v S = b := Option.some.inj h
    subst b
    obtain ⟨n,hn,hs⟩ := compile_stmt m (m l) v S
    exact ⟨n,hn.trans (budget l),hs⟩

private theorem compile_iterate (m : Λ → TM2.Stmt Γ Λ σ) (B : Nat)
    (budget : ∀ l, depth (m l) ≤ B) (a : TM2.Cfg Γ Λ σ) (n : Nat) (b : TM2.Cfg Γ Λ σ)
    (h : (flip bind (TM2.step m))^[n] (some a) = some b) :
    ∃ k ≤ B*n, (micro m)^[k] (encodeConfig m a) = encodeConfig m b := by
  induction n generalizing b with
  | zero => cases h; exact ⟨0,Nat.zero_le _,rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (flip bind (TM2.step m))^[n] (some a) with
    | none => rw [hp] at h; contradiction
    | some c =>
      have hc : TM2.step m c = some b := by rwa [hp] at h
      obtain ⟨i,hi,h1⟩ := ih c hp
      obtain ⟨j,hj,h2⟩ := compile_step m B budget c b hc
      exact ⟨j+i, by rw [Nat.mul_succ]; omega, by rw [Function.iterate_add_apply,h1,h2]⟩

noncomputable def overhead (tm : FinTM2) : Nat :=
  let _ := tm.ΛFin
  Finset.univ.sup fun l => depth (tm.m l)

/-- A successful run in Mathlib's *actual* FinTM2 model has an atomic realization
at the stated uniform horizon. Halting is absorbing in the compiled interpreter. -/
theorem finite_simulation (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁))
    (t : Nat) (h : TM2OutputsInTime tm x (some y) t) :
    (micro tm.m)^[overhead tm*t] (encodeConfig tm.m (initList tm x)) =
      encodeConfig tm.m (haltList tm y) := by
  let _ := tm.ΛFin
  have hb (l : tm.Λ) : depth (tm.m l) ≤ overhead tm := by
    unfold overhead
    exact Finset.le_sup (f := fun l => depth (tm.m l)) (Finset.mem_univ l)
  obtain ⟨n,hn,he⟩ := compile_iterate tm.m (overhead tm) hb
    (initList tm x) h.steps (haltList tm y) h.evals_in_steps
  have hnt : n ≤ overhead tm*t := hn.trans (Nat.mul_le_mul_left _ h.steps_le_m)
  have fixed : micro tm.m (encodeConfig tm.m (haltList tm y)) = encodeConfig tm.m (haltList tm y) := rfl
  rw [show overhead tm*t = (overhead tm*t-n)+n by omega,Function.iterate_add_apply,he]
  exact Function.iterate_fixed fixed _


def initialControl (tm : FinTM2) : Control tm.Γ tm.Λ tm.σ :=
  (some (tm.m tm.main),tm.initialState)

/-- Input cells are pushed from right to left before executing the compiled program. -/
def loadAndRun (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    Program tm.K (Sigma tm.Γ) (Control tm.Γ tm.Λ tm.σ) :=
  fun t q heads =>
    if hi : t < x.reverse.length then (q,.push tm.k₀ ⟨tm.k₀,x.reverse[t]⟩)
    else compile tm.m t q heads

private def inputCells (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) : tm.K → List (Sigma tm.Γ) :=
  Function.update (fun _ => []) tm.k₀ (xs.map (Sigma.mk tm.k₀))

private theorem consInput (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (a : tm.Γ tm.k₀) :
    pushPop (.push tm.k₀ ⟨tm.k₀,a⟩) (inputCells tm x) = inputCells tm (a::x) := by
  funext k
  by_cases he : k = tm.k₀
  · subst k; simp [inputCells,pushPop]
  · simp [inputCells,pushPop,Function.update_of_ne he]

private theorem load_prefix (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (i : Nat)
    (hi : i ≤ x.reverse.length) :
    run (loadAndRun tm x) (initialControl tm) i =
      ⟨initialControl tm, inputCells tm (x.reverse.take i).reverse⟩ := by
  induction i with
  | zero =>
    simp only [run,List.take_zero,List.reverse_nil]
    congr 1
    funext k
    by_cases he : k = tm.k₀ <;> simp [inputCells,he,Function.update_of_ne]
  | succ i ih =>
    have hlt : i < x.reverse.length := by omega
    rw [run,ih hlt.le,List.take_succ_eq_append_getElem hlt]
    simp only [advance,loadAndRun,hlt,dite_true,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,consInput]

private theorem initial_cells (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    inputCells tm x = encodeStacks (initList tm x).stk := by
  funext k
  by_cases h : k = tm.k₀
  · subst k; simp [inputCells,encodeStacks,initList]
  · simp [inputCells,encodeStacks,initList,h]

theorem after_load (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (d : Nat) :
    run (loadAndRun tm x) (initialControl tm) (x.length + d) =
      (micro tm.m)^[d] (encodeConfig tm.m (initList tm x)) := by
  induction d with
  | zero =>
    have h := load_prefix tm x x.reverse.length le_rfl
    rw [List.take_length,List.reverse_reverse] at h
    simpa [initialControl,encodeConfig,initList,initial_cells] using h
  | succ d ih =>
    rw [Nat.add_succ,run,ih,Function.iterate_succ_apply']
    simp [advance,loadAndRun,compile,micro]

theorem loaded_simulation (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁))
    (t : Nat) (h : TM2OutputsInTime tm x (some y) t) :
    run (loadAndRun tm x) (initialControl tm) (x.length+overhead tm*t) =
      encodeConfig tm.m (haltList tm y) :=
  (after_load tm x _).trans (finite_simulation tm x y t h)

end StackTrace.Atomic
namespace StackTrace.Atomic

open Turing
variable {K Λ σ : Type} {Γ : K → Type}

/-- The syntax tree of each finite label supplies a fixed finite list of program sites. -/
def nodes : TM2.Stmt Γ Λ σ → List (TM2.Stmt Γ Λ σ)
  | t@(.push _ _ q) | t@(.peek _ _ q) | t@(.pop _ _ q) | t@(.load _ q) => t :: nodes q
  | t@(.branch _ q r) => t :: (nodes q ++ nodes r)
  | t@(.goto _) | t@(.halt) => [t]

private theorem in_nodes (q : TM2.Stmt Γ Λ σ) : q ∈ nodes q := by cases q <;> simp [nodes]

private theorem nodes_closed (root q : TM2.Stmt Γ Λ σ) (hq : q ∈ nodes root) : nodes q ⊆ nodes root := by
  induction root generalizing q with
  | push k f p ih | pop k f p ih | peek k f p ih | load f p ih =>
    rcases List.mem_cons.mp hq with rfl|hp
    · exact fun _ => id
    · exact fun _ h => List.mem_cons_of_mem _ (ih q hp h)
  | branch f p r ip ir =>
    rcases List.mem_cons.mp hq with rfl|h
    · exact fun _ => id
    · rcases List.mem_append.mp h with hp|hr
      · exact fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ (ip q hp h))
      · exact fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ (ir q hr h))
  | goto f | halt => obtain rfl := List.mem_singleton.mp hq; exact fun _ => id

noncomputable def choices (X : Type) [Fintype X] : List X := Finset.univ.toList

private theorem in_choices (X : Type) [Fintype X] (x : X) : x ∈ choices X := by simp [choices]

noncomputable def sites (tm : FinTM2) : List (TM2.Stmt tm.Γ tm.Λ tm.σ) :=
  let _ := tm.ΛFin
  (choices tm.Λ).flatMap fun l => nodes (tm.m l)

private theorem isRoot (tm : FinTM2) (l : tm.Λ) : tm.m l ∈ sites tm := by
  let _ := tm.ΛFin
  exact List.mem_flatMap.mpr ⟨l,in_choices _ _,in_nodes _⟩

private theorem site_closed (tm : FinTM2) {q : TM2.Stmt tm.Γ tm.Λ tm.σ} (hq : q ∈ sites tm) :
    nodes q ⊆ sites tm := by
  obtain ⟨l,hl,hq'⟩ := List.mem_flatMap.mp hq
  exact fun _ h => List.mem_flatMap.mpr ⟨l,hl,nodes_closed _ _ hq' h⟩

noncomputable def pushed (tm : FinTM2) : TM2.Stmt tm.Γ tm.Λ tm.σ → List (Sigma tm.Γ)
  | .push k f _ =>
    let _ := tm.σFin
    (choices tm.σ).map fun v => ⟨k,f v⟩
  | _ => []

noncomputable def alphabet (tm : FinTM2) : List (Sigma tm.Γ) :=
  let _ := tm.Γk₀Fin
  (choices (tm.Γ tm.k₀)).map (Sigma.mk tm.k₀) ++ (sites tm).flatMap (pushed tm)

private theorem sym_push (tm : FinTM2) (k : tm.K) (f : tm.σ → tm.Γ k)
    (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (h : .push k f q ∈ sites tm) :
    (⟨k,f v⟩ : Sigma tm.Γ) ∈ alphabet tm := by
  let _ := tm.σFin
  exact List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨.push k f q,h,List.mem_map.mpr ⟨v,in_choices _ _,rfl⟩⟩)

private theorem sym_input (tm : FinTM2) (b : tm.Γ tm.k₀) :
    (⟨tm.k₀,b⟩ : Sigma tm.Γ) ∈ alphabet tm := by
  let _ := tm.Γk₀Fin
  exact List.mem_append_left _ (List.mem_map.mpr ⟨b,in_choices _ _,rfl⟩)

private def GoodPC (tm : FinTM2) (pc : Option (TM2.Stmt tm.Γ tm.Λ tm.σ)) : Prop :=
  ∀ q, pc = some q → q ∈ sites tm

private def InAlphabet (tm : FinTM2) (op : Command tm.K (Sigma tm.Γ)) : Prop :=
  ∀ k a, op = .push k a → a ∈ alphabet tm

private theorem compile_closed (tm : FinTM2) (t : Nat) (q : Control tm.Γ tm.Λ tm.σ)
    (heads : tm.K → Option (Sigma tm.Γ)) (hq : GoodPC tm q.1) :
    GoodPC tm (compile tm.m t q heads).1.1 ∧ InAlphabet tm (compile tm.m t q heads).2 := by
  obtain ⟨pc,v⟩ := q
  cases pc with
  | none => simp [GoodPC,InAlphabet,compile]
  | some p =>
    have here := hq p rfl
    have subs := site_closed tm here
    cases p with
    | push k f q =>
      have hchild : q ∈ sites tm := subs (List.mem_cons_of_mem _ (in_nodes q))
      have hp := sym_push tm k f q v here
      simpa [compile,GoodPC,InAlphabet] using And.intro hchild hp
    | pop k f q | peek k f q | load f q =>
      have hchild : q ∈ sites tm := subs (List.mem_cons_of_mem _ (in_nodes q))
      simpa [compile,GoodPC,InAlphabet] using hchild
    | branch f q r =>
      have hl : q ∈ sites tm := subs (List.mem_cons_of_mem _ (List.mem_append_left _ (in_nodes q)))
      have hr : r ∈ sites tm := subs (List.mem_cons_of_mem _ (List.mem_append_right _ (in_nodes r)))
      cases h : f v <;> simp [compile,GoodPC,InAlphabet,h,hl,hr]
    | goto f => simp [compile,GoodPC,InAlphabet,isRoot]
    | halt => simp [compile,GoodPC,InAlphabet]

private theorem loaded_closed (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (t : Nat)
    (q : Control tm.Γ tm.Λ tm.σ) (heads : tm.K → Option (Sigma tm.Γ)) (hq : GoodPC tm q.1) :
    GoodPC tm (loadAndRun tm x t q heads).1.1 ∧ InAlphabet tm (loadAndRun tm x t q heads).2 := by
  unfold loadAndRun
  split
  · refine ⟨hq,?_⟩
    intro k a h
    cases h
    exact sym_input tm _
  · exact compile_closed tm t q heads hq

noncomputable def controls (tm : FinTM2) : List (Control tm.Γ tm.Λ tm.σ) :=
  let _ := tm.σFin
  (none::(sites tm).map some).flatMap fun pc => (choices tm.σ).map fun v => (pc,v)

private theorem control_mem (tm : FinTM2) (q : Control tm.Γ tm.Λ tm.σ) (h : GoodPC tm q.1) :
    q ∈ controls tm := by
  let _ := tm.σFin
  refine List.mem_flatMap.mpr ⟨q.1,?_,List.mem_map.mpr ⟨q.2,in_choices _ _,rfl⟩⟩
  cases e : q.1 with
  | none => exact List.mem_cons_self
  | some p => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h p e,rfl⟩)

theorem canonical_finite (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (t : Nat) :
    let r := canonical (loadAndRun tm x) (initialControl tm) t
    r.state ∈ controls tm ∧ InAlphabet tm r.action := by
  let M := loadAndRun tm x
  let r := canonical M (initialControl tm)
  have states (i : Nat) : GoodPC tm (r i).state.1 := by
    induction i with
    | zero => exact fun q e => (Option.some.inj e) ▸ isRoot tm tm.main
    | succ i ih =>
      have h := (canonical_meets M (initialControl tm) i).2.2.1
      change (r (i+1)).state = _ at h
      rw [h]
      exact (loaded_closed tm x i (r i).state _ ih).1
  refine ⟨control_mem tm _ (states t),?_⟩
  have h := (canonical_meets M (initialControl tm) t).2.1
  change (r t).action = _ at h
  change InAlphabet tm (r t).action
  rw [h]
  exact (loaded_closed tm x t (r t).state _ (states t)).2

end StackTrace.Atomic

namespace TimeChallenge

abbrev Word (s : Nat) := {bs : List Bool // bs.length = s}

def encode (d i : Nat) : List Bool := List.ofFn fun j : Fin d => i.testBit j.val

def decode (bs : List Bool) : Nat := (BitVec.ofBoolListLE bs).toNat

theorem decode_encode (d i : Nat) (hi : i < 2^d) : decode (encode d i) = i := by
  have len : (encode d i).length = d := by simp [encode]
  have bits : (BitVec.ofBoolListLE (encode d i)).cast len = BitVec.ofNat d i := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,BitVec.getLsbD_ofNat]
    simp [encode,List.getD,hj]
  have natEq := congrArg BitVec.toNat bits
  simpa [decode,Nat.mod_eq_of_lt hi] using natEq

def challenge (d T : Nat) {s : Nat} (bs : Word s) : Fin (T+1) :=
  let t := decode (bs.val.take d)
  if h : t < T+1 then ⟨t,h⟩ else ⟨0,Nat.zero_lt_succ _⟩

theorem challenge_surjective (d T s : Nat) (fit : d ≤ s) (enough : T < 2^d) :
    Function.Surjective (challenge d T (s := s)) := by
  intro t
  let pre := encode d t.val
  have hp : pre.length = d := by simp [pre,encode]
  let code : Word s := ⟨pre ++ List.replicate (s-d) false,by simp [hp]; omega⟩
  have take : code.val.take d = pre := by
    change (pre ++ List.replicate (s-d) false).take d = pre
    rw [←hp,List.take_left]
  have dec : decode (code.val.take d) = t.val := by
    rw [take]
    exact decode_encode _ _ (by have := t.isLt; omega)
  exact ⟨code,by simp [challenge,dec,t.isLt]⟩

end TimeChallenge

namespace StackTrace.Binary

structure Numbering (A : Type) where
  encode : A → Nat
  read : Nat → Option A

variable {K A Q : Type} {s : Nat}

structure Format (K A Q : Type) (s : Nat) where
  indexStack : K ≃ Fin s
  symbols : Numbering A
  controls : Numbering Q
  fallback : Q

namespace Format

variable (F : Format K A Q s)

def unrank : Nat → Option Nat
  | 0 => none
  | n+1 => some n

private theorem unrank_rank (p : Option Nat) : unrank (rank p) = p := by cases p <;> rfl

def fields (r : Row K A Q) : Nat → Nat
  | 0 => F.controls.encode r.state
  | 1 => match r.action with | .idle => 0 | .pop _ => 1 | .push _ _ => 2
  | 2 => match r.action with | .idle => 0 | .pop k | .push k _ => (F.indexStack k).val
  | 3 => match r.action with | .push _ a => F.symbols.encode a | _ => 0
  | j+4 => if hj : j < s then rank (r.top (F.indexStack.symm ⟨j,hj⟩)) else 0

def stackAt (k : Nat) : Option K := if h : k < s then some (F.indexStack.symm ⟨k,h⟩) else none

def restore (cols : Nat → Nat) : Row K A Q where
  state := (F.controls.read (cols 0)).getD F.fallback
  action := match cols 1 with
    | 1 => ((F.stackAt (cols 2)).map Command.pop).getD .idle
    | 2 => ((F.stackAt (cols 2)).bind fun k => (F.symbols.read (cols 3)).map (Command.push k)).getD .idle
    | _ => .idle
  top k := unrank (cols ((F.indexStack k).val+4))

def Supported (r : Row K A Q) : Prop :=
  F.controls.read (F.controls.encode r.state) = some r.state ∧
  ∀ k a, r.action = .push k a → F.symbols.read (F.symbols.encode a) = some a

private theorem stackAt_index (k : K) : F.stackAt (F.indexStack k).val = some k := by
  simp [stackAt,(F.indexStack k).isLt]

theorem restore_fields (r : Row K A Q) (h : F.Supported r) : F.restore (F.fields r) = r := by
  obtain ⟨q,op,top⟩ := r
  obtain ⟨hc,ha⟩ := h
  cases op with
  | idle => simp [restore,fields,hc,unrank_rank]
  | pop k => simp [restore,fields,hc,stackAt_index,unrank_rank]
  | push k a =>
    have hs := ha k a rfl
    simp [restore,fields,hc,hs,stackAt_index,unrank_rank]

/-- Store each of the fixed number of scalar fields in d little-endian bits. -/
def flatten (d : Nat) (cols : Nat → Nat) (j : Nat) : Bool := (cols (j/d)).testBit (j%d)

def extract (d : Nat) (bit : Nat → Bool) (k : Nat) : Nat :=
  TimeChallenge.decode (List.ofFn fun j : Fin d => bit (k*d+j.val))

theorem extract_flatten (d : Nat) (hd : 0 < d) (cols : Nat → Nat) (k : Nat)
    (h : cols k < 2^d) : extract d (flatten d cols) k = cols k := by
  have ha (j : Fin d) : (k*d+j.val)/d = k := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hd,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  have hb (j : Fin d) : (k*d+j.val)%d = j.val := by
    rw [Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  simp only [extract,flatten,ha,hb]
  exact TimeChallenge.decode_encode d _ h

theorem restore_bits (d : Nat) (hd : 0 < d) (r : Row K A Q) (h : F.Supported r)
    (bounds : ∀ k, F.fields r k < 2^d) :
    F.restore (extract d (flatten d (F.fields r))) = r := by
  have eq : extract d (flatten d (F.fields r)) = F.fields r :=
    funext fun k => extract_flatten d hd _ k (bounds k)
  rw [eq,F.restore_fields r h]

theorem fields_bound (r : Row K A Q) (d : Nat) (small : 2 < 2^d) (hk : s ≤ 2^d)
    (hc : F.controls.encode r.state < 2^d)
    (ha : ∀ k a, r.action = .push k a → F.symbols.encode a < 2^d)
    (ht : ∀ k, rank (r.top k) < 2^d) : ∀ j, F.fields r j < 2^d := by
  intro j
  match j with
  | 0 => exact hc
  | 1 => cases h : r.action <;> simp only [fields,h] <;> omega
  | 2 =>
    cases h : r.action with
    | idle => simp [fields,h]
    | pop k | push k a =>
      simpa only [fields,h] using Nat.lt_of_lt_of_le (F.indexStack k).isLt hk
  | 3 =>
    cases h : r.action with
    | idle | pop k => simp [fields,h]
    | push k a => simpa [fields,h] using ha k a h
  | j+4 =>
    by_cases h : j < s
    · simpa [fields,h] using ht (F.indexStack.symm ⟨j,h⟩)
    · simp [fields,h]

theorem restore_ext (a b : Nat → Nat) (h : ∀ j < 4+s, a j = b j) :
    F.restore a = F.restore b := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have he : (fun k => unrank (a ((F.indexStack k).val+4))) =
      (fun k => unrank (b ((F.indexStack k).val+4))) := by
    funext k
    rw [h _ (by have := (F.indexStack k).isLt; omega)]
  simp only [restore,h0,h1,h2,h3,he]

/-- Equality of only the defined row-bit positions suffices to reconstruct that row. -/
theorem restore_oracle (d : Nat) (hd : 0 < d) (r : Row K A Q) (h : F.Supported r)
    (bounds : ∀ k, F.fields r k < 2^d) (bits : Nat → Bool)
    (correct : ∀ j < (4+s)*d, bits j = flatten d (F.fields r) j) :
    F.restore (extract d bits) = r := by
  rw [← F.restore_bits d hd r h bounds]
  apply F.restore_ext
  intro j hj
  apply congrArg TimeChallenge.decode
  apply congrArg List.ofFn
  funext b
  apply correct
  calc
    j*d+b.val < j*d+d := Nat.add_lt_add_left b.isLt _
    _ = (j+1)*d := (Nat.succ_mul _ _).symm
    _ ≤ (4+s)*d := Nat.mul_le_mul_right d hj

end Format

end StackTrace.Binary
namespace StackTrace.Binary

open Turing

noncomputable def numberingOfList {A : Type} (ls : List A) : Numbering A := by
  classical
  exact ⟨fun a => ls.idxOf a,fun i => ls[i]?⟩

private theorem numbering_mem {A : Type} (ls : List A) (a : A) (h : a ∈ ls) :
    (numberingOfList ls).read ((numberingOfList ls).encode a) = some a := by
  classical
  exact List.getElem?_idxOf h

private theorem numbering_bound {A : Type} (ls : List A) (a : A) :
    (numberingOfList ls).encode a ≤ ls.length := by
  classical
  exact List.idxOf_le_length

noncomputable def physical (tm : FinTM2) :
    Format tm.K (Sigma tm.Γ) (Option (TM2.Stmt tm.Γ tm.Λ tm.σ) × tm.σ) (@Fintype.card tm.K tm.kFin) where
  indexStack := @Fintype.equivFin tm.K tm.kFin
  symbols := numberingOfList (Atomic.alphabet tm)
  controls := numberingOfList (Atomic.controls tm)
  fallback := Atomic.initialControl tm

/-- A true compiled computation admits a fixed-width binary row. The number of fields
depends only on the machine, even when an internal Mathlib stack alphabet is an infinite type. -/
theorem physical_row (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (t d : Nat) (hd : 0 < d)
    (hi : t < 2^d) (h2 : 2 < 2^d) (hk : @Fintype.card tm.K tm.kFin ≤ 2^d)
    (hq : (Atomic.controls tm).length < 2^d) (ha : (Atomic.alphabet tm).length < 2^d)
    (bits : Nat → Bool) :
    let r := canonical (Atomic.loadAndRun tm x) (Atomic.initialControl tm) t
    (∀ j < (4+@Fintype.card tm.K tm.kFin)*d, bits j = Format.flatten d ((physical tm).fields r) j) →
      (physical tm).restore (Format.extract d bits) = r := by
  let M := Atomic.loadAndRun tm x
  let r := canonical M (Atomic.initialControl tm) t
  obtain ⟨hstate,hact⟩ := Atomic.canonical_finite tm x t
  have supported : (physical tm).Supported r :=
    ⟨numbering_mem _ _ hstate,fun k a h => numbering_mem _ _ (hact k a h)⟩
  have bounds : ∀ j, (physical tm).fields r j < 2^d :=
    (physical tm).fields_bound r d h2 hk
      (Nat.lt_of_le_of_lt (numbering_bound _ _) hq)
      (fun k a _ => Nat.lt_of_le_of_lt (numbering_bound _ _) ha)
      (fun k => by have hp := (canonical_meets M (Atomic.initialControl tm) t).1 k; change rank (r.top k) < t+1 at hp; omega)
  exact (physical tm).restore_oracle d hd r supported bounds bits

end StackTrace.Binary
namespace StackTrace.Packed

open PEqualNP.Library

variable {K A Q : Type} [DecidableEq K]

abbrev Word (s : Nat) := {w : List Bool // w.length = s}

def zeroWord (s : Nat) : Word s := ⟨List.replicate s false,by simp⟩

private theorem altThree (s : Nat) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ a : Word s, ∀ b : Word s, ∃ c : Word s, P (a.1 ++ b.1 ++ c.1) := by
  classical
  simp only [Alt,List.append_nil,List.append_assoc,not_not]
  push Not
  constructor
  · rintro ⟨a,ha,h⟩
    refine ⟨⟨a,ha⟩,fun b => ?_⟩
    obtain ⟨c,hc,hp⟩ := h b.1 b.2
    exact ⟨⟨c,hc⟩,hp⟩
  · rintro ⟨a,h⟩
    refine ⟨a.1,a.2,fun b hb => ?_⟩
    obtain ⟨c,hp⟩ := h ⟨b,hb⟩
    exact ⟨c.1,c.2,hp⟩

def oneCheck (M : Program K A Q) (start : Q) (T : Nat)
    (accept : Q → (K → Option A) → Prop) (r : Trace K A Q) (i : Fin (T+1)) : Prop :=
  (r 0).state = start ∧ (∀ k, (r 0).top k = none) ∧
    accept (r T).state (fun k => (node r k ((r T).top k)).map Prod.fst) ∧
    (i.val < T → Meets r M i.val)

private theorem node_agree {r r' : Trace K A Q} {T : Nat}
    (he : ∀ i ≤ T, r i = r' i) (k : K) (p : Option Nat) (h : rank p ≤ T+1) :
    node r k p = node r' k p := by
  cases p with
  | none => rfl
  | some j =>
    have hm : j ≤ T := by simpa [rank] using h
    simp only [node,he j hm]

private theorem meets_agree {r r' : Trace K A Q} {T i : Nat} {M : Program K A Q}
    (he : ∀ j ≤ T, r j = r' j) (hi : i < T) (hc : Meets r' M i) : Meets r M i := by
  obtain ⟨old,hop,hstate,htop⟩ := hc
  have atNode (k : K) :
      node r k ((r' i).top k) = node r' k ((r' i).top k) :=
    node_agree he k _ ((old k).le.trans (by omega))
  have ptr : pointerAdvance r i = pointerAdvance r' i := by
    unfold pointerAdvance
    simp only [he i hi.le,atNode]
  simp only [Meets,he i hi.le,he (i+1) hi,atNode,ptr]
  exact ⟨old,hop,hstate,htop⟩

/-- Short codes need only represent the genuine time rows. Every other claimed row reader
is checked against the same local equations. The universal player can inspect every time. -/
theorem commit_iff (M : Program K A Q) (start : Q) (T s : Nat)
    (accept : Q → (K → Option A) → Prop)
    (reader : Word s → Trace K A Q) (challenge : Word s → Fin (T+1))
    (authentic : ∃ code, ∀ i ≤ T, reader code i = canonical M start i)
    (allTimes : Function.Surjective challenge) :
    accept (run M start T).state (fun k => ((run M start T).stackContents k).head?) ↔
      ∃ code : Word s, ∀ b : Word s, oneCheck M start T accept (reader code) (challenge b) := by
  constructor
  · intro ha
    obtain ⟨code,he⟩ := authentic
    have hinit : (canonical M start 0).state = start := rfl
    have hnil : ∀ k, (canonical M start 0).top k = none := fun _ => rfl
    have ham : ∀ i < T, Meets (canonical M start) M i := fun i _ => canonical_meets M start i
    have hcfg := correct hinit hnil ham
    have ha' : accept (configAt (canonical M start) T).state
        (fun k => ((configAt (canonical M start) T).stackContents k).head?) := by rwa [hcfg]
    refine ⟨code,fun b => ?_⟩
    have atT (k : K) : node (reader code) k ((canonical M start T).top k) =
        node (canonical M start) k ((canonical M start T).top k) :=
      node_agree he k _ ((canonical_meets M start T).1 k).le
    refine ⟨by simpa only [he 0 (Nat.zero_le T)] using hinit,
      fun k => by simpa only [he 0 (Nat.zero_le T)] using hnil k,?_,?_⟩
    · simpa only [he T le_rfl,atT,configAt,decode_head] using ha'
    · exact fun hi => meets_agree he hi (ham _ hi)
  · rintro ⟨code,h⟩
    obtain ⟨hstart,hempty,ha,_⟩ := h (zeroWord s)
    apply (observed_iff_trace M start T accept).mpr
    refine ⟨reader code,hstart,hempty,ha,?_⟩
    intro i hi
    obtain ⟨b,hb⟩ := allTimes ⟨i,Nat.lt_succ_of_lt hi⟩
    have hc := h b
    rw [hb] at hc
    exact hc.2.2.2 hi

/-- This is the project's exact `SigmaV 3` verifier interface. The remaining machine
obligation is a *single*, uniform linear-time checker for a decoded row and its stack links. -/
theorem sigmaV_of_rows (L : Language Bool) (s T : Nat → Nat)
    (M : List Bool → Program K A Q) (start : List Bool → Q)
    (accept : List Bool → Q → (K → Option A) → Prop)
    (semantic : ∀ x : List Bool, x ∈ L ↔ accept x (run (M x) (start x) (T x.length)).state
      (fun k => ((run (M x) (start x) (T x.length)).stackContents k).head?))
    (reader : (x : List Bool) → Word (s x.length) → Trace K A Q)
    (challenge : (x : List Bool) → Word (s x.length) → Fin (T x.length+1))
    (authentic : ∀ x, ∃ code, ∀ i ≤ T x.length, reader x code i = canonical (M x) (start x) i)
    (allTimes : ∀ x, Function.Surjective (challenge x))
    (R : Set (List Bool × List Bool)) (B : Nat)
    (checker : DecidableInTime encodePair R (fun l => B*l+B))
    (check_spec : ∀ (x : List Bool) (a b c : Word (s x.length)),
      (x,a.1 ++ b.1 ++ c.1) ∈ R ↔
        oneCheck (M x) (start x) (T x.length) (accept x) (reader x a) (challenge x b)) :
    L ∈ SigmaV 3 s := by
  refine ⟨R,B,checker,fun x => ?_⟩
  rw [semantic,commit_iff (M x) (start x) (T x.length) (s x.length) (accept x) (reader x) (challenge x) (authentic x) (allTimes x),altThree]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,fun b => ⟨zeroWord _,(check_spec _ _ _ _).mpr (ha b)⟩⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,fun b => ?_⟩
    obtain ⟨c,hc⟩ := ha b
    exact (check_spec x a b c).mp hc

/-- A circuit evaluation transcript may depend on the challenged time and occupy the third block. -/
theorem sigmaV_of_nondet_rows (L : Language Bool) (s T : Nat → Nat)
    (M : List Bool → Program K A Q) (start : List Bool → Q)
    (accept : List Bool → Q → (K → Option A) → Prop)
    (semantic : ∀ x : List Bool, x ∈ L ↔ accept x (run (M x) (start x) (T x.length)).state
      (fun k => ((run (M x) (start x) (T x.length)).stackContents k).head?))
    (reader : (x : List Bool) → Word (s x.length) → Trace K A Q)
    (challenge : (x : List Bool) → Word (s x.length) → Fin (T x.length+1))
    (authentic : ∀ x, ∃ code, ∀ i ≤ T x.length, reader x code i = canonical (M x) (start x) i)
    (allTimes : ∀ x, Function.Surjective (challenge x))
    (R : Set (List Bool × List Bool)) (B : Nat)
    (checker : DecidableInTime encodePair R (fun l => B*l+B))
    (check_spec : ∀ (x : List Bool) (a b : Word (s x.length)),
      oneCheck (M x) (start x) (T x.length) (accept x) (reader x a) (challenge x b) ↔
        ∃ c : Word (s x.length), (x,a.1 ++ b.1 ++ c.1) ∈ R) :
    L ∈ SigmaV 3 s := by
  refine ⟨R,B,checker,fun x => ?_⟩
  rw [semantic,commit_iff (M x) (start x) (T x.length) (s x.length) (accept x) (reader x) (challenge x) (authentic x) (allTimes x),altThree]
  exact exists_congr fun a => forall_congr' fun b => check_spec x a b

end StackTrace.Packed
namespace StackTrace.PhysicalSigma

open Turing PEqualNP.Library
open StackTrace.Binary

abbrev Decider (f : List Bool → Bool) :=
  TM2ComputableInTime (fun x : List Bool => x) Computability.encodeBool f

variable {f : List Bool → Bool} (c : Decider f)

def input (x : List Bool) := x.map c.inputAlphabet.invFun

def prog (x : List Bool) := Atomic.loadAndRun c.tm (input c x)

noncomputable def T (bound : Nat → Nat) (n : Nat) := n + Atomic.overhead c.tm * bound n

def accept (_ : Option (TM2.Stmt c.tm.Γ c.tm.Λ c.tm.σ) × c.tm.σ)
    (heads : c.tm.K → Option (Sigma c.tm.Γ)) : Prop :=
  heads c.tm.k₁ = some ⟨c.tm.k₁,c.outputAlphabet.invFun true⟩

theorem run_accept (bound : Nat → Nat) (ht : ∀ n, c.time n ≤ bound n) (x : List Bool) :
    f x = true ↔ let cfg := run (prog c x) (Atomic.initialControl c.tm) (T c bound x.length)
      accept c cfg.state (fun k => (cfg.stackContents k).head?) := by
  let out := (Computability.encodeBool (f x)).map c.outputAlphabet.invFun
  have h := c.outputsFun x
  have runOut : TM2OutputsInTime c.tm (input c x) (some out) (bound x.length) :=
    ⟨h.toEvalsTo,h.steps_le_m.trans (ht x.length)⟩
  have eq := Atomic.loaded_simulation c.tm _ _ _ runOut
  have ilen : (input c x).length = x.length := by simp [input]
  rw [ilen] at eq
  change f x = true ↔ (((run (Atomic.loadAndRun c.tm (input c x)) (Atomic.initialControl c.tm)
    (x.length+Atomic.overhead c.tm*bound x.length)).stackContents c.tm.k₁).head? = _)
  rw [eq]
  simp [Atomic.encodeConfig,Atomic.encodeStacks,haltList,out,Computability.encodeBool]

noncomputable def capacity (tm : FinTM2) (time : Nat) : Nat :=
  time + (Atomic.controls tm).length + (Atomic.alphabet tm).length + @Fintype.card tm.K tm.kFin + 3

noncomputable def width (tm : FinTM2) (time : Nat) := (capacity tm time).log2+1

private theorem width_spec (tm : FinTM2) (time : Nat) : capacity tm time < 2^(width tm time) :=
  (Nat.log2_lt (by unfold capacity; omega)).mp (Nat.lt_succ_self _)

noncomputable def genuineBit (x : List Bool) (time i j : Nat) : Bool :=
  let r := canonical (prog c x) (Atomic.initialControl c.tm) i
  Format.flatten (width c.tm time) ((physical c.tm).fields r) j

abbrev Oracle (s : Nat → Nat) := (x : List Bool) → Packed.Word (s x.length) → Nat → Nat → Bool

noncomputable def decodeTrace (s bound : Nat → Nat) (bits : Oracle s) (x : List Bool)
    (a : Packed.Word (s x.length)) : Trace c.tm.K (Sigma c.tm.Γ) (Option (TM2.Stmt c.tm.Γ c.tm.Λ c.tm.σ) × c.tm.σ) :=
  fun i => (physical c.tm).restore (Format.extract (width c.tm (T c bound x.length)) (bits x a i))

noncomputable def timeQuery (s bound : Nat → Nat) (x : List Bool) (b : Packed.Word (s x.length)) :=
  TimeChallenge.challenge (width c.tm (T c bound x.length)) (T c bound x.length) b

noncomputable def test (s bound : Nat → Nat) (bits : Oracle s) (x : List Bool) (a b : Packed.Word (s x.length)) : Prop :=
  Packed.oneCheck (prog c x) (Atomic.initialControl c.tm) (T c bound x.length) (accept c)
    (decodeTrace c s bound bits x a) (timeQuery c s bound x b)

/-- A decider in the project's machine model and a succinct reader for each honest input
suffice once an individual test can be verified by a single uniform linear-time machine. -/
theorem sigmaV_of_honest_bits (L : Language Bool) (hL : ∀ x, x ∈ L ↔ f x = true)
    (s bound : Nat → Nat) (ht : ∀ n, c.time n ≤ bound n)
    (room : ∀ n, width c.tm (T c bound n) ≤ s n) (bits : Oracle s)
    (honest : ∀ x : List Bool, ∃ a : Packed.Word (s x.length), ∀ i ≤ T c bound x.length,
      ∀ j < (4+@Fintype.card c.tm.K c.tm.kFin)*width c.tm (T c bound x.length),
        bits x a i j = genuineBit c x (T c bound x.length) i j)
    (R : Set (List Bool × List Bool)) (B : Nat)
    (checker : DecidableInTime encodePair R (fun l => B*l+B))
    (encoding : ∀ (x : List Bool) (a b : Packed.Word (s x.length)), test c s bound bits x a b ↔
      ∃ z : Packed.Word (s x.length), (x,a.val ++ b.val ++ z.val) ∈ R) : L ∈ SigmaV 3 s := by
  apply Packed.sigmaV_of_nondet_rows L s (T c bound) (prog c) (fun _ => Atomic.initialControl c.tm)
    (fun _ => accept c) (fun x => (hL x).trans (run_accept c bound ht x))
    (decodeTrace c s bound bits) (timeQuery c s bound) _ _ R B checker encoding
  · intro x
    obtain ⟨a,ha⟩ := honest x
    refine ⟨a,fun i hi => ?_⟩
    have big := width_spec c.tm (T c bound x.length)
    unfold capacity at big
    apply physical_row c.tm (input c x) i (width c.tm (T c bound x.length)) (Nat.zero_lt_succ _)
      (by omega) (by omega) (by omega) (by omega) (by omega) (bits x a i)
    exact ha i hi
  · intro x
    have big := width_spec c.tm (T c bound x.length)
    unfold capacity at big
    exact TimeChallenge.challenge_surjective _ _ _ (room _) (by omega)

end StackTrace.PhysicalSigma

#print axioms StackTrace.PhysicalSigma.sigmaV_of_honest_bits
