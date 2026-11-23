import PEqualNP.Defs
import PEqualNP.Library.Machines.ComposeRun
import PEqualNP.Library.Machines.FilterMap
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.DependsOn
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Finset.Fold
import Mathlib.Logic.Function.Iterate


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

namespace PushdownTime

variable {Q A : Type*}

/-- A stationary deterministic machine observes only the current state and the
top symbol. A transition replaces that symbol by a finite word. -/
abbrev Rules (Q A : Type*) := Q → Option A → Option (Q × List A)

inductive Halts (δ : Rules Q A) : Q → List A → ℕ → Prop where
  | done {q xs} (h : δ q xs.head?=none) : Halts δ q xs 0
  | tick {q xs r w n} (op : δ q xs.head?=some (r,w)) (later : Halts δ r (w++xs.tail) n) :
      Halts δ q xs (n+1)

/-- An isolated prefix stops when it first exhausts the prefix or when the
control halts. It cannot inspect the suffix. -/
inductive Prefix (δ : Rules Q A) : Q → List A → ℕ → Option Q → Prop where
  | boundary (q) : Prefix δ q [] 0 (some q)
  | done {q a xs} (h : δ q (some a)=none) : Prefix δ q (a::xs) 0 none
  | tick {q a xs r w n z} (op : δ q (some a)=some (r,w)) (later : Prefix δ r (w++xs) n z) :
      Prefix δ q (a::xs) (n+1) z

private theorem halt_unique {δ : Rules Q A} {q xs n} (h : Halts δ q xs n) {m} (k : Halts δ q xs m) : n=m := by
  induction h generalizing m with
  | done h =>
    cases k with
    | done => rfl
    | tick k _ => rw [h] at k; contradiction
  | tick op _ ih =>
    cases k with
    | done kh => rw [kh] at op; contradiction
    | tick ko kl =>
      have eq := Option.some.inj (ko.symm.trans op)
      cases eq
      exact congrArg Nat.succ (ih kl)

private theorem prefix_unique {δ : Rules Q A} {q xs n z} (h : Prefix δ q xs n z)
    {m r} (k : Prefix δ q xs m r) : n=m := by
  induction h generalizing m r with
  | boundary => cases k; rfl
  | done h =>
    cases k with
    | done => rfl
    | tick k _ => rw [h] at k; contradiction
  | tick op _ ih =>
    cases k with
    | done kh => rw [kh] at op; contradiction
    | tick ko kl =>
      have eq := Option.some.inj (ko.symm.trans op)
      cases eq
      exact congrArg Nat.succ (ih kl)

private def Rest (δ : Rules Q A) (y : List A) (whole spent : ℕ) : Option Q → Prop
  | none => whole=spent
  | some r => ∃ left, Halts δ r y left ∧ whole=spent+left

private theorem divide {δ : Rules Q A} {q s n} (h : Halts δ q s n) (x y : List A) (eq : s=x++y) :
    ∃ spent result, Prefix δ q x spent result ∧ Rest δ y n spent result := by
  induction h generalizing x y with
  | @done q s stop =>
    cases x with
    | nil => exact ⟨0,some q,.boundary _,0,by simpa [eq] using Halts.done stop,rfl⟩
    | cons a x =>
      subst s
      exact ⟨0,none,.done stop,rfl⟩
  | @tick q s r w n op later ih =>
    cases x with
    | nil =>
      exact ⟨0,some q,.boundary _,n+1,by simpa [eq] using Halts.tick op later,by omega⟩
    | cons a x =>
      subst s
      obtain ⟨spent,result,first,rest⟩ := ih (w++x) y (by simp [List.append_assoc])
      refine ⟨spent+1,result,.tick op first,?_⟩
      cases result with
      | none => exact congrArg Nat.succ rest
      | some r =>
        obtain ⟨left,last,combine⟩ := rest
        exact ⟨left,last,by omega⟩

private noncomputable def isolatedCost (δ : Rules Q A) (p : Q × A) : ℕ := by
  classical
  exact if h : ∃ n z, Prefix δ p.1 [p.2] n z then h.choose else 0

private theorem isolated_bound {δ : Rules Q A} {q a n z} (h : Prefix δ q [a] n z) :
    n = isolatedCost δ (q,a) := by
  classical
  have ok : ∃ t r, Prefix δ q [a] t r := ⟨n,z,h⟩
  rw [isolatedCost,dite_eq_left ok]
  exact prefix_unique h ok.choose_spec.choose_spec

private noncomputable def emptyCost (δ : Rules Q A) (q : Q) : ℕ := by
  classical
  exact if h : ∃ n, Halts δ q [] n then h.choose else 0

private theorem empty_bound {δ : Rules Q A} {q n} (h : Halts δ q [] n) : n=emptyCost δ q := by
  classical
  have ok : ∃ t, Halts δ q [] t := ⟨n,h⟩
  rw [emptyCost,dite_eq_left ok]
  exact halt_unique h ok.choose_spec

/-- The bound depends only on the machine, including the finite alphabet and control. -/
noncomputable def rate [Fintype Q] [Fintype A] (δ : Rules Q A) : ℕ :=
  max (Finset.univ.sup (isolatedCost δ)) (Finset.univ.sup (emptyCost δ))

theorem one_stack_linear [Fintype Q] [Fintype A] (δ : Rules Q A) (q : Q) (stack : List A)
    (n : ℕ) (run : Halts δ q stack n) : n ≤ rate δ*(stack.length+1) := by
  classical
  have estimate (p : Q × A) : isolatedCost δ p ≤ rate δ :=
    (Finset.le_sup (f:=isolatedCost δ) (Finset.mem_univ p)).trans (le_max_left _ _)
  have empty (q : Q) : emptyCost δ q ≤ rate δ :=
    (Finset.le_sup (f:=emptyCost δ) (Finset.mem_univ q)).trans (le_max_right _ _)
  induction stack generalizing q n with
  | nil => simpa [empty_bound run] using empty q
  | cons a stack ih =>
    obtain ⟨spent,result,head,tail⟩ := divide run [a] stack rfl
    have bound := (isolated_bound head).le.trans (estimate (q,a))
    rw [List.length_cons,Nat.mul_succ]
    cases result with
    | none => change n=spent at tail; omega
    | some q' =>
      obtain ⟨left,last,combine⟩ := tail
      have rest := ih q' left last
      omega

end PushdownTime

namespace PushdownTime.Multistack

variable {K A Q : Type*} [DecidableEq K]

inductive Action (K A : Type*) where
  | idle
  | push (i : K) (a : A)
  | pop (i : K)

abbrev Program (K A Q : Type*) := Q → (K → Option A) → Option (Q × Action K A)

structure Config (K A Q : Type*) where
  state : Q
  cells : K → List A

def heads (c : Config K A Q) := fun k=> (c.cells k).head?

def allows (i : K) : Action K A → Prop
  | .idle | .push _ _ => True
  | .pop j => i=j

def perform (c : Config K A Q) (q : Q) : Action K A → Config K A Q
  | .idle => ⟨q,c.cells⟩
  | .push k a => ⟨q,Function.update c.cells k (a::c.cells k)⟩
  | .pop k => ⟨q,Function.update c.cells k (c.cells k).tail⟩

/-- A phase runs to termination or until the next command intends to pop a
different stack. Pushes and peeks can address every stack throughout. -/
inductive Phase (P : Program K A Q) (i : K) : Config K A Q → ℕ → Config K A Q → Prop where
  | stop (c) (boundary : ∀ q act, P c.state (heads c)=some (q,act) → ¬allows i act) : Phase P i c 0 c
  | more {c q act n out} (op : P c.state (heads c)=some (q,act)) (ok : allows i act)
      (later : Phase P i (perform c q act) n out) : Phase P i c (n+1) out

private abbrev Control (K A Q : Type*) := Q × (K → Option A)

private def cache (c : Config K A Q) (i : K) : K → Option A := Function.update (heads c) i none

private def control (c : Config K A Q) (i : K) : Control K A Q := (c.state,cache c i)

private def project (P : Program K A Q) (i : K) : Rules (Control K A Q) A := fun c top =>
  match P c.1 (Function.update c.2 i top) with
  | none => none
  | some (q,.idle) => some ((q,c.2),top.toList)
  | some (q,.push k a) =>
    if k=i then some ((q,c.2),a::top.toList)
    else some ((q,Function.update c.2 k (some a)),top.toList)
  | some (q,.pop k) => if k=i then some ((q,c.2),[]) else none

private theorem head_reconstructed (c : Config K A Q) (i : K) :
    Function.update (cache c i) i (c.cells i).head? = heads c := by
  funext k
  by_cases e : k=i
  · subst k; simp [heads]
  · simp [cache,e]

private theorem head_tail (xs : List A) : xs.head?.toList++xs.tail=xs := by cases xs <;> rfl

private theorem cache_active {i : K} {c : Config K A Q} {s : List A} {q : Q} :
    cache (⟨q,Function.update c.cells i s⟩ : Config K A Q) i = cache c i := by
  funext j; by_cases e : j=i
  · subst j; simp [cache]
  · simp [cache,heads,e]

private theorem cache_other {i j : K} (different : j≠i) {a : A} {c : Config K A Q} {q : Q} :
    cache (perform c q (.push j a)) i = Function.update (cache c i) j (some a) := by
  funext k
  by_cases ki : k=i
  · subst k; simp [cache,different.symm]
  · by_cases kj : k=j
    · subst k; simp [cache,heads,perform,different]
    · simp [cache,heads,perform,ki,kj]

private theorem projects {P : Program K A Q} {i : K} {c t n} (run : Phase P i c n t) :
    Halts (project P i) (control c i) (c.cells i) n := by
  induction run with
  | stop c boundary =>
    apply Halts.done
    simp only [project,control,head_reconstructed]
    cases cmd : P c.state (heads c) with
    | none => rfl
    | some result =>
      obtain ⟨q,act⟩ := result
      have no := boundary q act cmd
      cases act with
      | idle | push => exact False.elim (no trivial)
      | pop k => simp [show k≠i from fun e=> no e.symm]
  | @more c q act n t op ok later ih =>
    cases act with
    | idle =>
      apply Halts.tick (r:=((q,cache c i) : Control K A Q)) (w:=(c.cells i).head?.toList)
      · simp [project,control,head_reconstructed,op]
      · rw [head_tail]; exact ih
    | push k a =>
      by_cases eq : k=i
      · subst k
        apply Halts.tick (r:=((q,cache c i) : Control K A Q)) (w:=a::(c.cells i).head?.toList)
        · simp [project,control,head_reconstructed,op]
        · simpa only [List.cons_append,head_tail,perform,control,cache_active,Function.update_self] using ih
      · apply Halts.tick (r:=((q,Function.update (cache c i) k (some a)) : Control K A Q)) (w:=(c.cells i).head?.toList)
        · simp [project,control,head_reconstructed,op,eq]
        · rw [head_tail]
          change Halts _ (q,Function.update (cache c i) k (some a)) _ _
          change Halts _ (q,cache (perform c q (.push k a)) i) ((perform c q (.push k a)).cells i) n at ih
          rw [cache_other eq] at ih
          simpa only [perform,Function.update_of_ne (Ne.symm eq)] using ih
    | pop k =>
      have eq : i=k := ok
      subst k
      apply Halts.tick (r:=((q,cache c i) : Control K A Q)) (w:=[])
      · simp [project,control,head_reconstructed,op]
      · simpa only [List.nil_append,control,perform,cache_active,Function.update_self] using ih

variable [Fintype K] [Fintype Q] [Fintype A]

noncomputable def perPhase (P : Program K A Q) : ℕ := Finset.univ.sup (fun i=>rate (project P i))

theorem phase_linear {P : Program K A Q} {i : K} {c t n} (run : Phase P i c n t) :
    n ≤ perPhase P*((c.cells i).length+1) := by
  have estimate := one_stack_linear _ _ _ _ (projects run)
  have cost : rate (project P i) ≤ perPhase P :=
    Finset.le_sup (f:=fun k=>rate (project P k)) (Finset.mem_univ i)
  exact estimate.trans (Nat.mul_le_mul_right _ cost)

def height (c : Config K A Q) : ℕ := ∑ k, (c.cells k).length

omit [Fintype Q] [Fintype A] in
private theorem height_step (c : Config K A Q) (q : Q) (act : Action K A) :
    height (perform c q act) ≤ height c+1 := by
  cases act with
  | idle => simp [height,perform]
  | push k a =>
    have eq : (fun j=>(Function.update c.cells k (a::c.cells k) j).length) =
        Function.update (fun j=>(c.cells j).length) k ((c.cells k).length+1) := by
      funext j; by_cases h : j=k <;> simp [h]
    simp only [height,perform,eq,Finset.sum_update_of_mem (Finset.mem_univ k)]
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ k) (fun j=>(c.cells j).length)]
    omega
  | pop k =>
    apply (Finset.sum_le_sum (g:=fun j=>(c.cells j).length) ?_).trans (Nat.le_succ _)
    intro j _
    by_cases e : j=k
    · subst j; simp [perform]
    · simp [perform,e]

omit [Fintype Q] [Fintype A] in
private theorem height_run {P : Program K A Q} {i : K} {c t n} (run : Phase P i c n t) :
    height t≤height c+n := by
  induction run with
  | stop => simp
  | @more c q act n t _ _ _ ih => have h:=height_step c q act; omega

/-- Concatenation of maximal phases. Actions that would pop another stack
belong to the following phase. -/
inductive Phases (P : Program K A Q) : Config K A Q → ℕ → ℕ → Config K A Q → Prop where
  | nil (c) : Phases P c 0 0 c
  | more {i c mid endp n p r} (first : Phase P i c n mid) (rest : Phases P mid p r endp) :
      Phases P c (p+1) (n+r) endp

/-- A fixed phase allowance bounds the length of every run by a linear function
of the initial storage. An exponential runtime requires the phase count to grow. -/
theorem full_time {P : Program K A Q} {c t p n} (runs : Phases P c p n t) (credit : ℕ)
    (enough : height c+1≤credit) : n+credit ≤ (perPhase P+1)^p*credit := by
  induction runs generalizing credit with
  | nil => simp
  | @more i c mid endp n p r first rest ih =>
    have estimate := phase_linear first
    have hsmall : (c.cells i).length ≤ height c :=
      Finset.single_le_sum (fun j _=>Nat.zero_le (c.cells j).length) (Finset.mem_univ i)
    have work : n≤perPhase P*credit := estimate.trans (Nat.mul_le_mul_left _ (by omega))
    have acc : credit+n≤(perPhase P+1)*credit := by rw [Nat.succ_mul]; omega
    have storage := height_run first
    have elapsed := ih (credit+n) (by omega)
    rw [pow_succ,Nat.mul_assoc]
    exact (show n+r+credit=r+(credit+n) by omega) ▸ elapsed.trans (Nat.mul_le_mul_left _ acc)

end PushdownTime.Multistack
namespace PushdownTime.Multistack

variable {K A Q : Type*} [DecidableEq K]

inductive Journey (P : Program K A Q) : Config K A Q → List (Action K A) → Config K A Q → Prop where
  | stop (c) (finished : P c.state (heads c)=none) : Journey P c [] c
  | more {c q act tail out} (op : P c.state (heads c)=some (q,act))
      (later : Journey P (perform c q act) tail out) : Journey P c (act::tail) out

/-- Counts changes in the sequence of pop stacks, starting with the supplied
stack. Reads and pushes do not contribute. -/
def switches : K → List (Action K A) → ℕ
  | _,[] => 0
  | i,.idle::xs | i,.push _ _::xs => switches i xs
  | i,.pop k::xs => if k=i then switches i xs else switches k xs+1

private theorem group_phases {P : Program K A Q} {c acts out} (run : Journey P c acts out) (i : K) :
    ∃ n mid r, Phase P i c n mid ∧ Phases P mid (switches i acts) r out ∧ n+r=acts.length := by
  induction run generalizing i with
  | stop c done =>
    exact ⟨0,c,0,.stop _ (fun _ _ eq=>by rw [done] at eq; contradiction),.nil _,rfl⟩
  | @more c q act tail out op later ih =>
    have same (allowed : allows i act) (count : switches i (act::tail)=switches i tail) :
        ∃ n mid r, Phase P i c n mid ∧ Phases P mid (switches i (act::tail)) r out ∧ n+r=(act::tail).length := by
      obtain ⟨n,mid,r,first,rest,length⟩ := ih i
      exact ⟨n+1,mid,r,.more op allowed first,count ▸ rest,by simp; omega⟩
    cases act with
    | idle | push => exact same trivial rfl
    | pop k =>
      by_cases eq : k=i
      · subst k; exact same rfl (by simp [switches])
      · obtain ⟨n,mid,r,first,rest,length⟩ := ih k
        have stop : Phase P i c 0 c := .stop _ (by
          intro q' a eq'
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (op.symm.trans eq'))
          exact Ne.symm eq)
        have next : Phase P k c (n+1) mid := .more op rfl first
        refine ⟨0,c,n+1+r,stop,?_,by simp; omega⟩
        simpa [switches,eq] using Phases.more next rest

theorem chronological_phases {P : Program K A Q} {c acts out} (run : Journey P c acts out) (i : K) :
    Phases P c (switches i acts+1) acts.length out := by
  obtain ⟨n,mid,r,f,g,length⟩ := group_phases run i
  simpa only [length] using Phases.more f g

theorem switches_time [Fintype K] [Fintype Q] [Fintype A] {P : Program K A Q} {c acts out}
    (run : Journey P c acts out) (i : K) :
    acts.length+(height c+1) ≤ (perPhase P+1)^(switches i acts+1)*(height c+1) :=
  full_time (chronological_phases run i) _ le_rfl

end PushdownTime.Multistack
namespace StackTrace.Atomic

open Turing

/-- A genuine atomic walk has no padded ticks after the machine halts. -/
private inductive Walking (tm : FinTM2) : ACfg tm.Γ tm.Λ tm.σ → ℕ → ACfg tm.Γ tm.Λ tm.σ → Prop where
  | refl (c) : Walking tm c 0 c
  | next {c n out} (active : c.state.1.isSome) (rest : Walking tm (micro tm.m c) n out) :
      Walking tm c (n+1) out

private theorem walking_append {tm : FinTM2} {a b c n m} (f : Walking tm a n b) (g : Walking tm b m c) :
    Walking tm a (m+n) c := by
  induction f with
  | refl => simpa using g
  | next active _ ih => exact Walking.next active (ih g)

private theorem walking_statement (tm : FinTM2) (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : Stk tm.Γ) :
    ∃ k, 0<k ∧ Walking tm (inside q v S) k (encodeConfig tm.m (TM2.stepAux q v S)) := by
  induction q generalizing v S with
  | push i f q ih =>
    obtain ⟨n,_,w⟩ := ih v (Function.update S i (f v::S i))
    refine ⟨n+1,Nat.zero_lt_succ _,.next rfl ?_⟩
    simpa [micro,advance,compile,inside,encUpdate,encodeStacks,pushPop] using w
  | peek i f q ih =>
    obtain ⟨n,_,w⟩ := ih (f v (S i).head?) S
    refine ⟨n+1,Nat.zero_lt_succ _,.next rfl ?_⟩
    simpa [micro,advance,compile,inside,encHead,pushPop] using w
  | pop i f q ih =>
    obtain ⟨n,_,w⟩ := ih (f v (S i).head?) (Function.update S i (S i).tail)
    refine ⟨n+1,Nat.zero_lt_succ _,.next rfl ?_⟩
    simpa [micro,advance,compile,inside,encUpdate,pushPop,encHead,encodeStacks,castMapHead] using w
  | load f q ih =>
    obtain ⟨n,_,w⟩ := ih (f v) S
    exact ⟨n+1,Nat.zero_lt_succ _,.next rfl w⟩
  | branch f q r iq ir =>
    cases h : f v
    · obtain ⟨n,_,w⟩ := ir v S
      refine ⟨n+1,Nat.zero_lt_succ _,.next rfl ?_⟩
      simpa [micro,advance,compile,inside,h,pushPop] using w
    · obtain ⟨n,_,w⟩ := iq v S
      refine ⟨n+1,Nat.zero_lt_succ _,.next rfl ?_⟩
      simpa [micro,advance,compile,inside,h,pushPop] using w
  | goto f => exact ⟨1,by decide,.next rfl (.refl _)⟩
  | halt => exact ⟨1,by decide,.next rfl (.refl _)⟩

private theorem walking_macro (tm : FinTM2) (n : ℕ) {a b : tm.Cfg}
    (h : (flip bind tm.step)^[n] (some a)=some b) :
    ∃ k≥n, Walking tm (encodeConfig tm.m a) k (encodeConfig tm.m b) := by
  induction n generalizing b with
  | zero => cases h; exact ⟨0,le_rfl,.refl _⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases mid : (flip bind tm.step)^[n] (some a) with
    | none => rw [mid] at h; contradiction
    | some c =>
      obtain ⟨k,hk,before⟩ := ih mid
      have step : tm.step c=some b := by rwa [mid] at h
      obtain ⟨label,v,S⟩ := c
      cases label with
      | none => simp at step
      | some l =>
        have eq : TM2.stepAux (tm.m l) v S=b := Option.some.inj step
        subst b
        obtain ⟨j,hj,next⟩ := walking_statement tm (tm.m l) v S
        exact ⟨j+k,by omega,walking_append before next⟩

private abbrev Valid (tm : FinTM2) := {q : Control tm.Γ tm.Λ tm.σ // GoodPC tm q.1}

private noncomputable abbrev validFinite (tm : FinTM2) : Fintype (Valid tm) := by
  classical
  let s := (controls tm).toFinset
  let f : Valid tm → s := fun q=>⟨q.val,List.mem_toFinset.mpr (control_mem tm _ q.property)⟩
  exact Fintype.ofInjective f (fun a b e=>Subtype.ext (congrArg (fun z:s=>z.val) e))

private noncomputable abbrev oneAlphabet (tm : FinTM2) [Subsingleton tm.K] : Fintype (Sigma tm.Γ) := by
  let _ := tm.kFin
  let _ : ∀ i, Fintype (tm.Γ i) := fun i=>by
    have e : tm.k₀=i := Subsingleton.elim ..; rw [←e]; exact tm.Γk₀Fin
  infer_instance

private def oneRules (tm : FinTM2) : PushdownTime.Rules (Valid tm) (Sigma tm.Γ) := fun q top =>
  if q.val.1.isNone then none else
    let x := compile tm.m 0 q.val (fun _=>top)
    let next : Valid tm := ⟨x.1,(compile_closed tm 0 q.val (fun _=>top) q.property).1⟩
    match x.2 with
    | .idle => some (next,top.toList)
    | .push _ a => some (next,a::top.toList)
    | .pop _ => some (next,[])

private theorem wholeStack (tm : FinTM2) [Subsingleton tm.K] (c : ACfg tm.Γ tm.Λ tm.σ) :
    (fun _ : tm.K=>(c.stackContents tm.k₀).head?) = fun i=>(c.stackContents i).head? :=
  funext fun _=> congrArg (fun j=>(c.stackContents j).head?) (Subsingleton.elim ..)

private theorem local_head_tail {α : Type*} (s : List α) : s.head?.toList++s.tail=s := by
  cases s <;> rfl

private theorem one_halts {tm : FinTM2} [Subsingleton tm.K] {c n f} (run : Walking tm c n f)
    (good : GoodPC tm c.state.1) (halted : f.state.1=none) :
    PushdownTime.Halts (oneRules tm) ⟨c.state,good⟩ (c.stackContents tm.k₀) n := by
  induction run with
  | refl c =>
    apply PushdownTime.Halts.done
    simp [oneRules,halted]
  | @next c n out on _ ih =>
    let op := compile tm.m 0 c.state (fun i=>(c.stackContents i).head?)
    have legal : GoodPC tm op.1.1 := (compile_closed tm 0 _ _ good).1
    have after := ih legal halted
    have live : c.state.1.isNone=false := by cases e : c.state.1 <;> simp_all
    have view := wholeStack tm c
    let q' : Valid tm := ⟨op.1,legal⟩
    cases cmd : op.2 with
    | idle =>
      apply PushdownTime.Halts.tick (r:=q') (w:=(c.stackContents tm.k₀).head?.toList)
      · simp only [oneRules,live,Bool.false_eq_true,ite_false,view,
          show (compile tm.m 0 c.state _).2=.idle from cmd]
        rfl
      · rw [local_head_tail]
        simpa [micro,advance,op,show (compile tm.m 0 c.state _).2=.idle from cmd,pushPop,q'] using after
    | push i a =>
      apply PushdownTime.Halts.tick (r:=q') (w:=a::(c.stackContents tm.k₀).head?.toList)
      · simp only [oneRules,live,Bool.false_eq_true,ite_false,view,
          show (compile tm.m 0 c.state _).2=.push i a from cmd]
        rfl
      · rw [List.cons_append,local_head_tail]
        have eq : i=tm.k₀ := Subsingleton.elim ..
        subst i
        simpa [micro,advance,op,show (compile tm.m 0 c.state _).2=.push tm.k₀ a from cmd,pushPop,q'] using after
    | pop i =>
      apply PushdownTime.Halts.tick (r:=q') (w:=[])
      · simp only [oneRules,live,Bool.false_eq_true,ite_false,view,
          show (compile tm.m 0 c.state _).2=.pop i from cmd]
        rfl
      · have eq : i=tm.k₀ := Subsingleton.elim ..
        subst i
        simpa [micro,advance,op,show (compile tm.m 0 c.state _).2=.pop tm.k₀ from cmd,pushPop,q'] using after

/-- Every run of a fixed genuine single-stack FinTM2 which actually halts uses at
most a linear number of macrosteps. The bound is independent of any prior timer. -/
theorem single_stack_time (tm : FinTM2) [Subsingleton tm.K] :
    ∃ C : ℕ, ∀ (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (t : ℕ),
      Turing.TM2OutputsInTime tm x (some y) t →
      Nonempty (Turing.TM2OutputsInTime tm x (some y) (C*(x.length+1))) := by
  let _ := validFinite tm
  let _ := oneAlphabet tm
  refine ⟨PushdownTime.rate (oneRules tm),?_⟩
  intro x y t witnessed
  obtain ⟨k,microbound,walk⟩ := walking_macro tm witnessed.steps witnessed.evals_in_steps
  have init : GoodPC tm (encodeConfig tm.m (initList tm x)).state.1 :=
    fun q h=>(Option.some.inj h) ▸ isRoot tm tm.main
  have checked := one_halts walk init (show (encodeConfig tm.m (haltList tm y)).state.1=none from rfl)
  have bound := PushdownTime.one_stack_linear _ _ _ _ checked
  refine ⟨⟨⟨witnessed.steps,witnessed.evals_in_steps⟩,microbound.trans ?_⟩⟩
  simpa [encodeConfig,encodeStacks,initList] using bound

end StackTrace.Atomic
namespace StackTrace.Atomic

open Turing PushdownTime.Multistack

private abbrev Sym (tm : FinTM2) := {a : Sigma tm.Γ // a∈alphabet tm}

private noncomputable abbrev symbolFinite (tm : FinTM2) : Fintype (Sym tm) := by
  classical
  let s := (alphabet tm).toFinset
  let f : Sym tm → s := fun q=>⟨q.val,List.mem_toFinset.mpr q.property⟩
  exact Fintype.ofInjective f (fun a b e=>Subtype.ext (congrArg (fun z:s=>z.val) e))

private def asAction (tm : FinTM2) (act : Command tm.K (Sigma tm.Γ))
    (ok : InAlphabet tm act) : Action tm.K (Sym tm) :=
  match act with
  | .idle => .idle
  | .push k a => .push k ⟨a,ok k a rfl⟩
  | .pop k => .pop k

private def forgetAction (tm : FinTM2) : Action tm.K (Sym tm) → Command tm.K (Sigma tm.Γ)
  | .idle => .idle
  | .push k a => .push k a.val
  | .pop k => .pop k

private theorem as_forget (tm : FinTM2) (act) (ok) :
    forgetAction tm (asAction tm act ok)=act := by cases act <;> rfl

private abbrev PConfig (tm : FinTM2) := PushdownTime.Multistack.Config tm.K (Sym tm) (Valid tm)

private def program (tm : FinTM2) : PushdownTime.Multistack.Program tm.K (Sym tm) (Valid tm) := fun q hs =>
  if q.val.1.isNone then none else
    let h := fun k=>(hs k).map Subtype.val
    let x := compile tm.m 0 q.val h
    let ok := compile_closed tm 0 q.val h q.property
    some (⟨x.1,ok.1⟩,asAction tm x.2 ok.2)

private def erase (tm : FinTM2) (c : PConfig tm) : ACfg tm.Γ tm.Λ tm.σ :=
  ⟨c.state.val,fun k=>(c.cells k).map Subtype.val⟩

private theorem acfg_ext {tm : FinTM2} {c d : ACfg tm.Γ tm.Λ tm.σ} (hs : c.state=d.state)
    (hd : ∀ i, c.stackContents i=d.stackContents i) : c=d := by
  cases c; cases d; simp only [StackTrace.Config.mk.injEq]; exact ⟨hs,funext hd⟩

private def rawCommand (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) : Command tm.K (Sigma tm.Γ) :=
  (compile tm.m 0 c.state (fun i=>(c.stackContents i).head?)).2

private theorem faithful (tm : FinTM2) (c : PConfig tm) (active : (erase tm c).state.1.isSome) :
    ∃ q act, program tm c.state (heads c)=some (q,act) ∧
      forgetAction tm act=rawCommand tm (erase tm c) ∧
      erase tm (perform c q act)=micro tm.m (erase tm c) := by
  let h := fun k=>(c.cells k).head?.map Subtype.val
  let x := compile tm.m 0 c.state.val h
  have ok := compile_closed tm 0 c.state.val h c.state.property
  let q : Valid tm := ⟨x.1,ok.1⟩
  let act := asAction tm x.2 ok.2
  have on : c.state.val.1.isNone=false := by
    change c.state.val.1.isSome=true at active
    cases e : c.state.val.1 <;> simp_all
  have oe : (fun i=>((erase tm c).stackContents i).head?)=h := by
    funext i
    change ((c.cells i).map Subtype.val).head?= (c.cells i).head?.map Subtype.val
    rw [List.head?_map]
  refine ⟨q,act,by simp [program,on,heads,h,q,act,x],?_,?_⟩
  · change forgetAction tm (asAction tm x.2 ok.2)=_
    rw [as_forget]
    unfold rawCommand
    rw [oe]
    rfl
  · change erase tm (perform c q act) =
      ⟨(compile tm.m 0 (erase tm c).state _).1,pushPop (compile tm.m 0 (erase tm c).state _).2 (erase tm c).stackContents⟩
    rw [oe]
    change erase tm (perform c q act)=⟨x.1,pushPop x.2 (erase tm c).stackContents⟩
    generalize eq : x.2=cmd
    have actEq : act=asAction tm cmd (eq ▸ ok.2) := by subst cmd; rfl
    rw [actEq]
    cases cmd with
    | idle => rfl
    | push i a =>
      apply acfg_ext (tm:=tm)
      · rfl
      intro j
      by_cases same : j=i
      · subst j; simp [erase,perform,asAction,pushPop]
      · simp [erase,perform,asAction,pushPop,same]
    | pop i =>
      apply acfg_ext (tm:=tm)
      · rfl
      intro j
      by_cases same : j=i
      · subst j; simp [erase,perform,asAction,pushPop]; cases c.cells i <;> rfl
      · simp [erase,perform,asAction,pushPop,same]

private def initialP (tm : FinTM2) (input : List (tm.Γ tm.k₀)) : PConfig tm :=
  ⟨⟨initialControl tm,fun _ e=>(Option.some.inj e) ▸ isRoot tm tm.main⟩,
    Function.update (fun _=>[]) tm.k₀ (input.map fun a : tm.Γ tm.k₀=>(⟨⟨tm.k₀,a⟩,sym_input tm a⟩ : Sym tm))⟩

private theorem initial_erase (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    erase tm (initialP tm x)=encodeConfig tm.m (initList tm x) := by
  apply acfg_ext (tm:=tm)
  · rfl
  intro k
  by_cases eq : k=tm.k₀
  · subst k; simp [initialP,erase,encodeConfig,encodeStacks,initList]
    induction x with
    | nil => rfl
    | cons a x ih => exact congrArg (Sigma.mk tm.k₀ a :: ·) ih
  · simp [initialP,erase,encodeConfig,encodeStacks,initList,eq]

private theorem initial_size (tm : FinTM2) (x : List (tm.Γ tm.k₀)) :
    @height _ _ _ tm.kFin (initialP tm x)=x.length := by
  let _ := tm.kFin
  have eq : (fun k=>((initialP tm x).cells k).length)=Function.update (fun _=>0) tm.k₀ x.length := by
    funext j
    by_cases same : j=tm.k₀
    · subst j; simp [initialP]
    · simp [initialP,same]
  simp only [height,eq,Finset.sum_update_of_mem (Finset.mem_univ tm.k₀)]
  simp

/-- The chronological command stream of the real atomic interpreter. -/
def commandStream (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) : ℕ → List (Command tm.K (Sigma tm.Γ))
  | 0 => []
  | n+1 => rawCommand tm c :: commandStream tm (micro tm.m c) n

private theorem realize {tm : FinTM2} {c f n} (run : Walking tm c n f)
    (done : f.state.1=none) (s : PConfig tm) (start : erase tm s=c) :
    ∃ acts out, Journey (program tm) s acts out ∧ acts.map (forgetAction tm)=commandStream tm c n ∧
      acts.length=n ∧ erase tm out=f := by
  induction run generalizing s with
  | refl c =>
    refine ⟨[],s,.stop _ ?_,rfl,rfl,start⟩
    have h : s.state.val.1=none := (congrArg (fun x=>x.state.1) start).trans done
    simp [program,h]
  | @next c n f active rest ih =>
    obtain ⟨q,act,op,eq,next⟩ := faithful tm s (start ▸ active)
    rw [start] at eq next
    obtain ⟨acts,out,sub,raw,sz,final⟩ := ih done _ next
    exact ⟨act::acts,out,.more op sub,by simp [commandStream,eq,raw],by simp [sz],final⟩

/-- Counts pop-stack changes in a true machine trace. -/
def popChanges {K A : Type} [DecidableEq K] : K → List (Command K A) → ℕ
  | _,[] => 0
  | i,.idle::xs | i,.push _ _::xs => popChanges i xs
  | i,.pop k::xs => if k=i then popChanges i xs else popChanges k xs+1

private theorem pop_count (tm : FinTM2) (acts : List (Action tm.K (Sym tm))) (i : tm.K) :
    popChanges i (acts.map (forgetAction tm))=switches i acts := by
  induction acts generalizing i with
  | nil => rfl
  | cons act rest ih => cases act <;> simp [forgetAction,popChanges,switches,ih]

private theorem walk_eval {tm : FinTM2} {c f n} (walk : Walking tm c n f) :
    (micro tm.m)^[n] c=f := by
  induction walk with
  | refl => rfl
  | next active rest ih => rwa [Function.iterate_succ_apply]

/-- For the actual FinTM2, the time of a genuine terminating computation is
bounded exponentially in its number of pop-stack changes and linearly in its
initial input length. The machine-dependent base is uniform over inputs. -/
theorem real_phase_time (tm : FinTM2) :
    ∃ C : ℕ, ∀ (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (t : ℕ)
      (run : TM2OutputsInTime tm x (some y) t),
      ∃ n ≥ run.steps, (micro tm.m)^[n] (encodeConfig tm.m (initList tm x)) = encodeConfig tm.m (haltList tm y) ∧
        n+(x.length+1) ≤ C^(popChanges tm.k₀ (commandStream tm (encodeConfig tm.m (initList tm x)) n)+1)*(x.length+1) := by
  let _ := tm.kFin
  let _ := validFinite tm
  let _ := symbolFinite tm
  refine ⟨perPhase (program tm)+1,?_⟩
  intro x y t run
  obtain ⟨n,hn,walk⟩ := walking_macro tm run.steps run.evals_in_steps
  obtain ⟨acts,out,rel,eq,sz,_⟩ := realize walk rfl (initialP tm x) (initial_erase tm x)
  have bound := switches_time rel tm.k₀
  rw [initial_size,←pop_count,eq,sz] at bound
  exact ⟨n,hn,walk_eval walk,bound⟩

end StackTrace.Atomic
namespace StackTrace.Atomic

open Turing

private theorem commands_append (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (n t : ℕ) :
    commandStream tm c (n+t) = commandStream tm c n ++ commandStream tm ((micro tm.m)^[n] c) t := by
  induction n generalizing c with
  | zero => simp [commandStream]
  | succ n ih =>
    rw [Nat.succ_add,commandStream,commandStream,ih,Function.iterate_succ_apply]
    rfl

private theorem stopped_command (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (done : c.state.1=none) :
    rawCommand tm c=.idle ∧ micro tm.m c=c := by
  obtain ⟨⟨pc,v⟩,st⟩ := c
  change pc=none at done
  subst pc; exact ⟨rfl,rfl⟩

private theorem commands_stopped (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (done : c.state.1=none) (n : ℕ) :
    commandStream tm c n=List.replicate n .idle := by
  induction n with
  | zero => rfl
  | succ n ih => rw [commandStream,(stopped_command tm c done).1,(stopped_command tm c done).2,ih,List.replicate_succ]

private theorem empty_changes {K A : Type} [DecidableEq K] (i : K) (n : ℕ) :
    popChanges (A:=A) i (List.replicate n .idle)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,popChanges,ih]

private theorem changes_append_idle {K A : Type} [DecidableEq K] (i : K) (acts : List (Command K A)) (n : ℕ) :
    popChanges i (acts++List.replicate n .idle)=popChanges i acts := by
  induction acts generalizing i with
  | nil => exact empty_changes i n
  | cons act rest ih => cases act <;> simp [popChanges,ih]

private theorem clock_after (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (n t : ℕ) (past : n≤t)
    (done : ((micro tm.m)^[n] c).state.1=none) :
    popChanges tm.k₀ (commandStream tm c t)=popChanges tm.k₀ (commandStream tm c n) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le past
  rw [commands_append,commands_stopped tm _ done,changes_append_idle]

/-- An explicit number associated with the actual run up to the original supplied
clock. Extending the clock after termination has no effect on the pop history. -/
noncomputable def observedChanges (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (time : ℕ) : ℕ :=
  popChanges tm.k₀ (commandStream tm (encodeConfig tm.m (initList tm x)) (overhead tm*time))

theorem clock_phase_bound (tm : FinTM2) :
    ∃ C : ℕ, ∀ (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (t : ℕ)
      (run : TM2OutputsInTime tm x (some y) t),
      run.steps+(x.length+1) ≤ C^(observedChanges tm x t+1)*(x.length+1) := by
  obtain ⟨C,cost⟩ := real_phase_time tm
  refine ⟨C,?_⟩
  intro x y t run
  obtain ⟨n,hn,walk,phase⟩ := cost x y t run
  let start := encodeConfig tm.m (initList tm x)
  have closed : ((micro tm.m)^[n] start).state.1=none :=
    congrArg (fun c=>c.state.1) walk
  have haltAtClock : ((micro tm.m)^[overhead tm*t] start).state.1=none :=
    congrArg (fun c=>c.state.1) (finite_simulation tm x y t run)
  have eq : observedChanges tm x t = popChanges tm.k₀ (commandStream tm start n) := by
    rcases le_total n (overhead tm*t) with le|le
    · exact clock_after tm start _ _ le closed
    · exact (clock_after tm start _ _ le haltAtClock).symm
  rw [eq]
  exact (Nat.add_le_add_right hn _).trans phase

/-- The phase budget can be traded directly against a desired time exponent.
In particular, a sublinear number of switches gives subexponential time for a
fixed machine. -/
theorem exponential_clock_of_few_switches (tm : FinTM2) :
    ∃ D : ℕ, ∀ (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (t budget : ℕ)
      (_run : TM2OutputsInTime tm x (some y) t), D*(observedChanges tm x t+1) ≤ budget →
      Nonempty (TM2OutputsInTime tm x (some y) (2^budget*(x.length+1))) := by
  obtain ⟨C,bound⟩ := clock_phase_bound tm
  refine ⟨C,?_⟩
  intro x y t budget run phase
  have base : C≤2^C := Nat.lt_two_pow_self.le
  have pow : C^(observedChanges tm x t+1) ≤ 2^budget := by
    calc
      _ ≤ (2^C)^(observedChanges tm x t+1) := Nat.pow_le_pow_left base _
      _ = 2^(C*(observedChanges tm x t+1)) := (Nat.pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) phase
  refine ⟨⟨⟨run.steps,run.evals_in_steps⟩,?_⟩⟩
  exact ((Nat.le_add_right _ _).trans (bound x y t run)).trans (Nat.mul_le_mul_right _ pow)

end StackTrace.Atomic


namespace BudgetGuard

open Turing

inductive Store (K : Type) where
  | engine (k : K) | input | rev | fuel | clean | out
  deriving DecidableEq
inductive Label (L : Type) where
  | copy | restore | sim (l : L) | inspect | clear
  deriving DecidableEq

noncomputable def all (A : Type) [Fintype A] : List A := Finset.univ.toList
private theorem mem_all (A : Type) [Fintype A] (a : A) : a ∈ all A := by simp [all]
private theorem all_nodup (A : Type) [Fintype A] : (all A).Nodup := Finset.nodup_toList _

noncomputable instance {K : Type} [Fintype K] : Fintype (Store K) := by
  classical
  exact Fintype.ofList ((all K).map Store.engine ++ [.input,.rev,.fuel,.clean,.out])
    (by intro x; cases x <;> simp [mem_all])
noncomputable instance {L : Type} [Fintype L] : Fintype (Label L) := by
  classical
  exact Fintype.ofList ((all L).map Label.sim ++ [.copy,.restore,.inspect,.clear])
    (by intro x; cases x <;> simp [mem_all])

abbrev Alphabet (tm : FinTM2) : Store tm.K → Type
  | .engine k => tm.Γ k
  | .input | .rev => tm.Γ tm.k₀
  | .fuel | .clean => Unit
  | .out => Bool

abbrev Reg (tm : FinTM2) := tm.σ × Option (tm.Γ tm.k₀) × Bool × Bool
private abbrev St (tm : FinTM2) := TM2.Stmt (Alphabet tm) (Label tm.Λ) (Reg tm)
private abbrev Src (tm : FinTM2) := TM2.Stmt tm.Γ tm.Λ tm.σ
private abbrev Cell (tm : FinTM2) := (k : tm.K) → List (tm.Γ k)
private abbrev Stores (tm : FinTM2) := (k : Store tm.K) → List (Alphabet tm k)

private def reset (tm : FinTM2) (v : tm.σ) (answer : Bool := false) : Reg tm := (v,none,false,answer)
private def cache (tm : FinTM2) (r : Reg tm) (x : Option (tm.Γ tm.k₀)) : Reg tm := (r.1,x,false,r.2.2.2)
private def flag {A : Type} (tm : FinTM2) (r : Reg tm) (x : Option A) : Reg tm := (r.1,none,x.isSome,r.2.2.2)
private def goto (tm : FinTM2) (l : Label tm.Λ) : St tm :=
  .load (fun r => reset tm r.1 r.2.2.2) (.goto (fun _ => l))

/-- Lift a complete macro instruction. Halting is redirected to an output-inspection phase. -/
def lift (tm : FinTM2) : Src tm → St tm
  | .push k f q => .push (.engine k) (fun r => f r.1) (lift tm q)
  | .peek k f q => .peek (.engine k) (fun r a => (f r.1 a,r.2)) (lift tm q)
  | .pop k f q => .pop (.engine k) (fun r a => (f r.1 a,r.2)) (lift tm q)
  | .load f q => .load (fun r => (f r.1,r.2)) (lift tm q)
  | .branch f q p => .branch (fun r => f r.1) (lift tm q) (lift tm p)
  | .goto f => .goto (fun r => .sim (f r.1))
  | .halt => .goto (fun _ => .inspect)

/-- An untouched group of auxiliary stacks, reusable throughout one original macrostep. -/
structure More (tm : FinTM2) where
  input : List (tm.Γ tm.k₀)
  rev : List (tm.Γ tm.k₀)
  fuel : List Unit
  clean : List Unit
  out : List Bool

def bank (tm : FinTM2) (S : Cell tm) (a : More tm) : Stores tm
  | .engine k => S k
  | .input => a.input
  | .rev => a.rev
  | .fuel => a.fuel
  | .clean => a.clean
  | .out => a.out

private theorem update_engine (tm : FinTM2) (S : Cell tm) (a : More tm) (k : tm.K)
    (xs : List (tm.Γ k)) : Function.update (bank tm S a) (.engine k) xs = bank tm (Function.update S k xs) a := by
  funext p
  cases p with
  | engine j =>
    by_cases h : j=k
    · subst j; simp [Function.update,bank]
    · simp [Function.update,bank,h]
  | input | rev | fuel | clean | out => simp [Function.update,bank]

private def next {L : Type} : Option L → Label L
  | none => .inspect
  | some l => .sim l

private theorem lift_correct (tm : FinTM2) (q : Src tm) (v : tm.σ) (S : Cell tm) (a : More tm)
    (x : Option (tm.Γ tm.k₀)) (b c : Bool) :
    TM2.stepAux (lift tm q) (v,x,b,c) (bank tm S a) =
      let r := TM2.stepAux q v S
      ⟨some (next r.l),(r.var,x,b,c),bank tm r.stk a⟩ := by
  induction q generalizing v S with
  | push k f q ih =>
    change TM2.stepAux (lift tm q) _ (Function.update (bank tm S a) (.engine k) (f v :: S k)) = _
    rw [update_engine]
    exact ih v _
  | pop k f q ih =>
    change TM2.stepAux (lift tm q) _ (Function.update (bank tm S a) (.engine k) (S k).tail) = _
    rw [update_engine]
    exact ih (f v (S k).head?) _
  | peek k f q ih => exact ih (f v (S k).head?) S
  | load f q ih => exact ih (f v) S
  | branch f q p iq ip => cases h : f v <;> simp [lift,h,iq,ip]
  | goto f | halt => rfl

private def pushes {K Λ σ : Type} {Γ : K → Type} : TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => pushes q + 1
  | .peek _ _ q | .pop _ _ q | .load _ q => pushes q
  | .branch _ q p => max (pushes q) (pushes p)
  | .goto _ | .halt => 0

private theorem growth (tm : FinTM2) (q : Src tm) (v : tm.σ) (S : Cell tm) (k : tm.K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length+pushes q := by
  induction q generalizing v S with
  | push j f q ih =>
    apply (ih _ _).trans
    by_cases he : k = j
    · subst k; simp [pushes]; omega
    · simp [pushes,Function.update_of_ne he]
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    apply (ih _ _).trans
    by_cases he : k = j
    · subst k; simp [pushes]
    · simp [pushes,Function.update_of_ne he]
  | load f q ih => exact ih _ _
  | branch f q p iq ip =>
    cases h : f v
    · exact (show ((TM2.stepAux (.branch f q p) v S).stk k).length = ((TM2.stepAux p v S).stk k).length by simp [h]) ▸
        (ip _ _).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
    · exact (show ((TM2.stepAux (.branch f q p) v S).stk k).length = ((TM2.stepAux q v S).stk k).length by simp [h]) ▸
        (iq _ _).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f | halt => simp [pushes]

noncomputable def morePerInput (tm : FinTM2) : Nat := let _ := tm.ΛFin; Finset.univ.sup (fun l => pushes (tm.m l)) + 1

private def addClean (tm : FinTM2) : Nat → St tm → St tm
  | 0,q => q
  | n+1,q => .push .clean (fun _ => ()) (addClean tm n q)

private def addFuel (tm : FinTM2) : Nat → St tm → St tm
  | 0,q => q
  | n+1,q => .push .fuel (fun _=>()) (addFuel tm n q)

private def clearStackRow (tm : FinTM2) : List tm.K → St tm → St tm
  | [],q => q
  | k::ks,q => .pop (.engine k) (fun r _ => r) (clearStackRow tm ks q)

noncomputable def program (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool) : Label tm.Λ → St tm
  | .copy => .pop .input (cache tm) <| .branch (fun r => r.2.1.isSome)
      (.push .rev (fun r => r.2.1.getD blank) (addFuel tm scale (addClean tm (scale*morePerInput tm+1) (goto tm .copy))))
      (addFuel tm scale (addClean tm (scale*morePerInput tm+1) (goto tm .restore)))
  | .restore => .pop .rev (cache tm) <| .branch (fun r => r.2.1.isSome)
      (.push (.engine tm.k₀) (fun r => r.2.1.getD blank) (goto tm .restore)) (goto tm (.sim tm.main))
  | .sim l => .pop .fuel (flag tm) <| .branch (fun r => r.2.2.1)
      (.load (fun r => reset tm r.1) (lift tm (tm.m l))) (goto tm .clear)
  | .inspect => .peek (.engine tm.k₁) (fun r a => reset tm r.1 ((a.map out).getD false)) (goto tm .clear)
  | .clear =>
    let _ := tm.kFin
    .pop .clean (flag tm) <| .branch (fun r => r.2.2.1)
      (.pop .fuel (fun r _ => r) (clearStackRow tm (all tm.K) (goto tm .clear)))
      (.push .out (fun r => r.2.2.2) (.load (fun _ => reset tm tm.initialState) .halt))

noncomputable def machine (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool) : FinTM2 := by
  let _ := tm.kFin
  let _ := tm.ΛFin
  let _ := tm.σFin
  let _ := tm.Γk₀Fin
  exact {
    K := Store tm.K, k₀ := .input, k₁ := .out, Γ := Alphabet tm,
    Λ := Label tm.Λ, main := .copy, σ := Reg tm, initialState := reset tm tm.initialState,
    Γk₀Fin := tm.Γk₀Fin,m := program scale tm blank out }

end BudgetGuard

namespace BudgetGuard

open Turing

private theorem setInput (tm : FinTM2) (S : Cell tm) (a : More tm) (xs : List (tm.Γ tm.k₀)) :
    Function.update (bank tm S a) .input xs = bank tm S {a with input := xs} := by
  funext p; cases p <;> simp [Function.update,bank]
private theorem setRev (tm : FinTM2) (S : Cell tm) (a : More tm) (xs : List (tm.Γ tm.k₀)) :
    Function.update (bank tm S a) .rev xs = bank tm S {a with rev := xs} := by
  funext p; cases p <;> simp [Function.update,bank]
private theorem setFuel (tm : FinTM2) (S : Cell tm) (a : More tm) (xs : List Unit) :
    Function.update (bank tm S a) .fuel xs = bank tm S {a with fuel := xs} := by
  funext p; cases p <;> simp [Function.update,bank]
private theorem setClean (tm : FinTM2) (S : Cell tm) (a : More tm) (xs : List Unit) :
    Function.update (bank tm S a) .clean xs = bank tm S {a with clean := xs} := by
  funext p; cases p <;> simp [Function.update,bank]
private theorem setOut (tm : FinTM2) (S : Cell tm) (a : More tm) (xs : List Bool) :
    Function.update (bank tm S a) .out xs = bank tm S {a with out := xs} := by
  funext p; cases p <;> simp [Function.update,bank]

private theorem addClean_spec (tm : FinTM2) (n : Nat) (q : St tm) (r : Reg tm) (S : Cell tm) (a : More tm) :
    TM2.stepAux (addClean tm n q) r (bank tm S a) =
    TM2.stepAux q r (bank tm S {a with clean := List.replicate n () ++ a.clean}) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change TM2.stepAux (addClean tm n q) r (Function.update (bank tm S a) .clean (() :: a.clean)) = _
    rw [setClean,ih,List.replicate_succ']
    simp

private theorem addFuel_spec (tm : FinTM2) (n : Nat) (q : St tm) (r : Reg tm) (S : Cell tm) (a : More tm) :
    TM2.stepAux (addFuel tm n q) r (bank tm S a) =
    TM2.stepAux q r (bank tm S {a with fuel := List.replicate n () ++ a.fuel}) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    change TM2.stepAux (addFuel tm n q) r (Function.update (bank tm S a) .fuel (() :: a.fuel)) = _
    rw [setFuel,ih,List.replicate_succ']
    simp

private def trim (tm : FinTM2) : List tm.K → Cell tm → Cell tm
  | [],S => S
  | k::ks,S => trim tm ks (Function.update S k (S k).tail)

private theorem trim_spec (tm : FinTM2) (ks : List tm.K) (S : Cell tm) (j : tm.K) (nd : ks.Nodup) :
    trim tm ks S j = if j ∈ ks then (S j).tail else S j := by
  induction ks generalizing S with
  | nil => simp [trim]
  | cons k ks ih =>
    obtain ⟨hk,hd⟩ := List.nodup_cons.mp nd
    by_cases he : j=k
    · subst j; simp [trim,ih _ hd,hk]
    · simp [trim,ih _ hd,he]

private theorem clearRow_spec (tm : FinTM2) (ks : List tm.K) (q : St tm) (r : Reg tm) (S : Cell tm) (a : More tm) :
    TM2.stepAux (clearStackRow tm ks q) r (bank tm S a) = TM2.stepAux q r (bank tm (trim tm ks S) a) := by
  induction ks generalizing S with
  | nil => rfl
  | cons k ks ih =>
    change TM2.stepAux (clearStackRow tm ks q) r (Function.update (bank tm S a) (.engine k) (S k).tail) = _
    rw [update_engine,ih]
    rfl

private def frame (tm : FinTM2) (l : Label tm.Λ) (v : tm.σ) (good : Bool) (S : Cell tm) (a : More tm) :
    TM2.Cfg (Alphabet tm) (Label tm.Λ) (Reg tm) := ⟨some l,reset tm v good,bank tm S a⟩

variable (scale : ℕ)

private theorem copy_cell (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (x : tm.Γ tm.k₀) (xs : List (tm.Γ tm.k₀)) (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .copy tm.initialState false S {a with input := x::xs}) =
    some (frame tm .copy tm.initialState false S {a with input := xs,rev := x::a.rev, fuel := List.replicate scale () ++ a.fuel,clean := List.replicate (scale*morePerInput tm+1) () ++ a.clean}) := by
  simp [TM2.step,frame,program,reset,cache,goto,TM2.stepAux,setInput,setRev,addFuel_spec,addClean_spec,bank]

private theorem copy_end (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .copy tm.initialState false S {a with input := []}) =
    some (frame tm .restore tm.initialState false S {a with input := [],fuel := List.replicate scale () ++ a.fuel, clean := List.replicate (scale*morePerInput tm+1) () ++ a.clean}) := by
  simp [TM2.step,frame,program,reset,cache,goto,TM2.stepAux,setInput,addFuel_spec,addClean_spec,bank]

private theorem restore_cell (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (x : tm.Γ tm.k₀) (xs : List (tm.Γ tm.k₀)) (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .restore tm.initialState false S {a with rev := x::xs}) =
    some (frame tm .restore tm.initialState false (Function.update S tm.k₀ (x::S tm.k₀)) {a with rev := xs}) := by
  simp [TM2.step,frame,program,reset,cache,goto,TM2.stepAux,setRev,update_engine,bank]

private theorem restore_end (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .restore tm.initialState false S {a with rev := []}) =
    some (frame tm (.sim tm.main) tm.initialState false S {a with rev := []}) := by
  simp [TM2.step,frame,program,reset,cache,goto,TM2.stepAux,setRev,bank]

private theorem sim_cell (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (l : tm.Λ) (v : tm.σ) (S : Cell tm) (a : More tm) (fuel : List Unit) :
    let c := TM2.stepAux (tm.m l) v S
    TM2.step (program scale tm blank out) (frame tm (.sim l) v false S {a with fuel := ()::fuel}) =
    some (frame tm (next c.l) c.var false c.stk {a with fuel := fuel}) := by
  simp [TM2.step,frame,program,reset,flag,goto,TM2.stepAux,setFuel,lift_correct,bank]

private theorem sim_timeout (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (l : tm.Λ) (v : tm.σ) (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm (.sim l) v false S {a with fuel := []}) =
    some (frame tm .clear v false S {a with fuel := []}) := by
  simp [TM2.step,frame,program,reset,flag,goto,TM2.stepAux,setFuel,bank]

private theorem inspect_cell (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (v : tm.σ) (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .inspect v false S a) =
    some (frame tm .clear v (((S tm.k₁).head?.map out).getD false) S a) := by rfl

private theorem clear_cell (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (v : tm.σ) (good : Bool) (S : Cell tm) (a : More tm) (gauge : List Unit) :
    TM2.step (program scale tm blank out) (frame tm .clear v good S {a with clean := ()::gauge}) =
    some (frame tm .clear v good (fun k => (S k).tail) {a with clean := gauge,fuel := a.fuel.tail}) := by
  let _ := tm.kFin
  have trimmed : trim tm (all tm.K) S = (fun k => (S k).tail) := by
    funext k; rw [trim_spec tm _ _ _ (all_nodup _)]; simp [mem_all]
  simp [TM2.step,frame,program,reset,flag,goto,TM2.stepAux,setClean,setFuel,clearRow_spec,bank,trimmed]

private theorem clear_end (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (v : tm.σ) (good : Bool) (S : Cell tm) (a : More tm) :
    TM2.step (program scale tm blank out) (frame tm .clear v good S {a with clean := []}) =
    some ⟨none,reset tm tm.initialState,bank tm S {a with clean := [],out := good::a.out}⟩ := by
  simp [TM2.step,frame,program,reset,flag,TM2.stepAux,setClean,setOut,bank]

end BudgetGuard

namespace BudgetGuard

open Turing

private abbrev Run {A : Type} (step : A → Option A) (n : Nat) (c d : A) : Prop :=
  (flip bind step)^[n] (some c) = some d

private theorem runPre {A : Type} {step : A → Option A} {c d e : A} {n : Nat}
    (h : step c = some d) (t : Run step n d e) : Run step (n+1) c e := by
  unfold Run
  rw [Function.iterate_succ_apply]
  change (flip bind step)^[n] (step c) = _
  rwa [h]

private theorem runJoin {A : Type} {step : A → Option A} {c d e : A} {m n : Nat}
    (h : Run step m c d) (t : Run step n d e) : Run step (m+n) c e := by
  unfold Run at *
  rw [Nat.add_comm m n,Function.iterate_add_apply,h,t]

private def extras (tm : FinTM2) (xs rev : List (tm.Γ tm.k₀)) (fuel clean : Nat) : More tm :=
  ⟨xs,rev,List.replicate fuel (),List.replicate clean (),[]⟩

private def noCells (tm : FinTM2) : Cell tm := fun _ => []

variable (scale : ℕ)

private theorem copy_many (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (xs rev : List (tm.Γ tm.k₀)) (f c : Nat) :
    Run (TM2.step (program scale tm blank out)) (xs.length+1)
      (frame tm .copy tm.initialState false (noCells tm) (extras tm xs rev f c))
      (frame tm .restore tm.initialState false (noCells tm)
        (extras tm [] (xs.reverse++rev) (f+(xs.length+1)*scale) (c+(xs.length+1)*(scale*morePerInput tm+1)))) := by
  induction xs generalizing rev f c with
  | nil =>
    apply runPre (copy_end scale tm blank out _ (extras tm [] rev f c))
    simp [extras,Run,List.replicate_succ,Nat.add_comm]
    rw [← Nat.add_assoc c _ 1]
    rfl
  | cons x xs ih =>
    apply runPre (copy_cell scale tm blank out x xs _ (extras tm [] rev f c))
    have hr := ih (x::rev) (f+scale) (c+(scale*morePerInput tm+1))
    simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    convert hr using 1 <;> congr 2 <;> first | omega | (rw [Nat.succ_mul]; omega) | simp [extras,Nat.add_comm]


private theorem restore_many (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (rev : List (tm.Γ tm.k₀)) (S : Cell tm) (f c : Nat) :
    Run (TM2.step (program scale tm blank out)) (rev.length+1)
      (frame tm .restore tm.initialState false S (extras tm [] rev f c))
      (frame tm (.sim tm.main) tm.initialState false
        (Function.update S tm.k₀ (rev.reverse++S tm.k₀)) (extras tm [] [] f c)) := by
  induction rev generalizing S with
  | nil =>
    apply runPre (restore_end scale tm blank out _ (extras tm [] [] f c))
    simp [Run,extras]
  | cons x xs ih =>
    apply runPre (restore_cell scale tm blank out x xs _ (extras tm [] [] f c))
    simpa [List.append_assoc,extras] using ih (Function.update S tm.k₀ (x::S tm.k₀))

def boundedOutput (tm : FinTM2) (out : tm.Γ tm.k₁ → Bool) : Nat → tm.Cfg → Bool
  | 0,c => if c.l.isNone then ((c.stk tm.k₁).head?.map out).getD false else false
  | n+1,c =>
    match c.l with
    | none => ((c.stk tm.k₁).head?.map out).getD false
    | some l => boundedOutput tm out n (TM2.stepAux (tm.m l) c.var c.stk)

private theorem push_bound (tm : FinTM2) (l : tm.Λ) : pushes (tm.m l)+1 ≤ morePerInput tm := by
  let _ := tm.ΛFin
  exact Nat.succ_le_succ (Finset.le_sup (f := fun l => pushes (tm.m l)) (Finset.mem_univ l))

end BudgetGuard

namespace BudgetGuard

open Turing

private theorem halt_form (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀)
    (out : tm.Γ tm.k₁ → Bool) (good : Bool) :
    (⟨none,reset tm tm.initialState,bank tm (noCells tm) {extras tm [] [] 0 0 with out:=[good]}⟩ :
       (machine scale tm blank out).Cfg) = haltList (machine scale tm blank out) [good] := by
  unfold haltList
  change (⟨none,reset tm tm.initialState,_⟩ : TM2.Cfg (Alphabet tm) (Label tm.Λ) (Reg tm))=⟨none,reset tm tm.initialState,_⟩
  congr 1
  funext k
  cases k <;> rfl

private theorem clear_many (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (v : tm.σ) (good : Bool) (fuel clean : ℕ) (S : Cell tm)
    (hf : fuel≤clean) (hs : ∀ k, (S k).length≤clean) :
    Run (TM2.step (program scale tm blank out)) (clean+1)
      (frame tm .clear v good S (extras tm [] [] fuel clean)) (haltList (machine scale tm blank out) [good]) := by
  induction clean generalizing fuel S with
  | zero =>
    have eq : S=noCells tm := funext fun k=>List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hs k))
    subst S
    have zero : fuel=0 := by omega
    subst fuel
    apply runPre (clear_end scale tm blank out v good _ (extras tm [] [] 0 0))
    exact congrArg some (halt_form scale tm blank out good)
  | succ clean ih =>
    apply runPre (clear_cell scale tm blank out v good S (extras tm [] [] fuel clean) (List.replicate clean ()))
    have sub := ih (fuel-1) (fun k=>(S k).tail) (by omega) (fun k=>by simpa using Nat.sub_le_sub_right (hs k) 1)
    have ef : (List.replicate fuel ()).tail=List.replicate (fuel-1) () := by cases fuel <;> rfl
    simpa only [extras,ef] using sub

private theorem stopped_run (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (v : tm.σ) (S : Cell tm) (fuel clean : ℕ) (hf : fuel≤clean) (space : ∀ i, (S i).length≤clean) :
    ∃ n≤fuel+clean+2, Run (TM2.step (program scale tm blank out)) n
      (frame tm .inspect v false S (extras tm [] [] fuel clean)) (haltList (machine scale tm blank out)
        [boundedOutput tm out fuel ⟨none,v,S⟩]) := by
  have answer : boundedOutput tm out fuel ⟨none,v,S⟩=((S tm.k₁).head?.map out).getD false := by cases fuel <;> rfl
  rw [answer]
  exact ⟨clean+2,by omega,runPre (inspect_cell scale tm blank out v S _) (clear_many scale tm blank out _ _ _ _ _ hf space)⟩

private theorem simulate_many (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (fuel clean : ℕ) (c : tm.Cfg) (hf : fuel≤clean)
    (room : ∀ k, (c.stk k).length + fuel*(morePerInput tm-1)≤clean) :
    ∃ n≤fuel+clean+2, Run (TM2.step (program scale tm blank out)) n
      (frame tm (next c.l) c.var false c.stk (extras tm [] [] fuel clean))
      (haltList (machine scale tm blank out) [boundedOutput tm out fuel c]) := by
  induction fuel generalizing c with
  | zero =>
    obtain ⟨l,v,S⟩ := c
    have hs : ∀ k,(S k).length≤clean := by simpa using room
    cases l with
    | none => exact stopped_run scale tm blank out v S 0 clean hf hs
    | some l =>
      exact ⟨clean+2,by omega,runPre (sim_timeout scale tm blank out l v S (extras tm [] [] 0 clean))
        (clear_many scale tm blank out _ _ _ _ _ hf hs)⟩
  | succ f ih =>
    obtain ⟨l,v,S⟩ := c
    cases l with
    | none =>
      apply stopped_run scale tm blank out v S (f+1) clean hf
      intro k
      exact (Nat.le_add_right _ _).trans (room k)
    | some l =>
      let new := TM2.stepAux (tm.m l) v S
      have sub : ∀ k,(new.stk k).length+f*(morePerInput tm-1)≤clean := by
        intro k
        have add := growth tm (tm.m l) v S k
        have step := push_bound tm l
        have prior := room k
        change (S k).length+(f+1)*(morePerInput tm-1)≤clean at prior
        rw [Nat.succ_mul] at prior
        change ((TM2.stepAux (tm.m l) v S).stk k).length + f*(morePerInput tm-1) ≤ clean
        omega
      obtain ⟨n,bnd,go⟩ := ih new (by omega) sub
      exact ⟨n+1,by omega,runPre (sim_cell scale tm blank out l v S (extras tm [] [] f clean) (List.replicate f ())) go⟩

private theorem init_frame (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀)
    (out : tm.Γ tm.k₁ → Bool) (x : List (tm.Γ tm.k₀)) :
    initList (machine scale tm blank out) x = frame tm .copy tm.initialState false (noCells tm) (extras tm x [] 0 0) := by
  unfold initList frame
  congr 1
  funext k; cases k <;> rfl

/-- Input-length coefficient including copying, restoration, simulation and all cleanup. -/
noncomputable def coefficient (scale : ℕ) (tm : FinTM2) := scale+scale*morePerInput tm+5

/-- On every input the wrapper returns the source's result with the stated fuel.
It completely empties other memory and restores the required final control. -/
noncomputable def time_guard (scale : ℕ) (tm : FinTM2) (blank : tm.Γ tm.k₀) (out : tm.Γ tm.k₁ → Bool)
    (x : List (tm.Γ tm.k₀)) :
    TM2OutputsInTime (machine scale tm blank out) x
      (some [boundedOutput tm out ((x.length+1)*scale) (initList tm x)]) (coefficient scale tm*(x.length+1)) := by
  let n := x.length
  let fuel := (n+1)*scale
  let clean := (n+1)*(scale*morePerInput tm+1)
  let c := initList tm x
  have base : 1≤morePerInput tm := Nat.succ_pos _
  have small : ∀ k,(c.stk k).length≤n := by
    intro k
    by_cases h:k=tm.k₀
    · subst k; simp [c,initList,n]
    · simp [c,initList,h]
  have room : ∀ k,(c.stk k).length+fuel*(morePerInput tm-1)≤clean := by
    intro k
    have e := Nat.mul_le_mul_left fuel (Nat.sub_le (morePerInput tm) 1)
    unfold clean fuel at *
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    exact (Nat.add_le_add (small k) e).trans (by omega)
  have hf : fuel≤clean := by
    have ratio := Nat.mul_le_mul_left scale base
    dsimp [fuel,clean]
    exact Nat.mul_le_mul_left _ (by omega)
  let found := simulate_many scale tm blank out fuel clean c hf room
  let steps := Classical.choose found
  have budget := (Classical.choose_spec found).1
  have sim := (Classical.choose_spec found).2
  have copy := copy_many scale tm blank out x [] 0 0
  have restored := restore_many scale tm blank out x.reverse (noCells tm) fuel clean
  have active : Function.update (noCells tm) tm.k₀ (x.reverse.reverse++noCells tm tm.k₀)=c.stk := by
    funext i; by_cases h : i=tm.k₀
    · subst i; simp [c,noCells,initList]
    · simp [c,noCells,initList,h]
  rw [active,List.length_reverse] at restored
  have copy' : Run (TM2.step (program scale tm blank out)) (n+1)
      (frame tm .copy tm.initialState false (noCells tm) (extras tm x [] 0 0))
      (frame tm .restore tm.initialState false (noCells tm) (extras tm [] x.reverse fuel clean)) := by
    simpa only [List.append_nil,Nat.zero_add] using copy
  have together := runJoin (runJoin copy' restored) sim
  have lim : (n+1)+(n+1)+steps≤coefficient scale tm*(n+1) := by
    have b : steps ≤ fuel+clean+2 := budget
    dsimp [fuel,clean] at b
    dsimp [coefficient]
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one] at b ⊢
    nlinarith
  refine ⟨⟨_,?_⟩,lim⟩
  rw [init_frame]
  exact together

/-- A completed source computation has the same answer under any sufficient clock. -/
theorem bounded_agrees (tm : FinTM2) (out : tm.Γ tm.k₁ → Bool) (n fuel : ℕ)
    (c d : tm.Cfg) (h : (flip bind tm.step)^[n] (some c)=some d)
    (stopped : d.l=none) (enough : n≤fuel) :
    boundedOutput tm out fuel c = ((d.stk tm.k₁).head?.map out).getD false := by
  induction n generalizing fuel c with
  | zero =>
    have eq : c=d := Option.some.inj h
    subst c
    obtain ⟨l,v,S⟩ := d
    cases l with
    | none => cases fuel <;> rfl
    | some l => cases stopped
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[n] (tm.step c)=some d at h
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨l,v,S⟩ := c
      cases l with
      | none =>
        change (flip bind tm.step)^[n] none=some d at h
        rw [Function.iterate_fixed (show (flip bind tm.step) none=none from rfl)] at h
        cases h
      | some l =>
        exact ih fuel (TM2.stepAux (tm.m l) v S) h (by omega)

theorem bounded_outputs (tm : FinTM2) (out : tm.Γ tm.k₁ → Bool)
    (input : List (tm.Γ tm.k₀)) (z : tm.Γ tm.k₁) (n fuel : ℕ)
    (h : TM2OutputsInTime tm input (some [z]) n) (enough : n≤fuel) :
    boundedOutput tm out fuel (initList tm input) = out z := by
  obtain ⟨⟨m,hm⟩,hb⟩ := h
  have agree := bounded_agrees tm out m fuel _ (haltList tm [z]) hm rfl (hb.trans enough)
  simpa [haltList] using agree

end BudgetGuard

namespace DeterministicPadding

open Turing PEqualNP.Library PEqualNP.Library.Machines

private def left : Bool ⊕ Bool → Option Bool
  | .inl b => some b
  | .inr _ => none

private theorem first_of_pair (p : List Bool × List Bool) : (encodePair p).filterMap left=p.1 := by
  rcases p with ⟨x,w⟩
  have hl : ∀ l : List Bool, (l.map (.inl : Bool → Bool ⊕ Bool)).filterMap left=l := by
    intro l; induction l <;> simp_all [left]
  have hr : ∀ l : List Bool, (l.map (.inr : Bool → Bool ⊕ Bool)).filterMap left=[] := by
    intro l; induction l <;> simp_all [left]
  simp [encodePair,hl,hr]

private theorem alt_length (j s : ℕ) (P : List Bool → Prop) (Q : Prop)
    (h : ∀ w, w.length=j*s → (P w ↔ Q)) : Alt j s P ↔ Q := by
  classical
  induction j generalizing P Q with
  | zero => exact h [] (by simp)
  | succ j ih =>
    have tail : ∀ y : List Bool, y.length=s → (Alt j s (fun w=>¬P (y++w)) ↔ ¬Q) := by
      intro y hy
      apply ih
      intro w hw
      apply not_congr (h _ ?_)
      simp only [List.length_append,hy,hw,Nat.succ_mul]
      omega
    change (∃ y : List Bool, y.length=s ∧ ¬Alt j s (fun w=>¬P (y++w))) ↔ Q
    constructor
    · rintro ⟨y,hy,ok⟩; exact Classical.byContradiction fun hn=>ok ((tail y hy).2 hn)
    · intro yes
      let y:=List.replicate s false
      have hy : y.length=s := by simp [y]
      exact ⟨y,hy,fun hn=>(tail y hy).1 hn yes⟩

private abbrev Decider (f : List Bool → Bool) := TM2ComputableInTime (fun x : List Bool=>x) Computability.encodeBool f

private noncomputable def raw {f} (c : Decider f) :=
  comp (fm left (some false)) c.tm c.inputAlphabet.invFun (some (c.inputAlphabet.invFun false))

private theorem raw_run {f} (c : Decider f) (p : List Bool × List Bool) :
    ∃ n ≤ 2*(encodePair p).length+2+(2*p.1.length+2)+c.time p.1.length,
      (flip bind (raw c).step)^[n] (some (initList (raw c) (encodePair p)))=
        some (haltList (raw c) [c.outputAlphabet.invFun (f p.1)]) := by
  let μ := fm left (some false)
  let i := encodePair p
  have pre : (flip bind (TM2.step μ.m))^[i.length+1+(i.length+1)] (some (initList μ i))=some (haltList μ p.1) := by
    exact (fm_run left (some false) (by simp) i).trans (congrArg (fun z=>some (haltList μ z)) (first_of_pair p))
  let run := c.outputsFun p.1
  obtain ⟨n,hn,_,hr⟩ := comp_run (M1:=μ) (M2:=c.tm) c.inputAlphabet.invFun (some (c.inputAlphabet.invFun false))
    (by simp) i p.1 [c.outputAlphabet.invFun (f p.1)] _ run.steps pre run.evals_in_steps
  have hs : run.steps≤c.time p.1.length := run.steps_le_m
  change n≤((encodePair p).length+1+((encodePair p).length+1))+(2*p.1.length+2)+run.steps at hn
  exact ⟨n,by omega,hr⟩

/-- A deterministic run fitting in a constant multiple of the input plus all witness bits
has a uniform linear-time verifier at any fixed alternation count, even on short witnesses. -/
theorem sigma_of_clock {f : List Bool → Bool} (c : Decider f) (j k : ℕ) (T : ℕ → ℕ)
    (bound : ∀ n, c.time n≤k*(n+j*T n+1)) :
    {x : List Bool | f x=true} ∈ SigmaV j T := by
  classical
  let M:=raw c
  let sc:=k+4
  let cost:=BudgetGuard.coefficient sc M
  let ans : List Bool × List Bool → Bool := fun p=>BudgetGuard.boundedOutput M c.outputAlphabet
    (((encodePair p).length+1)*sc) (initList M (encodePair p))
  let R : Set (List Bool × List Bool) := {p | ans p=true}
  have checker : DecidableInTime encodePair R (fun n=>cost*n+cost) := by
    refine ⟨ans,fun _=>Iff.rfl,?_,fun n=>?_⟩
    · exact {
        tm := BudgetGuard.machine sc M (Sum.inl false) c.outputAlphabet
        inputAlphabet := Equiv.refl _
        outputAlphabet := Equiv.refl _
        time := fun n=>cost*(n+1)
        outputsFun := fun p=>by
          have run := BudgetGuard.time_guard sc M (Sum.inl false) c.outputAlphabet (encodePair p)
          change TM2OutputsInTime (BudgetGuard.machine sc M (Sum.inl false) c.outputAlphabet)
            ((encodePair p).map id) (some (([ans p] : List Bool).map id)) (cost*((encodePair p).length+1))
          exact (congrArg (fun l : List (Bool ⊕ Bool)=>TM2OutputsInTime
            (BudgetGuard.machine sc M (Sum.inl false) c.outputAlphabet) l (some [ans p])
            (cost*((encodePair p).length+1))) (List.map_id (encodePair p))).symm.mp run }
    · simp [Nat.mul_add]
  refine ⟨R,cost,checker,fun x=>?_⟩
  apply Iff.symm (alt_length _ _ _ _ ?_)
  intro w hw
  have len : (encodePair (x,w)).length=x.length+w.length := by simp [encodePair]
  obtain ⟨n,hn,hr⟩:=raw_run c (x,w)
  have budget : n≤((encodePair (x,w)).length+1)*sc := by
    simp only [len] at hn ⊢
    have b:=bound x.length
    rw [←hw] at b
    dsimp [sc]
    rw [Nat.mul_add,Nat.mul_comm _ k]
    omega
  have completed : TM2OutputsInTime M (encodePair (x,w)) (some [c.outputAlphabet.invFun (f x)]) n := ⟨⟨n,hr⟩,le_rfl⟩
  have out := BudgetGuard.bounded_outputs M c.outputAlphabet (encodePair (x,w)) (c.outputAlphabet.invFun (f x)) n _ completed budget
  change (ans (x,w)=true ↔ f x=true)
  have computed : ans (x,w)=f x := out.trans (c.outputAlphabet.right_inv _)
  rw [computed]

end DeterministicPadding

namespace DeterministicPadding

open Turing PEqualNP.Library StackTrace.Atomic

private theorem floor_budget {w a n b : ℕ} (hw : 0<w) (h : w*a≤n+b) : a≤n/w+b := by
  have hmul : b≤w*b := by simpa using Nat.mul_le_mul_right b hw
  calc
    a = w*a/w := (Nat.mul_div_cancel_left a hw).symm
    _ ≤ (n+w*b)/w := Nat.div_le_div_right (h.trans (Nat.add_le_add_left hmul _))
    _ = _ := Nat.add_mul_div_left _ _ hw

private theorem absorb_input (q n b : ℕ) (hq : 0<q) :
    2^(n/(2*q)+b)*(n+1) ≤ (2^b*(2*q))*2^(n/q) := by
  let w:=2*q
  have wpos : 0<w := Nat.mul_pos (by decide) hq
  have lin : n+1≤w*(n/w+1) := by
    have hm:=Nat.mod_lt n wpos
    have eq:=Nat.div_add_mod n w
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have size : n+1≤w*2^(n/w) := lin.trans (Nat.mul_le_mul_left _ Nat.lt_two_pow_self)
  have halves : n/w+n/w≤n/q := by
    have mul : (n/w+n/w)*q≤n := by
      calc
        _ = (n/w)*w := by dsimp [w]; ring
        _ ≤ n := Nat.div_mul_le_self _ _
    exact (Nat.le_div_iff_mul_le hq).2 mul
  calc
    _ ≤ 2^(n/w+b)*(w*2^(n/w)) := Nat.mul_le_mul_left _ size
    _ = (2^b*w)*2^(n/w+n/w) := by rw [Nat.pow_add,Nat.pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) halves)

/-- Sublinearly many changes of the popped stack imply three-round verification with
witness length 2^(n/q), for every fixed positive q. The machine and the constants
may depend on the language and q. -/
theorem sigma_of_sublinear_switches {f : List Bool → Bool} (c : Decider f)
    (few : ∀ d : ℕ, ∃ b : ℕ, ∀ x : List Bool,
      d*(observedChanges c.tm (x.map c.inputAlphabet.invFun) (c.time x.length)+1)≤x.length+b)
    (q : ℕ) (hq : 0<q) : {x : List Bool | f x=true} ∈ SigmaV 3 (fun n=>2^(n/q)) := by
  classical
  obtain ⟨D,fast⟩ := exponential_clock_of_few_switches c.tm
  obtain ⟨b,hb⟩ := few ((2*q)*D)
  let T := fun n : ℕ=>2^(n/(2*q)+b)*(n+1)
  let c' : Decider f := { c with
    time:=T
    outputsFun:=fun x=>by
      let y:=(Computability.encodeBool (f x)).map c.outputAlphabet.invFun
      have seen:=hb x
      rw [Nat.mul_assoc] at seen
      have v:=floor_budget (Nat.mul_pos (by decide : 0<2) hq) seen
      have out:=(fast (x.map c.inputAlphabet.invFun) y (c.time x.length) (x.length/(2*q)+b) (c.outputsFun x) v).some
      simpa only [List.length_map] using out }
  apply sigma_of_clock c' 3 (2^b*(2*q)) (fun n=>2^(n/q))
  intro n
  change 2^(n/(2*q)+b)*(n+1) ≤ _
  exact (absorb_input q n b hq).trans (Nat.mul_le_mul_left _ (by omega))

end DeterministicPadding
namespace PushdownTime

variable {Q A : Type*}

/-- A single-stack phase, recording the exact final stack. -/
inductive Ends (δ : Rules Q A) : Q → List A → ℕ → List A → Prop where
  | done {q xs} (stop : δ q xs.head?=none) : Ends δ q xs 0 xs
  | tick {q xs r w n out} (op : δ q xs.head?=some (r,w)) (tail : Ends δ r (w++xs.tail) n out) :
      Ends δ q xs (n+1) out

private theorem erases {δ : Rules Q A} {q s n out} (run : Ends δ q s n out) : Halts δ q s n := by
  induction run with
  | done h=>exact .done h
  | tick h _ ih=>exact .tick h ih

private def EndRest (δ : Rules Q A) (y out : List A) (whole spent : ℕ) : Option Q → Prop
  | none => whole=spent
  | some r => ∃ left, Ends δ r y left out ∧ whole=spent+left

private theorem cut_endpoint {δ : Rules Q A} {q s n out} (h : Ends δ q s n out) (x y : List A) (eq : s=x++y) :
    ∃ spent result, Prefix δ q x spent result ∧ EndRest δ y out n spent result := by
  induction h generalizing x y with
  | @done q s stop=>
    cases x with
    | nil=>exact ⟨0,some q,.boundary _,0,by subst s; simpa using Ends.done stop,rfl⟩
    | cons a x=>subst s; exact ⟨0,none,.done stop,rfl⟩
  | @tick q s r w n out op later ih=>
    cases x with
    | nil=>exact ⟨0,some q,.boundary _,n+1,by simpa [eq] using Ends.tick op later,by omega⟩
    | cons a x=>
      subst s
      obtain ⟨spent,result,first,rest⟩:=ih (w++x) y (by simp [List.append_assoc])
      refine ⟨spent+1,result,.tick op first,?_⟩
      cases result with
      | none=>exact congrArg Nat.succ rest
      | some r=>obtain ⟨left,last,combine⟩:=rest; exact ⟨left,last,by omega⟩

private theorem end_growth {δ : Rules Q A}
    (unit : ∀ q a r w, δ q a=some (r,w) → w.length≤a.toList.length+1)
    {q s n out} (run : Ends δ q s n out) : out.length≤s.length+n := by
  induction run with
  | done=>simp
  | @tick q s r w n out op later ih=>
    have growth:=unit _ _ _ _ op
    have identity : s.head?.toList.length+s.tail.length=s.length := by cases s <;> simp [Nat.add_comm]
    rw [List.length_append] at ih
    omega

/-- Elapsed steps plus a weighted final height are bounded by the corresponding
initial height and one fixed additive charge. The weight may be any number no
smaller than the maximum isolated-symbol cost. -/
theorem one_stack_amortized [Fintype Q] [Fintype A] (δ : Rules Q A) (R : ℕ) (fit : rate δ≤R)
    (unit : ∀ q a r w, δ q a=some (r,w) → w.length≤a.toList.length+1)
    (q : Q) (s : List A) (n : ℕ) (out : List A) (run : Ends δ q s n out) :
    n+R*out.length≤R*s.length+R*(R+1) := by
  classical
  have small : ∀ {q : Q} {a : A} {t z}, Prefix δ q [a] t z → t≤R := by
    intro q a t z h
    rw [isolated_bound h]
    exact (Finset.le_sup (f:=isolatedCost δ) (Finset.mem_univ (q,a))).trans ((le_max_left _ _).trans fit)
  have short {q : Q} {s : List A} {n : ℕ} {out : List A} (walk : Ends δ q s n out) (time : n≤R) :
      n+R*out.length≤R*s.length+R*(R+1) := by
    have length:=(end_growth unit walk).trans (Nat.add_le_add_left time _)
    have mul:=Nat.mul_le_mul_left R length
    rw [Nat.mul_add] at mul ⊢
    omega
  induction s generalizing q n out with
  | nil=>
    apply short run
    have b:=one_stack_linear δ q [] n (erases run)
    exact (by simpa using b : n≤rate δ).trans fit
  | cons a s ih=>
    obtain ⟨spent,result,head,tail⟩:=cut_endpoint run [a] s rfl
    have cap:=small head
    cases result with
    | none=>exact short run (tail ▸ cap)
    | some r=>
      obtain ⟨rest,walk,eq⟩:=tail
      have h:=ih r rest out walk
      rw [List.length_cons,Nat.mul_succ,eq]
      omega

end PushdownTime
namespace PushdownTime.Multistack

variable {K A Q : Type*} [DecidableEq K]

private theorem projects_end {P : Program K A Q} {i : K} {c t n} (run : Phase P i c n t) :
    Ends (project P i) (control c i) (c.cells i) n (t.cells i) := by
  induction run with
  | stop c boundary =>
    apply Ends.done
    simp only [project,control,head_reconstructed]
    cases cmd : P c.state (heads c) with
    | none => rfl
    | some result =>
      obtain ⟨q,act⟩ := result
      have no := boundary q act cmd
      cases act with
      | idle | push => exact False.elim (no trivial)
      | pop k => simp [show k≠i from fun e=> no e.symm]
  | @more c q act n t op ok later ih =>
    cases act with
    | idle =>
      apply Ends.tick (r:=((q,cache c i) : Control K A Q)) (w:=(c.cells i).head?.toList)
      · simp [project,control,head_reconstructed,op]
      · rw [head_tail]; exact ih
    | push k a =>
      by_cases eq : k=i
      · subst k
        apply Ends.tick (r:=((q,cache c i) : Control K A Q)) (w:=a::(c.cells i).head?.toList)
        · simp [project,control,head_reconstructed,op]
        · simpa only [List.cons_append,head_tail,perform,control,cache_active,Function.update_self] using ih
      · apply Ends.tick (r:=((q,Function.update (cache c i) k (some a)) : Control K A Q)) (w:=(c.cells i).head?.toList)
        · simp [project,control,head_reconstructed,op,eq]
        · rw [head_tail]
          change Ends _ (q,Function.update (cache c i) k (some a)) _ _ (t.cells i)
          change Ends _ (q,cache (perform c q (.push k a)) i) ((perform c q (.push k a)).cells i) n (t.cells i) at ih
          rw [cache_other eq] at ih
          simpa only [perform,Function.update_of_ne (Ne.symm eq)] using ih
    | pop k =>
      have eq : i=k := ok
      subst k
      apply Ends.tick (r:=((q,cache c i) : Control K A Q)) (w:=[])
      · simp [project,control,head_reconstructed,op]
      · simpa only [List.nil_append,control,perform,cache_active,Function.update_self] using ih

private theorem project_unit (P : Program K A Q) (i : K) :
    ∀ q a r w, project P i q a=some (r,w) → w.length≤a.toList.length+1 := by
  rintro ⟨v,cache⟩ a r w eq
  unfold project at eq
  cases op : P v (Function.update cache i a) with
  | none=>simp [op] at eq
  | some cmd=>
    obtain ⟨q,act⟩:=cmd
    cases act with
    | idle=>simp [op] at eq; rw [←eq.2]; omega
    | push k b=>by_cases e:k=i <;> simp [op,e] at eq <;> rw [←eq.2] <;> simp
    | pop k=>by_cases e:k=i <;> simp [op,e] at eq; rw [eq.2]; simp

/-- Number of symbols pushed onto stacks other than the stack being popped. -/
def foreign (i : K) : Action K A → ℕ
  | .push k _=>if k=i then 0 else 1
  | _=>0

inductive CountedPhase (P : Program K A Q) (i : K) : Config K A Q → ℕ → ℕ → Config K A Q → Prop where
  | stop (c) (boundary : ∀ q act, P c.state (heads c)=some (q,act) → ¬allows i act) : CountedPhase P i c 0 0 c
  | more {c q act n f out} (op : P c.state (heads c)=some (q,act)) (ok : allows i act)
      (later : CountedPhase P i (perform c q act) n f out) : CountedPhase P i c (n+1) (f+foreign i act) out

private theorem forget_phase {P : Program K A Q} {i : K} {c n f out} (r : CountedPhase P i c n f out) : Phase P i c n out := by
  induction r with
  | stop c h=>exact .stop c h
  | more op ok _ ih=>exact .more op ok ih

private def away [Fintype K] (c : Config K A Q) (i : K) : ℕ := ∑ j ∈ Finset.univ.erase i,(c.cells j).length

private theorem height_split [Fintype K] (c : Config K A Q) (i : K) : height c=(c.cells i).length+away c i :=
  (Finset.add_sum_erase Finset.univ (fun j=>(c.cells j).length) (Finset.mem_univ i)).symm

private theorem off_update [Fintype K] (c : Config K A Q) (q : Q) (i : K) (w : List A) :
    away (⟨q,Function.update c.cells i w⟩ : Config K A Q) i=away c i := by
  apply Finset.sum_congr rfl
  intro k mem
  simp [Function.update_of_ne (Finset.mem_erase.mp mem).1]

private theorem away_step [Fintype K] (c : Config K A Q) (q : Q) (i : K) (act : Action K A) (ok : allows i act) :
    away (perform c q act) i=away c i+foreign i act := by
  cases act with
  | idle=>rfl
  | pop k=>have same : i=k:=ok; subst k; exact off_update c q i _
  | push k a=>
    by_cases same:k=i
    · subst k; simpa [foreign,perform] using off_update c q i (a::c.cells i)
    · have member : k∈Finset.univ.erase i:=Finset.mem_erase.mpr ⟨same,Finset.mem_univ _⟩
      have sz : (fun j=>(Function.update c.cells k (a::c.cells k) j).length)=
          Function.update (fun j=>(c.cells j).length) k ((c.cells k).length+1) := by
        funext j; by_cases e:j=k <;> simp [e]
      simp only [away,perform,sz,Finset.sum_update_of_mem member,foreign,ite_eq_right same]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem member (fun j=>(c.cells j).length)]
      omega

private theorem counted_away [Fintype K] {P : Program K A Q} {i : K} {c n f out} (r : CountedPhase P i c n f out) :
    away out i=away c i+f := by
  induction r with
  | stop=>rfl
  | @more c q a n f out op ok _ ih=>rw [ih,away_step c q i a ok]; omega

/-- A phase may grow its other stacks only by explicit foreign pushes. The
remaining active-stack growth is covered by one fixed additive charge. -/
theorem charged_phase [Fintype K] [Fintype Q] [Fintype A] {P : Program K A Q} {i : K} {c n f out}
    (run : CountedPhase P i c n f out) :
    let R:=perPhase P
    n+R*height out≤R*height c+R*f+R*(R+1) := by
  let R:=perPhase P
  have cap : rate (project P i)≤R := Finset.le_sup (f:=fun j=>rate (project P j)) (Finset.mem_univ i)
  have localCost:=one_stack_amortized _ R cap (project_unit P i) _ _ _ _ (projects_end (forget_phase run))
  have storage:=counted_away run
  change n+R*height out≤R*height c+R*f+R*(R+1)
  rw [height_split out i,height_split c i,storage]
  simp only [Nat.mul_add] at localCost ⊢
  omega

end PushdownTime.Multistack
namespace PushdownTime.Multistack

variable {K A Q : Type*} [DecidableEq K]

/-- For each push, count it when its stack differs from the most recently
popped stack, initialized to the specified stack. -/
def crossWrites : K → List (Action K A) → ℕ
  | _,[]=>0
  | i,.idle::xs=>crossWrites i xs
  | i,.push j a::xs=>crossWrites i xs+foreign i (.push j a)
  | _,.pop j::xs=>crossWrites j xs

inductive CountedPhases (P : Program K A Q) : Config K A Q → ℕ → ℕ → ℕ → Config K A Q → Prop where
  | nil (c) : CountedPhases P c 0 0 0 c
  | more {i c mid out n p r f g} (first : CountedPhase P i c n f mid) (rest : CountedPhases P mid p r g out) :
      CountedPhases P c (p+1) (n+r) (f+g) out

private theorem split_counted {P : Program K A Q} {c acts out} (run : Journey P c acts out) (i : K) :
    ∃ n mid r f g, CountedPhase P i c n f mid ∧ CountedPhases P mid (switches i acts) r g out ∧
      n+r=acts.length ∧ f+g=crossWrites i acts := by
  induction run generalizing i with
  | stop c done=> exact ⟨0,c,0,0,0,.stop _ (fun _ _ eq=>by rw [done] at eq; contradiction),.nil _,rfl,rfl⟩
  | @more c q act tail out op later ih=>
    have same (allowed : allows i act) (count : switches i (act::tail)=switches i tail)
        (cross : crossWrites i (act::tail)=crossWrites i tail+foreign i act) :
        ∃ n mid r f g, CountedPhase P i c n f mid ∧ CountedPhases P mid (switches i (act::tail)) r g out ∧
          n+r=(act::tail).length ∧ f+g=crossWrites i (act::tail) := by
      obtain ⟨n,mid,r,f,g,first,rest,len,cf⟩:=ih i
      exact ⟨n+1,mid,r,f+foreign i act,g,.more op allowed first,count ▸ rest,by simp;omega,by omega⟩
    cases act with
    | idle | push=>exact same trivial rfl rfl
    | pop k=>
      by_cases eq:k=i
      · subst k; exact same rfl (by simp [switches]) rfl
      · obtain ⟨n,mid,r,f,g,first,rest,len,cf⟩:=ih k
        have stop : CountedPhase P i c 0 0 c := .stop _ (by
          intro q' a e
          obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj (op.symm.trans e))
          exact Ne.symm eq)
        have next : CountedPhase P k c (n+1) f mid := .more op rfl first
        have all : CountedPhases P c (switches i (.pop k::tail)) (n+1+r) (f+g) out := by
          simpa [switches,eq] using CountedPhases.more next rest
        exact ⟨0,c,n+1+r,0,f+g,stop,all,by simp;omega,by simpa [crossWrites] using cf⟩

private theorem sum_phases [Fintype K] [Fintype Q] [Fintype A] {P : Program K A Q} {c p n f out}
    (run : CountedPhases P c p n f out) :
    let R:=perPhase P
    n+R*height out≤R*height c+R*f+(R*(R+1))*p := by
  induction run with
  | nil=>simp
  | @more i c mid out n p r f g first rest ih=>
    have phase:=charged_phase first
    dsimp only at phase ih ⊢
    rw [Nat.mul_add (perPhase P) f g,Nat.mul_succ]
    omega

/-- A deterministic multistack run's elapsed time is linear in initial storage,
physical pop-stack switches, and pushes to a different stack during a phase. -/
theorem switches_writes_time [Fintype K] [Fintype Q] [Fintype A] {P : Program K A Q} {c acts out}
    (run : Journey P c acts out) (i : K) :
    let R:=perPhase P
    acts.length + R*height out ≤ R*height c + R*crossWrites i acts + (R*(R+1))*(switches i acts+1) := by
  obtain ⟨n,mid,r,f,g,first,rest,len,cf⟩:=split_counted run i
  have cat:=sum_phases (CountedPhases.more first rest)
  simpa only [len,cf] using cat

end PushdownTime.Multistack
namespace StackTrace.Atomic
open Turing PushdownTime.Multistack

/-- Foreign pushes in the chronological physical trace, relative to its last
popped stack. The input stack is used before the first pop. -/
def otherWrites {K A : Type} [DecidableEq K] : K → List (Command K A) → ℕ
  | _,[]=>0
  | i,.idle::as=>otherWrites i as
  | i,.push k _::as=>otherWrites i as+(if k=i then 0 else 1)
  | _,.pop k::as=>otherWrites k as

private theorem writes_count (tm : FinTM2) (as : List (Action tm.K (Sym tm))) (i : tm.K) :
    otherWrites i (as.map (forgetAction tm)) = crossWrites i as := by
  induction as generalizing i with
  | nil=>rfl
  | cons a as ih=>cases a <;> simp [forgetAction,otherWrites,crossWrites,foreign,ih]

private theorem appended_writes {K A : Type} [DecidableEq K] (i : K) (as : List (Command K A)) (n : ℕ) :
    otherWrites i (as++List.replicate n .idle)=otherWrites i as := by
  induction as generalizing i with
  | nil=>induction n with
    | zero=>rfl
    | succ n ih=>simpa [List.replicate_succ,otherWrites] using ih
  | cons a as ih=>cases a <;> simp [otherWrites,ih]

private theorem writes_after (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (n t : ℕ) (past : n≤t)
    (done : ((micro tm.m)^[n] c).state.1=none) :
    otherWrites tm.k₀ (commandStream tm c t)=otherWrites tm.k₀ (commandStream tm c n) := by
  obtain ⟨r,rfl⟩:=Nat.exists_eq_add_of_le past
  rw [commands_append,commands_stopped tm _ done,appended_writes]

noncomputable def observedForeign (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (t : ℕ) :=
  otherWrites tm.k₀ (commandStream tm (encodeConfig tm.m (initList tm x)) (overhead tm*t))

/-- A universal amortized bound for each fixed deterministic multistack machine.
Elapsed macrosteps are linear in input length, changes of popped stack, and the
number of pushes addressed to a different stack from the last popped one. -/
theorem switch_write_clock (tm : FinTM2) :
    ∃ C : ℕ, ∀ (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁)) (t : ℕ)
      (run : TM2OutputsInTime tm x (some y) t),
      run.steps≤C*(x.length+observedForeign tm x t+observedChanges tm x t+1) := by
  let _:=tm.kFin
  let _:=validFinite tm
  let _:=symbolFinite tm
  let R:=perPhase (program tm)
  let C:=R*(R+1)+R+1
  refine ⟨C,?_⟩
  intro x y t run
  obtain ⟨n,hn,walk⟩:=walking_macro tm run.steps run.evals_in_steps
  obtain ⟨acts,out,rel,eq,sz,_⟩:=realize walk rfl (initialP tm x) (initial_erase tm x)
  let start:=encodeConfig tm.m (initList tm x)
  have done : ((micro tm.m)^[n] start).state.1=none:=congrArg (fun z=>z.state.1) (walk_eval walk)
  have final : ((micro tm.m)^[overhead tm*t] start).state.1=none:=congrArg (fun z=>z.state.1) (finite_simulation tm x y t run)
  have changes : popChanges tm.k₀ (commandStream tm start n)=observedChanges tm x t := by
    rcases le_total n (overhead tm*t) with h|h
    · exact (clock_after tm start _ _ h done).symm
    · exact clock_after tm start _ _ h final
  have foreignEq : otherWrites tm.k₀ (commandStream tm start n)=observedForeign tm x t := by
    rcases le_total n (overhead tm*t) with h|h
    · exact (writes_after tm start _ _ h done).symm
    · exact writes_after tm start _ _ h final
  have charged:=switches_writes_time rel tm.k₀
  change acts.length+R*height out≤R*height (initialP tm x)+R*crossWrites tm.k₀ acts+(R*(R+1))*(switches tm.k₀ acts+1) at charged
  rw [initial_size,←pop_count,←writes_count,eq,sz,changes,foreignEq] at charged
  have rc : R≤C := by dsimp [C];omega
  have kc : R*(R+1)≤C := by dsimp [C];omega
  calc
    run.steps ≤ R*x.length+R*observedForeign tm x t+(R*(R+1))*(observedChanges tm x t+1) := hn.trans ((Nat.le_add_right _ _).trans charged)
    _ ≤ C*x.length+C*observedForeign tm x t+C*(observedChanges tm x t+1) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ rc) (Nat.mul_le_mul_right _ rc)) (Nat.mul_le_mul_right _ kc)
    _ = _ := by simp [Nat.mul_add];omega

end StackTrace.Atomic

namespace StackTrace.Atomic
open Turing

private theorem combined_le {K A : Type} [DecidableEq K] (i : K) (as : List (Command K A)) :
    otherWrites i as+popChanges i as≤as.length := by
  induction as generalizing i with
  | nil=>rfl
  | cons a as ih=>
    cases a with
    | idle=>simp only [otherWrites,popChanges,List.length_cons]; exact (ih i).trans (Nat.le_succ _)
    | push j a=>by_cases same:j=i <;> simp only [otherWrites,popChanges,List.length_cons,same,ite_true,ite_false] <;> have h:=ih i <;> omega
    | pop j=>
      by_cases same:j=i
      · subst j; simp only [otherWrites,popChanges,ite_true,List.length_cons]; exact (ih i).trans (Nat.le_succ _)
      · simp only [otherWrites,popChanges,same,ite_false,List.length_cons]; have h:=ih j; omega

private theorem stream_length (tm : FinTM2) (c : ACfg tm.Γ tm.Λ tm.σ) (n : ℕ) : (commandStream tm c n).length=n := by
  induction n generalizing c with
  | zero=>rfl
  | succ n ih=>simp [commandStream,ih]

/-- The converse estimate uses the actual halting time even when the supplied
clock has considerable slack. Each genuine atomic operation pays at most once. -/
theorem switch_write_cost (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (y : List (tm.Γ tm.k₁))
    (t : ℕ) (run : TM2OutputsInTime tm x (some y) t) :
    observedForeign tm x t+observedChanges tm x t ≤ overhead tm*run.steps := by
  let short : TM2OutputsInTime tm x (some y) run.steps := ⟨run.toEvalsTo,le_rfl⟩
  let start:=encodeConfig tm.m (initList tm x)
  have done : ((micro tm.m)^[overhead tm*run.steps] start).state.1=none:=
    congrArg (fun z=>z.state.1) (finite_simulation tm x y run.steps short)
  have le:=Nat.mul_le_mul_left (overhead tm) run.steps_le_m
  unfold observedForeign observedChanges
  rw [writes_after tm start _ _ le done,clock_after tm start _ _ le done]
  exact (combined_le tm.k₀ _).trans (stream_length tm start _).le

end StackTrace.Atomic
namespace DeterministicPadding
open Turing PEqualNP.Library StackTrace.Atomic

/-- Every language with a deterministic decider whose actual inter-stack traffic
fits the witness budget has the project's uniform linear-time verifier. -/
theorem sigma_of_transfer_budget {f : List Bool → Bool} (c : Decider f) (j k : ℕ) (T : ℕ → ℕ)
    (fits : ∀ x : List Bool,
      observedForeign c.tm (x.map c.inputAlphabet.invFun) (c.time x.length)+
      observedChanges c.tm (x.map c.inputAlphabet.invFun) (c.time x.length)≤k*(x.length+j*T x.length+1)) :
    {x : List Bool | f x=true} ∈ SigmaV j T := by
  obtain ⟨C,time⟩:=switch_write_clock c.tm
  let cap:=C*(k+1)
  let fast : Decider f := { c with
    time:=fun n=>cap*(n+j*T n+1)
    outputsFun:=fun x=>by
      let run:=c.outputsFun x
      have measured:=time _ _ _ run
      have counted:=fits x
      simp only [List.length_map] at measured
      let score:=x.length+j*T x.length+1
      have z : x.length + observedForeign c.tm (x.map c.inputAlphabet.invFun) (c.time x.length)+
          observedChanges c.tm (x.map c.inputAlphabet.invFun) (c.time x.length)+1≤ (k+1)*score := by
        rw [Nat.succ_mul]; dsimp [score] at *; omega
      exact ⟨run.toEvalsTo,measured.trans ((Nat.mul_le_mul_left _ z).trans_eq (Nat.mul_assoc C _ _).symm)⟩ }
  exact sigma_of_clock fast j cap T (fun _=>le_rfl)

end DeterministicPadding

#print axioms BudgetGuard.time_guard
#print axioms DeterministicPadding.sigma_of_clock
#print axioms DeterministicPadding.sigma_of_sublinear_switches
#print axioms StackTrace.Atomic.switch_write_clock
#print axioms StackTrace.Atomic.switch_write_cost
#print axioms DeterministicPadding.sigma_of_transfer_budget
