import FP3Columns
import FP3Game
namespace ColumnCheck

inductive Tree (n : ℕ) (A : Type) where
  | leaf (a : A)
  | node (q : Formula n) (yes no : Tree n A)

noncomputable def Tree.eval {n A} (l : List (Col n)) : Tree n A→A := by
  classical exact fun
    | .leaf a=>a
    | .node q y z=>if q.holds l then y.eval l else z.eval l

def Tree.bind {n A B} (tree : Tree n A) (f : A→Tree n B) : Tree n B :=
  match tree with
  | .leaf a=>f a
  | .node q t u=>.node q (t.bind f) (u.bind f)

theorem Tree.bind_eval {n A B} (t : Tree n A) (f : A→Tree n B) (l : List (Col n)) :
    (t.bind f).eval l=(f (t.eval l)).eval l := by
  induction t with
  | leaf=>rfl
  | node q a b ha hb=>by_cases h:q.holds l <;>simp [eval,bind,h,ha,hb]

noncomputable def Tree.test {n A} (tree : Tree n A) (P : A→Prop) : Formula n := by
  classical exact match tree with
    | .leaf a=>if P a then .const (fun _=>false) 0 else .neg (.const (fun _=>false) 0)
    | .node q y z=>.disj (.conj q (y.test P)) (.conj (.neg q) (z.test P))

theorem false_word {n} (l : List (Col n)) : value (fun _=>false) l=0 := by
  induction l with | nil=>rfl | cons a l ih=>simp [value,ih]

theorem Tree.test_correct {n A} (t : Tree n A) (P : A→Prop) (l : List (Col n)) :
    (t.test P).holds l ↔ P (t.eval l) := by
  classical
  induction t with
  | leaf a=>by_cases h:P a <;>simp [test,eval,h,Formula.holds,false_word]
  | node q y z hy hz=>by_cases h:q.holds l <;>simp [test,eval,h,Formula.holds,hy,hz]

def lookup {n A} (wire : Pick n) (fallback : A) : ℕ→List A→Tree n A
  | _,[]=>.leaf fallback
  | i,a::ls=>.node (.const wire i) (.leaf a) (lookup wire fallback (i+1) ls)

theorem lookup_value {n A} (wire : Pick n) (l : List (Col n)) (other : A) (xs : List A) :
    ∀ i, (lookup wire other i xs).eval l =
      if i≤value wire l then xs.getD (value wire l-i) other else other := by
  induction xs with
  | nil=>intro i;simp [lookup,Tree.eval]
  | cons a xs ih=>
    intro i
    by_cases eq:value wire l=i
    · simp [lookup,Tree.eval,Formula.holds,eq]
    · by_cases before:i≤value wire l
      · have above:i+1≤value wire l:=by omega
        have diff:value wire l-i=(value wire l-(i+1))+1:=by omega
        simp [lookup,Tree.eval,Formula.holds,eq,before,above,ih,diff,List.getD]
      · have low:¬i+1≤value wire l:=by omega
        simp [lookup,Tree.eval,Formula.holds,eq,before,low,ih]

def classOf {n A} (wire : Pick n) (fallback : A) (xs : List A) := lookup wire fallback 0 xs

theorem class_value {n A} (wire : Pick n) (l : List (Col n)) (other : A) (xs : List A) :
    (classOf wire other xs).eval l=xs.getD (value wire l) other := by simp [classOf,lookup_value]

def allValues {n} {K A : Type} [DecidableEq K] (base : K→A) (keys : List K) (get : K→Tree n A) :
    Tree n (K→A) :=
  match keys with
  | []=>.leaf base
  | k::ks=>(get k).bind fun v=>(allValues base ks get).bind fun fs=>.leaf (Function.update fs k v)

theorem allValues_get {n} {K A : Type} [DecidableEq K] (base : K→A) (keys : List K) (get : K→Tree n A)
    (l : List (Col n)) (k : K) (mem:k∈keys) :
    (allValues base keys get).eval l k=(get k).eval l := by
  induction keys with
  | nil=>simp at mem
  | cons a xs ih=>
    simp only [allValues,Tree.bind_eval,Tree.eval]
    by_cases h:k=a
    · subst a;exact Function.update_self ..
    · rw [Function.update_of_ne h];exact ih ((List.mem_cons.mp mem).resolve_left h)

end ColumnCheck

#print axioms ColumnCheck.Tree.test_correct
#print axioms ColumnCheck.allValues_get
namespace ColumnCheck.Pointer
open StackTrace
open scoped Classical

variable {K A Q : Type} [DecidableEq K]

def pushes (k : K) : Command K A→Bool
  | .push j _=>decide (k=j)
  | _=>false

def pops (k : K) : Command K A→Bool
  | .pop j=>decide (k=j)
  | _=>false

def backRank (r : Trace K A Q) (k : K) : Option ℕ→ℕ
  | none=>0
  | some u=>rank ((r u).top k)

def backPush (r : Trace K A Q) (k : K) : Option ℕ→Bool
  | none=>false
  | some u=>pushes k (r u).action

theorem parent_value (r : Trace K A Q) (k : K) (p : Option ℕ) :
    rank ((node r k p).bind Prod.snd)=
      if backPush r k p=true ∧ backRank r k p<rank p then backRank r k p else 0 := by
  cases p with
  | none=>rfl
  | some u=>
    cases act:(r u).action with
    | idle=>simp [node,backPush,backRank,act,pushes,rank]
    | pop j=>simp [node,backPush,backRank,act,pushes,rank]
    | push j v=>
      have rs:rank (some u)=u+1:=rfl
      by_cases same:k=j
      · subst j
        by_cases old:rank ((r u).top k)<u+1
        · have hnode:node r k (some u)=some (v,(r u).top k):=by simp [node,act,old]
          rw [hnode]
          simp [backPush,backRank,act,pushes,rs,old]
        · have hnode:node r k (some u)=none:=by simp [node,act,old]
          rw [hnode]
          simp [backPush,backRank,act,pushes,rs,old,show rank none=0 by rfl]
      · have hnode:node r k (some u)=none:=by simp [node,act,same]
        rw [hnode]
        simp [backPush,backRank,act,pushes,same,show rank none=0 by rfl]

theorem next_value (r : Trace K A Q) (k : K) (t : ℕ) :
    let p:=(r t).top k
    rank (pointerAdvance r t k)=if pushes k (r t).action then t+1 else if pops k (r t).action then
      (if backPush r k p=true ∧ backRank r k p<rank p then backRank r k p else 0) else rank p := by
  dsimp only
  cases act:(r t).action with
  | idle=>simp [pointerAdvance,act,pushes,pops]
  | push j v=>by_cases h:k=j <;>simp [pointerAdvance,act,pushes,pops,h,Function.update,rank]
  | pop j=>
    by_cases h:k=j
    · subst j
      simp [pointerAdvance,act,pushes,pops,parent_value]
    · simp [pointerAdvance,act,pushes,pops,h,Function.update]

private def zeroPick {n : ℕ} : Pick n := fun _=>false
private theorem value_zero {n : ℕ} (l : List (Col n)) : value zeroPick l=0 := by
  induction l with | nil=>rfl | cons a ls ih=>simp [value,zeroPick,ih]

structure Slots (n : ℕ) where
  time : Pick n
  old : Pick n
  back : Pick n
  next : Pick n
  push : Formula n
  pop : Formula n
  fromPush : Formula n

def choose {n} (test yes no : Formula n) : Formula n :=
  .disj (.conj test yes) (.conj (.neg test) no)

private theorem choose_iff {n} (t y z : Formula n) (l : List (Col n)) :
    (choose t y z).holds l ↔ if t.holds l then y.holds l else z.holds l := by
  classical
  by_cases h:t.holds l <;>simp [choose,Formula.holds,h]

def requirement {n} (s : Slots n) : Formula n :=
  let saved:=Formula.conj s.fromPush (.lt s.back s.old)
  .conj (.neg (.lt s.time s.old))
    (choose s.push (.add s.time zeroPick s.next true)
      (choose s.pop (choose saved (.eq s.next s.back) (.const s.next 0)) (.eq s.next s.old)))

theorem requirement_iff {n} (s : Slots n) (l : List (Col n)) :
    (requirement s).holds l ↔ value s.old l≤value s.time l ∧
      value s.next l=(if s.push.holds l then value s.time l+1 else if s.pop.holds l then
        (if s.fromPush.holds l ∧ value s.back l<value s.old l then value s.back l else 0) else value s.old l) := by
  classical
  unfold requirement
  simp only [Formula.holds,choose_iff,value_zero,Nat.add_zero,Bool.toNat_true,not_lt]
  by_cases h:s.push.holds l <;>by_cases j:s.pop.holds l <;>
    by_cases k:s.fromPush.holds l ∧ value s.back l<value s.old l <;>simp [h,j,k,Formula.holds] <;> omega

structure Encodes {n} (s : Slots n) (l : List (Col n)) (r : Trace K A Q) (t : ℕ) (k : K) : Prop where
  time : value s.time l=t
  old : value s.old l=rank ((r t).top k)
  back : ((r t).top k).isSome=true → value s.back l=backRank r k ((r t).top k)
  next : value s.next l=rank ((r (t+1)).top k)
  push : s.push.holds l ↔ pushes k (r t).action=true
  pop : s.pop.holds l ↔ pops k (r t).action=true
  fromPush : ((r t).top k).isSome=true → (s.fromPush.holds l ↔ backPush r k ((r t).top k)=true)

theorem slot_semantics {n} (s : Slots n) (l : List (Col n)) (r : Trace K A Q) (t : ℕ) (k : K)
    (h:Encodes s l r t k) :
    (requirement s).holds l ↔ rank ((r t).top k)<t+1 ∧ (r (t+1)).top k=pointerAdvance r t k := by
  classical
  rw [requirement_iff,h.time,h.old,h.next,h.push,h.pop]
  have prev : (if s.fromPush.holds l ∧ value s.back l<rank ((r t).top k) then value s.back l else 0)=
      (if backPush r k ((r t).top k)=true ∧ backRank r k ((r t).top k)<rank ((r t).top k)
        then backRank r k ((r t).top k) else 0) := by
    by_cases present:((r t).top k).isSome=true
    · rw [h.back present,h.fromPush present]
      by_cases ok:backPush r k ((r t).top k)=true ∧ backRank r k ((r t).top k)<rank ((r t).top k) <;>simp [ok]
    · have empty:(r t).top k=none:=by cases e:(r t).top k <;>simp_all
      simp [empty,rank,backRank,backPush]
  rw [prev]
  have inj:Function.Injective rank:=by intro a b eq;cases a <;>cases b <;>simp_all [rank]
  apply and_congr (by omega)
  have nx:=next_value r k t
  dsimp only at nx
  by_cases p:pushes k (r t).action=true <;>by_cases q:pops k (r t).action=true <;>
    by_cases z:backPush r k ((r t).top k)=true ∧ backRank r k ((r t).top k)<rank ((r t).top k) <;>
    simp only [p,q,z,ite_true,ite_false] at nx ⊢ <;>rw [←nx] <;>exact inj.eq_iff

def conjunction {n} : List (Formula n)→Formula n
  | []=>.const zeroPick 0
  | q::qs=>.conj q (conjunction qs)

theorem conjunction_iff {n} (ss : List (Formula n)) (l : List (Col n)) :
    (conjunction ss).holds l ↔ ∀ s∈ss,s.holds l := by
  induction ss with
  | nil=>simp [conjunction,Formula.holds,value_zero]
  | cons s ss ih=>simp [conjunction,Formula.holds,ih]

/-- Every temporal, pointer, push/pop and earlier-node bound in one transition
is handled by the fixed width-independent formula. The source action and control
are represented by a separate finite transition test supplied by the caller. -/
theorem all_stacks {n} (ports : K→Slots n) (ls : List K) (all:∀ k : K,k∈ls)
    (l : List (Col n)) (M : Program K A Q) (r : Trace K A Q) (t : ℕ) (state : Formula n)
    (wires:∀ k,Encodes (ports k) l r t k)
    (stateCheck:state.holds l ↔
      let op:=M t (r t).state (fun k=>(node r k ((r t).top k)).map Prod.fst)
      (r t).action=op.2 ∧ (r (t+1)).state=op.1) :
    (Formula.conj state (conjunction (ls.map (fun k=>requirement (ports k))))).holds l ↔ Meets r M t := by
  simp only [Formula.holds,conjunction_iff,List.forall_mem_map,stateCheck]
  constructor
  · rintro ⟨⟨op,ctrl⟩,ok⟩
    have h (k : K):=(slot_semantics (ports k) l r t k (wires k)).mp (ok k (all k))
    exact ⟨fun k=>(h k).1,op,ctrl,funext (fun k=>(h k).2)⟩
  · rintro ⟨older,op,ctrl,ptr⟩
    exact ⟨⟨op,ctrl⟩,fun k _=>(slot_semantics (ports k) l r t k (wires k)).mpr
      ⟨older k,congrFun ptr k⟩⟩

end ColumnCheck.Pointer

#print axioms ColumnCheck.Pointer.all_stacks
namespace ColumnCheck.Control
open Turing StackTrace StackTrace.Binary
open scoped Classical

structure Layout (n s : ℕ) where
  control : Pick n
  opcode : Pick n
  stack : Pick n
  symbol : Pick n
  top : Fin s→Pick n

def Layout.cols {n s} (f : Layout n s) (l : List (Col n)) : ℕ→ℕ
  | 0=>value f.control l | 1=>value f.opcode l | 2=>value f.stack l | 3=>value f.symbol l
  | j+4=>if h:j<s then value (f.top ⟨j,h⟩) l else 0

abbrev controlType (tm : FinTM2) := Option (TM2.Stmt tm.Γ tm.Λ tm.σ) × tm.σ
abbrev size (tm : FinTM2) := @Fintype.card tm.K tm.kFin

noncomputable def state {n} (tm : FinTM2) (f : Layout n (size tm)) : Tree n (controlType tm) :=
  classOf f.control (Atomic.initialControl tm) (Atomic.controls tm)

noncomputable def symbol {n} (tm : FinTM2) (f : Layout n (size tm)) : Tree n (Option (Sigma tm.Γ)) :=
  classOf f.symbol none ((Atomic.alphabet tm).map some)

noncomputable def stack {n} (tm : FinTM2) (f : Layout n (size tm)) : Tree n (Option tm.K) :=
  classOf f.stack none (List.ofFn (fun i=>(some ((StackTrace.Binary.physical tm).indexStack.symm i))))

noncomputable def command {n} (tm : FinTM2) (f : Layout n (size tm)) : Tree n (Command tm.K (Sigma tm.Γ)) :=
  .node (.const f.opcode 1)
    ((stack tm f).bind fun k=>.leaf ((k.map Command.pop).getD .idle))
    (.node (.const f.opcode 2)
      ((stack tm f).bind fun k=>(symbol tm f).bind fun a=>.leaf
          ((k.bind fun i=>a.map (Command.push i)).getD .idle))
      (.leaf .idle))

theorem state_value {n} (tm : FinTM2) (f : Layout n (size tm)) (l : List (Col n)) :
    (state tm f).eval l=((StackTrace.Binary.physical tm).restore (f.cols l)).state := by
  rw [state,class_value];rfl

theorem symbol_value {n} (tm : FinTM2) (f : Layout n (size tm)) (l : List (Col n)) :
    (symbol tm f).eval l=(StackTrace.Binary.physical tm).symbols.read (value f.symbol l) := by
  rw [symbol,class_value]
  change ((Atomic.alphabet tm).map some).getD (value f.symbol l) none=(Atomic.alphabet tm)[value f.symbol l]?
  simp only [List.getD,List.getElem?_map]
  cases (Atomic.alphabet tm)[value f.symbol l]? <;>rfl

theorem stack_value {n} (tm : FinTM2) (f : Layout n (size tm)) (l : List (Col n)) :
    (stack tm f).eval l=(StackTrace.Binary.physical tm).stackAt (value f.stack l) := by
  rw [stack,class_value]
  by_cases h:value f.stack l<size tm <;> simp [Format.stackAt,List.getD,h]

theorem command_value {n} (tm : FinTM2) (f : Layout n (size tm)) (l : List (Col n)) :
    (command tm f).eval l=((StackTrace.Binary.physical tm).restore (f.cols l)).action := by
  have st:=stack_value tm f l
  have sy:=symbol_value tm f l
  cases h:value f.opcode l with
  | zero=>simp [command,Tree.eval,Formula.holds,h,Format.restore,Layout.cols]
  | succ c=>cases c with
    | zero=>simp [command,Tree.eval,Formula.holds,h,Tree.bind_eval,st,Format.restore,Layout.cols]
    | succ v=>cases v with
      | zero=>simp [command,Tree.eval,Formula.holds,h,Tree.bind_eval,st,sy,Format.restore,Layout.cols]
      | succ b=>simp [command,Tree.eval,Formula.holds,h,Format.restore,Layout.cols]

def peek {n} {K A : Type} [DecidableEq K] (k : K) (old back : Pick n) (action : Tree n (Command K A)) :
    Tree n (Option A) :=
  action.bind fun op=>match op with
    | .push j a=>if k=j then .node (.lt back old) (.leaf (some a)) (.leaf none) else .leaf none
    | _=>.leaf none

theorem peek_value {n} {K A Q : Type} [DecidableEq K] (l : List (Col n)) (r : Trace K A Q) (k : K)
    (p : Option ℕ) (old back : Pick n) (action : Tree n (Command K A))
    (rankOld:value old l=rank p)
    (previous:∀ t,p=some t → value back l=rank ((r t).top k) ∧ action.eval l=(r t).action) :
    (peek k old back action).eval l=(node r k p).map Prod.fst := by
  rw [peek,Tree.bind_eval]
  cases p with
  | none=>
    change value old l=0 at rankOld
    cases op:action.eval l with
    | idle | pop=>rfl
    | push j a=>by_cases eq:k=j <;>simp [eq,Tree.eval,Formula.holds,rankOld,node]
  | some t=>
    obtain ⟨prev,act⟩:=previous t rfl
    change value old l=t+1 at rankOld
    rw [act]
    cases op:(r t).action with
    | idle=>simp [Tree.eval,node,op]
    | pop=>simp [Tree.eval,node,op]
    | push j a=>
      by_cases eq:k=j <;>by_cases usable:rank ((r t).top k)<t+1 <;>
        simp [Tree.eval,Formula.holds,node,op,eq,prev,rankOld,usable]

def nextOp (tm : FinTM2) (mode : Option (tm.Γ tm.k₀)) (q : controlType tm) (heads : tm.K→Option (Sigma tm.Γ)) :
    controlType tm × Command tm.K (Sigma tm.Γ) :=
  match mode with
  | some a=>(q,Command.push tm.k₀ ⟨tm.k₀,a⟩)
  | none=>Atomic.compile tm.m 0 q heads

theorem nextOp_eq (tm : FinTM2) (x : List (tm.Γ tm.k₀)) (t : ℕ) (q : controlType tm)
    (heads : tm.K→Option (Sigma tm.Γ)) :
    nextOp tm x.reverse[t]? q heads=Atomic.loadAndRun tm x t q heads := by
  unfold Atomic.loadAndRun
  by_cases h:t<x.reverse.length
  · rw [dif_pos h,List.getElem?_eq_getElem h]
    rfl
  · rw [dif_neg h,List.getElem?_eq_none (by omega)]
    rfl

noncomputable def stateTest {n} (tm : FinTM2) (mode : Tree n (Option (tm.Γ tm.k₀)))
    (current next : Layout n (size tm)) (heads : Tree n (tm.K→Option (Sigma tm.Γ))) : Formula n :=
  let verdict:=mode.bind fun phase=>(state tm current).bind fun q=>heads.bind fun head=>
    (command tm current).bind fun op=>(state tm next).bind fun nq=>
      .leaf (op=(nextOp tm phase q head).2 ∧ nq=(nextOp tm phase q head).1)
  verdict.test id

theorem stateTest_eval {n} (tm : FinTM2) (l : List (Col n)) (input : List (tm.Γ tm.k₀))
    (t : ℕ) (mode : Tree n (Option (tm.Γ tm.k₀))) (current next : Layout n (size tm))
    (heads : Tree n (tm.K→Option (Sigma tm.Γ))) (phase:mode.eval l=input.reverse[t]?) :
    (stateTest tm mode current next heads).holds l ↔
      let c:=(StackTrace.Binary.physical tm).restore (current.cols l)
      let n:=(StackTrace.Binary.physical tm).restore (next.cols l)
      let expected:=Atomic.loadAndRun tm input t c.state (heads.eval l)
      c.action=expected.2 ∧ n.state=expected.1 := by
  simp only [stateTest,Tree.test_correct,Tree.bind_eval,Tree.eval,id_eq,state_value,command_value,phase,nextOp_eq]

end ColumnCheck.Control

#print axioms ColumnCheck.Control.command_value
#print axioms ColumnCheck.Control.peek_value
#print axioms ColumnCheck.Control.stateTest_eval
namespace ColumnCheck.Runtime
open Turing StackTrace StackTrace.Binary ColumnCheck.Control
open scoped Classical

abbrev RowOf (tm : FinTM2) := Row tm.K (Sigma tm.Γ) (controlType tm)
abbrev TraceOf (tm : FinTM2) := ℕ→RowOf tm

noncomputable def keys (tm : FinTM2) : List tm.K :=
  List.ofFn (fun i=>(StackTrace.Binary.physical tm).indexStack.symm i)

theorem key_mem (tm : FinTM2) (k : tm.K) : k∈keys tm := by
  apply List.mem_ofFn.mpr
  exact ⟨(StackTrace.Binary.physical tm).indexStack k,(StackTrace.Binary.physical tm).indexStack.symm_apply_apply k⟩

noncomputable def top {n} (tm : FinTM2) (layout : Layout n (size tm)) (k : tm.K) : Pick n :=
  layout.top ((StackTrace.Binary.physical tm).indexStack k)

theorem top_value {n} (tm : FinTM2) (layout : Layout n (size tm)) (l : List (Col n)) (k : tm.K) :
    value (top tm layout k) l=rank (((StackTrace.Binary.physical tm).restore (layout.cols l)).top k) := by
  have inverse (x : ℕ) : rank (StackTrace.Binary.Format.unrank x)=x := by cases x <;>rfl
  change _=rank (StackTrace.Binary.Format.unrank (layout.cols l ((StackTrace.Binary.physical tm).indexStack k).val.succ.succ.succ.succ))
  rw [inverse]
  simp [top,Layout.cols,((StackTrace.Binary.physical tm).indexStack k).isLt]

structure Frame (n : ℕ) (tm : FinTM2) where
  time : Pick n
  current : Layout n (size tm)
  next : Layout n (size tm)
  parent : tm.K→Layout n (size tm)
  mode : Tree n (Option (tm.Γ tm.k₀))

noncomputable def port {n} (tm : FinTM2) (f : Frame n tm) (k : tm.K) : Pointer.Slots n where
  time:=f.time
  old:=top tm f.current k
  back:=top tm (f.parent k) k
  next:=top tm f.next k
  push:=(command tm f.current).test (fun a=>Pointer.pushes k a=true)
  pop:=(command tm f.current).test (fun a=>Pointer.pops k a=true)
  fromPush:=(command tm (f.parent k)).test (fun a=>Pointer.pushes k a=true)

noncomputable def readHeads {n} (tm : FinTM2) (f : Frame n tm) : Tree n (tm.K→Option (Sigma tm.Γ)) :=
  allValues (fun _=>none) (keys tm) (fun k=>
    peek k (top tm f.current k) (top tm (f.parent k) k) (command tm (f.parent k)))

noncomputable def step {n} (tm : FinTM2) (f : Frame n tm) : Formula n :=
  .conj (stateTest tm f.mode f.current f.next (readHeads tm f))
    (Pointer.conjunction ((keys tm).map (fun k=>Pointer.requirement (port tm f k))))

structure Agrees {n} (tm : FinTM2) (f : Frame n tm) (l : List (Col n))
    (input : List (tm.Γ tm.k₀)) (r : TraceOf tm) (t : ℕ) : Prop where
  time : value f.time l=t
  current : (StackTrace.Binary.physical tm).restore (f.current.cols l)=r t
  next : (StackTrace.Binary.physical tm).restore (f.next.cols l)=r (t+1)
  parent : ∀ k j,(r t).top k=some j → (StackTrace.Binary.physical tm).restore ((f.parent k).cols l)=r j
  phase : f.mode.eval l=input.reverse[t]?

theorem checks {n} (tm : FinTM2) (f : Frame n tm) (l : List (Col n))
    (input : List (tm.Γ tm.k₀)) (r : TraceOf tm) (t : ℕ) (data:Agrees tm f l input r t) :
    (step tm f).holds l ↔ Meets r (Atomic.loadAndRun tm input) t := by
  apply Pointer.all_stacks (port tm f) (keys tm) (key_mem tm)
  · intro k
    refine ⟨data.time,?_,?_,?_,?_,?_,?_⟩
    · change value (top tm f.current k) l=_
      rw [top_value,data.current]
    · intro present
      obtain ⟨j,hj⟩:=Option.isSome_iff_exists.mp present
      change value (top tm (f.parent k) k) l=_
      rw [top_value,data.parent k j hj,hj]
      rfl
    · change value (top tm f.next k) l=_
      rw [top_value,data.next]
    · change ((command tm f.current).test _).holds l ↔ _
      rw [Tree.test_correct,command_value,data.current]
    · change ((command tm f.current).test _).holds l ↔ _
      rw [Tree.test_correct,command_value,data.current]
    · intro present
      obtain ⟨j,hj⟩:=Option.isSome_iff_exists.mp present
      change ((command tm (f.parent k)).test _).holds l ↔ _
      rw [Tree.test_correct,command_value,data.parent k j hj,hj]
      rfl
  · have hs : (readHeads tm f).eval l=(fun k=>(node r k ((r t).top k)).map Prod.fst) := by
      funext k
      rw [readHeads,allValues_get _ _ _ l k (key_mem tm k)]
      apply peek_value
      · rw [top_value,data.current]
      · intro j hj
        rw [top_value,command_value,data.parent k j hj]
        exact ⟨rfl,rfl⟩
    simpa only [data.current,data.next,hs] using
      stateTest_eval tm l input t f.mode f.current f.next (readHeads tm f) data.phase

end ColumnCheck.Runtime

#print axioms ColumnCheck.Runtime.checks
namespace ColumnCheck.Runtime
open Turing StackTrace StackTrace.Binary ColumnCheck.Control
open scoped Classical

noncomputable def decodedHeads {n} (tm : FinTM2) (current : Layout n (size tm))
    (parent : tm.K→Layout n (size tm)) : Tree n (tm.K→Option (Sigma tm.Γ)) :=
  allValues (fun _=>none) (keys tm) (fun k=>
    peek k (top tm current k) (top tm (parent k) k) (command tm (parent k)))

theorem head_values {n} (tm : FinTM2) (current : Layout n (size tm))
    (parent : tm.K→Layout n (size tm)) (l : List (Col n)) (r : TraceOf tm) (t : ℕ)
    (cur:(StackTrace.Binary.physical tm).restore (current.cols l)=r t)
    (old:∀ k j,(r t).top k=some j → (StackTrace.Binary.physical tm).restore ((parent k).cols l)=r j) :
    (decodedHeads tm current parent).eval l=(fun k=>(node r k ((r t).top k)).map Prod.fst) := by
  funext k
  rw [decodedHeads,allValues_get _ _ _ l k (key_mem tm k)]
  apply peek_value
  · rw [top_value,cur]
  · intro j hj;rw [top_value,command_value,old k j hj];exact ⟨rfl,rfl⟩

structure Window (n : ℕ) (tm : FinTM2) extends Frame n tm where
  horizon : Pick n
  initial : Layout n (size tm)
  finalRow : Layout n (size tm)
  finalParent : tm.K→Layout n (size tm)

noncomputable def window {n} (tm : FinTM2) (w : Window n tm) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) : Formula n :=
  let initial:=(state tm w.initial).test (·=start)
  let bottom:=Pointer.conjunction ((keys tm).map (fun k=>.const (top tm w.initial k) 0))
  let accepted:=((state tm w.finalRow).bind fun q=>
    (decodedHeads tm w.finalRow w.finalParent).bind fun h=>.leaf (accept q h)).test id
  .conj initial (.conj bottom (.conj accepted (.disj (.neg (.lt w.time w.horizon)) (step tm w.toFrame))))

structure Whole {n} (tm : FinTM2) (w : Window n tm) (l : List (Col n))
    (input : List (tm.Γ tm.k₀)) (r : TraceOf tm) (T i : ℕ) extends Agrees tm w.toFrame l input r i where
  horizon : value w.horizon l=T
  initial : (StackTrace.Binary.physical tm).restore (w.initial.cols l)=r 0
  finalRow : (StackTrace.Binary.physical tm).restore (w.finalRow.cols l)=r T
  finalParent : ∀ k j,(r T).top k=some j → (StackTrace.Binary.physical tm).restore ((w.finalParent k).cols l)=r j

theorem all_checks {n} (tm : FinTM2) (w : Window n tm) (l : List (Col n)) (input : List (tm.Γ tm.k₀))
    (r : TraceOf tm) (start : controlType tm) (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop)
    (T : ℕ) (i : Fin (T+1)) (data:Whole tm w l input r T i.val) :
    (window tm w start accept).holds l ↔ Packed.oneCheck (Atomic.loadAndRun tm input) start T accept r i := by
  have bot : (∀ k∈keys tm,(Formula.const (top tm w.initial k) 0).holds l) ↔ ∀ k,(r 0).top k=none := by
    have point (k : tm.K) : (Formula.const (top tm w.initial k) 0).holds l ↔ (r 0).top k=none := by
      change value _ l=0 ↔ _
      rw [top_value,data.initial]
      cases (r 0).top k <;>simp [rank]
    exact ⟨fun h k=>(point k).mp (h k (key_mem tm k)),fun h k _=>(point k).mpr (h k)⟩
  have head:=head_values tm w.finalRow w.finalParent l r T data.finalRow data.finalParent
  simp only [window,Formula.holds,Tree.test_correct,state_value,data.initial,Pointer.conjunction_iff,
    List.forall_mem_map,Tree.bind_eval,Tree.eval,id_eq,data.finalRow,head,data.time,data.horizon,
    checks tm w.toFrame l input r i.val data.toAgrees,Packed.oneCheck]
  have bot' : (∀ k∈keys tm,value (top tm w.initial k) l=0) ↔ ∀ k,(r 0).top k=none:=bot
  rw [bot']
  tauto

end ColumnCheck.Runtime

#print axioms ColumnCheck.Runtime.all_checks
namespace ColumnCheck.Table
open Turing StackTrace StackTrace.Binary ColumnCheck.Control ColumnCheck.Runtime
open scoped Classical

abbrev zero {n : ℕ} : Pick n:=fun _=>false

inductive Ref (n : ℕ) where
  | base (p : Pick n)
  | succ (p : Pick n)
  | pred (p : Pick n)

def Ref.denote {n} (l : List (Col n)) : Ref n→ℕ
  | .base p=>value p l
  | .succ p=>value p l+1
  | .pred p=>value p l-1

def Ref.matches {n} (addr : Pick n) : Ref n→Formula n
  | .base p=>.eq addr p
  | .succ p=>.add p zero addr true
  | .pred p=>.disj (.add addr zero p true) (.conj (.const addr 0) (.const p 0))

theorem Ref.matches_iff {n} (r : Ref n) (addr : Pick n) (l : List (Col n)) :
    (r.matches addr).holds l ↔ value addr l=r.denote l := by
  cases r <;>simp [Ref.matches,denote,Formula.holds,zero,false_word] <;>omega

structure Slot (n s : ℕ) where
  active : Formula n
  address : Pick n
  row : Layout n s

def blank {n s : ℕ} : Layout n s:=⟨zero,zero,zero,zero,fun _=>zero⟩

noncomputable def atTime {n s} (l : List (Col n)) (t : ℕ) : List (Slot n s)→Layout n s
  | []=>blank
  | e::es=>if e.active.holds l ∧ value e.address l=t then e.row else atTime l t es

def findRow {n s} (t : Ref n) : List (Slot n s)→Tree n (Layout n s)
  | []=>.leaf blank
  | e::es=>.node (.conj e.active (t.matches e.address)) (.leaf e.row) (findRow t es)

theorem find_eval {n s} (t : Ref n) (entries : List (Slot n s)) (l : List (Col n)) :
    (findRow t entries).eval l=atTime l (t.denote l) entries := by
  induction entries with
  | nil=>rfl
  | cons e es ih=>simp [findRow,atTime,Tree.eval,Formula.holds,Ref.matches_iff,ih]

noncomputable def rowTrace {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (l : List (Col n)) :
    TraceOf tm := fun t=>(StackTrace.Binary.physical tm).restore ((atTime l t entries).cols l)

noncomputable def parents {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (current : Layout n (size tm)) :
    Tree n (tm.K→Layout n (size tm)) :=
  allValues (fun _=>blank) (keys tm) (fun k=>findRow (.pred (top tm current k)) entries)

theorem parents_eval {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (current : Layout n (size tm))
    (l : List (Col n)) (i : ℕ) (cur:(StackTrace.Binary.physical tm).restore (current.cols l)=rowTrace tm entries l i) (k : tm.K)
    (j : ℕ) (h:(rowTrace tm entries l i).top k=some j) :
    (StackTrace.Binary.physical tm).restore (((parents tm entries current).eval l k).cols l)=rowTrace tm entries l j := by
  rw [parents,allValues_get _ _ _ l k (key_mem tm k),find_eval]
  simp only [Ref.denote,top_value,cur,h,rank,Nat.add_sub_cancel]
  rfl

noncomputable def windows {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (time horizon : Pick n)
    (mode : Tree n (Option (tm.Γ tm.k₀))) : Tree n (Window n tm) :=
  (findRow (.base zero) entries).bind fun first=>(findRow (.base time) entries).bind fun current=>
  (findRow (.succ time) entries).bind fun next=>(findRow (.base horizon) entries).bind fun last=>
  (parents tm entries current).bind fun old=>(parents tm entries last).bind fun targets=>
  .leaf ⟨⟨time,current,next,old,mode⟩,horizon,first,last,targets⟩

theorem selected_agrees {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (time horizon : Pick n)
    (mode : Tree n (Option (tm.Γ tm.k₀))) (l : List (Col n)) (input : List (tm.Γ tm.k₀))
    (phase:mode.eval l=input.reverse[value time l]?) :
    Whole tm ((windows tm entries time horizon mode).eval l) l input (rowTrace tm entries l) (value horizon l)
      (value time l) := by
  simp only [windows,Tree.bind_eval,Tree.eval,find_eval,Ref.denote,zero,false_word]
  exact ⟨⟨rfl,rfl,rfl,parents_eval tm entries _ l _ rfl,phase⟩,rfl,rfl,rfl,parents_eval tm entries _ l _ rfl⟩

def collapse {n} : Tree n (Formula n)→Formula n
  | .leaf a=>a
  | .node q y z=>.disj (.conj q (collapse y)) (.conj (.neg q) (collapse z))

theorem collapse_iff {n} (t : Tree n (Formula n)) (l : List (Col n)) :
    (collapse t).holds l ↔ (t.eval l).holds l := by
  classical
  induction t with
  | leaf=>rfl
  | node q y z hy hz=>by_cases h:q.holds l <;>simp [collapse,Formula.holds,Tree.eval,h,hy,hz]

noncomputable def check {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (time horizon : Pick n)
    (mode : Tree n (Option (tm.Γ tm.k₀))) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) : Formula n :=
  collapse ((windows tm entries time horizon mode).bind (fun w=>.leaf (window tm w start accept)))

theorem check_iff {n} (tm : FinTM2) (entries : List (Slot n (size tm))) (time horizon : Pick n)
    (mode : Tree n (Option (tm.Γ tm.k₀))) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) (l : List (Col n)) (input : List (tm.Γ tm.k₀))
    (i : Fin (value horizon l+1)) (timeval:value time l=i.val) (phase:mode.eval l=input.reverse[i.val]?) :
    (check tm entries time horizon mode start accept).holds l ↔
      Packed.oneCheck (Atomic.loadAndRun tm input) start (value horizon l) accept (rowTrace tm entries l) i := by
  rw [check,collapse_iff,Tree.bind_eval]
  apply all_checks
  have h:=selected_agrees tm entries time horizon mode l input (timeval ▸ phase)
  rwa [timeval] at h

end ColumnCheck.Table

#print axioms ColumnCheck.Table.check_iff
namespace ColumnCheck.Table
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Runtime
open scoped Classical

theorem word_bound {n} (p : Pick n) (l : List (Col n)) : value p l<2^l.length := by
  rw [value_binary]
  simpa using (BitVec.ofBoolListLE (l.map p)).isLt

theorem layout_bound {n s} (f : Layout n s) (l : List (Col n)) (j : ℕ) : f.cols l j<2^l.length := by
  match j with
  | 0 | 1 | 2 | 3=>apply word_bound
  | i+4=>dsimp only [Layout.cols];split
         · apply word_bound
         · positivity

theorem blank_cols {n s} (l : List (Col n)) (j : ℕ) : (blank (n:=n) (s:=s)).cols l j=0 := by
  match j with
  | 0 | 1 | 2 | 3=>apply false_word
  | i+4=>simp [Layout.cols,blank,zero,false_word]

def rawBits {n s} (f : Layout n s) (l : List (Col n)) : List Bool :=
  List.ofFn (fun i : Fin ((4+s)*l.length)=>Format.flatten l.length (f.cols l) i.val)

noncomputable def asSample {n s} (l : List (Col n)) : List (Slot n s)→Sample
  | []=>[]
  | e::es=>if e.active.holds l then (value e.address l,rawBits e.row l)::asSample l es else asSample l es

theorem sample_width {n s} (l : List (Col n)) (es : List (Slot n s)) :
    ∀ e∈asSample l es,e.2.length=(4+s)*l.length := by
  induction es with
  | nil=>simp [asSample]
  | cons e es ih=>
    intro x hx
    by_cases active:e.active.holds l
    · rw [asSample,if_pos active] at hx
      rcases List.mem_cons.mp hx with eq|rest
      · subst x;simp [rawBits]
      · exact ih x rest
    · rw [asSample,if_neg active] at hx
      exact ih x hx

theorem sample_bit {n s} (l : List (Col n)) (es : List (Slot n s)) (t j : ℕ) (hj:j<(4+s)*l.length) :
    sampled (asSample l es) t j=Format.flatten l.length ((atTime l t es).cols l) j := by
  induction es with
  | nil=>simp [sampled,asSample,rowAt,atTime,Format.flatten,blank_cols,List.getD]
  | cons e es ih=>
    by_cases on:e.active.holds l
    · by_cases eq:t=value e.address l
      · subst t
        simp [sampled,asSample,on,rowAt,atTime,rawBits,List.getD,hj]
      · simpa [sampled,asSample,on,rowAt,atTime,eq,Ne.symm eq] using ih
    · simpa [sampled,asSample,on,atTime] using ih

theorem decoded_table {n} (tm : FinTM2) (l : List (Col n)) (entries : List (Slot n (size tm))) (hd:0<l.length) :
    decoded (StackTrace.Binary.physical tm) l.length (sampled (asSample l entries))=rowTrace tm entries l := by
  funext t
  apply (StackTrace.Binary.physical tm).restore_ext
  intro j hj
  let layout:=atTime l t entries
  calc
    Format.extract l.length (sampled (asSample l entries) t) j=
        Format.extract l.length (Format.flatten l.length (layout.cols l)) j := by
      apply congrArg TimeChallenge.decode
      apply congrArg List.ofFn
      funext i
      apply sample_bit
      calc j*l.length+i.val < j*l.length+l.length := Nat.add_lt_add_left i.isLt _
           _=(j+1)*l.length := (Nat.succ_mul _ _).symm
           _≤_ := Nat.mul_le_mul_right _ hj
    _=layout.cols l j:=Format.extract_flatten _ hd _ _ (layout_bound layout l j)

end ColumnCheck.Table

#print axioms ColumnCheck.Table.decoded_table
namespace ColumnCheck.Table
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Runtime
open scoped Classical

def fixed {n : ℕ} (b : Bool) : Formula n :=
  if b then .const zero 0 else .neg (.const zero 0)

theorem fixed_iff {n} (b : Bool) (l : List (Col n)) : (fixed b).holds l ↔ b=true := by
  cases b <;>simp [fixed,Formula.holds,zero,false_word]

def activeKeys {n s} : List (Slot n s)→Tree n (List (Pick n))
  | []=>.leaf []
  | e::es=>let rest:=activeKeys es
           .node e.active (rest.bind (fun ks=>.leaf (e.address::ks))) rest

theorem active_values {n s} (es : List (Slot n s)) (l : List (Col n)) :
    ((activeKeys es).eval l).map (fun p=>value p l)=(asSample l es).map Prod.fst := by
  induction es with
  | nil=>rfl
  | cons e es ih=>by_cases h:e.active.holds l <;>simp [activeKeys,asSample,Tree.eval,Tree.bind_eval,h,ih]

noncomputable def linkRows {n} (tm : FinTM2) (row : Layout n (size tm)) : List tm.K→Tree n (List (Ref n))
  | []=>.leaf []
  | k::ks=>let rest:=linkRows tm row ks
           let p:=top tm row k
           .node (.const p 0) rest (rest.bind (fun rs=>.leaf (.pred p::rs)))

theorem link_values {n} (tm : FinTM2) (row : Layout n (size tm)) (ks : List tm.K) (l : List (Col n)) :
    ((linkRows tm row ks).eval l).map (Ref.denote l)=links ks ((StackTrace.Binary.physical tm).restore (row.cols l)) := by
  induction ks with
  | nil=>rfl
  | cons k ks ih=>
    have val:=top_value tm row l k
    cases h:((StackTrace.Binary.physical tm).restore (row.cols l)).top k with
    | none=>
      have z:value (top tm row k) l=0:=by rw [val,h];rfl
      simpa [linkRows,Tree.eval,Formula.holds,z,links,h] using ih
    | some j=>
      have z:value (top tm row k) l=j+1:=by rw [val,h];rfl
      simpa [linkRows,Tree.eval,Tree.bind_eval,Formula.holds,z,links,h,Ref.denote] using
        congrArg (List.cons j) ih

def align {n} : List (Ref n)→List (Pick n)→Formula n
  | [],[]=>fixed true
  | r::rs,a::as'=>.conj (r.matches a) (align rs as')
  | _,_=>fixed false

theorem align_iff {n} (rs : List (Ref n)) (ks : List (Pick n)) (l : List (Col n)) :
    (align rs ks).holds l ↔ ks.map (fun p=>value p l)=rs.map (Ref.denote l) := by
  induction rs generalizing ks with
  | nil=>cases ks <;>simp [align,fixed_iff]
  | cons r rs ih=>cases ks <;>simp [align,fixed_iff,Formula.holds,Ref.matches_iff,ih]

noncomputable def expected {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) : Tree n (List (Ref n)) :=
  (findRow (.base horizon) es).bind fun last=>(findRow (.base time) es).bind fun cur=>
  (linkRows tm last ks).bind fun ls=>(linkRows tm cur ks).bind fun cs=>
  let lo:=fun p=>[.base zero,.base horizon,.base time,p]++ls++cs
  .node (.lt time horizon) (.leaf (lo (.succ time))) (.leaf (lo (.base horizon)))

theorem expected_values {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) (l : List (Col n)) :
    ((expected tm es ks time horizon).eval l).map (Ref.denote l)=
      footprint ks (rowTrace tm es l) (value horizon l) (value time l) := by
  simp only [expected,Tree.bind_eval,find_eval,Ref.denote,Tree.eval,Formula.holds]
  by_cases h:value time l<value horizon l
  · have m:min (value time l+1) (value horizon l)=value time l+1:=Nat.min_eq_left (by omega)
    simp [h,footprint,anchors,Ref.denote,zero,false_word,link_values,rowTrace,m]
  · have m:min (value time l+1) (value horizon l)=value horizon l:=Nat.min_eq_right (by omega)
    simp [h,footprint,anchors,Ref.denote,zero,false_word,link_values,rowTrace,m]

noncomputable def shape {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) : Formula n :=
  collapse ((expected tm es ks time horizon).bind fun rs=>
    (activeKeys es).bind fun as'=>.leaf (align rs as'))

theorem shape_iff {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) (l : List (Col n)) :
    (shape tm es ks time horizon).holds l ↔ (asSample l es).map Prod.fst=
      footprint ks (rowTrace tm es l) (value horizon l) (value time l) := by
  simp only [shape,collapse_iff,Tree.bind_eval,Tree.eval,align_iff,active_values,expected_values]

noncomputable def counter {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) (mode : Tree n (Option (tm.Γ tm.k₀))) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) : Formula n :=
  .conj (shape tm es ks time horizon) (.neg (check tm es time horizon mode start accept))

theorem counter_iff {n} (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) (mode : Tree n (Option (tm.Γ tm.k₀))) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) (l : List (Col n))
    (input : List (tm.Γ tm.k₀)) (d:0<l.length) (i : Fin (value horizon l+1)) (timeval:value time l=i.val)
    (phase:mode.eval l=input.reverse[i.val]?) :
    (counter tm es ks time horizon mode start accept).holds l ↔
      counterView ks (StackTrace.Binary.physical tm) l.length (Atomic.loadAndRun tm input) start (value horizon l) accept i
        (asSample l es) := by
  simp only [counter,Formula.holds,shape_iff,check_iff tm es time horizon mode start accept l input i timeval phase,
    counterView,decoded_table tm l es d,timeval]
  exact ⟨fun h=>⟨sample_width l es,h⟩,And.right⟩

end ColumnCheck.Table

#print axioms ColumnCheck.Table.counter_iff
namespace ColumnCheck.Table
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Runtime
open scoped Classical

/-- Quasilocal counterexample checking, including legal query addresses, malformed decoded symbols,
all node look-backs, control evolution, initialization and acceptance, is regular on synchronized
binary fields. The machine depends only on the fixed layouts and the source machine. -/
theorem physical_counter {n} (hn:0<n) (tm : FinTM2) (es : List (Slot n (size tm))) (ks : List tm.K)
    (time horizon : Pick n) (mode : Tree n (Option (tm.Γ tm.k₀))) (start : controlType tm)
    (accept : controlType tm→(tm.K→Option (Sigma tm.Γ))→Prop) (l : List (Col n))
    (input : List (tm.Γ tm.k₀)) (d:0<l.length) (i : Fin (value horizon l+1)) (timeval:value time l=i.val)
    (phase:mode.eval l=input.reverse[i.val]?) :
    ∃ b : Bool,(b=true ↔ counterView ks (StackTrace.Binary.physical tm) l.length (Atomic.loadAndRun tm input) start
       (value horizon l) accept i (asSample l es)) ∧ Nonempty (TM2OutputsInTime
       (machine (serial (counter tm es ks time horizon mode start accept).reader hn))
       (serialize l) (some [b]) (2*(serialize l).length+3)) := by
  obtain ⟨b,ok,run⟩:=ColumnCheck.physical (counter tm es ks time horizon mode start accept) hn l
  exact ⟨b,ok.trans (counter_iff tm es ks time horizon mode start accept l input d i timeval phase),run⟩

end ColumnCheck.Table

#print axioms ColumnCheck.Table.physical_counter
