import FP3Game
import Mathlib.Tactic.Linarith
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Finset.Fold
import Mathlib.Logic.Function.Iterate

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

namespace BudgetGuard
open Turing

/-- Successful bounded evaluation exhibits a terminal source configuration.
No well-formedness assumption on this configuration or the input is needed. -/
theorem bounded_true_run (tm : FinTM2) (out : tm.Γ tm.k₁→Bool) (fuel : ℕ) (c : tm.Cfg)
    (yes:boundedOutput tm out fuel c=true) :
    ∃ n≤fuel,∃ d : tm.Cfg,(flip bind tm.step)^[n] (some c)=some d ∧ d.l=none ∧
      ((d.stk tm.k₁).head?.map out).getD false=true := by
  induction fuel generalizing c with
  | zero=>
    obtain ⟨l,v,S⟩:=c
    cases l with
    | none=>exact ⟨0,le_rfl,_,rfl,rfl,yes⟩
    | some l=>simp [boundedOutput] at yes
  | succ fuel ih=>
    obtain ⟨l,v,S⟩:=c
    cases l with
    | none=>exact ⟨0,Nat.zero_le _,_,rfl,rfl,yes⟩
    | some l=>
      obtain ⟨n,hn,d,run,stop,result⟩:=ih (TM2.stepAux (tm.m l) v S) yes
      exact ⟨n+1,Nat.succ_le_succ hn,d,by rw [Function.iterate_succ_apply];exact run,stop,result⟩

end BudgetGuard

#print axioms BudgetGuard.bounded_true_run

namespace RawClock
open Turing PEqualNP.Library

variable (M : FinTM2) (alphabet : M.Γ M.k₀ ≃ Bool ⊕ Bool)
    (output : M.Γ M.k₁→Bool) (scale : ℕ)

def word (p : List Bool×List Bool) := (encodePair p).map alphabet.invFun

def fuel (p : List Bool×List Bool) := ((encodePair p).length+1)*scale

def relation : Set (List Bool×List Bool) :=
  {p | BudgetGuard.boundedOutput M output (fuel scale p) (initList M (word M alphabet p))=true}

theorem linear : DecidableInTime encodePair (relation M alphabet output scale)
    (fun n=>BudgetGuard.coefficient scale M*n+BudgetGuard.coefficient scale M) := by
  let answer:=fun p=>BudgetGuard.boundedOutput M output (fuel scale p) (initList M (word M alphabet p))
  let K:=BudgetGuard.coefficient scale M
  refine ⟨answer,fun _=>Iff.rfl,?_,fun n=>?_⟩
  · exact {
      tm:=BudgetGuard.machine scale M (alphabet.invFun (.inl false)) output
      inputAlphabet:=alphabet
      outputAlphabet:=Equiv.refl _
      time:=fun n=>K*(n+1)
      outputsFun:=fun p=>by
        have run:=BudgetGuard.time_guard scale M (alphabet.invFun (.inl false)) output (word M alphabet p)
        change TM2OutputsInTime (BudgetGuard.machine scale M (alphabet.invFun (.inl false)) output) (word M alphabet p) (some [answer p]) (K*((encodePair p).length+1))
        simpa only [answer,K,word,fuel,List.length_map] using run }
  · simp [Nat.mul_add,K]

theorem accepts_iff (p : List Bool×List Bool) :
    p∈relation M alphabet output scale ↔
      ∃ h≤fuel scale p,∃ d : M.Cfg,(flip bind M.step)^[h] (some (initList M (word M alphabet p)))=some d ∧
        d.l=none ∧ ((d.stk M.k₁).head?.map output).getD false=true := by
  constructor
  · exact BudgetGuard.bounded_true_run M output _ _
  · rintro ⟨h,hh,d,run,stop,out⟩
    exact (BudgetGuard.bounded_agrees M output h _ _ d run stop hh).trans out

theorem raw_yes (p : List Bool×List Bool) (z : M.Γ M.k₁) (v:output z=true)
    (n : ℕ) (run:TM2OutputsInTime M (word M alphabet p) (some [z]) n) (fits:n≤fuel scale p) :
    p∈relation M alphabet output scale :=
  (BudgetGuard.bounded_outputs M output _ z n _ run fits).trans v

end RawClock

#print axioms RawClock.linear
#print axioms RawClock.accepts_iff

namespace StackTrace.OneOpeningGame
open Turing PEqualNP.Library

private theorem three (s : ℕ) (P : List Bool→Prop) :
    Alt 3 s P ↔ ∃ a : Packed.Word s,∀ b : Packed.Word s,∃ z : Packed.Word s,P (a.val++b.val++z.val) := by
  classical
  simp only [Alt,List.append_nil,List.append_assoc,not_not]
  push Not
  constructor
  · rintro ⟨a,ha,h⟩
    refine ⟨⟨a,ha⟩,fun b=>?_⟩
    obtain ⟨z,hz,hp⟩:=h b.val b.property
    exact ⟨⟨z,hz⟩,hp⟩
  · rintro ⟨a,h⟩
    refine ⟨a.val,a.property,fun b hb=>?_⟩
    obtain ⟨z,hp⟩:=h ⟨b,hb⟩
    exact ⟨z.val,z.property,hp⟩

/-- A raw implementation need only produce timely honest accepts and have sound
accepting halts. The verifier used for SigmaV is guarded on every binary input,
including malformed and unexpectedly short words. -/
theorem guarded_game (L : Language Bool) (s : ℕ→ℕ) (R : Set (List Bool×List Bool))
    (game:∀ x,x∈L ↔ Alt 3 (s x.length) (fun w=>(x,w)∈R))
    (M : FinTM2) (alphabet : M.Γ M.k₀ ≃ Bool ⊕ Bool) (output : M.Γ M.k₁→Bool) (scale : ℕ)
    (sound:∀ x (a b z : Packed.Word (s x.length)) h (d : M.Cfg),
      let p:=(x,a.val++b.val++z.val)
      (flip bind M.step)^[h] (some (initList M (RawClock.word M alphabet p)))=some d →
      d.l=none → ((d.stk M.k₁).head?.map output).getD false=true → p∈R)
    (complete:∀ x (a b z : Packed.Word (s x.length)), (x,a.val++b.val++z.val)∈R →
      ∃ z' : Packed.Word (s x.length),let p:=(x,a.val++b.val++z'.val)
      ∃ v : M.Γ M.k₁,output v=true ∧ ∃ h≤RawClock.fuel scale p,
        Nonempty (TM2OutputsInTime M (RawClock.word M alphabet p) (some [v]) h)) :
    L∈SigmaV 3 s := by
  refine ⟨RawClock.relation M alphabet output scale,BudgetGuard.coefficient scale M,
    RawClock.linear M alphabet output scale,fun x=>?_⟩
  rw [game x,three,three]
  constructor
  · rintro ⟨a,win⟩
    refine ⟨a,fun b=>?_⟩
    obtain ⟨z,hz⟩:=win b
    obtain ⟨z',v,hv,h,hh,⟨hr⟩⟩:=complete x a b z hz
    exact ⟨z',RawClock.raw_yes M alphabet output scale _ v hv h hr hh⟩
  · rintro ⟨a,win⟩
    refine ⟨a,fun b=>?_⟩
    obtain ⟨z,hz⟩:=win b
    obtain ⟨h,_,d,run,stop,res⟩:=(RawClock.accepts_iff M alphabet output scale _).mp hz
    exact ⟨z,sound x a b z h d run stop res⟩

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.guarded_game
