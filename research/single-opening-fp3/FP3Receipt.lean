import FP3KernelC
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic

namespace SharedBatch
open Turing

inductive Store (K : Type) where
  | engine (k : K) | input | shared | temp | out
  deriving DecidableEq,Fintype

inductive Label (L : Type) where
  | head | dispatch | job | copy | restore | sim (l : L) | back | clean
  deriving DecidableEq,Fintype

abbrev A (tm : FinTM2) := tm.Γ tm.k₀
abbrev Alphabet (tm : FinTM2) : Store tm.K→Type
  | .engine k=>tm.Γ k
  | .input=>Option (A tm)
  | .shared | .temp=>A tm
  | .out=>Bool
abbrev Reg (tm : FinTM2) := tm.σ × Option (Option (A tm)) × Bool
abbrev St (tm : FinTM2) := TM2.Stmt (Alphabet tm) (Label tm.Λ) (Reg tm)
abbrev Src (tm : FinTM2) := TM2.Stmt tm.Γ tm.Λ tm.σ
abbrev Cell (tm : FinTM2) := (k : tm.K)→List (tm.Γ k)

private def fresh (tm : FinTM2) (v : tm.σ) (g : Bool) : Reg tm := (v,none,g)
private def cached (tm : FinTM2) (r : Reg tm) (x : Option (Option (A tm))) : Reg tm := (r.1,x,r.2.2)
private def value (tm : FinTM2) (blank : A tm) (r : Reg tm) : A tm := r.2.1.join.getD blank
private def goto (tm : FinTM2) (l : Label tm.Λ) : St tm :=
  .load (fun r=>fresh tm r.1 r.2.2) (.goto (fun _=>l))

def lift (tm : FinTM2) : Src tm→St tm
  | .push k f q=>.push (.engine k) (fun r=>f r.1) (lift tm q)
  | .peek k f q=>.peek (.engine k) (fun r a=>(f r.1 a,r.2)) (lift tm q)
  | .pop k f q=>.pop (.engine k) (fun r a=>(f r.1 a,r.2)) (lift tm q)
  | .load f q=>.load (fun r=>(f r.1,r.2)) (lift tm q)
  | .branch f q p=>.branch (fun r=>f r.1) (lift tm q) (lift tm p)
  | .goto f=>.goto (fun r=>.sim (f r.1))
  | .halt=>.goto (fun _=>.back)

def program (tm : FinTM2) (blank : A tm) (test : tm.Γ tm.k₁→Bool) : Label tm.Λ→St tm
  | .head=>.pop .input (cached tm) <| .branch (fun r=>r.2.1.join.isSome)
      (.push .shared (value tm blank) (goto tm .head)) (goto tm .dispatch)
  | .dispatch=>.peek .input (cached tm) <| .branch (fun r=>r.2.1.isSome)
      (goto tm .job) (goto tm .clean)
  | .job=>.pop .input (cached tm) <| .branch (fun r=>r.2.1.join.isSome)
      (.push (.engine tm.k₀) (value tm blank) (goto tm .job)) (goto tm .copy)
  | .copy=>.pop .shared (fun r a=>cached tm r (a.map some)) <| .branch (fun r=>r.2.1.isSome)
      (.push .temp (value tm blank) (.push (.engine tm.k₀) (value tm blank) (goto tm .copy)))
      (goto tm .restore)
  | .restore=>.pop .temp (fun r a=>cached tm r (a.map some)) <| .branch (fun r=>r.2.1.isSome)
      (.push .shared (value tm blank) (goto tm .restore)) (goto tm (.sim tm.main))
  | .sim l=>lift tm (tm.m l)
  | .back=>.pop (.engine tm.k₁) (fun r a=>fresh tm tm.initialState (r.2.2 && (a.map test).getD false))
      (goto tm .dispatch)
  | .clean=>.pop .shared (fun r a=>cached tm r (a.map some)) <| .branch (fun r=>r.2.1.isSome)
      (goto tm .clean) (.push .out (fun r=>r.2.2) (.load (fun _=>fresh tm tm.initialState true) .halt))

def machine (tm : FinTM2) (blank : A tm) (test : tm.Γ tm.k₁→Bool) : FinTM2 := by
  let _:=tm.kFin
  let _:=tm.ΛFin
  let _:=tm.σFin
  let _:=tm.Γk₀Fin
  exact {
    K:=Store tm.K,k₀:=.input,k₁:=.out,Γ:=Alphabet tm,Λ:=Label tm.Λ,main:=.head,
    σ:=Reg tm,initialState:=fresh tm tm.initialState true,m:=program tm blank test }

structure Aux (tm : FinTM2) where
  input : List (Option (A tm))
  shared : List (A tm)
  temp : List (A tm)
  out : List Bool

def bank (tm : FinTM2) (S : Cell tm) (aux : Aux tm) : (k : Store tm.K)→List (Alphabet tm k)
  | .engine k=>S k
  | .input=>aux.input
  | .shared=>aux.shared
  | .temp=>aux.temp
  | .out=>aux.out

private theorem engine_set (tm : FinTM2) (S : Cell tm) (aux : Aux tm) (k : tm.K) (xs : List (tm.Γ k)) :
    Function.update (bank tm S aux) (.engine k) xs=bank tm (Function.update S k xs) aux := by
  funext t
  cases t with
  | engine j=>
    by_cases h : j=k
    · subst j;simp [Function.update,bank]
    · simp [Function.update,bank,h]
  | input | shared | temp | out=>simp [Function.update,bank]

private theorem inp_set (tm : FinTM2) (S : Cell tm) (a : Aux tm) (xs : List (Option (A tm))) :
    Function.update (bank tm S a) .input xs=bank tm S {a with input:=xs} := by
  funext t;cases t <;> simp [Function.update,bank]
private theorem shared_set (tm : FinTM2) (S : Cell tm) (a : Aux tm) (xs : List (A tm)) :
    Function.update (bank tm S a) .shared xs=bank tm S {a with shared:=xs} := by
  funext t;cases t <;> simp [Function.update,bank]
private theorem temp_set (tm : FinTM2) (S : Cell tm) (a : Aux tm) (xs : List (A tm)) :
    Function.update (bank tm S a) .temp xs=bank tm S {a with temp:=xs} := by
  funext t;cases t <;> simp [Function.update,bank]
private theorem out_set (tm : FinTM2) (S : Cell tm) (a : Aux tm) (xs : List Bool) :
    Function.update (bank tm S a) .out xs=bank tm S {a with out:=xs} := by
  funext t;cases t <;> simp [Function.update,bank]

private def next {L : Type} : Option L→Label L
  | none=>.back
  | some l=>.sim l

private theorem lift_correct (tm : FinTM2) (q : Src tm) (v : tm.σ) (S : Cell tm) (aux : Aux tm)
    (x : Option (Option (A tm))) (g : Bool) :
    TM2.stepAux (lift tm q) (v,x,g) (bank tm S aux) =
      let r:=TM2.stepAux q v S
      ⟨some (next r.l),(r.var,x,g),bank tm r.stk aux⟩ := by
  induction q generalizing v S with
  | push k f q ih=>
    change TM2.stepAux (lift tm q) _ (Function.update (bank tm S aux) (.engine k) (f v::S k))=_
    rw [engine_set];exact ih v _
  | pop k f q ih=>
    change TM2.stepAux (lift tm q) _ (Function.update (bank tm S aux) (.engine k) (S k).tail)=_
    rw [engine_set];exact ih (f v (S k).head?) _
  | peek k f q ih=>exact ih (f v (S k).head?) S
  | load f q ih=>exact ih (f v) S
  | branch f q p iq ip=>cases h:f v <;>simp [lift,h,iq,ip]
  | goto f | halt=>rfl

def encode {A : Type} (pre : List A) (jobs : List (List A)) : List (Option A) :=
  pre.map some ++ none :: jobs.flatMap (fun job=>job.reverse.map some++[none])

end SharedBatch
namespace SharedBatch
open Turing

private abbrev Walk {X : Type} (step : X→Option X) (n : ℕ) (c d : X) :=
  (flip bind step)^[n] (some c)=some d

private theorem before {X : Type} {step : X→Option X} {a b c : X} {n : ℕ}
    (h : step a=some b) (later : Walk step n b c) : Walk step (n+1) a c := by
  unfold Walk;rw [Function.iterate_succ_apply]
  change (flip bind step)^[n] (step a)=_
  rwa [h]

private theorem combine {X : Type} {step : X→Option X} {a b c : X} {n m : ℕ}
    (h : Walk step n a b) (g : Walk step m b c) : Walk step (n+m) a c := by
  unfold Walk at *;rw [Nat.add_comm,Function.iterate_add_apply,h,g]

private def empty (tm : FinTM2) : Cell tm := fun _=>[]
private def cells (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k)) : Cell tm := Function.update (empty tm) k xs
private theorem reset_cells (tm : FinTM2) (k : tm.K) : cells tm k []=empty tm := by
  funext j;by_cases h:j=k
  · subst j;simp [cells,empty,Function.update]
  · simp [cells,empty,Function.update,h]
private theorem put_cells (tm : FinTM2) (k : tm.K) (xs ys : List (tm.Γ k)) :
    Function.update (cells tm k xs) k ys=cells tm k ys := Function.update_idem .. 
private theorem peek_cells (tm : FinTM2) (k : tm.K) (xs : List (tm.Γ k)) : cells tm k xs k=xs :=
  Function.update_self ..

private def frame (tm : FinTM2) (l : Label tm.Λ) (g : Bool) (inp : List (Option (A tm))) (h v : List (A tm))
    (S : Cell tm) : TM2.Cfg (Alphabet tm) (Label tm.Λ) (Reg tm) :=
  ⟨some l,fresh tm tm.initialState g,bank tm S ⟨inp,h,v,[]⟩⟩

variable (tm : FinTM2) (blank : A tm) (test : tm.Γ tm.k₁→Bool)

private abbrev step := TM2.step (program tm blank test)

private theorem head_list (xs : List (A tm)) (tail : List (Option (A tm))) (acc : List (A tm)) :
    Walk (step tm blank test) (xs.length+1)
      (frame tm .head true (xs.map some++none::tail) acc [] (empty tm))
      (frame tm .dispatch true tail (xs.reverse++acc) [] (empty tm)) := by
  induction xs generalizing acc with
  | nil=>
    apply before (n:=0) ?_ (by rfl)
    simp [step,frame,program,fresh,cached,goto,TM2.step,TM2.stepAux,inp_set,bank]
  | cons a xs ih=>
    have run:=ih (a::acc)
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at *
    apply before _ run
    simp [step,frame,program,fresh,cached,value,goto,TM2.step,TM2.stepAux,inp_set,shared_set,bank]

private theorem dispatch_job (z : Option (A tm)) (zs : List (Option (A tm))) (pre : List (A tm)) (g : Bool) :
    step tm blank test (frame tm .dispatch g (z::zs) pre [] (empty tm)) =
      some (frame tm .job g (z::zs) pre [] (empty tm)) := by rfl

private theorem job_list (ys : List (A tm)) (rest : List (Option (A tm))) (pre acc : List (A tm)) (g : Bool) :
    Walk (step tm blank test) (ys.length+1)
      (frame tm .job g (ys.map some++none::rest) pre [] (cells tm tm.k₀ acc))
      (frame tm .copy g rest pre [] (cells tm tm.k₀ (ys.reverse++acc))) := by
  induction ys generalizing acc with
  | nil=>
    apply before (n:=0) ?_ (by rfl)
    simp [step,frame,program,fresh,cached,goto,TM2.step,TM2.stepAux,inp_set,bank]
  | cons a ys ih=>
    have run:=ih (a::acc)
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at *
    apply before _ run
    simp [step,frame,program,fresh,cached,value,goto,TM2.step,TM2.stepAux,inp_set,engine_set,
      bank,peek_cells,put_cells]

private theorem copy_list (ys : List (A tm)) (rest : List (Option (A tm))) (temp acc : List (A tm)) (g : Bool) :
    Walk (step tm blank test) (ys.length+1)
      (frame tm .copy g rest ys temp (cells tm tm.k₀ acc))
      (frame tm .restore g rest [] (ys.reverse++temp) (cells tm tm.k₀ (ys.reverse++acc))) := by
  induction ys generalizing acc temp with
  | nil=>
    apply before (n:=0) ?_ (by rfl)
    simp [step,frame,program,fresh,cached,goto,TM2.step,TM2.stepAux,shared_set,bank]
  | cons a ys ih=>
    have run:=ih (a::temp) (a::acc)
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at *
    apply before _ run
    simp [step,frame,program,fresh,cached,value,goto,TM2.step,TM2.stepAux,shared_set,temp_set,
      engine_set,bank,peek_cells,put_cells]

private theorem restore_list (ys : List (A tm)) (rest : List (Option (A tm))) (pre : List (A tm)) (S : Cell tm) (g : Bool) :
    Walk (step tm blank test) (ys.length+1)
      (frame tm .restore g rest pre ys S)
      (frame tm (.sim tm.main) g rest (ys.reverse++pre) [] S) := by
  induction ys generalizing pre with
  | nil=>
    apply before (n:=0) ?_ (by rfl)
    simp [step,frame,program,fresh,cached,goto,TM2.step,TM2.stepAux,temp_set,bank]
  | cons a ys ih=>
    have run:=ih (a::pre)
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append] at *
    apply before _ run
    simp [step,frame,program,fresh,cached,value,goto,TM2.step,TM2.stepAux,temp_set,shared_set,bank]

private def embed (tm : FinTM2) (aux : Aux tm) (good : Bool) (c : tm.Cfg) :
    TM2.Cfg (Alphabet tm) (Label tm.Λ) (Reg tm) :=
  ⟨some (next c.l),fresh tm c.var good,bank tm c.stk aux⟩

private theorem embed_run (aux : Aux tm) (g : Bool) (n : ℕ) (c d : tm.Cfg)
    (h : Walk tm.step n c d) : Walk (step tm blank test) n (embed tm aux g c) (embed tm aux g d) := by
  induction n generalizing c d with
  | zero=>
    change some c=some d at h
    cases h;rfl
  | succ n ih=>
    unfold Walk at h
    rw [Function.iterate_succ_apply] at h
    change (flip bind tm.step)^[n] (tm.step c)=_ at h
    cases c with
    | mk l v S=>
      cases l with
      | none=>
        change (flip bind tm.step)^[n] none=some d at h
        rw [Function.iterate_fixed (show (flip bind tm.step) none=none from rfl)] at h
        cases h
      | some l=>
        let nxt:=TM2.stepAux (tm.m l) v S
        have middle : step tm blank test (embed tm aux g ⟨some l,v,S⟩)=some (embed tm aux g nxt) := by
          simp [step,embed,fresh,next,TM2.step,program,lift_correct,nxt]
        exact before middle (ih nxt d h)

private theorem return_step (rest : List (Option (A tm))) (pre : List (A tm)) (b : tm.Γ tm.k₁) (g : Bool) :
    step tm blank test (frame tm .back g rest pre [] (cells tm tm.k₁ [b]))=
      some (frame tm .dispatch (g&&test b) rest pre [] (empty tm)) := by
  simp [step,frame,program,fresh,goto,TM2.step,TM2.stepAux,peek_cells,put_cells,engine_set,reset_cells,bank]

private theorem clean_list (pre : List (A tm)) (g : Bool) :
    Walk (step tm blank test) (pre.length+1) (frame tm .clean g [] pre [] (empty tm))
      (haltList (machine tm blank test) [g]) := by
  induction pre with
  | nil=>
    apply before (n:=0) ?_ (by rfl)
    have finalEq : (⟨none,fresh tm tm.initialState true,bank tm (empty tm) ⟨[],[],[],[g]⟩⟩ :
      TM2.Cfg (Alphabet tm) (Label tm.Λ) (Reg tm))=haltList (machine tm blank test) [g] := by
      unfold haltList;congr 1;funext k;cases k <;>rfl
    rw [←finalEq]
    simp [step,frame,program,fresh,cached,TM2.step,TM2.stepAux,shared_set,out_set,bank]
  | cons a pre ih=>
    apply before _ ih
    simp [step,frame,program,fresh,cached,goto,TM2.step,TM2.stepAux,shared_set,bank]

end SharedBatch
namespace SharedBatch
open Turing

structure Ticket (tm : FinTM2) where
  job : List (A tm)
  result : tm.Γ tm.k₁
  clock : ℕ

def charge (pre : List (A tm)) (t : Ticket tm) := t.job.length+2*pre.length+t.clock+5

def suffix {tm : FinTM2} (ts : List (Ticket tm)) : List (Option (A tm)) :=
  ts.flatMap fun t=>t.job.reverse.map some++[none]

def valueOf {tm : FinTM2} (test : tm.Γ tm.k₁→Bool) (ts : List (Ticket tm)) :=
  ts.all fun t=>test t.result

variable (tm : FinTM2) (blank : A tm) (test : tm.Γ tm.k₁→Bool)

private theorem one (pre : List (A tm)) (t : Ticket tm) (g : Bool) (rest : List (Option (A tm)))
    (run : TM2OutputsInTime tm (pre++t.job) (some [t.result]) t.clock) :
    ∃ k≤charge pre t, Walk (step tm blank test) k
      (frame tm .dispatch g (t.job.reverse.map some++none::rest) pre.reverse [] (empty tm))
      (frame tm .dispatch (g&&test t.result) rest pre.reverse [] (empty tm)) := by
  have begin : step tm blank test (frame tm .dispatch g (t.job.reverse.map some++none::rest) pre.reverse [] (empty tm))=
      some (frame tm .job g (t.job.reverse.map some++none::rest) pre.reverse [] (empty tm)) := by
    cases e:t.job.reverse.map some <;>apply dispatch_job
  have r1:=job_list tm blank test t.job.reverse rest pre.reverse [] g
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,reset_cells] at r1
  have r2:=copy_list tm blank test pre.reverse rest [] t.job g
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at r2
  have r3:=restore_list tm blank test pre rest [] (cells tm tm.k₀ (pre++t.job)) g
  simp only [List.append_nil] at r3
  have r4 : Walk (step tm blank test) run.steps
      (frame tm (.sim tm.main) g rest pre.reverse [] (cells tm tm.k₀ (pre++t.job)))
      (frame tm .back g rest pre.reverse [] (cells tm tm.k₁ [t.result])) :=
    by
      have ini : (initList tm (pre++t.job)).stk=cells tm tm.k₀ (pre++t.job) := by
        funext j;by_cases hj:j=tm.k₀
        · subst j;simp [initList,cells,Function.update]
        · simp [initList,cells,Function.update,empty,hj]
      have fin : (haltList tm [t.result]).stk=cells tm tm.k₁ [t.result] := by
        funext j;by_cases hj:j=tm.k₁
        · subst j;simp [haltList,cells,Function.update]
        · simp [haltList,cells,Function.update,empty,hj]
      have e:=embed_run tm blank test ⟨rest,pre.reverse,[],[]⟩ g run.steps _ _ run.evals_in_steps
      unfold embed at e
      rw [ini,fin] at e
      exact e
  have r5:=return_step tm blank test rest pre.reverse t.result g
  have last : Walk (step tm blank test) 1
      (frame tm .back g rest pre.reverse [] (cells tm tm.k₁ [t.result]))
      (frame tm .dispatch (g&&test t.result) rest pre.reverse [] (empty tm)) := before r5 (by rfl)
  refine ⟨_,?_,combine (combine (combine (combine (before begin r1) r2) r3) r4) last⟩
  dsimp [charge]
  have :=run.steps_le_m
  omega

private theorem jobs (pre : List (A tm)) (ts : List (Ticket tm)) (g : Bool)
    (runs : ∀ t∈ts, Nonempty (TM2OutputsInTime tm (pre++t.job) (some [t.result]) t.clock)) :
    ∃ k≤(ts.map (charge pre)).sum+pre.length+2, Walk (step tm blank test) k
      (frame tm .dispatch g (suffix ts) pre.reverse [] (empty tm))
      (haltList (machine tm blank test) [g && valueOf test ts]) := by
  induction ts generalizing g with
  | nil=>
    have h : step tm blank test (frame tm .dispatch g [] pre.reverse [] (empty tm))=
      some (frame tm .clean g [] pre.reverse [] (empty tm)) := rfl
    have clear:=before h (clean_list tm blank test pre.reverse g)
    refine ⟨pre.length+2,by simp,?_⟩
    simpa [suffix,valueOf,Nat.add_assoc] using clear
  | cons t ts ih=>
    obtain ⟨hit⟩:=runs t (by simp)
    obtain ⟨k,hk,first⟩:=one tm blank test pre t g (suffix ts) hit
    obtain ⟨m,hm,tail⟩:=ih (g&&test t.result) (fun z hz=>runs z (List.mem_cons_of_mem _ hz))
    refine ⟨k+m,by simp only [List.map_cons,List.sum_cons];omega,?_⟩
    simpa [suffix,valueOf,List.append_assoc,Bool.and_assoc] using combine first tail

/-- The immutable first string appears once in the physical input and is restored for
each subcall. The outer machine returns the conjunction of the actual singleton answers. -/
theorem runs (pre : List (A tm)) (ts : List (Ticket tm))
    (correct : ∀ t∈ts, Nonempty (TM2OutputsInTime tm (pre++t.job) (some [t.result]) t.clock)) :
    Nonempty (TM2OutputsInTime (machine tm blank test) (encode pre (ts.map Ticket.job))
      (some [valueOf test ts]) ((ts.map (charge pre)).sum+2*pre.length+3)) := by
  have start:=head_list tm blank test pre (suffix ts) []
  simp only [List.append_nil] at start
  obtain ⟨k,hk,tail⟩:=jobs tm blank test pre ts true correct
  have init : initList (machine tm blank test) (encode pre (ts.map Ticket.job))=
      frame tm .head true (pre.map some++none::suffix ts) [] [] (empty tm) := by
    have flat : (ts.map Ticket.job).flatMap (fun job=>job.reverse.map some++[none])=suffix ts := by
      simp [suffix,List.flatMap_map,Function.comp_def]
    unfold encode;rw [flat]
    unfold initList frame
    congr 1;funext k;cases k <;>rfl
  refine ⟨⟨⟨pre.length+1+k,?_⟩,show pre.length+1+k≤(ts.map (charge pre)).sum+2*pre.length+3 from by omega⟩⟩
  change (flip bind (machine tm blank test).step)^[pre.length+1+k]
    (some (initList (machine tm blank test) (encode pre (ts.map Ticket.job)))) =
    some (haltList (machine tm blank test) [valueOf test ts])
  rw [init,show (machine tm blank test).step=step tm blank test from rfl]
  have doneRun:=combine start tail
  simp only [Bool.true_and] at doneRun
  exact doneRun

end SharedBatch

#print axioms SharedBatch.runs

namespace OwnedRadix.Batch
open Turing OwnedRadix.Code

structure Claim where
  args : List Bool
  bit : Bool
  opening : List Bool

def common (c : List Bool) : List Parameter.Symbol :=
  c.reverse.map fun b=>Sum.inl (false,b)

def job (p : Claim) : List Parameter.Symbol :=
  (p.args++[p.bit]).reverse.map (fun b=>Sum.inl (true,b)) ++ p.opening.map Sum.inr

theorem request (c : List Bool) (p : Claim) :
    common c++job p=Parameter.triple c (p.args++[p.bit]) p.opening := by
  simp only [common,job,Parameter.triple,List.append_assoc];rfl

noncomputable def checker := SharedBatch.machine queryVerifier (Sum.inr false) id

def stream (c : List Bool) (ps : List Claim) : List (Option Parameter.Symbol) :=
  SharedBatch.encode (common c) (ps.map job)

private noncomputable def ticket (c : List Bool) (p : Claim) : SharedBatch.Ticket queryVerifier :=
  let result:=(total_query c (p.args++[p.bit]) p.opening).choose
  let clock:=(total_query c (p.args++[p.bit]) p.opening).choose_spec.choose
  ⟨job p,result,clock⟩

private theorem ticket_runs (c : List Bool) (p : Claim) :
    Nonempty (TM2OutputsInTime queryVerifier (common c++job p) (some [(ticket c p).result]) (ticket c p).clock) := by
  change Nonempty (TM2OutputsInTime queryVerifier (common c++job p) _ _)
  rw [request]
  exact (total_query c (p.args++[p.bit]) p.opening).choose_spec.choose_spec

/-- A single physical execution verifies any finite batch using one shared circuit
commitment. Every accepted bit in the batch agrees with every other valid opening
to that commitment at its input. -/
theorem sound (c : List Bool) (ps : List Claim) {n}
    (yes : TM2OutputsInTime checker (stream c ps) (some [true]) n) :
    ∀ p∈ps, Answered c p.args p.bit := by
  let ts:=ps.map (ticket c)
  have run : Nonempty (TM2OutputsInTime checker (stream c ps) (some [SharedBatch.valueOf id ts])
      ((ts.map (SharedBatch.charge (common c))).sum+2*(common c).length+3)) := by
    have h:=SharedBatch.runs queryVerifier (Sum.inr false) id (common c) ts (by
      intro t ht;obtain ⟨p,_,rfl⟩:=List.mem_map.mp ht;exact ticket_runs c p)
    have jobs : ts.map SharedBatch.Ticket.job = ps.map job := by
      change (ps.map (ticket c)).map _ = _
      rw [List.map_map]
      rfl
    rw [jobs] at h
    exact h
  have pass : SharedBatch.valueOf id ts=true:=(List.cons.inj (machine_answers_agree run.some yes)).1
  intro p hp
  have mem:(ticket c p)∈ts:=List.mem_map_of_mem hp
  have good:(ticket c p).result=true:=List.all_eq_true.mp pass (ticket c p) mem
  have witness:=ticket_runs c p
  change Nonempty (TM2OutputsInTime queryVerifier (common c++job p) _ _) at witness
  rw [request,good] at witness
  exact ⟨p.opening,_,witness⟩

/-- Honest openings can be supplied independently. The stated clock charges the
immutable prefix twice per use and all job data once, in addition to the genuine
verifier clocks. -/
theorem complete (c : List Bool) (ps : List Claim) (clock : Claim→ℕ)
    (runs : ∀ p∈ps, Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple c (p.args++[p.bit]) p.opening)
      (some [true]) (clock p))) :
    Nonempty (TM2OutputsInTime checker (stream c ps) (some [true])
      ((ps.map (fun p=>p.args.length+1+p.opening.length+2*c.length+clock p+5)).sum+2*c.length+3)) := by
  let make (p : Claim) : SharedBatch.Ticket queryVerifier := ⟨job p,true,clock p⟩
  let ts:=ps.map make
  have h:=SharedBatch.runs queryVerifier (Sum.inr false) id (common c) ts (by
    intro t ht;obtain ⟨p,hp,rfl⟩:=List.mem_map.mp ht
    change Nonempty (TM2OutputsInTime queryVerifier (common c++job p) (some [true]) (clock p))
    rw [request];exact runs p hp)
  have pass : SharedBatch.valueOf id ts=true := by
    apply List.all_eq_true.mpr;intro t ht;obtain ⟨p,_,rfl⟩:=List.mem_map.mp ht;rfl
  have jobs : ts.map SharedBatch.Ticket.job = ps.map job := by
    change (ps.map make).map _ = _
    rw [List.map_map]
    rfl
  have clen:(common c).length=c.length:=by simp [common]
  have sums:(ts.map (SharedBatch.charge (common c))).sum=
      (ps.map (fun p=>p.args.length+1+p.opening.length+2*c.length+clock p+5)).sum := by
    apply congrArg List.sum
    change (ps.map make).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    change (job p).length+2*(common c).length+clock p+5=_
    simp [job,clen]
    omega
  rw [pass,jobs,sums] at h
  obtain ⟨r⟩:=h
  refine ⟨⟨r.toEvalsTo,r.steps_le_m.trans_eq ?_⟩⟩
  exact congrArg (fun n=>(ps.map (fun p=>p.args.length+1+p.opening.length+2*c.length+clock p+5)).sum+2*n+3) clen

end OwnedRadix.Batch

#print axioms OwnedRadix.Batch.sound
#print axioms OwnedRadix.Batch.complete

namespace OwnedRadix.Batch
open Turing OwnedRadix.Code

abbrev Request := List Bool × Bool

def asks (ps : List Claim) : List Request := ps.map fun p=>(p.args,p.bit)

/-- A successful physical batch with fixed per-opening and bit-clock bounds.
The clock includes resetting and copying the retained commitment on each queried bit. -/
def Endorsed (c : List Bool) (qs : List Request) (W K : ℕ) : Prop :=
  ∃ ps : List Claim, asks ps=qs ∧ (∀ p∈ps,p.opening.length≤W) ∧
    ∃ n≤(qs.map (fun q=>q.1.length+1+W+2*c.length+K+5)).sum+2*c.length+3,
      Nonempty (TM2OutputsInTime checker (stream c ps) (some [true]) n)

theorem endorsed_sound {c : List Bool} {qs : List Request} {W K : ℕ} (h : Endorsed c qs W K) :
    ∀ q∈qs, Answered c q.1 q.2 := by
  obtain ⟨ps,rfl,_,_,_,⟨yes⟩⟩:=h
  intro q hq
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hq
  exact sound c ps yes p hp

private theorem map_sum_le {X : Type} (ls : List X) (f g : X→ℕ) (h : ∀ x∈ls,f x≤g x) :
    (ls.map f).sum≤(ls.map g).sum := by
  induction ls with
  | nil=>rfl
  | cons a l ih=>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun x hx=>h x (by simp [hx])))

/-- Completeness requires a short opening for each actual request. Their machine
runs can be combined entirely within one shared-commitment stack machine. -/
theorem endorsed_complete (c : List Bool) (qs : List Request) (W K : ℕ)
    (ok : ∀ q∈qs,∃ w : List Bool, w.length≤W ∧
      Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple c (q.1++[q.2]) w) (some [true]) K)) :
    Endorsed c qs W K := by
  classical
  let witness (q : Request) := if h:q∈qs then (ok q h).choose else []
  let mk (q : Request) : Claim := ⟨q.1,q.2,witness q⟩
  let ps:=qs.map mk
  have hw {q : Request} (hq : q∈qs) : (witness q).length≤W ∧
      Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple c (q.1++[q.2]) (witness q)) (some [true]) K) := by
    simpa only [witness,dif_pos hq] using (ok q hq).choose_spec
  have agree : asks ps=qs:=by simp [asks,ps,mk,List.map_map,Function.comp_def]
  have px : ∀ p∈ps,p.opening.length≤W := by
    intro p hp;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp;exact (hw hq).1
  have yes:=complete c ps (fun _=>K) (by
    intro p hp;obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp;exact (hw hq).2)
  refine ⟨ps,agree,px,_,?_,yes⟩
  have term (q : Request) (hq : q∈qs) :
      q.1.length+1+(witness q).length+2*c.length+K+5 ≤ q.1.length+1+W+2*c.length+K+5 := by
    have := (hw hq).1;omega
  have total:=map_sum_le qs _ _ term
  simp only [ps,List.map_map,Function.comp_def,mk]
  omega

end OwnedRadix.Batch

#print axioms OwnedRadix.Batch.endorsed_sound
#print axioms OwnedRadix.Batch.endorsed_complete

namespace OwnedRadix.Batch
open OwnedRadix.Code Turing

/-- A single commitment handles every finite batch of inputs to an official circuit.
Every input in a batch receives an honest transcript under the same per-bit bounds. -/
theorem all_batches {m gates : ℕ} {f : (Fin m→Bool)→Bool}
    (C : PEqualNP.MetaComplexity.HasCircuitSize m f gates) (d : ℕ) (addr : m+gates≤2^d) :
    let W:=(6*(d+1)+9)*(2+m+gates)+2*(d+1)+3
    let clock:=(7*(d+1)+23)*W+19
    ∃ c : List Bool,c.length≤W ∧ ∀ inputs : List (Fin m→Bool),
      Endorsed c (inputs.map fun q=>([false,true]++List.ofFn q,f q)) W clock := by
  let W:=(6*(d+1)+9)*(2+m+gates)+2*(d+1)+3
  obtain ⟨c,hc,runs,_⟩:=OwnedRadix.Compiler.realize_official C d addr
  refine ⟨c,hc,fun inputs=>?_⟩
  apply endorsed_complete
  intro claim hm
  obtain ⟨q,_,rfl⟩:=List.mem_map.mp hm
  obtain ⟨w,hlen,⟨run⟩⟩:=runs q
  refine ⟨w,hlen,⟨⟨run.toEvalsTo,run.steps_le_m.trans ?_⟩⟩⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) _

private theorem payloadLength {A : Type} (jobs : List (List A)) :
    (jobs.flatMap (fun j=>j.reverse.map some++[none])).length=(jobs.map List.length).sum+jobs.length := by
  induction jobs with
  | nil=>rfl
  | cons j jobs ih=>
    simp only [List.flatMap_cons,List.length_append,List.length_map,List.length_reverse,List.map_cons,
      List.sum_cons,List.length_cons,List.length_nil,ih]
    omega

theorem stream_length (c : List Bool) (ps : List Claim) :
    (stream c ps).length=c.length+1+(ps.map fun p=>p.args.length+1+p.opening.length).sum+ps.length := by
  simp [stream,SharedBatch.encode,common,job,payloadLength,List.map_map,Function.comp_def]
  omega

theorem witness_bits {c : List Bool} {qs : List Request} {W k : ℕ} (e : Endorsed c qs W k) :
    ∃ ps : List Claim, asks ps=qs ∧
      (ps.map fun p=>p.opening.length).sum≤qs.length*W ∧
      ∃ n,Nonempty (TM2OutputsInTime checker (stream c ps) (some [true]) n) := by
  obtain ⟨ps,rfl,hs,n,_,run⟩:=e
  refine ⟨ps,rfl,?_,n,run⟩
  have count:=map_sum_le ps (fun p=>p.opening.length) (fun _=>W) hs
  simpa [asks,List.map_const,Nat.nsmul_eq_mul] using count

end OwnedRadix.Batch

#print axioms OwnedRadix.Batch.all_batches
#print axioms OwnedRadix.Batch.witness_bits
