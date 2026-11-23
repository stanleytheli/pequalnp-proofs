import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import PEqualNP.Library.Machines.Transducer
import PEqualNP.Library.Machines.ComposeRun
import PEqualNP.Defs
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.OfFn

namespace OwnedRadix

abbrev Mark := Bool × Bool
abbrev Record := List Bool × Mark
inductive Token where | key (b : Bool) | value (m : Mark) | close deriving DecidableEq

def encode (r : Record) := r.1.map Token.key ++ [.value r.2]
def body (rs : List Record) := rs.flatMap encode
def group (rs : List Record) := body rs++[.close]
def optionalGroup (rs : List Record) := if rs=[] then [] else group rs

def child (b : Bool) (rs : List Record) := rs.filterMap fun r=>match r.1 with
  | []=>none
  | h::t=>if h=b then some (t,r.2) else none

def values (k : List Bool) (rs : List Record) : List Mark :=
  rs.filterMap fun r=>if r.1=k then some r.2 else none

def allowed (seen old : Bool) (m : Mark) : Bool :=
  if seen then !m.1 && (old==m.2) else m.1

def observe (S : Bool × Bool × Bool) (m : Mark) : Bool × Bool × Bool :=
  (true,if S.1 then S.2.1 else m.2,S.2.2 && allowed S.1 S.2.1 m)

def validFrom (seen old : Bool) : List Mark → Bool
  | []=>true
  | m::ms=>allowed seen old m && validFrom true (if seen then old else m.2) ms

private theorem walk_ok (z o g : Bool) (ms : List Mark) :
    (ms.foldl observe (z,o,g)).2.2 = (g && validFrom z o ms) := by
  induction ms generalizing z o g with
  | nil=>simp [validFrom]
  | cons m ms ih=>
    simp only [List.foldl_cons,observe,validFrom]
    rw [ih,Bool.and_assoc]

def fine (rs : List Record) : Bool := rs.all fun r=>validFrom false false (values r.1 rs)
def cleanRoot (rs : List Record) : Bool := validFrom false false (values [] rs)

def weight (rs : List Record) := (rs.map (fun r=>(r.1.length+1)^2)).sum

private theorem child_nil (b : Bool) : child b []=[] := rfl
private theorem child_root (b : Bool) (v : Mark) (rs : List Record) : child b (([],v)::rs)=child b rs := rfl
private theorem child_step (b h : Bool) (v : Mark) (t : List Bool) (rs : List Record) :
    child b ((h::t,v)::rs)=if h=b then (t,v)::child b rs else child b rs := by by_cases e:h=b <;> simp [child,e]

private theorem values_cons (k : List Bool) (r : Record) (rs : List Record) :
    values k (r::rs)=if r.1=k then r.2::values k rs else values k rs := by
  by_cases e:r.1=k <;> simp [values,e]

private theorem down (b : Bool) (k : List Bool) (rs : List Record) :
    values k (child b rs)=values (b::k) rs := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    obtain ⟨keys,v⟩:=r
    cases keys with
    | nil=>rw [child_root,values_cons];simpa using ih
    | cons h t=>
      rw [child_step,values_cons]
      by_cases eq:h=b
      · subst h; simp [values_cons,ih]
      · simp [eq,ih]

private theorem values_absent (k : List Bool) (rs : List Record)
    (absent : ∀ r∈rs,r.1≠k) : values k rs=[] := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    rw [values_cons,ite_eq_right (absent r List.mem_cons_self)]
    exact ih (fun s hs=>absent s (List.mem_cons_of_mem _ hs))

theorem fine_iff (rs : List Record) :
    fine rs=true ↔ ∀ k, validFrom false false (values k rs)=true := by
  rw [fine,List.all_eq_true]
  constructor
  · intro ok k
    by_cases found : ∃ r∈rs,r.1=k
    · obtain ⟨r,hr,rfl⟩:=found;exact ok r hr
    · rw [values_absent k rs (fun r h eq=>found ⟨r,h,eq⟩)];rfl
  · exact fun all r _=>all r.1

theorem decompose (rs : List Record) : fine rs=(cleanRoot rs && fine (child false rs) && fine (child true rs)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,fine_iff]
  constructor
  · intro all
    exact ⟨⟨all [],fun k=>by rw [down];exact all _⟩,fun k=>by rw [down];exact all _⟩
  · rintro ⟨⟨root,left⟩,right⟩ k
    cases k with
    | nil=>exact root
    | cons b t=>rw [←down];cases b
                · exact left t
                · exact right t

private theorem body_cons (r : Record) (rs : List Record) : body (r::rs)=encode r++body rs := rfl
private theorem encode_length (r : Record) : (encode r).length=r.1.length+1 := by simp [encode]

private theorem group_cost (rs : List Record) :
    (body rs).length+weight (child false rs)+weight (child true rs)≤weight rs := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    obtain ⟨keys,v⟩:=r
    rw [body_cons,List.length_append,encode_length]
    cases keys with
    | nil=>simp only [child_root,weight,List.map_cons,List.sum_cons,List.length_nil,Nat.zero_add,one_pow]; dsimp [weight] at ih;omega
    | cons b t=>
      cases b <;> simp only [child_step,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true,weight,List.map_cons,List.sum_cons,List.length_cons]
        <;> dsimp [weight] at ih <;> nlinarith

private theorem bodies_shrink (rs : List Record) :
    (body (child false rs)).length+(body (child true rs)).length≤(body rs).length := by
  induction rs with
  | nil=>rfl
  | cons r rs ih=>
    obtain ⟨keys,v⟩:=r
    cases keys with
    | nil=>rw [child_root,child_root,body_cons,List.length_append]; omega
    | cons b t=>cases b <;> simp only [child_step,ite_true,Bool.true_eq_false,Bool.false_eq_true,ite_false,body_cons,List.length_append,encode_length,List.length_cons] <;> omega

private theorem body_nonempty {rs : List Record} (h : rs≠[]) : 0<(body rs).length := by
  cases rs with
  | nil=>contradiction
  | cons r rs=>rw [body_cons,List.length_append,encode_length];omega

end OwnedRadix
namespace OwnedRadix
open Turing

instance : Fintype Token := Fintype.ofList [.key false,.key true,.value (false,false),.value (false,true),.value (true,false),.value (true,true),.close] (by intro v;cases v with
  | key b=>cases b <;> simp
  | value m=>obtain ⟨a,b⟩:=m;cases a <;> cases b <;> simp
  | close=>simp)

abbrev K := Option (Option Bool)
private abbrev input : K:=some none
private abbrev bucket (b : Bool) : K:=some (some b)
private abbrev output : K:=none
private abbrev Alphabet : K → Type | none=>Bool | some _=>Token
private abbrev Label := Option (Fin 3 × Bool)
private def scan : Label:=none
private def copyTo (b : Bool) : Label:=some (0,b)
private def prepare (b : Bool) : Label:=some (1,b)
private def flush (b : Bool) : Label:=some (2,b)
private def after (b : Bool) : Label:=if b then prepare false else scan
private abbrev Reg := Option Token × Bool × Bool × Bool
private abbrev St := TM2.Stmt Alphabet Label Reg
private abbrev Bins := Bool → List Token
private def reg (z o g : Bool) : Reg := (none,z,o,g)
private def cached (r : Reg) (t : Option Token) : Reg := (t,r.2)
private def token (r : Reg) := r.1.getD .close
private def bit : Token → Bool | .key b=>b | _=>false
private def isKey : Token → Bool | .key _=>true | _=>false
private def isValue : Token → Bool | .value _=>true | _=>false
private def reset (r : Reg) := reg r.2.1 r.2.2.1 r.2.2.2
private def go (l : Label) : St := .load reset (.goto fun _=>l)
private def close (r : Reg) := reg false false r.2.2.2
private def mark : Token → Mark | .value m=>m | _=>(false,false)
private def leaf (r : Reg) : Reg := (none,observe r.2 (mark (token r)))
private def done (v : Reg → Bool) : St := .push output v (.load (fun _=>reg false false true) .halt)

private def program : Label → St
  | none => .pop input cached <| .branch (fun r=>r.1.isNone) (done fun r=>r.2.2.2)
    (.branch (fun r=>isKey (token r)) (.branch (fun r=>bit (token r)) (go (copyTo true)) (go (copyTo false)))
      (.branch (fun r=>isValue (token r)) (.load leaf (.goto fun _=>scan)) (.load close (.goto fun _=>prepare true))))
  | some (k,b) => if k=0 then .pop input cached <| .branch (fun r=>isKey (token r))
      (.push (bucket b) token (go (copyTo b)))
      (.branch (fun r=>isValue (token r)) (.push (bucket b) token (go scan)) (done fun _=>false))
    else if k=1 then .peek (bucket b) cached <| .branch (fun r=>r.1.isSome)
      (.push input (fun _=>.close) (go (flush b))) (go (after b))
    else .pop (bucket b) cached <| .branch (fun r=>r.1.isSome) (.push input token (go (flush b))) (go (after b))

/-- A fixed finite-control four-stack machine for equality of addressed bits. -/
def machine : FinTM2 where
  K:=K; k₀:=input; k₁:=output; Γ:=Alphabet; Λ:=Label; main:=scan; σ:=Reg; initialState:=reg false false true
  Γk₀Fin:=inferInstanceAs (Fintype Token); m:=program

private def bank (xs : List Token) (B : Bins) (ans : List Bool) : (k : K) → List (Alphabet k)
  | none=>ans | some none=>xs | some (some b)=>B b
private def frame (l : Label) (z o g : Bool) (xs : List Token) (B : Bins) : machine.Cfg :=
  ⟨some l,reg z o g,bank xs B []⟩
private def empty : Bins:=fun _=>[]

private theorem setInput (xs ys : List Token) (B : Bins) (ans : List Bool) :
    Function.update (bank xs B ans) input ys = bank ys B ans := by
  funext k; rcases k with _|_|b <;> rfl
private theorem setBin (xs : List Token) (B : Bins) (ans : List Bool) (b : Bool) (ys : List Token) :
    Function.update (bank xs B ans) (bucket b) ys = bank xs (Function.update B b ys) ans := by
  funext k; rcases k with _|_|c
  · rfl
  · rfl
  · cases b <;> cases c <;> rfl
private theorem setOutput (xs : List Token) (B : Bins) (ans ys : List Bool) :
    Function.update (bank xs B ans) output ys=bank xs B ys := by
  funext k; rcases k with _|_|b <;> rfl

private theorem bank_in (xs : List Token) (B : Bins) (ans : List Bool) : bank xs B ans input=xs := rfl
private theorem bank_bin (xs : List Token) (B : Bins) (ans : List Bool) (b : Bool) : bank xs B ans (bucket b)=B b := rfl
private theorem bank_out (xs : List Token) (B : Bins) (ans : List Bool) : bank xs B ans output=ans := rfl

private theorem scan_key (z o g b : Bool) (xs : List Token) (B : Bins) :
    machine.step (frame scan z o g (.key b::xs) B)=some (frame (copyTo b) z o g xs B) := by
  change TM2.step program _=_
  cases b <;> simp [frame,scan,program,TM2.step,TM2.stepAux,reg,cached,token,bit,isKey,go,reset,bank_in,bank_bin,bank_out,setInput] <;> rfl

private theorem scan_value (z o g : Bool) (m : Mark) (xs : List Token) (B : Bins) :
    machine.step (frame scan z o g (.value m::xs) B)=some
      (frame scan true (if z then o else m.2) (g && allowed z o m) xs B) := by
  change TM2.step program _=_
  simp [frame,scan,program,TM2.step,TM2.stepAux,reg,cached,token,mark,isKey,isValue,leaf,observe,bank_in,bank_bin,bank_out,setInput]
  rfl

private theorem scan_close (z o g : Bool) (xs : List Token) (B : Bins) :
    machine.step (frame scan z o g (.close::xs) B)=some (frame (prepare true) false false g xs B) := by
  change TM2.step program _=_
  simp [frame,scan,program,TM2.step,TM2.stepAux,reg,cached,token,bit,isKey,isValue,close,bank_in,bank_bin,bank_out,setInput] <;> rfl

private theorem copy_key (z o g bucketBit v : Bool) (xs : List Token) (B : Bins) :
    machine.step (frame (copyTo bucketBit) z o g (.key v::xs) B)=
    some (frame (copyTo bucketBit) z o g xs (Function.update B bucketBit (.key v::B bucketBit))) := by
  change TM2.step program _=_
  simp [frame,copyTo,program,TM2.step,TM2.stepAux,reg,cached,token,isKey,go,reset,bank_in,bank_bin,bank_out,setInput,setBin] <;> rfl

private theorem copy_value (z o g b : Bool) (v : Mark) (xs : List Token) (B : Bins) :
    machine.step (frame (copyTo b) z o g (.value v::xs) B)=
    some (frame scan z o g xs (Function.update B b (.value v::B b))) := by
  change TM2.step program _=_
  simp [frame,copyTo,program,TM2.step,TM2.stepAux,reg,cached,token,isKey,isValue,go,reset,bank_in,bank_bin,bank_out,setInput,setBin] <;> rfl

private theorem prepare_step (z o g b : Bool) (xs : List Token) (B : Bins) :
    machine.step (frame (prepare b) z o g xs B)=some (if B b=[] then frame (after b) z o g xs B else frame (flush b) z o g (.close::xs) B) := by
  change TM2.step program _=_
  cases h:B b <;> simp [frame,prepare,program,TM2.step,TM2.stepAux,reg,cached,go,reset,bank_in,bank_bin,bank_out,h,setInput] <;> rfl

private theorem flush_next (z o g b : Bool) (xs : List Token) (B : Bins) (v : Token) (vs : List Token) (h:B b=v::vs) :
    machine.step (frame (flush b) z o g xs B)=some (frame (flush b) z o g (v::xs) (Function.update B b vs)) := by
  change TM2.step program _=_
  simp [frame,flush,program,TM2.step,TM2.stepAux,reg,cached,token,go,reset,bank_in,bank_bin,bank_out,h,setInput,setBin] <;> rfl

private theorem flush_end (z o g b : Bool) (xs : List Token) (B : Bins) (h:B b=[]) :
    machine.step (frame (flush b) z o g xs B)=some (frame (after b) z o g xs B) := by
  have eq:Function.update B b []=B:=Function.update_eq_self_iff.mpr h.symm
  change TM2.step program _=_
  simp [frame,flush,program,TM2.step,TM2.stepAux,reg,cached,go,reset,bank_in,bank_bin,bank_out,h,setInput,setBin,eq] <;> rfl

private theorem whole_done (g : Bool) : machine.step (frame scan false false g [] empty)=some (haltList machine [g]) := by
  have finished : (⟨none,reg false false true,bank [] empty [g]⟩ : TM2.Cfg Alphabet Label Reg) = haltList machine [g] := by
    unfold haltList; congr 1;funext k;rcases k with _|_|b <;>rfl
  apply Eq.trans _ (congrArg some finished)
  change TM2.step program _=_
  simp [frame,scan,program,TM2.step,TM2.stepAux,reg,cached,bank_in,bank_out,done,setInput,setOutput]

end OwnedRadix
namespace OwnedRadix
open Turing
private abbrev Run (n : ℕ) (c d : machine.Cfg) := (flip bind machine.step)^[n] (some c)=some d
private theorem before {n : ℕ} {c d e : machine.Cfg} (h : machine.step c=some d) (t : Run n d e) : Run (n+1) c e := by
  unfold Run
  rw [Function.iterate_succ_apply]
  change (flip bind machine.step)^[n] (machine.step c)=some e
  rwa [h]
private theorem single {c d : machine.Cfg} (h : machine.step c=some d) : Run 1 c d:= before h rfl
private theorem join {m n : ℕ} {c d e : machine.Cfg} (h : Run m c d) (t : Run n d e) : Run (m+n) c e := by
  unfold Run at *
  rw [Nat.add_comm m n,Function.iterate_add_apply,h,t]

private theorem copy_record (z o g b : Bool) (v : Mark) (keys : List Bool) (rest : List Token) (B : Bins) :
    Run (keys.length+1) (frame (copyTo b) z o g (encode (keys,v)++rest) B)
      (frame scan z o g rest (Function.update B b ((encode (keys,v)).reverse++B b))) := by
  induction keys generalizing B with
  | nil=>exact single (copy_value z o g b v rest B)
  | cons h t ih=>
    have sub:=ih (Function.update B b (.key h::B b))
    have next:=before (copy_key z o g b h (encode (t,v)++rest) B) sub
    simpa [encode,List.append_assoc] using next

private def insertRecord (B : Bins) (r : Record) : Bins := match r.1 with
  | []=>B
  | h::t=>Function.update B h ((encode (t,r.2)).reverse++B h)

private def frameS (S : Bool × Bool × Bool) (rest : List Token) (B : Bins) :=
  frame scan S.1 S.2.1 S.2.2 rest B

private theorem scan_record (S : Bool × Bool × Bool) (r : Record) (rest : List Token) (B : Bins) :
    Run (r.1.length+1) (frameS S (encode r++rest) B)
      (frameS (if r.1=[] then observe S r.2 else S) rest (insertRecord B r)) := by
  obtain ⟨z,o,g⟩:=S
  obtain ⟨keys,v⟩:=r
  cases keys with
  | nil=>simpa [frameS,observe,encode,insertRecord] using single (scan_value z o g v rest B)
  | cons b t=>
    have next:=before (scan_key z o g b (encode (t,v)++rest) B) (copy_record z o g b v t rest B)
    simpa [frameS,encode,insertRecord,List.append_assoc] using next

private def collected (B : Bins) (rs : List Record) (b : Bool) := (body (child b rs)).reverse++B b
private theorem collected_cons (B : Bins) (r : Record) (rs : List Record) : collected (insertRecord B r) rs=collected B (r::rs) := by
  funext b
  obtain ⟨keys,v⟩:=r
  cases keys with
  | nil=>rfl
  | cons h t=>by_cases eq:h=b
              · subst h; simp [collected,child_step,insertRecord,body_cons,List.append_assoc]
              · simp [collected,child_step,insertRecord,eq,Ne.symm eq]

private theorem scan_group (z o g : Bool) (rs : List Record) (rest : List Token) (B : Bins) :
    Run (body rs).length (frame scan z o g (body rs++rest) B)
      (frameS ((values [] rs).foldl observe (z,o,g)) rest (collected B rs)) := by
  induction rs generalizing z o g B with
  | nil=>
    have eq : collected B []=B:=by funext b;rfl
    simp [body,values,eq,frameS,Run]
  | cons r rs ih=>
    rw [body_cons,List.length_append,List.append_assoc,encode_length]
    let S:=if r.1=[] then observe (z,o,g) r.2 else (z,o,g)
    have r1:=scan_record (z,o,g) r (body rs++rest) B
    have r2:=ih S.1 S.2.1 S.2.2 (insertRecord B r)
    have h:=join r1 r2
    rw [values_cons]
    by_cases e:r.1=[] <;> simpa [e,S,collected_cons,frameS] using h

end OwnedRadix
namespace OwnedRadix
open Turing

private theorem flush_all (z o g b : Bool) (vs xs : List Token) (B : Bins) (h:B b=vs) :
    Run (vs.length+1) (frame (flush b) z o g xs B)
      (frame (after b) z o g (vs.reverse++xs) (Function.update B b [])) := by
  induction vs generalizing xs B with
  | nil=>
    have eq : Function.update B b []=B:=Function.update_eq_self_iff.mpr h.symm
    simpa only [List.length_nil,List.reverse_nil,List.nil_append,eq] using single (flush_end z o g b xs B h)
  | cons v vs ih=>
    apply before (flush_next z o g b xs B v vs h)
    have go:=ih (v::xs) (Function.update B b vs) (Function.update_self ..)
    simpa only [List.length_cons,Function.update_idem,List.reverse_cons,List.append_assoc,List.singleton_append] using go

private theorem flush_group (z o g b : Bool) (rs : List Record) (xs : List Token) (B : Bins) (h : B b=(body rs).reverse) :
    ∃ n≤(body rs).length+2, Run n (frame (prepare b) z o g xs B)
      (frame (after b) z o g (optionalGroup rs++xs) (Function.update B b [])) := by
  by_cases nil : rs=[]
  · subst rs
    have e:B b=[]:=h
    have eq : Function.update B b []=B:=Function.update_eq_self_iff.mpr e.symm
    refine ⟨1,by omega,?_⟩
    have ready:=prepare_step z o g b xs B
    rw [ite_eq_left e] at ready
    simpa only [optionalGroup,ite_true,List.nil_append,eq] using single ready
  · have bodyNe : body rs≠[] := List.ne_nil_of_length_pos (body_nonempty nil)
    have bn : B b≠[] := by rw [h]; simpa using bodyNe
    have ready:=prepare_step z o g b xs B
    rw [ite_eq_right bn] at ready
    have turn:=flush_all z o g b (body rs).reverse (.close::xs) B h
    refine ⟨(body rs).length+2,le_rfl,?_⟩
    simpa only [List.length_reverse,List.reverse_reverse,optionalGroup,ite_eq_right nil,group,List.append_assoc,List.singleton_append] using before ready turn

private theorem one_group (g : Bool) (rs : List Record) (xs : List Token) :
    ∃ n≤2*(body rs).length+5, Run n (frame scan false false g (group rs++xs) empty)
      (frame scan false false (g && cleanRoot rs) (optionalGroup (child false rs) ++ (optionalGroup (child true rs) ++xs)) empty) := by
  let B:=collected empty rs
  have bins : ∀ b, B b=(body (child b rs)).reverse := by intro b; simp [B,collected,empty]
  let ok:=g && cleanRoot rs
  let after1:=Function.update B true ([] : List Token)
  have b0 : after1 false=(body (child false rs)).reverse:=bins false
  have emptyBoth : Function.update after1 false []=empty:=by funext b;cases b <;> rfl
  obtain ⟨a,ha,one⟩:=flush_group false false ok true (child true rs) xs B (bins true)
  obtain ⟨b,hb,two⟩:=flush_group false false ok false (child false rs) (optionalGroup (child true rs)++xs) after1 b0
  have start:=scan_group false false g rs (.close::xs) empty
  let S := (values [] rs).foldl observe (false,false,g)
  have closed:=scan_close S.1 S.2.1 S.2.2 xs B
  have answer : S.2.2=(g && cleanRoot rs):=walk_ok false false g (values [] rs)
  have entrance:=join start (single closed)
  rw [answer] at entrance
  have together:=join (join entrance one) two
  rw [emptyBoth] at together
  have shrink:=bodies_shrink rs
  refine ⟨(body rs).length+1+a+b,by omega,?_⟩
  simpa only [after,Bool.false_eq_true,ite_false,ok,group,List.append_assoc,List.singleton_append] using together

end OwnedRadix
namespace OwnedRadix
open Turing

/-- A nonempty prefix class splits into at most two smaller classes. Its scan
and redistribution cost is paid by the decrease in the squared key lengths. -/
private theorem consume (rs : List Record) : ∀ (g : Bool) (tail : List Token),
    ∃ n≤7*weight rs, Run n (frame scan false false g (optionalGroup rs++tail) empty)
      (frame scan false false (g && fine rs) tail empty) := by
  intro g tail
  by_cases nil : rs=[]
  · subst rs; exact ⟨0,by simp [weight],by simp [optionalGroup,fine,Run]⟩
  · have length:=body_nonempty nil
    have energy:=group_cost rs
    have lf : weight (child false rs)<weight rs:=by omega
    have rt : weight (child true rs)<weight rs:=by omega
    obtain ⟨n,hn,first⟩:=one_group g rs tail
    obtain ⟨l,hl,left⟩:=consume (child false rs) (g && cleanRoot rs) (optionalGroup (child true rs)++tail)
    obtain ⟨r,hr,right⟩:=consume (child true rs) ((g && cleanRoot rs) && fine (child false rs)) tail
    have run:=join (join first left) right
    refine ⟨n+l+r,by omega,?_⟩
    simpa only [optionalGroup,ite_eq_right nil,decompose rs,Bool.and_assoc] using run
termination_by weight rs

private theorem init_frame (xs : List Token) : initList machine xs=frame scan false false true xs empty := by
  unfold initList frame
  congr 1
  funext k;rcases k with _|_|b <;> rfl

/-- The actual four-stack checker outputs one truth bit and clears its stacks.
Its runtime is at most seven times the sum of (address length + 1) squared,
plus a single final macrostep. It treats addresses of different lengths distinctly. -/
noncomputable def checks (rs : List Record) :
    TM2OutputsInTime machine (optionalGroup rs) (some [fine rs]) (7*weight rs+1) := by
  let given:=consume rs true []
  let n:=Classical.choose given
  have bound: n≤7*weight rs := (Classical.choose_spec given).1
  have progress : Run n (frame scan false false true (optionalGroup rs++[]) empty)
      (frame scan false false (true && fine rs) [] empty) := (Classical.choose_spec given).2
  simp only [List.append_nil,Bool.true_and] at progress
  have finish:=join progress (single (whole_done (fine rs)))
  refine ⟨⟨n+1,?_⟩,Nat.succ_le_succ bound⟩
  change (flip bind machine.step)^[n+1] (some (initList machine (optionalGroup rs))) = some (haltList machine [fine rs])
  exact (congrArg (fun x=>(flip bind machine.step)^[n+1] (some x)) (init_frame (optionalGroup rs))).trans finish

theorem uniform_time (rs : List Record) (width : ℕ) (fits : ∀ r∈rs, r.1.length≤width) :
    7*weight rs+1≤7*rs.length*(width+1)^2+1 := by
  have sum : weight rs≤rs.length*(width+1)^2 := by
    induction rs with
    | nil=>simp [weight]
    | cons r rs ih=>
      have h:=ih (fun x hx=>fits x (List.mem_cons_of_mem _ hx))
      have size:=Nat.pow_le_pow_left (Nat.add_le_add_right (fits r List.mem_cons_self) 1) 2
      change (r.1.length+1)^2+weight rs≤_
      rw [List.length_cons,Nat.succ_mul];omega
  rw [Nat.mul_assoc]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ sum) _

end OwnedRadix
namespace OwnedRadix

abbrev Name := List Bool
abbrev Env := Name → Option Bool
def emptyEnv : Env := fun _=>none
def put (e : Env) (k : Name) (v : Bool) : Env := Function.update e k (some v)

private def vAt (o : Option Bool) (ms : List Mark) : Bool :=
  validFrom o.isSome (o.getD false) ms
private def holds (e : Env) (rs : List Record) : Prop := ∀ k, vAt (e k) (values k rs)=true

private theorem holds_nil (e : Env) : holds e [] := by intro k;rfl

private theorem holds_cons (e : Env) (key : Name) (m : Mark) (rs : List Record) :
    holds e ((key,m)::rs) ↔ allowed (e key).isSome ((e key).getD false) m=true ∧
      holds (put e key ((e key).getD m.2)) rs := by
  have atKey : vAt (e key) (m::values key rs)=
      (allowed (e key).isSome ((e key).getD false) m && vAt (some ((e key).getD m.2)) (values key rs)) := by
    cases h:e key <;> rfl
  constructor
  · intro all
    have h:=all key
    rw [values_cons,ite_eq_left (show (key,m).1=key from rfl),atKey,Bool.and_eq_true] at h
    refine ⟨h.1,?_⟩
    intro k
    by_cases eq:key=k
    · subst k;simpa [put] using h.2
    · have other:=all k
      simpa [values_cons,eq,put,Ne.symm eq] using other
  · rintro ⟨ok,tail⟩ k
    by_cases eq:key=k
    · subst k
      rw [values_cons,ite_eq_left (show (key,m).1=key from rfl),atKey,Bool.and_eq_true]
      exact ⟨ok,by simpa [put] using tail key⟩
    · simpa [values_cons,eq,put,Ne.symm eq] using tail k

private theorem holds_use (e : Env) (key : Name) (v : Bool) (rs : List Record) :
    holds e ((key,(false,v))::rs) ↔ e key=some v ∧ holds e rs := by
  rw [holds_cons]
  cases h:e key with
  | none=>simp [allowed]
  | some b=>
    have p:put e key b=e:=Function.update_eq_self_iff.mpr h.symm
    simp [allowed,p]

private theorem holds_define (e : Env) (key : Name) (v : Bool) (rs : List Record) :
    holds e ((key,(true,v))::rs) ↔ e key=none ∧ holds (put e key v) rs := by
  rw [holds_cons]
  cases h:e key <;> simp [allowed]

private theorem holds_fine (rs : List Record) : holds emptyEnv rs ↔ fine rs=true := by
  rw [fine_iff]
  rfl

/-- Names are arbitrary finite bit strings. Names need not form an initial segment of the naturals. -/
inductive Expr where
  | literal (v : Bool)
  | neg (a : Name)
  | conj (a b : Name)
  | disj (a b : Name)
  deriving DecidableEq

structure Gate where
  name : Name
  expr : Expr
  deriving DecidableEq

abbrev Guess := Bool × Bool
abbrev Decorated := Gate × Guess

def applyOp : Expr → Guess → Bool
  | .literal b,_=>b
  | .neg _,q=>!q.1
  | .conj ..,q=>q.1 && q.2
  | .disj ..,q=>q.1 || q.2

def evalOp (e : Env) : Expr → Option Bool
  | .literal b=>some b
  | .neg a=>(e a).map (!·)
  | .conj a b=>return (← e a) && (← e b)
  | .disj a b=>return (← e a) || (← e b)

def evalGate (e : Env) (g : Gate) : Option Env := do
  if (e g.name).isSome then none else return put e g.name (← evalOp e g.expr)

def evalProgram (e : Env) : List Gate → Option Env
  | []=>some e
  | g::gs=> (evalGate e g).bind (fun next=>evalProgram next gs)

def reads : Expr → Guess → List Record
  | .literal _,_=>[]
  | .neg a,q=>[(a,(false,q.1))]
  | .conj a b,q | .disj a b,q=>[(a,(false,q.1)),(b,(false,q.2))]

def events (g : Gate) (q : Guess) : List Record :=
  reads g.expr q ++ [(g.name,(true,applyOp g.expr q))]

def typed (e : Env) : Expr → Guess → Prop
  | .literal _,_=>True
  | .neg a,q=>e a=some q.1
  | .conj a b,q | .disj a b,q=>e a=some q.1 ∧ e b=some q.2

private theorem holds_reads (e : Env) (op : Expr) (q : Guess) (tail : List Record) :
    holds e (reads op q ++ tail) ↔ typed e op q ∧ holds e tail := by
  cases op <;> simp only [reads,typed,List.nil_append,List.cons_append,holds_use,true_and,and_assoc]

private theorem holds_events (e : Env) (g : Gate) (q : Guess) (tail : List Record) :
    holds e (events g q++tail) ↔ typed e g.expr q ∧ e g.name=none ∧ holds (put e g.name (applyOp g.expr q)) tail := by
  rw [events,List.append_assoc,holds_reads];simp [holds_define]

private theorem typed_correct (e : Env) (op : Expr) (q : Guess) (ok:typed e op q) :
    evalOp e op=some (applyOp op q) := by
  cases op with
  | literal b=>rfl
  | neg a=>simp [evalOp,applyOp,show e a=some q.1 from ok]
  | conj a b=>simp [evalOp,applyOp,show e a=some q.1 from ok.1,show e b=some q.2 from ok.2]
  | disj a b=>simp [evalOp,applyOp,show e a=some q.1 from ok.1,show e b=some q.2 from ok.2]

private theorem typed_complete (e : Env) (op : Expr) (v : Bool) (ok:evalOp e op=some v) :
    ∃ q, typed e op q ∧ applyOp op q=v := by
  cases op with
  | literal b=>exact ⟨(false,false),trivial,Option.some.inj ok⟩
  | neg a=>
    cases h:e a with
    | none=>simp [evalOp,h] at ok
    | some b=>exact ⟨(b,false),h,by simpa [evalOp,h,applyOp] using ok⟩
  | conj a b | disj a b=>
    cases h:e a with
    | none=>simp [evalOp,h] at ok
    | some u=>
      cases k:e b with
      | none=>simp [evalOp,h,k] at ok
      | some w=>exact ⟨(u,w),⟨h,k⟩,by simpa [evalOp,h,k,applyOp] using ok⟩

def trace (ds : List Decorated) : List Record := ds.flatMap fun (g,q)=>events g q

private theorem from_trace (e : Env) (ds : List Decorated) (tail : List Record)
    (valid : holds e (trace ds++tail)) : ∃ final,
    evalProgram e (ds.map Prod.fst)=some final ∧ holds final tail := by
  induction ds generalizing e with
  | nil=>exact ⟨e,rfl,valid⟩
  | cons d ds ih=>
    obtain ⟨g,q⟩:=d
    change holds e ((events g q ++ trace ds) ++ tail) at valid
    rw [List.append_assoc,holds_events] at valid
    obtain ⟨well,fresh,rest⟩:=valid
    obtain ⟨final,ev,hf⟩:=ih (put e g.name (applyOp g.expr q)) rest
    exact ⟨final,by simpa [evalProgram,evalGate,fresh,typed_correct e g.expr q well] using ev,hf⟩

private theorem to_trace (gs : List Gate) (e final : Env) (tail : List Record)
    (h : evalProgram e gs=some final) (rest : holds final tail) :
    ∃ ds : List Decorated, ds.map Prod.fst=gs ∧ holds e (trace ds++tail) := by
  induction gs generalizing e with
  | nil=>obtain rfl:=Option.some.inj h;exact ⟨[],rfl,rest⟩
  | cons g gs ih=>
    cases fresh:e g.name with
    | some old=>simp [evalProgram,evalGate,fresh] at h
    | none=>
      cases ev:evalOp e g.expr with
      | none=>simp [evalProgram,evalGate,fresh,ev] at h
      | some v=>
        have h' : evalProgram (put e g.name v) gs=some final:=by simpa [evalProgram,evalGate,fresh,ev] using h
        obtain ⟨q,typedQ,out⟩:=typed_complete e g.expr v ev
        obtain ⟨ds,mapped,valid⟩:=ih (put e g.name v) h'
        refine ⟨(g,q)::ds,by simp [mapped],?_⟩
        change holds e ((events g q++trace ds)++tail)
        rw [List.append_assoc,holds_events,out]
        exact ⟨typedQ,fresh,valid⟩

/-- The certificate detects all undefined reads, forward references, repeated output
names, cycles, wrong operand values, and a missing or incorrect designated output. -/
theorem named_output_iff (gs : List Gate) (out : Name) (b : Bool) :
    (∃ e, evalProgram emptyEnv gs=some e ∧ e out=some b) ↔
    ∃ ds : List Decorated, ds.map Prod.fst=gs ∧ fine (trace ds++[(out,(false,b))])=true := by
  constructor
  · rintro ⟨e,ev,h⟩
    obtain ⟨ds,erase,ok⟩:=to_trace gs emptyEnv e [(out,(false,b))] ev ((holds_use ..).mpr ⟨h,holds_nil e⟩)
    exact ⟨ds,erase,(holds_fine _).mp ok⟩
  · rintro ⟨ds,rfl,ok⟩
    obtain ⟨e,ev,h⟩:=from_trace emptyEnv ds [(out,(false,b))] ((holds_fine _).mpr ok)
    exact ⟨e,ev,((holds_use ..).mp h).1⟩

end OwnedRadix

namespace OwnedRadix.Code

inductive Shape where | lit (b : Bool) | neg | conj | disj deriving DecidableEq, Fintype
inductive Rest where
  | returnGate | returnAsk | last (out : Mark) | pair (other out : Mark)
  deriving DecidableEq, Fintype
inductive State where
  | start | classify | literalBit | unaryOrBinary | binaryBit
  | guess1 (op : Shape) | guess2 (op : Shape) (a : Bool)
  | askBit | field (current : Mark) (rest : Rest) | digit (current : Mark) (rest : Rest)
  | closed | bad
  deriving DecidableEq, Fintype

def next : Rest → State
  | .returnGate=>.start | .returnAsk=>.closed
  | .last m=>.field m .returnGate | .pair m o=>.field m (.last o)

def plan : Shape → Bool → Bool → State
  | .lit v,_,_=>.field (true,v) .returnGate
  | .neg,a,_=>.field (false,a) (.last (true,!a))
  | .conj,a,b=>.field (false,a) (.pair (false,b) (true,a && b))
  | .disj,a,b=>.field (false,a) (.pair (false,b) (true,a || b))

def step : State → Bool → State
  | .start,b=>if b then .askBit else .classify
  | .classify,b=>if b then .unaryOrBinary else .literalBit
  | .literalBit,b=>.guess1 (.lit b)
  | .unaryOrBinary,b=>if b then .binaryBit else .guess1 .neg
  | .binaryBit,b=>.guess1 (if b then .disj else .conj)
  | .guess1 op,b=>.guess2 op b
  | .guess2 op a,b=>plan op a b
  | .askBit,b=>.field (false,b) .returnAsk
  | .field m r,b=>if b then next r else .digit m r
  | .digit m r,_=>.field m r
  | .closed,_ | .bad,_=>.bad

def emit : State → Bool → Option Token
  | .field m _,true=>some (.value m)
  | .digit ..,b=>some (.key b)
  | _,_=>none

def finish (s : State) : Token := if s=.closed then .close else .value (false,false)
def lex : State → List Bool → List Token
  | s,[]=>[finish s]
  | s,b::bs=>(emit s b).toList++lex (step s b) bs
def accept (s : State) (bs : List Bool) : Prop := bs.foldl step s=.closed
instance (s : State) (bs : List Bool) : Decidable (accept s bs) := inferInstanceAs (Decidable (bs.foldl step s=State.closed))

def nameBits : Name → List Bool
  | []=>[true]
  | b::bs=>false::b::nameBits bs

def opcode : Shape → List Bool
  | .lit b=>[false,false,b]
  | .neg=>[false,true,false]
  | .conj=>[false,true,true,false]
  | .disj=>[false,true,true,true]

def shape : Expr → Shape
  | .literal b=>.lit b | .neg _=>.neg | .conj ..=>.conj | .disj ..=>.disj

def inputs : Expr → List Name
  | .literal _=>[] | .neg a=>[a] | .conj a b | .disj a b=>[a,b]

def names (g : Gate) : List Bool := ((inputs g.expr)++[g.name]).flatMap nameBits

def clause (d : Decorated) : List Bool := opcode (shape d.1.expr) ++ [d.2.1,d.2.2] ++ names d.1
def raw (ds : List Decorated) (out : Name) (answer : Bool) : List Bool :=
  ds.flatMap clause ++ [true,answer] ++ nameBits out

private theorem consumeName (k : Name) (m : Mark) (r : Rest) (suffix : List Bool) :
    lex (.field m r) (nameBits k++suffix)=encode (k,m)++lex (next r) suffix := by
  induction k with
  | nil=>rfl
  | cons b bs ih=>exact congrArg (Token.key b::·) ih

private theorem acceptName (k : Name) (m : Mark) (r : Rest) (suffix : List Bool) :
    accept (.field m r) (nameBits k++suffix) ↔ accept (next r) suffix := by
  induction k with
  | nil=>rfl
  | cons b bs ih=>exact ih

private theorem scanHeader (op : Shape) (a b : Bool) (tail : List Bool) :
    lex .start (opcode op ++ [a,b] ++ tail)=lex (plan op a b) tail := by
  cases op <;> rfl

private theorem acceptHeader (op : Shape) (a b : Bool) (tail : List Bool) :
    accept .start (opcode op ++ [a,b] ++ tail) ↔ accept (plan op a b) tail := by
  cases op <;> rfl

private theorem compile_clause (d : Decorated) (w : List Bool) :
    lex .start (clause d++w)=body (events d.1 d.2)++lex .start w := by
  obtain ⟨⟨out,op⟩,a,b⟩:=d
  unfold clause
  rw [List.append_assoc,scanHeader]
  cases op <;> simp [shape,names,inputs,plan,next,events,reads,applyOp,body,
    List.append_assoc,consumeName]

private theorem pass_clause (d : Decorated) (w : List Bool) :
    accept .start (clause d++w) ↔ accept .start w := by
  obtain ⟨⟨out,op⟩,a,b⟩:=d
  unfold clause
  rw [List.append_assoc,acceptHeader]
  cases op <;> simp [shape,names,inputs,plan,next,List.append_assoc,acceptName]

theorem compiled (ds : List Decorated) (out : Name) (b : Bool) :
    lex .start (raw ds out b)=group (trace ds ++ [(out,(false,b))]) := by
  induction ds with
  | nil=>
    change lex (.field (false,b) .returnAsk) (nameBits out)=_
    have h:=consumeName out (false,b) .returnAsk []
    simpa [group,body,trace,next,lex,finish] using h
  | cons d ds ih=>
    have h:=compile_clause d (raw ds out b)
    simpa [raw,trace,group,body,List.append_assoc,ih] using h.trans (congrArg (body (events d.1 d.2)++·) ih)

theorem wellformed (ds : List Decorated) (out : Name) (b : Bool) : accept .start (raw ds out b) := by
  induction ds with
  | nil=>
    change accept (.field (false,b) .returnAsk) (nameBits out)
    simpa using (acceptName out (false,b) .returnAsk []).mpr (show accept .closed [] from rfl)
  | cons d ds ih=>
    simpa [raw,List.append_assoc] using (pass_clause d (raw ds out b)).mpr ih

end OwnedRadix.Code
namespace OwnedRadix.Code

private theorem dead (w : List Bool) : ¬accept .bad w := by
  induction w with
  | nil=>decide
  | cons b bs ih=>exact ih

private theorem closedWord (w : List Bool) (h : accept .closed w) : w=[] := by
  cases w with
  | nil=>rfl
  | cons b bs=>exact (dead bs h).elim

private theorem readName (w : List Bool) (m : Mark) (r : Rest) (h : accept (.field m r) w) :
    ∃ k suffix, w=nameBits k++suffix ∧ accept (next r) suffix := by
  cases w with
  | nil=>cases h
  | cons bit bs=>
    cases bit with
    | true=>exact ⟨[],bs,rfl,h⟩
    | false=>
      cases bs with
      | nil=>cases h
      | cons v rest=>
        obtain ⟨k,suffix,split,ok⟩:=readName rest m r h
        exact ⟨v::k,suffix,by simp [nameBits,split],ok⟩
termination_by w.length

private theorem splitGate (op : Shape) (a b : Bool) (w : List Bool) (h : accept (plan op a b) w) :
    ∃ g : Gate, ∃ suffix, op=shape g.expr ∧ w=names g++suffix ∧ accept .start suffix := by
  cases op with
  | lit v=>
    obtain ⟨out,tail,split,ok⟩:=readName w (true,v) .returnGate h
    exact ⟨⟨out,.literal v⟩,tail,rfl,by simpa [names,inputs] using split,ok⟩
  | neg=>
    obtain ⟨x,tail,e,ok⟩:=readName w (false,a) (.last (true,!a)) h
    obtain ⟨out,suf,f,ok'⟩:=readName tail (true,!a) .returnGate ok
    exact ⟨⟨out,.neg x⟩,suf,rfl,by simp [e,f,names,inputs,List.append_assoc],ok'⟩
  | conj=>
    obtain ⟨x,t,e,h1⟩:=readName w (false,a) (.pair (false,b) (true,a && b)) h
    obtain ⟨y,s,f,h2⟩:=readName t (false,b) (.last (true,a && b)) h1
    obtain ⟨out,z,k,h3⟩:=readName s (true,a && b) .returnGate h2
    exact ⟨⟨out,.conj x y⟩,z,rfl,by simp [e,f,k,names,inputs,List.append_assoc],h3⟩
  | disj=>
    obtain ⟨x,t,e,h1⟩:=readName w (false,a) (.pair (false,b) (true,a || b)) h
    obtain ⟨y,s,f,h2⟩:=readName t (false,b) (.last (true,a || b)) h1
    obtain ⟨out,z,k,h3⟩:=readName s (true,a || b) .returnGate h2
    exact ⟨⟨out,.disj x y⟩,z,rfl,by simp [e,f,k,names,inputs,List.append_assoc],h3⟩

private theorem headerInv (w : List Bool) (h : accept .classify w) :
    ∃ (op : Shape) (q : Guess) (rest : List Bool), false::w=opcode op++[q.1,q.2]++rest ∧ accept (plan op q.1 q.2) rest := by
  have guesses (op : Shape) (t : List Bool) (h : accept (.guess1 op) t) :
      ∃ q : Guess, ∃ rest, t=q.1::q.2::rest ∧ accept (plan op q.1 q.2) rest := by
    rcases t with _|⟨a,_|⟨b,bs⟩⟩
    · cases h
    · cases h
    · exact ⟨(a,b),bs,rfl,h⟩
  rcases w with _|⟨bit,bs⟩
  · cases h
  cases bit with
  | false=>
    rcases bs with _|⟨v,tail⟩
    · cases h
    obtain ⟨q,rest,rfl,hq⟩:=guesses (.lit v) tail h
    exact ⟨.lit v,q,rest,rfl,hq⟩
  | true=>
    rcases bs with _|⟨u,tail⟩
    · cases h
    cases u with
    | false=>
      obtain ⟨q,rest,rfl,hq⟩:=guesses .neg tail h
      exact ⟨.neg,q,rest,rfl,hq⟩
    | true=>
      rcases tail with _|⟨v,more⟩
      · cases h
      cases v with
      | false=>
        obtain ⟨q,rest,rfl,hq⟩:=guesses .conj more h
        exact ⟨.conj,q,rest,rfl,hq⟩
      | true=>
        obtain ⟨q,rest,rfl,hq⟩:=guesses .disj more h
        exact ⟨.disj,q,rest,rfl,hq⟩

theorem decode_exists (w : List Bool) (ok : accept .start w) :
    ∃ ds out b, w=raw ds out b := by
  cases w with
  | nil=>cases ok
  | cons bit bs=>
    cases bit with
    | true=>
      rcases bs with _|⟨b,t⟩
      · cases ok
      obtain ⟨out,suf,split,finish⟩:=readName t (false,b) .returnAsk ok
      obtain rfl:=closedWord suf finish
      exact ⟨[],out,b,by simp [raw,split]⟩
    | false=>
      obtain ⟨op,q,t,header,ok'⟩:=headerInv bs ok
      obtain ⟨g,suf,eshape,split,ready⟩:=splitGate op q.1 q.2 t ok'
      have short : suf.length<(false::bs).length := by
        have hh:=congrArg List.length header
        simp only [List.length_cons,List.length_append,List.length_nil] at hh
        rw [split,List.length_append] at hh
        simp;omega
      obtain ⟨ds,out,b,tail⟩:=decode_exists suf ready
      refine ⟨(g,q)::ds,out,b,?_⟩
      simpa [raw,clause,List.append_assoc,eshape,split,tail] using header
termination_by w.length

end OwnedRadix.Code
namespace OwnedRadix.Code.Guard
open Turing

inductive Tape where | inp | tmp | out deriving DecidableEq
instance : Fintype Tape := Fintype.ofList [.inp,.tmp,.out] (by intro k;cases k <;> simp)
inductive Label where | forward | back (good : Bool) deriving DecidableEq, Fintype
private abbrev A : Tape → Type := fun _=>Bool
private abbrev R := State × Option Bool
private abbrev St := TM2.Stmt A Label R
private def flag : State → Bool | .closed=>true | _=>false
private theorem flag_spec (s : State) : flag s=true ↔ s=State.closed := by cases s <;> simp [flag]
private def got (r : R) (o : Option Bool) : R := (r.1,o)
private def bit (r : R) : Bool := r.2.getD false
private def launch (l : R → Label) : St := .goto l
private def back (g : Bool) : St := .load (fun _=>(.start,none)) (.goto fun _=>.back g)

private def prog : Label → St
  | .forward=>.pop .inp got (.branch (fun r=>r.2.isSome)
     (.push .tmp bit (.load (fun r=>(step r.1 (bit r),none)) (launch fun _=>.forward)))
     (.branch (fun r=>flag r.1) (back true) (back false)))
  | .back g=>.pop .tmp got (.branch (fun r=>r.2.isSome)
     (if g then .push .out bit (back g) else back g)
     (.load (fun _=>(.start,none)) .halt))

def machine : FinTM2 where
  K:=Tape; k₀:=.inp; k₁:=.out; Γ:=A; Λ:=Label; main:=.forward
  σ:=R; initialState:=(.start,none); m:=prog

private def cells (xs ws ys : List Bool) : (k : Tape) → List (A k)
  | .inp=>xs | .tmp=>ws | .out=>ys

private def frame (l : Label) (s : State) (xs tmp ys : List Bool) : machine.Cfg :=
  ⟨some l,(s,none),cells xs tmp ys⟩

private theorem inputSet (xs ys ws ans : List Bool) :
    Function.update (cells xs ws ans) .inp ys=cells ys ws ans := by funext k;cases k <;>rfl
private theorem tempSet (xs ys ws ans : List Bool) :
    Function.update (cells xs ws ans) .tmp ys=cells xs ys ans := by funext k;cases k <;>rfl
private theorem outSet (xs ys ws ans : List Bool) :
    Function.update (cells xs ws ans) .out ys=cells xs ws ys := by funext k;cases k <;>rfl

private theorem forward_step (b : Bool) (s : State) (xs ws ys : List Bool) :
    machine.step (frame .forward s (b::xs) ws ys)=some (frame .forward (step s b) xs (b::ws) ys) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,got,bit,launch,inputSet,tempSet,cells] <;> rfl

private theorem forward_end (s : State) (ws ys : List Bool) :
    machine.step (frame .forward s [] ws ys)=some (frame (.back (flag s)) .start [] ws ys) := by
  change TM2.step prog _=_
  cases s <;> simp [frame,prog,TM2.step,TM2.stepAux,got,back,cells,inputSet,flag] <;> rfl

private theorem back_step (g b : Bool) (ws ys : List Bool) :
    machine.step (frame (.back g) .start [] (b::ws) ys)=
      some (frame (.back g) .start [] ws (if g then b::ys else ys)) := by
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,got,back,bit,cells,tempSet,outSet] <;> rfl

private theorem back_end (g : Bool) (ys : List Bool) :
    machine.step (frame (.back g) .start [] [] ys)=some (haltList machine ys) := by
  have e : (⟨none,(.start,none),cells [] [] ys⟩ : TM2.Cfg A Label R)=haltList machine ys := by
    unfold haltList; congr 1; funext k;cases k <;>rfl
  apply Eq.trans _ (congrArg some e)
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,got,cells,tempSet]

private abbrev Walk (n : ℕ) (a b : machine.Cfg) := (flip bind machine.step)^[n] (some a)=some b
private theorem before {n : ℕ} {a b c : machine.Cfg} (h : machine.step a=some b) (t : Walk n b c) : Walk (n+1) a c := by
  unfold Walk;rw [Function.iterate_succ_apply];change (flip bind machine.step)^[n] (machine.step a)=some c;rwa [h]

private theorem forward_run (s : State) (xs ws ys : List Bool) :
    Walk (xs.length+1) (frame .forward s xs ws ys)
      (frame (.back (flag (xs.foldl step s))) .start [] (xs.reverse++ws) ys) := by
  induction xs generalizing s ws with
  | nil=>exact before (forward_end s ws ys) rfl
  | cons b xs ih=>
    simpa only [List.length_cons,List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using before (forward_step b s xs ws ys) (ih (step s b) (b::ws))

private theorem back_run (g : Bool) (ws ys : List Bool) :
    Walk (ws.length+1) (frame (.back g) .start [] ws ys) (haltList machine ((if g then ws.reverse else [])++ys)) := by
  induction ws generalizing ys with
  | nil=>simpa using before (back_end g ys) (show Walk 0 _ _ from rfl)
  | cons w ws ih=>
    have run:=before (back_step g w ws ys) (ih (if g then w::ys else ys))
    cases g <;> simpa [List.append_assoc] using run

def goodWord (xs : List Bool) : List Bool := if accept .start xs then xs else []

def runs (xs : List Bool) : TM2OutputsInTime machine xs (some (goodWord xs)) (2*xs.length+2) := by
  have init : initList machine xs=frame .forward .start xs [] [] := by
    unfold initList frame;congr 1;funext k;cases k <;>rfl
  have front:=forward_run .start xs [] []
  simp only [List.append_nil] at front
  have rear:=back_run (flag (xs.foldl step .start)) xs.reverse []
  rw [List.length_reverse,List.reverse_reverse,List.append_nil] at rear
  refine ⟨⟨(xs.length+1)+(xs.length+1),?_⟩,show (xs.length+1)+(xs.length+1)≤2*xs.length+2 by omega⟩
  rw [Function.iterate_add_apply,init,front]
  change Walk (xs.length+1) _ (haltList machine (goodWord xs))
  have out : (if flag (xs.foldl step .start) then xs else [])=goodWord xs := by
    by_cases h : xs.foldl step .start=State.closed <;> simp only [goodWord,accept,flag_spec,h,ite_true,ite_false]
  rwa [←out]

end OwnedRadix.Code.Guard
namespace OwnedRadix.Code

def keep : State → Bool | .guess1 _ | .guess2 ..=>false | _=>true

def erase : State → List Bool → List Bool
  | _,[]=>[]
  | s,b::bs=>if keep s then b::erase (step s b) bs else erase (step s b) bs

def bare (gs : List Gate) (out : Name) (b : Bool) :=
  gs.flatMap (fun g=>opcode (shape g.expr)++names g) ++ [true,b] ++ nameBits out

private theorem erase_name (k : Name) (m : Mark) (r : Rest) (suffix : List Bool) :
    erase (.field m r) (nameBits k++suffix)=nameBits k++erase (next r) suffix := by
  induction k with
  | nil=>rfl
  | cons b bs ih=>exact congrArg (fun s=>false::b::s) ih

private theorem erase_head (op : Shape) (a b : Bool) (t : List Bool) :
    erase .start (opcode op++[a,b]++t)=opcode op++erase (plan op a b) t := by cases op <;> rfl

private theorem erase_clause (d : Decorated) (t : List Bool) :
    erase .start (clause d++t)=opcode (shape d.1.expr)++names d.1++erase .start t := by
  obtain ⟨⟨out,op⟩,a,b⟩:=d
  unfold clause
  rw [List.append_assoc,erase_head]
  cases op <;> simp [shape,names,inputs,plan,next,List.append_assoc,erase_name]

theorem erase_raw (ds : List Decorated) (out : Name) (b : Bool) :
    erase .start (raw ds out b)=bare (ds.map Prod.fst) out b := by
  induction ds with
  | nil=>
    change true::b::erase (.field (false,b) .returnAsk) (nameBits out)=true::b::nameBits out
    simpa [erase] using congrArg (fun s=>true::b::s) (erase_name out (false,b) .returnAsk [])
  | cons d ds ih=>
    simpa [bare,raw,List.append_assoc] using
      (erase_clause d (raw ds out b)).trans (congrArg (opcode (shape d.1.expr)++names d.1++·) ih)

private theorem name_unique {a b : Name} {u v : List Bool} (e : nameBits a++u=nameBits b++v) :
    a=b ∧ u=v := by
  induction a generalizing b with
  | nil=>cases b with
         | nil=>exact ⟨rfl,List.cons.inj e |>.2⟩
         | cons h t=>cases e
  | cons h t ih=>
    cases b with
    | nil=>cases e
    | cons h' t'=>
      obtain ⟨e1,e2⟩:=List.cons.inj (List.cons.inj e |>.2)
      obtain ⟨e3,e4⟩:=ih e2
      exact ⟨by rw [e1,e3],e4⟩

private theorem op_unique (a b : Shape) (u v : List Bool) (h : opcode a++u=opcode b++v) :
    a=b ∧ u=v := by cases a <;> cases b <;> simp_all [opcode]

private theorem clause_unique (g h : Gate) (u v : List Bool)
    (e : (opcode (shape g.expr)++names g)++u=(opcode (shape h.expr)++names h)++v) :
    g=h ∧ u=v := by
  obtain ⟨out,x⟩:=g
  obtain ⟨other,y⟩:=h
  rw [List.append_assoc,List.append_assoc] at e
  obtain ⟨es,en⟩:=op_unique _ _ _ _ e
  cases x <;> cases y <;> simp [shape] at es
  all_goals simp only [names,inputs,List.nil_append,List.cons_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] at en
  all_goals repeat obtain ⟨rfl,en⟩:=name_unique en
  all_goals simp_all
  all_goals first | exact name_unique en | (
    obtain ⟨a,h⟩:=name_unique en
    obtain ⟨o,r⟩:=name_unique h
    exact ⟨⟨o,a⟩,r⟩)

/-- A commitment denotes at most one untyped circuit, output wire, and requested bit. -/
theorem bare_injective {gs hs : List Gate} {out other : Name} {b c : Bool}
    (e : bare gs out b=bare hs other c) : gs=hs ∧ out=other ∧ b=c := by
  induction gs generalizing hs with
  | nil=>
    cases hs with
    | nil=>
      change (true::b::nameBits out)=(true::c::nameBits other) at e
      obtain ⟨eb,ek⟩:=List.cons.inj (List.cons.inj e |>.2)
      have keys:=name_unique (u:=[]) (v:=[]) (by simpa using ek)
      exact ⟨rfl,keys.1,eb⟩
    | cons h hs=>cases op:shape h.expr <;> simp [bare,op,opcode] at e
  | cons g gs ih=>
    cases hs with
    | nil=>cases op:shape g.expr <;> simp [bare,op,opcode] at e
    | cons h hs=>
      have h' : (opcode (shape g.expr)++names g)++bare gs out b=(opcode (shape h.expr)++names h)++bare hs other c := by
        simpa [bare,List.append_assoc] using e
      obtain ⟨rfl,tail⟩:=clause_unique _ _ _ _ h'
      obtain ⟨rfl,rfl,rfl⟩:=ih tail
      exact ⟨rfl,rfl,rfl⟩

end OwnedRadix.Code
namespace OwnedRadix.Code.Match
open Turing

inductive Tape where | inp | want | buf | out deriving DecidableEq
instance : Fintype Tape := Fintype.ofList [.inp,.want,.buf,.out] (by intro k;cases k <;> simp)
inductive Label where | load | scan | drain (good : Bool) | back (good : Bool) deriving DecidableEq, Fintype
private abbrev A : Tape → Type | .inp=>Bool ⊕ Bool | _=>Bool
private abbrev R := State × Bool × Option (Bool ⊕ Bool) × Option Bool
private abbrev St := TM2.Stmt A Label R
private def reg (s : State) (ok : Bool) : R := (s,ok,none,none)
private def arg (r : R) (a : Option (Bool ⊕ Bool)) : R := (r.1,r.2.1,a,r.2.2.2)
private def test (r : R) (a : Option Bool) : R := (r.1,r.2.1,r.2.2.1,a)
private def bit (r : R) : Bool := match r.2.2.1 with | some (.inl b) | some (.inr b)=>b | none=>false
private def left (r : R) : Bool := match r.2.2.1 with | some (.inl _)=>true | _=>false
private def go (l : Label) (s : R → R) : St := .load s (.goto fun _=>l)
private def reset (r : R) := reg r.1 r.2.1
private def back (g : Bool) : St :=go (.back g) (fun _=>reg .start true)
private def again (compare : Bool) : St :=
  go .scan (fun r=>reg (step r.1 (bit r)) (r.2.1 && (!compare || (r.2.2.2==some (bit r)))))

private def prog : Label → St
  | .load=>.peek .inp arg (.branch left
      (.pop .inp arg (.push .want bit (go .load reset))) (go .scan reset))
  | .scan=>.pop .inp arg (.branch (fun r=>r.2.2.1.isSome)
      (.push .buf bit (.branch (fun r=>keep r.1) (.pop .want test (again true)) (again false)))
      (.peek .want test (.goto fun r=>.drain (r.2.1 && r.2.2.2.isNone))))
  | .drain g=>.pop .want test (.branch (fun r=>r.2.2.2.isSome) (go (.drain g) (fun _=>reg .start true)) (back g))
  | .back g=>.pop .buf test (.branch (fun r=>r.2.2.2.isSome)
      (if g then .push .out (fun r=>r.2.2.2.getD false) (back g) else back g)
      (.load (fun _=>reg .start true) .halt))

def machine : FinTM2 where
  K:=Tape; k₀:=.inp; k₁:=.out; Γ:=A; Λ:=Label; main:=.load; σ:=R; initialState:=reg .start true; m:=prog

private def bank (xs : List (Bool ⊕ Bool)) (want buf out : List Bool) : (k : Tape) → List (A k)
  | .inp=>xs | .want=>want | .buf=>buf | .out=>out
private def frame (l : Label) (r : R) (xs : List (Bool ⊕ Bool)) (want buf out : List Bool) : machine.Cfg :=
  ⟨some l,r,bank xs want buf out⟩

private theorem inputSet (xs ws : List (Bool ⊕ Bool)) (a b c : List Bool) :
    Function.update (bank xs a b c) .inp ws=bank ws a b c := by funext k;cases k <;> rfl
private theorem wantSet (xs : List (Bool ⊕ Bool)) (a b c v : List Bool) :
    Function.update (bank xs a b c) .want v=bank xs v b c := by funext k;cases k <;> rfl
private theorem bufSet (xs : List (Bool ⊕ Bool)) (a b c v : List Bool) :
    Function.update (bank xs a b c) .buf v=bank xs a v c := by funext k;cases k <;> rfl
private theorem outSet (xs : List (Bool ⊕ Bool)) (a b c v : List Bool) :
    Function.update (bank xs a b c) .out v=bank xs a b v := by funext k;cases k <;> rfl
private theorem arg_in (xs : List (Bool ⊕ Bool)) (a b c : List Bool) : bank xs a b c .inp=xs:=rfl
private theorem arg_want (xs : List (Bool ⊕ Bool)) (a b c : List Bool) : bank xs a b c .want=a:=rfl
private theorem arg_buf (xs : List (Bool ⊕ Bool)) (a b c : List Bool) : bank xs a b c .buf=b:=rfl
private theorem arg_out (xs : List (Bool ⊕ Bool)) (a b c : List Bool) : bank xs a b c .out=c:=rfl

private theorem loadOne (b : Bool) (xs : List (Bool ⊕ Bool)) (want : List Bool) :
    machine.step (frame .load (reg .start true) (.inl b::xs) want [] [])=
      some (frame .load (reg .start true) xs (b::want) [] []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,arg,test,bit,left,go,reg,reset,arg_in,arg_want,inputSet,wantSet] <;>rfl

private theorem loadEnd (xs want : List Bool) :
    machine.step (frame .load (reg .start true) (xs.map Sum.inr) want [] [])=
      some (frame .scan (reg .start true) (xs.map Sum.inr) want [] []) := by
  change TM2.step prog _=_
  cases xs <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,left,go,reg,reset,arg_in] <;>rfl

private theorem scanOne (s : State) (good b : Bool) (xs want buf : List Bool) :
    machine.step (frame .scan (reg s good) (.inr b::xs.map Sum.inr) want buf [])=
      some (frame .scan (reg (step s b) (good && (!keep s || (want.head?==some b))))
        (xs.map Sum.inr) (if keep s then want.tail else want) (b::buf) []) := by
  change TM2.step prog _=_
  cases h:keep s <;> cases want <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,test,go,reg,again,bit,h,
    inputSet,wantSet,bufSet,arg_in,arg_want,arg_buf] <;>rfl

private theorem scanEnd (s : State) (good : Bool) (want buf : List Bool) :
    machine.step (frame .scan (reg s good) [] want buf [])=
      some (frame (.drain (good && want.isEmpty)) (reg s good |> fun r=>test r want.head?) [] want buf []) := by
  change TM2.step prog _=_
  cases want <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,test,reg,arg_in,arg_want,inputSet] <;>rfl

private theorem drainOne (g b : Bool) (r : R) (want buf : List Bool) :
    machine.step (frame (.drain g) r [] (b::want) buf [])=
      some (frame (.drain g) (reg .start true) [] want buf []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,test,go,reg,arg_want,wantSet] <;> rfl
private theorem drainEnd (g : Bool) (r : R) (buf : List Bool) :
    machine.step (frame (.drain g) r [] [] buf [])=some (frame (.back g) (reg .start true) [] [] buf []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,test,back,go,reg,arg_want,wantSet] <;>rfl

private theorem backOne (g b : Bool) (buf out : List Bool) :
    machine.step (frame (.back g) (reg .start true) [] [] (b::buf) out)=
      some (frame (.back g) (reg .start true) [] [] buf (if g then b::out else out)) := by
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,test,back,go,reg,arg_buf,arg_out,bufSet,outSet] <;>rfl
private theorem backEnd (g : Bool) (out : List Bool) :
    machine.step (frame (.back g) (reg .start true) [] [] [] out)=some (haltList machine out) := by
  have eq : (⟨none,reg .start true,bank [] [] [] out⟩ : TM2.Cfg A Label R)=haltList machine out:=by
    unfold haltList;congr 1;funext k;cases k <;>rfl
  apply Eq.trans _ (congrArg some eq)
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,test,reg,arg_buf,bufSet] <;>rfl

private abbrev Walk (n : ℕ) (a b : machine.Cfg) := (flip bind machine.step)^[n] (some a)=some b
private theorem before {n : ℕ} {a b c : machine.Cfg} (h : machine.step a=some b) (t : Walk n b c) : Walk (n+1) a c := by
  unfold Walk;rw [Function.iterate_succ_apply];change (flip bind machine.step)^[n] (machine.step a)=some c;rwa [h]
private theorem chain {m n : ℕ} {a b c : machine.Cfg} (h : Walk m a b) (g : Walk n b c) : Walk (m+n) a c := by
  unfold Walk at *;rw [Nat.add_comm m n,Function.iterate_add_apply,h,g]

private theorem loadAll (xs w want : List Bool) :
    Walk (xs.length+1) (frame .load (reg .start true) (xs.map Sum.inl++w.map Sum.inr) want [] [])
      (frame .scan (reg .start true) (w.map Sum.inr) (xs.reverse++want) [] []) := by
  induction xs generalizing want with
  | nil=>exact before (loadEnd w want) rfl
  | cons b xs ih=>simpa only [List.length_cons,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append]
      using before (loadOne b (xs.map Sum.inl++w.map Sum.inr) want) (ih (b::want))

private theorem scanAll (s : State) (g : Bool) (w want buf : List Bool) :
    ∃ r : R, ∃ rem : List Bool, rem.length≤want.length ∧
    Walk (w.length+1) (frame .scan (reg s g) (w.map Sum.inr) want buf [])
      (frame (.drain (g && (want==erase s w))) r [] rem (w.reverse++buf) []) := by
  induction w generalizing s g want buf with
  | nil=>
    have eq : (want.isEmpty)=(want==[]) := by cases want <;>rfl
    refine ⟨test (reg s g) want.head?,want,le_rfl,?_⟩
    simpa only [erase,List.length_nil,List.reverse_nil,List.nil_append,List.map_nil,eq] using before (scanEnd s g want buf) (show Walk 0 _ _ from rfl)
  | cons b w ih=>
    let g':=g && (!keep s || (want.head?==some b))
    let want':=if keep s then want.tail else want
    obtain ⟨r,rem,le,run⟩:=ih (step s b) g' want' (b::buf)
    have le':want'.length≤want.length:=by dsimp [want'];split <;> simp
    refine ⟨r,rem,le.trans le',?_⟩
    have go:=before (scanOne s g b w want buf) run
    have eq : (g' && (want'==erase (step s b) w))=(g && (want==erase s (b::w))) := by
      cases hk:keep s <;> cases want with
      | nil=>simp [g',want',erase,hk]
      | cons x xs=>cases x <;> cases b <;> simp [g',want',erase,hk,Bool.and_assoc]
    simpa only [List.length_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,eq] using go

private theorem drainAll (g : Bool) (r : R) (ws buf : List Bool) :
    Walk (ws.length+1) (frame (.drain g) r [] ws buf []) (frame (.back g) (reg .start true) [] [] buf []) := by
  induction ws generalizing r with
  | nil=>exact before (drainEnd g r buf) rfl
  | cons b ws ih=>exact before (drainOne g b r ws buf) (ih _)

private theorem backAll (g : Bool) (ws ys : List Bool) :
    Walk (ws.length+1) (frame (.back g) (reg .start true) [] [] ws ys)
      (haltList machine ((if g then ws.reverse else [])++ys)) := by
  induction ws generalizing ys with
  | nil=>simpa using before (backEnd g ys) (show Walk 0 _ _ from rfl)
  | cons w ws ih=>
    have run:=before (backOne g w ws ys) (ih (if g then w::ys else ys))
    cases g <;> simpa [List.append_assoc] using run

/-- The first part contains the reversed commitment, matching its order on the work stack. -/
def pair (c w : List Bool) : List (Bool ⊕ Bool) := c.reverse.map Sum.inl ++ w.map Sum.inr

def matched (c w : List Bool) : List Bool := if c=erase .start w then w else []

noncomputable def runs (c w : List Bool) :
    TM2OutputsInTime machine (pair c w) (some (matched c w)) (2*c.length+2*w.length+4) := by
  have init : initList machine (pair c w)=frame .load (reg .start true) (pair c w) [] [] [] := by
    unfold initList frame;congr 1;funext k;cases k <;>rfl
  have first:=loadAll c.reverse w []
  rw [List.reverse_reverse,List.append_nil,List.length_reverse] at first
  let aux:=scanAll .start true w c []
  let r:=aux.choose
  let rem:=aux.choose_spec.choose
  have le:rem.length≤c.length:=aux.choose_spec.choose_spec.1
  have second : Walk (w.length+1) (frame .scan (reg .start true) (w.map Sum.inr) c [] [])
      (frame (.drain (true && (c==erase .start w))) r [] rem (w.reverse++[]) []) :=aux.choose_spec.choose_spec.2
  simp only [Bool.true_and,List.append_nil] at second
  have third:=drainAll (c==erase .start w) r rem w.reverse
  have fourth:=backAll (c==erase .start w) w.reverse []
  rw [List.length_reverse,List.reverse_reverse,List.append_nil] at fourth
  have run:=chain (chain (chain first second) third) fourth
  have eq : (if (c==erase .start w) then w else [])=matched c w:=by simp [matched]
  rw [eq] at run
  let n:=(c.length+1)+(w.length+1)+(rem.length+1)+(w.length+1)
  refine ⟨⟨n,?_⟩,show n≤2*c.length+2*w.length+4 by dsimp [n];omega⟩
  change Walk n (initList machine (pair c w)) (haltList machine (matched c w))
  rw [init]
  exact run

end OwnedRadix.Code.Match

namespace OwnedRadix
open Turing

private theorem finish_unclosed (z o g : Bool) :
    machine.step (frame scan z o g [] empty)=some (Turing.haltList machine [g]) := by
    have eq : (⟨none,reg false false true,bank [] empty [g]⟩ : TM2.Cfg Alphabet Label Reg)=haltList machine [g] := by
      unfold haltList; congr 1;funext k;rcases k with _|_|b <;>rfl
    apply Eq.trans _ (congrArg some eq)
    change TM2.step program _=_
    simp [frame,scan,program,TM2.step,TM2.stepAux,reg,cached,bank_in,bank_out,done,setInput,setOutput]

private def rejectsSentinel : Turing.TM2OutputsInTime machine [.value (false,false)] (some [false]) 2 := by
  refine ⟨⟨2,?_⟩,le_rfl⟩
  have a:=scan_value false false true (false,false) [] empty
  have b:=finish_unclosed true false false
  change Run 2 (Turing.initList machine _) (Turing.haltList machine [false])
  exact (congrArg (fun c : machine.Cfg=>(flip bind machine.step)^[2] (some c)) (init_frame [.value (false,false)])).trans (before a (single b))

namespace Code
open Turing PEqualNP.Library.Machines

private noncomputable def seq {M N : FinTM2} (f : M.Γ M.k₁→N.Γ N.k₀) (d : N.Γ N.k₀)
    {x y z m n} (a : TM2OutputsInTime M x (some y) m)
    (b : TM2OutputsInTime N (y.map f) (some z) n) :
    TM2OutputsInTime (comp M N f (some d)) x (some z) (m+(2*y.length+2)+n) := by
  have found : ∃ k≤m+(2*y.length+2)+n, (flip bind (comp M N f (some d)).step)^[k]
      (some (initList (comp M N f (some d)) x))=some (haltList (comp M N f (some d)) z) := by
    obtain ⟨k,h,_,run⟩:=comp_run f (some d) (by simp) x y z a.steps b.steps a.evals_in_steps b.evals_in_steps
    change k≤a.steps+(2*y.length+2)+b.steps at h
    exact ⟨k,by have :=a.steps_le_m;have :=b.steps_le_m;omega,run⟩
  exact ⟨⟨found.choose,found.choose_spec.2⟩,found.choose_spec.1⟩

private def extend {M : FinTM2} {x y m n} (a : TM2OutputsInTime M x y m) (h:m≤n) :
    TM2OutputsInTime M x y n := ⟨a.toEvalsTo,a.steps_le_m.trans h⟩

private def emitStep (s : State) (b : Bool) : State × Option Token × Option Token :=
  (step s b,emit s b,none)
private def lastToken (s : State) : Option Token := some (finish s)
private def parser := trM emitStep lastToken .start (some .close)

private theorem fst_lex (s : State) (w : List Bool) : fstRun2 emitStep lastToken s w=lex s w := by
  induction w generalizing s with
  | nil=>rfl
  | cons b bs ih=>simp [fstRun2,lex,emitStep,ih]

private def parsing (w : List Bool) : TM2OutputsInTime parser w (some (lex .start w)) (2*w.length+3) := by
  refine ⟨⟨w.length+1+1+(w.length+1),?_⟩,show w.length+1+1+(w.length+1)≤2*w.length+3 by omega⟩
  exact (trM_run emitStep lastToken .start (some .close) (by simp) w).trans
    (congrArg (fun t=>some (haltList parser t)) (fst_lex .start w))

private noncomputable def checkedParser := comp Guard.machine parser id (some false)
noncomputable def evaluator := comp checkedParser machine id (some .close)

private theorem word_len (w : List Bool) : (Guard.goodWord w).length≤w.length := by
  unfold Guard.goodWord;split <;> simp
private theorem lex_len (s : State) (w : List Bool) : (lex s w).length≤w.length+1 := by
  induction w generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    have h:=ih (step s b)
    have e:((emit s b).toList).length≤1:=by cases emit s b <;> simp
    rw [lex,List.length_append,List.length_cons];omega

private noncomputable def frontRun (w : List Bool) :
    TM2OutputsInTime checkedParser w (some (lex .start (Guard.goodWord w))) (6*w.length+7) := by
  have second : TM2OutputsInTime parser ((Guard.goodWord w).map id) (some (lex .start (Guard.goodWord w))) (2*(Guard.goodWord w).length+3) :=
    (List.map_id (Guard.goodWord w)).symm ▸ parsing (Guard.goodWord w)
  apply extend (seq (M:=Guard.machine) (N:=parser) id false (Guard.runs w) second)
  change 2*w.length+2+(2*(Guard.goodWord w).length+2)+(2*(Guard.goodWord w).length+3)≤6*w.length+7
  have :=word_len w;omega

private noncomputable def evaluateWith (w : List Bool) (v : Bool) (m : ℕ)
    (a : TM2OutputsInTime machine (lex .start (Guard.goodWord w)) (some [v]) m) :
    TM2OutputsInTime evaluator w (some [v]) (8*w.length+m+11) := by
  have second : TM2OutputsInTime machine ((lex .start (Guard.goodWord w)).map id) (some [v]) m := by
    exact (List.map_id (lex .start (Guard.goodWord w))).symm ▸ a
  apply extend (seq (M:=checkedParser) (N:=machine) id .close (frontRun w) second)
  change 6*w.length+7+(2*(lex .start (Guard.goodWord w)).length+2)+m≤8*w.length+m+11
  have :=lex_len .start (Guard.goodWord w);have :=word_len w;omega

private def records (ds : List Decorated) (out : Name) (v : Bool) := trace ds++[(out,(false,v))]
def spend (w : List Bool) (rs : List Record) := 8*w.length+7*weight rs+12

noncomputable def on_code (ds : List Decorated) (out : Name) (v : Bool) :
    TM2OutputsInTime evaluator (raw ds out v) (some [fine (records ds out v)])
      (spend (raw ds out v) (records ds out v)) := by
  let w:=raw ds out v
  let rs:=records ds out v
  have ne:rs≠[]:=by simp [rs,records]
  have arg: lex .start (Guard.goodWord w)=optionalGroup rs := by
    rw [optionalGroup,ite_eq_right ne]
    simp only [w,Guard.goodWord,wellformed,ite_true,compiled,rs,records]
  have mid : TM2OutputsInTime machine (lex .start (Guard.goodWord w)) (some [fine rs]) (7*weight rs+1) :=
    arg.symm ▸ checks rs
  apply extend (evaluateWith w _ _ mid)
  dsimp [spend,w,rs];omega

noncomputable def malformed (w : List Bool) (h : ¬accept .start w) :
    TM2OutputsInTime evaluator w (some [false]) (8*w.length+13) := by
  apply extend (evaluateWith w false 2 ?_) (by omega)
  have e : lex .start (Guard.goodWord w)=[Token.value (false,false)] := by simp [Guard.goodWord,h,lex,finish]
  exact e.symm ▸ rejectsSentinel

end Code
end OwnedRadix
namespace OwnedRadix.Code
open Turing PEqualNP.Library.Machines

private theorem outputs_agree {tm : FinTM2} {input : List (tm.Γ tm.k₀)}
    {u v : List (tm.Γ tm.k₁)} {s t : ℕ}
    (a : TM2OutputsInTime tm input (some u) s) (b : TM2OutputsInTime tm input (some v) t) : u=v := by
  have later {x y : List (tm.Γ tm.k₁)} {k m : ℕ}
      (h : (flip bind tm.step)^[k] (some (initList tm input))=some (haltList tm x))
      (g : (flip bind tm.step)^[m] (some (initList tm input))=some (haltList tm y)) (le : k≤m) : x=y := by
    obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le le
    rw [Nat.add_comm k d,Function.iterate_add_apply,h] at g
    cases d with
    | zero=>
      have e : haltList tm x=haltList tm y:=Option.some.inj g
      simpa [haltList] using congrArg (fun c : tm.Cfg=>c.stk tm.k₁) e
    | succ d=>
      rw [Function.iterate_succ_apply] at g
      change (flip bind tm.step)^[d] none=some _ at g
      rw [Function.iterate_fixed (show (flip bind tm.step) none=none from rfl)] at g
      cases g
  rcases Nat.le_total a.steps b.steps with h|h
  · exact later a.evals_in_steps b.evals_in_steps h
  · exact (later b.evals_in_steps a.evals_in_steps h).symm

noncomputable def protocol := comp Match.machine evaluator id (some false)

private noncomputable def run_spec (c w : List Bool) (v : Bool) (n : ℕ)
    (a : TM2OutputsInTime evaluator (Match.matched c w) (some [v]) n) :
    TM2OutputsInTime protocol (Match.pair c w) (some [v]) (2*c.length+4*w.length+n+6) := by
  let mw:=Match.matched c w
  have b : TM2OutputsInTime evaluator (mw.map id) (some [v]) n:=(List.map_id mw).symm ▸ a
  apply extend (seq (M:=Match.machine) (N:=evaluator) id false (Match.runs c w) b)
  have le : mw.length≤w.length:=by dsimp [mw,Match.matched];split <;>simp
  change 2*c.length+2*w.length+4+(2*mw.length+2)+n≤2*c.length+4*w.length+n+6
  omega

private theorem filtered (ds : List Decorated) (out : Name) (v : Bool) :
    Match.matched (bare (ds.map Prod.fst) out v) (raw ds out v)=raw ds out v := by simp [Match.matched,erase_raw]

def honestSteps (ds : List Decorated) (out : Name) (v : Bool) :=
  2*(bare (ds.map Prod.fst) out v).length+4*(raw ds out v).length+
    spend (raw ds out v) (records ds out v)+6

noncomputable def honest_run (ds : List Decorated) (out : Name) (v : Bool) :
    TM2OutputsInTime protocol (Match.pair (bare (ds.map Prod.fst) out v) (raw ds out v))
      (some [fine (records ds out v)]) (honestSteps ds out v) :=
  run_spec _ _ _ _ ((filtered ds out v).symm ▸ on_code ds out v)

/-- Rigidity on arbitrary, possibly malformed byte strings. Any accepted opening
recovers an evaluable named circuit, its unique commitment, and the claimed output. -/
theorem accepts_only {c w : List Bool} {n : ℕ}
    (yes : TM2OutputsInTime protocol (Match.pair c w) (some [true]) n) :
    ∃ ds out v, w=raw ds out v ∧ c=bare (ds.map Prod.fst) out v ∧
      ∃ e, evalProgram emptyEnv (ds.map Prod.fst)=some e ∧ e out=some v := by
  have eq : c=erase .start w := by
    by_contra diff
    have mw : Match.matched c w=[]:=by simp [Match.matched,diff]
    have reject : TM2OutputsInTime evaluator (Match.matched c w) (some [false]) 13 :=
      (congrArg (fun x : List Bool=>TM2OutputsInTime evaluator x (some [false]) 13) mw).mpr (malformed [] (by decide))
    have no:=run_spec c w false _ reject
    have bad:=outputs_agree no yes
    cases bad
  have mw : Match.matched c w=w:=by simp [Match.matched,eq]
  have parses : accept .start w := by
    by_contra wrong
    have no:=run_spec c w false _ (mw.symm ▸ malformed w wrong)
    cases outputs_agree no yes
  obtain ⟨ds,out,v,rfl⟩:=decode_exists w parses
  have ec:=eq.trans (erase_raw ds out v)
  clear eq mw
  subst c
  have bit : fine (records ds out v)=true:=List.cons.inj (outputs_agree (honest_run ds out v) yes) |>.1
  exact ⟨ds,out,v,rfl,rfl,(named_output_iff _ _ _).mpr ⟨ds,rfl,bit⟩⟩

/-- Raw commitment evaluation by one fixed finite multistack machine. Every
possible opening is covered by the soundness direction. -/
theorem committed_output_iff (gs : List Gate) (out : Name) (v : Bool) :
    (∃ e, evalProgram emptyEnv gs=some e ∧ e out=some v) ↔
    ∃ (w : List Bool) (n : ℕ), Nonempty (TM2OutputsInTime protocol (Match.pair (bare gs out v) w) (some [true]) n) := by
  constructor
  · intro value
    obtain ⟨ds,rfl,ok⟩:=(named_output_iff gs out v).mp value
    refine ⟨raw ds out v,honestSteps ds out v,⟨?_⟩⟩
    change fine (records ds out v)=true at ok
    exact ok ▸ honest_run ds out v
  · rintro ⟨w,n,⟨yes⟩⟩
    obtain ⟨ds,other,b,_,same,h⟩:=accepts_only yes
    obtain ⟨rfl,rfl,rfl⟩:=bare_injective same
    exact h

end OwnedRadix.Code
namespace OwnedRadix.Code

def bounded (d : ℕ) (g : Gate) : Prop := ∀ n∈inputs g.expr++[g.name],n.length≤d

private theorem name_size (k : Name) : (nameBits k).length=2*k.length+1 := by
  induction k with
  | nil=>rfl
  | cons b k ih=>simp [nameBits,ih];omega

private theorem op_size (op : Shape) : (opcode op).length≤4 := by cases op <;> simp [opcode]

private theorem fields_size (g : Gate) (d : ℕ) (h : bounded d g) : (names g).length≤3*(2*d+1) := by
  have one (n : Name) (hn:n∈inputs g.expr++[g.name]) : (nameBits n).length≤2*d+1 := by
    rw [name_size];have :=h _ hn;omega
  have sum (ks : List Name) (mem : ∀ n∈ks,n∈inputs g.expr++[g.name]) :
      (ks.flatMap nameBits).length≤ks.length*(2*d+1) := by
    induction ks with
    | nil=>simp
    | cons k ks ih=>
      have u:=one k (mem k List.mem_cons_self)
      have v:=ih (fun x hx=>mem x (List.mem_cons_of_mem _ hx))
      rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul];omega
  have count : (inputs g.expr++[g.name]).length≤3 :=by cases g.expr <;> simp [inputs]
  exact (sum _ (fun _ h=>h)).trans (Nat.mul_le_mul_right _ count)

private theorem item_bound (g : Gate) (q : Guess) (d : ℕ) (h:bounded d g) :
    (clause (g,q)).length≤6*d+9 := by
  have :=fields_size g d h
  have :=op_size (shape g.expr)
  simp only [clause,List.length_append,List.length_cons,List.length_nil];omega

theorem raw_size (ds : List Decorated) (out : Name) (v : Bool) (d : ℕ)
    (hs : ∀ a∈ds,bounded d a.1) (ho:out.length≤d) :
    (raw ds out v).length≤(6*d+9)*ds.length+2*d+3 := by
  have entries : (ds.flatMap clause).length≤(6*d+9)*ds.length := by
    induction ds with
    | nil=>simp
    | cons a ds ih=>
      have h:=item_bound a.1 a.2 d (hs a List.mem_cons_self)
      change (clause a).length≤6*d+9 at h
      have t:=ih (fun x hx=>hs x (List.mem_cons_of_mem _ hx))
      rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ];omega
  simp only [raw,List.length_append,List.length_cons,List.length_nil,name_size];omega

private theorem erase_length (s : State) (w : List Bool) : (erase s w).length≤w.length := by
  induction w generalizing s with
  | nil=>rfl
  | cons b w ih=>
    have h:=ih (step s b)
    cases e:keep s <;> simp [erase,e] <;> omega

private theorem bounded_event (g : Gate) (q : Guess) (d : ℕ) (h : bounded d g) :
    ∀ r∈events g q,r.1.length≤d := by
  have key (r : Record) (hr : r∈reads g.expr q) : r.1∈inputs g.expr := by
    cases op:g.expr <;> simp [op,reads] at hr <;> simp_all [inputs]
    all_goals rcases hr with rfl|rfl <;> simp
  intro r hr
  rcases List.mem_append.mp hr with use|defn
  · exact h _ (List.mem_append_left _ (key r use))
  · obtain rfl:=List.mem_singleton.mp defn;exact h _ (List.mem_append_right _ List.mem_cons_self)

private theorem bounded_records (ds : List Decorated) (out : Name) (v : Bool) (d : ℕ)
    (h : ∀ a∈ds,bounded d a.1) (last:out.length≤d) :
    ∀ r∈records ds out v,r.1.length≤d := by
  intro r hr
  rcases List.mem_append.mp hr with use|final
  · obtain ⟨a,ha,obs⟩:=List.mem_flatMap.mp use
    exact bounded_event a.1 a.2 d (h _ ha) r obs
  · obtain rfl:=List.mem_singleton.mp final;exact last

private theorem tariff (rs : List Record) (d : ℕ) (h : ∀ r∈rs,r.1.length≤d) :
    weight rs≤(d+1)*(body rs).length := by
  induction rs with
  | nil=>simp [weight,body]
  | cons r rs ih=>
    have e:=Nat.mul_le_mul_right (r.1.length+1) (Nat.succ_le_succ (h r List.mem_cons_self))
    change (r.1.length+1)*(r.1.length+1)≤(d+1)*(r.1.length+1) at e
    have k:=ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
    change (r.1.length+1)^2+weight rs≤_
    rw [body_cons,List.length_append,encode_length,Nat.mul_add,pow_two];omega

private theorem raw_body (ds : List Decorated) (out : Name) (v : Bool) :
    (body (records ds out v)).length≤(raw ds out v).length := by
  have cap:=lex_len .start (raw ds out v)
  rw [compiled,group,List.length_append] at cap
  simpa only [records,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_le_add_iff_right] using cap

theorem near_linear_steps (ds : List Decorated) (out : Name) (v : Bool) (d : ℕ)
    (h : ∀ a∈ds,bounded d a.1) (last : out.length≤d) :
    honestSteps ds out v≤(7*d+21)*(raw ds out v).length+18 := by
  have lean:=tariff (records ds out v) d (bounded_records ds out v d h last)
  have body:=Nat.mul_le_mul_left (d+1) (raw_body ds out v)
  have hdr:=erase_length .start (raw ds out v)
  rw [erase_raw] at hdr
  dsimp [honestSteps,spend]
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc] at *
  omega

/-- End-to-end binary length and physical clock on an honest answer, with
equivalence on every malicious opening supplied by committed_output_iff. -/
theorem efficient_opening (gs : List Gate) (out : Name) (v : Bool) (d : ℕ)
    (h : ∀ g∈gs,bounded d g) (last : out.length≤d)
    (ok : ∃ e, evalProgram emptyEnv gs=some e ∧ e out=some v) :
    ∃ w : List Bool, w.length≤(6*d+9)*gs.length+2*d+3 ∧
      Nonempty (Turing.TM2OutputsInTime protocol (Match.pair (bare gs out v) w) (some [true])
        ((7*d+21)*w.length+18)) := by
  obtain ⟨ds,rfl,bit⟩:=(named_output_iff gs out v).mp ok
  have hh (a : Decorated) (ha:a∈ds) : bounded d a.1:=h a.1 (List.mem_map_of_mem ha)
  refine ⟨raw ds out v,by simpa only [List.length_map] using raw_size ds out v d hh last,⟨?_⟩⟩
  have run:=extend (honest_run ds out v) (near_linear_steps ds out v d hh last)
  change fine (records ds out v)=true at bit
  exact bit ▸ run

end OwnedRadix.Code
namespace OwnedRadix.Code

/-- Literal cells supply the ordered variable ports. The final answer is supplied
by the querying context, so its slot has the same status as these input bits. -/
def port : State → Bool | .literalBit | .askBit=>true | _=>false
def fixedBit (s : State) (b : Bool) := if port s then false else b
def structureBits : State → List Bool → List Bool
  | _,[]=>[]
  | s,b::bs=>if keep s then fixedBit s b::structureBits (step s b) bs else structureBits (step s b) bs
def portBits : State → List Bool → List Bool
  | _,[]=>[]
  | s,b::bs=>if port s then b::portBits (step s b) bs else portBits (step s b) bs

def normalize (g : Gate) : Gate :=
  match g.expr with
  | .literal _=>⟨g.name,.literal false⟩
  | _=>g
def circuit (gs : List Gate) (out : Name) := bare (gs.map normalize) out false
def params (gs : List Gate) : List Bool := gs.filterMap (fun g=>match g.expr with | .literal b=>some b | _=>none)

private theorem projections_name (k : Name) (m : Mark) (r : Rest) (t : List Bool) :
    structureBits (.field m r) (nameBits k++t)=nameBits k++structureBits (next r) t ∧
    portBits (.field m r) (nameBits k++t)=portBits (next r) t := by
  induction k with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b k ih=>exact ⟨congrArg (fun a=>false::b::a) ih.1,ih.2⟩

private theorem projections_clause (d : Decorated) (w : List Bool) :
    structureBits .start (clause d++w)=opcode (shape (normalize d.1).expr)++names (normalize d.1)++structureBits .start w ∧
    portBits .start (clause d++w)=params [d.1]++portBits .start w := by
  obtain ⟨⟨out,expr⟩,a,b⟩:=d
  have st (s : Shape) (k : List Bool) :
      structureBits .start (opcode s++[a,b]++k)=opcode (match s with | .lit _=>.lit false | _=>s)++structureBits (plan s a b) k := by cases s <;>rfl
  have pt (s : Shape) (k : List Bool) :
      portBits .start (opcode s++[a,b]++k)=(match s with | .lit v=>[v] | _=>[])++portBits (plan s a b) k := by cases s <;>rfl
  unfold clause
  rw [List.append_assoc,st,pt]
  cases expr <;> simp [normalize,names,inputs,plan,next,shape,params,List.append_assoc,
    fun k m r t=>(projections_name k m r t).1,fun k m r t=>(projections_name k m r t).2]

theorem raw_projections (ds : List Decorated) (out : Name) (v : Bool) :
    structureBits .start (raw ds out v)=circuit (ds.map Prod.fst) out ∧
    portBits .start (raw ds out v)=params (ds.map Prod.fst)++[v] := by
  induction ds with
  | nil=>
    obtain ⟨hs,hp⟩:=projections_name out (false,v) .returnAsk []
    constructor
    · change true::false::structureBits (.field (false,v) .returnAsk) (nameBits out)=true::false::nameBits out
      simpa [structureBits] using congrArg (fun u=>true::false::u) hs
    · change v::portBits (.field (false,v) .returnAsk) (nameBits out)=[v]
      simpa [portBits] using congrArg (v::·) hp
  | cons d ds ih=>
    obtain ⟨hs,hp⟩:=projections_clause d (raw ds out v)
    refine ⟨?_,?_⟩
    · simpa [circuit,bare,raw,List.append_assoc] using
        hs.trans (congrArg (opcode (shape (normalize d.1).expr)++names (normalize d.1)++·) ih.1)
    · have p : params (d.1::ds.map Prod.fst)=params [d.1]++params (ds.map Prod.fst) := by
        cases e:d.1.expr <;> simp [params,e]
      simpa [raw,p,List.append_assoc] using hp.trans (congrArg (params [d.1]++·) ih.2)

private theorem gate_recover (a b : Gate) (h:normalize a=normalize b) (q:params [a]=params [b]) : a=b := by
  obtain ⟨na,x⟩:=a
  obtain ⟨nb,y⟩:=b
  cases x <;> cases y <;> simp_all [normalize,params]

/-- A normalized program plus its ordered input string determine every gate. -/
theorem filled_unique {gs hs : List Gate} (eg:gs.map normalize=hs.map normalize) (eq:params gs=params hs) : gs=hs := by
  induction gs generalizing hs with
  | nil=>simpa using eg.symm
  | cons g gs ih=>
    rcases hs with _|⟨h,hs⟩
    · cases eg
    obtain ⟨first,rest⟩:=List.cons.inj eg
    have parts (a : Gate) (t : List Gate) : params (a::t)=params [a]++params t := by cases op:a.expr <;>simp [params,op]
    rw [parts g gs,parts h hs] at eq
    have sameLen : (params [g]).length=(params [h]).length := by
      clear parts eq rest ih
      obtain ⟨n,x⟩:=g
      obtain ⟨m,y⟩:=h
      cases x <;> cases y <;> simp_all [normalize,params]
    obtain ⟨q,tail⟩:=List.append_inj eq sameLen
    exact congrArg₂ List.cons (gate_recover g h first q) (ih rest tail)

end OwnedRadix.Code
namespace OwnedRadix.Code.Parameter
open Turing

abbrev Symbol := (Bool × Bool) ⊕ Bool
inductive Tape where | inp | want (side : Bool) | buf | out deriving DecidableEq
instance : Fintype Tape := Fintype.ofList [.inp,.want false,.want true,.buf,.out] (by
  intro k;cases k with | want b=>cases b <;>simp | inp | buf | out=>simp)
inductive Label where | load | scan | drain (side good : Bool) | back (good : Bool) deriving DecidableEq, Fintype
private abbrev A : Tape → Type | .inp=>Symbol | _=>Bool
private abbrev R := State × Bool × Option Symbol × Option Bool
private abbrev St := TM2.Stmt A Label R
private def reg (s : State) (ok : Bool) : R := (s,ok,none,none)
private def arg (r : R) (a : Option Symbol) : R := (r.1,r.2.1,a,r.2.2.2)
private def test (r : R) (a : Option Bool) : R := (r.1,r.2.1,r.2.2.1,a)
private def bit (r : R) : Bool := match r.2.2.1 with | some (.inl (_,b)) | some (.inr b)=>b | none=>false
private def isLoad (r : R) : Bool := match r.2.2.1 with | some (.inl _)=>true | _=>false
private def side (r : R) : Bool := match r.2.2.1 with | some (.inl (c,_))=>c | _=>false
private def go (l : Label) (s : R → R) : St := .load s (.goto fun _=>l)
private def reset (r : R) := reg r.1 r.2.1
private def again : St :=go .scan (fun r=>reg (step r.1 (bit r)) r.2.1)
private def advance (l : Label) : St :=go l (fun _=>reg .start true)
private def check (c : Bool) (r : R) (a : Option Bool) : R :=
  (r.1,r.2.1 && (a==some (if c then bit r else fixedBit r.1 (bit r))),r.2.2.1,none)
private def exhausted (r : R) (a : Option Bool) : R := (r.1,r.2.1 && a.isNone,r.2.2.1,none)
private def portTest : St := .branch (fun r=>port r.1) (.pop (.want true) (check true) again) again

private def prog : Label → St
  | .load=>.peek .inp arg (.branch isLoad (.pop .inp arg (.branch side
      (.push (.want true) bit (go .load reset)) (.push (.want false) bit (go .load reset)))) (go .scan reset))
  | .scan=>.pop .inp arg (.branch (fun r=>r.2.2.1.isSome)
      (.push .buf bit (.branch (fun r=>keep r.1) (.pop (.want false) (check false) portTest) portTest))
      (.peek (.want false) exhausted (.peek (.want true) exhausted (.goto fun r=>.drain false r.2.1))))
  | .drain c g=>.pop (.want c) test (.branch (fun r=>r.2.2.2.isSome)
      (advance (.drain c g)) (advance (if c then .back g else .drain true g)))
  | .back g=>.pop .buf test (.branch (fun r=>r.2.2.2.isSome)
      (if g then .push .out (fun r=>r.2.2.2.getD false) (advance (.back g)) else advance (.back g))
      (.load (fun _=>reg .start true) .halt))

def machine : FinTM2 where
  K:=Tape; k₀:=.inp; k₁:=.out; Γ:=A; Λ:=Label; main:=.load; σ:=R; initialState:=reg .start true; m:=prog

private abbrev Wants := Bool → List Bool
private def bank (xs : List Symbol) (ws : Wants) (buf out : List Bool) : (k : Tape) → List (A k)
  | .inp=>xs | .want c=>ws c | .buf=>buf | .out=>out
private def frame (l : Label) (r : R) (xs : List Symbol) (ws : Wants) (buf out : List Bool) : machine.Cfg :=
  ⟨some l,r,bank xs ws buf out⟩
private def wants (a b : List Bool) : Wants | false=>a | true=>b

private theorem inSet (xs ys : List Symbol) (ws : Wants) (buf out : List Bool) :
    Function.update (bank xs ws buf out) .inp ys=bank ys ws buf out := by
  funext k;cases k <;>rfl
private theorem wantSet (xs : List Symbol) (ws : Wants) (buf out : List Bool) (c : Bool) (v : List Bool) :
    Function.update (bank xs ws buf out) (.want c) v = bank xs (Function.update ws c v) buf out := by
  funext k;cases k with
  | want b=>cases b <;> cases c <;>rfl
  | inp | buf | out=>rfl
private theorem bufSet (xs : List Symbol) (ws : Wants) (buf out v : List Bool) :
    Function.update (bank xs ws buf out) .buf v=bank xs ws v out := by funext k;cases k <;>rfl
private theorem outSet (xs : List Symbol) (ws : Wants) (buf out v : List Bool) :
    Function.update (bank xs ws buf out) .out v=bank xs ws buf v := by funext k;cases k <;>rfl
private theorem want0 (a b v : List Bool) : Function.update (wants a b) false v=wants v b := by funext c;cases c <;>rfl
private theorem want1 (a b v : List Bool) : Function.update (wants a b) true v=wants a v := by funext c;cases c <;>rfl
private theorem arg_in (xs : List Symbol) (ws : Wants) (a b : List Bool) : bank xs ws a b .inp=xs:=rfl
private theorem arg_want (xs : List Symbol) (ws : Wants) (a b : List Bool) (c : Bool) : bank xs ws a b (.want c)=ws c:=rfl
private theorem arg_buf (xs : List Symbol) (ws : Wants) (a b : List Bool) : bank xs ws a b .buf=a:=rfl
private theorem arg_out (xs : List Symbol) (ws : Wants) (a b : List Bool) : bank xs ws a b .out=b:=rfl
private theorem w0 (a b : List Bool) : wants a b false=a:=rfl
private theorem w1 (a b : List Bool) : wants a b true=b:=rfl

private theorem loadOne (b c : Bool) (xs : List Symbol) (ws : Wants) :
    machine.step (frame .load (reg .start true) (.inl (c,b)::xs) ws [] [])=
      some (frame .load (reg .start true) xs (Function.update ws c (b::ws c)) [] []) := by
  change TM2.step prog _=_
  cases c <;>simp [frame,prog,TM2.step,TM2.stepAux,arg,bit,isLoad,side,go,reg,reset,arg_in,arg_want,inSet,wantSet] <;>rfl

private theorem loadEnd (xs : List Bool) (ws : Wants) :
    machine.step (frame .load (reg .start true) (xs.map Sum.inr) ws [] [])=
      some (frame .scan (reg .start true) (xs.map Sum.inr) ws [] []) := by
  change TM2.step prog _=_
  cases xs <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,isLoad,go,reg,reset,arg_in] <;>rfl

private def fits (use v : Bool) (w : List Bool) : Bool := !use || (w.head?==some v)
private def consume (use : Bool) (w : List Bool) := if use then w.tail else w

private theorem scanOne (s : State) (g b : Bool) (xs u v buf : List Bool) :
    machine.step (frame .scan (reg s g) (.inr b::xs.map Sum.inr) (wants u v) buf [])=
      some (frame .scan (reg (step s b) (g && fits (keep s) (fixedBit s b) u && fits (port s) b v))
        (xs.map Sum.inr) (wants (consume (keep s) u) (consume (port s) v)) (b::buf) []) := by
  change TM2.step prog _=_
  cases h:keep s <;> cases k:port s <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,test,go,reg,again,bit,h,k,
    portTest,check,consume,fits,inSet,wantSet,want0,want1,w0,w1,bufSet,arg_in,arg_want,arg_buf] <;>rfl

private theorem scanEnd (s : State) (g : Bool) (u v buf : List Bool) :
    machine.step (frame .scan (reg s g) [] (wants u v) buf [])=
      some (frame (.drain false (g && u.isEmpty && v.isEmpty))
        (exhausted (exhausted (reg s g) u.head?) v.head?) [] (wants u v) buf []) := by
  change TM2.step prog _=_
  cases u <;> cases v <;> simp [frame,prog,TM2.step,TM2.stepAux,arg,exhausted,reg,arg_in,arg_want,w0,w1,inSet] <;>rfl

private theorem drainOne (s g b : Bool) (r : R) (ws : Wants) (buf t : List Bool) (e:ws s=b::t) :
    machine.step (frame (.drain s g) r [] ws buf [])=
      some (frame (.drain s g) (reg .start true) [] (Function.update ws s t) buf []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,advance,test,go,reg,arg_want,wantSet,e] <;>rfl
private theorem drainEnd (s g : Bool) (r : R) (ws : Wants) (buf : List Bool) (e:ws s=[]) :
    machine.step (frame (.drain s g) r [] ws buf [])=
      some (frame (if s then .back g else .drain true g) (reg .start true) [] ws buf []) := by
  have up : Function.update ws s []=ws:=Function.update_eq_self_iff.mpr e.symm
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,advance,test,go,reg,arg_want,wantSet,e,up] <;>rfl

private theorem backOne (g b : Bool) (buf out : List Bool) :
    machine.step (frame (.back g) (reg .start true) [] (wants [] []) (b::buf) out)=
      some (frame (.back g) (reg .start true) [] (wants [] []) buf (if g then b::out else out)) := by
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,test,advance,go,reg,arg_buf,arg_out,bufSet,outSet] <;>rfl
private theorem backEnd (g : Bool) (out : List Bool) :
    machine.step (frame (.back g) (reg .start true) [] (wants [] []) [] out)=some (haltList machine out) := by
  have eq : (⟨none,reg .start true,bank [] (wants [] []) [] out⟩ : TM2.Cfg A Label R)=haltList machine out:=by
    unfold haltList;congr 1;funext k;cases k with | want b=>cases b <;>rfl | inp | buf | out=>rfl
  apply Eq.trans _ (congrArg some eq)
  change TM2.step prog _=_
  cases g <;> simp [frame,prog,TM2.step,TM2.stepAux,test,reg,arg_buf,bufSet] <;>rfl

private abbrev Walk (n : ℕ) (a b : machine.Cfg) := (flip bind machine.step)^[n] (some a)=some b
private theorem before {n : ℕ} {a b c : machine.Cfg} (h : machine.step a=some b) (t : Walk n b c) : Walk (n+1) a c := by
  unfold Walk;rw [Function.iterate_succ_apply];change (flip bind machine.step)^[n] (machine.step a)=some c;rwa [h]
private theorem chain {m n : ℕ} {a b c : machine.Cfg} (h : Walk m a b) (g : Walk n b c) : Walk (m+n) a c := by
  unfold Walk at *;rw [Nat.add_comm m n,Function.iterate_add_apply,h,g]

end OwnedRadix.Code.Parameter
namespace OwnedRadix.Code.Parameter
open Turing

private def tag (s b : Bool) : Symbol := .inl (s,b)
private theorem loadList (c : Bool) (xs : List Bool) (tail : List Symbol) (ws : Wants) :
    Walk xs.length (frame .load (reg .start true) (xs.map (tag c)++tail) ws [] [])
      (frame .load (reg .start true) tail (Function.update ws c (xs.reverse++ws c)) [] []) := by
  induction xs generalizing ws with
  | nil=>simp [Walk]
  | cons b xs ih=>
    have go:=before (loadOne b c (xs.map (tag c)++tail) ws) (ih (Function.update ws c (b::ws c)))
    simpa only [tag,List.length_cons,List.map_cons,List.cons_append,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append,Function.update_self,Function.update_idem] using go

private theorem fits_tail (use b : Bool) (w tail : List Bool) :
    (fits use b w && (consume use w==tail))=(w==(if use then b::tail else tail)) := by
  cases use <;> cases w with
  | nil=>simp [consume,fits]
  | cons a w=>cases a <;> cases b <;> simp [consume,fits]

private theorem scanAll (s : State) (g : Bool) (w u v buf : List Bool) :
    ∃ r : R, ∃ un vn : List Bool, un.length≤u.length ∧ vn.length≤v.length ∧
    Walk (w.length+1) (frame .scan (reg s g) (w.map Sum.inr) (wants u v) buf [])
      (frame (.drain false (g && (u==structureBits s w) && (v==portBits s w))) r [] (wants un vn) (w.reverse++buf) []) := by
  induction w generalizing s g u v buf with
  | nil=>
    have eq (a : List Bool) : a.isEmpty=(a==[]) := by cases a <;>rfl
    refine ⟨exhausted (exhausted (reg s g) u.head?) v.head?,u,v,le_rfl,le_rfl,?_⟩
    simpa only [structureBits,portBits,List.length_nil,List.reverse_nil,List.nil_append,List.map_nil,eq] using before (scanEnd s g u v buf) (show Walk 0 _ _ from rfl)
  | cons b w ih=>
    let good:=g && fits (keep s) (fixedBit s b) u && fits (port s) b v
    obtain ⟨r,un,vn,le0,le1,run⟩:=ih (step s b) good (consume (keep s) u) (consume (port s) v) (b::buf)
    have use_le (flag : Bool) (xs : List Bool) : (consume flag xs).length≤xs.length := by cases flag <;> simp [consume]
    refine ⟨r,un,vn,le0.trans (use_le _ _),le1.trans (use_le _ _),?_⟩
    have go:=before (scanOne s g b w u v buf) run
    have eq : (good && (consume (keep s) u==structureBits (step s b) w) && (consume (port s) v==portBits (step s b) w)) =
        (g && (u==structureBits s (b::w)) && (v==portBits s (b::w))) := by
      rw [structureBits,portBits,←fits_tail,←fits_tail]
      simp only [good,Bool.and_assoc,Bool.and_left_comm,Bool.and_comm]
    simpa only [List.length_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append,eq] using go

private theorem drainAll (c g : Bool) (r : R) (ws : Wants) (xs buf : List Bool) (e:ws c=xs) :
    Walk (xs.length+1) (frame (.drain c g) r [] ws buf [])
      (frame (if c then .back g else .drain true g) (reg .start true) [] (Function.update ws c []) buf []) := by
  induction xs generalizing ws r with
  | nil=>
    have up:Function.update ws c []=ws:=Function.update_eq_self_iff.mpr e.symm
    simpa only [List.length_nil,up] using before (drainEnd c g r ws buf e) (show Walk 0 _ _ from rfl)
  | cons b xs ih=>
    have go:=before (drainOne c g b r ws buf xs e) (ih _ (Function.update ws c xs) (Function.update_self ..))
    simpa only [List.length_cons,Function.update_idem] using go

private theorem backAll (g : Bool) (ws ys : List Bool) :
    Walk (ws.length+1) (frame (.back g) (reg .start true) [] (wants [] []) ws ys)
      (haltList machine ((if g then ws.reverse else [])++ys)) := by
  induction ws generalizing ys with
  | nil=>simpa using before (backEnd g ys) (show Walk 0 _ _ from rfl)
  | cons w ws ih=>
    have run:=before (backOne g w ws ys) (ih (if g then w::ys else ys))
    cases g <;> simpa [List.append_assoc] using run

def triple (c x w : List Bool) : List Symbol :=
  c.reverse.map (tag false) ++ x.reverse.map (tag true) ++ w.map Sum.inr

def good (c x w : List Bool) : List Bool :=
  if c=structureBits .start w ∧ x=portBits .start w then w else []

noncomputable def runs (c x w : List Bool) :
    TM2OutputsInTime machine (triple c x w) (some (good c x w)) (2*c.length+2*x.length+2*w.length+5) := by
  have init : initList machine (triple c x w)=frame .load (reg .start true) (triple c x w) (wants [] []) [] [] := by
    unfold initList frame;congr 1;funext k;cases k with | want b=>cases b <;>rfl | inp | buf | out=>rfl
  have lc:=loadList false c.reverse (x.reverse.map (tag true)++w.map Sum.inr) (wants [] [])
  simp only [List.length_reverse,List.reverse_reverse,w0,List.append_nil,want0] at lc
  have lx:=loadList true x.reverse (w.map Sum.inr) (wants c [])
  simp only [List.length_reverse,List.reverse_reverse,w1,List.append_nil,want1] at lx
  have start:=chain (chain lc lx) (before (loadEnd w (wants c x)) (show Walk 0 _ _ from rfl))
  let aux:=scanAll .start true w c x []
  let r:=aux.choose
  let u:=aux.choose_spec.choose
  let v:=aux.choose_spec.choose_spec.choose
  let g:=(c==structureBits .start w) && (x==portBits .start w)
  have ulen:u.length≤c.length:=aux.choose_spec.choose_spec.choose_spec.1
  have vlen:v.length≤x.length:=aux.choose_spec.choose_spec.choose_spec.2.1
  have middle : Walk (w.length+1) (frame .scan (reg .start true) (w.map Sum.inr) (wants c x) [] [])
      (frame (.drain false g) r [] (wants u v) w.reverse []) := by
    have run : Walk (w.length+1) (frame .scan (reg .start true) (w.map Sum.inr) (wants c x) [] [])
        (frame (.drain false (true && (c==structureBits .start w) && (x==portBits .start w))) r [] (wants u v) (w.reverse++[]) []) :=
      aux.choose_spec.choose_spec.choose_spec.2.2
    simpa only [Bool.true_and,List.append_nil,g] using run
  have d0:=drainAll false g r (wants u v) u w.reverse rfl
  have d1:=drainAll true g (reg .start true) (wants [] v) v w.reverse rfl
  simp only [Bool.false_eq_true,ite_false,want0] at d0
  simp only [ite_true,want1] at d1
  have last:=backAll g w.reverse []
  rw [List.length_reverse,List.reverse_reverse,List.append_nil] at last
  have run:=chain (chain (chain (chain start middle) d0) d1) last
  have eq : (if g then w else [])=good c x w:=by simp [good,g]
  rw [eq] at run
  let n:=c.length+x.length+1+(w.length+1)+(u.length+1)+(v.length+1)+(w.length+1)
  refine ⟨⟨n,?_⟩,show n≤2*c.length+2*x.length+2*w.length+5 by dsimp [n];omega⟩
  change Walk n (initList machine (triple c x w)) (haltList machine (good c x w))
  rw [init]
  simpa only [triple,List.append_assoc] using run

end OwnedRadix.Code.Parameter
namespace OwnedRadix.Code
open Turing PEqualNP.Library.Machines

noncomputable def queryVerifier := comp Parameter.machine evaluator id (some false)

private noncomputable def query_run (c x w : List Bool) (v : Bool) (n : ℕ)
    (a : TM2OutputsInTime evaluator (Parameter.good c x w) (some [v]) n) :
    TM2OutputsInTime queryVerifier (Parameter.triple c x w) (some [v]) (2*c.length+2*x.length+4*w.length+n+7) := by
  let mw:=Parameter.good c x w
  have b : TM2OutputsInTime evaluator (mw.map id) (some [v]) n:=(List.map_id mw).symm ▸ a
  apply extend (seq (M:=Parameter.machine) (N:=evaluator) id false (Parameter.runs c x w) b)
  have le : mw.length≤w.length:=by dsimp [mw,Parameter.good];split <;>simp
  change 2*c.length+2*x.length+2*w.length+5+(2*mw.length+2)+n≤2*c.length+2*x.length+4*w.length+n+7
  omega

private theorem query_filtered (ds : List Decorated) (out : Name) (b : Bool) :
    Parameter.good (circuit (ds.map Prod.fst) out) (params (ds.map Prod.fst)++[b]) (raw ds out b)=raw ds out b := by
  obtain ⟨c,p⟩:=raw_projections ds out b
  simp [Parameter.good,c,p]

def querySpend (ds : List Decorated) (out : Name) (b : Bool) :=
  2*(circuit (ds.map Prod.fst) out).length+2*(params (ds.map Prod.fst)++[b]).length+4*(raw ds out b).length+
    spend (raw ds out b) (records ds out b)+7

noncomputable def query_honest (ds : List Decorated) (out : Name) (b : Bool) :
    TM2OutputsInTime queryVerifier (Parameter.triple (circuit (ds.map Prod.fst) out)
      (params (ds.map Prod.fst)++[b]) (raw ds out b))
      (some [fine (records ds out b)]) (querySpend ds out b) :=
  query_run _ _ _ _ _ ((query_filtered ds out b).symm ▸ on_code ds out b)

/-- An arbitrary accepted commitment and opening determine a normalized circuit,
its true input port values, and its actual claimed output. -/
theorem query_extract {c x w : List Bool} {n : ℕ}
    (yes : TM2OutputsInTime queryVerifier (Parameter.triple c x w) (some [true]) n) :
    ∃ ds out b, w=raw ds out b ∧ c=circuit (ds.map Prod.fst) out ∧
      x=params (ds.map Prod.fst)++[b] ∧ ∃ e, evalProgram emptyEnv (ds.map Prod.fst)=some e ∧ e out=some b := by
  have ok : c=structureBits .start w ∧ x=portBits .start w := by
    by_contra wrong
    have none : Parameter.good c x w=[]:=by simp [Parameter.good,wrong]
    have reject : TM2OutputsInTime evaluator (Parameter.good c x w) (some [false]) 13 :=
      (congrArg (fun t : List Bool=>TM2OutputsInTime evaluator t (some [false]) 13) none).mpr (malformed [] (by decide))
    cases outputs_agree (query_run c x w false 13 reject) yes
  have mw : Parameter.good c x w=w:=by simp [Parameter.good,ok]
  have parses : accept .start w := by
    by_contra wrong
    cases outputs_agree (query_run c x w false _ (mw.symm ▸ malformed w wrong)) yes
  obtain ⟨ds,out,b,rfl⟩:=decode_exists w parses
  obtain ⟨shapeBits,ports⟩:=raw_projections ds out b
  have ec:=ok.1.trans shapeBits
  have ex:=ok.2.trans ports
  clear ok mw
  subst c
  subst x
  have bit : fine (records ds out b)=true:=List.cons.inj (outputs_agree (query_honest ds out b) yes) |>.1
  exact ⟨ds,out,b,rfl,rfl,rfl,(named_output_iff _ _ _).mpr ⟨ds,rfl,bit⟩⟩

def Answered (c x : List Bool) (b : Bool) : Prop :=
  ∃ w n, Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple c (x++[b]) w) (some [true]) n)

/-- This property holds for every bit string used as the commitment, including
arbitrary strings supplied independently of the input query. -/
theorem answer_unique {c x : List Bool} {u v : Bool} (au:Answered c x u) (av:Answered c x v) : u=v := by
  obtain ⟨_,_,⟨yes⟩⟩:=au
  obtain ⟨_,_,⟨also⟩⟩:=av
  obtain ⟨d,o,b,_,ec,ex,e1,ev1,h1⟩:=query_extract yes
  obtain ⟨d',p,b',_,ec',ex',e2,ev2,h2⟩:=query_extract also
  have p1:=List.append_inj_right' (s₁:=x) (s₂:=params (d.map Prod.fst)) (t₁:=[u]) (t₂:=[b]) ex (by rfl)
  have p2:=List.append_inj_right' (s₁:=x) (s₂:=params (d'.map Prod.fst)) (t₁:=[v]) (t₂:=[b']) ex' (by rfl)
  have xu : x=params (d.map Prod.fst):=List.append_inj_left' ex (by rfl)
  have xv : x=params (d'.map Prod.fst):=List.append_inj_left' ex' (by rfl)
  have same:=bare_injective (ec.symm.trans ec')
  have gates:=filled_unique same.1 (xu.symm.trans xv)
  rw [gates] at ev1
  have env:e1=e2:=Option.some.inj (ev1.symm.trans ev2)
  rw [env,same.2.1] at h1
  exact (List.cons.inj p1).1.trans ((Option.some.inj (h1.symm.trans h2)).trans (List.cons.inj p2).1.symm)

/-- Every byte commitment has a single global Boolean completion compatible
with all of its accepted challenge answers. -/
theorem commitment_function (c : List Bool) : ∃ f : List Bool → Bool, ∀ x b, Answered c x b → f x=b := by
  classical
  refine ⟨fun x=>decide (Answered c x true),?_⟩
  intro x b ok
  cases b with
  | true=>simp [ok]
  | false=>
    have bad : ¬Answered c x true:=fun h=>Bool.false_ne_true (answer_unique ok h)
    simp [bad]

end OwnedRadix.Code
namespace OwnedRadix.Code
open Turing

private theorem projection_length (s : State) (w : List Bool) :
    (structureBits s w).length≤w.length ∧ (portBits s w).length≤w.length := by
  induction w generalizing s with
  | nil=>exact ⟨le_rfl,le_rfl⟩
  | cons b w ih=>
    obtain ⟨hs,hp⟩:=ih (step s b)
    constructor
    · cases e:keep s <;> simp [structureBits,e] <;>omega
    · cases e:port s <;> simp [portBits,e] <;>omega

theorem query_near_linear (ds : List Decorated) (out : Name) (v : Bool) (d : ℕ)
    (h : ∀ a∈ds,bounded d a.1) (last : out.length≤d) :
    querySpend ds out v≤(7*d+23)*(raw ds out v).length+19 := by
  let r:=raw ds out v
  have lean:=tariff (records ds out v) d (bounded_records ds out v d h last)
  have body:=Nat.mul_le_mul_left (d+1) (raw_body ds out v)
  obtain ⟨c,p⟩:=projection_length .start (raw ds out v)
  obtain ⟨sc,sp⟩:=raw_projections ds out v
  rw [sc] at c
  rw [sp] at p
  dsimp [querySpend,spend]
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc] at *
  omega

theorem query_opening (gs : List Gate) (out : Name) (v : Bool) (d : ℕ)
    (h : ∀ g∈gs,bounded d g) (last : out.length≤d)
    (yes : ∃ e, evalProgram emptyEnv gs=some e ∧ e out=some v) :
    ∃ (w : List Bool), w.length≤(6*d+9)*gs.length+2*d+3 ∧ (circuit gs out).length≤w.length ∧
      Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple (circuit gs out) (params gs++[v]) w) (some [true])
        ((7*d+23)*w.length+19)) := by
  obtain ⟨ds,rfl,ok⟩:=(named_output_iff gs out v).mp yes
  have hs (a : Decorated) (ha:a∈ds) : bounded d a.1:=h a.1 (List.mem_map_of_mem ha)
  have len:=(projection_length .start (raw ds out v)).1
  rw [(raw_projections ds out v).1] at len
  refine ⟨raw ds out v,by simpa only [List.length_map] using raw_size ds out v d hs last,len,⟨?_⟩⟩
  have run:=extend (query_honest ds out v) (query_near_linear ds out v d hs last)
  change fine (records ds out v)=true at ok
  exact ok ▸ run

end OwnedRadix.Code

namespace OwnedRadix.Compiler
open PEqualNP.CircuitLowerBounds

private abbrev FGate := PEqualNP.CircuitLowerBounds.Gate
private abbrev NGate := OwnedRadix.Gate

def wire (d i : ℕ) : Name := false::List.ofFn (fun j : Fin d=>i.testBit j.val)
private def zero : Name := []
private def one : Name := [true]

private theorem distinct {d a b : ℕ} (ha:a<2^d) (hb:b<2^d) (he:wire d a=wire d b) : a=b := by
  have eq:=(List.cons.inj he).2
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases lt:i<d
  · have h:=congrArg (fun l : List Bool=>l[i]?) eq
    simpa [lt] using h
  · have wide:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt lt)
    rw [Nat.testBit_eq_false_of_lt (ha.trans_le wide),Nat.testBit_eq_false_of_lt (hb.trans_le wide)]

private def Fits (d : ℕ) (vs : List Bool) (e : Env) : Prop :=
  e zero=some false ∧ e one=some true ∧ ∀ i<2^d,e (wire d i)=vs[i]?

private theorem append_fit {d : ℕ} {vs : List Bool} {e : Env} (h:Fits d vs e) (cap:vs.length<2^d) (v : Bool) :
    Fits d (vs++[v]) (put e (wire d vs.length) v) := by
  refine ⟨by simpa [put,zero,wire] using h.1,by simpa [put,one,wire] using h.2.1,?_⟩
  intro i hi
  by_cases eq:i=vs.length
  · subst i;simp [put]
  · have diff : wire d i≠wire d vs.length:=fun k=>eq (distinct hi cap k)
    rw [put,Function.update_of_ne diff,h.2.2 i hi]
    by_cases lt:i<vs.length
    · rw [List.getElem?_append_left lt]
    · have large : (vs++[v]).length ≤ i :=by simp;omega
      rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none large]

private def noop (a : Name) := Expr.disj a a
private def reference (d k i : ℕ) := if i<k then wire d i else zero

private theorem rd {d} {vs : List Bool} {e : Env} (h:Fits d vs e) (cap:vs.length≤2^d) (i : ℕ) :
    e (reference d vs.length i)=some (vs.getD i false) := by
  by_cases lt:i<vs.length
  · simp [reference,lt,h.2.2 i (lt.trans_le cap),List.getD_eq_getElem?_getD]
  · simp [reference,lt,h.1,List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_gt lt)]

private def expr (d k : ℕ) (g : FGate) : Expr :=
  let ref:=reference d k
  match g.op,g.inputs with
  | .and,[]=>noop one
  | .and,[a]=>noop (ref a)
  | .and,a::b::_=>.conj (ref a) (ref b)
  | .or,[]=>noop zero
  | .or,[a]=>noop (ref a)
  | .or,a::b::_=>.disj (ref a) (ref b)
  | .not,[]=>.neg zero
  | .not,a::_=>.neg (ref a)
  | _,_=>noop zero

private def gate (d k : ℕ) (g : FGate) : NGate := ⟨wire d k,expr d k g⟩
private def val (vs : List Bool) (g : FGate) := g.op.eval (g.inputs.map fun i=>vs.getD i false)
private def allowedGate (g : FGate) :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem calculated {d} {vs : List Bool} {e : Env} (h:Fits d vs e) (cap:vs.length≤2^d)
    (g : FGate) (hg:allowedGate g) : evalOp e (expr d vs.length g)=some (val vs g) := by
  obtain ⟨op,args⟩:=g
  obtain ⟨allowed,short⟩:=hg
  change op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at allowed
  change args.length≤2 at short
  rcases args with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩
  all_goals try simp at short
  all_goals cases op <;> simp_all [expr,noop,evalOp,val,GateOp.eval,h.1,h.2.1,rd h cap]

private def program (d : ℕ) : ℕ → List FGate → List NGate
  | _,[]=>[]
  | k,g::gs=>gate d k g::program d (k+1) gs

private theorem execute {d} (gs : List FGate) (vs : List Bool) (e : Env) (h:Fits d vs e)
    (cap:vs.length+gs.length≤2^d) (ok:∀ a∈gs,allowedGate a) :
    ∃ f, evalProgram e (program d vs.length gs)=some f ∧
      Fits d (gs.foldl (fun w a=>w++[val w a]) vs) f := by
  induction gs generalizing vs e with
  | nil=>exact ⟨e,rfl,h⟩
  | cons g gs ih=>
    simp only [List.length_cons] at cap
    have space:vs.length<2^d:=by omega
    have fresh : e (wire d vs.length)=none:=(h.2.2 _ space).trans (List.getElem?_eq_none le_rfl)
    have step : evalGate e (gate d vs.length g)=some (put e (wire d vs.length) (val vs g)) := by
      simp [evalGate,gate,fresh,calculated h space.le g (ok g List.mem_cons_self)]
    obtain ⟨f,k,final⟩:=ih (vs++[val vs g]) _ (append_fit h space _) (by simp;omega)
      (fun a ha=>ok a (List.mem_cons_of_mem _ ha))
    exact ⟨f,by simpa [program,evalProgram,step] using k,final⟩

private def load (d : ℕ) : ℕ → List Bool → List NGate
  | _,[]=>[]
  | k,b::bs=>⟨wire d k,.literal b⟩::load d (k+1) bs

private theorem load_run {d : ℕ} (xs vs : List Bool) (e : Env) (h:Fits d vs e)
    (cap:vs.length+xs.length≤2^d) :
    ∃ f, evalProgram e (load d vs.length xs)=some f ∧ Fits d (vs++xs) f := by
  induction xs generalizing vs e with
  | nil=>exact ⟨e,rfl,by simpa using h⟩
  | cons b bs ih=>
    simp only [List.length_cons] at cap
    have sp:vs.length<2^d:=by omega
    have fresh : e (wire d vs.length)=none:=(h.2.2 _ sp).trans (List.getElem?_eq_none le_rfl)
    have g : evalGate e ⟨wire d vs.length,.literal b⟩=some (put e (wire d vs.length) b):=by simp [evalGate,fresh,evalOp]
    obtain ⟨f,k,hf⟩:=ih (vs++[b]) _ (append_fit h sp b) (by simp;omega)
    exact ⟨f,by simpa [load,evalProgram,g] using k,by simpa using hf⟩

private def constants : List NGate := [⟨zero,.literal false⟩,⟨one,.literal true⟩]
private def start := put (put emptyEnv zero false) one true
private theorem constants_run : evalProgram emptyEnv constants=some start := by
  simp [evalProgram,constants,evalGate,evalOp,emptyEnv,put,start,one,zero]
private theorem constants_fit (d : ℕ) : Fits d [] start := by
  refine ⟨?_,?_,?_⟩
  · simp [start,put,zero,one]
  · simp [start,put,one]
  · intro i hi;simp [start,put,wire,one,zero,emptyEnv]

private theorem eval_append (e : Env) (a b : List NGate) :
    evalProgram e (a++b)=(evalProgram e a).bind (fun f=>evalProgram f b) := by
  induction a generalizing e with
  | nil=>rfl
  | cons g gs ih=>simp [evalProgram,ih,Option.bind_assoc]

def named (d : ℕ) (C : Circuit) (x : List Bool) : List NGate :=
  constants++load d 0 x++program d x.length C.gates
def output (d n : ℕ) (C : Circuit) := reference d (n+C.gates.length) C.output

private theorem end_length (vs : List Bool) (gs : List FGate) :
    (gs.foldl (fun w a=>w++[val w a]) vs).length=vs.length+gs.length := by
  induction gs generalizing vs with
  | nil=>simp
  | cons g gs ih=>simp [ih];omega

theorem faithful (d : ℕ) (C : Circuit) (x : List Bool)
    (cap:x.length+C.gates.length≤2^d) (ok:∀ g∈C.gates,allowedGate g) :
    ∃ f, evalProgram emptyEnv (named d C x)=some f ∧ f (output d x.length C)=some (C.eval x) := by
  obtain ⟨mid,hload,relation⟩:=load_run x [] start (constants_fit d) (by simpa using (show x.length≤2^d by omega))
  simp only [List.length_nil,List.nil_append] at hload relation
  obtain ⟨f,hprog,rep⟩:=execute C.gates x mid relation cap ok
  refine ⟨f,by simp [named,List.append_assoc,eval_append,constants_run,hload,hprog],?_⟩
  have len:=end_length x C.gates
  have extract:=rd rep (len ▸ cap) C.output
  rw [len] at extract
  exact extract

end OwnedRadix.Compiler
namespace OwnedRadix.Compiler
open PEqualNP.CircuitLowerBounds
open OwnedRadix.Code

private theorem normalized_load (d k : ℕ) (x : List Bool) :
    (load d k x).map normalize=load d k (List.replicate x.length false) := by
  induction x generalizing k with
  | nil=>rfl
  | cons b xs ih=>simp [load,Code.normalize,List.replicate_succ,ih]

private theorem commitment_fixed (d : ℕ) (C : Circuit) (x : List Bool) :
    circuit (named d C x) (output d x.length C)=
      circuit (named d C (List.replicate x.length false)) (output d x.length C) := by
  simp [circuit,named,List.map_append,normalized_load]

private theorem parameters_append (a b : List NGate) : params (a++b)=params a++params b := by simp [params]
private theorem parameters_load (d k : ℕ) (xs : List Bool) : params (load d k xs)=xs := by
  induction xs generalizing k with
  | nil=>rfl
  | cons b bs ih=>
    change b::params (load d (k+1) bs)=b::bs
    rw [ih]

private theorem parameters_program (d k : ℕ) (gs : List FGate) : params (program d k gs)=[] := by
  induction gs generalizing k with
  | nil=>rfl
  | cons g gs ih=>
    have single : params [gate d k g]=[] := by
      obtain ⟨op,args⟩:=g
      cases op <;> rcases args with _|⟨a,_|⟨b,tail⟩⟩ <;> rfl
    change params ([gate d k g]++program d (k+1) gs)=[]
    rw [parameters_append,single,ih];rfl

private theorem parameters (d : ℕ) (C : Circuit) (x : List Bool) :
    params (named d C x)=[false,true]++x := by
  rw [named,parameters_append,parameters_append,parameters_load,parameters_program,List.append_nil];rfl

private theorem width_wire (d i : ℕ) : (wire d i).length=d+1 := by simp [wire]
private theorem width_ref (d k i : ℕ) : (reference d k i).length≤d+1 := by unfold reference;split <;>simp [width_wire,zero]
private theorem width_gate (d k : ℕ) (g : FGate) : bounded (d+1) (gate d k g) := by
  obtain ⟨op,args⟩:=g
  cases op <;> rcases args with _|⟨a,_|⟨b,t⟩⟩
  all_goals simp [bounded,gate,expr,inputs,noop,zero,one,width_wire,width_ref]

private theorem width_load (d k : ℕ) (x : List Bool) : ∀ g∈load d k x,bounded (d+1) g := by
  induction x generalizing k with
  | nil=>simp [load]
  | cons b xs ih=>
    intro g hg
    rcases List.mem_cons.mp hg with rfl|h
    · simp [bounded,inputs,width_wire]
    · exact ih (k+1) _ h

private theorem width_program (d k : ℕ) (gs : List FGate) : ∀ g∈program d k gs,bounded (d+1) g := by
  induction gs generalizing k with
  | nil=>simp [program]
  | cons g gs ih=>
    intro a ha
    rcases List.mem_cons.mp ha with rfl|hm
    · exact width_gate _ _ _
    · exact ih (k+1) _ hm

private theorem width_named (d : ℕ) (C : Circuit) (x : List Bool) :
    ∀ g∈named d C x,bounded (d+1) g := by
  intro g hg
  rcases List.mem_append.mp hg with start|last
  · rcases List.mem_append.mp start with constants|vars
    · simp only [Compiler.constants,List.mem_cons,List.not_mem_nil,or_false] at constants
      rcases constants with rfl|rfl <;>simp [bounded,inputs,zero,one]
    · exact width_load _ _ _ _ vars
  · exact width_program _ _ _ _ last

private theorem length_named (d : ℕ) (C : Circuit) (x : List Bool) :
    (named d C x).length=2+x.length+C.gates.length := by
  have lh (k) (xs : List Bool) : (load d k xs).length=xs.length := by
    induction xs generalizing k with
    | nil=>rfl
    | cons b xs ih=>simp [load,ih]
  have ph (k) (gs : List FGate) : (program d k gs).length=gs.length := by
    induction gs generalizing k with
    | nil=>rfl
    | cons g gs ih=>simp [program,ih]
  simp [named,constants,lh,ph];omega

/-- A single commitment handles all inputs to any official bounded fan-in-two
De Morgan circuit. All three messages are binary strings. The machine's input
alphabet tags their boundaries, and its two preparatory scans read the first
two strings in reverse order. The two constant input ports are false and true. -/
theorem realize_official {m s : ℕ} {f : (Fin m → Bool) → Bool}
    (circ : PEqualNP.MetaComplexity.HasCircuitSize m f s) (d : ℕ) (width:m+s≤2^d) :
    ∃ c : List Bool, c.length≤(6*(d+1)+9)*(2+m+s)+2*(d+1)+3 ∧
      (∀ x : Fin m → Bool, ∃ w : List Bool, w.length≤(6*(d+1)+9)*(2+m+s)+2*(d+1)+3 ∧
        Nonempty (Turing.TM2OutputsInTime queryVerifier
          (Parameter.triple c (([false,true]++List.ofFn x)++[f x]) w) (some [true])
          ((7*(d+1)+23)*w.length+19))) ∧
      (∀ (x : Fin m → Bool) (b : Bool), Answered c ([false,true]++List.ofFn x) b → b=f x) := by
  obtain ⟨C,hok,hsize,truth⟩:=circ
  change C.gates.length≤s at hsize
  let c:=circuit (named d C (List.replicate m false)) (output d m C)
  have run (x : Fin m → Bool) : ∃ w : List Bool, w.length≤(6*(d+1)+9)*(2+m+s)+2*(d+1)+3 ∧ c.length≤w.length ∧
      Nonempty (Turing.TM2OutputsInTime queryVerifier
        (Parameter.triple c (([false,true]++List.ofFn x)++[f x]) w) (some [true]) ((7*(d+1)+23)*w.length+19)) := by
    let xs:=List.ofFn x
    have l:xs.length=m:=List.length_ofFn
    have faith:=faithful d C xs (by omega) hok
    have genuine : ∃ e, evalProgram emptyEnv (named d C xs)=some e ∧ e (output d xs.length C)=some (f x) := by
      simpa only [xs,truth x] using faith
    obtain ⟨w,hw,hc,hy⟩:=query_opening (named d C xs) (output d xs.length C) (f x) (d+1)
      (width_named _ _ _) (width_ref _ _ _) genuine
    rw [length_named,l] at hw
    have bound : (6*(d+1)+9)*(2+m+C.gates.length)+2*(d+1)+3≤(6*(d+1)+9)*(2+m+s)+2*(d+1)+3 := by gcongr
    have fixed : circuit (named d C xs) (output d xs.length C)=c:=by simpa only [l,c] using commitment_fixed d C xs
    rw [fixed] at hc hy
    rw [parameters] at hy
    exact ⟨w,hw.trans bound,hc,hy⟩
  obtain ⟨_,wlen,clen,_⟩:=run (fun _=>false)
  refine ⟨c,clen.trans wlen,?_,?_⟩
  · intro x;obtain ⟨w,h,_,yes⟩:=run x;exact ⟨w,h,yes⟩
  · intro x b alleged
    obtain ⟨w,_,_,good⟩:=run x
    exact answer_unique alleged ⟨w,_,good⟩

end OwnedRadix.Compiler
namespace OwnedRadix.Code
open Turing

/-- Every framed raw query terminates with exactly one Boolean answer, including
arbitrary binary commitments, requested bits and malformed openings. -/
theorem total_query (c x w : List Bool) :
    ∃ b : Bool, ∃ n : ℕ, Nonempty (TM2OutputsInTime queryVerifier (Parameter.triple c x w) (some [b]) n) := by
  let v:=Parameter.good c x w
  have total (u : List Bool) : ∃ b : Bool, ∃ n : ℕ, Nonempty (TM2OutputsInTime evaluator u (some [b]) n) := by
    by_cases correct : accept .start u
    · obtain ⟨ds,out,b,rfl⟩:=decode_exists u correct
      exact ⟨_,_,⟨on_code ds out b⟩⟩
    · exact ⟨false,_,⟨malformed u correct⟩⟩
  obtain ⟨b,n,⟨h⟩⟩:=total v
  exact ⟨b,_,⟨query_run c x w b n h⟩⟩

theorem machine_answers_agree {tm : FinTM2} {input : List (tm.Γ tm.k₀)}
    {u v : List (tm.Γ tm.k₁)} {s t : ℕ}
    (a : TM2OutputsInTime tm input (some u) s) (b : TM2OutputsInTime tm input (some v) t) : u=v :=
  outputs_agree a b

end OwnedRadix.Code

#print axioms OwnedRadix.Compiler.realize_official
#print axioms OwnedRadix.Code.commitment_function
