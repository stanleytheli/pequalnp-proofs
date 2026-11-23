import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Tactic.DeriveFintype

namespace DyadicLookup
open Turing

def retain {A : Type} (keep : Bool) : List A→List A
  | []=>[]
  | a::as'=>if keep then a::retain (!keep) as' else retain (!keep) as'

theorem length_bound {A : Type} (b : Bool) (xs : List A) :
    2*(retain b xs).length≤xs.length+1 ∧ 2*(retain b xs).length≤xs.length+b.toNat := by
  induction xs generalizing b with
  | nil=>simp [retain]
  | cons a xs ih=>cases b <;>simp [retain] <;>have t:=ih true <;>have f:=ih false <;>simp at t f <;>omega

theorem digit_lookup {A : Type} (xs : List A) (bit : Bool) (j : ℕ) :
    (retain (!bit) xs)[j]?=xs[bit.toNat+2*j]? := by
  induction xs using List.twoStepInduction generalizing j with
  | nil=>simp [retain]
  | singleton a=>cases bit <;>cases j <;>simp [retain]
  | cons_cons a b xs ih=>
    cases bit with
    | false=>
      cases j with
      | zero=>rfl
      | succ j=>
        change (retain true xs)[j]?=(a::b::xs)[0+2*(j+1)]?
        rw [show 0+2*(j+1)=(0+2*j)+2 by omega]
        exact ih j
    | true=>
      cases j with
      | zero=>rfl
      | succ j=>
        change (retain false xs)[j]?=(a::b::xs)[1+2*(j+1)]?
        rw [show 1+2*(j+1)=(1+2*j)+2 by omega]
        exact ih j


def numeric : List Bool→ℕ
  | []=>0
  | a::as'=>a.toNat+2*numeric as'

def lookup {A : Type} : List Bool→List A→Option A
  | [],xs=>xs.head?
  | b::bs,xs=>lookup bs (retain (!b) xs)

theorem lookup_value {A : Type} (bits : List Bool) (xs : List A) : lookup bits xs=xs[numeric bits]? := by
  induction bits generalizing xs with
  | nil=>cases xs <;>rfl
  | cons b bs ih=>rw [lookup,ih,digit_lookup];rfl

def steps {A : Type} : List Bool→List A→ℕ
  | [],xs=>xs.length+2
  | b::bs,xs=>xs.length+(retain (!b) xs).length+3+steps bs (retain (!b) xs)

theorem time_bound {A : Type} (bits : List Bool) (xs : List A) : steps bits xs≤3*xs.length+5*bits.length+2 := by
  induction bits generalizing xs with
  | nil=>simp [steps];omega
  | cons b bs ih=>
    have z:=ih (retain (!b) xs)
    have r:=(length_bound (!b) xs).1
    simp only [steps,List.length_cons]
    omega

end DyadicLookup
namespace DyadicLookup
open Turing

inductive Tape where | inp | data | temp | out deriving DecidableEq
instance : Fintype Tape:=Fintype.ofList [.inp,.data,.temp,.out] (by intro k;cases k <;>simp)
inductive Label where | load | next | scan (keep : Bool) | restore | clean deriving DecidableEq, Fintype
private abbrev Token:=Bool⊕Bool
private abbrev A : Tape→Type | .inp=>Token | _=>Bool
private abbrev R:=Option Token × Option Bool
private abbrev St:=TM2.Stmt A Label R
private def empty : R:=(none,none)
private def got (r : R) (v : Option Token) : R:=(v,r.2)
private def saved (r : R) (v : Option Bool) : R:=(r.1,v)
private def tokenBit (r : R) : Bool:=match r.1 with | some (.inl b) | some (.inr b)=>b | none=>false
private def wasData (r : R) : Bool:=match r.1 with | some (.inl _)=>true | _=>false
private def go (l : Label) : St:=.load (fun _=>empty) (.goto fun _=>l)
private def endState : St:=.load (fun _=>empty) .halt

private def prog : Label→St
  | .load=>.peek .inp got <| .branch wasData
      (.pop .inp got (.push .data tokenBit (go .load))) (go .next)
  | .next=>.pop .inp got <| .branch (fun r=>r.1.isSome)
      (.branch tokenBit (go (.scan false)) (go (.scan true)))
      (.pop .data saved (.branch (fun r=>r.2.isSome) (.push .out (fun r=>r.2.getD false) (go .clean)) endState))
  | .scan keep=>.pop .data saved <| .branch (fun r=>r.2.isSome)
      (if keep then .push .temp (fun r=>r.2.getD false) (go (.scan false)) else go (.scan true)) (go .restore)
  | .restore=>.pop .temp saved <| .branch (fun r=>r.2.isSome)
      (.push .data (fun r=>r.2.getD false) (go .restore)) (go .next)
  | .clean=>.pop .data saved <| .branch (fun r=>r.2.isSome) (go .clean) endState

def machine : FinTM2 where
  K:=Tape;Γ:=A;k₀:=.inp;k₁:=.out;Λ:=Label;σ:=R;main:=.load;initialState:=empty;m:=prog

private def cells (ts : List Token) (xs tmp out : List Bool) : (k : Tape)→List (A k)
  | .inp=>ts | .data=>xs | .temp=>tmp | .out=>out
private def frame (l : Label) (ts : List Token) (xs tmp out : List Bool) : machine.Cfg:=
  ⟨some l,empty,cells ts xs tmp out⟩
private theorem inpSet (a b : List Token) (x y z : List Bool) :
    Function.update (cells a x y z) .inp b=cells b x y z:=by funext k;cases k <;>rfl
private theorem dataSet (a : List Token) (x u y z : List Bool) :
    Function.update (cells a x y z) .data u=cells a u y z:=by funext k;cases k <;>rfl
private theorem tmpSet (a : List Token) (x u y z : List Bool) :
    Function.update (cells a x y z) .temp u=cells a x u z:=by funext k;cases k <;>rfl
private theorem outSet (a : List Token) (x u y z : List Bool) :
    Function.update (cells a x y z) .out u=cells a x y u:=by funext k;cases k <;>rfl
private theorem terminal (out : List Bool) :
    (⟨none,empty,cells [] [] [] out⟩ : machine.Cfg)=haltList machine out:=by
  unfold haltList
  congr 1
  funext k;cases k <;>rfl

private theorem load_one (b : Bool) (ts : List Token) (xs : List Bool) :
    machine.step (frame .load (.inl b::ts) xs [] [])=some (frame .load ts (b::xs) [] []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,got,wasData,tokenBit,go,cells,inpSet,dataSet] <;>rfl

private theorem load_end (bs : List Bool) (xs : List Bool) :
    machine.step (frame .load (bs.map Sum.inr) xs [] [])=some (frame .next (bs.map Sum.inr) xs [] []) := by
  change TM2.step prog _=_
  cases bs <;>simp [frame,prog,TM2.step,TM2.stepAux,got,wasData,go,cells] <;>rfl

private theorem next_bit (b : Bool) (ts : List Token) (xs : List Bool) :
    machine.step (frame .next (.inr b::ts) xs [] [])=some (frame (.scan (!b)) ts xs [] []) := by
  change TM2.step prog _=_
  cases b <;>simp [frame,prog,TM2.step,TM2.stepAux,got,tokenBit,go,cells,inpSet] <;>rfl

private theorem scan_one (b v : Bool) (ts : List Token) (xs tmp : List Bool) :
    machine.step (frame (.scan b) ts (v::xs) tmp [])=some (frame (.scan (!b)) ts xs (if b then v::tmp else tmp) []) := by
  change TM2.step prog _=_
  cases b <;>simp [frame,prog,TM2.step,TM2.stepAux,saved,go,cells,dataSet,tmpSet] <;>rfl

private theorem scan_end (b : Bool) (ts : List Token) (tmp : List Bool) :
    machine.step (frame (.scan b) ts [] tmp [])=some (frame .restore ts [] tmp []) := by
  change TM2.step prog _=_
  cases b <;>simp [frame,prog,TM2.step,TM2.stepAux,saved,go,cells,dataSet] <;>rfl

private theorem restore_one (v : Bool) (ts : List Token) (xs tmp : List Bool) :
    machine.step (frame .restore ts xs (v::tmp) [])=some (frame .restore ts (v::xs) tmp []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,go,cells,dataSet,tmpSet] <;>rfl

private theorem restore_end (ts : List Token) (xs : List Bool) :
    machine.step (frame .restore ts xs [] [])=some (frame .next ts xs [] []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,go,cells,tmpSet] <;>rfl

private theorem empty_end :
    machine.step (frame .next [] [] [] [])=some (haltList machine []) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,got,endState,cells,inpSet,dataSet]
  exact congrArg some (terminal [])
private theorem hit_end (v : Bool) (xs : List Bool) :
    machine.step (frame .next [] (v::xs) [] [])=some (frame .clean [] xs [] [v]) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,got,go,cells,inpSet,dataSet,outSet] <;>rfl
private theorem clean_one (v : Bool) (xs out : List Bool) :
    machine.step (frame .clean [] (v::xs) [] out)=some (frame .clean [] xs [] out) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,go,cells,dataSet] <;>rfl
private theorem clean_end (out : List Bool) :
    machine.step (frame .clean [] [] [] out)=some (haltList machine out) := by
  change TM2.step prog _=_
  simp [frame,prog,TM2.step,TM2.stepAux,saved,endState,cells,dataSet]
  exact congrArg some (terminal out)

private abbrev Walk (n : ℕ) (a b : machine.Cfg) := (flip bind machine.step)^[n] (some a)=some b
private theorem before {n : ℕ} {a b c : machine.Cfg} (h : machine.step a=some b) (t : Walk n b c) : Walk (n+1) a c := by
  unfold Walk;rw [Function.iterate_succ_apply];change (flip bind machine.step)^[n] (machine.step a)=some c;rwa [h]
private theorem seq {m n : ℕ} {a b c : machine.Cfg} (h : Walk m a b) (t : Walk n b c) : Walk (n+m) a c := by
  unfold Walk;rw [Function.iterate_add_apply,h];exact t

private theorem loading (xs bits acc : List Bool) :
    Walk (xs.length+1) (frame .load (xs.map Sum.inl++bits.map Sum.inr) acc [] [])
      (frame .next (bits.map Sum.inr) (xs.reverse++acc) [] []) := by
  induction xs generalizing acc with
  | nil=>exact before (load_end bits acc) rfl
  | cons x xs ih=>
    simpa only [List.map_cons,List.cons_append,List.length_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,List.nil_append] using before (load_one x _ acc) (ih (x::acc))

private theorem scanning (keep : Bool) (xs acc : List Bool) (ts : List Token) :
    Walk (xs.length+1) (frame (.scan keep) ts xs acc []) (frame .restore ts [] ((retain keep xs).reverse++acc) []) := by
  induction xs generalizing keep acc with
  | nil=>exact before (scan_end keep ts acc) rfl
  | cons x xs ih=>
    have h:=before (scan_one keep x ts xs acc) (ih (!keep) (if keep then x::acc else acc))
    cases keep <;>simpa [retain,List.append_assoc] using h

private theorem restoring (xs acc : List Bool) (ts : List Token) :
    Walk (xs.length+1) (frame .restore ts acc xs []) (frame .next ts (xs.reverse++acc) [] []) := by
  induction xs generalizing acc with
  | nil=>exact before (restore_end ts acc) rfl
  | cons x xs ih=>
    simpa [List.append_assoc] using before (restore_one x ts acc xs) (ih (x::acc))

private theorem draining (xs out : List Bool) :
    Walk (xs.length+1) (frame .clean [] xs [] out) (haltList machine out) := by
  induction xs with
  | nil=>exact before (clean_end out) rfl
  | cons x xs ih=>exact before (clean_one x xs out) ih

private theorem indexing (bits xs : List Bool) :
    ∃ k,k≤steps bits xs ∧ Walk k (frame .next (bits.map Sum.inr) xs [] [])
        (haltList machine ((lookup bits xs).toList)) := by
  induction bits generalizing xs with
  | nil=>
    cases xs with
    | nil=>exact ⟨1,by decide,before empty_end rfl⟩
    | cons x xs=>exact ⟨xs.length+2,by simp [steps],before (hit_end x xs) (draining xs [x])⟩
  | cons b bs ih=>
    let ys:=retain (!b) xs
    obtain ⟨k,hk,tail⟩:=ih ys
    have sc:=scanning (!b) xs [] (bs.map Sum.inr)
    have rs:=restoring ys.reverse [] (bs.map Sum.inr)
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at sc rs
    let m:=k+(ys.length+1)+(xs.length+1)+1
    refine ⟨m,?_,?_⟩
    · dsimp [m,steps,ys] at *;omega
    · exact before (next_bit b (bs.map Sum.inr) xs) (seq sc (seq rs tail))

/-- The input carries x followed by the little-endian bits of the address, on disjoint tags.
A missing address returns the empty word. A present address returns its source bit. -/
theorem physical_lookup (x bits : List Bool) : Nonempty (TM2OutputsInTime machine
    (x.map Sum.inl++bits.map Sum.inr) (some ((x.reverse[numeric bits]?).toList))
    (4*x.length+5*bits.length+3)) := by
  let input:=x.map Sum.inl++bits.map Sum.inr
  have start:initList machine input=frame .load input [] [] []:=by
    unfold initList frame;congr 1;funext k;cases k <;>rfl
  have load:=loading x bits []
  simp only [List.append_nil] at load
  obtain ⟨k,hk,run⟩:=indexing bits x.reverse
  rw [lookup_value] at run
  have upper:=time_bound bits x.reverse
  simp only [List.length_reverse] at upper
  exact ⟨⟨⟨k+(x.length+1),start ▸ seq load run⟩,show k+(x.length+1)≤4*x.length+5*bits.length+3 by omega⟩⟩

end DyadicLookup
#print axioms DyadicLookup.physical_lookup

namespace DyadicLookup
open Turing

theorem numeric_binary (bits : List Bool) : numeric bits=(BitVec.ofBoolListLE bits).toNat := by
  induction bits with
  | nil=>rfl
  | cons a xs ih=>
    change a.toNat+2*numeric xs=(BitVec.concat (BitVec.ofBoolListLE xs) a).toNat
    rw [BitVec.toNat_concat,ih];omega

theorem physical_binary_address (x bits : List Bool) : Nonempty (TM2OutputsInTime machine
    (x.map Sum.inl++bits.map Sum.inr) (some ((x.reverse[(BitVec.ofBoolListLE bits).toNat]?).toList))
    (4*x.length+5*bits.length+3)) := by
  rw [←numeric_binary]
  exact physical_lookup x bits

end DyadicLookup

#print axioms DyadicLookup.physical_binary_address
