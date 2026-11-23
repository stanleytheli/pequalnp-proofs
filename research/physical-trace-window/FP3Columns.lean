import FP3KernelR
import PEqualNP.Library.Machines.Transducer
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace ColumnCheck

abbrev Col (k : ℕ) := Fin k→Bool
abbrev Pick (k : ℕ) := Col k→Bool

def value {k : ℕ} (read : Pick k) : List (Col k)→ℕ
  | []=>0
  | a::rest=>(read a).toNat+2*value read rest

theorem value_binary {k : ℕ} (read : Pick k) (l : List (Col k)) :
    value read l=(BitVec.ofBoolListLE (l.map read)).toNat := by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    change (read a).toNat+2*value read l=(BitVec.concat (BitVec.ofBoolListLE (l.map read)) (read a)).toNat
    rw [BitVec.toNat_concat,ih];omega

structure Reader (A : Type) where
  S : Type
  [finite : Fintype S]
  start : S
  step : S→A→S
  answer : S→Bool

def Reader.run {A} (r : Reader A) (l : List A) := r.answer (l.foldl r.step r.start)

def combine {A} (r t : Reader A) (op : Bool→Bool→Bool) : Reader A :=
  let _:=r.finite
  let _:=t.finite
  { S:=r.S×t.S,start:=(r.start,t.start),step:=fun q a=>(r.step q.1 a,t.step q.2 a),
    answer:=fun q=>op (r.answer q.1) (t.answer q.2) }

theorem combine_run {A} (r t : Reader A) (op : Bool→Bool→Bool) (l : List A) :
    (combine r t op).run l=op (r.run l) (t.run l) := by
  have h (x : r.S) (y : t.S) : l.foldl (fun q a=>(r.step q.1 a,t.step q.2 a)) (x,y)=
      (l.foldl r.step x,l.foldl t.step y) := by
    induction l generalizing x y with
    | nil=>rfl
    | cons a l ih=>exact ih _ _
  exact congrArg (fun q=>op (r.answer q.1) (t.answer q.2)) (h _ _)

def negated {A} (r : Reader A) : Reader A := {r with answer:=fun q=> !(r.answer q)}

def equal {k} (x y : Pick k) : Reader (Col k) where
  S:=Bool
  start:=true
  step:=fun q a=>q && (x a==y a)
  answer:=id

theorem equal_run {k} (x y : Pick k) (l : List (Col k)) :
    (equal x y).run l=true ↔ value x l=value y l := by
  have h (b : Bool) : l.foldl (fun (q : Bool) a=>q && (x a==y a)) b=true ↔ b=true ∧ value x l=value y l := by
    induction l generalizing b with
    | nil=>simp [value]
    | cons a rest ih=>
      rw [List.foldl_cons,ih]
      cases hx:x a <;>cases hy:y a <;>cases b <;>simp [equal,value,hx,hy] <;> omega
  exact (h true).trans (by simp)

def less {k} (x y : Pick k) : Reader (Col k) where
  S:=Bool
  start:=false
  step:=fun q a=>if x a=y a then q else y a
  answer:=id

theorem less_run {k} (x y : Pick k) (l : List (Col k)) :
    (less x y).run l=true ↔ value x l<value y l := by
  have h (b : Bool) : l.foldl (fun (q : Bool) a=>if x a=y a then q else y a) b=true ↔
      value x l<value y l ∨ (value x l=value y l ∧ b=true) := by
    induction l generalizing b with
    | nil=>simp [value]
    | cons a rest ih=>
      rw [List.foldl_cons,ih]
      cases hx:x a <;>cases hy:y a <;>cases b <;>simp [less,value,hx,hy] <;>omega
  exact (h false).trans (by simp)

def addStep {k} (x y z : Pick k) : Option Bool→Col k→Option Bool
  | none,_=>none
  | some carry,a=>
    let sum:=(x a).toNat+(y a).toNat+carry.toNat
    if sum%2=(z a).toNat then some (decide (2≤sum)) else none

def added {k} (x y z : Pick k) (carry : Bool) : Reader (Col k) where
  S:=Option Bool
  start:=some carry
  step:=addStep x y z
  answer:=fun q=>q==some false

theorem added_run {k} (x y z : Pick k) (carry : Bool) (l : List (Col k)) :
    (added x y z carry).run l=true ↔ value x l+value y l+carry.toNat=value z l := by
  have dead (ls : List (Col k)) : ls.foldl (addStep x y z) none = none := by
    induction ls with
    | nil=>rfl
    | cons a ls ih=>exact ih
  have h (c : Bool) : l.foldl (addStep x y z) (some c)=some false ↔ value x l+value y l+c.toNat=value z l := by
    induction l generalizing c with
    | nil=>cases c <;>simp [value]
    | cons a l ih=>
      simp only [List.foldl_cons,value]
      cases hx:x a <;>cases hy:y a <;>cases hz:z a <;>cases c <;>
        simp [addStep,hx,hy,hz,ih,dead] <;>omega
  simpa only [Reader.run,added,beq_iff_eq] using h carry

def kStep {k} (x : Pick k) (c : ℕ) : Option (Fin (c+1))→Col k→Option (Fin (c+1))
  | none,_=>none
  | some r,a=> if r.val%2=(x a).toNat then some ⟨r.val/2,by have:=r.isLt;omega⟩ else none

def constant {k} (x : Pick k) (c : ℕ) : Reader (Col k) where
  S:=Option (Fin (c+1))
  start:=some ⟨c,Nat.lt_succ_self _⟩
  step:=kStep x c
  answer:=fun q=>q==some ⟨0,Nat.zero_lt_succ _⟩

theorem constant_run {k} (x : Pick k) (c : ℕ) (l : List (Col k)) :
    (constant x c).run l=true ↔ value x l=c := by
  let zero : Fin (c+1):=⟨0,Nat.zero_lt_succ _⟩
  have dead (ls : List (Col k)) : ls.foldl (kStep x c) none=none := by
    induction ls with | nil=>rfl | cons a ls ih=>exact ih
  have h (r : Fin (c+1)) : l.foldl (kStep x c) (some r)=some zero ↔ value x l=r.val := by
    induction l generalizing r with
    | nil=>
      change some r=some zero ↔ 0=r.val
      rw [Option.some.injEq,Fin.ext_iff]
      exact eq_comm
    | cons a l ih=>
      simp only [List.foldl_cons,value,kStep]
      split
      · rw [ih]
        change value x l=r.val/2 ↔ (x a).toNat+2*value x l=r.val
        omega
      · rw [dead];cases hx:x a <;>simp_all <;>omega
  simpa only [Reader.run,constant,beq_iff_eq,zero] using h ⟨c,Nat.lt_succ_self _⟩

inductive Formula (k : ℕ) where
  | eq (x y : Pick k)
  | lt (x y : Pick k)
  | add (x y z : Pick k) (carry : Bool)
  | const (x : Pick k) (v : ℕ)
  | neg (r : Formula k)
  | conj (r s : Formula k)
  | disj (r s : Formula k)

def Formula.holds {k} (l : List (Col k)) : Formula k→Prop
  | .eq x y=>value x l=value y l
  | .lt x y=>value x l<value y l
  | .add x y z c=>value x l+value y l+c.toNat=value z l
  | .const x v=>value x l=v
  | .neg r=>¬r.holds l
  | .conj r s=>r.holds l ∧ s.holds l
  | .disj r s=>r.holds l ∨ s.holds l

def Formula.reader {k} : Formula k→Reader (Col k)
  | .eq x y=>equal x y
  | .lt x y=>less x y
  | .add x y z c=>added x y z c
  | .const x v=>constant x v
  | .neg r=>negated r.reader
  | .conj r s=>combine r.reader s.reader Bool.and
  | .disj r s=>combine r.reader s.reader Bool.or

theorem Formula.correct {k} (F : Formula k) (l : List (Col k)) : F.reader.run l=true ↔ F.holds l := by
  induction F with
  | eq x y=>exact equal_run x y l
  | lt x y=>exact less_run x y l
  | add x y z c=>exact added_run x y z c l
  | const x v=>exact constant_run x v l
  | neg r ih=>change (!r.reader.run l)=true ↔ ¬r.holds l;simp [←ih]
  | conj r s ir is=>simp [reader,holds,combine_run,ir,is]
  | disj r s ir is=>simp [reader,holds,combine_run,ir,is]

end ColumnCheck

#print axioms ColumnCheck.Formula.correct

namespace ColumnCheck
abbrev Short (k : ℕ) := {xs : List Bool // xs.length<k}

private def address (k : ℕ) (w : Short k) : Fin k × (Fin k→Bool) :=
  (⟨w.val.length,w.property⟩,fun j=>w.val.getD j.val false)

noncomputable instance shortFinite (k : ℕ) : Fintype (Short k) :=
  Fintype.ofInjective (address k) (by
    intro x y h
    apply Subtype.ext
    apply List.ext_getElem
    · exact congrArg (fun v : Fin k × (Fin k→Bool)=>v.1.val) h
    · intro j hx hy
      have eq:=congrFun (congrArg Prod.snd h) ⟨j,hx.trans x.property⟩
      simpa [address,List.getD,hx,hy] using eq)

def emptyBuf {k : ℕ} (hk:0<k) : Short k := ⟨[],hk⟩

def inBuf {k : ℕ} (pre : List Bool) (h:pre.length<k) : Short k :=
  ⟨pre.reverse,by simpa using h⟩

def serialStep {k} (r : Reader (Col k)) (hk:0<k) (s : r.S × Short k) (b : Bool) : r.S × Short k :=
  let raw:=b::s.2.val
  if h:raw.length<k then (s.1,⟨raw,h⟩) else
    (r.step s.1 (fun i=>raw.reverse.getD i.val false),emptyBuf hk)

noncomputable def serial {k} (r : Reader (Col k)) (hk:0<k) : Reader Bool :=
  let _:=r.finite
  { S:=r.S × Short k,start:=(r.start,emptyBuf hk),step:=serialStep r hk,
    answer:=fun s=>s.2.val.isEmpty && r.answer s.1 }

theorem block {k} (r : Reader (Col k)) (hk:0<k) (q : r.S) (pre rest : List Bool)
    (small:pre.length<k) (full:pre.length+rest.length=k) :
    rest.foldl (serialStep r hk) (q,inBuf pre small)=
      (r.step q (fun i=>(pre++rest).getD i.val false),emptyBuf hk) := by
  induction rest generalizing pre with
  | nil=>simp at full;omega
  | cons b bs ih=>
    rw [List.foldl_cons]
    by_cases done:bs=[]
    · subst bs
      have finish:¬(b::pre.reverse).length<k:=by simp at full ⊢;omega
      have ended:¬pre.length+1<k:=by simpa using finish
      simp [serialStep,inBuf,ended,List.append_assoc]
    · have nonempty:0<bs.length:=List.length_pos_iff.mpr done
      have room:(pre++[b]).length<k:=by simp at full ⊢;omega
      have step:serialStep r hk (q,inBuf pre small) b=(q,inBuf (pre++[b]) room):=by
        have less:(b::pre.reverse).length<k:=by simp at room ⊢;omega
        have more:pre.length+1<k:=by simpa using less
        simp [serialStep,inBuf,more]
      rw [step,ih (pre++[b]) room (by simp at full ⊢;omega)]
      simp [List.append_assoc]

def serialize {k} (rows : List (Col k)) : List Bool := rows.flatMap List.ofFn

theorem serial_rows {k} (r : Reader (Col k)) (hk:0<k) (l : List (Col k)) :
    (serial r hk).run (serialize l)=r.run l := by
  have groups (q : r.S) : (serialize l).foldl (serialStep r hk) (q,emptyBuf hk)=
      (l.foldl r.step q,emptyBuf hk) := by
    induction l generalizing q with
    | nil=>rfl
    | cons col cs ih=>
      have step:=block r hk q [] (List.ofFn col) hk (by simp)
      have key:(fun i : Fin k=>([]++List.ofFn col).getD i.val false)=col:=by
        funext i;simp [List.getD,i.isLt]
      rw [key] at step
      simp only [serialize,List.flatMap_cons,List.foldl_append,List.foldl_cons]
      change _=_
      rw [show emptyBuf hk=inBuf [] hk from rfl,step]
      exact ih _
  change ((List.foldl (serialStep r hk) (r.start,emptyBuf hk) (serialize l)).2.val.isEmpty &&
    r.answer (List.foldl (serialStep r hk) (r.start,emptyBuf hk) (serialize l)).1)=_
  rw [groups]
  rfl

theorem serialized_length {k} (l : List (Col k)) : (serialize l).length=k*l.length := by
  induction l with
  | nil=>simp [serialize]
  | cons a l ih=>simp [serialize,List.length_flatMap,Nat.mul_add] at ih ⊢;omega

end ColumnCheck

#print axioms ColumnCheck.serial_rows

namespace ColumnCheck
open Turing PEqualNP.Library.Machines

def transition {A} (r : Reader A) (q : r.S) (a : A) : r.S × Option Bool × Option Bool :=
  (r.step q a,none,none)

def terminal {A} (r : Reader A) (q : r.S) := some (r.answer q)

noncomputable def machine {A} [Fintype A] (r : Reader A) : FinTM2 :=
  let _:=r.finite
  trM (transition r) (terminal r) r.start (some false)

theorem interpreter {A} (r : Reader A) (l : List A) (q : r.S) :
    fstRun2 (transition r) (terminal r) q l=[r.answer (l.foldl r.step q)] := by
  induction l generalizing q with | nil=>rfl | cons a l ih=>exact ih _

theorem machine_run {A} [Fintype A] (r : Reader A) (l : List A) :
    Nonempty (TM2OutputsInTime (machine r) l (some [r.run l]) (2*l.length+3)) := by
  let _:=r.finite
  have h:=trM_run (transition r) (terminal r) r.start (some false) (by simp) l
  have full:=h.trans (congrArg (fun o : List Bool=>some (haltList (machine r) o)) (interpreter r l r.start))
  exact ⟨⟨⟨_,full⟩,by change l.length+1+1+(l.length+1)≤2*l.length+3;omega⟩⟩

/-- One fixed binary-input physical machine checks any fixed formula in the
synchronized natural-number fields. Its clock is linear on every bit stream. -/
theorem physical {k} (F : Formula k) (hk:0<k) (l : List (Col k)) :
    ∃ b : Bool,(b=true ↔ F.holds l) ∧ Nonempty (TM2OutputsInTime (machine (serial F.reader hk))
      (serialize l) (some [b]) (2*(serialize l).length+3)) := by
  let b:=(serial F.reader hk).run (serialize l)
  exact ⟨b,(congrArg (fun v=>v=true) (serial_rows F.reader hk l)) ▸ F.correct l,machine_run _ _⟩

end ColumnCheck

#print axioms ColumnCheck.physical
