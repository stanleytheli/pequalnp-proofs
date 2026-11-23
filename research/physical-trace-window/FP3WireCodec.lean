import FP3Window
namespace ColumnCheck.Wire
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Runtime ColumnCheck.Table
open scoped Classical

/-- Two header words, a source-symbol word, and one presence/address/field group per slot. -/
abbrev Tracks (r s : ℕ) := Fin 3 ⊕ (Fin r × (Fin 2 ⊕ Fin (4+s)))

noncomputable def pick {r s} (t : Tracks r s) : Pick (Fintype.card (Tracks r s)) :=
  fun c=>c ((Fintype.equivFin (Tracks r s)) t)

noncomputable def encode {r s} (d : ℕ) (a : Tracks r s→ℕ) : List (Col (Fintype.card (Tracks r s))) :=
  List.ofFn (fun j : Fin d=>fun p=>(a ((Fintype.equivFin (Tracks r s)).symm p)).testBit j.val)

theorem encode_len {r s} (d : ℕ) (a : Tracks r s→ℕ) : (encode d a).length=d:=by simp [encode]

theorem pick_encode {r s} (d : ℕ) (a : Tracks r s→ℕ) (t : Tracks r s) (fit:a t<2^d) :
    value (pick t) (encode d a)=a t := by
  have eq : (encode d a).map (pick t)=TimeChallenge.encode d (a t) := by
    apply List.ext_getElem
    · simp [encode_len,TimeChallenge.encode]
    · intro j hj hj'
      simp [encode,pick,TimeChallenge.encode]
  rw [value_binary,eq]
  exact TimeChallenge.decode_encode d (a t) fit

noncomputable def entry {r s : ℕ} (i : Fin r) : Slot (Fintype.card (Tracks r s)) s :=
  let field:=fun j : Fin (4+s)=>pick (Sum.inr (i,Sum.inr j) : Tracks r s)
  {active:=.const (pick (Sum.inr (i,Sum.inl 0))) 1,address:=pick (Sum.inr (i,Sum.inl 1)),
   row:=⟨field ⟨0,by omega⟩,field ⟨1,by omega⟩,field ⟨2,by omega⟩,field ⟨3,by omega⟩,fun j=>field ⟨j.val+4,by omega⟩⟩}

noncomputable def entries (r s : ℕ) : List (Slot (Fintype.card (Tracks r s)) s) := List.ofFn (entry (r:=r) (s:=s))

def words (d : ℕ) (head : Fin 3→ℕ) (v : Sample) {r s : ℕ} : Tracks r s→ℕ
  | .inl h=>head h
  | .inr (i,.inl u)=>if u=0 then (v[i.val]?).isSome.toNat else (v[i.val]?).getD (0,[]) |>.1
  | .inr (i,.inr j)=>Format.extract d (fun b=>((v[i.val]?).getD (0,[])).2.getD b false) j.val

theorem pack_bound (d : ℕ) (hd:0<d) (head : Fin 3→ℕ) (hh:∀ j,head j<2^d) (v : Sample)
    (addr:∀ p∈v,p.1<2^d) {r s : ℕ} (t : Tracks r s) : words d head v t<2^d := by
  rcases t with j|⟨i,u|j⟩
  · exact hh j
  · cases h:v[i.val]? with
    | none=>by_cases eq:u=0 <;>simp [words,eq,h]
    | some p=>
      have mem:p∈v:=List.mem_of_getElem? h
      by_cases eq:u=0
      · have pow:1<2^d:=by have := Nat.pow_le_pow_right (show 0<2 by decide) (show 1≤d by omega);omega
        simpa [words,eq,h] using pow
      · simpa [words,eq,h] using addr p mem
  · change (BitVec.ofBoolListLE (List.ofFn (fun b : Fin d=>_))).toNat<2^d
    simpa using (BitVec.ofBoolListLE (List.ofFn (fun b : Fin d=>
      ((v[i.val]?).getD (0,[])).2.getD (j.val*d+b.val) false))).isLt

theorem field_value (d : ℕ) {r s} (a : Tracks r s→ℕ) (fit:∀ t,a t<2^d) (i : Fin r) (j : Fin (4+s)) :
    (entry (s:=s) i).row.cols (encode d a) j.val=a (.inr (i,.inr j)) := by
  obtain ⟨j,hj⟩:=j
  match j with
  | 0 | 1 | 2 | 3=>apply pick_encode _ _ _ (fit _)
  | j+4=>simp only [Layout.cols,dif_pos (show j<s by omega)]
         apply pick_encode _ _ _ (fit _)

theorem bit_recover (d : ℕ) (hd:0<d) (bits : List Bool) (j : ℕ) :
    Format.flatten d (Format.extract d (fun b=>bits.getD b false)) j=bits.getD j false := by
  have mod:j%d<d:=Nat.mod_lt _ hd
  have idx:(j/d)*d+j%d=j:=by rw [Nat.mul_comm, Nat.div_add_mod]
  simp only [Format.flatten,Format.extract,TimeChallenge.decode,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
  simp [List.getD,mod,idx]

theorem row_recover {r s} (d : ℕ) (hd:0<d) (head : Fin 3→ℕ) (v : Sample)
    (fit:∀ t : Tracks r s,words d head v t<2^d) (i : Fin r) (p : ℕ×List Bool) (atI:v[i.val]?=some p)
    (width:p.2.length=(4+s)*d) :
    rawBits (entry i).row (encode d (words (r:=r) (s:=s) d head v))=p.2 := by
  apply List.ext_getElem
  · simp [rawBits,encode_len,width]
  · intro j left right
    have jb:j<(4+s)*d:=by simpa [rawBits,encode_len] using left
    have fj:j/d<4+s:=(Nat.div_lt_iff_lt_mul hd).mpr jb
    have field:=field_value d (words d head v) fit i ⟨j/d,fj⟩
    have idx:(j/d)*d+j%d=j:=by rw [Nat.mul_comm, Nat.div_add_mod]
    have mj:j%d<d:=Nat.mod_lt _ hd
    simp only [rawBits,List.getElem_ofFn,encode_len,Format.flatten]
    change ((entry i).row.cols (encode d (words d head v)) (j/d)).testBit (j%d)=p.2[j]
    change (entry i).row.cols (encode d (words d head v)) (j/d)=_ at field
    rw [field]
    change (Format.extract d (fun b=>((v[i.val]?).getD (0,[])).2.getD b false) (j/d)).testBit (j%d)=p.2[j]
    rw [atI]
    exact (bit_recover d hd p.2 j).trans (by simp [List.getD,right])

theorem sample_map {A : Type} {n s} (f : A→Option (ℕ×List Bool)) (xs : List A) (g : A→Slot n s) (l : List (Col n))
    (ok : ∀ i∈xs,(if (g i).active.holds l then some (value (g i).address l,rawBits (g i).row l) else none)=f i) :
    asSample l (xs.map g)=xs.filterMap f := by
  induction xs with
  | nil=>rfl
  | cons i xs ih=>
    have h:=ok i (by simp)
    have rest:=ih (fun j hj=>ok j (List.mem_cons_of_mem _ hj))
    cases fi:f i with
    | none=>by_cases a:(g i).active.holds l <;>simp [a,fi] at h <;>simp [asSample,a,fi,rest]
    | some b=>by_cases a:(g i).active.holds l <;>simp [a,fi] at h <;>simp [asSample,a,fi,rest,h]

theorem list_complete {A : Type} (v : List A) (r : ℕ) :
    (List.range r).filterMap (fun i=>v[i]?)=v.take r := by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [List.range_succ,List.filterMap_append,ih,List.take_succ];cases h:v[r]? <;>simp [List.filterMap,h]

end ColumnCheck.Wire

#print axioms ColumnCheck.Wire.row_recover
namespace ColumnCheck.Wire
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Table
open scoped Classical

theorem represent {r s} (d : ℕ) (hd:0<d) (head : Fin 3→ℕ) (hh:∀ j,head j<2^d) (v : Sample)
    (many:v.length≤r) (width:∀ p∈v,p.2.length=(4+s)*d) (addr:∀ p∈v,p.1<2^d) :
    asSample (encode d (words (r:=r) (s:=s) d head v)) (entries r s)=v := by
  let a:=words (r:=r) (s:=s) d head v
  have fit:=pack_bound d hd head hh v addr (r:=r) (s:=s)
  have ok (i : Fin r) : (if (entry (s:=s) i).active.holds (encode d a) then
      some (value (entry (s:=s) i).address (encode d a),rawBits (entry (s:=s) i).row (encode d a))
    else none)=v[i.val]? := by
    have act:value (pick (.inr (i,.inl 0) : Tracks r s)) (encode d a)=(v[i.val]?).isSome.toNat:=by
      rw [pick_encode d a _ (fit _)];simp [a,words]
    have ad:value (pick (.inr (i,.inl 1) : Tracks r s)) (encode d a)=((v[i.val]?).getD (0,[])).1:=by
      rw [pick_encode d a _ (fit _)];simp [a,words]
    cases h:v[i.val]? with
    | none=>simp [entry,Formula.holds,act,h]
    | some p=>
      have row:=row_recover d hd head v fit i p h (width p (List.mem_of_getElem? h))
      have yes:(entry (s:=s) i).active.holds (encode d a):=by
        change value (pick _) _=1
        rw [act,h];rfl
      rw [if_pos yes]
      apply congrArg some
      exact Prod.ext (by change value (pick _) _=p.1;rw [ad,h];rfl) row
  have use:=sample_map (fun i : Fin r=>v[i.val]?) (List.finRange r) (entry (s:=s)) (encode d a) (fun i _=>ok i)
  have enum:(List.finRange r).map Fin.val=List.range r:=by
    apply List.ext_getElem <;>simp
  have rhs:(List.finRange r).filterMap (fun i : Fin r=>v[i.val]?)=v:=by
    calc _=((List.finRange r).map Fin.val).filterMap (fun i=>v[i]?) := by rw [List.filterMap_map];rfl
         _=v:=by rw [enum,list_complete,List.take_of_length_le many]
  rw [rhs] at use
  simpa only [entries,List.finRange,List.map_ofFn,Function.comp_def,a] using use

def loadCode : Option Bool→ℕ
  | none=>0
  | some false=>1
  | some true=>2

noncomputable def mode {r s} {A : Type} (letter : Bool→A) : Tree (Fintype.card (Tracks r s)) (Option A) :=
  .node (.const (pick (.inl 2)) 1) (.leaf (some (letter false)))
    (.node (.const (pick (.inl 2)) 2) (.leaf (some (letter true))) (.leaf none))

theorem mode_value {r s} {A : Type} (letter : Bool→A) (d : ℕ) (a : Tracks r s→ℕ) (phase : Option Bool)
    (fit:∀ t,a t<2^d) (hdr:a (.inl 2)=loadCode phase) :
    (mode letter).eval (encode d a)=phase.map letter := by
  cases phase with
  | none=>simp [mode,Tree.eval,Formula.holds,pick_encode d a _ (fit _),hdr,loadCode]
  | some b=>cases b <;>simp [mode,Tree.eval,Formula.holds,pick_encode d a _ (fit _),hdr,loadCode]

noncomputable def headers (i T : ℕ) (phase : Option Bool) : Fin 3→ℕ
  | ⟨0,_⟩=>i | ⟨1,_⟩=>T | ⟨2,_⟩=>loadCode phase

theorem header_bound {i T d} (it:i≤T) (tf:T<2^d) (df:2<2^d) (phase : Option Bool) :
    ∀ j,headers i T phase j<2^d := by
  intro j
  fin_cases j
  · exact it.trans_lt tf
  · exact tf
  · cases phase with
    | none=>exact (show 0<2 by decide).trans df
    | some b=>cases b
              · exact (show 1<2 by decide).trans df
              · exact df

end ColumnCheck.Wire

#print axioms ColumnCheck.Wire.represent
namespace ColumnCheck.Wire
open Turing StackTrace StackTrace.Binary StackTrace.RowAccess ColumnCheck.Control ColumnCheck.Table
open scoped Classical

def matrix (n d : ℕ) (w : List Bool) : List (Col n) :=
  List.ofFn (fun j : Fin d=>fun i : Fin n=>w.getD (j.val*n+i.val) false)

theorem matrix_length (n d : ℕ) (w : List Bool) : (matrix n d w).length=d:=by simp [matrix]

theorem serialized_digit {n} (l : List (Col n)) (tail : List Bool) (j : Fin l.length) (i : Fin n) :
    (serialize l++tail).getD (j.val*n+i.val) false=l[j.val] i := by
  induction l with
  | nil=>exact Fin.elim0 j
  | cons a l ih=>
    refine Fin.cases ?_ (fun k=>?_) j
    · have idx:i.val<(List.ofFn a).length:=by simpa using i.isLt
      simp [serialize,List.append_assoc,List.getD,List.getElem?_append_left idx,idx]
      rfl
    · have ix:n≤(k.val+1)*n+i.val:=by rw [Nat.succ_mul];omega
      have sub:(k.val+1)*n+i.val-n=k.val*n+i.val:=by rw [Nat.succ_mul];omega
      change (List.ofFn a++serialize l++tail).getD ((k.val+1)*n+i.val) false=_
      rw [List.append_assoc]
      have ge:(List.ofFn a).length≤(k.val+1)*n+i.val:=by simpa using ix
      simpa [List.getD,List.getElem?_append_right ge,sub] using ih k

theorem matrix_roundtrip {n} (l : List (Col n)) (tail : List Bool) :
    matrix n l.length (serialize l++tail)=l := by
  apply List.ext_getElem
  · exact matrix_length .. 
  · intro j h hj
    funext i
    have pick:=List.getElem_ofFn (f:=fun k : Fin l.length=>fun t : Fin n=>
      (serialize l++tail).getD (k.val*n+t.val) false) (i:=j) h
    exact (congrFun pick i).trans (serialized_digit l tail ⟨j,hj⟩ i)

theorem pack_word {n} (l : List (Col n)) (z : ℕ) (fit:n*l.length≤z) :
    ∃ w : {w : List Bool // w.length=z},matrix n l.length w.val=l := by
  let tail:=List.replicate (z-n*l.length) false
  refine ⟨⟨serialize l++tail,?_⟩,matrix_roundtrip l tail⟩
  simp [tail,serialized_length,fit]

theorem represent_word {r s} (d : ℕ) (hd:0<d) (head : Fin 3→ℕ) (hh:∀ j,head j<2^d) (v : Sample)
    (many:v.length≤r) (width:∀ p∈v,p.2.length=(4+s)*d) (addr:∀ p∈v,p.1<2^d)
    (z : ℕ) (room:Fintype.card (Tracks r s)*d≤z) :
    ∃ w : {w : List Bool // w.length=z},
      let l:=matrix (Fintype.card (Tracks r s)) d w.val
      asSample l (entries r s)=v ∧ ∀ j:Fin 3,value (pick (.inl j)) l=head j := by
  let a:=words (r:=r) (s:=s) d head v
  let l:=encode d a
  obtain ⟨w,h⟩:=pack_word l z (by simpa [l,encode_len] using room)
  have len:l.length=d:=encode_len d a
  rw [len] at h
  refine ⟨w,?_⟩
  dsimp only
  rw [h]
  exact ⟨represent d hd head hh v many width addr,fun j=>pick_encode d a (.inl j) (hh j)⟩

end ColumnCheck.Wire

#print axioms ColumnCheck.Wire.represent_word
