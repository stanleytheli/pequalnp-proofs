import FP3Joint
namespace StackTrace.Generated
open OneOpeningGame PhysicalSigma RowAddress

variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)

def word (n v : ℕ) := TimeChallenge.encode n v

noncomputable def tables (bound : ℕ→ℕ) (n : ℕ) : List (List (List Bool)) :=
  List.ofFn fun i : Fin (2^n)=>physicalSweep c.tm (input c (word n i.val))
    (timeWidth c bound n) (bitWidth c bound n)

private theorem input_roundtrip (x : List Bool) : word x.length (TimeChallenge.decode x)=x := by
  apply List.ext_getElem
  · simp [word,TimeChallenge.encode]
  · intro i hi hj
    change (List.ofFn fun k : Fin x.length=>(TimeChallenge.decode x).testBit k.val)[i]=x[i]
    simp only [List.getElem_ofFn,TimeChallenge.decode,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE]
    simp [List.getD,hj]

private theorem decode_lt (b : List Bool) : TimeChallenge.decode b<2^b.length :=
  (BitVec.ofBoolListLE b).isLt

theorem lookup (bound : ℕ→ℕ) (x : List Bool) (u : Fin (arity c bound x.length)→Bool) :
    let d:=timeWidth c bound x.length
    let e:=bitWidth c bound x.length
    let cube:=tables c bound x.length
    (((cube.getD (TimeChallenge.decode x) []).getD (first d e u) []).getD (second d e u) false)=table c bound x u := by
  let d:=timeWidth c bound x.length
  let e:=bitWidth c bound x.length
  have hi:=decode_lt x
  have ht:first d e u<2^d:=by
    simpa [first] using decode_lt (List.ofFn fun j : Fin d=>u (Fin.castAdd e j))
  have hj:second d e u<2^e:=by
    simpa [second] using decode_lt (List.ofFn fun j : Fin e=>u (Fin.natAdd d j))
  have get:(tables c bound x.length).getD (TimeChallenge.decode x) [] =
      physicalSweep c.tm (input c x) d e := by
    simp [tables,List.getD,hi,input_roundtrip,d,e]
  change ((((tables c bound x.length).getD (TimeChallenge.decode x) []).getD (first d e u) []).getD (second d e u) false)=_
  rw [get]
  exact physicalSweep_bit c.tm (input c x) d e _ _ ht hj

/-- Simulating each n-bit input once and emitting one complete packet per
chronological tick gives the jointly indexed table, including off-horizon addresses. -/
theorem joint_lookup (bound : ℕ→ℕ) (x : List Bool) (u : Fin (arity c bound x.length)→Bool) :
    let d:=timeWidth c bound x.length
    let e:=bitWidth c bound x.length
    let cube:=tables c bound x.length
    (((cube.getD (TimeChallenge.decode x) []).getD (first d e u) []).getD (second d e u) false)=
      joint c bound x.length (Fin.append x.get u) := by
  rw [joint_slice]
  exact lookup c bound x u

theorem dimensions (bound : ℕ→ℕ) (n : ℕ) :
    (tables c bound n).length=2^n ∧ ∀ page∈tables c bound n,
      page.length=2^(timeWidth c bound n) ∧ ∀ row∈page,row.length=2^(bitWidth c bound n) := by
  constructor
  · simp [tables]
  · intro p hp
    obtain ⟨i,eq⟩:=List.mem_ofFn.mp hp
    subst p
    exact physicalSweep_shape c.tm _ _ _

theorem bit_count (bound : ℕ→ℕ) (n : ℕ) :
    (((tables c bound n).flatMap id).flatMap id).length=2^(n+arity c bound n) := by
  let d:=timeWidth c bound n
  let e:=bitWidth c bound n
  obtain ⟨np,page⟩:=dimensions c bound n
  have flat (p : List (List Bool)) (hp:p∈tables c bound n) : (p.flatMap id).length=2^d*2^e:=by
    obtain ⟨rows,width⟩:=page p hp
    rw [List.length_flatMap]
    have arr:p.map (fun x=> (id x).length)=List.replicate p.length (2^e):=by
      apply List.eq_replicate_iff.mpr
      refine ⟨List.length_map _,fun x hx=>?_⟩
      obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx;exact width r hr
    rw [arr,List.sum_replicate_nat,rows]
  have counts:(tables c bound n).map (fun x=>(x.flatMap id).length)=
      List.replicate (tables c bound n).length (2^d*2^e):=by
    apply List.eq_replicate_iff.mpr
    refine ⟨List.length_map _,fun x hx=>?_⟩
    obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hx;exact flat p hp
  calc
    _ = ((tables c bound n).flatMap (fun p=>p.flatMap id)).length := by simp [Function.comp_def]
    _ = _ := by
      rw [List.length_flatMap,counts,List.sum_replicate_nat,np]
      change 2^n*(2^d*2^e)=2^(n+(d+e))
      rw [Nat.pow_add,Nat.pow_add]

end StackTrace.Generated

#print axioms StackTrace.Generated.joint_lookup
#print axioms StackTrace.Generated.bit_count
