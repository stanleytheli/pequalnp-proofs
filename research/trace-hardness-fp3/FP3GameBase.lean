import FP3Bases
namespace StackTrace.CircuitRows
open PEqualNP.Library Turing
open OwnedRadix OwnedRadix.Code

noncomputable def answer (c xs : List Bool) : Bool := (Classical.choose (commitment_function c)) xs

theorem answer_spec {c xs : List Bool} {b : Bool} (h : Answered c xs b) : answer c xs=b :=
  (Classical.choose_spec (commitment_function c)) xs b h

def ports {m : ℕ} (x : Fin m → Bool) : List Bool := [false,true]++List.ofFn x

def openSize (m gates d : ℕ) := (6*(d+1)+9)*(2+m+gates)+2*(d+1)+3

/-- One fixed first block carries a circuit commitment and supplies short, physically
checkable openings for all inputs. The last delimiter costs exactly one bit. -/
theorem framed_circuit {m gates d s : ℕ} {f : (Fin m → Bool) → Bool}
    (C : PEqualNP.MetaComplexity.HasCircuitSize m f gates) (width : m+gates≤2^d)
    (room : openSize m gates d+1≤s) :
    ∃ a : Packed.Word s, ∀ x : Fin m → Bool,
      answer (unpack a.val) (ports x)=f x ∧ ∃ w : List Bool,
        w.length≤openSize m gates d ∧ Nonempty (TM2OutputsInTime queryVerifier
          (Parameter.triple (unpack a.val) (ports x++[f x]) w) (some [true]) ((7*(d+1)+23)*w.length+19)) := by
  obtain ⟨c,clen,hr,_⟩ := OwnedRadix.Compiler.realize_official C d width
  have pad : c.length+1≤s := by unfold openSize at room;omega
  refine ⟨pack c pad,fun x=>?_⟩
  rw [unpack_pack]
  obtain ⟨w,hlen,hyes⟩ := hr x
  exact ⟨answer_spec ⟨w,_,hyes⟩,w,hlen,hyes⟩

/-- A fixed decoder interprets every possible first block. Even an adversarial commitment
can only open a claimed physical bit to its single decoded value. -/
noncomputable def bits {s m : ℕ → ℕ}
    (query : (x : List Bool) → ℕ → ℕ → (Fin (m x.length) → Bool)) : PhysicalSigma.Oracle s :=
  fun x a i j => answer (unpack a.val) (ports (query x i j))

theorem opened_bit {s m : ℕ → ℕ}
    (query : (x : List Bool) → ℕ → ℕ → (Fin (m x.length) → Bool))
    (x : List Bool) (a : Packed.Word (s x.length)) (i j : ℕ) (b : Bool)
    (h : Answered (unpack a.val) (ports (query x i j)) b) : bits query x a i j=b :=
  answer_spec h

/-- The honest availability condition contains actual finite-machine accepting executions
on all the named inputs. No such premise is required for malicious first blocks. -/
def Available {s m : ℕ → ℕ} (gates d : ℕ → ℕ)
    (x : List Bool) (a : Packed.Word (s x.length)) : Prop :=
  ∀ key : Fin (m x.length) → Bool, ∃ w : List Bool, w.length≤openSize (m x.length) (gates x.length) (d x.length) ∧
    Nonempty (TM2OutputsInTime queryVerifier
      (Parameter.triple (unpack a.val) ((ports key)++[answer (unpack a.val) (ports key)]) w) (some [true])
      ((7*(d x.length+1)+23)*w.length+19))

private theorem altThree (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ a : Packed.Word s, ∀ b : Packed.Word s, ∃ z : Packed.Word s, P (a.val++b.val++z.val) := by
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

/-- A relation may reject every malformed commitment. Completeness is required only on
the same honest first block whose actual short openings are available. -/
theorem sigmaV_of_circuit_rows {f : List Bool → Bool} (c : PhysicalSigma.Decider f)
    (L : Language Bool) (hL : ∀ x, x∈L ↔ f x=true)
    (s bound m gates d : ℕ→ℕ) (ht : ∀ n, c.time n≤bound n)
    (timeRoom : ∀ n, PhysicalSigma.width c.tm (PhysicalSigma.T c bound n)≤s n)
    (addrRoom : ∀ n, m n+gates n≤2^(d n)) (padRoom : ∀ n, openSize (m n) (gates n) (d n)+1≤s n)
    (table : (x : List Bool) → (Fin (m x.length) → Bool) → Bool)
    (query : (x : List Bool) → ℕ → ℕ → (Fin (m x.length) → Bool))
    (small : ∀ x, PEqualNP.MetaComplexity.HasCircuitSize (m x.length) (table x) (gates x.length))
    (correctRows : ∀ (x : List Bool) i, i≤PhysicalSigma.T c bound x.length →
      ∀ j, j<(4+@Fintype.card c.tm.K c.tm.kFin)*PhysicalSigma.width c.tm (PhysicalSigma.T c bound x.length) →
        table x (query x i j)=PhysicalSigma.genuineBit c x (PhysicalSigma.T c bound x.length) i j)
    (R : Set (List Bool × List Bool)) (B : ℕ)
    (checker : DecidableInTime encodePair R (fun l=>B*l+B))
    (sound : ∀ x (a b z : Packed.Word (s x.length)), (x,a.val++b.val++z.val)∈R →
      PhysicalSigma.test c s bound (bits query) x a b)
    (complete : ∀ x (a : Packed.Word (s x.length)), Available (m:=m) gates d x a →
      ∀ b, PhysicalSigma.test c s bound (bits query) x a b →
        ∃ z : Packed.Word (s x.length), (x,a.val++b.val++z.val)∈R) : L∈SigmaV 3 s := by
  classical
  let rd := PhysicalSigma.decodeTrace c s bound (bits query)
  let chall := PhysicalSigma.timeQuery c s bound
  have authentic (x : List Bool) : ∃ a : Packed.Word (s x.length), Available (m:=m) gates d x a ∧
      ∀ i≤PhysicalSigma.T c bound x.length, rd x a i=canonical (PhysicalSigma.prog c x) (Atomic.initialControl c.tm) i := by
    obtain ⟨a,ha⟩ := framed_circuit (small x) (addrRoom _) (padRoom _)
    refine ⟨a,fun key=>?_,fun i hi=>?_⟩
    · obtain ⟨h,w,hw,hyes⟩:=ha key
      exact ⟨w,hw,by rwa [h]⟩
    · let W:=PhysicalSigma.width c.tm (PhysicalSigma.T c bound x.length)
      have big : PhysicalSigma.capacity c.tm (PhysicalSigma.T c bound x.length)<2^W :=
        (Nat.log2_lt (by unfold PhysicalSigma.capacity;omega)).mp (Nat.lt_succ_self _)
      unfold PhysicalSigma.capacity at big
      apply Binary.physical_row c.tm (PhysicalSigma.input c x) i W (Nat.zero_lt_succ _)
        (by omega) (by omega) (by omega) (by omega) (by omega) (bits query x a i)
      intro j hj
      exact (ha (query x i j)).1.trans (correctRows x i hi j hj)
  have times (x : List Bool) : Function.Surjective (chall x) := by
    let T:=PhysicalSigma.T c bound x.length
    have big : PhysicalSigma.capacity c.tm T < 2^(PhysicalSigma.width c.tm T) :=
      (Nat.log2_lt (by unfold PhysicalSigma.capacity;omega)).mp (Nat.lt_succ_self _)
    unfold PhysicalSigma.capacity at big
    have fit : T < 2^(PhysicalSigma.width c.tm T) := by omega
    exact TimeChallenge.challenge_surjective _ _ _ (timeRoom _) fit
  refine ⟨R,B,checker,fun x=>?_⟩
  obtain ⟨a,available,genuine⟩:=authentic x
  let M:=PhysicalSigma.prog c x
  let start:=Atomic.initialControl c.tm
  let T:=PhysicalSigma.T c bound x.length
  have semantics := (hL x).trans (PhysicalSigma.run_accept c bound ht x)
  rw [altThree]
  constructor
  · intro h
    have hchecks := (Packed.commit_iff M start T (s x.length) (PhysicalSigma.accept c)
      (fun _=>rd x a) (chall x) ⟨a,genuine⟩ (times x)).mp (semantics.mp h)
    obtain ⟨_,all⟩:=hchecks
    exact ⟨a,fun b=>complete x a available b (all b)⟩
  · rintro ⟨alleged,hall⟩
    apply semantics.mpr
    apply (Packed.commit_iff M start T (s x.length) (PhysicalSigma.accept c) (rd x) (chall x) ⟨a,genuine⟩ (times x)).mpr
    refine ⟨alleged,fun b=>?_⟩
    obtain ⟨z,hz⟩:=hall b
    exact sound x alleged b z hz

end StackTrace.CircuitRows

#print axioms StackTrace.CircuitRows.framed_circuit
#print axioms StackTrace.CircuitRows.opened_bit
#print axioms StackTrace.CircuitRows.sigmaV_of_circuit_rows

namespace StackTrace.RowAddress

def enc (d e i j : ℕ) : Fin (d+e)→Bool :=
  Fin.addCases (fun k : Fin d=>i.testBit k.val) (fun k : Fin e=>j.testBit k.val)

def first (d e : ℕ) (key : Fin (d+e)→Bool) : ℕ :=
  TimeChallenge.decode (List.ofFn fun k : Fin d=>key (Fin.castAdd e k))

def second (d e : ℕ) (key : Fin (d+e)→Bool) : ℕ :=
  TimeChallenge.decode (List.ofFn fun k : Fin e=>key (Fin.natAdd d k))

theorem first_enc (d e i j : ℕ) (hi : i<2^d) : first d e (enc d e i j)=i := by
  simpa [first,enc,TimeChallenge.encode] using TimeChallenge.decode_encode d i hi

theorem second_enc (d e i j : ℕ) (hj : j<2^e) : second d e (enc d e i j)=j := by
  simpa [second,enc,TimeChallenge.encode] using TimeChallenge.decode_encode e j hj

/-- The time width grows by a constant over qn; encoding the field index adds
at most another n bits and a machine-dependent constant. -/
theorem widths (q A B H : ℕ) (hq : 0<q) : ∃ C : ℕ, ∀ n t : ℕ, t≤n+A*2^(q*n)+B →
    let d:=t.log2+1
    let e:=(H*d).log2+1
    d+e≤(q+1)*n+C := by
  let D:=A+B+3
  let E:=H*(q+D)+2
  refine ⟨D+E,fun n t ht=>?_⟩
  let d:=t.log2+1
  have nq : n≤q*n:=by nlinarith
  have hn : n+1≤2^(q*n):=(Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) nq)
  have powpos : 1≤2^(q*n):=Nat.one_le_two_pow
  have Hsmall : t<2^(q*n+D) := by
    rw [Nat.pow_add]
    have gap : A+B+2≤2^D :=(Nat.lt_two_pow_self (n:=D)).le.trans' (by dsimp [D];omega)
    have bbound : B≤B*2^(q*n):=by nlinarith
    have strict : t < (A+B+2)*2^(q*n):=by nlinarith
    exact strict.trans_le (by rw [Nat.mul_comm];exact Nat.mul_le_mul_left _ gap)
  have dw : d≤q*n+D:=by
    by_cases zero:t=0
    · subst t;dsimp [d,D];omega
    · exact (Nat.log2_lt zero).mpr Hsmall
  have index : H*d<2^(n+E) := by
    rw [Nat.pow_add]
    have l : d≤(q+D)*(n+1):=by nlinarith
    have hbound : H*d≤H*(q+D)*(n+1):=by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ l
    have nroom : n+1≤2^n:=Nat.lt_two_pow_self
    have eroom : H*(q+D)<2^E:=(Nat.lt_two_pow_self (n:=E)).trans' (by dsimp [E];omega)
    calc
      H*d ≤ H*(q+D)*(n+1) := hbound
      _ ≤ H*(q+D)*2^n := Nat.mul_le_mul_left _ nroom
      _ < 2^E*2^n := Nat.mul_lt_mul_of_pos_right eroom (by positivity)
      _ = 2^n*2^E := Nat.mul_comm _ _
  have ew : (H*d).log2+1≤n+E:=by
    by_cases zero:H*d=0
    · rw [zero];simp;dsimp [E];omega
    · exact (Nat.log2_lt zero).mpr index
  change d+((H*d).log2+1)≤(q+1)*n+(D+E)
  rw [Nat.add_mul,Nat.one_mul];omega

end StackTrace.RowAddress

#print axioms StackTrace.RowAddress.widths

namespace StackTrace.RowAddress
open Turing PEqualNP.Library PhysicalSigma CircuitRows

variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)

noncomputable def timeWidth (bound : ℕ→ℕ) (n : ℕ) := width c.tm (T c bound n)
noncomputable def bitWidth (bound : ℕ→ℕ) (n : ℕ) := ((4+@Fintype.card c.tm.K c.tm.kFin)*timeWidth c bound n).log2+1
noncomputable def arity (bound : ℕ→ℕ) (n : ℕ) := timeWidth c bound n+bitWidth c bound n

noncomputable def key (bound : ℕ→ℕ) (x : List Bool) (i j : ℕ) : Fin (arity c bound x.length)→Bool :=
  enc (timeWidth c bound x.length) (bitWidth c bound x.length) i j

/-- The exact per-input Boolean function whose short circuit would suffice.
Out-of-range coordinates are assigned by the same global physical trace convention. -/
noncomputable def table (bound : ℕ→ℕ) (x : List Bool) (u : Fin (arity c bound x.length)→Bool) : Bool :=
  let d:=timeWidth c bound x.length
  let e:=bitWidth c bound x.length
  genuineBit c x (T c bound x.length) (first d e u) (second d e u)

theorem table_key (bound : ℕ→ℕ) (x : List Bool) {i j : ℕ} (hi : i≤T c bound x.length)
    (hj : j<(4+@Fintype.card c.tm.K c.tm.kFin)*timeWidth c bound x.length) :
    table c bound x (key c bound x i j)=genuineBit c x (T c bound x.length) i j := by
  have cap : capacity c.tm (T c bound x.length)<2^(timeWidth c bound x.length) :=
    (Nat.log2_lt (by unfold capacity;omega)).mp (Nat.lt_succ_self _)
  have ei : i<2^(timeWidth c bound x.length):=by unfold capacity at cap;omega
  have ej : j<2^(bitWidth c bound x.length):=by
    let H:=(4+@Fintype.card c.tm.K c.tm.kFin)*timeWidth c bound x.length
    have e : H<2^(H.log2+1):=(Nat.log2_lt (by dsimp [H];omega)).mp (Nat.lt_succ_self _)
    exact hj.trans e
  exact congrArg₂ (genuineBit c x (T c bound x.length)) (first_enc _ _ _ _ ei) (second_enc _ _ _ _ ej)

/-- The only circuit size hypothesis concerns the named, binary-addressed physical row
table. The machine for the whole local challenge is still a separate explicit premise. -/
theorem sigmaV_of_short_row_tables (L : Language Bool) (hL : ∀ x,x∈L↔f x=true)
    (s bound gates : ℕ→ℕ) (ht : ∀ n,c.time n≤bound n)
    (timeRoom : ∀ n,timeWidth c bound n≤s n)
    (addrRoom : ∀ n,arity c bound n+gates n≤2^(arity c bound n+1))
    (padRoom : ∀ n,openSize (arity c bound n) (gates n) (arity c bound n+1)+1≤s n)
    (small : ∀ x,PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (gates x.length))
    (R : Set (List Bool × List Bool)) (B : ℕ) (checker : DecidableInTime encodePair R (fun l=>B*l+B))
    (sound : ∀ x (a b z : Packed.Word (s x.length)),(x,a.val++b.val++z.val)∈R →
      test c s bound (bits (key c bound)) x a b)
    (complete : ∀ x (a : Packed.Word (s x.length)),
      Available (m:=arity c bound) gates (fun n=>arity c bound n+1) x a → ∀ b,
      test c s bound (bits (key c bound)) x a b → ∃ z : Packed.Word (s x.length),(x,a.val++b.val++z.val)∈R) :
    L∈SigmaV 3 s :=
  sigmaV_of_circuit_rows c L hL s bound (arity c bound) gates (fun n=>arity c bound n+1) ht timeRoom addrRoom padRoom
    (table c bound) (key c bound) small (fun x _ hi _ hj=>table_key c bound x hi hj) R B checker sound complete

end StackTrace.RowAddress

#print axioms StackTrace.RowAddress.sigmaV_of_short_row_tables

namespace StackTrace.RowAccess

variable {K A Q : Type} [DecidableEq K]

/-- The four always-readable rows. The successor is clipped at the final time. -/
def anchors (T i : ℕ) : List ℕ := [0,T,i,min (i+1) T]

def links (ks : List K) (row : Row K A Q) : List ℕ := ks.filterMap row.top

/-- The pointer queries depend only on two rows in the first round. -/
def footprint (ks : List K) (r : Trace K A Q) (T i : ℕ) : List ℕ :=
  anchors T i ++ links ks (r T) ++ links ks (r i)

theorem count (ks : List K) (r : Trace K A Q) (T i : ℕ) :
    (footprint ks r T i).length≤4+2*ks.length := by
  have hT:=List.length_filterMap_le (f:=(r T).top) (l:=ks)
  have hi:=List.length_filterMap_le (f:=(r i).top) (l:=ks)
  simp [footprint,anchors,links] at *
  omega

theorem second_round (ks : List K) {r u : Trace K A Q} {T i : ℕ}
    (hT : r T=u T) (hi : r i=u i) : footprint ks r T i=footprint ks u T i := by
  simp only [footprint,hT,hi]

private theorem deref {r u : Trace K A Q} {row : Row K A Q} {ks : List K}
    (all : ∀ k : K, k∈ks) (agree : ∀ j∈links ks row, r j=u j) (k : K) :
    node r k (row.top k)=node u k (row.top k) := by
  cases hv : row.top k with
  | none=>rfl
  | some j=>
    have mem : j∈links ks row:=List.mem_filterMap.mpr ⟨k,all k,hv⟩
    simp only [node,agree j mem]

/-- Agreement on the two-round footprint suffices for the actual local trace predicate,
including pointer sanity, terminal output and all stack heads. -/
theorem check_congr (ks : List K) (all : ∀ k : K,k∈ks)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (r u : Trace K A Q) (i : Fin (T+1))
    (agree : ∀ j∈footprint ks r T i.val, r j=u j) :
    Packed.oneCheck M start T accept r i ↔ Packed.oneCheck M start T accept u i := by
  have hz:=agree 0 (by simp [footprint,anchors])
  have ht:=agree T (by simp [footprint,anchors])
  have hi:=agree i.val (by simp [footprint,anchors])
  have term (k : K) : node r k ((u T).top k)=node u k ((u T).top k) := by
    rw [←ht];apply deref all (fun j hj=>agree j (by simp [footprint,hj]))
  have cur (k : K) : node r k ((u i.val).top k)=node u k ((u i.val).top k) := by
    rw [←hi];apply deref all (fun j hj=>agree j (by simp [footprint,hj]))
  have ptr : pointerAdvance r i.val=pointerAdvance u i.val := by
    unfold pointerAdvance
    simp only [hi,cur]
  have step (early : i.val<T) : Meets r M i.val ↔ Meets u M i.val := by
    have hn:=agree (i.val+1) (by simp [footprint,anchors,Nat.min_eq_left early])
    simp only [Meets,hi,hn,cur,ptr]
  unfold Packed.oneCheck
  simp only [hz,ht,term]
  exact and_congr_right' (and_congr_right' (and_congr_right' (forall_congr' step)))

/-- The authentic schedule stays in bounds, even on the last universal challenge. -/
theorem canonical_in_range (ks : List K) (M : Program K A Q) (start : Q) (T : ℕ)
    (i : Fin (T+1)) : ∀ j∈footprint ks (canonical M start) T i.val, j≤T := by
  have old {t j : ℕ} (mem : j∈links ks (canonical M start t)) : j<t := by
    obtain ⟨k,_,he⟩:=List.mem_filterMap.mp mem
    have h:rank ((canonical M start t).top k)<t+1:=(canonical_meets M start t).1 k
    simpa [he,rank] using h
  intro j hj
  have ile:=i.isLt
  simp only [footprint,anchors,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with (((rfl|rfl|rfl|rfl)|ht)|hi)
  · omega
  · rfl
  · omega
  · exact Nat.min_le_right _ _
  · exact (old ht).le
  · have :=old hi;omega

end StackTrace.RowAccess

#print axioms StackTrace.RowAccess.count
#print axioms StackTrace.RowAccess.check_congr
#print axioms StackTrace.RowAccess.canonical_in_range

namespace StackTrace.RowAccess
open Binary

abbrev Sample := List (ℕ × List Bool)

def slices {B : ℕ} (times : List ℕ) (bits : ℕ→ℕ→Bool) : Sample :=
  times.map fun t=>(t,List.ofFn fun j : Fin B=>bits t j.val)

def rowAt (t : ℕ) : Sample→List Bool
  | []=>[]
  | (s,row)::rest=>if t=s then row else rowAt t rest

def sampled (v : Sample) (t j : ℕ) : Bool := (rowAt t v).getD j false

private theorem slice_found {B : ℕ} (ts : List ℕ) (bits : ℕ→ℕ→Bool) {t : ℕ} (ht : t∈ts) :
    rowAt t (slices (B:=B) ts bits)=List.ofFn (fun j : Fin B=>bits t j.val) := by
  induction ts with
  | nil=>simp at ht
  | cons s ts ih=>
    by_cases h:t=s
    · subst s;simp [slices,rowAt]
    · simpa [slices,rowAt,h] using ih ((List.mem_cons.mp ht).resolve_left h)

private theorem slice_bit {B : ℕ} (ts : List ℕ) (bits : ℕ→ℕ→Bool) {t : ℕ} (ht : t∈ts)
    {j : ℕ} (hj : j<B) : sampled (slices (B:=B) ts bits) t j=bits t j := by
  simp [sampled,slice_found ts bits ht,List.getD,hj]

variable {K A Q : Type} [DecidableEq K] {s : ℕ}

def decoded (F : Format K A Q s) (d : ℕ) (bits : ℕ→ℕ→Bool) : Trace K A Q :=
  fun t=>F.restore (Format.extract d (bits t))

theorem decoded_ext (F : Format K A Q s) (d : ℕ) (x y : ℕ→ℕ→Bool) (t : ℕ)
    (h : ∀ j<(4+s)*d,x t j=y t j) : decoded F d x t=decoded F d y t := by
  apply F.restore_ext
  intro k hk
  apply congrArg TimeChallenge.decode
  apply congrArg List.ofFn
  funext j
  apply h
  calc
    k*d+j.val < k*d+d:=Nat.add_lt_add_left j.isLt _
    _=(k+1)*d:=(Nat.succ_mul _ _).symm
    _≤(4+s)*d:=Nat.mul_le_mul_right d hk

/-- A concrete finite certificate for one challenge. The row addresses in the
reply must coincide with the addresses computed from the reply itself. -/
def viewCheck (ks : List K) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (i : Fin (T+1)) (v : Sample) : Prop :=
  (∀ entry∈v,entry.2.length=(4+s)*d) ∧
  v.map Prod.fst=footprint ks (decoded F d (sampled v)) T i.val ∧
  Packed.oneCheck M start T accept (decoded F d (sampled v)) i

/-- A challenge succeeds exactly when a finite two-round reply passes its local
test and every listed bit agrees with the common oracle. -/
theorem finite_view (ks : List K) (all : ∀ k : K,k∈ks) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (i : Fin (T+1)) (bits : ℕ→ℕ→Bool) :
    Packed.oneCheck M start T accept (decoded F d bits) i ↔
      ∃ v : Sample, v.length≤4+2*ks.length ∧ viewCheck ks F d M start T accept i v ∧
        ∀ t∈v.map Prod.fst,∀ j<(4+s)*d, sampled v t j=bits t j := by
  let r:=decoded F d bits
  let want:=footprint ks r T i.val
  let B:=(4+s)*d
  constructor
  · intro yes
    let v:=slices (B:=B) want bits
    have keys : v.map Prod.fst=want:=by simp [v,slices,List.map_map,Function.comp_def]
    have same {t : ℕ} (ht : t∈want) : decoded F d (sampled v) t=r t :=
      decoded_ext F d _ _ t (fun _ hj=>slice_bit want bits ht hj)
    have atT : T∈want:=by simp [want,footprint,anchors]
    have atI : i.val∈want:=by simp [want,footprint,anchors]
    have stamp : footprint ks (decoded F d (sampled v)) T i.val=want:=second_round ks (same atT) (same atI)
    refine ⟨v,?_,⟨?_,keys.trans stamp.symm,?_⟩,?_⟩
    · simpa [v,slices,want] using count ks r T i.val
    · intro e he;obtain ⟨t,_,rfl⟩:=List.mem_map.mp he;exact List.length_ofFn
    · apply (check_congr ks all M start T accept _ r i ?_).mpr yes
      intro t ht;exact same (by rwa [stamp] at ht)
    · intro t ht j hj;exact slice_bit want bits (keys ▸ ht) hj
  · rintro ⟨v,_,⟨_,keys,pass⟩,honest⟩
    apply (check_congr ks all M start T accept _ _ i ?_).mp pass
    intro t ht
    exact decoded_ext F d _ _ t (honest t (keys.symm ▸ ht))

end StackTrace.RowAccess

#print axioms StackTrace.RowAccess.finite_view

namespace StackTrace.RowAccess
open Binary

variable {K A Q : Type} [DecidableEq K] {s : ℕ}

def counterView (ks : List K) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (i : Fin (T+1)) (v : Sample) : Prop :=
  (∀ e∈v,e.2.length=(4+s)*d) ∧
  v.map Prod.fst=footprint ks (decoded F d (sampled v)) T i.val ∧
  ¬Packed.oneCheck M start T accept (decoded F d (sampled v)) i

/-- Every decoded pointer, including a malicious one, fits the time field.
The property concerns all bit oracles and requires no trace validity. -/
theorem arbitrary_link_lt (F : Format K A Q s) (d : ℕ) (bits : ℕ→ℕ→Bool)
    {t j : ℕ} (ks : List K) (h : j∈links ks (decoded F d bits t)) : j<2^d := by
  obtain ⟨k,_,pointed⟩:=List.mem_filterMap.mp h
  let col:=(F.indexStack k).val+4
  let row:=Format.extract d (bits t) col
  have cap : row<2^d := by
    unfold row Format.extract TimeChallenge.decode
    have bound:=(BitVec.ofBoolListLE (List.ofFn (fun v : Fin d=>bits t (col*d+v.val)))).isLt
    simpa using bound
  change Format.unrank row=some j at pointed
  cases hrow:row with
  | zero=>simp [hrow,Format.unrank] at pointed
  | succ m=>
    have eq:m=j:=Option.some.inj (by simpa [hrow,Format.unrank] using pointed)
    omega

theorem arbitrary_footprint_lt (F : Format K A Q s) (d : ℕ) (bits : ℕ→ℕ→Bool)
    (T : ℕ) (fit : T<2^d) (i : Fin (T+1)) (ks : List K) {j : ℕ}
    (mem : j∈footprint ks (decoded F d bits) T i.val) : j<2^d := by
  have interval:=i.isLt
  simp only [footprint,anchors,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with (((rfl|rfl|rfl|rfl)|h)|h)
  · omega
  · exact fit
  · omega
  · exact (Nat.min_le_right _ _).trans_lt fit
  · exact arbitrary_link_lt F d bits ks h
  · exact arbitrary_link_lt F d bits ks h

/-- A passing global local test refutes any well-formed alleged failure by a
single bit discrepancy. An actual global failure admits an unrefutable short
reply whose row addresses all fit d bits, including for malicious commitments. -/
theorem single_bit_refutations (ks : List K) (all : ∀ k : K,k∈ks) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (fit : T<2^d) (accept : Q→(K→Option A)→Prop)
    (i : Fin (T+1)) (bits : ℕ→ℕ→Bool) :
    Packed.oneCheck M start T accept (decoded F d bits) i ↔
      ∀ v : Sample, v.length≤4+2*ks.length → (∀ t∈v.map Prod.fst,t<2^d) →
        counterView ks F d M start T accept i v →
        ∃ t∈v.map Prod.fst,∃ j<(4+s)*d,sampled v t j≠bits t j := by
  classical
  let r:=decoded F d bits
  constructor
  · intro pass v _ _ bad
    obtain ⟨_,keys,no⟩:=bad
    by_contra! agree
    apply no
    apply (check_congr ks all M start T accept _ r i ?_).mpr pass
    intro t ht
    exact decoded_ext F d _ _ t (agree t (keys.symm ▸ ht))
  · intro refute
    by_contra lost
    let want:=footprint ks r T i.val
    let v:=slices (B:=(4+s)*d) want bits
    have keys : v.map Prod.fst=want:=by simp [v,slices,List.map_map,Function.comp_def]
    have same {t : ℕ} (ht : t∈want) : decoded F d (sampled v) t=r t :=
      decoded_ext F d _ _ t (fun _ hj=>slice_bit want bits ht hj)
    have atT : T∈want:=by simp [want,footprint,anchors]
    have atI : i.val∈want:=by simp [want,footprint,anchors]
    have stamp : footprint ks (decoded F d (sampled v)) T i.val=want:=second_round ks (same atT) (same atI)
    have valid : counterView ks F d M start T accept i v := by
      refine ⟨?_,keys.trans stamp.symm,fun pass=>lost ?_⟩
      · intro e he;obtain ⟨t,_,rfl⟩:=List.mem_map.mp he;exact List.length_ofFn
      · apply (check_congr ks all M start T accept _ r i ?_).mp pass
        intro t ht;exact same (by rwa [stamp] at ht)
    obtain ⟨t,ht,j,hj,diff⟩:=refute v (by simpa [v,slices,want] using count ks r T i.val)
      (fun t ht=>arbitrary_footprint_lt F d bits T fit i ks (show t∈want by rwa [←keys])) valid
    exact diff (slice_bit want bits (keys ▸ ht) hj)

end StackTrace.RowAccess

#print axioms StackTrace.RowAccess.arbitrary_footprint_lt
#print axioms StackTrace.RowAccess.single_bit_refutations

namespace StackTrace.RowAccess.Codec

abbrev Word (n : ℕ) := {w : List Bool // w.length=n}

def rows (d B : ℕ) : ℕ→List Bool→Sample
  | 0,_=>[]
  | _+1,[]=>[]
  | _+1,false::_=>[]
  | r+1,true::tail=>
    let addr:=tail.take d
    let rest:=tail.drop d
    (TimeChallenge.decode addr,rest.take B)::rows d B r (rest.drop B)

def payload (d : ℕ) : Sample→List Bool
  | []=>[]
  | (i,bs)::rest=>true::(TimeChallenge.encode d i++bs++payload d rest)

private theorem split_row (r : ℕ) (addr bs tail : List Bool) :
    rows addr.length bs.length (r+1) (true::(addr++(bs++tail)))=
      (TimeChallenge.decode addr,bs)::rows addr.length bs.length r tail := by
  simp [rows,List.take_left,List.drop_left]

theorem rows_payload (d B r : ℕ) (v : Sample) (room:v.length≤r)
    (width:∀ e∈v,e.2.length=B) (fit:∀ e∈v,e.1<2^d) (tail : List Bool) :
    rows d B r (payload d v++false::tail)=v := by
  induction v generalizing r with
  | nil=>cases r <;>rfl
  | cons entry rest ih=>
    obtain ⟨t,bs⟩:=entry
    cases r with
    | zero=>simp at room
    | succ r=>
      let addr:=TimeChallenge.encode d t
      have al:addr.length=d:=by simp [addr,TimeChallenge.encode]
      have wk:bs.length=B:=width (t,bs) (by simp)
      have h:=split_row r addr bs (payload d rest++false::tail)
      rw [al,wk] at h
      have sub:=ih r (by simpa using room) (fun e he=>width e (by simp [he]))
        (fun e he=>fit e (by simp [he]))
      have dec:TimeChallenge.decode addr=t:=TimeChallenge.decode_encode d t (fit (t,bs) (by simp))
      simpa only [payload,List.cons_append,List.append_assoc,addr,dec,sub] using h

theorem payload_length (d B : ℕ) (v : Sample) (width:∀ e∈v,e.2.length=B) :
    (payload d v).length=v.length*(1+d+B) := by
  induction v with
  | nil=>simp [payload]
  | cons e v ih=>
    obtain ⟨t,bs⟩:=e
    have hw:bs.length=B:=width (t,bs) (by simp)
    have h:=ih (fun e he=>width e (by simp [he]))
    simp only [payload,List.length_cons,List.length_append,TimeChallenge.encode,List.length_ofFn,
      hw,h,Nat.succ_mul]
    omega

def challenge (d B r T : ℕ) (w : List Bool) : Fin (T+1) × Sample :=
  let t:=TimeChallenge.decode (w.take d)
  let i : Fin (T+1):=if h:t<T+1 then ⟨t,h⟩ else ⟨0,Nat.zero_lt_succ _⟩
  (i,rows d B r (w.drop d))

/-- A universal block needs one d-bit time and at most r fixed slots. Each slot
contains an enabled flag, another d-bit time address and B row bits. A final
zero terminates the slots, after which arbitrary padding is ignored. -/
theorem represent (d B r T s : ℕ) (timeFit:T<2^d) (room:d+r*(1+d+B)+1≤s)
    (i : Fin (T+1)) (v : Sample) (count:v.length≤r)
    (width:∀ e∈v,e.2.length=B) (fit:∀ e∈v,e.1<2^d) :
    ∃ w : Word s, challenge d B r T w.val=(i,v) := by
  let addr:=TimeChallenge.encode d i.val
  let body:=payload d v
  have la:addr.length=d:=by simp [addr,TimeChallenge.encode]
  have lb:body.length=v.length*(1+d+B):=payload_length d B v width
  have capacity:addr.length+body.length+1≤s:=by
    calc
      addr.length+body.length+1=d+v.length*(1+d+B)+1:=by rw [la,lb]
      _≤d+r*(1+d+B)+1:=by gcongr
      _≤s:=room
  let tail:=List.replicate (s-(addr.length+body.length+1)) false
  let z:=addr++(body++false::tail)
  have zlen:z.length=s:=by simp [z,tail];omega
  have take:z.take d=addr:=by rw [←la];exact List.take_left
  have drop:z.drop d=body++false::tail:=by rw [←la];exact List.drop_left
  have dec:TimeChallenge.decode addr=i.val:=TimeChallenge.decode_encode d i.val (by have:=i.isLt;omega)
  have rd:=rows_payload d B r v count width fit tail
  exact ⟨⟨z,zlen⟩,by simp only [challenge,take,drop,dec,i.isLt,dif_pos,body,rd]⟩

end StackTrace.RowAccess.Codec

#print axioms StackTrace.RowAccess.Codec.represent

namespace StackTrace.RowAccess
open Binary Turing OwnedRadix OwnedRadix.Code

variable {K A Q : Type} [DecidableEq K] {s : ℕ}

def refuted (ks : List K) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (c : List Bool) (key : ℕ→ℕ→List Bool) (W rate : ℕ) (i : Fin (T+1)) (v : Sample) : Prop :=
  ¬counterView ks F d M start T accept i v ∨
    ∃ t∈v.map Prod.fst,∃ j<(4+s)*d,∃ w : List Bool,w.length≤W ∧
      Nonempty (TM2OutputsInTime queryVerifier
        (Parameter.triple c (key t j++[!sampled v t j]) w) (some [true]) (rate*w.length+19))

/-- If the prover can refute every proposed complete local failure, the committed
interpretation passes all genuine times. This holds for all binary commitments. -/
theorem universal_sound (ks : List K) (all : ∀ k : K,k∈ks) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (fit:T<2^d) (accept : Q→(K→Option A)→Prop)
    (c : List Bool) (key : ℕ→ℕ→List Bool) (W rate z : ℕ)
    (room:d+(4+2*ks.length)*(1+d+(4+s)*d)+1≤z)
    (win : ∀ b : Codec.Word z,let sample:=Codec.challenge d ((4+s)*d) (4+2*ks.length) T b.val
      refuted ks F d M start T accept c key W rate sample.1 sample.2) :
    ∀ i : Fin (T+1),Packed.oneCheck M start T accept
      (decoded F d (fun t j=>CircuitRows.answer c (key t j))) i := by
  intro i
  apply (single_bit_refutations ks all F d M start T fit accept i _).mpr
  intro v count bound invalid
  have vfit (e : ℕ × List Bool) (he:e∈v) : e.1<2^d:=bound _ (List.mem_map_of_mem he)
  obtain ⟨b,dec⟩:=Codec.represent d ((4+s)*d) (4+2*ks.length) T z fit room i v count invalid.1 vfit
  have h:=win b
  simp only [dec] at h
  rcases h with dismiss | accusation
  · exact (dismiss invalid).elim
  · obtain ⟨t,ht,j,hj,w,_,yes⟩:=accusation
    have value:=CircuitRows.answer_spec (c:=c) (xs:=key t j) (b:=!sampled v t j) ⟨w,_,yes⟩
    refine ⟨t,ht,j,hj,?_⟩
    rw [value]
    cases sampled v t j <;>decide

/-- On an honest commitment, an alleged failing sample can be dismissed or refuted
with one physical circuit opening, independently of the number of stack heads. -/
theorem universal_complete (ks : List K) (all : ∀ k : K,k∈ks) (F : Format K A Q s) (d : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (fit:T<2^d) (accept : Q→(K→Option A)→Prop)
    (c : List Bool) (key : ℕ→ℕ→List Bool) (W rate : ℕ)
    (available : ∀ t j,∃ w : List Bool,w.length≤W ∧
      Nonempty (TM2OutputsInTime queryVerifier
        (Parameter.triple c (key t j++[CircuitRows.answer c (key t j)]) w) (some [true]) (rate*w.length+19)))
    (i : Fin (T+1)) (pass : Packed.oneCheck M start T accept
      (decoded F d (fun t j=>CircuitRows.answer c (key t j))) i) (v : Sample) :
    refuted ks F d M start T accept c key W rate i v := by
  classical
  by_cases bad : counterView ks F d M start T accept i v
  · right
    have keys:=bad.2.1
    have vcount:v.length≤4+2*ks.length:=by
      have h:=count ks (decoded F d (sampled v)) T i.val
      rwa [←keys,List.length_map] at h
    have vfit (t : ℕ) (ht:t∈v.map Prod.fst) : t<2^d:=
      arbitrary_footprint_lt F d (sampled v) T fit i ks (keys ▸ ht)
    obtain ⟨t,ht,j,hj,diff⟩:=(single_bit_refutations ks all F d M start T fit accept i _).mp pass v vcount vfit bad
    have eq : CircuitRows.answer c (key t j)=!sampled v t j := by
      cases h:sampled v t j <;>cases y:CircuitRows.answer c (key t j) <;>simp_all
    refine ⟨t,ht,j,hj,?_⟩
    simpa only [eq] using available t j
  · exact Or.inl bad

end StackTrace.RowAccess

#print axioms StackTrace.RowAccess.universal_sound
#print axioms StackTrace.RowAccess.universal_complete
