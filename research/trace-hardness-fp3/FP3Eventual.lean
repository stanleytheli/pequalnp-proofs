import FP3Joint
import FP3Splice
namespace StackTrace.OneOpeningGame
open Turing PEqualNP.Library PhysicalSigma CircuitRows RowAddress RowAccess
variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)
private theorem word_alt_three (s : ℕ) (P : List Bool→Prop) :
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

private theorem wordAllChecks {K A Q : Type} [DecidableEq K] (M : Program K A Q) (start : Q)
    (T : ℕ) (accept : Q→(K→Option A)→Prop) (r : Trace K A Q)
    (authentic : ∀ i≤T,r i=canonical M start i) :
    accept (run M start T).state (fun k=>((run M start T).stackContents k).head?) →
    ∀ i : Fin (T+1),Packed.oneCheck M start T accept r i := by
  let d:=T.log2+1
  have fit:T<2^d:=by
    by_cases h:T=0
    · subst T;decide
    · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)
  let ch:=TimeChallenge.challenge d T (s:=d)
  have onto:Function.Surjective ch:=TimeChallenge.challenge_surjective d T d le_rfl fit
  intro h i
  obtain ⟨_,win⟩:=(Packed.commit_iff M start T d accept (fun _=>r) ch ⟨Packed.zeroWord _,authentic⟩ onto).mp h
  obtain ⟨b,hb⟩:=onto i
  exact hb ▸ win b

private theorem wordAccepting {K A Q : Type} [DecidableEq K] (M : Program K A Q) (start : Q)
    (T : ℕ) (accept : Q→(K→Option A)→Prop) (r : Trace K A Q)
    (win : ∀ i : Fin (T+1),Packed.oneCheck M start T accept r i) :
    accept (run M start T).state (fun k=>((run M start T).stackContents k).head?) := by
  have w:=win ⟨0,Nat.zero_lt_succ _⟩
  exact (observed_iff_trace M start T accept).mpr
    ⟨r,w.1,w.2.1,w.2.2.1,fun i hi=>(win ⟨i,Nat.lt_succ_of_lt hi⟩).2.2.2 hi⟩

theorem word_game_at (L : Language Bool) (hL:∀ x,x∈L↔f x=true)
    (s bound gates : ℕ→ℕ) (ht:∀ n,c.time n≤bound n)
    (addr:∀ n,arity c bound n+gates n≤2^(arity c bound n+1))
    (universalRoom:∀ n,let d:=timeWidth c bound n
      d+(4+2*(channels c.tm).length)*(1+d+(4+@Fintype.card c.tm.K c.tm.kFin)*d)+1≤s n)
    (responseRoom:∀ n,arity c bound n+budgetSize c bound gates n+1≤s n)
    (x : List Bool) (small:PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (gates x.length))
    : x∈L ↔ Alt 3 (s x.length) (fun w=>(x,w)∈relation c bound gates) := by
  classical
  let n:=x.length
  let d:=timeWidth c bound n
  let e:=bitWidth c bound n
  let T:=PhysicalSigma.T c bound n
  let F:=Binary.physical c.tm
  let M:=prog c x
  let start:=Atomic.initialControl c.tm
  let ks:=channels c.tm
  let ak:=fun t j=>ports (key c bound x t j)
  let W:=budgetSize c bound gates n
  let rate:=7*(arity c bound n+1+1)+23
  let H:=(4+@Fintype.card c.tm.K c.tm.kFin)*d
  have cap:capacity c.tm T<2^d:=(Nat.log2_lt (by unfold capacity;omega)).mp (Nat.lt_succ_self _)
  unfold capacity at cap
  have fit:T<2^d:=by omega
  have hpos:0<H:=Nat.mul_pos (by omega) (Nat.zero_lt_succ _)
  have idx:H≤2^e:=(show H<2^(H.log2+1) from (Nat.log2_lt (Nat.ne_of_gt hpos)).mp (Nat.lt_succ_self _)).le
  have room:d+e+W+1≤s n:=responseRoom n
  have physical:∀ a : Packed.Word (s n),∀ b : Packed.Word (s n),
      let sample:=Codec.challenge d H (4+2*ks.length) T b.val
      refuted ks F d M start T (accept c) (unpack a.val) ak W rate sample.1 sample.2 ↔
        ∃ z : Packed.Word (s n),(x,a.val++b.val++z.val)∈relation c bound gates := by
    intro a b
    let sample:=Codec.challenge d H (4+2*ks.length) T b.val
    have equivalence:=refuted_iff_response ks F d e M start T fit idx (accept c)
      (unpack a.val) ak W rate (s n) room sample.1 sample.2
    exact equivalence.trans (exists_congr fun z=>(relation_join c bound gates x a b z).symm)
  have semantics:=(hL x).trans (run_accept c bound ht x)
  rw [word_alt_three]
  constructor
  · intro mem
    have space:W+1≤s n:=by omega
    obtain ⟨a,hs⟩:=framed_circuit small (addr n) space
    let r:=decoded F d (fun t j=>answer (unpack a.val) (ak t j))
    have authentic (i : ℕ) (hi:i≤T) : r i=canonical M start i := by
      apply Binary.physical_row c.tm (input c x) i d (Nat.zero_lt_succ _)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      intro j hj
      exact (hs (key c bound x i j)).1.trans (table_key c bound x hi hj)
    have win:=wordAllChecks M start T (accept c) r authentic (semantics.mp mem)
    have avail (t j : ℕ) : ∃ w : List Bool,w.length≤W ∧ Nonempty (TM2OutputsInTime OwnedRadix.Code.queryVerifier
        (OwnedRadix.Code.Parameter.triple (unpack a.val) (ak t j++[answer (unpack a.val) (ak t j)]) w)
          (some [true]) (rate*w.length+19)) := by
      obtain ⟨hv,w,hw,hy⟩:=hs (key c bound x t j)
      exact ⟨w,hw,by simpa only [ak,hv] using hy⟩
    refine ⟨a,fun b=>(physical a b).mp ?_⟩
    let sample:=Codec.challenge d H (4+2*ks.length) T b.val
    exact universal_complete ks (allChannels c.tm) F d M start T fit (accept c) (unpack a.val) ak
      W rate avail sample.1 (win sample.1) sample.2
  · rintro ⟨a,win⟩
    apply semantics.mpr
    apply wordAccepting M start T (accept c) (decoded F d (fun t j=>answer (unpack a.val) (ak t j)))
    exact universal_sound ks (allChannels c.tm) F d M start T fit (accept c) (unpack a.val)
      ak W rate (s n) (universalRoom n) (fun b=>(physical a b).mpr (win b))

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.word_game_at

namespace StackTrace.OneOpeningGame
open PEqualNP.Library PhysicalSigma CircuitRows RowAddress

variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)

/-- Finitely many exceptional input lengths can have completely arbitrary
trace-circuit complexity. The finite-state override embeds their true language
answers in the finite control of a physical uniform verifier. -/
theorem speedup_of_eventual_joint (a C : ℕ) (hC:1≤C) (L : Language Bool) (hL:∀ x,x∈L↔f x=true)
    (clock:∀ n,c.time n≤originalTime a C n)
    (small:∃ N : ℕ,∀ n≥N,PEqualNP.MetaComplexity.HasCircuitSize (n+arity c (originalTime a C) n)
      (joint c (originalTime a C) n) (jointGates c a C n))
    (checker:∃ B : ℕ,DecidableInTime encodePair
      (relation c (originalTime a C) (fun n=>jointGates c a C n+2)) (fun n=>B*n+B)) :
    ∃ K : ℕ,1≤K ∧ L∈SigmaV 3 (fun n=>K*2^((5*a+4)*n)+K) := by
  let bound:=originalTime a C
  let k:=@Fintype.card c.tm.K c.tm.kFin
  let gates:=fun n=>jointGates c a C n+2
  let R:=relation c bound gates
  obtain ⟨D,dim⟩:=total_arity c a C
  obtain ⟨N,tail⟩:=small
  obtain ⟨K,resources⟩:=TraceBudget.BitOpening.projected_blocks a D k
  let s:=fun n=>(K+1)*2^((5*a+4)*n)+(K+1)
  have grow (n : ℕ):K*2^((5*a+4)*n)+K≤s n:=
    Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.le_succ _)
  have res (n : ℕ):=resources n (timeWidth c bound n) (bitWidth c bound n) (n+arity c bound n)
    (Nat.le_add_left _ _) (dim n)
  have len:(channels c.tm).length=k:=Finset.length_toList _
  let L₀ : Language Bool:={x | Alt 3 (s x.length) (fun w=>(x,w)∈R)}
  obtain ⟨B,check⟩:=checker
  have base:L₀∈SigmaV 3 s:=⟨R,B,check,fun _=>Iff.rfl⟩
  refine ⟨K+1,Nat.zero_lt_succ _,FiniteOverride.finite_changes L₀ L N 3 s ?_ base⟩
  intro x large
  have H:=Hardwire.specialize (tail x.length large) x.get
  have localBound:PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (gates x.length):=
    by simpa only [joint_slice] using H
  refine (word_game_at c L hL s bound gates clock (fun n=>joint_gate_address c a C n hC)
      (fun n=>?_) (fun n=>(res n).2.1.trans (grow n)) x localBound).symm
  simpa only [len] using (res n).1.trans (grow n)

def SmallJoint {f : List Bool→Bool} (a : ℕ) (c : PhysicalSigma.Decider f) (C n : ℕ) : Prop :=
  PEqualNP.MetaComplexity.HasCircuitSize (n+arity c (originalTime a C) n)
    (joint c (originalTime a C) n) (jointGates c a C n)

def FrontExists {f : List Bool→Bool} (a : ℕ) (c : PhysicalSigma.Decider f) (C : ℕ) : Prop :=
  ∃ B : ℕ,DecidableInTime encodePair
      (relation c (originalTime a C) (fun n=>jointGates c a C n+2)) (fun n=>B*n+B)

theorem fp3_of_eventual_joint (a : ℕ)
    (small:∀ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),1≤C →
      (∀ n,c.time n≤originalTime a C n) → ∃ N : ℕ,∀ n≥N,SmallJoint a c C n)
    (checker:∀ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),1≤C →
      (∀ n,c.time n≤originalTime a C n) → FrontExists a c C) :
    FP3 (5*a+4) (5*a+5) := by
  intro L mem
  obtain ⟨C,f,hL,c,time⟩:=mem
  have bound (n : ℕ):c.time n≤originalTime a (C+1) n:=by
    have t:=time n
    change c.time n≤C*2^((5*a+5)*n)+C at t
    exact t.trans (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.le_succ _))
  exact speedup_of_eventual_joint c a (C+1) (Nat.zero_lt_succ _) L hL bound
    (small f c _ (Nat.zero_lt_succ _) bound) (checker f c _ (Nat.zero_lt_succ _) bound)

/-- Failure of this fixed speedup, assuming the explicit local verifier can
be implemented for all machines, forces infinitely many hard jointly indexed
trace tables of one fixed deterministic machine. -/
theorem hard_trace_if_no_fp3 (a : ℕ) (failure:¬FP3 (5*a+4) (5*a+5))
    (checker:∀ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),1≤C →
      (∀ n,c.time n≤originalTime a C n) → FrontExists a c C) :
    ∃ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),1≤C ∧
      (∀ n,c.time n≤originalTime a C n) ∧ ∀ N : ℕ,∃ n≥N,¬SmallJoint a c C n := by
  classical
  by_contra! all
  apply failure
  apply fp3_of_eventual_joint a _ checker
  intro f c C hC time
  exact all f c C hC time

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.speedup_of_eventual_joint
#print axioms StackTrace.OneOpeningGame.fp3_of_eventual_joint
#print axioms StackTrace.OneOpeningGame.hard_trace_if_no_fp3
