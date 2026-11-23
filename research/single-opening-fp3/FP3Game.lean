import FP3GameBase
namespace StackTrace.RowAccess
open Binary Turing OwnedRadix OwnedRadix.Code

variable {K A Q : Type} [DecidableEq K] {s : ℕ}

theorem take_prefix (a b : List Bool) (n : ℕ) (h:a.length=n) : (a++b).take n=a := by
  subst n;exact List.take_left

theorem drop_prefix (a b : List Bool) (n : ℕ) (h:a.length=n) : (a++b).drop n=b := by
  subst n;exact List.drop_left

def responseFields (d e : ℕ) (z : List Bool) : ℕ × ℕ × List Bool :=
  (TimeChallenge.decode (z.take d),TimeChallenge.decode ((z.drop d).take e),
   CircuitRows.unpack ((z.drop d).drop e))

theorem responseFields_pack (d e s W t j : ℕ) (w : List Bool) (ht:t<2^d) (hj:j<2^e)
    (hw:w.length≤W) (room:d+e+W+1≤s) :
    ∃ z : Packed.Word s,responseFields d e z.val=(t,j,w) := by
  let a:=TimeChallenge.encode d t
  let b:=TimeChallenge.encode e j
  have al:a.length=d:=by simp [a,TimeChallenge.encode]
  have bl:b.length=e:=by simp [b,TimeChallenge.encode]
  let p:=CircuitRows.pack (s:=s-(d+e)) w (by omega)
  let raw:=a++(b++p.val)
  have len:raw.length=s:=by simp only [raw,List.length_append,al,bl,p.property];omega
  have take:raw.take d=a:=take_prefix a (b++p.val) d al
  have drop:raw.drop d=b++p.val:=drop_prefix a (b++p.val) d al
  have take2:(b++p.val).take e=b:=take_prefix b p.val e bl
  have drop2:(b++p.val).drop e=p.val:=drop_prefix b p.val e bl
  exact ⟨⟨raw,len⟩,by simp only [responseFields,take,drop,take2,drop2,a,b,
    TimeChallenge.decode_encode d t ht,TimeChallenge.decode_encode e j hj,p,CircuitRows.unpack_pack]⟩

/-- The last fixed-length block specifies a disputed coordinate and contains one opening. -/
def response (ks : List K) (F : Format K A Q s) (d e : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (accept : Q→(K→Option A)→Prop)
    (c : List Bool) (key : ℕ→ℕ→List Bool) (W rate : ℕ) (i : Fin (T+1)) (v : Sample) (z : List Bool) : Prop :=
  ¬counterView ks F d M start T accept i v ∨
    let (t,j,w):=responseFields d e z
    t∈v.map Prod.fst ∧ j<(4+s)*d ∧ w.length≤W ∧
      Nonempty (TM2OutputsInTime queryVerifier
        (Parameter.triple c (key t j++[!sampled v t j]) w) (some [true]) (rate*w.length+19))

theorem refuted_iff_response (ks : List K) (F : Format K A Q s) (d e : ℕ)
    (M : Program K A Q) (start : Q) (T : ℕ) (fit:T<2^d) (bitFit:(4+s)*d≤2^e)
    (accept : Q→(K→Option A)→Prop) (c : List Bool) (key : ℕ→ℕ→List Bool) (W rate b : ℕ)
    (room:d+e+W+1≤b) (i : Fin (T+1)) (v : Sample) :
    refuted ks F d M start T accept c key W rate i v ↔
      ∃ z : Packed.Word b,response ks F d e M start T accept c key W rate i v z.val := by
  classical
  constructor
  · intro h
    by_cases fail:counterView ks F d M start T accept i v
    · obtain ⟨t,ht,j,hj,w,hw,yes⟩:=h.resolve_left (fun no=>no fail)
      have tfit:t<2^d:=arbitrary_footprint_lt F d (sampled v) T fit i ks (fail.2.1 ▸ ht)
      obtain ⟨z,decode⟩:=responseFields_pack d e b W t j w tfit (hj.trans_le bitFit) hw room
      exact ⟨z,Or.inr (by simpa only [decode] using And.intro ht ⟨hj,hw,yes⟩)⟩
    · exact ⟨Packed.zeroWord b,Or.inl fail⟩
  · rintro ⟨z,invalid|h⟩
    · exact Or.inl invalid
    · obtain ⟨t,j,w,eq⟩:=(show ∃ t j w,responseFields d e z.val=(t,j,w) by
        obtain ⟨t,j,w⟩:=responseFields d e z.val;exact ⟨_,_,_,rfl⟩)
      rw [eq] at h
      exact Or.inr ⟨t,h.1,j,h.2.1,w,h.2.2⟩

end StackTrace.RowAccess

#print axioms StackTrace.RowAccess.refuted_iff_response

namespace StackTrace.OneOpeningGame

open Turing PEqualNP.Library PhysicalSigma CircuitRows RowAddress RowAccess

noncomputable def channels (tm : FinTM2) : List tm.K := tm.kFin.elems.toList

theorem allChannels (tm : FinTM2) (k : tm.K) : k∈channels tm := by
  simp [channels,tm.kFin.complete k]

def thirds (w : List Bool) : List Bool × List Bool × List Bool :=
  let n:=w.length/3
  (w.take n,(w.drop n).take n,(w.drop n).drop n)

theorem thirds_join {s : ℕ} (a b z : Packed.Word s) :
    thirds (a.val++b.val++z.val)=(a.val,b.val,z.val) := by
  have len:(a.val++b.val++z.val).length/3=s:=by simp [a.property,b.property,z.property];omega
  have t:(a.val++(b.val++z.val)).take s=a.val:=take_prefix a.val (b.val++z.val) s a.property
  have u:(a.val++(b.val++z.val)).drop s=b.val++z.val:=drop_prefix a.val (b.val++z.val) s a.property
  have v:(b.val++z.val).take s=b.val:=take_prefix b.val z.val s b.property
  have w:(b.val++z.val).drop s=z.val:=drop_prefix b.val z.val s b.property
  unfold thirds
  rw [len]
  simp only [List.append_assoc,t,u,v,w]

variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)

noncomputable def budgetSize (bound gates : ℕ→ℕ) (n : ℕ) :=
  openSize (arity c bound n) (gates n) (arity c bound n+1)

noncomputable def front (bound gates : ℕ→ℕ) (x a b z : List Bool) : Prop :=
  let d:=timeWidth c bound x.length
  let k:=@Fintype.card c.tm.K c.tm.kFin
  let sample:=Codec.challenge d ((4+k)*d) (4+2*(channels c.tm).length) (T c bound x.length) b
  response (channels c.tm) (Binary.physical c.tm) d (bitWidth c bound x.length)
    (prog c x) (Atomic.initialControl c.tm) (T c bound x.length) (accept c) (unpack a)
    (fun t j=>ports (key c bound x t j)) (budgetSize c bound gates x.length)
    (7*(arity c bound x.length+1+1)+23) sample.1 sample.2 z

/-- One fixed relation parses three equal-length words directly from the input.
Each successful disputed bit is checked by the explicit physical query machine. -/
noncomputable def relation (bound gates : ℕ→ℕ) : Set (List Bool × List Bool) :=
  {p | let (a,b,z):=thirds p.2;front c bound gates p.1 a b z}

theorem relation_join (bound gates : ℕ→ℕ) (x : List Bool) {s : ℕ} (a b z : Packed.Word s) :
    (x,a.val++b.val++z.val)∈relation c bound gates ↔ front c bound gates x a.val b.val z.val := by
  change (let (u,v,w):=thirds (a.val++b.val++z.val);front c bound gates x u v w) ↔ _
  rw [thirds_join]

private theorem alt_three (s : ℕ) (P : List Bool→Prop) :
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

private theorem allChecks {K A Q : Type} [DecidableEq K] (M : Program K A Q) (start : Q)
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

private theorem accepting_of_all {K A Q : Type} [DecidableEq K] (M : Program K A Q) (start : Q)
    (T : ℕ) (accept : Q→(K→Option A)→Prop) (r : Trace K A Q)
    (win : ∀ i : Fin (T+1),Packed.oneCheck M start T accept r i) :
    accept (run M start T).state (fun k=>((run M start T).stackContents k).head?) := by
  have w:=win ⟨0,Nat.zero_lt_succ _⟩
  exact (observed_iff_trace M start T accept).mpr
    ⟨r,w.1,w.2.1,w.2.2.1,fun i hi=>(win ⟨i,Nat.lt_succ_of_lt hi⟩).2.2.2 hi⟩

/-- It suffices to save the exponent in circuits for one named physical
trace table and to implement the single named uniform relation in linear time.
The universal and last existential blocks are ordinary fixed-length binary words. -/
theorem word_game (L : Language Bool) (hL:∀ x,x∈L↔f x=true)
    (s bound gates : ℕ→ℕ) (ht:∀ n,c.time n≤bound n)
    (addr:∀ n,arity c bound n+gates n≤2^(arity c bound n+1))
    (universalRoom:∀ n,let d:=timeWidth c bound n
      d+(4+2*(channels c.tm).length)*(1+d+(4+@Fintype.card c.tm.K c.tm.kFin)*d)+1≤s n)
    (responseRoom:∀ n,arity c bound n+budgetSize c bound gates n+1≤s n)
    (small:∀ x,PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (gates x.length))
    : ∀ x : List Bool,x∈L ↔ Alt 3 (s x.length) (fun w=>(x,w)∈relation c bound gates) := by
  classical
  intro x
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
  rw [alt_three]
  constructor
  · intro mem
    have space:W+1≤s n:=by omega
    obtain ⟨a,hs⟩:=framed_circuit (small x) (addr n) space
    let r:=decoded F d (fun t j=>answer (unpack a.val) (ak t j))
    have authentic (i : ℕ) (hi:i≤T) : r i=canonical M start i := by
      apply Binary.physical_row c.tm (input c x) i d (Nat.zero_lt_succ _)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      intro j hj
      exact (hs (key c bound x i j)).1.trans (table_key c bound x hi hj)
    have win:=allChecks M start T (accept c) r authentic (semantics.mp mem)
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
    apply accepting_of_all M start T (accept c) (decoded F d (fun t j=>answer (unpack a.val) (ak t j)))
    exact universal_sound ks (allChannels c.tm) F d M start T fit (accept c) (unpack a.val)
      ak W rate (s n) (universalRoom n) (fun b=>(physical a b).mpr (win b))


theorem sigmaV_of_single_opening (L : Language Bool) (hL:∀ x,x∈L↔f x=true)
    (s bound gates : ℕ→ℕ) (ht:∀ n,c.time n≤bound n)
    (addr:∀ n,arity c bound n+gates n≤2^(arity c bound n+1))
    (universalRoom:∀ n,let d:=timeWidth c bound n
      d+(4+2*(channels c.tm).length)*(1+d+(4+@Fintype.card c.tm.K c.tm.kFin)*d)+1≤s n)
    (responseRoom:∀ n,arity c bound n+budgetSize c bound gates n+1≤s n)
    (small:∀ x,PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (gates x.length))
    (B : ℕ) (checker:DecidableInTime encodePair (relation c bound gates) (fun l=>B*l+B)) :
    L∈SigmaV 3 s :=
  ⟨relation c bound gates,B,checker,word_game c L hL s bound gates ht addr universalRoom responseRoom small⟩

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.sigmaV_of_single_opening

#print axioms StackTrace.OneOpeningGame.word_game
