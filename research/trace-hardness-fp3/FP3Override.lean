import PEqualNP.Defs.TimeAlt
import PEqualNP.Library.Machines.ComposeRun
import PEqualNP.Library.Machines.FirstGRun
import PEqualNP.Library.Machines.Transducer
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum

namespace FiniteOverride
open Turing PEqualNP.Library PEqualNP.Library.Machines

abbrev In := Bool ⊕ Bool
abbrev Keep := Option Bool

theorem joined {M N : FinTM2} (φ : M.Γ M.k₁→N.Γ N.k₀) (default : N.Γ N.k₀)
    {i o p t u} (h₁:TM2OutputsInTime M i (some o) t) (h₂:TM2OutputsInTime N (o.map φ) (some p) u) :
    Nonempty (TM2OutputsInTime (comp M N φ (some default)) i (some p) (t+2*o.length+2+u)) := by
  obtain ⟨n,hn,_,run⟩:=comp_run (M1:=M) (M2:=N) φ (some default) (by simp)
    i o p h₁.steps h₂.steps h₁.evals_in_steps h₂.evals_in_steps
  exact ⟨⟨⟨n,run⟩,by change n≤t+2*o.length+2+u;have:=h₁.steps_le_m;have:=h₂.steps_le_m;omega⟩⟩

variable {Q : Type} [Fintype Q]

def inputStep (δ : Q→In→Q) (q : Q) (a : In) : Q × Option (In ⊕ Keep) × Option (In ⊕ Keep) :=
  (δ q a,some (.inl a),none)

def last (flags : Q→Keep) (q : Q) : Option (In ⊕ Keep) := some (.inr (flags q))

def inputMachine (δ : Q→In→Q) (flags : Q→Keep) (q : Q) :=
  trM (inputStep δ) (last flags) q (some (Sum.inl (Sum.inl false)))

theorem prep_value (δ : Q→In→Q) (flags : Q→Keep) (q : Q) (x : List In) :
    fstRun2 (inputStep δ) (last flags) q x=Gen.gpair (x,[flags (x.foldl δ q)]) := by
  induction x generalizing q with
  | nil=>rfl
  | cons a x ih=>simp [fstRun2,inputStep,ih,Gen.gpair]

theorem prep_run (δ : Q→In→Q) (flags : Q→Keep) (q : Q) (x : List In) :
    Nonempty (TM2OutputsInTime (inputMachine δ flags q) x (some (Gen.gpair (x,[flags (x.foldl δ q)]))) (2*x.length+3)) := by
  have h:=trM_run (inputStep δ) (last flags) q (some (Sum.inl (Sum.inl false))) (by simp) x
  have run:=h.trans (congrArg (fun w : List (In ⊕ Keep)=>some (haltList (inputMachine δ flags q) w))
    (prep_value δ flags q x))
  exact ⟨⟨⟨_,run⟩,by change x.length+1+1+(x.length+1)≤2*x.length+3;omega⟩⟩

def outputStep (q : Bool) (a : Bool ⊕ Keep) : Bool × Option Bool × Option Bool :=
  (a.elim id (fun v=>v.getD q),none,none)

def suffix := trM outputStep some false (some false)

theorem finish_run (a : Bool) (v : Keep) :
    Nonempty (TM2OutputsInTime suffix (Gen.gpair ([a],[v])) (some [v.getD a]) 7) := by
  have h:=trM_run outputStep some false (some false) (by simp) (Gen.gpair ([a],[v]))
  exact ⟨⟨⟨_,h⟩,show 7≤7 from le_rfl⟩⟩

variable {f : (List Bool×List Bool)→Bool}
abbrev Decider (f : (List Bool×List Bool)→Bool) := TM2ComputableInTime encodePair Computability.encodeBool f

noncomputable def side (c : Decider f) :=
  Gen.firstM c.tm Keep c.inputAlphabet.invFun c.outputAlphabet

noncomputable def compound (c : Decider f) (δ : Q→In→Q) (flags : Q→Keep) (q : Q) :=
  comp (comp (inputMachine δ flags q) (side c) id (some (Sum.inl (Sum.inl false))))
    suffix id (some (Sum.inl false))

theorem tagged_run (c : Decider f) (p : List Bool×List Bool) (v : Keep) :
    Nonempty (TM2OutputsInTime (side c) (Gen.gpair (encodePair p,[v]))
      (some (Gen.gpair ([f p],[v]))) (c.time (encodePair p).length+2*(encodePair p).length+9)) := by
  let o:=[c.outputAlphabet.invFun (f p)]
  have run:=c.outputsFun p
  obtain ⟨k,hk,h⟩:=Gen.first_run (C:=Keep) c.inputAlphabet.invFun c.outputAlphabet
    (encodePair p) [v] o run.steps run.evals_in_steps
  have mapped:o.map c.outputAlphabet=[f p]:=by simp [o]
  rw [mapped] at h
  have step:=run.steps_le_m
  simp only [o,List.length_singleton] at hk
  exact ⟨⟨⟨k,h⟩,by change k≤_;omega⟩⟩

/-- A prepass over the input remembers a finite-state flag during an arbitrary
bounded physical decider run. A final two-symbol pass can override its answer. -/
theorem compound_run (c : Decider f) (δ : Q→In→Q) (flags : Q→Keep) (q : Q) (p : List Bool×List Bool) :
    Nonempty (TM2OutputsInTime (compound c δ flags q) (encodePair p)
      (some [(flags ((encodePair p).foldl δ q)).getD (f p)])
      (c.time (encodePair p).length+6*(encodePair p).length+27+5)) := by
  let x:=encodePair p
  let v:=flags (x.foldl δ q)
  let y:=Gen.gpair (x,[v])
  let out:=Gen.gpair ([f p],[v])
  obtain ⟨first⟩:=prep_run δ flags q x
  obtain ⟨second⟩:=tagged_run c p v
  have alongside:TM2OutputsInTime (side c) (y.map id) (some out) (c.time x.length+2*x.length+9):=by
    exact (congrArg (fun u : List (In ⊕ Keep)=>TM2OutputsInTime (side c) u (some out)
      (c.time x.length+2*x.length+9)) (List.map_id y)).mpr second
  have start:=joined (M:=inputMachine δ flags q) (N:=side c) id (Sum.inl (Sum.inl false)) first alongside
  obtain ⟨middle⟩:=start
  obtain ⟨done⟩:=finish_run (f p) v
  have rest:TM2OutputsInTime suffix (out.map id) (some [v.getD (f p)]) 7:= (congrArg (fun u : List (Bool ⊕ Keep)=>
    TM2OutputsInTime suffix u (some [v.getD (f p)]) 7) (List.map_id out)).mpr done
  obtain ⟨run⟩:=joined (M:=comp (inputMachine δ flags q) (side c) id (some (Sum.inl (Sum.inl false))))
    (N:=suffix) id (Sum.inl false) middle rest
  have len:y.length=x.length+1:=by simp [y,Gen.gpair]
  have ol:out.length=2:=rfl
  have limit:=run.steps_le_m
  change run.steps≤(2*x.length+3+2*y.length+2+(c.time x.length+2*x.length+9))+2*out.length+2+7 at limit
  exact ⟨⟨run.toEvalsTo,by rw [len,ol] at limit;change run.steps≤c.time x.length+6*x.length+27+5;omega⟩⟩

theorem decidable (c : Decider f) (K : ℕ) (lim:∀ n,c.time n≤K*n+K)
    (δ : Q→In→Q) (flags : Q→Keep) (q : Q) :
    DecidableInTime encodePair {p | (flags ((encodePair p).foldl δ q)).getD (f p)=true}
      (fun n=>(K+32)*n+(K+32)) := by
  let result:=fun p=>(flags ((encodePair p).foldl δ q)).getD (f p)
  refine ⟨result,fun _=>Iff.rfl,?_,fun n=>?_⟩
  · exact {
      tm:=compound c δ flags q
      inputAlphabet:=Equiv.refl _
      outputAlphabet:=Equiv.refl _
      time:=fun n=>c.time n+6*n+27+5
      outputsFun:=fun p=>by
        let run:=(compound_run c δ flags q p).some
        change TM2OutputsInTime (compound c δ flags q) ((encodePair p).map id) (some [result p]) _
        exact (congrArg (fun w : List In=>TM2OutputsInTime (compound c δ flags q) w (some [result p])
          (c.time (encodePair p).length+6*(encodePair p).length+27+5)) (List.map_id (encodePair p))).mpr run }
  · change c.time n+6*n+27+5≤(K+32)*n+(K+32)
    have ht:=lim n
    nlinarith

end FiniteOverride

#print axioms FiniteOverride.compound_run
#print axioms FiniteOverride.decidable
