import Mathlib.Data.Fin.Basic

/-! Semantic verification of the read-two SAT switch. Occurrence ports
are supplied by the syntactic construction described in the manuscript. -/

namespace MetaComplexity.MonotoneSwitch
variable {V J U : Type*}
abbrev Lit (V : Type*) := V × Bool
abbrev Ports (V : Type*) := V → Bool → Fin 2 → Prop

def Clash (p : Ports V) : Prop :=
  ∃ v i j, p v true i ∧ p v false j

def Clauses (terms : J → Lit V → Prop) (σ : V → Bool) : Prop :=
  ∀ j, ∃ l, terms j l ∧ σ l.1 = l.2

def Guard (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2) (p : Ports V) : Prop :=
  ∀ j, ∃ l, terms j l ∧ p l.1 l.2 (slot j l)

def consistentPorts (σ : V → Bool) : Ports V := fun v sign _ => σ v = sign

theorem consistent_noclash (σ : V → Bool) : ¬Clash (consistentPorts σ) := by
  rintro ⟨v,i,j,h₁,h₂⟩
  exact Bool.noConfusion (h₁.symm.trans h₂)

theorem guard_consistent (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2)
    (σ : V → Bool) : Guard terms slot (consistentPorts σ) ↔ Clauses terms σ :=
  Iff.rfl

theorem consistent_guard_iff (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2) :
    (∃ p, ¬Clash p ∧ Guard terms slot p) ↔ ∃ σ, Clauses terms σ := by
  classical
  constructor
  · rintro ⟨p,none,hit⟩
    let σ (v : V) : Bool := decide (∃ i, p v true i)
    refine ⟨σ,?_⟩
    intro j
    obtain ⟨⟨v,sign⟩,hv,hs⟩ := hit j
    refine ⟨(v,sign),hv,?_⟩
    cases sign with
    | true =>
      apply decide_eq_true
      exact ⟨_,hs⟩
    | false =>
      apply decide_eq_false
      rintro ⟨i,yes⟩
      exact none ⟨v,i,_,yes,hs⟩
  · rintro ⟨σ,hs⟩
    exact ⟨consistentPorts σ, consistent_noclash σ, hs⟩

def switched (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2)
    (matched extra : U → Prop) (p : Ports V) (x : U) : Prop :=
  Clash p ∨ matched x ∨ Guard terms slot p ∧ extra x

theorem unsat_floor_function (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2)
    (matched extra : U → Prop) (unsat : ¬∃ σ, Clauses terms σ) (p : Ports V) (x : U) :
    switched terms slot matched extra p x ↔ Clash p ∨ matched x := by
  constructor
  · rintro (hp|hm|⟨guard,_⟩)
    · exact Or.inl hp
    · exact Or.inr hm
    · by_contra h
      exact unsat ((consistent_guard_iff terms slot).mp
        ⟨p,fun hp => h (Or.inl hp),guard⟩)
  · exact fun h => h.elim Or.inl (fun hm => Or.inr (Or.inl hm))

theorem satisfying_restriction (terms : J → Lit V → Prop) (slot : J → Lit V → Fin 2)
    (matched extra : U → Prop) (σ : V → Bool) (yes : Clauses terms σ) (x : U) :
    switched terms slot matched extra (consistentPorts σ) x ↔ matched x ∨ extra x := by
  change (Clash (consistentPorts σ) ∨ matched x ∨
    Guard terms slot (consistentPorts σ) ∧ extra x) ↔ _
  simp [consistent_noclash,guard_consistent,yes]

end MetaComplexity.MonotoneSwitch
#print axioms MetaComplexity.MonotoneSwitch.consistent_guard_iff
#print axioms MetaComplexity.MonotoneSwitch.unsat_floor_function
#print axioms MetaComplexity.MonotoneSwitch.satisfying_restriction
