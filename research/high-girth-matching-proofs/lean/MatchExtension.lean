import FamilyShape
import Mathlib.GroupTheory.Perm.Option

namespace SparsePermanent

abbrev Perfect {I : Type*} (E : I→I→Prop) := {p : Equiv.Perm I // ∀ i,E i (p i)}

namespace MatchExtension
variable {I : Type*} [DecidableEq I]

private def lift (j : Option I) (p : Equiv.Perm I) := Equiv.Perm.decomposeOption.symm (j,p)
private def tag (r c : I) (p : Equiv.Perm I) := if p c=r then some r else none

private theorem at_none (j : Option I) (p : Equiv.Perm I) : lift j p none=j := by simp [lift]
private theorem at_plain (p : Equiv.Perm I) (i : I) : lift none p (some i)=some (p i) := by simp [lift]
private theorem at_used {p : Equiv.Perm I} {i j : I} (e : p i=j) :
    lift (some j) p (some i)=none := by simp [lift,e]
private theorem at_free {p : Equiv.Perm I} {i j : I} (e : p i≠j) :
    lift (some j) p (some i)=some (p i) := by simp [lift,Equiv.swap_apply_of_ne_of_ne,e]

private theorem characterize (E : I→I→Prop) (r c : I) (hit : E c r) (p : Equiv.Perm I) (j : Option I) :
    (∀ i, divideAdj E r c i (lift j p i)) ↔ (∀ i,E i (p i)) ∧ j=tag r c p := by
  cases j with
  | none =>
    constructor
    · intro all
      have ok (i : I) := all (some i)
      simp only [at_plain,divideAdj] at ok
      refine ⟨fun i=>(ok i).1,?_⟩
      have miss : p c≠r := fun v=>(ok c).2 ⟨rfl,v⟩
      simp [tag,miss]
    · rintro ⟨h,tagEq⟩
      have miss : p c≠r := by intro e; simp [tag,e] at tagEq
      rintro (_|i)
      · rw [at_none]; trivial
      · rw [at_plain]
        exact ⟨h i,fun ⟨e,e'⟩=>miss (e ▸ e')⟩
  | some b =>
    constructor
    · intro all
      have source:=all none
      rw [at_none] at source
      change b=r at source
      subst b
      have atInv:=all (some (p.symm r))
      rw [at_used (p.apply_symm_apply r)] at atInv
      change p.symm r=c at atInv
      have used : p c=r := by rw [←atInv]; simp
      refine ⟨fun i=>?_,by simp [tag,used]⟩
      by_cases e : i=c
      · simpa [e,used] using hit
      · have hi:=all (some i)
        have skip : p i≠r := fun v=>e (p.injective (v.trans used.symm))
        rw [at_free skip] at hi
        exact hi.1
    · rintro ⟨h,tagEq⟩
      by_cases used : p c=r
      · have same : b=r := by simpa [tag,used] using tagEq
        subst b
        rintro (_|i)
        · rw [at_none]; rfl
        · by_cases e : i=c
          · subst i; rw [at_used used]; rfl
          · have skip : p i≠r := fun v=>e (p.injective (v.trans used.symm))
            rw [at_free skip]
            exact ⟨h i,fun z=>e z.1⟩
      · simp [tag,used] at tagEq

/-- Every old matching has exactly one extension across an odd subdivision.
This explicit equivalence remembers the old permutation through removeNone. -/
noncomputable def divide (E : I→I→Prop) (r c : I) (hit : E c r) : Perfect E ≃ Perfect (divideAdj E r c) := by
  let f : Perfect E→Perfect (divideAdj E r c) := fun p=>
    ⟨lift (tag r c p.val) p.val, (characterize E r c hit _ _).mpr ⟨p.prop,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b eq
    apply Subtype.ext
    have e:=congrArg (fun z : Perfect (divideAdj E r c)=>(Equiv.Perm.decomposeOption z.val).2) eq
    change (Equiv.Perm.decomposeOption (Equiv.Perm.decomposeOption.symm (tag r c a.val,a.val))).2 =
      (Equiv.Perm.decomposeOption (Equiv.Perm.decomposeOption.symm (tag r c b.val,b.val))).2 at e
    simpa only [Equiv.apply_symm_apply] using e
  · rintro ⟨q,ok⟩
    obtain ⟨⟨j,p⟩,eq⟩:=Equiv.Perm.decomposeOption.symm.surjective q
    have h : ∀ i,divideAdj E r c i (lift j p i) := by rw [show lift j p=q from eq]; exact ok
    obtain ⟨old,tagEq⟩:=(characterize E r c hit _ _).mp h
    refine ⟨⟨p,old⟩,Subtype.ext ?_⟩
    change lift (tag r c p) p=q
    rw [←tagEq]
    exact eq

noncomputable def run {D R : Type*} [DecidableEq D] [CommSemiring R] (B : Board D I R) (ops : List D) :
    Perfect B.adj ≃ Perfect (B.run ops).adj := by
  induction ops with
  | nil => exact Equiv.refl _
  | cons d ds ih =>
    exact ih.trans (divide _ _ _ ((B.run ds).marked d))

/-- The canonical subdivided graph, including all internal vertices, has
perfect matchings in explicit bijection with the dense permutations. -/
noncomputable def family (k h : ℕ) : Perfect (physical k h) ≃ Equiv.Perm (Node k) :=
  (run (coreBoard (0 : Matrix (Node k) (Node k) ℕ)) (operations k h)).symm.trans CoreMatching.equivOriginal

end MatchExtension
end SparsePermanent
#print axioms SparsePermanent.MatchExtension.family
