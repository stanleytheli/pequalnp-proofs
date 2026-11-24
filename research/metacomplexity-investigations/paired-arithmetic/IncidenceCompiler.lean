import CopyCompiler
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

namespace AlgebraicMeta.IncidenceCompiler
open CopyCompiler Finset Function
universe u v w

/-- Every literal position has one clause, one variable, and one sign. This
incidence representation counts repeated literal occurrences separately. -/
structure Formula (V : Type u) (C : Type v) (O : Type w) where
  clause : O → C
  owner : O → V
  sign : O → Bool

def Formula.Sat {V C O : Type*} (f : Formula V C O) (a : V → Bool) : Prop :=
  ∀ c, ∃ o, f.clause o=c ∧ a (f.owner o)=f.sign o

noncomputable def fiberSize {V O : Type*} [Fintype O] [DecidableEq V] (owner : O → V) (v : V) :=
  Fintype.card {o // owner o=v}

/-- Coordinate zero provides a representative, including for an old bit
which occurs nowhere. Each original incidence gets its own positive index. -/
noncomputable def allocate {V O : Type*} [Fintype O] [DecidableEq V] (owner : O → V) :
    O ↪ Pos (fiberSize owner) :=
  (Equiv.sigmaFiberEquiv owner).symm.toEmbedding.trans <|
    Function.Embedding.sigmaMap (Function.Embedding.refl V) (fun v =>
      (Fintype.equivFin {o // owner o=v}).toEmbedding.trans ⟨Fin.succ,Fin.succ_injective _⟩)

@[simp] theorem allocate_owner {V O : Type*} [Fintype O] [DecidableEq V] (owner : O → V) (o : O) :
    (allocate owner o).1=owner o := rfl

def rotation {V : Type*} (count : V → ℕ) : Equiv.Perm (Pos count) :=
  Equiv.sigmaCongrRight (fun v => finRotate (count v+1))

def split {V C O : Type*} (f : Formula V C O) {count : V → ℕ}
    (atCopy : O ↪ Pos count) (flips : Pos count → Bool) :
    Formula (Pos count) (C ⊕ Pos count) (O ⊕ (Pos count ⊕ Pos count)) where
  clause := Sum.elim (Sum.inl ∘ f.clause) (Sum.elim Sum.inr Sum.inr)
  owner := Sum.elim atCopy (Sum.elim id (rotation count))
  sign := Sum.elim (fun o => xor (f.sign o) (flips (atCopy o)))
                   (Sum.elim flips (fun p => !(flips (rotation count p))))

private theorem signed_read (b s f : Bool) : b=xor s f ↔ xor b f=s := by
  cases b <;> cases s <;> cases f <;> decide

private theorem link_read (b c f g : Bool) :
    (b=f ∨ c=(!g)) ↔ xor b f ≤ xor c g := by
  cases b <;> cases c <;> cases f <;> cases g <;> decide

theorem split_semantics {V C O : Type*} (f : Formula V C O) {count : V → ℕ}
    (atCopy : O ↪ Pos count) (flips b : Pos count → Bool) :
    (split f atCopy flips).Sat b ↔
      (∀ c, ∃ o, f.clause o=c ∧ logical count flips b (atCopy o)=f.sign o) ∧
      ∀ p, logical count flips b p ≤ logical count flips b (rotation count p) := by
  simp [-Sigma.exists,Formula.Sat,split,Sum.forall,Sum.exists,logical,signed_read,link_read]

theorem rotated_iff_cycling {V : Type*} (count : V → ℕ) (flips b : Pos count → Bool) :
    (∀ p, logical count flips b p ≤ logical count flips b (rotation count p)) ↔ Cycling count flips b := by
  constructor
  · intro h v
    constructor
    · intro j hj
      have hh := h ⟨v,⟨j,hj.trans_le (Nat.le_succ _)⟩⟩
      simpa [rotation, pos,finRotate_of_lt hj,Nat.min_eq_left hj.le,
        Nat.min_eq_left (Nat.succ_le_of_lt hj)] using hh
    · have hh := h ⟨v,Fin.last (count v)⟩
      change _ ≤ logical count flips b ⟨v,finRotate _ (Fin.last _)⟩ at hh
      rw [finRotate_last] at hh
      simpa [pos,Fin.last] using hh
  · intro h p
    obtain ⟨v,j⟩ := p
    by_cases hlt : j.val<count v
    · have hh := (h v).1 j.val hlt
      have rot : finRotate (count v+1) j=⟨j.val+1,Nat.succ_lt_succ hlt⟩ := finRotate_of_lt hlt
      simpa [rotation,rot,pos,Nat.min_eq_left hlt.le,Nat.min_eq_left (Nat.succ_le_of_lt hlt)] using hh
    · have eq : j=Fin.last (count v) := Fin.ext (by have := j.isLt; simp [Fin.last]; omega)
      subst j
      change _ ≤ logical count flips b ⟨v,finRotate _ (Fin.last _)⟩
      rw [finRotate_last]
      simpa [pos,Fin.last] using (h v).2

/-- A genuine concrete source-CNF to signed occurrence-CNF equivalence,
retaining all assignments (and thus all multiplicities). -/
noncomputable def satisfyingEquiv {V C O : Type*} [Fintype O] [DecidableEq V]
    (f : Formula V C O) (flips : Pos (fiberSize f.owner) → Bool) :
    {a // f.Sat a} ≃ {b // (split f (allocate f.owner) flips).Sat b} := by
  let count := fiberSize f.owner
  let loc := allocate f.owner
  let accept (z : Pos count → Bool) := ∀ c, ∃ o, f.clause o=c ∧ z (loc o)=f.sign o
  have left (a) : f.Sat a ↔ accept (fun p => a p.1) := by rfl
  have right (b) : Cycling count flips b ∧ accept (logical count flips b) ↔
      (split f loc flips).Sat b := by
    rw [split_semantics,rotated_iff_cycling]
    exact and_comm
  exact (Equiv.subtypeEquivRight left).trans <| (modelEquiv count flips accept).trans <| Equiv.subtypeEquivRight right

private def role {O P : Type*} : O ⊕ (P ⊕ P) → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

open Classical in
theorem three_occurrences {V C O : Type*} [Fintype V] [Fintype O] (f : Formula V C O)
    {count : V → ℕ} (atCopy : O ↪ Pos count) (flips : Pos count → Bool) (p : Pos count) :
    Fintype.card {o // (split f atCopy flips).owner o=p} ≤ 3 := by
  classical
  let label (t : {o // (split f atCopy flips).owner o=p}) := role t.1
  have oneEach : Injective label := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ e
    apply Subtype.ext
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> simp [label,role] at e
    · exact congrArg Sum.inl (atCopy.injective (ha.trans hb.symm))
    · exact congrArg (fun x => Sum.inr (Sum.inl x)) (ha.trans hb.symm)
    · exact congrArg (fun x => Sum.inr (Sum.inr x)) ((rotation count).injective (ha.trans hb.symm))
  simpa using Fintype.card_le_of_injective label oneEach

open Classical in
theorem old_width {V C O : Type*} [Fintype V] [Fintype O] (f : Formula V C O)
    {count : V → ℕ} (atCopy : O ↪ Pos count) (flips : Pos count → Bool) (c : C) :
    Fintype.card {o // (split f atCopy flips).clause o=Sum.inl c} = Fintype.card {o // f.clause o=c} := by
  classical
  let lift (t : {o // f.clause o=c}) : {o // (split f atCopy flips).clause o=Sum.inl c} :=
    ⟨Sum.inl t.val,congrArg Sum.inl t.property⟩
  have onto : Surjective lift := by
    rintro ⟨o,ho⟩
    rcases o with o | (o | o)
    · exact ⟨⟨o,Sum.inl.inj ho⟩,rfl⟩
    · cases ho
    · cases ho
  have inj : Injective lift := by
    intro a b eq
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val eq))
  exact (Fintype.card_of_bijective (show Bijective lift from ⟨inj,onto⟩)).symm

open Classical in
theorem link_width {V C O : Type*} [Fintype V] [Fintype O] (f : Formula V C O)
    {count : V → ℕ} (atCopy : O ↪ Pos count) (flips : Pos count → Bool) (p : Pos count) :
    Fintype.card {o // (split f atCopy flips).clause o=Sum.inr p} = 2 := by
  classical
  let lift : Bool → {o // (split f atCopy flips).clause o=Sum.inr p}
    | false => ⟨Sum.inr (Sum.inl p),rfl⟩
    | true => ⟨Sum.inr (Sum.inr p),rfl⟩
  have onto : Surjective lift := by
    rintro ⟨o,ho⟩
    rcases o with o | (o | o)
    · cases ho
    · obtain rfl := Sum.inr.inj ho
      exact ⟨false,rfl⟩
    · obtain rfl := Sum.inr.inj ho
      exact ⟨true,rfl⟩
  have inj : Injective lift := by
    intro a b e
    have ee := congrArg Subtype.val e
    cases a <;> cases b <;> simp [lift] at ee ⊢
  simpa using (Fintype.card_of_bijective (show Bijective lift from ⟨inj,onto⟩)).symm

end AlgebraicMeta.IncidenceCompiler
#print axioms AlgebraicMeta.IncidenceCompiler.satisfyingEquiv
#print axioms AlgebraicMeta.IncidenceCompiler.three_occurrences
#print axioms AlgebraicMeta.IncidenceCompiler.old_width
#print axioms AlgebraicMeta.IncidenceCompiler.link_width
