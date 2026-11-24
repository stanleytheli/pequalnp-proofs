import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Tauto

namespace AlgebraicMeta.BooleanBlocks
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Coordinates with the same profile cannot be separated by any member. -/
def Same (s : Finset (Finset I)) (i j : I) : Prop :=
  ∀ a∈s, i∈a ↔ j∈a

def block (s : Finset (Finset I)) (i : I) : Finset I :=
  univ \ (s.filter (fun a => i∉a)).biUnion id

theorem same_block {s : Finset (Finset I)} (complement : ∀a∈s, univ\a∈s) (i j : I) :
    j∈block s i ↔ Same s i j := by
  classical
  have eq : j∈block s i ↔ ∀a∈s, j∈a → i∈a := by
    simp [block]
    constructor
    · intro h a ha hj
      by_contra hi
      exact h a ha hi hj
    · intro h a ha hi hj
      exact hi (h a ha hj)
  rw [eq]
  constructor
  · intro h a ha
    refine ⟨fun hi=>?_,h a ha⟩
    by_contra hj
    have contra := h (univ\a) (complement a ha) (by simp [hj])
    simp [hi] at contra
  · exact fun h a ha hj => (h a ha).mpr hj

omit [Fintype I] in
private theorem union_closed {s : Finset (Finset I)} (empty : ∅∈s)
    (cu : ∀a∈s,∀b∈s,a∪b∈s) (selected : Finset (Finset I)) (all : selected⊆s) :
    selected.biUnion id ∈s := by
  classical
  induction selected using Finset.induction_on with
  | empty => simpa using empty
  | insert a z ha ih =>
    rw [biUnion_insert]
    exact cu a (all (mem_insert_self ..)) _ (ih (fun _ h=>all (mem_insert_of_mem h)))

/-- A finite field of sets is precisely the unions of the coordinate blocks
on which all its members have identical membership bits. -/
theorem membership_iff_blocks (s : Finset (Finset I)) (empty : ∅∈s)
    (cm : ∀a∈s,∀b∈s,a∩b∈s) (cc : ∀a∈s, univ\a∈s) (x : Finset I) :
    x∈s ↔ ∀ i j, Same s i j → (i∈x ↔ j∈x) := by
  classical
  have union (a : Finset I) (ha : a∈s) (b : Finset I) (hb : b∈s) : a∪b∈s := by
    have h := cc _ (cm _ (cc _ ha) _ (cc _ hb))
    have eq : univ\((univ\a)∩(univ\b))=a∪b := by ext v; simp; tauto
    rwa [eq] at h
  have hb (i : I) : block s i ∈s := cc _ (union_closed empty union _
    (filter_subset (fun a=>i∉a) s))
  constructor
  · intro hx i j same
    exact same _ hx
  · intro h
    let u := x.image (block s)
    have hu : u⊆s := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact hb i
    have eq : u.biUnion id=x := by
      ext i
      constructor
      · intro hi
        obtain ⟨a,ha,hi⟩ := mem_biUnion.mp hi
        obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
        exact (h _ _ ((same_block cc _ _).mp hi)).mp hj
      · intro hi
        apply mem_biUnion.mpr
        refine ⟨block s i,mem_image_of_mem _ hi,?_⟩
        exact (same_block cc _ _).mpr (fun _ _ => Iff.rfl)
    rw [←eq]
    exact union_closed empty union u hu

end AlgebraicMeta.BooleanBlocks
#print axioms AlgebraicMeta.BooleanBlocks.membership_iff_blocks
