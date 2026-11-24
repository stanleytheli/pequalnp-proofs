import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Prod.Lex

/-! Avoiding vertices in a family of bipartite covers closed under its two
uncrossing operations. A failed avoidance request has a witness of size ≤2. -/
namespace Midpoint
variable {L R : Type*} [DecidableEq L] [DecidableEq R]
abbrev Omitted (L R : Type*) := Finset L × Finset R

def leftUnion (a b : Omitted L R) : Omitted L R := (a.1 ∪ b.1, a.2 ∩ b.2)
def rightUnion (a b : Omitted L R) : Omitted L R := (a.1 ∩ b.1, a.2 ∪ b.2)

def Feasible (G : Set (Omitted L R)) (x : Finset L) (y : Finset R) : Prop :=
  ∃ a∈G, x⊆a.1 ∧ y⊆a.2

structure Closed (G : Set (Omitted L R)) : Prop where
  left : ∀ a∈G, ∀ b∈G, leftUnion a b∈G
  right : ∀ a∈G, ∀ b∈G, rightUnion a b∈G

theorem feasible_smaller {G : Set (Omitted L R)} {x x' : Finset L} {y y' : Finset R}
    (h : Feasible G x y) (xl : x'⊆x) (yr : y'⊆y) : Feasible G x' y' := by
  obtain ⟨a,ha,l,r⟩ := h
  exact ⟨a,ha,xl.trans l,yr.trans r⟩

theorem glue_left {G : Set (Omitted L R)} (h : Closed G) {x x' : Finset L} {y : Finset R}
    (a : Feasible G x y) (b : Feasible G x' y) : Feasible G (x∪x') y := by
  obtain ⟨a,ha,al,ar⟩ := a
  obtain ⟨b,hb,bl,br⟩ := b
  exact ⟨leftUnion a b,h.left a ha b hb,Finset.union_subset_union al bl,
    fun v hv => Finset.mem_inter.mpr ⟨ar hv,br hv⟩⟩

theorem glue_right {G : Set (Omitted L R)} (h : Closed G) {x : Finset L} {y y' : Finset R}
    (a : Feasible G x y) (b : Feasible G x y') : Feasible G x (y∪y') := by
  obtain ⟨a,ha,al,ar⟩ := a
  obtain ⟨b,hb,bl,br⟩ := b
  exact ⟨rightUnion a b,h.right a ha b hb,fun v hv => Finset.mem_inter.mpr ⟨al hv,bl hv⟩,
    Finset.union_subset_union ar br⟩

private theorem all_left {G : Set (Omitted L R)} (h : Closed G) {x : Finset L} {y : Finset R}
    (empty : Feasible G ∅ y) (each : ∀ v∈x, Feasible G {v} y) : Feasible G x y := by
  induction x using Finset.induction_on with
  | empty => exact empty
  | @insert a x _ ih =>
    have one := each a (Finset.mem_insert_self a x)
    have rest := ih (fun v hv => each v (Finset.mem_insert_of_mem hv))
    simpa using glue_left h one rest

private theorem all_right {G : Set (Omitted L R)} (h : Closed G) {x : Finset L} {y : Finset R}
    (empty : Feasible G x ∅) (each : ∀ v∈y, Feasible G x {v}) : Feasible G x y := by
  induction y using Finset.induction_on with
  | empty => exact empty
  | @insert a y _ ih =>
    have one := each a (Finset.mem_insert_self a y)
    have rest := ih (fun v hv => each v (Finset.mem_insert_of_mem hv))
    simpa using glue_right h one rest

/-- The empty, left singleton, right singleton and opposite-side pair tests
characterize simultaneous feasibility of every requested omission. -/
theorem pair_helly {G : Set (Omitted L R)} (h : Closed G) (x : Finset L) (y : Finset R) :
    Feasible G x y ↔ Feasible G ∅ ∅ ∧
      (∀ u∈x, Feasible G {u} ∅) ∧ (∀ v∈y, Feasible G ∅ {v}) ∧
      (∀ u∈x, ∀ v∈y, Feasible G {u} {v}) := by
  constructor
  · intro f
    exact ⟨feasible_smaller f (Finset.empty_subset _) (Finset.empty_subset _),
      fun _ hu => feasible_smaller f (Finset.singleton_subset_iff.mpr hu) (Finset.empty_subset _),
      fun _ hv => feasible_smaller f (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr hv),
      fun _ hu _ hv => feasible_smaller f (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_subset_iff.mpr hv)⟩
  · rintro ⟨emp,ls,rs,ps⟩
    exact all_right h (all_left h emp ls) (fun v hv => all_left h (rs v hv) (fun u hu => ps u hu v hv))

end Midpoint
#print axioms Midpoint.pair_helly
