import GreedyRouting

namespace SparsePermanent.DirectedGrowth
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A simple directed path keeps its vertices in travel order, with both
endpoints included and forbidden vertices excluded. -/
inductive SimpleRoute (E : V→V→Prop) (F : Finset V) : V→V→List V→Prop
  | nil {a : V} (safe:a∉F) : SimpleRoute E F a a [a]
  | snoc {a b c : V} {xs : List V} (prev : SimpleRoute E F a b xs)
      (edge:E b c) (safe:c∉F) (fresh:c∉xs) : SimpleRoute E F a c (xs++[c])

variable {E : V→V→Prop} {F : Finset V} {a b : V} {xs : List V}

theorem SimpleRoute.nodup (p : SimpleRoute E F a b xs) : xs.Nodup := by
  induction p with
  | nil=>simp
  | snoc _ _ _ fresh ih=>
    simp [List.nodup_append,ih]
    rintro _ h rfl;exact fresh h

theorem SimpleRoute.inside (p : SimpleRoute E F a b xs) : ∀x∈xs,x∉F := by
  induction p with
  | nil safe=>simpa using safe
  | snoc _ _ safe _ ih=>
    intro x hx
    rcases List.mem_append.mp hx with old|last
    · exact ih x old
    · exact (List.mem_singleton.mp last) ▸ safe

theorem SimpleRoute.ends (p : SimpleRoute E F a b xs) : xs.head?=some a ∧ xs.getLast?=some b := by
  induction p with
  | nil=>simp
  | @snoc b c ys prev _ _ _ ih=>simp [List.head?_append,ih.1]

private theorem SimpleRoute.prefix (p : SimpleRoute E F a b xs) (c : V) (hc : c∈xs) :
    ∃ys,SimpleRoute E F a c ys ∧ ys.Sublist xs := by
  induction p with
  | nil safe=>simp only [List.mem_singleton] at hc;subst c;exact ⟨_,.nil safe,.refl _⟩
  | @snoc b d ys prev edge safe fresh ih=>
    rcases List.mem_append.mp hc with old|last
    · obtain ⟨zs,p,sub⟩:=ih old
      exact ⟨zs,p,sub.trans (List.sublist_append_left ..)⟩
    · simp only [List.mem_singleton] at last;subst c
      exact ⟨_,.snoc prev edge safe fresh,.refl _⟩

/-- Loop erasure preserves directedness and stays inside the original
allowed set. No girth assumption is needed for this step. -/
theorem Route.simple {t : ℕ} (p : Route E F a b t) : ∃xs,SimpleRoute E F a b xs ∧ xs.length≤t+1 := by
  induction p with
  | nil safe=>exact ⟨_,.nil safe,le_rfl⟩
  | @snoc b c t prev edge safe ih=>
    obtain ⟨ys,w,len⟩:=ih
    by_cases old:c∈ys
    · obtain ⟨zs,q,sub⟩:=w.prefix c old
      exact ⟨zs,q,sub.length_le.trans (by omega)⟩
    · exact ⟨_,.snoc w edge safe old,by simp;omega⟩

variable {P : Finset V} {L W r M : ℕ}

def PrivatePath (job : Demand E P L W r) (xs : List V) : Prop :=
  SimpleRoute E ∅ job.forward.origin job.backward.origin xs ∧ xs.length≤M+1 ∧
    xs.toFinset∩P⊆job.trunks

private theorem SimpleRoute.weaken (p : SimpleRoute E F a b xs) (H : Finset V) (sub:H⊆F) :
    SimpleRoute E H a b xs := by
  induction p with
  | nil safe=>exact .nil (fun h=>safe (sub h))
  | snoc _ edge safe fresh ih=>exact .snoc ih edge (fun h=>safe (sub h)) fresh

/-- Ordered finite paths corresponding one-to-one to the demand list. All
path supports are disjoint and every protected vertex belongs to that
path's own two port trunks. -/
theorem Packed.simplePaths {jobs : List (Demand E P L W r)} {U : Finset V} (p : Packed E P L W r M jobs U) :
    ∃paths : List (List V),List.Forall₂ (PrivatePath (M:=M)) jobs paths ∧
      paths.Pairwise (fun a b=>Disjoint a.toFinset b.toFinset) ∧ ∀xs∈paths,xs.toFinset⊆U := by
  induction p with
  | nil=>exact ⟨[],.nil,.nil,by simp⟩
  | @cons job jobs S T t route len size own tail split ih=>
    obtain ⟨ys,q,short⟩:=route.simple
    obtain ⟨ps,agree,separate,old⟩:=ih
    have inside : ys.toFinset⊆S := by
      intro z hz
      simpa using q.inside z (List.mem_toFinset.mp hz)
    have absorb : ys.toFinset∩P⊆job.trunks := fun z hz=>own (mem_inter.mpr ⟨inside (mem_inter.mp hz).1,(mem_inter.mp hz).2⟩)
    refine ⟨ys::ps,.cons ⟨q.weaken ∅ (empty_subset _),by omega,absorb⟩ agree,
      List.pairwise_cons.mpr ⟨fun zs mem=>split.mono inside (old zs mem),separate⟩,?_⟩
    · intro xs mem
      rcases List.mem_cons.mp mem with rfl|prev
      · exact inside.trans subset_union_left
      · exact (old xs prev).trans subset_union_right

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Packed.simplePaths
