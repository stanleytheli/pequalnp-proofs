import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Relation

/-! Two proof traces in a binary monotone circuit.  Inputs and gates have
separate indices. The two slots of a gate are distinct even if their operands agree. -/
namespace NearReadOnce

open Finset

private theorem trace_count {W E : Type*} [Fintype W] [Fintype E]
    [DecidableEq W] [DecidableEq E] (root : W) (child owner : E → W)
    (A B : Finset W) (P Q : Finset E) (commonLeaves : Finset W)
    (trimmed : ∀ w, w ≠ root → ∃ e, child e = w)
    (rootA : root ∈ A)
    (coverA : A ⊆ insert root (P.image child)) (coverB : B ⊆ insert root (Q.image child))
    (endsA : ∀ e ∈ P, child e ∈ A) (endsB : ∀ e ∈ Q, child e ∈ B)
    (common : (P ∩ Q).image owner ⊆ A ∩ B)
    (unique : Set.InjOn owner (↑(P ∩ Q) : Set E))
    (leaves : commonLeaves ⊆ A ∩ B)
    (apart : Disjoint ((P ∩ Q).image owner) commonLeaves) :
    Fintype.card W + commonLeaves.card ≤ Fintype.card E + 2 := by
  classical
  have ca : A.card ≤ P.card + 1 := by
    have := (card_le_card coverA).trans (card_insert_le root (P.image child))
    have := card_image_le (s := P) (f := child)
    omega
  have cb : B.card ≤ Q.card + 1 := by
    have := (card_le_card coverB).trans (card_insert_le root (Q.image child))
    have := card_image_le (s := Q) (f := child)
    omega
  have hi : (P ∩ Q).card + commonLeaves.card ≤ (A ∩ B).card := by
    have h := card_le_card (Finset.union_subset common leaves)
    rw [card_union_of_disjoint apart, card_image_of_injOn unique] at h
    exact h
  have hc : (univ : Finset W) \ (A ∪ B) ⊆ (((univ : Finset E) \ (P ∪ Q)).image child) := by
    intro w hw
    have hw' := (mem_sdiff.mp hw).2
    obtain ⟨e, rfl⟩ := trimmed w (fun h => hw' (h ▸ mem_union_left B rootA))
    refine mem_image.mpr ⟨e, mem_sdiff.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    intro he
    rcases mem_union.mp he with hp | hq
    · exact hw' (mem_union_left B (endsA _ hp))
    · exact hw' (mem_union_right A (endsB _ hq))
  have houtside := (card_le_card hc).trans card_image_le
  have hW := card_sdiff_add_card_eq_card (subset_univ (A ∪ B))
  have hE := card_sdiff_add_card_eq_card (subset_univ (P ∪ Q))
  have hAB := card_union_add_card_inter A B
  have hPQ := card_union_add_card_inter P Q
  simp only [card_univ] at hW hE
  omega

abbrev Wire (n g : Nat) := Fin n ⊕ Fin g
abbrev Slot (g : Nat) := Fin g × Bool

/-- `isAnd = true` chooses an AND gate. -/
structure Circuit (n g : Nat) where
  root : Wire n g
  operand : Fin g → Bool → Wire n g
  isAnd : Fin g → Bool
  rank : Wire n g → Nat
  before : ∀ i side, rank (operand i side) < rank (.inr i)
  trimmed : ∀ w, w ≠ root → ∃ i side, operand i side = w

def gateValue (isAnd a b : Bool) := if isAnd then a && b else a || b

/-- Evaluation equations for a physical circuit. -/
structure Eval {n g : Nat} (C : Circuit n g) where
  val : Finset (Fin n) → Wire n g → Bool
  input : ∀ x i, val x (.inl i) = decide (i ∈ x)
  gate : ∀ x i, val x (.inr i) = gateValue (C.isAnd i) (val x (C.operand i false)) (val x (C.operand i true))

private def Selected (isAnd goal left side : Bool) : Prop :=
  isAnd = goal ∨ side = !(left == goal)

private theorem selected_disagreement (o goal a b a' b' : Bool)
    (h : gateValue o a b = goal) (h' : gateValue o a' b' ≠ goal) :
    ∃ s : Bool, Selected o goal a s ∧ (if s then b else a) = goal ∧
      (if s then b' else a') ≠ goal := by
  have witness : (Selected o goal a false ∧ a = goal ∧ a' ≠ goal) ∨
      (Selected o goal a true ∧ b = goal ∧ b' ≠ goal) := by
    cases o <;> cases goal <;> cases a <;> cases b <;> cases a' <;> cases b' <;>
      simp_all [gateValue, Selected]
  rcases witness with left | right
  · exact ⟨false, by simpa using left⟩
  · exact ⟨true, by simpa using right⟩

variable {n g : Nat} {C : Circuit n g} (E : Eval C)

private def Step (x : Finset (Fin n)) (goal : Bool) (u v : Wire n g) : Prop :=
  ∃ i s, u = .inr i ∧ v = C.operand i s ∧
    Selected (C.isAnd i) goal (E.val x (C.operand i false)) s

private noncomputable def nodes (x : Finset (Fin n)) (goal : Bool) : Finset (Wire n g) := by
  classical exact univ.filter (Relation.ReflTransGen (Step E x goal) C.root)

private noncomputable def slots (x : Finset (Fin n)) (goal : Bool) : Finset (Slot g) := by
  classical
  exact univ.filter fun e => Sum.inr e.1 ∈ nodes E x goal ∧
    Selected (C.isAnd e.1) goal (E.val x (C.operand e.1 false)) e.2

private theorem mem_nodes (x : Finset (Fin n)) (goal : Bool) (w : Wire n g) :
    w ∈ nodes E x goal ↔ Relation.ReflTransGen (Step E x goal) C.root w := by
  classical simp [nodes]

private theorem mem_slots (x : Finset (Fin n)) (goal : Bool) (e : Slot g) :
    e ∈ slots E x goal ↔ Sum.inr e.1 ∈ nodes E x goal ∧
      Selected (C.isAnd e.1) goal (E.val x (C.operand e.1 false)) e.2 := by
  classical simp [slots]

private theorem nodes_covered (x : Finset (Fin n)) (goal : Bool) :
    nodes E x goal ⊆ insert C.root ((slots E x goal).image fun e => C.operand e.1 e.2) := by
  classical
  intro w hw
  cases (mem_nodes E x goal w).mp hw with
  | refl => exact mem_insert_self ..
  | tail hlast hstep =>
    obtain ⟨i, s, rfl, rfl, hsel⟩ := hstep
    exact mem_insert_of_mem (mem_image.mpr ⟨(i,s), (mem_slots E x goal _).mpr
      ⟨(mem_nodes E x goal _).mpr hlast, hsel⟩, rfl⟩)

private theorem child_mem (x : Finset (Fin n)) (goal : Bool) (e : Slot g)
    (h : e ∈ slots E x goal) : C.operand e.1 e.2 ∈ nodes E x goal := by
  have ⟨hp, hs⟩ := (mem_slots E x goal _).mp h
  exact (mem_nodes E x goal _).mpr (((mem_nodes E x goal _).mp hp).tail ⟨e.1,e.2,rfl,rfl,hs⟩)

/- If changing only input k changes the root away from the reference output,
   the reference proof trace must include that input. -/
private theorem pivotal_mem (x y : Finset (Fin n)) (goal : Bool) (k : Fin n)
    (same : ∀ i, i ≠ k → (i ∈ x ↔ i ∈ y))
    (href : E.val x C.root = goal) (hother : E.val y C.root ≠ goal) :
    Sum.inl k ∈ nodes E x goal := by
  classical
  apply (mem_nodes E x goal _).mpr
  suffices h : ∀ w : Wire n g, E.val x w = goal → E.val y w ≠ goal →
      Relation.ReflTransGen (Step E x goal) w (.inl k) from h C.root href hother
  intro w
  induction w using (measure C.rank).wf.induction with
  | h w ih =>
    intro hx hy
    cases w with
    | inl i =>
      by_cases hik : i = k
      · subst i; exact .refl
      · exfalso
        apply hy
        by_cases hi : i ∈ x
        · have hj := (same i hik).mp hi
          simpa [E.input, hi, hj] using hx
        · have hj : i ∉ y := fun h => hi ((same i hik).mpr h)
          simpa [E.input, hi, hj] using hx
    | inr i =>
      rw [E.gate] at hx hy
      obtain ⟨s, hs, h1, h2⟩ := selected_disagreement _ _ _ _ _ _ hx hy
      have hstep : Step E x goal (.inr i) (C.operand i s) := ⟨i,s,rfl,rfl,hs⟩
      apply Relation.ReflTransGen.head hstep
      apply ih (C.operand i s) (C.before i s)
      · cases s <;> simpa using h1
      · cases s <;> simpa using h2

/-- A minterm M and minimal zero certificate Z force an excess of at least
`(M ∩ Z).card - 1` over the `n-1` gate baseline. The physically trimmed
circuit uses binary AND/OR, free fanout, and a topological ranking. -/
theorem minterm_maxterm_gate_bound (M Z : Finset (Fin n))
    (m_yes : E.val M C.root = true)
    (m_min : ∀ i ∈ M, E.val (M.erase i) C.root = false)
    (z_no : E.val (univ \ Z) C.root = false)
    (z_min : ∀ i ∈ Z, E.val (insert i (univ \ Z)) C.root = true) :
    n + (M ∩ Z).card ≤ g + 2 := by
  classical
  let y : Finset (Fin n) := univ \ Z
  let own : Slot g → Wire n g := fun e => Sum.inr e.1
  let P := slots E M true
  let Q := slots E y false
  let A := nodes E M true
  let B := nodes E y false
  let L : Finset (Wire n g) := (M ∩ Z).image Sum.inl
  have hcommon : (P ∩ Q).image own ⊆ A ∩ B := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    obtain ⟨hp,hq⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨((mem_slots E M true _).mp hp).1, ((mem_slots E y false _).mp hq).1⟩
  have huid : Set.InjOn own (↑(P ∩ Q) : Set (Slot g)) := by
    rintro ⟨i,s⟩ hp ⟨j,t⟩ hq heq
    have ij : i = j := Sum.inr.inj heq
    subst j
    obtain ⟨hpP,hpQ⟩ := mem_inter.mp hp
    obtain ⟨hqP,hqQ⟩ := mem_inter.mp hq
    have h1 := ((mem_slots E M true _).mp hpP).2
    have h2 := ((mem_slots E M true _).mp hqP).2
    have h3 := ((mem_slots E y false _).mp hpQ).2
    have h4 := ((mem_slots E y false _).mp hqQ).2
    cases h : C.isAnd i <;> simp [Selected, h] at h1 h2 h3 h4 <;> grind
  have hleaves : L ⊆ A ∩ B := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
    obtain ⟨him,hiz⟩ := mem_inter.mp hi
    apply mem_inter.mpr
    constructor
    · apply pivotal_mem E M (M.erase i) true i _ m_yes
      · simp [m_min i him]
      · intro j hji; simp [hji]
    · apply pivotal_mem E y (insert i y) false i _ z_no
      · simp [y, z_min i hiz]
      · intro j hji; simp [hji]
  have disj : Disjoint ((P ∩ Q).image own) L := by
    apply Finset.disjoint_left.mpr
    intro w hw hL
    obtain ⟨e,_,rfl⟩ := mem_image.mp hw
    obtain ⟨i,_,hi⟩ := mem_image.mp hL
    cases hi
  have all_slots : ∀ w, w ≠ C.root → ∃ e : Slot g, C.operand e.1 e.2 = w := by
    intro w hw
    obtain ⟨i,s,hi⟩ := C.trimmed w hw
    exact ⟨(i,s),hi⟩
  have h := trace_count C.root (fun e : Slot g => C.operand e.1 e.2) own A B P Q L
    all_slots ((mem_nodes E M true _).mpr .refl) (nodes_covered E M true)
    (nodes_covered E y false) (child_mem E M true) (child_mem E y false)
    hcommon huid hleaves disj
  have hl : L.card = (M ∩ Z).card := card_image_of_injective _ Sum.inl_injective
  rw [hl] at h
  simp [Wire, Slot, Fintype.card_sum, Fintype.card_prod] at h
  omega

end NearReadOnce

#print axioms NearReadOnce.minterm_maxterm_gate_bound
