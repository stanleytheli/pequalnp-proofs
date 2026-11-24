import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace PermanentDecision
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def used (a : I → ℕ) := univ.filter fun i => 0 < a i
def repeated (a : I → ℕ) := univ.filter fun i => 1 < a i
def outside (a : I → ℕ) (K : Finset I) := ∑ i ∈ univ \ K, a i

@[simp] theorem mem_used {a : I → ℕ} {i : I} : i ∈ used a ↔ 0 < a i := by simp [used]
@[simp] theorem mem_repeated {a : I → ℕ} {i : I} : i ∈ repeated a ↔ 1 < a i := by simp [repeated]

theorem face_identity (a : I → ℕ) (K : Finset I) :
    K.card + outside a K = (used a).card + (K \ used a).card +
      ∑ i ∈ used a \ K, (a i - 1) := by
  have sub : used a \ K ⊆ univ \ K := fun i hi =>
    mem_sdiff.mpr ⟨mem_univ i, (mem_sdiff.mp hi).2⟩
  have eq : outside a K = ∑ i ∈ used a \ K, a i := by
    symm
    apply sum_subset sub
    intro i hi no
    have := (mem_sdiff.mp hi).2
    have nz : ¬ 0 < a i := fun h => no (mem_sdiff.mpr ⟨mem_used.mpr h, this⟩)
    omega
  have split : (∑ i ∈ used a \ K, a i) =
      (used a \ K).card + ∑ i ∈ used a \ K, (a i - 1) := by
    calc
      _ = ∑ i ∈ used a \ K, (1 + (a i - 1)) := by
        apply sum_congr rfl
        intro i hi
        have := mem_used.mp (mem_sdiff.mp hi).1
        omega
      _ = _ := by simp [sum_add_distrib]
  have hA := card_sdiff_add_card_inter (used a) K
  have hK := card_sdiff_add_card_inter K (used a)
  rw [inter_comm K] at hK
  omega

theorem all_above (a : I → ℕ) (K : Finset I) {h : ℕ} (lo : h ≤ (used a).card) :
    h ≤ K.card + outside a K := by
  rw [face_identity]
  omega

/-- The support-size bound makes the corrected degree a supporting functional. -/
theorem on_face_iff (a : I → ℕ) (K : Finset I) {h : ℕ} (lo : h ≤ (used a).card) :
    K.card + outside a K = h ↔
      (used a).card = h ∧ K ⊆ used a ∧ repeated a ⊆ K := by
  rw [face_identity]
  constructor
  · intro eq
    have miss : (K \ used a).card = 0 := by omega
    have zero : ∑ i ∈ used a \ K, (a i - 1) = 0 := by omega
    have each := Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ used a \ K) => Nat.zero_le (a i - 1)) |>.mp zero
    refine ⟨by omega, sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp miss), ?_⟩
    intro i hi
    by_contra no
    have large := mem_repeated.mp hi
    have tiny := each i (mem_sdiff.mpr ⟨mem_used.mpr (by omega), no⟩)
    omega
  · rintro ⟨eq, inside, rep⟩
    have miss := sdiff_eq_empty_iff_subset.mpr inside
    have zero : ∑ i ∈ used a \ K, (a i - 1) = 0 := by
      apply sum_eq_zero
      intro i hi
      have small : ¬ 1 < a i := fun h => (mem_sdiff.mp hi).2 (rep (mem_repeated.mpr h))
      omega
    simp [eq,miss,zero]

theorem padded_face (a : I → ℕ) {r : ℕ} (lower : (repeated a).card ≤ r)
    (upper : r ≤ (used a).card) :
    ∃ K : Finset I, K.card = r ∧ K.card + outside a K = (used a).card := by
  have incl : repeated a ⊆ used a := fun _ hi =>
    mem_used.mpr (Nat.zero_lt_of_lt (mem_repeated.mp hi))
  obtain ⟨K, hr, hs, card⟩ := exists_subsuperset_card_eq incl lower upper
  exact ⟨K, card, (on_face_iff a K (le_refl _)).mpr ⟨rfl, hs, hr⟩⟩

def clamp (K : Finset I) (a : I → ℕ) (i : I) := if i ∈ K then 1 else a i
def indicator (S : Finset I) (i : I) : ℕ := if i ∈ S then 1 else 0

theorem clamp_on_face (a : I → ℕ) (K : Finset I) {h : ℕ} (lo : h ≤ (used a).card)
    (eq : K.card + outside a K = h) : clamp K a = indicator (used a) := by
  obtain ⟨_, inside, rep⟩ := (on_face_iff a K lo).mp eq
  funext i
  by_cases hi : i ∈ K
  · simp [clamp, indicator, hi, inside hi]
  · have small : ¬1 < a i := fun hx => hi (rep (mem_repeated.mpr hx))
    by_cases hu : i ∈ used a
    · have pos := mem_used.mp hu
      have hi1 : a i = 1 := by omega
      simp [clamp, indicator, hi, hi1, hu]
    · have nz : ¬0 < a i := fun hx => hu (mem_used.mpr hx)
      have hi0 : a i = 0 := by omega
      simp [clamp, indicator, hi, hi0, hu]

/-- Exact recovery from the Boolean tests through weight h, allowing arbitrary
extra positive supports above that layer. Each correcting face has exactly r pins. -/
theorem exact_face_union (A : Set (I → ℕ)) (F : Set (Finset I)) {h r : ℕ}
    (uniform : ∀ S ∈ F, S.card = h) (rh : r ≤ h)
    (tests : ∀ X : Finset I, X.card ≤ h → ((∃ a ∈ A, used a ⊆ X) ↔ X ∈ F))
    (realizes : ∀ S ∈ F, ∃ a ∈ A, used a = S ∧ (repeated a).card ≤ r)
    (z : I → ℕ) :
    (∃ S ∈ F, z = indicator S) ↔
      ∃ K : Finset I, K.card = r ∧ ∃ a ∈ A,
        K.card + outside a K = h ∧ z = clamp K a := by
  have lower (a : I → ℕ) (ha : a ∈ A) : h ≤ (used a).card := by
    by_contra no
    have sm : (used a).card ≤ h := by omega
    have mem := (tests (used a) sm).mp ⟨a, ha, fun _ e => e⟩
    have eq := uniform _ mem
    omega
  constructor
  · rintro ⟨S, hs, rfl⟩
    obtain ⟨a, ha, eq, small⟩ := realizes S hs
    have card : (used a).card = h := by rw [eq]; exact uniform S hs
    obtain ⟨K, kr, face⟩ := padded_face a small (by omega)
    refine ⟨K, kr, a, ha, face.trans card, ?_⟩
    rw [clamp_on_face a K (lower a ha) (face.trans card), eq]
  · rintro ⟨K, _, a, ha, face, rfl⟩
    have card := ((on_face_iff a K (lower a ha)).mp face).1
    have target := (tests (used a) card.le).mp ⟨a, ha, fun _ e => e⟩
    exact ⟨used a, target, clamp_on_face a K (lower a ha) face⟩

end PermanentDecision
#print axioms PermanentDecision.on_face_iff
#print axioms PermanentDecision.padded_face
#print axioms PermanentDecision.exact_face_union
