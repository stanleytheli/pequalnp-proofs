import Mathlib.Tactic

/-!
On a rectangle of compatible choices, every pair of choices must supply exactly
one category. Completing both side readouts uses one extra dummy category.
-/
namespace CategoricalCut

variable {A B C : Type*}

def Offers (l : A → Option C) (c : C) : Prop := ∃ a, l a = some c

def Flexible (l : A → Option C) : Prop :=
  ∃ c d, c ≠ d ∧ Offers l c ∧ Offers l d

def Compatible (l : A → Option C) (r : B → Option C) : Prop :=
  ∀ a b, ∃ c, (l a = some c ∨ r b = some c) ∧
    ∀ d, l a = some d ∨ r b = some d → d = c

theorem Compatible.cross {l : A → Option C} {r : B → Option C}
    (h : Compatible l r) {c d} (hc : Offers l c) (hd : Offers r d) : c = d := by
  obtain ⟨a, ha⟩ := hc
  obtain ⟨b, hb⟩ := hd
  obtain ⟨_, _, hu⟩ := h a b
  exact (hu _ (.inl ha)).trans (hu _ (.inr hb)).symm

theorem Compatible.silent_right {l : A → Option C} {r : B → Option C}
    (h : Compatible l r) (hf : Flexible l) : ∀ c, ¬ Offers r c := by
  obtain ⟨a, b, hab, ha, hb⟩ := hf
  exact fun _ hc => hab ((h.cross ha hc).trans (h.cross hb hc).symm)

theorem Compatible.silent_left {l : A → Option C} {r : B → Option C}
    (h : Compatible l r) (hf : Flexible r) : ∀ c, ¬ Offers l c := by
  obtain ⟨a, b, hab, ha, hb⟩ := hf
  exact fun _ hc => hab ((h.cross hc ha).symm.trans (h.cross hc hb))

theorem rigid_unique {l : A → Option C} (h : ¬ Flexible l)
    {c d} (hc : Offers l c) (hd : Offers l d) : c = d := by
  by_contra hn
  exact h ⟨c, d, hn, hc, hd⟩

/-- If needed, color the cut edge with the unique possible color, or with the
fresh dummy color. The outer option permits leaving the edge unmarked. -/
noncomputable def marker (l : A → Option C) : Option (Option C) := by
  classical
  exact if Flexible l then none else
    if ho : ∃ c, Offers l c then some (some (Classical.choose ho)) else some none

theorem marker_real {l : A → Option C} (a : A) (c : C) :
    (l a = some c ∨ marker l = some (some c)) ↔
      ((Flexible l ∧ l a = some c) ∨ (¬ Flexible l ∧ Offers l c)) := by
  classical
  by_cases hf : Flexible l
  · simp [marker, hf]
  by_cases ho : ∃ d, Offers l d
  · have hu : Offers l c ↔ Classical.choose ho = c :=
      ⟨fun hc => rigid_unique hf (Classical.choose_spec ho) hc,
       fun hc => hc ▸ Classical.choose_spec ho⟩
    simp [marker, hf, ho, ← hu]
    exact fun ha => ⟨a, ha⟩
  · have hn : ¬ Offers l c := fun hc => ho ⟨c, hc⟩
    have hl : l a ≠ some c := fun ha => hn ⟨a, ha⟩
    simp [marker, hf, ho, hn, hl]

/-- A completed side always gives a unique category on any actual side choice.
The witness from the other side guarantees that a flexible side never goes blank. -/
theorem marker_complete {l : A → Option C} {r : B → Option C}
    (h : Compatible l r) (a : A) (b : B) :
    ∃! q : Option C, (∃ c, l a = some c ∧ q = some c) ∨ marker l = some q := by
  classical
  by_cases hf : Flexible l
  · obtain ⟨c, hc, _⟩ := h a b
    have ha : l a = some c := hc.resolve_right (fun hb => h.silent_right hf c ⟨b, hb⟩)
    refine ⟨some c, .inl ⟨c, ha, rfl⟩, ?_⟩
    intro q hq
    rcases hq with ⟨d, hd, rfl⟩ | hm
    · simpa [ha] using hd.symm
    · simp [marker, hf] at hm
  by_cases ho : ∃ c, Offers l c
  · let c := Classical.choose ho
    refine ⟨some c, .inr (by simp [marker, hf, ho, c]), ?_⟩
    intro q hq
    rcases hq with ⟨d, hd, rfl⟩ | hm
    · exact congrArg some (rigid_unique hf ⟨a, hd⟩ (Classical.choose_spec ho))
    · simpa [marker, hf, ho, c] using hm.symm
  · refine ⟨none, .inr (by simp [marker, hf, ho]), ?_⟩
    intro q hq
    rcases hq with ⟨d, hd, _⟩ | hm
    · exact (ho ⟨d, a, hd⟩).elim
    · simpa [marker, hf, ho] using hm.symm

noncomputable def bit (p : Prop) : ℕ := by classical exact if p then 1 else 0

theorem indicator_identity {l : A → Option C} {r : B → Option C}
    (h : Compatible l r) (a : A) (b : B) (c : C) :
    bit (l a = some c ∨ r b = some c) +
      bit (Offers l c ∧ Offers r c) =
    bit (l a = some c ∨ marker l = some (some c)) +
      bit (r b = some c ∨ marker r = some (some c)) := by
  classical
  rw [marker_real, marker_real]
  by_cases hl : Flexible l
  · have hr := h.silent_right hl c
    have hb : r b ≠ some c := fun hh => hr ⟨b, hh⟩
    simp [hl, hr, hb, bit]
  by_cases hr : Flexible r
  · have hnl := h.silent_left hr c
    have ha : l a ≠ some c := fun hh => hnl ⟨a, hh⟩
    simp [hr, hnl, ha, bit]
  have iff' : (l a = some c ∨ r b = some c) ↔ (Offers l c ∨ Offers r c) := by
    constructor
    · rintro (ha | hb)
      · exact .inl ⟨a, ha⟩
      · exact .inr ⟨b, hb⟩
    · intro hc
      obtain ⟨d, hd, _⟩ := h a b
      suffices d = c by simpa [this] using hd
      rcases hd with ha | hb <;> rcases hc with lc | rc
      · exact rigid_unique hl ⟨a, ha⟩ lc
      · exact h.cross ⟨a, ha⟩ rc
      · exact (h.cross lc ⟨b, hb⟩).symm
      · exact rigid_unique hr ⟨b, hb⟩ rc
  simp only [hl, hr, false_and, not_false_eq_true, true_and, false_or, iff']
  by_cases a' : Offers l c <;> by_cases b' : Offers r c <;> simp [bit, a', b']

#print axioms marker_complete
#print axioms indicator_identity

end CategoricalCut
