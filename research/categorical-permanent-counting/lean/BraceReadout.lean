import Mathlib.Tactic

/-! Category readouts of a bipartite multigraph. Physical edges may be parallel.
The matching system only needs pair extension, matching uniqueness at rows and
columns, and two-row neighborhood expansion for rectangle avoidance. -/
namespace BraceReadout

variable {E I J C : Type*}

def Independent (row : E → I) (col : E → J) (matchings : Finset E → Prop) : Prop :=
  ∀ M, matchings M → ∀ a ∈ M, ∀ b ∈ M, a ≠ b → row a ≠ row b ∧ col a ≠ col b

def Extend (row : E → I) (col : E → J) (matchings : Finset E → Prop) : Prop :=
  ∀ a b, row a ≠ row b → col a ≠ col b → ∃ M, matchings M ∧ a ∈ M ∧ b ∈ M

def Avoid (row : E → I) (col : E → J) (matchings : Finset E → Prop) : Prop :=
  ∀ r s j k, r ≠ s → j ≠ k → ∃ M, matchings M ∧
    ∀ e ∈ M, ¬ ((row e = r ∨ row e = s) ∧ (col e = j ∨ col e = k))

theorem distinct_representatives [DecidableEq J] {U V : Finset J} (u : U.Nonempty) (v : V.Nonempty)
    (hh : 2 ≤ (U ∪ V).card) :
    ∃ a ∈ U, ∃ b ∈ V, a ≠ b := by
  classical
  obtain ⟨a, ha⟩ := u
  obtain ⟨b, hb⟩ := v
  by_contra! hn
  have hab := hn a ha b hb
  have incl : U ∪ V ⊆ {a} := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simpa [hab] using hn x hx b hb
    · simpa using (hn a ha x hx).symm
  have hc := Finset.card_le_card incl
  simp at hc
  omega

/-- Two-row Hall expansion outside two columns supplies nonconflicting neighbors. -/
theorem avoid_from_neighbors [DecidableEq J]
    {row : E → I} {col : E → J} {matchings : Finset E → Prop}
    (hind : Independent row col matchings) (hext : Extend row col matchings)
    (N : I → Finset J) (realize : ∀ i j, j ∈ N i → ∃ e, row e = i ∧ col e = j)
    (three : ∀ i, 3 ≤ (N i).card)
    (four : ∀ i i', i ≠ i' → 4 ≤ (N i ∪ N i').card) : Avoid row col matchings := by
  classical
  intro r s j k hrs hjk
  let D : Finset J := {j, k}
  have dc : D.card = 2 := by simp [D, hjk]
  have one (i : I) : (N i \ D).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_le_card (Finset.inter_subset_right (s₁ := N i) (s₂ := D))
    have hc' := Finset.card_sdiff_add_card_inter (N i) D
    have ht := three i
    omega
  have join : 2 ≤ ((N r \ D) ∪ (N s \ D)).card := by
    have heq : (N r \ D) ∪ (N s \ D) = (N r ∪ N s) \ D := by ext; simp; tauto
    rw [heq]
    have hc := Finset.card_le_card (Finset.inter_subset_right (s₁ := N r ∪ N s) (s₂ := D))
    have hc' := Finset.card_sdiff_add_card_inter (N r ∪ N s) D
    have ht := four r s hrs
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := distinct_representatives (one r) (one s) join
  obtain ⟨x, hxr, hxa⟩ := realize r a (Finset.mem_sdiff.mp ha).1
  obtain ⟨y, hys, hyb⟩ := realize s b (Finset.mem_sdiff.mp hb).1
  obtain ⟨M, hM, hx, hy⟩ := hext x y (by simpa [hxr,hys] using hrs)
    (by simpa [hxa,hyb] using hab)
  refine ⟨M, hM, ?_⟩
  intro e he bad
  have same (z : E) (hz : z ∈ M) (h : row e = row z) : e = z := by
    by_contra neq
    exact (hind M hM e he z hz neq).1 h
  obtain ⟨hr | hs, ht⟩ := bad
  · obtain rfl := same x hx (hr.trans hxr.symm)
    exact (Finset.mem_sdiff.mp ha).2 (by simpa [D, hxa] using ht)
  · obtain rfl := same y hy (hs.trans hys.symm)
    exact (Finset.mem_sdiff.mp hb).2 (by simpa [D, hyb] using ht)

def Pure (tag : E → Option C) (matchings : Finset E → Prop) : Prop :=
  ∀ M, matchings M → ∃ c, (∃ e ∈ M, tag e = some c) ∧
    ∀ e ∈ M, ∀ d, tag e = some d → d = c

def Double (row : E → I) (col : E → J) (tag : E → Option C) (c : C) : Prop :=
  ∃ a b, tag a = some c ∧ tag b = some c ∧ row a ≠ row b ∧ col a ≠ col b

theorem conflict {row : E → I} {col : E → J} {matchings : Finset E → Prop}
    {tag : E → Option C} (hext : Extend row col matchings) (hp : Pure tag matchings)
    {a b c d} (ha : tag a = some c) (hb : tag b = some d) (hcd : c ≠ d) :
    row a = row b ∨ col a = col b := by
  by_contra! hn
  obtain ⟨M,hM,am,bm⟩ := hext a b hn.1 hn.2
  obtain ⟨_, _, unique⟩ := hp M hM
  exact hcd ((unique a am c ha).trans (unique b bm d hb).symm)

private theorem corners {r s x : I} {c d y : J} (hrs : r ≠ s) (hcd : c ≠ d)
    (h : x = r ∨ y = c) (h' : x = s ∨ y = d) :
    (x = r ∧ y = d) ∨ (x = s ∧ y = c) := by grind

theorem only_one_double {row : E → I} {col : E → J} {matchings : Finset E → Prop}
    {tag : E → Option C} (hext : Extend row col matchings) (ha : Avoid row col matchings)
    (hp : Pure tag matchings) {c d} (hc : Double row col tag c)
    (hd : Double row col tag d) : c = d := by
  by_contra hcd
  obtain ⟨p,q,pt,qt,pr,pc⟩ := hc
  obtain ⟨u,v,ut,vt,ur,uc⟩ := hd
  have loc {e : E} {w : C} (et : tag e = some w) (ew : w ≠ c) :
      (row e = row p ∧ col e = col q) ∨ (row e = row q ∧ col e = col p) :=
    corners pr pc (conflict hext hp et pt ew) (conflict hext hp et qt ew)
  have ul := loc ut (Ne.symm hcd)
  have vl := loc vt (Ne.symm hcd)
  obtain ⟨M,hM,avoid⟩ := ha (row p) (row q) (col p) (col q) pr pc
  obtain ⟨w,⟨e,em,et⟩,_⟩ := hp M hM
  apply avoid e em
  by_cases eqc : w = c
  · subst w
    have pos := corners ur uc (conflict hext hp et ut hcd) (conflict hext hp et vt hcd)
    grind
  · have pos := loc et eqc
    grind

/-- If no two disjoint edges of a color can occur, its hit count on every
matching that has the color is exactly one. -/
private theorem unique_tag {row : E → I} {col : E → J} {matchings : Finset E → Prop}
    {tag : E → Option C} (hind : Independent row col matchings)
    {c M} (hM : matchings M) (hc : ¬ Double row col tag c)
    {p e} (hp : p ∈ M) (he : e ∈ M) (pt : tag p = some c) (et : tag e = some c) : e = p := by
  by_contra hne
  obtain ⟨hr,hq⟩ := hind M hM e he p hp hne
  exact hc ⟨e,p,et,pt,hr,hq⟩

open scoped Classical in
/-- Joint affine readouts exist. For each color the coefficients are integers:
the ordinary colors are counted, the exceptional color is one minus the count
of every other tagged edge. The constant and weights are fixed across matchings. -/
theorem affine_readout {row : E → I} {col : E → J} {matchings : Finset E → Prop}
    {tag : E → Option C} (hind : Independent row col matchings)
    (hext : Extend row col matchings) (ha : Avoid row col matchings)
    (hp : Pure tag matchings) (c : C) :
    ∃ (b : ℤ) (weight : E → ℤ), ∀ (M : Finset E), matchings M →
      (if ∃ e ∈ M, tag e = some c then 1 else 0 : ℤ) = b + ∑ e ∈ M, weight e := by
  classical
  by_cases dbl : Double row col tag c
  · let w : E → ℤ := fun e => if ∃ d, tag e = some d ∧ d ≠ c then -1 else 0
    refine ⟨1, w, ?_⟩
    intro M hM
    obtain ⟨d, ⟨p,hpM,pt⟩, mon⟩ := hp M hM
    by_cases eq : d = c
    · subst d
      have hz (e) (he : e ∈ M) : w e = 0 := by
        have hh : ¬ ∃ d, tag e = some d ∧ d ≠ c := by
          rintro ⟨d, hd, hne⟩
          exact hne (mon e he d hd)
        simp [w, hh]
      have hit : ∃ e ∈ M, tag e = some c := ⟨p,hpM,pt⟩
      simp [hit, Finset.sum_eq_zero hz]
    · have nd : ¬ Double row col tag d := fun dd => eq (only_one_double hext ha hp dd dbl)
      have nohit : ¬ ∃ e ∈ M, tag e = some c := by
        rintro ⟨e,he,et⟩
        exact eq (mon _ he _ et).symm
      have sole (e) (he : e ∈ M) (hne : e ≠ p) : w e = 0 := by
        have hh : ¬ ∃ d', tag e = some d' ∧ d' ≠ c := by
          rintro ⟨d',et,_⟩
          obtain rfl := mon e he d' et
          exact hne (unique_tag hind hM nd hpM he pt et)
        simp [w, hh]
      rw [Finset.sum_eq_single p sole (by simp [hpM])]
      simp only [nohit, ite_false]
      simp [w, show ∃ d, tag p = some d ∧ d ≠ c from ⟨d,pt,eq⟩]
  · let w : E → ℤ := fun e => if tag e = some c then 1 else 0
    refine ⟨0, w, ?_⟩
    intro M hM
    by_cases hh : ∃ e ∈ M, tag e = some c
    · obtain ⟨p,hpM,pt⟩ := hh
      have sole (e) (he : e ∈ M) (hne : e ≠ p) : w e = 0 := by
        have hn : tag e ≠ some c := fun et => hne (unique_tag hind hM dbl hpM he pt et)
        simp [w, hn]
      have hit : ∃ e ∈ M, tag e = some c := ⟨p,hpM,pt⟩
      rw [Finset.sum_eq_single p sole (by simp [hpM])]
      simp [hit, w, pt]
    · have hz (e) (he : e ∈ M) : w e = 0 := by
        simp [w, show tag e ≠ some c from fun et => hh ⟨e,he,et⟩]
      simp [hh, Finset.sum_eq_zero hz]

#print axioms avoid_from_neighbors
#print axioms only_one_double
#print axioms affine_readout

end BraceReadout
