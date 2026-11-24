import WindowCore997

/-! The private-gate cutoff centered on an arbitrary Boolean assignment.
Clamping inputs is encoded in the tested assignments, so the gate count stays
exact even when a surviving output is a raw, repeated, or out-of-bounds wire. -/
namespace LimitedNegation.Project
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.Window997

def responses {n} (C : Circuit) (base : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (bits (base ∪ {p})) w=true)

lemma mem_responses {n} (C : Circuit) (base : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ responses C base w ↔ value C (bits (base ∪ {p})) w=true := by simp [responses]

lemma real_response_gate {n} (C : Circuit) (base : Finset (Fin n)) (w : ℕ)
    (absent : value C (bits base) w=false) (two : 2≤(responses C base w).card) :
    n≤w ∧ w<n+C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w,hw⟩
    have p0 : p ∉ base := by
      change value C (bits base) p=false at absent
      simpa [input_value,bits] using absent
    have sub : responses C base w ⊆ {p} := by
      intro q hq
      have h := (mem_responses C base w q).mp hq
      change value C (bits (base∪{q})) p = true at h
      simpa [input_value,bits,p0,eq_comm] using h
    have := Finset.card_le_card sub
    simp at this
    omega
  · by_contra! hw
    have hz : responses C base w=∅ := by
      ext p; simp [mem_responses, missing_value C _ w hw]
    simp [hz] at two

noncomputable def charges {n} (C : Circuit) (base S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter (fun w => value C (bits base) w=false ∧
    responses C base w ⊆ S ∧ 2≤(responses C base w).card)

theorem count_above {n k} (C : Circuit) (hg : monoG C) (base S : Finset (Fin n)) (o : ℕ)
    (hpos : ∀ p ∈ S, value C (bits (base∪{p})) o = true)
    (hneg : ∀ A : Finset (Fin n), A.card < k → Disjoint A S → value C (bits (base∪A)) o = false) :
    min k S.card ≤ (charges C base S).card + 1 := by
  classical
  let G := charges C base S
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hd,hc,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have h := Finset.card_filter_le G (· < n+C.size)
    simp only [Finset.card_singleton] at hc
    omega
  by_contra! hsmall
  change G.card + 1 < min k S.card at hsmall
  let clean (w : ℕ) : Finset (Fin n) := if value C (bits base) w = false ∧ responses C base w ⊆ S then responses C base w else ∅
  have clean_one (w) (hw : w ∈ B) : (clean w).card ≤ 1 := by
    by_cases h : value C (bits base) w = false ∧ responses C base w ⊆ S
    · simp only [clean,ite_eq_left h]
      by_contra! hn
      have hn' : 2 ≤ (responses C base w).card := by omega
      exact Finset.disjoint_left.mp hd hw (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (real_response_gate C base w h.1 hn'),h.1,h.2,hn'⟩)
    · simp [clean,h]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 clean_one
    simp only [mul_one] at h
    omega
  obtain ⟨p,hp,hpB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let bad := B.filter fun w => ¬ responses C base w ⊆ S
  have hex (d : {w // w ∈ bad}) : ∃ q : Fin n, q ∈ responses C base d.val ∧ q ∉ S := by
    have := (Finset.mem_filter.mp d.property).2
    exact Finset.not_subset.mp this
  choose f hf using hex
  let Z := Finset.univ.image f
  have hz : Z.card < k := by
    have hz' := Finset.card_image_le (s := (Finset.univ : Finset {w // w ∈ bad})) (f := f)
    simp only [Finset.card_univ,Fintype.card_coe] at hz'
    have hb' := Finset.card_filter_le B (fun w => ¬ responses C base w ⊆ S)
    change bad.card ≤ B.card at hb'
    change (Finset.univ.image f).card < k
    omega
  have hdZ : Disjoint Z S := by
    refine Finset.disjoint_left.mpr ?_
    rintro q hq hs
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hq
    exact (hf d).2 hs
  have hfire : value C (bits (base∪Z)) o = true := by
    apply hcut (bits (base∪{p})) (bits (base∪Z)) _ o (Finset.mem_singleton_self _) (hpos p hp)
    intro w hw hv
    by_cases hzero : value C (bits base) w = true
    · exact mono_bits C hg (Finset.subset_union_left) w hzero
    have hfalse : value C (bits base) w = false := Bool.eq_false_iff.mpr hzero
    by_cases hs : responses C base w ⊆ S
    · exact False.elim (hpB (Finset.mem_biUnion.mpr
        ⟨w,hw, by simpa only [clean,ite_eq_left (And.intro hfalse hs)] using (mem_responses C base w p).mpr hv⟩))
    · let d : {w // w ∈ bad} := ⟨w,Finset.mem_filter.mpr ⟨hw,hs⟩⟩
      apply mono_bits C hg (A:=base∪{f d}) (B:=base∪Z) _ w ((mem_responses C base w (f d)).mp (hf d).1)
      exact Finset.union_subset_union_right (Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩))
  rw [hneg Z hz hdZ] at hfire
  contradiction

/-- Pack an arbitrary subfamily of the pairwise-linear outputs. -/
theorem sum_above {n m k r : ℕ} (C : Circuit) (hg : monoG C) (base : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (linear : linear997 S)
    (survive : Finset (Fin m))
    (lengths : ∀ i∈survive, (S i).card=r)
    (hpos : ∀ i∈survive, ∀ p∈S i, value C (bits (base∪{p})) (o i)=true)
    (hneg : ∀ i∈survive, ∀ A : Finset (Fin n), A.card<k → Disjoint A (S i) →
      value C (bits (base∪A)) (o i)=false) :
    survive.card*(min k r-1) ≤ C.size := by
  classical
  let sets (i : Fin m) := if i∈survive then charges C base (S i) else ∅
  have sep {i j : Fin m} (ne : i≠j) : Disjoint (sets i) (sets j) := by
    by_cases hi : i∈survive <;> by_cases hj : j∈survive <;> simp [sets,hi,hj]
    refine Finset.disjoint_left.mpr ?_
    intro w wi wj
    have a := (Finset.mem_filter.mp wi).2
    have b := (Finset.mem_filter.mp wj).2
    have sub : responses C base w ⊆ S i ∩ S j :=
      fun v hv => Finset.mem_inter.mpr ⟨a.2.1 hv,b.2.1 hv⟩
    have lo := a.2.2
    have up := (Finset.card_le_card sub).trans (linear i j ne)
    omega
  have within (i) (w : ℕ) (hw : w∈sets i) : w∈Finset.Ico n (n+C.size) := by
    by_cases hi : i∈survive
    · apply (Finset.mem_filter.mp (by simpa [sets,hi] using hw : w∈charges C base (S i))).1
    · simp [sets,hi] at hw
  have price (i) : (if i∈survive then min k r-1 else 0) ≤ (sets i).card := by
    by_cases hi : i∈survive
    · have h := count_above C hg base (S i) (o i) (hpos i hi) (hneg i hi)
      rw [lengths i hi] at h
      simp [sets,hi]
      omega
    · simp [sets,hi]
  have total := pack997 (Finset.Ico n (n+C.size)) ∅ sets (fun i => if i∈survive then min k r-1 else 0)
    (by simp) within (by simp) (fun i j hij => sep hij) price
  simpa [Nat.card_Ico,Finset.sum_ite_mem,Finset.inter_comm,Nat.mul_comm] using total

end LimitedNegation.Project
#print axioms LimitedNegation.Project.count_above
#print axioms LimitedNegation.Project.sum_above
