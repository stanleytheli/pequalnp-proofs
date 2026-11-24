import OneNotRefundCases
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
theorem regional_count997 {n k} (C : Circuit) (hg : monoG C) (P S : Finset (Fin n)) (z o : ℕ)
    (hz : ∀ A : Finset (Fin n), value C (bits A) z = true)
    (hpos : ∀ p ∈ S ∩ P, value C (bits {p}) o = true)
    (hneg : ∀ A : Finset (Fin n), A ⊆ P → A.card < k → Disjoint A S → value C (bits A) o = false) :
    min k (S ∩ P).card ≤ (restricted997 C P S z).card + 1 := by
  classical
  let G := restricted997 C P S z
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size := Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  obtain ⟨B,hd,hc,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have h := Finset.card_filter_le G (· < n+C.size)
    simp only [Finset.card_singleton] at hc
    omega
  by_contra! hsmall
  change G.card + 1 < min k (S ∩ P).card at hsmall
  let clean (w : ℕ) : Finset (Fin n) := if value C (bits (∅ : Finset (Fin n))) w = false ∧ ones C w ∩ P ⊆ S then ones C w ∩ P else ∅
  have clean_one (w) (hw : w ∈ B) : (clean w).card ≤ 1 := by
    by_cases h : value C (bits (∅ : Finset (Fin n))) w = false ∧ ones C w ∩ P ⊆ S
    · simp only [clean,ite_eq_left h]
      by_contra! hn
      have hn' : 2 ≤ (ones C w ∩ P).card := by omega
      have h2 := hn'.trans (Finset.card_le_card (Finset.inter_subset_left (s₁:=ones C w) (s₂:=P)))
      have ne : w ≠ z := by
        rintro rfl
        exact Bool.false_ne_true (h.1.symm.trans (hz ∅))
      exact Finset.disjoint_left.mp hd hw (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne,Finset.mem_Ico.mpr (two_gate C w h2)⟩,h.2,hn'⟩)
    · simp [clean,h]
  have hcover : (B.biUnion clean).card < (S ∩ P).card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 clean_one
    simp only [mul_one] at h
    omega
  obtain ⟨p,hp,hpB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let bad := B.filter fun w => ¬ ones C w ∩ P ⊆ S
  have hex (d : {w // w ∈ bad}) : ∃ q : Fin n, q ∈ ones C d.val ∩ P ∧ q ∉ S := by
    have := (Finset.mem_filter.mp d.property).2
    exact Finset.not_subset.mp this
  choose f hf using hex
  let Z := Finset.univ.image f
  have hz : Z.card < k := by
    have hz' := Finset.card_image_le (s := (Finset.univ : Finset {w // w ∈ bad})) (f := f)
    simp only [Finset.card_univ,Fintype.card_coe] at hz'
    have hb' := Finset.card_filter_le B (fun w => ¬ ones C w ∩ P ⊆ S)
    change bad.card ≤ B.card at hb'
    change (Finset.univ.image f).card < k
    omega
  have hdZ : Disjoint Z S := by
    refine Finset.disjoint_left.mpr ?_
    rintro q hq hs
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hq
    exact (hf d).2 hs
  have hfire : value C (bits Z) o = true := by
    apply hcut (bits {p}) (bits Z) _ o (Finset.mem_singleton_self _) (hpos p hp)
    intro w hw hv
    by_cases hzero : value C (bits (∅ : Finset (Fin n))) w = true
    · exact mono_bits C hg (Finset.empty_subset Z) w hzero
    have hfalse : value C (bits (∅ : Finset (Fin n))) w = false := Bool.eq_false_iff.mpr hzero
    by_cases hs : ones C w ∩ P ⊆ S
    · exact False.elim (hpB (Finset.mem_biUnion.mpr
        ⟨w,hw, by simpa only [clean,ite_eq_left (And.intro hfalse hs)] using Finset.mem_inter.mpr ⟨(mem_ones C w p).mpr hv,(Finset.mem_inter.mp hp).2⟩⟩))
    · let d : {w // w ∈ bad} := ⟨w,Finset.mem_filter.mpr ⟨hw,hs⟩⟩
      apply mono_bits C hg (A:={f d}) (B:=Z) _ w ((mem_ones C w (f d)).mp (Finset.mem_inter.mp (hf d).1).1)
      exact Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩)
  have hZP : Z ⊆ P := by
    intro q hq
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_inter.mp (hf d).1).2
  rw [hneg Z hZP hz hdZ] at hfire
  contradiction


/-- A chain of subcubes admits different first-activation thresholds for different rows. -/
theorem chain_first997 {m n} (C : Circuit) (S P : Fin m → Finset (Fin n)) (o K : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (chain : ∀ i j, P i ⊆ P j ∨ P j ⊆ P i)
    (local_off : ∀ i (Z : Finset (Fin n)), Z ⊆ P i → Z.card < K i → Disjoint Z (S i) →
      value (prefix997 C t) (bits Z) (head997 n C t) = false) :
    Y.card + ∑ i, (min (K i) ((S i) ∩ (P i)).card - 1) ≤ C.size := by
  classical
  let B := prefix997 C t
  let z := n+t.val
  let R := insert z (dark B Y)
  have htN : t.val<C.size := t.isLt
  have hsub (w) (hw : w ∈ dark B Y) : n≤w ∧ w<z := by
    simpa [B,z] using Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have bound : Y.card ≤ R.card := by
    have hn : z ∉ dark B Y := fun hz => lt_irrefl _ (hsub z hz).2
    simpa [R,Finset.card_insert_of_notMem hn] using first_weight B (prefix_mono997 C t hg) Y _ hon hoff
  have hR : R ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|h
    · exact Finset.mem_Ico.mpr ⟨by dsimp [z];omega,by dsimp [z];omega⟩
    · have hh := hsub w h; exact Finset.mem_Ico.mpr ⟨hh.1,by dsimp [z] at hh;omega⟩
  have emptySupp (w) (hw : w∈dark B Y) : ones (n:=n) (pin997 C t true) w = ∅ := by
    have he : ones (n:=n) (pin997 C t true) w = ones B w := by
      ext p; simp only [mem_ones]; rw [pin_prefix997 C t true _ w (hsub w hw).2]
    exact he.trans (Finset.mem_filter.mp hw).2.2

  let C₁ := pin997 C t true
  let A (i) := restricted997 C₁ (P i) (S i) z
  let c (i) := min (K i) ((S i) ∩ (P i)).card - 1
  have inside (i) : A i ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    simpa [C₁] using (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  have reserved (i) : Disjoint (A i) R := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hwR
    obtain ⟨hne,ha⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp hwR with rfl|hd
    · exact (Finset.mem_erase.mp hne).1 rfl
    · have hh := ha.2; simp [C₁,emptySupp w hd] at hh
  have separate (i j : Fin m) (hne : i ≠ j) (hij : P i ⊆ P j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    obtain ⟨his,hc2⟩ := (Finset.mem_filter.mp hi).2
    have hjs := (Finset.mem_filter.mp hj).2.1
    have hsub : ones C₁ w ∩ P i ⊆ S i ∩ S j := by
      intro p hp
      have hh := Finset.mem_inter.mp hp
      exact Finset.mem_inter.mpr ⟨his hp,hjs (Finset.mem_inter.mpr ⟨hh.1,hij hh.2⟩)⟩
    have bor := (Finset.card_le_card hsub).trans (hl i j hne)
    omega
  have sep (i j : Fin m) (hne : i ≠ j) : Disjoint (A i) (A j) := by
    rcases chain i j with h|h
    · exact separate i j hne h
    · exact (separate j i hne.symm h).symm
  have per (i) : c i ≤ (A i).card := by
    have ha := regional_count997 C₁ (pin_mono997 C t hg true) (P i) (S i) z (o i)
      (fun Z => pin_wire997 C t true (bits Z))
      (fun p hp => (sandwich997 C t ht hg _ _).2 (by simpa [hc,bits] using (Finset.mem_inter.mp hp).1))
      (k:=K i) (by
        intro Z hZ hk hd
        have hpin := pin_on997 C t ht (bits Z) false (local_off i Z hZ hk hd) (o i)
        change value C (bits Z) (o i) = value C₁ (bits Z) (o i) at hpin
        rw [←hpin,hc]
        simp only [bits,decide_eq_true_eq,decide_eq_false_iff_not]
        rintro ⟨p,hp,hz'⟩
        exact Finset.disjoint_left.mp hd hz' hp)
    change min (K i) ((S i) ∩ (P i)).card - 1 ≤ (restricted997 C₁ (P i) (S i) z).card
    omega
  have total := pack997 _ R A c hR inside reserved sep per
  exact (Nat.add_le_add_right bound (∑ i, c i)).trans (by simpa [Nat.card_Ico] using total)

#print axioms chain_first997
/-- If each disjoint row has the full required local rank gap away from itself
inside their common ambient B, the weighted count already holds without refunds. -/
theorem local_rank_exact997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y B : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hcover : ∀ i, Disjoint (S i) Y → S i ⊆ B)
    (hlocal : ∀ i, Disjoint (S i) Y → ∀ Z : Finset (Fin n), Z ⊆ B → Z.card < (S i).card →
      Disjoint Z (S i) → value (prefix997 C t) (bits Z) (head997 n C t) = false) :
    Y.card + (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ C.size + m := by
  classical
  let P (i) := if Disjoint (S i) Y then B else Finset.univ
  let K (i) := if Disjoint (S i) Y then (S i).card else Y.card
  have hchain (i j : Fin m) : P i ⊆ P j ∨ P j ⊆ P i := by
    by_cases hi : Disjoint (S i) Y <;> by_cases hj : Disjoint (S j) Y <;> simp [P,hi,hj]
  have hloc (i) (Z : Finset (Fin n)) (hZ : Z ⊆ P i) (hcard : Z.card < K i) (hd : Disjoint Z (S i)) :
      value (prefix997 C t) (bits Z) (head997 n C t) = false := by
    by_cases h : Disjoint (S i) Y
    · exact hlocal i h Z (by simpa [P,h] using hZ) (by simpa [K,h] using hcard) hd
    · exact hoff Z (by simpa [K,h] using hcard)
  have hmain := chain_first997 C S P o K t ht hg hl hc Y hon hoff hchain hloc
  have hrow (i) : (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card)
      ≤ (min (K i) ((S i) ∩ P i).card - 1) + 1 := by
    by_cases h : Disjoint (S i) Y
    · simp only [P,K,ite_eq_left h,Finset.inter_eq_left.mpr (hcover i h),min_self]
      omega
    · simp only [P,K,ite_eq_right h,Finset.inter_univ]
      omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hrow i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
  omega

#print axioms local_rank_exact997
/-- The private count for one row can exclude every wire true at the empty input. -/
theorem false_full_cut997 {n} (C : Circuit) (hg : monoG C) (S : Finset (Fin n)) (o : ℕ)
    (positive : ∀ p ∈ S, value C (bits {p}) o = true)
    (negative : value C (bits (∅ : Finset (Fin n))) o = false) :
    S.card ≤ ((Finset.Ico n (n+C.size)).filter fun w =>
      value C (bits (∅ : Finset (Fin n))) w = false ∧ 2 ≤ (ones C w ∩ S).card).card + 1 := by
  classical
  let G := (Finset.Ico n (n+C.size)).filter fun w =>
    value C (bits (∅ : Finset (Fin n))) w = false ∧ 2 ≤ (ones C w ∩ S).card
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hd,hcard,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  let F := B.filter fun w => value C (bits (∅ : Finset (Fin n))) w = false
  have small (w) (hw : w ∈ F) : (ones C w ∩ S).card ≤ 1 := by
    obtain ⟨hwB,hzero⟩ := Finset.mem_filter.mp hw
    by_contra! hsize
    have hsize' : 2 ≤ (ones C w ∩ S).card := by omega
    have h2 := hsize'.trans (Finset.card_le_card (Finset.inter_subset_left (s₁:=ones C w) (s₂:=S)))
    exact Finset.disjoint_left.mp hd hwB (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (two_gate C w h2),hzero,hsize'⟩)
  have hcover : S ⊆ F.biUnion (fun w => ones C w ∩ S) := by
    intro p hp
    by_contra hn
    have hbad : value C (bits (∅ : Finset (Fin n))) o = true := by
      apply hcut (bits {p}) (bits (∅ : Finset (Fin n))) _ o (Finset.mem_singleton_self _) (positive p hp)
      intro w hw hv
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,Bool.eq_false_iff.mpr he⟩,
        Finset.mem_inter.mpr ⟨(mem_ones C w p).mpr hv,hp⟩⟩)
    exact Bool.false_ne_true (negative.symm.trans hbad)
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul F (fun w => ones C w ∩ S) 1 small
  have h3 : F.card ≤ B.card := Finset.card_filter_le _ _
  have h4 := Finset.card_filter_le G (· < n+C.size)
  simp only [mul_one] at h2
  simp only [Finset.card_singleton] at hcard
  change S.card ≤ G.card + 1
  omega

#print axioms false_full_cut997
end PEqualNP.Outside.Window997
