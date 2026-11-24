import PhysicalSparse997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
/-- A slot whose value can always be propagated from at most one earlier wire. -/
def transparent997 {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card ≤ 1 ∧ (∀ r ∈ P, r < w) ∧ ∀ x y : Fin n → Bool,
    (∀ r ∈ P, value C x r=true → value C y r=true) → value C x w=true → value C y w=true

lemma skip_cut997 {n} (C : Circuit) (hg : monoG C) (G : Finset ℕ)
    (hG : ∀ w ∈ G, n ≤ w ∧ w < n+C.size) (o a : ℕ) (ha : transparent997 (n:=n) C a) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ (G.erase a).card + 1 ∧
      ∀ x y : Fin n → Bool, (∀ r ∈ B, value C x r=true → value C y r=true) → value C x o=true → value C y o=true := by
  classical
  let val := fun u : (Fin n → Bool) × (Fin n → Bool) => fun r => value C u.1 r=true → value C u.2 r=true
  have step (w) (hw : w∈G) (_ : True) : ∃ P : Finset ℕ, P.card≤2 ∧ (w∉G.erase a → P.card≤1) ∧
      (∀ r ∈ P, r<w ∧ True) ∧ ∀ u, (∀ r∈P, val u r) → val u w := by
    by_cases he : w=a
    · subst w
      obtain ⟨P,hp,hlt,forward⟩ := ha
      exact ⟨P,by omega,fun _ => hp,fun r h => ⟨hlt r h,trivial⟩,fun u hu => forward u.1 u.2 hu⟩
    · obtain ⟨P,hp,hlt,forward⟩ := gate_inputs C hg w (hG w hw).1 (hG w hw).2
      exact ⟨P,hp,fun h => False.elim (h (Finset.mem_erase.mpr ⟨he,hw⟩)),fun r h => ⟨hlt r h,trivial⟩,
        fun u hu => forward u.1 u.2 hu⟩
  obtain ⟨B,hd,_,hc,forward⟩ := asymmetric_cut997 (fun _ => True) val G (G.erase a) step
    (n+C.size) {o} (by simp) (fun w _ hw => (hG w hw).2)
  have hsize := Finset.card_filter_le (G.erase a) (· < n+C.size)
  simp only [Finset.card_singleton] at hc
  exact ⟨B,hd,by omega,fun x y he => forward (x,y) he o (Finset.mem_singleton_self _)⟩

lemma card_le_skip997 {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T) (hso : sound C T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o  = true)
    (a : ℕ) (ha : transparent997 (n:=n) C a) :
    T.card ≤ ((asg C Y T).erase a).card + 1 := by
  classical
  let G := asg C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => ((mem_asg C Y T w).mp hw).1
  obtain ⟨B,hd,hb,hcut⟩ := skip_cut997 C hG G hgate o a ha
  let clean (w : ℕ) : Finset (Fin n) := if sound C T w then supp C Y w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : sound C T w
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      have hg := supp_gate C Y T w hYT hs (by omega)
      exact Finset.disjoint_left.mp hd hw ((mem_asg C Y T w).mpr ⟨hg, hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    have hG' : (G.erase a).card + 1 < T.card := hsmall
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ sound C T w)
  have hout (w : {w // w ∈ Dn}) :
      ∃ x : Fin n → Bool, value C x w.val = true ∧ ∀ q ∈ T, x q = false := by
    have hns := (Finset.mem_filter.mp w.property).2
    unfold sound at hns
    push Not at hns
    obtain ⟨x, hx, hxT⟩ := hns
    exact ⟨x, hx, fun q hq => by simpa using hxT q hq⟩
  choose xs hxs using hout
  let z : Fin n → Bool := fun v => decide (v ∈ Y ∨ ∃ d : {w // w ∈ Dn}, xs d v = true)
  have hzfalse : value C z o = false := by
    by_contra hne
    have ht : value C z o = true := by simpa using hne
    obtain ⟨q, hqT, hzq⟩ := hso z ht
    simp only [z, decide_eq_true_eq] at hzq
    rcases hzq with hqY | ⟨d, hd'⟩
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · rw [(hxs d).2 q hqT] at hd'
      exact Bool.false_ne_true hd'
  have hztrue : value C z o = true := by
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ (hfire p hp)
    intro w hw hx
    by_cases hs : sound C T w
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_supp C Y w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (xs d) z _ w (hxs d).1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

theorem heavy_skip997 {m n r} (C : Circuit) (hg : monoG C) (Y : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hlin : linear997 S)
    (hsize : ∀ i, (S i).card = r) (hsound : ∀ i, sound C (S i) (o i))
    (hfire : ∀ i p, p ∈ S i → value C (fun v => decide (v ∈ Y ∨ v = p)) (o i) = true)
    (hbase : ∀ i, ¬ Disjoint (S i) Y → value C (bits Y) (o i) = true)
    (ho : ∀ i, o i ∈ Finset.Ico n (n+C.size)) (hinj : Function.Injective o)
    (a : ℕ) (htr : transparent997 (n:=n) C a) (hne : ∀ i, a ≠ o i)
    (R : Finset ℕ) (hr : R ⊆ Finset.Ico n (n+C.size))
    (hex : ∀ i, Disjoint ((heavyGroup997 C Y S o i).erase a) R) :
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    R.card + (d * (r-1) + (m-d)) ≤ C.size := by
  classical
  intro d
  let B := heavyGroup997 C Y S o
  let A (i) := (B i).erase a
  have hB (i) : B i ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    by_cases h : Disjoint (S i) Y
    · simp only [B,heavyGroup997,ite_eq_left h] at hw
      exact Finset.mem_Ico.mpr ((mem_asg ..).mp hw).1
    · simpa [B,heavyGroup997,h] using (show w ∈ Finset.Ico n (n+C.size) from by
        have he : w = o i := by simpa [B,heavyGroup997,h] using hw
        exact he ▸ ho i)
  have sepB (i j : Fin m) (hij : i ≠ j) : Disjoint (B i) (B j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    by_cases hdi : Disjoint (S i) Y <;> by_cases hdj : Disjoint (S j) Y
    · simp only [B,heavyGroup997,ite_eq_left hdi,ite_eq_left hdj] at hi hj
      have pi := (mem_asg ..).mp hi
      have pj := (mem_asg ..).mp hj
      exact meet C Y (S i) (S j) w hdi.symm pi.2.1 pj.2.1 pi.2.2 (hlin i j hij) hdj.symm
    · have eq : w = o j := by simpa [B,heavyGroup997,hdj] using hj
      have hw : w ∈ asg C Y (S i) := by simpa [B,heavyGroup997,hdi] using hi
      have hz := sound_base997 C Y (S i) w hdi ((mem_asg ..).mp hw).2.1
      rw [eq,hbase j hdj] at hz
      contradiction
    · have eq : w = o i := by simpa [B,heavyGroup997,hdi] using hi
      have hw : w ∈ asg C Y (S j) := by simpa [B,heavyGroup997,hdj] using hj
      have hz := sound_base997 C Y (S j) w hdj ((mem_asg ..).mp hw).2.1
      rw [eq,hbase i hdi] at hz
      contradiction
    · have eqi : w = o i := by simpa [B,heavyGroup997,hdi] using hi
      have eqj : w = o j := by simpa [B,heavyGroup997,hdj] using hj
      exact hij (hinj (eqi.symm.trans eqj))
  have hA (i) : A i ⊆ Finset.Ico n (n+C.size) := fun w hw => hB i (Finset.mem_erase.mp hw).2
  have sep (i j) (hij : i ≠ j) : Disjoint (A i) (A j) := Finset.disjoint_left.mpr fun w hi hj =>
    Finset.disjoint_left.mp (sepB i j hij) (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hj).2
  let c (i : Fin m) := if Disjoint (S i) Y then r-1 else 1
  have hc (i) : c i ≤ (A i).card := by
    by_cases h : Disjoint (S i) Y
    · simp only [c,A,B,heavyGroup997,ite_eq_left h]
      have hh := card_le_skip997 C hg Y (S i) (o i) h.symm (hsound i) (hfire i) a htr
      rw [hsize] at hh
      omega
    · simp [c,A,B,heavyGroup997,h,hne i]
  have hh := pack997 _ _ A c hr hA hex sep hc
  have hd : ∑ i, c i = d * (r-1) + (m-d) := by
    simp [c,d,Finset.sum_ite,Finset.filter_not,Finset.card_sdiff_of_subset,Finset.subset_univ]
  simpa [hd,Nat.card_Ico] using hh

#print axioms heavy_skip997
end PEqualNP.Outside.Window997
