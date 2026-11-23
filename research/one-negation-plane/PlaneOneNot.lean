import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Window997

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def sound {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x w = true → ∃ p ∈ T, x p = true

def supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v ∈ Y ∨ v = p)) w = true)

lemma mem_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ supp C Y w ↔ value C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [supp]

noncomputable def asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w => sound C T w ∧ 2 ≤ (supp C Y w).card)

lemma mem_asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) :
    w ∈ asg C Y T ↔ (n ≤ w ∧ w < n + C.size) ∧ sound C T w ∧ 2 ≤ (supp C Y w).card := by
  classical
  unfold asg
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma supp_gate {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) (hYT : Disjoint Y T)
    (hs : sound C T w) (h2 : 2 ≤ (supp C Y w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p0 : Fin n := ⟨w, hw⟩
    have hY : p0 ∉ Y := by
      intro hp0
      have hv : value C (fun v => decide (v ∈ Y)) w = true := by
        change value C (fun v => decide (v ∈ Y)) p0 = true
        rw [input_value]
        simpa using hp0
      obtain ⟨q, hqT, hqY⟩ := hs _ hv
      exact Finset.disjoint_left.mp hYT (by simpa using hqY) hqT
    have hsub : supp C Y w ⊆ {p0} := by
      intro q hq
      have hv := (mem_supp C Y w q).mp hq
      change value C (fun v => decide (v ∈ Y ∨ v = q)) p0 = true at hv
      rw [input_value] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hv | hv
      · exact absurd hv hY
      · simp [hv]
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hw
    have hs0 : supp (n := n) C Y w = ∅ := by
      ext q
      simp [mem_supp, missing_value C _ w hw]
    simp [hs0] at h2

lemma card_le {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T) (hso : sound C T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (asg C Y T).card + 1 := by
  classical
  let G := asg C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => ((mem_asg C Y T w).mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
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
    have hG' : G.card + 1 < T.card := hsmall
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
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ o (Finset.mem_singleton_self o) (hfire p hp)
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

lemma meet {n : ℕ} (C : Circuit) (Yi Ti Tj : Finset (Fin n)) (w : ℕ) (hdi : Disjoint Yi Ti)
    (hsi : sound C Ti w) (hsj : sound C Tj w) (h2 : 2 ≤ (supp C Yi w).card)
    (hint : (Ti ∩ Tj).card ≤ 1) : ¬ Disjoint Yi Tj := by
  intro hdj
  have hsub : supp C Yi w ⊆ Ti ∩ Tj := by
    intro p hp
    have hv := (mem_supp C Yi w p).mp hp
    obtain ⟨q, hqT, hqv⟩ := hsi _ hv
    obtain ⟨r, hrT, hrv⟩ := hsj _ hv
    simp only [decide_eq_true_eq] at hqv hrv
    rcases hqv with hqv | hqv
    · exact absurd hqT (Finset.disjoint_left.mp hdi hqv)
    rcases hrv with hrv | hrv
    · exact absurd hrT (Finset.disjoint_left.mp hdj hrv)
    rw [hqv] at hqT
    rw [hrv] at hrT
    exact Finset.mem_inter.mpr ⟨hqT, hrT⟩
  have := Finset.card_le_card hsub
  omega
open PEqualNP.CircuitLowerBounds

abbrev monoG (C : Circuit) := ∀ g ∈ C.gates,
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def bits {n} (A : Finset (Fin n)) (v : Fin n) := decide (v ∈ A)

def ones {n} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (bits {p}) w = true)

lemma mem_ones {n} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ ones C w ↔ value C (bits {p}) w = true := by simp [ones]

lemma mono_bits {n} (C : Circuit) (hg : monoG C) {A B : Finset (Fin n)} (h : A ⊆ B) (w : ℕ) :
    value C (bits A) w = true → value C (bits B) w = true := by
  apply value_mono C hg
  intro p hp
  simpa [bits] using h (of_decide_eq_true hp)

lemma two_gate {n} (C : Circuit) (w : ℕ) (h : 2 ≤ (ones (n:=n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w,hw⟩
    have ho : ones C w ⊆ {p} := by
      intro q hq
      have hx := (mem_ones C w q).mp hq
      change value C (bits {q}) p = true at hx
      simpa [input_value,bits,eq_comm] using hx
    have := Finset.card_le_card ho
    simp at this
    omega
  · by_contra! hw
    have : ones (n:=n) C w = ∅ := by ext p; simp [mem_ones,missing_value C _ w hw]
    simp [this] at h

noncomputable def privateLight {n} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n+C.size)).filter fun w => value C (bits (∅ : Finset (Fin n))) w = false ∧
    ones C w ⊆ S ∧ 2 ≤ (ones (n:=n) C w).card

/-- A monotone circuit that agrees with a set OR on all inputs below weight k
has a private two-point gate for each of the first min(k, |S|)−1 points. -/
theorem light_count {n k} (C : Circuit) (hg : monoG C) (S : Finset (Fin n)) (o : ℕ)
    (hpos : ∀ p ∈ S, value C (bits {p}) o = true)
    (hneg : ∀ A : Finset (Fin n), A.card < k → Disjoint A S → value C (bits A) o = false) :
    min k S.card ≤ (privateLight C S).card + 1 := by
  classical
  let G := privateLight C S
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hd,hc,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have h := Finset.card_filter_le G (· < n+C.size)
    simp only [Finset.card_singleton] at hc
    omega
  by_contra! hsmall
  change G.card + 1 < min k S.card at hsmall
  let clean (w : ℕ) : Finset (Fin n) := if value C (bits (∅ : Finset (Fin n))) w = false ∧ ones C w ⊆ S then ones C w else ∅
  have clean_one (w) (hw : w ∈ B) : (clean w).card ≤ 1 := by
    by_cases h : value C (bits (∅ : Finset (Fin n))) w = false ∧ ones C w ⊆ S
    · simp only [clean,ite_eq_left h]
      by_contra! hn
      have hn' : 2 ≤ (ones (n:=n) C w).card := by omega
      exact Finset.disjoint_left.mp hd hw (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (two_gate C w hn'),h.1,h.2,hn'⟩)
    · simp [clean,h]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 clean_one
    simp only [mul_one] at h
    omega
  obtain ⟨p,hp,hpB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let bad := B.filter fun w => ¬ ones C w ⊆ S
  have hex (d : {w // w ∈ bad}) : ∃ q : Fin n, q ∈ ones C d.val ∧ q ∉ S := by
    have := (Finset.mem_filter.mp d.property).2
    exact Finset.not_subset.mp this
  choose f hf using hex
  let Z := Finset.univ.image f
  have hz : Z.card < k := by
    have hz' := Finset.card_image_le (s := (Finset.univ : Finset {w // w ∈ bad})) (f := f)
    simp only [Finset.card_univ,Fintype.card_coe] at hz'
    have hb' := Finset.card_filter_le B (fun w => ¬ ones C w ⊆ S)
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
    by_cases hs : ones C w ⊆ S
    · exact False.elim (hpB (Finset.mem_biUnion.mpr
        ⟨w,hw, by simpa only [clean,ite_eq_left (And.intro hfalse hs)] using (mem_ones C w p).mpr hv⟩))
    · let d : {w // w ∈ bad} := ⟨w,Finset.mem_filter.mpr ⟨hw,hs⟩⟩
      apply mono_bits C hg (A:={f d}) (B:=Z) _ w ((mem_ones C w (f d)).mp (hf d).1)
      exact Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩)
  rw [hneg Z hz hdZ] at hfire
  contradiction

#print axioms light_count

noncomputable def dark {n} (C : Circuit) (Y : Finset (Fin n)) :=
  (Finset.Ico n (n+C.size)).filter fun w => value C (bits Y) w = true ∧ ones (n:=n) C w = ∅

/-- A monotone wire first attainable at weight k incurs at least k−1 gates
that fire at a witness but fire at no singleton anywhere. -/
theorem first_weight {n k} (C : Circuit) (hg : monoG C) (Y : Finset (Fin n)) (o : ℕ)
    (hon : value C (bits Y) o = true)
    (hoff : ∀ A : Finset (Fin n), A.card < k → value C (bits A) o = false) :
    k ≤ (dark C Y).card + 1 := by
  classical
  let G := dark C Y
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hd,hc,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  have hb : B.card ≤ G.card+1 := by
    have h := Finset.card_filter_le G (· < n+C.size)
    simp only [Finset.card_singleton] at hc
    omega
  let D := B.filter fun w => value C (bits Y) w = true
  have hex (w : {w // w ∈ D}) : ∃ p : Fin n, value C (bits {p}) w.val = true := by
    have ⟨hwB,hwY⟩ := Finset.mem_filter.mp w.property
    by_cases hi : w.val < n
    · let p : Fin n := ⟨w.val,hi⟩
      exact ⟨p,by change value C (bits {p}) p = true; simp [input_value,bits]⟩
    by_cases hm : n+C.size ≤ w.val
    · simp [missing_value C _ w.val hm] at hwY
    by_contra! hempty
    have hz : ones (n:=n) C w.val = ∅ := by
      ext p
      simpa [mem_ones] using hempty p
    exact Finset.disjoint_left.mp hd hwB (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,hwY,hz⟩)
  choose f hf using hex
  let Z := Finset.univ.image f
  have hz : Z.card ≤ G.card+1 := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset {w // w ∈ D})) (f := f)
    simp only [Finset.card_univ,Fintype.card_coe] at h
    exact (h.trans (Finset.card_filter_le _ _)).trans hb
  have hfire : value C (bits Z) o = true := by
    apply hcut (bits Y) (bits Z) _ o (Finset.mem_singleton_self _) hon
    intro w hw hv
    let d : {w // w ∈ D} := ⟨w,Finset.mem_filter.mpr ⟨hw,hv⟩⟩
    apply mono_bits C hg (A:={f d}) (B:=Z) _ w (hf d)
    exact Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩)
  by_contra! hcontra
  change G.card+1 < k at hcontra
  rw [hoff Z (by omega)] at hfire
  contradiction

#print axioms first_weight


lemma pack997 {m : ℕ} (U R : Finset ℕ) (A : Fin m → Finset ℕ) (c : Fin m → ℕ)
    (hRU : R ⊆ U) (hA : ∀ i, A i ⊆ U) (hR : ∀ i, Disjoint (A i) R)
    (hd : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hc : ∀ i, c i ≤ (A i).card) :
    R.card + ∑ i, c i ≤ U.card := by
  classical
  have hp : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := fun i _ j _ hij => hd i j hij
  have hh : ∑ i, c i ≤ (U \ R).card := calc
    _ ≤ ∑ i, (A i).card := Finset.sum_le_sum (fun i _ => hc i)
    _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion hp).symm
    _ ≤ _ := Finset.card_le_card fun w hw => by
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      exact Finset.mem_sdiff.mpr ⟨hA i hi,fun hr => Finset.disjoint_left.mp (hR i) hi hr⟩
  have := Finset.card_sdiff_add_card_eq_card hRU
  omega

abbrev linear997 {m n} (S : Fin m → Finset (Fin n)) :=
  ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1

lemma light_sep997 {m n} (S : Fin m → Finset (Fin n)) (hlin : linear997 S)
    (C : Circuit) {i j : Fin m} (hij : i ≠ j) :
    Disjoint (privateLight C (S i)) (privateLight C (S j)) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro w hwi hwj
  have ha := (Finset.mem_filter.mp hwi).2
  have hb := (Finset.mem_filter.mp hwj).2
  have hs : ones C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨ha.2.1 hp,hb.2.1 hp⟩
  have h1 := (Finset.card_le_card hs).trans (hlin i j hij)
  exact (by omega : ¬ 2 ≤ (ones (n:=n) C w).card) ha.2.2

theorem light_family997 {m n r k} (C : Circuit) (hg : monoG C) (S : Fin m → Finset (Fin n))
    (o : Fin m → ℕ) (hlin : linear997 S) (hsize : ∀ i, (S i).card = r)
    (hpos : ∀ i p, p ∈ S i → value C (bits {p}) (o i) = true)
    (hneg : ∀ i (A : Finset (Fin n)), A.card < k → Disjoint A (S i) → value C (bits A) (o i) = false)
    (R : Finset ℕ) (hr : R ⊆ Finset.Ico n (n+C.size))
    (hex : ∀ i, Disjoint (privateLight C (S i)) R) :
    R.card + m * (min k r - 1) ≤ C.size := by
  classical
  have hh := pack997 _ R (fun i => privateLight C (S i)) (fun _ => min k r - 1)
    hr (fun i w hw => (Finset.mem_filter.mp hw).1) hex (fun i j h => light_sep997 S hlin C h)
    (fun i => by have := light_count C hg (S i) (o i) (hpos i) (hneg i); rw [hsize] at this; omega)
  simpa [Nat.card_Ico] using hh

lemma sound_base997 {n} (C : Circuit) (Y S : Finset (Fin n)) (w : ℕ)
    (hdis : Disjoint S Y) (hs : sound C S w) : value C (bits Y) w = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨p,hp,hY⟩ := hs _ h
  exact Finset.disjoint_left.mp hdis hp (of_decide_eq_true hY)

noncomputable def heavyGroup997 {m n} (C : Circuit) (Y : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (i : Fin m) : Finset ℕ := by
  classical
  exact if Disjoint (S i) Y then asg C Y (S i) else {o i}

theorem heavy_family997 {m n r} (C : Circuit) (hg : monoG C) (Y : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hlin : linear997 S)
    (hsize : ∀ i, (S i).card = r) (hsound : ∀ i, sound C (S i) (o i))
    (hfire : ∀ i p, p ∈ S i → value C (fun v => decide (v ∈ Y ∨ v = p)) (o i) = true)
    (hbase : ∀ i, ¬ Disjoint (S i) Y → value C (bits Y) (o i) = true)
    (ho : ∀ i, o i ∈ Finset.Ico n (n+C.size)) (hinj : Function.Injective o)
    (R : Finset ℕ) (hr : R ⊆ Finset.Ico n (n+C.size))
    (hex : ∀ i, Disjoint (heavyGroup997 C Y S o i) R) :
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    R.card + (d * (r-1) + (m-d)) ≤ C.size := by
  classical
  intro d
  let A := heavyGroup997 C Y S o
  have hA (i) : A i ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    by_cases h : Disjoint (S i) Y
    · simp only [A,heavyGroup997,ite_eq_left h] at hw
      exact Finset.mem_Ico.mpr ((mem_asg ..).mp hw).1
    · simpa [A,heavyGroup997,h] using (show w ∈ Finset.Ico n (n+C.size) from by
        have he : w = o i := by simpa [A,heavyGroup997,h] using hw
        exact he ▸ ho i)
  have sep (i j : Fin m) (hij : i ≠ j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    by_cases hdi : Disjoint (S i) Y <;> by_cases hdj : Disjoint (S j) Y
    · simp only [A,heavyGroup997,ite_eq_left hdi,ite_eq_left hdj] at hi hj
      have pi := (mem_asg ..).mp hi
      have pj := (mem_asg ..).mp hj
      exact meet C Y (S i) (S j) w hdi.symm pi.2.1 pj.2.1 pi.2.2 (hlin i j hij) hdj.symm
    · have eq : w = o j := by simpa [A,heavyGroup997,hdj] using hj
      have hw : w ∈ asg C Y (S i) := by simpa [A,heavyGroup997,hdi] using hi
      have hz := sound_base997 C Y (S i) w hdi ((mem_asg ..).mp hw).2.1
      rw [eq,hbase j hdj] at hz
      contradiction
    · have eq : w = o i := by simpa [A,heavyGroup997,hdi] using hi
      have hw : w ∈ asg C Y (S j) := by simpa [A,heavyGroup997,hdj] using hj
      have hz := sound_base997 C Y (S j) w hdj ((mem_asg ..).mp hw).2.1
      rw [eq,hbase i hdi] at hz
      contradiction
    · have eqi : w = o i := by simpa [A,heavyGroup997,hdi] using hi
      have eqj : w = o j := by simpa [A,heavyGroup997,hdj] using hj
      exact hij (hinj (eqi.symm.trans eqj))
  let c (i : Fin m) := if Disjoint (S i) Y then r-1 else 1
  have hc (i) : c i ≤ (A i).card := by
    by_cases h : Disjoint (S i) Y
    · simp only [c,A,heavyGroup997,ite_eq_left h]
      have hh := card_le C hg Y (S i) (o i) h.symm (hsound i) (hfire i)
      rw [hsize] at hh
      omega
    · simp [c,A,heavyGroup997,h]
  have hh := pack997 _ _ A c hr hA hex sep hc
  have hd : ∑ i, c i = d * (r-1) + (m-d) := by
    simp [c,d,Finset.sum_ite,Finset.filter_not,Finset.card_sdiff_of_subset,Finset.subset_univ]
  simpa [hd,Nat.card_Ico] using hh

open PEqualNP.CircuitLowerBounds

/-- All nonexceptional gates are monotone with fan-in at most two. -/
abbrev others997 (C : Circuit) (t : Fin C.gates.length) := ∀ i : Fin C.gates.length, i≠t →
  ((C.gates[i].op=.and ∨ C.gates[i].op=.or) ∧ C.gates[i].inputs.length≤2)

def prefix997 (C : Circuit) (t : Fin C.gates.length) : Circuit := ⟨C.gates.take t.val,C.output⟩

def const997 (b : Bool) : Gate := ⟨if b then .and else .or,[]⟩

def pin997 (C : Circuit) (t : Fin C.gates.length) (b : Bool) : Circuit :=
  ⟨C.gates.take t.val ++ const997 b :: C.gates.drop (t.val+1),C.output⟩

/-- The first raw NOT operand. A missing operand reads the nonexistent wire n+t
of the prefix circuit. Forward references have their ordinary false value. -/
def head997 (n : ℕ) (C : Circuit) (t : Fin C.gates.length) : ℕ :=
  C.gates[t].inputs.headD (n+t.val)

@[simp] lemma prefix_size997 (C : Circuit) (t : Fin C.gates.length) : (prefix997 C t).size=t.val := by
  simp [Circuit.size,prefix997]

@[simp] lemma pin_size997 (C : Circuit) (t : Fin C.gates.length) (b : Bool) : (pin997 C t b).size=C.size := by
  simp [Circuit.size,pin997]
  omega

private lemma prefixGood997 (C : Circuit) (t : Fin C.gates.length) (hg : others997 C t) :
    ∀ g∈C.gates.take t.val, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g mem
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp mem
  have hlt : j<t.val := by simpa [Nat.min_eq_left t.isLt.le] using hj
  have index : (⟨j,hlt.trans t.isLt⟩ : Fin C.gates.length)≠t := by intro e; exact hlt.ne (congrArg Fin.val e)
  simpa [←eq] using hg ⟨j,hlt.trans t.isLt⟩ index

private lemma suffixGood997 (C : Circuit) (t : Fin C.gates.length) (hg : others997 C t) :
    ∀ g∈C.gates.drop (t.val+1), (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by
  intro g mem
  obtain ⟨j,hj,eq⟩:=List.mem_iff_getElem.mp mem
  have hlt : t.val+1+j<C.gates.length := by simp only [List.length_drop] at hj; omega
  have index : (⟨t.val+1+j,hlt⟩ : Fin C.gates.length)≠t := by
    intro e
    have he : t.val+1+j=t.val := congrArg Fin.val e
    omega
  simpa [←eq,List.getElem_drop] using hg ⟨t.val+1+j,hlt⟩ index

lemma prefix_mono997 (C : Circuit) (t : Fin C.gates.length) (hg : others997 C t) : monoG (prefix997 C t) :=
  prefixGood997 C t hg

lemma pin_mono997 (C : Circuit) (t : Fin C.gates.length) (hg : others997 C t) (b : Bool) :
    monoG (pin997 C t b) := by
  intro g mem
  change g∈_ ++ _::_ at mem
  rcases List.mem_append.mp mem with h|h
  · exact prefixGood997 C t hg g h
  · rcases List.mem_cons.mp h with h|h
    · subst g; cases b <;> simp [const997]
    · exact suffixGood997 C t hg g h

private abbrev initial997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (x : Fin n → Bool) :=
  run (C.gates.take t.val) (List.ofFn x)

private lemma initial_length997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (x : Fin n → Bool) :
    (initial997 C t x).length=n+t.val := by simp [initial997,run_length]

private lemma pin_run997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (b : Bool) (x : Fin n → Bool) :
    run (pin997 C t b).gates (List.ofFn x)=run (C.gates.drop (t.val+1)) (initial997 C t x ++ [b]) := by
  cases b <;> simp [pin997,run,initial997,List.foldl_append,const997,GateOp.eval]

private lemma original_run997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (x : Fin n→Bool)
    (hnot : C.gates[t].op=.not) : run C.gates (List.ofFn x)=run (C.gates.drop (t.val+1))
      (initial997 C t x ++ [!(value (prefix997 C t) x (head997 n C t))]) := by
  change C.gates[t.val].op=.not at hnot
  rw [run_split C.gates _ t.val,List.drop_eq_getElem_cons t.isLt,run_cons,hnot]
  congr 2
  apply congrArg List.singleton
  change (!(List.map _ C.gates[t.val].inputs).headD false) = (!((initial997 C t x).getD (head997 n C t) false))
  unfold head997
  change (!(List.map _ C.gates[t.val].inputs).headD false) = (!((initial997 C t x).getD (C.gates[t.val].inputs.headD (n+t.val)) false))
  cases hi : C.gates[t.val].inputs with
  | nil =>
    have absent : (initial997 C t x).getD (n+t.val) false=false :=
      List.getD_eq_default _ _ (by rw [initial_length997])
    change (!false)=(!((initial997 C t x).getD (n+t.val) false))
    rw [absent]
  | cons i is => rfl

lemma pin_eval997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (hnot : C.gates[t].op=.not)
    (x : Fin n→Bool) (w : ℕ) : value C x w = value (pin997 C t (!(value (prefix997 C t) x (head997 n C t)))) x w := by
  change (run C.gates (List.ofFn x)).getD w false=(run _ _).getD w false
  rw [original_run997 C t x hnot,pin_run997]

lemma original_prefix997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (x : Fin n→Bool) (w : ℕ)
    (hw : w<n+t.val) : value C x w=value (prefix997 C t) x w := by
  change (run C.gates (List.ofFn x)).getD w false=(initial997 C t x).getD w false
  rw [run_split C.gates _ t.val]
  apply run_getD
  simpa only [←initial_length997 C t x] using hw

lemma pin_prefix997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (b : Bool) (x : Fin n→Bool) (w : ℕ)
    (hw : w<n+t.val) : value (pin997 C t b) x w=value (prefix997 C t) x w := by
  change (run _ (List.ofFn x)).getD w false=(initial997 C t x).getD w false
  rw [pin_run997]
  have hl : w<(initial997 C t x).length := (initial_length997 C t x).symm ▸ hw
  rw [run_getD _ _ _ (by simp; omega),List.getD_append _ _ _ _ hl]

lemma pin_wire997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (b : Bool) (x : Fin n→Bool) :
    value (pin997 C t b) x (n+t.val)=b := by
  change (run _ (List.ofFn x)).getD _ false=_
  rw [pin_run997,run_getD _ _ _ (by simp [initial_length997])]
  rw [List.getD_append_right _ _ _ _ (by rw [initial_length997])]
  simp [initial_length997]

private def statesLe997 (a b : List Bool) := a.length=b.length ∧ ∀ w,a.getD w false=true → b.getD w false=true

private lemma snocLe997 {a b : List Bool} {u v : Bool} (h : statesLe997 a b) (hu : u=true → v=true) :
    statesLe997 (a++[u]) (b++[v]) := by
  obtain ⟨hl,hi⟩:=h
  refine ⟨by simp [hl],fun w hw=>?_⟩
  by_cases e : w<a.length
  · rw [List.getD_append _ _ _ _ e] at hw
    rw [List.getD_append _ _ _ _ (hl ▸ e)]
    exact hi w hw
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hw
    rw [List.getD_append_right _ _ _ _ (by omega),←hl]
    cases diff : w-a.length with
    | zero => simpa [diff] using hu (by simpa [diff] using hw)
    | succ i => simp [diff] at hw

private lemma runLe997 (gs : List Gate) (hg : ∀ g∈gs,g.op=.and ∨ g.op=.or)
    {a b : List Bool} (h : statesLe997 a b) : statesLe997 (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons,run_cons]
    apply ih (fun el mem=>hg el (List.mem_cons_of_mem _ mem))
    apply snocLe997 h
    rcases hg g List.mem_cons_self with op|op
    · simp only [op,GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
      intro fine b hb
      obtain ⟨i,hi,rfl⟩:=hb
      exact h.2 i (fine _ ⟨i,hi,rfl⟩)
    · simp only [op,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
      rintro ⟨v,⟨i,hi,rfl⟩,hv⟩
      exact ⟨_,⟨i,hi,rfl⟩,h.2 i hv⟩

lemma pins_order997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (hg : others997 C t)
    (x : Fin n→Bool) (w : ℕ) : value (pin997 C t false) x w=true → value (pin997 C t true) x w=true := by
  change (run _ (List.ofFn x)).getD w false=true → (run _ (List.ofFn x)).getD w false=true
  rw [pin_run997,pin_run997]
  apply (runLe997 _ (fun g h=>(suffixGood997 C t hg g h).1) _).2 w
  exact snocLe997 ⟨rfl,fun _ v=>v⟩ (fun _=>rfl)

lemma sandwich997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (hn : C.gates[t].op=.not)
    (hg : others997 C t) (x : Fin n→Bool) (w : ℕ) :
    (value (pin997 C t false) x w=true → value C x w=true) ∧
    (value C x w=true → value (pin997 C t true) x w=true) := by
  rw [pin_eval997 C t hn x w]
  cases value (prefix997 C t) x (head997 n C t) <;> simp only [Bool.not_false,Bool.not_true] <;>
    exact ⟨by first | exact id | exact pins_order997 C t hg x w,by first | exact id | exact pins_order997 C t hg x w⟩

lemma pin_on997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (hn : C.gates[t].op=.not)
    (x : Fin n → Bool) (b : Bool) (hb : value (prefix997 C t) x (head997 n C t)=b) (w : ℕ) :
    value C x w=value (pin997 C t (!b)) x w := by simpa [hb] using pin_eval997 C t hn x w

lemma head_earlier997 {n : ℕ} (C : Circuit) (t : Fin C.gates.length) (x : Fin n→Bool)
    (hx : value (prefix997 C t) x (head997 n C t)=true) : head997 n C t<n+t.val := by
  by_contra! h
  have hz := missing_value (prefix997 C t) x (head997 n C t) (by simpa [prefix_size997] using h)
  simp [hz] at hx


abbrev computes997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) :=
  ∀ i (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)

lemma out_ones997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hc : computes997 C S o) (i : Fin m) : ones C (o i) = S i := by
  ext p
  simp [mem_ones,hc,bits]

lemma out_inj997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hc : computes997 C S o) (hr : 2 ≤ r) (hs : ∀ i, (S i).card = r) (hl : linear997 S) :
    Function.Injective o := by
  intro i j h
  by_contra hij
  have he : S i = S j := by rw [← out_ones997 C S o hc i,← out_ones997 C S o hc j,h]
  have hh := hl i j hij
  rw [he,Finset.inter_self,hs] at hh
  omega

theorem monotone_full997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : monoG C) (hs : ∀ i, (S i).card = r) (hl : linear997 S) (hc : computes997 C S o) :
    m * (r-1) ≤ C.size := by
  classical
  have hp i p (h : p ∈ S i) : value C (bits {p}) (o i) = true := by simpa [hc,bits] using h
  have hn i (A : Finset (Fin n)) (_ : A.card < r) (h : Disjoint A (S i)) : value C (bits A) (o i) = false := by
    simp only [hc,bits,decide_eq_true_eq,decide_eq_false_iff_not]
    rintro ⟨p,hp,hA⟩
    exact Finset.disjoint_left.mp h hA hp
  simpa using light_family997 C hg S o hl hs hp hn ∅ (Finset.empty_subset _) (by simp)

theorem threshold_bounds997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op = .not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card = r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false) :
    Y.card + m*(min Y.card r-1) ≤ C.size ∧
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    Y.card + (d*(r-1)+(m-d)) ≤ C.size := by
  classical
  let P := prefix997 C t
  let C₀ := pin997 C t false
  let C₁ := pin997 C t true
  let h := head997 n C t
  let z := n+t.val
  let R := insert z (dark P Y)
  have hts : t.val < C.size := t.isLt
  have hsub (w) (hw : w ∈ dark P Y) : n ≤ w ∧ w < z := by
    have hh := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    simpa [P,z] using hh
  have hR : Y.card ≤ R.card := by
    have hn : z ∉ dark P Y := fun hz => lt_irrefl _ (hsub z hz).2
    have hw := first_weight P (prefix_mono997 C t hg) Y h hon hoff
    simpa [R,Finset.card_insert_of_notMem hn] using hw
  have hRU : R ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by dsimp [z]; omega⟩
    · have hh := hsub w hw
      exact Finset.mem_Ico.mpr ⟨hh.1,by dsimp [z] at hh; omega⟩
  have pre_ones (w) (hw : w<z) : ones (n:=n) C₁ w = ones P w := by
    ext p
    simp only [mem_ones]
    rw [pin_prefix997 C t true _ w hw]
  have pon (i p) (hp : p ∈ S i) : value C₁ (bits {p}) (o i) = true := by
    apply (sandwich997 C t ht hg _ _).2
    simpa [hc,bits] using hp
  have poff (i) (Z : Finset (Fin n)) (hz : Z.card < Y.card) (hdi : Disjoint Z (S i)) :
      value C₁ (bits Z) (o i) = false := by
    have he := pin_on997 C t ht (bits Z) false (hoff Z hz) (o i)
    change value C (bits Z) (o i) = value C₁ (bits Z) (o i) at he
    rw [← he,hc]
    simp only [bits,decide_eq_true_eq,decide_eq_false_iff_not]
    rintro ⟨p,hp,hZ⟩
    exact Finset.disjoint_left.mp hdi hZ hp
  have light_avoid (i) : Disjoint (privateLight C₁ (S i)) R := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hwR
    have ha := (Finset.mem_filter.mp hw).2
    rcases Finset.mem_insert.mp hwR with rfl | hd
    · have hv := pin_wire997 C t true (bits (∅ : Finset (Fin n)))
      exact Bool.false_ne_true (ha.1.symm.trans hv)
    · have hs0 := (Finset.mem_filter.mp hd).2.2
      have hz0 := (pre_ones w (hsub w hd).2).trans hs0
      have h2 := ha.2.2
      rw [hz0] at h2
      simp at h2
  have hL := light_family997 C₁ (pin_mono997 C t hg true) S o hl hs pon poff R
    (by simpa [C₁] using hRU) light_avoid
  have hL' : R.card + m*(min Y.card r-1) ≤ C.size := by simpa [C₁] using hL
  refine ⟨le_trans (Nat.add_le_add_right hR _) hL',?_⟩
  have sound0 i : sound C₀ (S i) (o i) := by
    intro x hx
    exact of_decide_eq_true ((hc i x).symm.trans ((sandwich997 C t ht hg x (o i)).1 hx))
  have agree (i) (x : Fin n → Bool) (hxy : ∀ p ∈ Y, x p = true) : value C x (o i) = value C₀ x (o i) := by
    have hh : value P x h = true := value_mono P (prefix_mono997 C t hg) (bits Y) x
      (fun p hp => hxy p (of_decide_eq_true hp)) h hon
    exact pin_on997 C t ht x true hh (o i)
  have fire0 i p (hp : p ∈ S i) : value C₀ (fun v => decide (v ∈ Y ∨ v=p)) (o i) = true := by
    rw [← agree i _ (fun v hv => by simp [hv]),hc]
    exact decide_eq_true ⟨p,hp,by simp⟩
  have base0 i (hi : ¬ Disjoint (S i) Y) : value C₀ (bits Y) (o i) = true := by
    rw [← agree i _ (fun v hv => by simp [bits,hv]),hc]
    obtain ⟨p,hp,hY⟩ := Finset.not_disjoint_iff.mp hi
    exact decide_eq_true ⟨p,hp,by simpa [bits] using hY⟩
  have hout (i) : o i ∈ Finset.Ico n (n+C₀.size) := by
    have hv : 2 ≤ (ones (n:=n) C (o i)).card := by rw [out_ones997 C S o hc,hs]; exact hr
    simpa [C₀] using Finset.mem_Ico.mpr (two_gate C (o i) hv)
  have heavy_avoid (i) : Disjoint (heavyGroup997 C₀ Y S o i) R := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hwR
    by_cases hdi : Disjoint (S i) Y
    · have ha : w ∈ asg C₀ Y (S i) := by simpa [heavyGroup997,hdi] using hw
      have ha' := (mem_asg ..).mp ha
      rcases Finset.mem_insert.mp hwR with rfl | hd
      · have he : supp C₀ Y z = ∅ := by ext p; simp [mem_supp,C₀,z,pin_wire997]
        have hh := ha'.2.2
        simp [he] at hh
      · have hv : value P (bits Y) w = true := (Finset.mem_filter.mp hd).2.1
        have hp0 := pin_prefix997 C t false (bits Y) w (hsub w hd).2
        have hv0 := sound_base997 C₀ Y (S i) w hdi ha'.2.1
        exact Bool.false_ne_true (hv0.symm.trans (hp0.trans hv))
    · have hw' : w = o i := by simpa [heavyGroup997,hdi] using hw
      rcases Finset.mem_insert.mp hwR with hrz | hd
      · have hv := base0 i hdi
        rw [← hw',hrz] at hv
        have hh := pin_wire997 C t false (bits Y)
        exact Bool.false_ne_true (hh.symm.trans hv)
      · have hs0 := (Finset.mem_filter.mp hd).2.2
        have he : ones (n:=n) C w = ones P w := by
          ext p
          simp only [mem_ones]
          rw [original_prefix997 C t _ w (hsub w hd).2]
        have hgate := out_ones997 C S o hc i
        rw [← hw',he,hs0] at hgate
        have hzero : (S i).card = 0 := by rw [← hgate]; rfl
        rw [hs] at hzero
        omega
  have hH := heavy_family997 C₀ (pin_mono997 C t hg false) Y S o hl hs sound0 fire0 base0 hout
    (out_inj997 C S o hc hr hs hl) R (by simpa [C₀] using hRU) heavy_avoid
  dsimp only at hH ⊢
  have hH' := le_trans (Nat.add_le_add_right hR _) hH
  simpa [C₀] using hH'

theorem one_not_uniform997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hunique : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card = r) (hl : linear997 S) (hc : computes997 C S o) :
    m*(r-1) ≤ C.size ∨ ∃ Y : Finset (Fin n),
      Y.card + m*(min Y.card r-1) ≤ C.size ∧
      let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
      Y.card + (d*(r-1)+(m-d)) ≤ C.size := by
  classical
  by_cases hnot : ∃ t : Fin C.gates.length, C.gates[t].op=.not
  · obtain ⟨t,ht⟩ := hnot
    have hg : others997 C t := by
      intro i hit
      obtain ⟨hop,hlen⟩ := hops C.gates[i] (List.getElem_mem _)
      exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun hn => False.elim (hit (hunique i t hn ht)))),hlen⟩
    let P := prefix997 C t
    let h := head997 n C t
    let F := Finset.univ.filter (fun A : Finset (Fin n) => value P (bits A) h = true)
    by_cases hF : F.Nonempty
    · obtain ⟨Y,hY,hmin⟩ := Finset.exists_min_image F Finset.card hF
      have hoff (Z : Finset (Fin n)) (hz : Z.card < Y.card) : value P (bits Z) h = false := by
        apply Bool.eq_false_iff.mpr
        intro hon
        exact (not_le_of_gt hz) (hmin Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hon⟩))
      exact Or.inr ⟨Y,threshold_bounds997 C S o t ht hg hr hs hl hc Y (Finset.mem_filter.mp hY).2 hoff⟩
    · left
      have off (x : Fin n → Bool) : value P x h = false := by
        apply Bool.eq_false_iff.mpr
        intro hx
        let X := Finset.univ.filter (fun p => x p=true)
        have he : bits X = x := by
          funext p
          cases hp : x p <;> simp [bits,X,hp]
        apply hF
        exact ⟨X,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hx⟩⟩
      have hh : computes997 (pin997 C t true) S o := by
        intro i x
        have he := pin_on997 C t ht x false (off x) (o i)
        exact he.symm.trans (hc i x)
      simpa using monotone_full997 (pin997 C t true) S o (pin_mono997 C t hg true) hs hl hh
  · left
    apply monotone_full997 C S o _ hs hl hc
    intro g hmem
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨hop,hlen⟩ := hops C.gates[i] (List.getElem_mem _)
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun hn => False.elim (hnot ⟨⟨i,hi⟩,hn⟩))),hlen⟩


def base57 : Finset (Fin 57) := {0,1,3,13,32,36,43,52}

def plane57 (i : Fin 57) : Finset (Fin 57) := base57.image (fun v => v+i)

lemma shift57 (p i a : Fin 57) : p+a ∈ plane57 (i+a) ↔ p ∈ plane57 i := by
  simp only [plane57,Finset.mem_image]
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨z,hz,add_right_cancel ((add_assoc z i a).trans he)⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz,(add_assoc z i a).symm⟩

lemma plane57_size (i : Fin 57) : (plane57 i).card = 8 := by
  rw [plane57,Finset.card_image_of_injective _ (fun _ _ => add_right_cancel)]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem plane57_zero_linear : ∀ i : Fin 57, i ≠ 0 → (plane57 0 ∩ plane57 i).card ≤ 1 := by
  decide +kernel

theorem plane57_linear : linear997 plane57 := by
  intro i j hij
  let T := plane57 0 ∩ plane57 (j-i)
  have hmap : plane57 i ∩ plane57 j = T.image (fun p => p+i) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hi,hj⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_image.mpr
      refine ⟨x-i,Finset.mem_inter.mpr ⟨?_,?_⟩,sub_add_cancel x i⟩
      · apply (shift57 (x-i) 0 i).mp
        simpa using hi
      · apply (shift57 (x-i) (j-i) i).mp
        simpa using hj
    · intro hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hi,hj⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨by simpa using (shift57 z 0 i).mpr hi,
        by simpa using (shift57 z (j-i) i).mpr hj⟩
  rw [hmap]
  exact (Finset.card_image_le (s:=T)).trans (plane57_zero_linear _ (sub_ne_zero.mpr hij.symm))

def incident57 (p : Fin 57) : Finset (Fin 57) := Finset.univ.filter (fun i => p ∈ plane57 i)

private theorem incident57_zero : (incident57 0).card = 8 := by decide +kernel

lemma incident57_size (p : Fin 57) : (incident57 p).card = 8 := by
  have he : incident57 p = (incident57 0).image (fun i => i+p) := by
    ext i
    simp only [incident57,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro h
      refine ⟨i-p, (shift57 0 (i-p) p).mp (by simpa using h),sub_add_cancel i p⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using (shift57 0 j p).mpr hj
  rw [he,Finset.card_image_of_injective _ (fun _ _ => add_right_cancel),incident57_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem plane57_zero_common : ∀ q : Fin 57, ∃ i, 0 ∈ plane57 i ∧ q ∈ plane57 i := by decide +kernel

lemma plane57_common (p q : Fin 57) : ∃ i, i ∈ incident57 p ∧ i ∈ incident57 q := by
  obtain ⟨i,h0,hq⟩ := plane57_zero_common (q-p)
  refine ⟨i+p,?_,?_⟩
  · simpa [incident57] using (shift57 0 i p).mpr h0
  · simpa [incident57] using (shift57 (q-p) i p).mpr hq

lemma plane57_meets (Y : Finset (Fin 57)) : (Y.biUnion incident57).card ≤ 7 * Y.card + 1 := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert p Y hnot ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hnot]
    by_cases hy : Y.Nonempty
    · obtain ⟨q,hq⟩ := hy
      obtain ⟨i,hi,hj⟩ := plane57_common p q
      have hmem : i ∈ incident57 p ∩ Y.biUnion incident57 :=
        Finset.mem_inter.mpr ⟨hi,Finset.mem_biUnion.mpr ⟨q,hq,hj⟩⟩
      have hpos := Finset.card_pos.mpr (show (incident57 p ∩ Y.biUnion incident57).Nonempty from ⟨i,hmem⟩)
      have hc := Finset.card_union_add_card_inter (incident57 p) (Y.biUnion incident57)
      rw [incident57_size] at hc
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hy]
      simp [incident57_size]

theorem plane57_disjoint_bound (Y : Finset (Fin 57)) :
    57 ≤ (Finset.univ.filter (fun i => Disjoint (plane57 i) Y)).card + 7*Y.card+1 := by
  classical
  have he : Finset.univ.filter (fun i => Disjoint (plane57 i) Y) = Finset.univ \ Y.biUnion incident57 := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,Finset.mem_biUnion]
    constructor
    · rintro hd ⟨p,hY,hp⟩
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hp).2 hY
    · intro h
      exact Finset.disjoint_left.mpr fun p hp hY => h ⟨p,hY,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Y.biUnion incident57))
  rw [← he] at htot
  simp only [Finset.card_univ,Fintype.card_fin] at htot
  have := plane57_meets Y
  omega

#print axioms plane57_linear
#print axioms plane57_disjoint_bound

/-- The 57 cyclic lines of the order-seven plane require at least 229 gates
in any fan-in-two De Morgan circuit with at most one NOT gate. -/
theorem plane57_one_not_229
    (gates : List Gate) (out : Fin 57 → ℕ)
    (hops : ∀ g ∈ gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2)
    (hunique : ∀ i j : Fin gates.length, (gates.get i).op=.not → (gates.get j).op=.not → i=j)
    (hc : ∀ (w : Fin 57) (x : Fin 57 → Bool), Circuit.eval ⟨gates,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ (({0,1,3,13,32,36,43,52} : Finset (Fin 57)).image (fun u => u+w)), x v=true)) :
    229 ≤ gates.length := by
  classical
  let C : Circuit := ⟨gates,0⟩
  have compute : computes997 C plane57 out := fun i x => hc i x
  rcases one_not_uniform997 C plane57 out hops hunique (by decide : 2 ≤ 8) plane57_size plane57_linear compute with
    h | ⟨Y,hL,hH⟩
  · change 57*(8-1) ≤ gates.length at h
    omega
  · let d := (Finset.univ.filter (fun i => Disjoint (plane57 i) Y)).card
    change Y.card + (d*(8-1)+(57-d)) ≤ gates.length at hH
    change Y.card + 57*(min Y.card 8-1) ≤ gates.length at hL
    have hcover : 57 ≤ d + 7*Y.card+1 := plane57_disjoint_bound Y
    have hd : d≤57 := (Finset.card_filter_le _ _).trans (by simp)
    omega

#print axioms plane57_one_not_229


def pointLines997 {m n} (S : Fin m → Finset (Fin n)) (p : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun i => p ∈ S i

lemma plane_meets_general997 {m n q} (S : Fin m → Finset (Fin n))
    (hp : ∀ p, (pointLines997 S p).card = q+1)
    (hpair : ∀ p p', ∃ i, i ∈ pointLines997 S p ∧ i ∈ pointLines997 S p')
    (Y : Finset (Fin n)) : (Y.biUnion (pointLines997 S)).card ≤ q*Y.card+1 := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | @insert p Y hnot ih =>
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hnot,Nat.mul_add,Nat.mul_one]
    by_cases hy : Y.Nonempty
    · obtain ⟨z,hz⟩ := hy
      obtain ⟨i,hi,hj⟩ := hpair p z
      have hmem : i ∈ pointLines997 S p ∩ Y.biUnion (pointLines997 S) :=
        Finset.mem_inter.mpr ⟨hi,Finset.mem_biUnion.mpr ⟨z,hz,hj⟩⟩
      have hpos := Finset.card_pos.mpr (show (pointLines997 S p ∩ Y.biUnion (pointLines997 S)).Nonempty from ⟨i,hmem⟩)
      have hh := Finset.card_union_add_card_inter (pointLines997 S p) (Y.biUnion (pointLines997 S))
      rw [hp] at hh
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hy]
      simp [hp]

lemma plane_cover_general997 {m n q} (S : Fin m → Finset (Fin n))
    (hp : ∀ p, (pointLines997 S p).card = q+1)
    (hpair : ∀ p p', ∃ i, i ∈ pointLines997 S p ∧ i ∈ pointLines997 S p') (Y : Finset (Fin n)) :
    m ≤ (Finset.univ.filter (fun i => Disjoint (S i) Y)).card + q*Y.card+1 := by
  classical
  have he : Finset.univ.filter (fun i => Disjoint (S i) Y) = Finset.univ \ Y.biUnion (pointLines997 S) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,Finset.mem_biUnion]
    constructor
    · rintro hd ⟨p,hY,hpi⟩
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hpi).2 hY
    · exact fun h => Finset.disjoint_left.mpr fun p hpi hY =>
        h ⟨p,hY,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpi⟩⟩
  have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Y.biUnion (pointLines997 S)))
  rw [← he] at htot
  simp only [Finset.card_univ,Fintype.card_fin] at htot
  have := plane_meets_general997 S hp hpair Y
  omega

private lemma heavy_num997 {M q k d N : ℕ} (hq : 2 ≤ q) (hd : d ≤ M)
    (hh : k+(d*q+(M-d))≤N) (hc : M≤d+q*k+1) :
    (k:ℤ) + (q:ℤ)*M - ((q:ℤ)-1)*(1+(q:ℤ)*k) ≤ N := by
  zify [hd] at hh hc hq ⊢
  have hp : (0:ℤ) ≤ (q:ℤ)-1 := by omega
  have hp' : (0:ℤ) ≤ (d:ℤ)+(q:ℤ)*k+1-M := by omega
  nlinarith [mul_nonneg hp hp']

private lemma even_num997 {a k d N : ℕ} (ha : 1≤a)
    (M : ℕ) (hM : M=(2*a)^2+2*a+1) (hd : d≤M)
    (hL : k+M*(min k (2*a+1)-1)≤N) (hH : k+(d*(2*a)+(M-d))≤N)
    (hC : M≤d+(2*a)*k+1) : 4*a^3+2*a^2+3*a+2≤N := by
  by_cases hk : k≤a+1
  · have hh := heavy_num997 (q:=2*a) (by omega) hd hH hC
    subst M
    push_cast at hh
    zify at ha hk ⊢
    have hpos : (0:ℤ) ≤ 2*(a:ℤ)*(2*a-1)-1 := by nlinarith [sq_nonneg ((a:ℤ)-1)]
    have hgap : (0:ℤ) ≤ (a:ℤ)+1-k := by omega
    nlinarith [mul_nonneg hpos hgap]
  · have hmin : a+1 ≤ min k (2*a+1)-1 := by omega
    have hh := le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left M hmin) k) hL
    subst M
    nlinarith [Nat.zero_le (a*a),Nat.zero_le a]

private lemma odd_num997 {a k d N : ℕ} (ha : 1≤a)
    (M : ℕ) (hM : M=(2*a+1)^2+(2*a+1)+1) (hd : d≤M)
    (hL : k+M*(min k (2*a+1+1)-1)≤N) (hH : k+(d*(2*a+1)+(M-d))≤N)
    (hC : M≤d+(2*a+1)*k+1) : 4*a^3+10*a^2+9*a+4≤N := by
  by_cases hk : k≤a+1
  · have hh := heavy_num997 (q:=2*a+1) (by omega) hd hH hC
    subst M
    push_cast at hh
    zify at ha hk ⊢
    have hpos : (0:ℤ) ≤ (2*(a:ℤ)+1)*(2*a)-1 := by nlinarith [sq_nonneg ((a:ℤ)-1)]
    have hgap : (0:ℤ) ≤ (a:ℤ)+1-k := by omega
    nlinarith [mul_nonneg hpos hgap]
  · have hmin : a+1 ≤ min k (2*a+1+1)-1 := by omega
    have hh := le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left M hmin) k) hL
    subst M
    nlinarith [Nat.zero_le a]

theorem plane_parameters997 {m n q} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hq : 2≤q) (hs : ∀ i, (S i).card = q+1) (hl : linear997 S)
    (hp : ∀ p, (pointLines997 S p).card = q+1)
    (hpair : ∀ p p', ∃ i, i ∈ pointLines997 S p ∧ i ∈ pointLines997 S p')
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C S o) : ∃ k d : ℕ, d ≤ m ∧ k+m*(min k (q+1)-1)≤C.size ∧
      k+(d*q+(m-d))≤C.size ∧ m≤d+q*k+1 := by
  classical
  rcases one_not_uniform997 C S o hops hn (show 2≤q+1 by omega) hs hl hc with h | ⟨Y,hL,hH⟩
  · exact ⟨0,m,le_rfl,by simp,by simpa using h,by simp⟩
  · let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    exact ⟨Y.card,d,(Finset.card_filter_le _ _).trans (by simp),hL,by simpa using hH,
      plane_cover_general997 S hp hpair Y⟩

/-- General projective-plane one-NOT lower bound for even order 2a. -/
theorem even_plane_one_not997 {m n a} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (ha : 1≤a) (hm : m=(2*a)^2+2*a+1) (hs : ∀ i, (S i).card = 2*a+1) (hl : linear997 S)
    (hp : ∀ p, (pointLines997 S p).card = 2*a+1)
    (hpair : ∀ p p', ∃ i, i ∈ pointLines997 S p ∧ i ∈ pointLines997 S p')
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C S o) : 4*a^3+2*a^2+3*a+2 ≤ C.size := by
  obtain ⟨k,d,hd,hL,hH,hC⟩ := plane_parameters997 C S o (show 2≤2*a by omega) hs hl hp hpair hops hn hc
  exact even_num997 ha m hm hd hL hH hC

/-- General projective-plane one-NOT lower bound for odd order 2a+1. -/
theorem odd_plane_one_not997 {m n a} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (ha : 1≤a) (hm : m=(2*a+1)^2+(2*a+1)+1) (hs : ∀ i, (S i).card = 2*a+1+1) (hl : linear997 S)
    (hp : ∀ p, (pointLines997 S p).card = 2*a+1+1)
    (hpair : ∀ p p', ∃ i, i ∈ pointLines997 S p ∧ i ∈ pointLines997 S p')
    (hops : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C S o) : 4*a^3+10*a^2+9*a+4 ≤ C.size := by
  obtain ⟨k,d,hd,hL,hH,hC⟩ := plane_parameters997 C S o (show 2≤2*a+1 by omega) hs hl hp hpair hops hn hc
  exact odd_num997 ha m hm hd hL hH hC

#print axioms even_plane_one_not997
#print axioms odd_plane_one_not997
end PEqualNP.Outside.Window997
