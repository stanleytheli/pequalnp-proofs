import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import PEqualNP.Defs.CircuitLowerBounds

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


end PEqualNP.Outside.Window997
