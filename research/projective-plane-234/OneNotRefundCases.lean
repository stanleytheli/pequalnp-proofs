import WindowCore997
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Finset.Powerset
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
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


def orientedBase57 (i : Fin 57) : Finset (Fin 57) := ({5,14,20} : Finset (Fin 57)).image (fun p => p+i)

lemma oriented_shift57 (p i a : Fin 57) : p+a ∈ orientedBase57 (i+a) ↔ p ∈ orientedBase57 i := by
  simp only [orientedBase57,Finset.mem_image]
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨z,hz,add_right_cancel ((add_assoc z i a).trans he)⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,hz,(add_assoc z i a).symm⟩

lemma oriented_size57 (i : Fin 57) : (orientedBase57 i).card = 3 := by
  rw [orientedBase57,Finset.card_image_of_injective _ (fun _ _ => add_right_cancel)]
  decide

lemma sep_shift57 (i j a : Fin 57) (h : Disjoint (orientedBase57 i) (plane57 j)) :
    Disjoint (orientedBase57 (i+a)) (plane57 (j+a)) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hq
  exact Finset.disjoint_left.mp h
    ((oriented_shift57 (p-a) i a).mp (by simpa only [sub_add_cancel] using hp))
    ((shift57 (p-a) j a).mp (by simpa only [sub_add_cancel] using hq))

set_option maxHeartbeats 2000000 in
private theorem orient0_57 : ∀ i : Fin 57, Disjoint (orientedBase57 0) (plane57 i) ∨
    Disjoint (orientedBase57 i) (plane57 0) := by decide +kernel

lemma orient_sep57 (i j : Fin 57) : Disjoint (orientedBase57 i) (plane57 j) ∨
    Disjoint (orientedBase57 j) (plane57 i) := by
  rcases orient0_57 (j-i) with h | h
  · exact Or.inl (by simpa only [zero_add,sub_add_cancel] using sep_shift57 _ _ i h)
  · exact Or.inr (by simpa only [zero_add,sub_add_cancel] using sep_shift57 _ _ i h)

/-- If the NOT input is true on each three-point translated test base, the
monotone private count costs 399 gates and the unique NOT costs one more. -/
theorem oriented400997 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (guard : ∀ i, value (prefix997 C t) (bits (orientedBase57 i)) (head997 57 C t)=true) :
    400 ≤ C.size := by
  classical
  let B := pin997 C t false
  let z := 57+t.val
  let A (i) := asg B (orientedBase57 i) (plane57 i)
  have hself i : Disjoint (orientedBase57 i) (plane57 i) := (orient_sep57 i i).elim id id
  have hsound i : sound B (plane57 i) (o i) := fun x hx =>
    of_decide_eq_true ((hc i x).symm.trans ((sandwich997 C t ht hg x (o i)).1 hx))
  have hfire i p (hp : p ∈ plane57 i) : value B (fun v => decide (v ∈ orientedBase57 i ∨ v=p)) (o i)=true := by
    let x (v : Fin 57) := decide (v ∈ orientedBase57 i ∨ v=p)
    have hhi : value (prefix997 C t) x (head997 57 C t)=true := by
      apply value_mono _ (prefix_mono997 C t hg) (bits (orientedBase57 i)) x _ _ (guard i)
      exact fun q hq => decide_eq_true (Or.inl (of_decide_eq_true hq))
    have eq := pin_on997 C t ht x true hhi (o i)
    change value C x (o i)=value B x (o i) at eq
    change value B x (o i)=true
    rw [←eq,hc]
    exact decide_eq_true ⟨p,hp,by simp [x]⟩
  have hcA (i) : 7 ≤ (A i).card := by
    have hh := card_le B (pin_mono997 C t hg false) (orientedBase57 i) (plane57 i) (o i)
      (hself i) (hsound i) (hfire i)
    rw [plane57_size] at hh
    dsimp [A]; omega
  have hsep i j (hij : i≠j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwi hwj
    have ha := (mem_asg B _ _ w).mp hwi
    have hb := (mem_asg B _ _ w).mp hwj
    rcases orient_sep57 i j with h | h
    · exact meet B _ _ _ w (hself i) ha.2.1 hb.2.1 ha.2.2 (plane57_linear i j hij) h
    · exact meet B _ _ _ w (hself j) hb.2.1 ha.2.1 hb.2.2 (plane57_linear j i hij.symm) h
  have hpos : {z} ⊆ Finset.Ico 57 (57+B.size) := by
    apply Finset.singleton_subset_iff.mpr
    have hts : t.val<C.size := t.isLt
    simp only [B,pin_size997,z,Finset.mem_Ico]
    omega
  have unused (i) : Disjoint (A i) {z} := by
    apply Finset.disjoint_singleton_right.mpr
    intro hw
    have h2 := ((mem_asg B _ _ z).mp hw).2.2
    have he : supp B (orientedBase57 i) z = ∅ := by ext p; simp [mem_supp,B,z,pin_wire997]
    simp [he] at h2
  have packed := pack997 _ _ A (fun _ => 7) hpos (fun i w hw => (Finset.mem_filter.mp hw).1) unused hsep hcA
  simpa [B,Nat.card_Ico] using packed

theorem plane57_threshold_three997 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (guard : ∀ Y : Finset (Fin 57), 3 ≤ Y.card → value (prefix997 C t) (bits Y) (head997 57 C t)=true) :
    400 ≤ C.size := oriented400997 C o t ht hg hc (fun i => guard _ (by rw [oriented_size57]))

#print axioms plane57_threshold_three997


noncomputable def restricted997 {n} (C : Circuit) (P S : Finset (Fin n)) (z : ℕ) : Finset ℕ :=
  ((Finset.Ico n (n+C.size)).erase z).filter fun w =>
    ones C w ∩ P ⊆ S ∧ 2 ≤ (ones (n:=n) C w ∩ P).card

theorem restricted_count997 {n} (C : Circuit) (hg : monoG C) (P S : Finset (Fin n)) (z o : ℕ)
    (hz : ∀ A : Finset (Fin n), value C (bits A) z = true)
    (hpos : ∀ p ∈ S ∩ P, value C (bits {p}) o = true)
    (hneg : value C (bits (P \ S)) o = false) :
    (S ∩ P).card - 1 ≤ (restricted997 C P S z).card := by
  classical
  let G := restricted997 C P S z
  have hg' (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size :=
    Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  obtain ⟨B,hd,hc,hcut⟩ := cut C hg G hg' (n+C.size) {o} (fun w _ hw => (hg' w hw).2)
  let F := B.filter fun w => value C (bits (P \ S)) w = false
  have small (w) (hw : w ∈ F) : (ones C w ∩ P).card ≤ 1 := by
    obtain ⟨hwB,hw0⟩ := Finset.mem_filter.mp hw
    have hs : ones C w ∩ P ⊆ S := by
      intro p hp
      by_contra he
      have hp' := Finset.mem_inter.mp hp
      have hp0 : {p} ⊆ P \ S := Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨hp'.2,he⟩)
      exact Bool.false_ne_true (hw0.symm.trans (mono_bits C hg hp0 w ((mem_ones C w p).mp hp'.1)))
    by_contra! hlarge
    have h2 : 2≤(ones C w ∩ P).card := by omega
    have htop : 2≤(ones (n:=n) C w).card := h2.trans (Finset.card_le_card Finset.inter_subset_left)
    have hne : w ≠ z := by rintro rfl; rw [hz] at hw0; contradiction
    exact Finset.disjoint_left.mp hd hwB (Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hne,Finset.mem_Ico.mpr (two_gate C w htop)⟩,hs,h2⟩)
  have covered : S ∩ P ⊆ F.biUnion (fun w => ones C w ∩ P) := by
    intro p hp
    by_contra hn
    have hfire : value C (bits (P \ S)) o = true := by
      apply hcut (bits {p}) (bits (P \ S)) _ o (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hv
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,Bool.eq_false_iff.mpr he⟩,
        Finset.mem_inter.mpr ⟨(mem_ones C w p).mpr hv,(Finset.mem_inter.mp hp).2⟩⟩)
    rw [hneg] at hfire
    contradiction
  have hc1 := Finset.card_le_card covered
  have hc2 := Finset.card_biUnion_le_card_mul F (fun w => ones C w ∩ P) 1 small
  have hc3 := Finset.card_filter_le B (fun w => value C (bits (P \ S)) w = false)
  have hc4 := Finset.card_filter_le G (· < n+C.size)
  change F.card ≤ B.card at hc3
  simp only [mul_one] at hc2
  simp only [Finset.card_singleton] at hc
  change _ ≤ G.card
  omega

/-- Every row can independently use the better private count from the low-weight window
or from one common subcube whose inputs outside P are false. -/
theorem nested_reserved997 {m n k} (C : Circuit) (hg : monoG C) (P : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (z : ℕ) (hl : linear997 S)
    (hz : ∀ A : Finset (Fin n), value C (bits A) z = true)
    (hpos : ∀ i p, p ∈ S i → value C (bits {p}) (o i) = true)
    (hneg : ∀ i (A : Finset (Fin n)), A.card < k → Disjoint A (S i) → value C (bits A) (o i) = false)
    (hP : ∀ i, min k (S i).card < ((S i) ∩ P).card → value C (bits (P \ S i)) (o i) = false)
    (R : Finset ℕ) (hR : R ⊆ Finset.Ico n (n+C.size))
    (hRw : ∀ i, Disjoint (privateLight C (S i)) R)
    (hRp : ∀ i, Disjoint (restricted997 C P (S i) z) R) :
    R.card + ∑ i, (max (min k (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
  classical
  let useWhole (i : Fin m) := ((S i) ∩ P).card ≤ min k (S i).card
  let A (i : Fin m) := if useWhole i then privateLight C (S i) else restricted997 C P (S i) z
  let c (i : Fin m) := max (min k (S i).card) ((S i) ∩ P).card - 1
  have cost (i) : c i ≤ (A i).card := by
    by_cases h : useWhole i
    · have hh := light_count C hg (S i) (o i) (hpos i) (hneg i)
      change ((S i) ∩ P).card ≤ min k (S i).card at h
      simp only [c,A,useWhole,ite_eq_left h,max_eq_left h]
      omega
    · have hh := restricted_count997 C hg P (S i) z (o i) hz (fun p hp => hpos i p (Finset.mem_inter.mp hp).1) (hP i (lt_of_not_ge h))
      change ¬ ((S i) ∩ P).card ≤ min k (S i).card at h
      simpa only [c,A,useWhole,ite_eq_right h,max_eq_right (le_of_not_ge h)] using hh
  have contained (i) : A i ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    by_cases h : useWhole i
    · simp only [A,ite_eq_left h] at hw
      exact (Finset.mem_filter.mp hw).1
    · simp only [A,ite_eq_right h] at hw
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  have sep (i j : Fin m) (hij : i≠j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    have no_two (W : Finset (Fin n)) (h2 : 2≤W.card) (hi' : W ⊆ S i) (hj' : W ⊆ S j) : False := by
      have hh : W⊆S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi' hp,hj' hp⟩
      have := (Finset.card_le_card hh).trans (hl i j hij)
      omega
    by_cases hwi : useWhole i <;> by_cases hwj : useWhole j
    · simp only [A,ite_eq_left hwi,ite_eq_left hwj] at hi hj
      exact Finset.disjoint_left.mp (light_sep997 S hl C hij) hi hj
    · simp only [A,ite_eq_left hwi,ite_eq_right hwj] at hi hj
      have h1 := (Finset.mem_filter.mp hi).2.2.1
      have h2 := (Finset.mem_filter.mp hj).2
      exact no_two _ h2.2 (Finset.inter_subset_left.trans h1) h2.1
    · simp only [A,ite_eq_right hwi,ite_eq_left hwj] at hi hj
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2.2.1
      exact no_two _ h1.2 h1.1 (Finset.inter_subset_left.trans h2)
    · simp only [A,ite_eq_right hwi,ite_eq_right hwj] at hi hj
      have h1 := (Finset.mem_filter.mp hi).2
      have h2 := (Finset.mem_filter.mp hj).2
      exact no_two _ h1.2 h1.1 h2.1
  have hRA (i) : Disjoint (A i) R := by
    by_cases hh : useWhole i
    · simpa [A,hh] using hRw i
    · simpa [A,hh] using hRp i
  simpa [c,Nat.card_Ico] using pack997 _ R A c hR contained hRA sep cost

theorem nested_count997 {m n k} (C : Circuit) (hg : monoG C) (P : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (z : ℕ) (hl : linear997 S)
    (hz : ∀ A : Finset (Fin n), value C (bits A) z = true)
    (hpos : ∀ i p, p ∈ S i → value C (bits {p}) (o i) = true)
    (hneg : ∀ i (A : Finset (Fin n)), A.card < k → Disjoint A (S i) → value C (bits A) (o i) = false)
    (hP : ∀ i, value C (bits (P \ S i)) (o i) = false) :
    ∑ i, (max (min k (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
  simpa using nested_reserved997 C hg P S o z hl hz hpos hneg (fun i _ => hP i) ∅ (Finset.empty_subset _) (by simp) (by simp)

#print axioms nested_count997

theorem nested_physical_reserved997 {m n k} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (P : Finset (Fin n))
    (hoff : ∀ Z : Finset (Fin n), Z.card < k → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : ∀ i, min k (S i).card < ((S i) ∩ P).card → value (prefix997 C t) (bits (P \ S i)) (head997 n C t) = false)
    (R : Finset ℕ) (hR : R ⊆ Finset.Ico n (n+C.size))
    (hw : ∀ i, Disjoint (privateLight (pin997 C t true) (S i)) R)
    (hp : ∀ i, Disjoint (restricted997 (pin997 C t true) P (S i) (n+t.val)) R) :
    R.card + ∑ i, (max (min k (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
  classical
  let C₁ := pin997 C t true
  have quiet {i} {A : Finset (Fin n)} (hA : value (prefix997 C t) (bits A) (head997 n C t) = false)
      (hS : Disjoint A (S i)) : value C₁ (bits A) (o i) = false := by
    have hx := pin_on997 C t ht (bits A) false hA (o i)
    change value C (bits A) (o i) = value C₁ (bits A) (o i) at hx
    rw [← hx,hc]
    simp only [bits,decide_eq_true_eq,decide_eq_false_iff_not]
    rintro ⟨p,hp,ha⟩
    exact Finset.disjoint_left.mp hS ha hp
  have h := nested_reserved997 C₁ (pin_mono997 C t hg true) P S o (n+t.val) hl
    (fun A => pin_wire997 C t true (bits A))
    (fun i p hp => (sandwich997 C t ht hg _ _).2 (by simpa [hc,bits] using hp))
    (fun i A hA hs => quiet (hoff A hA) hs)
    (fun i hi => quiet (hP i hi) (Finset.sdiff_disjoint)) R (by simpa [C₁] using hR) hw hp
  simpa [C₁] using h

theorem nested_physical997 {m n k} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (P : Finset (Fin n))
    (hoff : ∀ Z : Finset (Fin n), Z.card < k → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : value (prefix997 C t) (bits P) (head997 n C t) = false) :
    ∑ i, (max (min k (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
  have only_false (i : Fin m) : value (prefix997 C t) (bits (P \ S i)) (head997 n C t) = false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    have hh := mono_bits (prefix997 C t) (prefix_mono997 C t hg) (Finset.sdiff_subset (s:=P) (t:=S i)) (head997 n C t) hx
    exact Bool.false_ne_true (hP.symm.trans hh)
  simpa using nested_physical_reserved997 C S o t ht hg hl hc P hoff (fun i _ => only_false i) ∅ (Finset.empty_subset _) (by simp) (by simp)

theorem rowwise_first997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y P : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : ∀ i, min Y.card (S i).card < ((S i) ∩ P).card → value (prefix997 C t) (bits (P \ S i)) (head997 n C t) = false) :
    Y.card + ∑ i, (max (min Y.card (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
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
  have whole (i) : Disjoint (privateLight (pin997 C t true) (S i)) R := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hwR
    have ha := (Finset.mem_filter.mp hw).2
    rcases Finset.mem_insert.mp hwR with rfl|hd
    · exact Bool.false_ne_true (ha.1.symm.trans (pin_wire997 C t true (bits (∅ : Finset (Fin n)))))
    · have hh := ha.2.2; simp [emptySupp w hd] at hh
  have part (i) : Disjoint (restricted997 (pin997 C t true) P (S i) z) R := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hwR
    obtain ⟨hne,ha⟩ := Finset.mem_filter.mp hw
    rcases Finset.mem_insert.mp hwR with rfl|hd
    · exact (Finset.mem_erase.mp hne).1 rfl
    · have hh := ha.2; simp [emptySupp w hd] at hh
  exact le_trans (Nat.add_le_add_right bound _)
    (nested_physical_reserved997 C S o t ht hg hl hc P hoff hP R hR whole part)

theorem nested_first997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y P : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : value (prefix997 C t) (bits P) (head997 n C t) = false) :
    Y.card + ∑ i, (max (min Y.card (S i).card) ((S i) ∩ P).card - 1) ≤ C.size := by
  apply rowwise_first997 C S o t ht hg hl hc Y P hon hoff
  intro i _
  apply Bool.eq_false_iff.mpr
  intro hx
  exact Bool.false_ne_true (hP.symm.trans (mono_bits _ (prefix_mono997 C t hg) Finset.sdiff_subset _ hx))

/-- An arbitrary selected row earns its entire size less one, with the rest still
earning their low-weight charges, even when the NOT input fires on the row. -/
theorem full_one_row997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y : Finset (Fin n)) (j : Fin m)
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true) (hY : 0 < Y.card)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false) :
    Y.card + ∑ i, ((if i=j then (S i).card else min Y.card (S i).card) - 1) ≤ C.size := by
  classical
  have hcap (i : Fin m) (hne : i ≠ j) : ((S i) ∩ (S j)).card ≤ min Y.card (S i).card :=
    le_min ((hl i j hne).trans hY) (Finset.card_le_card Finset.inter_subset_left)
  have hh := rowwise_first997 C S o t ht hg hl hc Y (S j) hon hoff (by
    intro i hi
    by_cases he : i = j
    · subst i
      simpa using hoff ∅ (by simpa using hY)
    · exact False.elim ((not_lt_of_ge (hcap i he)) hi))
  convert hh using 2
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : i = j
  · simp [he]
  · simp [he,max_eq_left (hcap i he)]

#print axioms full_one_row997

noncomputable def refund997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g =>
    (∃ i, ∀ p : Fin n, value C (bits {p}) (n+g.val) = true ↔ p ∈ S i) ∧
    (∃ i, Disjoint (S i) Y ∧ ∀ p : Fin n, p ∉ Y →
      (value C (fun v => decide (v ∈ Y ∨ v=p)) (n+g.val) = true ↔ p ∈ S i))

theorem disjoint_refunds997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (Y : Finset (Fin n)) (hl : linear997 S) (hc : computes997 C S o) :
    (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card ≤ (refund997 C S Y).card := by
  classical
  let D := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)
  have ow (i : D) : n ≤ o i.val ∧ o i.val < n+C.size := by
    apply two_gate
    rw [out_ones997 C S o hc]
    exact (Finset.mem_filter.mp i.property).2.2
  let f (i : D) : Fin C.gates.length := ⟨o i.val-n,by have := ow i; change _ < C.size; omega⟩
  have f_spec (i : D) : n+(f i).val = o i.val := by dsimp [f]; have := ow i; omega
  have fr (i : D) : f i ∈ refund997 C S Y := by
    obtain ⟨hd,hcard⟩ := (Finset.mem_filter.mp i.property).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,⟨i.val,?_⟩,⟨i.val,hd,?_⟩⟩
    · intro p
      simp [f_spec,hc,bits]
    · intro p _
      rw [f_spec,hc]
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨v,hv,hY|rfl⟩
        · exact False.elim (Finset.disjoint_left.mp hd hv hY)
        · exact hv
      · exact fun hp => ⟨p,hp,Or.inr rfl⟩
  let j : D ↪ {g // g ∈ refund997 C S Y} :=
    ⟨fun i => ⟨f i,fr i⟩, by
      intro i i' hi
      have he : o i.val = o i'.val := by
        rw [← f_spec i,← f_spec i']
        exact congrArg (fun g : Fin C.gates.length => n+g.val) (congrArg Subtype.val hi)
      apply Subtype.ext
      by_contra hn
      have hS : S i.val = S i'.val := by rw [← out_ones997 C S o hc i.val,← out_ones997 C S o hc i'.val,he]
      have ha := hl i.val i'.val hn
      rw [hS,Finset.inter_self] at ha
      have hsize := (Finset.mem_filter.mp i'.property).2.2
      omega⟩
  have hcj := Fintype.card_le_of_embedding j
  simpa only [Fintype.card_coe] using hcj

/-- The entire project L997 inequality holds if the largest tested subcube loses
at most one point of each output disjoint from the witness. -/
theorem thin_deletion997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y P : Finset (Fin n))
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : value (prefix997 C t) (bits P) (head997 n C t) = false)
    (hthin : ∀ i, Disjoint (S i) Y → (S i).card ≤ ((S i) ∩ P).card + 1) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ C.size + (refund997 C S Y).card + m := by
  classical
  let c (i : Fin m) := max (min Y.card (S i).card) ((S i) ∩ P).card - 1
  let d (i : Fin m) := if Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0
  have per (i) : (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ c i+d i+1 := by
    by_cases hd : Disjoint (S i) Y
    · have := hthin i hd
      by_cases hs : 2≤(S i).card <;> simp [hd,hs,c,d] <;> omega
    · simp [hd,c,d]; omega
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => per i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hsum
  have hd : ∑ i, d i = (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card := by
    simp [d,Finset.sum_boole]
  rw [hd] at hsum
  have h1 : ∑ i, c i ≤ C.size := nested_physical997 C S o t ht hg hl hc P hoff hP
  have h2 := disjoint_refunds997 C S o Y hl hc
  omega

#print axioms thin_deletion997

lemma excess_pair997 (r : ℕ) : r ≤ 1+r.choose 2 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega

lemma packing_pairs997 {m n} (S : Fin m → Finset (Fin n)) (hl : linear997 S) (H : Finset (Fin n)) :
    ∑ i, ((S i) ∩ H).card.choose 2 ≤ H.card.choose 2 := by
  classical
  let A (i : Fin m) := ((S i) ∩ H).powersetCard 2
  have pd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro W hi hj
    obtain ⟨his,hn⟩ := Finset.mem_powersetCard.mp hi
    obtain ⟨hjs,-⟩ := Finset.mem_powersetCard.mp hj
    have hsub : W⊆S i ∩ S j := fun p hp => Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (his hp)).1,(Finset.mem_inter.mp (hjs hp)).1⟩
    have h := (Finset.card_le_card hsub).trans (hl i j hij)
    omega
  calc
    _ = ∑ i, (A i).card := by simp [A,Finset.card_powersetCard]
    _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion pd).symm
    _ ≤ (H.powersetCard 2).card := Finset.card_le_card fun W hW => by
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hW
      have hh := Finset.mem_powersetCard.mp hi
      exact Finset.mem_powersetCard.mpr ⟨hh.1.trans Finset.inter_subset_right,hh.2⟩
    _ = _ := Finset.card_powersetCard ..

theorem small_transversal997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y P H : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t) = true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t) = false)
    (hP : value (prefix997 C t) (bits P) (head997 n C t) = false)
    (hcov : ∀ i, Disjoint (S i) Y → S i ⊆ P ∪ H) (hsmall : H.card.choose 2 ≤ Y.card) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ C.size + (refund997 C S Y).card + m := by
  classical
  let c (i : Fin m) := max (min Y.card (S i).card) ((S i) ∩ P).card - 1
  let d (i : Fin m) := if Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0
  let v (i : Fin m) := ((S i) ∩ H).card.choose 2
  have row (i) : (if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤ c i+d i+v i+1 := by
    by_cases hdi : Disjoint (S i) Y
    · have hsub : S i ⊆ (S i ∩ P) ∪ (S i ∩ H) := by
        intro p hp
        rcases Finset.mem_union.mp (hcov i hdi hp) with h|h
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp,h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp,h⟩)
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hpair := excess_pair997 (S i ∩ H).card
      by_cases h2 : 2≤(S i).card <;> simp [c,d,v,hdi,h2] <;> omega
    · simp [c,d,v,hdi]; omega
  have hall := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => row i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hall
  have hd : ∑ i, d i = (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card := by simp [d,Finset.sum_boole]
  rw [hd] at hall
  have hc' : Y.card + ∑ i, c i ≤ C.size := nested_first997 C S o t ht hg hl hc Y P hon hoff hP
  have hv : ∑ i, v i ≤ H.card.choose 2 := packing_pairs997 S hl H
  have hrefund := disjoint_refunds997 C S o Y hl hc
  omega

#print axioms small_transversal997

end PEqualNP.Outside.Window997
