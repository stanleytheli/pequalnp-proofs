import Chain997
import SparseCertificate997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
theorem physical_heavy_pack997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (R : Finset ℕ) (hR : R ⊆ Finset.Ico n (n+C.size))
    (avoid : ∀ i, Disjoint (heavyGroup997 (pin997 C t false) Y S o i) R) :
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    R.card + (d*(r-1)+(m-d)) ≤ C.size := by
  classical
  let P := prefix997 C t
  let C₀ := pin997 C t false
  let h := head997 n C t
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
  simpa [C₀] using heavy_family997 C₀ (pin_mono997 C t hg false) Y S o hl hs sound0 fire0 base0 hout
    (out_inj997 C S o hc hr hs hl) R (by simpa [C₀] using hR) avoid

noncomputable def pref_ordinary997 {m n} (C : Circuit) (t : Fin C.gates.length) (S : Fin m → Finset (Fin n))
    (Y : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n+t.val)).filter fun w =>
    ¬ ∃ i, Disjoint (S i) Y ∧ sound (pin997 C t false) (S i) w

lemma not_heavy_pin997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true) (i) :
    n+t.val ∉ heavyGroup997 (pin997 C t false) Y S o i := by
  classical
  by_cases h : Disjoint (S i) Y
  · intro hw
    have ha : n+t.val ∈ asg (pin997 C t false) Y (S i) := by simpa [heavyGroup997,h] using hw
    have hh := ((mem_asg ..).mp ha).2.2
    have he : supp (pin997 C t false) Y (n+t.val) = ∅ := by
      ext p
      simp [mem_supp,pin_wire997]
    simp [he] at hh
  · intro hw
    have he : n+t.val = o i := by simpa [heavyGroup997,h] using hw
    have hx := pin_on997 C t ht (bits Y) true hon (o i)
    change value C (bits Y) (o i)=value (pin997 C t false) (bits Y) (o i) at hx
    have htrue : value C (bits Y) (o i)=true := by
      obtain ⟨p,hp,hY⟩ := Finset.not_disjoint_iff.mp h
      rw [hc]
      exact decide_eq_true ⟨p,hp,by simpa [bits] using hY⟩
    rw [←he,pin_wire997] at hx
    exact Bool.false_ne_true (hx.symm.trans (he ▸ htrue))

/-- When every meeting output follows the NOT, prefix gates lacking a
heavy-row soundness witness are paid by the genuine heavy-packing slack. -/
theorem ordinary_packing997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (later : ∀ i, ¬Disjoint (S i) Y → n+t.val ≤ o i) :
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    (pref_ordinary997 C t S Y).card + 1 + (d*(r-1)+(m-d)) ≤ C.size := by
  classical
  let G := pref_ordinary997 C t S Y
  let z := n+t.val
  have htt : t.val < C.size := t.isLt
  have within (w) (hw : w∈G) : n ≤ w ∧ w<z := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have sub : insert z G ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|h
    · exact Finset.mem_Ico.mpr ⟨by dsimp [z];omega,by dsimp [z];omega⟩
    · have hh := within _ h
      exact Finset.mem_Ico.mpr ⟨hh.1,by dsimp [z] at hh;omega⟩
  have sep i : Disjoint (heavyGroup997 (pin997 C t false) Y S o i) (insert z G) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hG
    rcases Finset.mem_insert.mp hG with rfl|hG
    · exact not_heavy_pin997 C S o t ht hc Y hon i hw
    · by_cases h : Disjoint (S i) Y
      · have ha : w ∈ asg (pin997 C t false) Y (S i) := by simpa [heavyGroup997,h] using hw
        exact (Finset.mem_filter.mp hG).2 ⟨i,h,((mem_asg ..).mp ha).2.1⟩
      · have he : w=o i := by simpa [heavyGroup997,h] using hw
        exact (not_lt_of_ge (later i h)) (he ▸ (within w hG).2)
  have hne : z∉G := fun h => lt_irrefl _ (within z h).2
  simpa [Finset.card_insert_of_notMem hne,G] using physical_heavy_pack997 C S o t ht hg hr hs hl hc Y hon (insert z G) sub sep


theorem early_meeting_cost997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t)=false)
    (i : Fin m) (hmi : ¬Disjoint (S i) Y) (hei : o i < n+t.val) :
    let d := (Finset.univ.filter (fun j => Disjoint (S j) Y)).card
    Y.card + (r-2) + (d*(r-1)+(m-d)) ≤ C.size := by
  classical
  let P := prefix997 C t
  let C₀ := pin997 C t false
  let z := n+t.val
  let E := (privateLight P (S i)).erase (o i)
  let R := insert z (dark P Y)
  have htN : t.val < C.size := t.isLt
  have inD (w) (hw : w ∈ dark P Y) : n ≤ w ∧ w < z := by
    simpa [P,z] using Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have inE (w) (hw : w ∈ E) : n ≤ w ∧ w < z := by
    simpa [P,z] using Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hw).2).1
  have equivalent (x) : value P x (o i) = decide (∃ p ∈ S i, x p=true) :=
    (original_prefix997 C t x (o i) hei).symm.trans (hc i x)
  have ecount : r-2 ≤ E.card := by
    have pos (p) (hp : p ∈ S i) : value P (bits {p}) (o i)=true := by
      simpa [equivalent,bits] using hp
    have neg (Z : Finset (Fin n)) (_ : Z.card<r) (hd : Disjoint Z (S i)) : value P (bits Z) (o i)=false := by
      rw [equivalent]
      simp only [bits,decide_eq_true_eq,decide_eq_false_iff_not]
      rintro ⟨p,hp,hz⟩
      exact Finset.disjoint_left.mp hd hz hp
    have h := light_count P (prefix_mono997 C t hg) (S i) (o i) pos neg
    rw [hs,min_self] at h
    have hh : (privateLight P (S i)).card ≤ E.card+1 := by
      by_cases hm : o i ∈ privateLight P (S i)
      · exact le_of_eq (Finset.card_erase_add_one hm).symm
      · simp [E,Finset.erase_eq_of_notMem hm]
    omega
  have rcount : Y.card ≤ R.card := by
    have hn : z∉dark P Y := fun h => lt_irrefl _ (inD z h).2
    simpa [R,Finset.card_insert_of_notMem hn] using first_weight P (prefix_mono997 C t hg) Y _ hon hoff
  have sepRE : Disjoint R E := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hd'
    rcases Finset.mem_insert.mp hw with rfl|hd
    · exact lt_irrefl _ (inE z hd').2
    · have h0 := (Finset.mem_filter.mp hd).2.2
      have h2 := (Finset.mem_filter.mp (Finset.mem_erase.mp hd').2).2.2.2
      simp [h0] at h2
  have sub : R ∪ E ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw|hw
    · rcases Finset.mem_insert.mp hw with rfl|h
      · exact Finset.mem_Ico.mpr ⟨by dsimp [z];omega,by dsimp [z];omega⟩
      · have h' := inD _ h
        exact Finset.mem_Ico.mpr ⟨h'.1,by dsimp [z] at h';omega⟩
    · have h' := inE _ hw
      exact Finset.mem_Ico.mpr ⟨h'.1,by dsimp [z] at h';omega⟩
  have prOrig (w) (hw : w<z) : ones (n:=n) C w=ones P w := by
    ext p
    simp only [mem_ones]
    rw [original_prefix997 C t _ _ hw]
  have small (A : Finset (Fin n)) {i j : Fin m} (hne : i≠j) (hi : A⊆S i) (hj : A⊆S j) :
      A.card ≤ 1 := by
    exact (Finset.card_le_card (show A⊆S i∩S j from fun p hp => Finset.mem_inter.mpr ⟨hi hp,hj hp⟩)).trans (hl i j hne)
  have sep (j) : Disjoint (heavyGroup997 C₀ Y S o j) (R ∪ E) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hz
    rcases Finset.mem_union.mp hz with hR|hE
    · rcases Finset.mem_insert.mp hR with rfl|hd
      · exact not_heavy_pin997 C S o t ht hc Y hon j hw
      · by_cases hj : Disjoint (S j) Y
        · have ha : w ∈ asg C₀ Y (S j) := by simpa [heavyGroup997,hj] using hw
          have hv := (Finset.mem_filter.mp hd).2.1
          have eq := pin_prefix997 C t false (bits Y) w (inD w hd).2
          exact Bool.false_ne_true ((sound_base997 C₀ Y (S j) w hj ((mem_asg ..).mp ha).2.1).symm.trans (eq.trans hv))
        · have he : w=o j := by simpa [heavyGroup997,hj] using hw
          have h0 := (Finset.mem_filter.mp hd).2.2
          have hrow := out_ones997 C S o hc j
          rw [←he,prOrig _ (inD w hd).2,h0] at hrow
          have hz0 : (S j).card=0 := by rw [←hrow];rfl
          rw [hs] at hz0
          omega
    · have hv := (Finset.mem_filter.mp (Finset.mem_erase.mp hE).2).2
      by_cases hj : Disjoint (S j) Y
      · have hne : i≠j := by rintro rfl;exact hmi hj
        have ha : w ∈ asg C₀ Y (S j) := by simpa [heavyGroup997,hj] using hw
        have hsound := ((mem_asg ..).mp ha).2.1
        have hjp : ones P w⊆S j := by
          intro p hp
          have hfire := (pin_prefix997 C t false (bits {p}) w (inE w hE).2).trans ((mem_ones P w p).mp hp)
          obtain ⟨v,hv,hp'⟩ := hsound _ hfire
          have hsame : v=p := by simpa [bits] using hp'
          exact hsame ▸ hv
        have hh := small _ hne hv.2.1 hjp
        omega
      · have he : w=o j := by simpa [heavyGroup997,hj] using hw
        have hne : i≠j := by rintro rfl;exact (Finset.mem_erase.mp hE).1 he
        have hrow := out_ones997 C S o hc j
        rw [←he,prOrig _ (inE w hE).2] at hrow
        have hh := small _ hne hv.2.1 (by rw [hrow])
        omega
  have total := physical_heavy_pack997 C S o t ht hg hr hs hl hc Y hon (R∪E) sub sep
  rw [Finset.card_union_of_disjoint sepRE] at total
  omega

#print axioms ordinary_packing997
#print axioms early_meeting_cost997

theorem physical_sparse997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t)=false)
    (y : Fin n) (hy : y ∈ Y) :
    let d := (Finset.univ.filter (fun j => Disjoint (S j) Y)).card
    let base := d*(r-1)+(m-d)
    C.size<Y.card+(r-2)+base →
    ∃ U : Finset (Finset (Fin n)), U.card+Y.card+base ≤ C.size ∧
      (∀ T ∈ U, T=∅ ∨ (∃ i, Disjoint (S i) Y ∧ T=S i) ∨ ∃ p : Fin n, p ∉ Y ∧ T={p}) ∧
      ∀ P : Finset (Fin n), y ∉ P → (∀ T ∈ U, Disjoint T P) →
        value (prefix997 C t) (bits P) (head997 n C t)=false := by
  classical
  intro d base budget
  let G := pref_ordinary997 C t S Y
  let F := (Finset.univ.filter (fun i => Disjoint (S i) Y)).image S
  have later i (hi : ¬ Disjoint (S i) Y) : n+t.val ≤ o i := by
    by_contra! he
    exact (not_le_of_gt budget) (early_meeting_cost997 C S o t ht hg hr hs hl hc Y hon hoff i hi he)
  have cap := ordinary_packing997 C S o t ht hg hr hs hl hc Y hon later
  change G.card+1+base ≤ C.size at cap
  have hG (w) (hw : w ∈ G) : n ≤ w ∧ w < n+(prefix997 C t).size := by
    simpa using Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hf (T) (hT : T ∈ F) : Disjoint T Y := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hT
    exact (Finset.mem_filter.mp hi).2
  have classify (w) (hn : n≤w) (hu : w<n+(prefix997 C t).size) (he : w∉G) :
      ∃ T ∈ F, sound (prefix997 C t) T w := by
    have hsmall : w<n+t.val := by simpa using hu
    have hh : ∃ i, Disjoint (S i) Y ∧ sound (pin997 C t false) (S i) w := by
      by_contra h
      exact he (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn,hsmall⟩,h⟩)
    obtain ⟨i,hi,hso⟩ := hh
    refine ⟨S i,Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩,?_⟩
    intro x hx
    exact hso x ((pin_prefix997 C t false x w hsmall).trans hx)
  obtain ⟨U,limit,shape,force⟩ := sparse_certificate997 (prefix997 C t) (prefix_mono997 C t hg) G hG Y F hf
    classify (head997 n C t) hon hoff y hy
  refine ⟨U,by omega,?_,force⟩
  intro T hT
  rcases shape T hT with h|h|h
  · exact Or.inl h
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact Or.inr (Or.inl ⟨i,(Finset.mem_filter.mp hi).2,rfl⟩)
  · exact Or.inr (Or.inr h)

#print axioms physical_sparse997
end PEqualNP.Outside.Window997
