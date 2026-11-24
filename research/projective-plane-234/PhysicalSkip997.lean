import Transparent997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
theorem physical_heavy_skip997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (a : ℕ) (htr : transparent997 (n:=n) (pin997 C t false) a) (hne : ∀ i, a ≠ o i)
    (R : Finset ℕ) (hR : R ⊆ Finset.Ico n (n+C.size))
    (avoid : ∀ i, Disjoint ((heavyGroup997 (pin997 C t false) Y S o i).erase a) R) :
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
  simpa [C₀] using heavy_skip997 C₀ (pin_mono997 C t hg false) Y S o hl hs sound0 fire0 base0 hout
    (out_inj997 C S o hc hr hs hl) a htr hne R (by simpa [C₀] using hR) avoid

theorem ordinary_skip_packing997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (a : ℕ) (ha : n+t.val < a) (hau : a<n+C.size) (htr : transparent997 (n:=n) (pin997 C t false) a)
    (hne_out : ∀ i, a≠o i) (later : ∀ i, ¬Disjoint (S i) Y → n+t.val ≤ o i) :
    let d := (Finset.univ.filter (fun i => Disjoint (S i) Y)).card
    (pref_ordinary997 C t S Y).card + 2 + (d*(r-1)+(m-d)) ≤ C.size := by
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
  have hgout : a∉insert z G := by
    intro hm
    rcases Finset.mem_insert.mp hm with he|he
    · change z<a at ha;omega
    · have hh := (within a he).2;change z<a at ha;omega
  have sub' : insert a (insert z G) ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact Finset.mem_Ico.mpr ⟨by omega,hau⟩
    · exact sub hw
  have sep' i : Disjoint ((heavyGroup997 (pin997 C t false) Y S o i).erase a) (insert a (insert z G)) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw h
    rcases Finset.mem_insert.mp h with rfl|h
    · exact (Finset.mem_erase.mp hw).1 rfl
    · exact Finset.disjoint_left.mp (sep i) (Finset.mem_erase.mp hw).2 h
  have total := physical_heavy_skip997 C S o t ht hg hr hs hl hc Y hon a htr hne_out (insert a (insert z G)) sub' sep'
  simp only [Finset.card_insert_of_notMem hgout,Finset.card_insert_of_notMem hne,G] at total
  omega

theorem physical_sparse_skip997 {m n r} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hr : 2 ≤ r) (hs : ∀ i, (S i).card=r) (hl : linear997 S) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t)=false)
    (a : ℕ) (ha : n+t.val<a) (hau : a<n+C.size) (htr : transparent997 (n:=n) (pin997 C t false) a)
    (hne_out : ∀ i, a≠o i) (y : Fin n) (hy : y ∈ Y) :
    let d := (Finset.univ.filter (fun j => Disjoint (S j) Y)).card
    let base := d*(r-1)+(m-d)
    C.size<Y.card+(r-2)+base →
    ∃ U : Finset (Finset (Fin n)), U.card+Y.card+base+1 ≤ C.size ∧
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
  have cap := ordinary_skip_packing997 C S o t ht hg hr hs hl hc Y hon a ha hau htr hne_out later
  change G.card+2+base ≤ C.size at cap
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


#print axioms physical_sparse_skip997
end PEqualNP.Outside.Window997
