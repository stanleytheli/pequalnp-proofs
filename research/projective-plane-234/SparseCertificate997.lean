import BiCut997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
lemma branch_partition997 {n} (C : Circuit) (hg : monoG C) (G : Finset ℕ)
    (hG : ∀ w ∈ G, n ≤ w ∧ w < n+C.size) :
    (branch997 (n:=n) C G true).card + (branch997 (n:=n) C G false).card = G.card := by
  classical
  have sep : Disjoint (branch997 (n:=n) C G true) (branch997 (n:=n) C G false) := by
    refine Finset.disjoint_left.mpr ?_
    intro w ha hb
    obtain ⟨_,i,hi,hopi⟩ := Finset.mem_filter.mp ha
    obtain ⟨_,j,hj,hopj⟩ := Finset.mem_filter.mp hb
    have he : i=j := Fin.ext (by omega)
    subst j
    exact GateOp.noConfusion (hopi.symm.trans hopj)
  have cov : branch997 (n:=n) C G true ∪ branch997 (n:=n) C G false = G := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with h|h <;> exact (Finset.mem_filter.mp h).1
    · intro hw
      obtain ⟨hn,hu⟩ := hG w hw
      let i : Fin C.gates.length := ⟨w-n,by change w-n < C.size;omega⟩
      have hi : n+i.val=w := by dsimp [i];omega
      rcases (hg C.gates[i] (List.getElem_mem _)).1 with hop|hop
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,i,hi,hop⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw,i,hi,hop⟩)
  simpa only [cov] using (Finset.card_union_of_disjoint sep).symm

/-- A monotone prefix containing few ordinary gates amid row-sound gates has a
small falsity certificate, measured in raw points and entire row sets. -/
theorem sparse_certificate997 {n} (C : Circuit) (hg : monoG C) (G : Finset ℕ)
    (hG : ∀ w ∈ G, n ≤ w ∧ w < n+C.size)
    (Y : Finset (Fin n)) (F : Finset (Finset (Fin n))) (hf : ∀ S ∈ F, Disjoint S Y)
    (classify : ∀ w, n ≤ w → w < n+C.size → w ∉ G → ∃ S ∈ F, sound C S w)
    (o : ℕ) (hon : value C (bits Y) o=true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value C (bits Z) o=false)
    (y : Fin n) (hy : y ∈ Y) :
    ∃ U : Finset (Finset (Fin n)), U.card+Y.card ≤ G.card+1 ∧
      (∀ T ∈ U, T=∅ ∨ T ∈ F ∨ ∃ p : Fin n, p ∉ Y ∧ T={p}) ∧
      ∀ P : Finset (Fin n), y ∉ P → (∀ T ∈ U, Disjoint T P) → value C (bits P) o=false := by
  classical
  have zero (S A : Finset (Fin n)) (w) (hs : sound C S w) (hd : Disjoint S A) :
      value C (bits A) w=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨p,hp,hz⟩ := hs _ h
    exact Finset.disjoint_left.mp hd hp (of_decide_eq_true hz)
  have falseY (w) (hn : n≤w) (hw : w<n+C.size) (he : w∉G) : value C (bits Y) w=false := by
    obtain ⟨S,hs,hso⟩ := classify w hn hw he
    exact zero S Y w hso (hf S hs)
  obtain ⟨B,hd,hl,hcard,hforce⟩ := gate_witness997 C hg G hG true (bits Y) o hon
  let T := Finset.univ.filter (fun p : Fin n => (p : ℕ) ∈ B)
  have hT : T.card ≤ B.card := by
    let emb : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
    calc
      _ = (T.map emb).card := (Finset.card_map _).symm
      _ ≤ _ := Finset.card_le_card (by intro w hw;obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hw;exact (Finset.mem_filter.mp hp).2)
  have hYsize : Y.card ≤ (branch997 (n:=n) C G true).card+1 := by
    by_contra! hn
    have hbad := hoff T (by omega)
    have hfire := hforce (bits T) (by
      intro w hw
      have ne : w ∉ G := fun hh => Finset.disjoint_left.mp hd hw hh
      by_cases hh : w < n
      · let p : Fin n := ⟨w,hh⟩
        change value C (bits T) p = true
        rw [input_value]
        exact decide_eq_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)
      · by_cases hu : w < n+C.size
        · exact False.elim (Bool.false_ne_true ((falseY w (by omega) hu ne).symm.trans (hl w hw)))
        · exact False.elim (Bool.false_ne_true ((missing_value C (bits Y) w (by omega)).symm.trans (hl w hw))))
    exact Bool.false_ne_true (hbad.symm.trans hfire)
  have hyoff := hoff (Y.erase y) (Finset.card_erase_lt_of_mem hy)
  obtain ⟨B₀,hd₀,hl₀,hcard₀,force₀⟩ := gate_witness997 C hg G hG false (bits (Y.erase y)) o hyoff
  have yB : (y : ℕ) ∈ B₀ := by
    by_contra hne
    have hbad := force₀ (bits Y) (by
      intro w hw
      have ne : w ∉ G := fun hh => Finset.disjoint_left.mp hd₀ hw hh
      by_cases hin : w<n
      · let p : Fin n := ⟨w,hin⟩
        have hp : p ≠ y := by intro h;apply hne;simpa [←h,p] using hw
        have hv := hl₀ w hw
        change value C (bits (Y.erase y)) p=false at hv
        change value C (bits Y) p=false
        simpa [input_value,bits,hp] using hv
      · by_cases hu : w<n+C.size
        · exact falseY w (by omega) hu ne
        · exact missing_value C _ w (by omega))
    exact Bool.false_ne_true (hbad.symm.trans hon)
  let D := B₀.erase y.val
  have select (w : ℕ) (hw : w ∈ D) : ∃ T : Finset (Fin n),
      (T=∅ ∨ T ∈ F ∨ ∃ p : Fin n, p ∉ Y ∧ T={p}) ∧
      ∀ P : Finset (Fin n), Disjoint T P → value C (bits P) w=false := by
    obtain ⟨hne,hw'⟩ := Finset.mem_erase.mp hw
    by_cases hin : w<n
    · let p : Fin n := ⟨w,hin⟩
      have hp : p ≠ y := by intro e;exact hne (congrArg Fin.val e)
      have hv := hl₀ w hw'
      change value C (bits (Y.erase y)) p=false at hv
      have hpy : p ∉ Y := by simpa [input_value,bits,hp] using hv
      refine ⟨{p},Or.inr (Or.inr ⟨p,hpy,rfl⟩),?_⟩
      intro P hdP
      change value C (bits P) p=false
      simp [input_value,bits,Finset.disjoint_singleton_left.mp hdP]
    · by_cases hu : w<n+C.size
      · have hnotG : w ∉ G := fun h => Finset.disjoint_left.mp hd₀ hw' h
        obtain ⟨S,hs,hso⟩ := classify w (by omega) hu hnotG
        exact ⟨S,Or.inr (Or.inl hs),fun P hP => zero S P w hso hP⟩
      · exact ⟨∅,Or.inl rfl,fun P _ => missing_value C _ w (by omega)⟩
  choose f hf' using fun w : D => select w.val w.property
  let U := Finset.univ.image f
  have hlim := Finset.card_image_le (s:=Finset.univ) (f:=f)
  simp only [Finset.card_univ,Fintype.card_coe] at hlim
  have hD : D.card+1=B₀.card := Finset.card_erase_add_one yB
  have hsum := branch_partition997 (n:=n) C hg G hG
  refine ⟨U,by change (Finset.univ.image f).card+Y.card ≤ G.card+1;omega,?_,?_⟩
  · intro T hT
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hT
    exact (hf' w).1
  · intro P hyP hp
    apply force₀
    intro w hw
    by_cases he : w=y.val
    · subst w
      simp [input_value,bits,hyP]
    · let d : D := ⟨w,Finset.mem_erase.mpr ⟨he,hw⟩⟩
      exact (hf' d).2 P (hp _ (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩))

#print axioms sparse_certificate997
end PEqualNP.Outside.Window997
