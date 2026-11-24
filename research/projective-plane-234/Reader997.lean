import Transparent997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
lemma pin_slot_after997 (C : Circuit) (t j : Fin C.gates.length) (b : Bool) (hj : t<j) :
    (pin997 C t b).gates[j.val]'(by change j.val < (pin997 C t b).size; rw [pin_size997]; exact j.isLt)=C.gates[j] := by
  have lt : t.val<j.val := hj
  have ht : t.val<C.gates.length := t.isLt
  unfold pin997
  dsimp only
  rw [List.getElem_append_right (by simp;omega)]
  have sub : j.val-(C.gates.take t.val).length = (j.val-t.val-1)+1 := by
    simp
    omega
  simp only [sub,List.getElem_cons_succ,List.getElem_drop]
  congr 1
  omega

lemma post_formula997 {n} (C : Circuit) (t j : Fin C.gates.length) (hj : t<j) (b : Bool) (x : Fin n → Bool) :
    value (pin997 C t b) x (n+j.val)=C.gates[j].op.eval
      (C.gates[j].inputs.map (fun a => if a<n+j.val then value (pin997 C t b) x a else false)) := by
  have hpos : n+j.val<n+(pin997 C t b).size := by rw [pin_size997]; exact Nat.add_lt_add_left j.isLt n
  have h := gate_value (pin997 C t b) x (n+j.val) (by omega) hpos
  dsimp only at h
  simpa only [Nat.add_sub_cancel_left,pin_slot_after997 C t j b hj] using h

/-- When the NOT has no subsequent reader, its two pins agree on every other physical wire. -/
theorem no_readers997 {n} (C : Circuit) (t : Fin C.gates.length)
    (hn : ∀ j : Fin C.gates.length, t<j → n+t.val ∉ C.gates[j].inputs)
    (x : Fin n → Bool) (w : ℕ) (hw : w≠n+t.val) : value (pin997 C t false) x w=value (pin997 C t true) x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w<n+t.val
    · exact (pin_prefix997 C t false x w h).trans (pin_prefix997 C t true x w h).symm
    · by_cases hu : w<n+C.size
      · let j : Fin C.gates.length := ⟨w-n,by change w-n<C.size;omega⟩
        have hj : t<j := by change t.val<w-n;omega
        have he : n+j.val=w := by dsimp [j];omega
        rw [←he,post_formula997 C t j hj false,post_formula997 C t j hj true]
        congr 1
        apply List.map_congr_left
        intro a ha
        by_cases hlt : a<n+j.val
        · simp only [ite_eq_left hlt]
          exact ih a (by omega) (fun hn' => hn j hj (hn' ▸ ha))
        · simp [hlt]
      · rw [missing_value,missing_value] <;> simp only [pin_size997] <;> omega

/-- A reader of a pinned-false NOT has at most one effective antecedent. -/
theorem reader_transparent997 {n} (C : Circuit) (t j : Fin C.gates.length) (hj : t<j)
    (hg : others997 C t) (hread : n+t.val ∈ C.gates[j].inputs) :
    transparent997 (n:=n) (pin997 C t false) (n+j.val) := by
  classical
  let g := C.gates[j]
  let z := n+t.val
  let w := n+j.val
  let B := pin997 C t false
  obtain ⟨hop,hl⟩ := hg j (Fin.ne_of_gt hj)
  have hcase : g.op=.and ∨ g.op=.or := hop
  have ec (x : Fin n → Bool) : value B x w=g.op.eval (g.inputs.map (fun r => if r<w then value B x r else false)) :=
    post_formula997 C t j hj false x
  have zlt : z<w := Nat.add_lt_add_left hj n
  have hmem : z∈g.inputs.toFinset := List.mem_toFinset.mpr hread
  let A := (g.inputs.toFinset.erase z).filter (· < w)
  have ha1 : A.card≤1 := by
    have hfin : g.inputs.toFinset.card ≤ 2 := (List.toFinset_card_le _).trans hl
    have her := Finset.card_erase_add_one hmem
    have := Finset.card_filter_le (g.inputs.toFinset.erase z) (· < w)
    change A.card ≤ _ at this
    omega
  refine ⟨A,ha1,fun r hr => (Finset.mem_filter.mp hr).2,?_⟩
  intro x y hx hv
  rw [ec] at hv ⊢
  rcases hcase with hA|hO
  · simp only [hA,GateOp.eval,List.all_eq_true,id_eq] at hv
    have hh := hv _ (List.mem_map.mpr ⟨z,hread,rfl⟩)
    simp [zlt,B,z,pin_wire997] at hh
  · simp only [hO,GateOp.eval,List.any_eq_true,id_eq] at hv ⊢
    obtain ⟨a,ha,he⟩ := hv
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
    have hlt : r<w := by by_contra h; simp [h] at he
    have hne : r≠z := by rintro rfl;simp [zlt,B,z,pin_wire997] at he
    have ha' : r∈A := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne,List.mem_toFinset.mpr hr⟩,hlt⟩
    exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,by simpa [hlt] using hx r ha' (by simpa [hlt] using he)⟩

lemma reader_not_output997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t j : Fin C.gates.length) (hj : t<j) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hread : n+t.val ∈ C.gates[j].inputs) (hc : computes997 C S o)
    (Y : Finset (Fin n)) (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (hem : value (prefix997 C t) (bits (∅ : Finset (Fin n))) (head997 n C t)=false)
    (nonempty : ∀ i, (S i).Nonempty) (i : Fin m) : n+j.val ≠ o i := by
  intro he
  let w := n+j.val
  let z := n+t.val
  have zlt : z<w := Nat.add_lt_add_left hj n
  rcases (hg j (Fin.ne_of_gt hj)).1 with hA|hO
  · obtain ⟨p,hp⟩ := nonempty i
    let x (v : Fin n) := decide (v ∈ Y ∨ v=p)
    have hx : value (prefix997 C t) x (head997 n C t)=true := by
      apply value_mono _ (prefix_mono997 C t hg) (bits Y) x _ _ hon
      exact fun p h => decide_eq_true (Or.inl (of_decide_eq_true h))
    have htrue : value C x (o i)=true := by rw [hc];exact decide_eq_true ⟨p,hp,by simp [x]⟩
    have hh := (pin_on997 C t ht x true hx (o i)).symm.trans htrue
    change value (pin997 C t false) x (o i)=true at hh
    rw [←he,post_formula997 C t j hj false,hA] at hh
    simp only [GateOp.eval,List.all_eq_true,id_eq] at hh
    have hv := hh _ (List.mem_map.mpr ⟨z,hread,rfl⟩)
    change (if z<w then value (pin997 C t false) x z else false)=true at hv
    simp [zlt,z,pin_wire997] at hv
  · let x := bits (∅ : Finset (Fin n))
    have hz : value C x (o i)=false := by simp [hc,x,bits]
    have hh := (pin_on997 C t ht x false hem (o i)).symm.trans hz
    change value (pin997 C t true) x (o i)=false at hh
    have hv : value (pin997 C t true) x (n+j.val)=true := by
      rw [post_formula997 C t j hj true,hO]
      simp only [GateOp.eval,List.any_eq_true,id_eq]
      exact ⟨_,List.mem_map.mpr ⟨z,hread,rfl⟩,by change (if z<w then value (pin997 C t true) x z else false)=true;simp [zlt,z,pin_wire997]⟩
    exact Bool.false_ne_true (hh.symm.trans (he ▸ hv))

#print axioms reader_transparent997
#print axioms no_readers997
end PEqualNP.Outside.Window997
