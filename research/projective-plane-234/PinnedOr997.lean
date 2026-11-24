import OrHeavy997
import Reader997

namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds

lemma pin_slot_before997 (C : Circuit) (t j : Fin C.gates.length) (b : Bool) (hj : j<t) :
    (pin997 C t b).gates[j.val]'(by change j.val < (pin997 C t b).size; rw [pin_size997]; exact j.isLt)=C.gates[j] := by
  have hlt : j.val<t.val := hj
  unfold pin997
  dsimp only
  rw [List.getElem_append_left (by simp;omega)]
  simp

/-- A private OR in the false-pin circuit occupies an actual OR gate slot of the original
circuit. The artificial false pin itself has empty test support. -/
lemma pin_or_original997 {n} (C : Circuit) (t : Fin C.gates.length) (Y S : Finset (Fin n)) :
    branch997 (n:=n) (pin997 C t false) (asg (pin997 C t false) Y S) false ⊆
      branch997 (n:=n) C (Finset.Ico n (n+C.size)) false := by
  classical
  intro w hw
  obtain ⟨has,⟨j,hj,hop⟩⟩ := Finset.mem_filter.mp hw
  obtain ⟨hslot,_,hcard⟩ := (mem_asg ..).mp has
  have hne : w≠n+t.val := by
    rintro rfl
    have he : supp (pin997 C t false) Y (n+t.val)=∅ := by ext p;simp [mem_supp,pin_wire997]
    simp [he] at hcard
  let j' : Fin C.gates.length := ⟨j.val,by change j.val<C.size; rw [←pin_size997 C t false]; exact j.isLt⟩
  have hj' : n+j'.val=w := hj
  have hdiff : j'≠t := by intro e;exact hne (hj'.symm.trans (congrArg (fun k : Fin C.gates.length => n+k.val) e))
  have he : (pin997 C t false).gates[j]=C.gates[j'] := by
    rcases lt_or_gt_of_ne hdiff with h|h
    · exact pin_slot_before997 C t j' false h
    · exact pin_slot_after997 C t j' false h
  exact Finset.mem_filter.mpr ⟨by simpa using hslot,⟨j',hj',he ▸ hop⟩⟩

/-- For any linearly intersecting output subfamily missed by a true assignment of the
NOT input, the original circuit pays the full sum in physical OR gates alone. -/
theorem physical_or_oriented997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y : Fin m → Finset (Fin n))
    (hon : ∀ i, value (prefix997 C t) (bits (Y i)) (head997 n C t)=true) (hd : ∀ i, Disjoint (Y i) (S i))
    (cross : ∀ i j, i≠j → Disjoint (Y i) (S j) ∨ Disjoint (Y j) (S i)) :
    ∑ i, ((S i).card-1) ≤ (branch997 (n:=n) C (Finset.Ico n (n+C.size)) false).card := by
  classical
  let C₀ := pin997 C t false
  let U := branch997 (n:=n) C (Finset.Ico n (n+C.size)) false
  let A i := branch997 (n:=n) C₀ (asg C₀ (Y i) (S i)) false
  have gin := pin_mono997 C t hg false
  have sound0 i : sound C₀ (S i) (o i) := by
    intro x hx
    exact of_decide_eq_true ((hc i x).symm.trans ((sandwich997 C t ht hg x (o i)).1 hx))
  have fire i p (hp : p ∈ S i) : value C₀ (fun v => decide (v ∈ Y i ∨ v=p)) (o i)=true := by
    let x (v : Fin n) := decide (v∈Y i ∨ v=p)
    have hh : value (prefix997 C t) x (head997 n C t)=true := by
      apply value_mono _ (prefix_mono997 C t hg) (bits (Y i)) x _ _ (hon i)
      exact fun a ha => decide_eq_true (Or.inl (of_decide_eq_true ha))
    have he := pin_on997 C t ht x true hh (o i)
    change value C x (o i)=value C₀ x (o i) at he
    change value C₀ x (o i)=true
    rw [←he,hc]
    exact decide_eq_true ⟨p,hp,by simp [x]⟩
  have sep (i j : Fin m) (hne : i≠j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    have h1 := (mem_asg ..).mp (Finset.mem_filter.mp hi).1
    have h2 := (mem_asg ..).mp (Finset.mem_filter.mp hj).1
    rcases cross i j hne with h|h
    · exact meet C₀ _ _ _ _ (hd i) h1.2.1 h2.2.1 h1.2.2 (hl i j hne) h
    · exact meet C₀ _ _ _ _ (hd j) h2.2.1 h1.2.1 h2.2.2 (hl j i hne.symm) h
  have cost i : (S i).card-1 ≤ (A i).card := by
    have h := heavy_or997 C₀ gin (Y i) (S i) (o i) (hd i) (sound0 i) (fire i)
    dsimp [A]
    omega
  simpa only [Finset.card_empty,Nat.zero_add] using pack997 U ∅ A (fun i => (S i).card-1)
    (Finset.empty_subset _) (fun i => pin_or_original997 C t (Y i) (S i)) (by simp) sep cost

/-- The common-base specialization requires only that the selected rows miss Y. -/
theorem physical_or_family997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y : Finset (Fin n))
    (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true) (hd : ∀ i, Disjoint Y (S i)) :
    ∑ i, ((S i).card-1) ≤ (branch997 (n:=n) C (Finset.Ico n (n+C.size)) false).card :=
  physical_or_oriented997 C S o t ht hg hl hc (fun _ => Y) (fun _ => hon) hd (fun _ j _ => Or.inl (hd j))

#print axioms physical_or_oriented997
#print axioms physical_or_family997
end PEqualNP.Outside.Window997
