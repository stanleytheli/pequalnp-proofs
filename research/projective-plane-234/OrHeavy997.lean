import BiCut997

namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds

/-- A globally sound row earns all its private gates from OR positions.
Every AND can be excluded from its charge. -/
theorem heavy_or997 {n} (C : Circuit) (hg : monoG C) (Y S : Finset (Fin n)) (o : ℕ)
    (hdis : Disjoint Y S) (hso : sound C S o)
    (hpos : ∀ p ∈ S, value C (fun i => decide (i ∈ Y ∨ i=p)) o=true) :
    S.card ≤ (branch997 (n:=n) C (asg C Y S) false).card+1 := by
  classical
  let X := Finset.univ \ S
  have hXS : Disjoint S X := Finset.disjoint_sdiff
  have hneg := sound_base997 C X S o hXS hso
  have hvalid (w) (hw : w ∈ asg C Y S) := ((mem_asg C Y S w).mp hw).1
  obtain ⟨B,avoid,cold,size,force⟩ := gate_witness997 C hg _ hvalid false (bits X) o hneg
  have soundB (w) (hw : w∈B) : sound C S w := by
    intro x hx
    by_contra! hn
    have hwX := value_mono C hg x (bits X) (by
      intro p hp
      apply decide_eq_true
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hs
      exact hn p hs hp) w hx
    exact Bool.false_ne_true ((cold w hw).symm.trans hwX)
  have small (w) (hw : w∈B) : (supp C Y w).card ≤ 1 := by
    by_contra! h
    have h2 : 2≤(supp C Y w).card := by omega
    have hs := soundB w hw
    exact Finset.disjoint_left.mp avoid hw ((mem_asg C Y S w).mpr ⟨supp_gate C Y S w hdis hs h2,hs,h2⟩)
  have cover : S ⊆ B.biUnion (supp C Y) := by
    intro p hp
    by_contra hn
    have hbad := force (fun i => decide (i∈Y ∨ i=p)) (by
      intro w hw
      apply Bool.eq_false_iff.mpr
      intro h
      exact hn (Finset.mem_biUnion.mpr ⟨w,hw,(mem_supp C Y w p).mpr h⟩))
    exact Bool.false_ne_true (hbad.symm.trans (hpos p hp))
  have h1 := Finset.card_le_card cover
  have h2 := Finset.card_biUnion_le_card_mul B (supp C Y) 1 small
  simp only [mul_one] at h2
  omega

/-- Oriented bases keep the OR witnesses for different rows disjoint. -/
theorem or_family997 {m n} (C : Circuit) (hg : monoG C) (Y S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hl : linear997 S) (hself : ∀ i, Disjoint (Y i) (S i))
    (cross : ∀ i j, i≠j → Disjoint (Y i) (S j) ∨ Disjoint (Y j) (S i))
    (hs : ∀ i, sound C (S i) (o i))
    (hpos : ∀ i, ∀ p ∈ S i, value C (fun v => decide (v∈Y i ∨ v=p)) (o i)=true) :
    ∑ i, ((S i).card-1) ≤ (branch997 (n:=n) C (Finset.Ico n (n+C.size)) false).card := by
  classical
  let U := branch997 (n:=n) C (Finset.Ico n (n+C.size)) false
  let A (i) := branch997 (n:=n) C (asg C (Y i) (S i)) false
  have inside i : A i ⊆ U := by
    intro w hw
    obtain ⟨hg,hOp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,hOp⟩
  have sep (i j : Fin m) (hne : i≠j) : Disjoint (A i) (A j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    have h1 := (mem_asg ..).mp (Finset.mem_filter.mp hi).1
    have h2 := (mem_asg ..).mp (Finset.mem_filter.mp hj).1
    rcases cross i j hne with h|h
    · exact meet C _ _ _ _ (hself i) h1.2.1 h2.2.1 h1.2.2 (hl i j hne) h
    · exact meet C _ _ _ _ (hself j) h2.2.1 h1.2.1 h2.2.2 (hl j i hne.symm) h
  have cost i : (S i).card-1 ≤ (A i).card := by
    have h := heavy_or997 C hg (Y i) (S i) (o i) (hself i) (hs i) (hpos i)
    dsimp [A]
    omega
  simpa only [Finset.card_empty,Nat.zero_add] using pack997 U ∅ A (fun i => (S i).card-1)
    (Finset.empty_subset _) inside (by simp) sep cost

#print axioms heavy_or997
#print axioms or_family997
end PEqualNP.Outside.Window997
