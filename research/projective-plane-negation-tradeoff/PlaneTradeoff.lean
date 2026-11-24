import PhysicalWindow
import WindowAtBase

namespace LimitedNegation.Project
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.Window997

/-- A size/negation tradeoff for every pairwise-linear output system.
`avoid` is its extremal number of lines missed by a set of points. -/
theorem stable_packing {n m r h} (C : Circuit) (good : legal C)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (lin : linear997 S)
    (sz : ∀ i, (S i).card=r)
    (sem : ∀ z : Finset (Fin n), ∀ i, value C (bits z) (o i)=true ↔ ¬Disjoint z (S i))
    (avoid : ℕ → ℕ) (lower : ∀ b : Finset (Fin n),
      avoid b.card ≤ (Finset.univ.filter fun i => Disjoint (S i) b).card)
    (anti : Antitone avoid) :
    avoid ((2^(C.gates.countP (fun g => isNot g.op))-1)*h) * (min (h+1) r - 1) ≤ C.size := by
  classical
  by_cases hz : h=0
  · subst h; simp
  obtain ⟨base,P,small,pos,equal,fixed⟩ := freeze_window n C good h
  let alive := Finset.univ.filter fun i => Disjoint (S i) base
  have yes (i) (_ : i∈alive) (p) (mem : p∈S i) :
      value P (bits (base∪{p})) (o i)=true := by
    have cap : (base∪{p}).card≤base.card+h := by
      have z := Finset.card_union_le base {p}
      simp only [Finset.card_singleton] at z
      omega
    rw [fixed _ Finset.subset_union_left cap, sem]
    exact fun no => Finset.disjoint_left.mp no (Finset.mem_union_right _ (Finset.mem_singleton_self p)) mem
  have no (i) (hi : i∈alive) (A : Finset (Fin n)) (sm : A.card<h+1) (dis : Disjoint A (S i)) :
      value P (bits (base∪A)) (o i)=false := by
    have cap : (base∪A).card ≤ base.card+h := by have := Finset.card_union_le base A; omega
    rw [fixed _ Finset.subset_union_left cap]
    apply Bool.eq_false_iff.mpr
    exact fun he => (sem _ i).mp he (Finset.disjoint_union_left.mpr ⟨(Finset.mem_filter.mp hi).2.symm,dis⟩)
  have total := sum_above P pos base S o lin alive (fun i _ => sz i) yes no
  rw [equal] at total
  exact (Nat.mul_le_mul_right _ ((anti small).trans (lower base))).trans total

/-- At most one line in addition to `q` per selected point can be hit in a
projective plane. This form also applies to other incidence systems. -/
theorem plane_survivors {n m q} (S : Fin m → Finset (Fin n))
    (I : Fin n → Finset (Fin m)) (inc : ∀ p i, i∈I p ↔ p∈S i)
    (valency : ∀ p, (I p).card = q+1)
    (joined : ∀ p z, (I p ∩ I z).Nonempty) (b : Finset (Fin n)) :
    m - (q*b.card+1) ≤ (Finset.univ.filter fun i => Disjoint (S i) b).card := by
  classical
  have hits (a : Finset (Fin n)) : (a.biUnion I).card ≤ q*a.card+1 := by
    induction a using Finset.induction_on with
    | empty => simp
    | @insert p a fresh ih =>
      rw [Finset.biUnion_insert,Finset.card_insert_of_notMem fresh,Nat.mul_add,Nat.mul_one]
      by_cases ne : a.Nonempty
      · obtain ⟨z,hz⟩ := ne
        obtain ⟨i,hi⟩ := joined p z
        have overlap : (I p ∩ a.biUnion I).Nonempty := ⟨i,Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hi).1,Finset.mem_biUnion.mpr ⟨z,hz,(Finset.mem_inter.mp hi).2⟩⟩⟩
        have := Finset.card_pos.mpr overlap
        have hu := Finset.card_union_add_card_inter (I p) (a.biUnion I)
        rw [valency] at hu
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp ne]
        simp [valency]
  have eq : (Finset.univ.filter fun i => Disjoint (S i) b) = Finset.univ \ b.biUnion I := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,Finset.mem_biUnion]
    constructor
    · rintro hd ⟨p,hp,hi⟩
      exact Finset.disjoint_left.mp hd ((inc p i).mp hi) hp
    · exact fun h => Finset.disjoint_left.mpr fun p hs hb => h ⟨p,hb,(inc p i).mpr hs⟩
  have tot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (b.biUnion I))
  rw [←eq] at tot
  simp only [Finset.card_univ,Fintype.card_fin] at tot
  have := hits b
  omega

/-- Binary AND/OR gates, arbitrary NOT count and arbitrary fanout. -/
theorem plane_tradeoff {n m q h} (C : Circuit) (good : legal C)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (lin : linear997 S)
    (sz : ∀ i, (S i).card=q+1)
    (sem : ∀ z : Finset (Fin n), ∀ i, value C (bits z) (o i)=true ↔ ¬Disjoint z (S i))
    (I : Fin n → Finset (Fin m)) (inc : ∀ p i, i∈I p ↔ p∈S i)
    (valency : ∀ p, (I p).card=q+1) (joined : ∀ p z, (I p ∩ I z).Nonempty) (leq : h≤q) :
    (m - (q*((2^(C.gates.countP (fun g => isNot g.op))-1)*h)+1))*h ≤ C.size := by
  have anti : Antitone (fun b : ℕ => m-(q*b+1)) := by
    intro a b ab
    exact Nat.sub_le_sub_left (Nat.add_le_add_right (Nat.mul_le_mul_left q ab) 1) m
  have main := stable_packing (h:=h) C good S o lin sz sem _ (plane_survivors S I inc valency joined) anti
  rwa [min_eq_left (by omega : h+1≤q+1),Nat.add_sub_cancel] at main

end LimitedNegation.Project
#print axioms LimitedNegation.Project.plane_tradeoff
