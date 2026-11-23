import Mathlib

/-! Two replacement and operand-slot counting lemmas for two AND layers. -/
namespace ORReplacement
open Finset

/-- For a sound raw-center term, one operand of its internal AND has at most
one nonneighbor of that center. The proof uses only the three-vertex tests. -/
theorem near_operand {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (A B : Finset V)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (safe : ∀ a∈A, ∀ b∈B, G.Adj z a ∨ G.Adj z b ∨ G.Adj a b) :
    (A.filter (fun a => ¬G.Adj z a)).card ≤ 1 ∨ (B.filter (fun b => ¬G.Adj z b)).card ≤ 1 := by
  classical
  by_contra! large
  obtain ⟨a,ha,c,hc,ac⟩ := Finset.one_lt_card.mp large.1
  obtain ⟨b,hb,d,hd,bd⟩ := Finset.one_lt_card.mp large.2
  have cross {u v : V} (hu : u∈A.filter (fun a => ¬ G.Adj z a))
      (hv : v∈B.filter (fun b => ¬G.Adj z b)) : G.Adj u v :=
    ((safe u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1).resolve_left
      (Finset.mem_filter.mp hu).2).resolve_left (Finset.mem_filter.mp hv).2
  exact (c4 a b c d (cross ha hb) (cross hc hb).symm (cross hc hd) (cross ha hd).symm).elim ac bd

/-- If a singleton operand has at least two stray neighbors, replacing its
absorbed AND signal by that operand can spoil at most one receiving center. -/
theorem unique_wrong_receiver {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) (B T : Finset V)
    (c4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (safe : ∀ z∈T, ∀ b∈B, G.Adj z a ∨ G.Adj z b ∨ G.Adj a b)
    (stray : 2 ≤ (B.filter (fun b => ¬G.Adj a b)).card) :
    (T.filter (fun z => ¬ G.Adj z a)).card ≤ 1 := by
  classical
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp stray
  have cross {z b : V} (hz : z∈T.filter (fun z => ¬ G.Adj z a))
      (hb : b∈B.filter (fun b => ¬G.Adj a b)) : G.Adj z b :=
    ((safe z (Finset.mem_filter.mp hz).1 b (Finset.mem_filter.mp hb).1).resolve_left
      (Finset.mem_filter.mp hz).2).resolve_right (Finset.mem_filter.mp hb).2
  apply Finset.card_le_one.mpr
  intro z hz w hw
  exact (c4 z u w v (cross hz hu) (cross hw hu).symm (cross hw hv) (cross hz hv).symm).resolve_right ne

/-- Every deleted proxy or newly zero OR wire has an outgoing zero operand
slot or is itself one of the newly zero designated queries. -/
theorem delete_slots {W : Type*} [DecidableEq W]
    (sources zero mixed dead : Finset W) (left right single : W → W)
    (fresh : Disjoint sources zero)
    (used : ∀ w∈sources∪zero, w∈zero.image left ∨ w∈zero.image right ∨
      w∈mixed.image single ∨ w∈dead) :
    sources.card  ≤  zero.card+mixed.card+dead.card := by
  have sub : sources∪zero ⊆ (zero.image left∪zero.image right) ∪ (mixed.image single∪dead) := by
    intro w hw
    rcases used w hw with h | h | h | h <;> simp [h]
  have c := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint fresh] at c
  have x := Finset.card_union_le (zero.image left) (zero.image right)
  have y := Finset.card_union_le (mixed.image single) dead
  have z := Finset.card_union_le (zero.image left∪zero.image right) (mixed.image single∪dead)
  have x1 : (zero.image left).card ≤ zero.card := Finset.card_image_le
  have x2 : (zero.image right).card ≤ zero.card := Finset.card_image_le
  have y1 : (mixed.image single).card ≤ mixed.card := Finset.card_image_le
  omega

end ORReplacement

#print axioms ORReplacement.near_operand
#print axioms ORReplacement.unique_wrong_receiver
#print axioms ORReplacement.delete_slots
