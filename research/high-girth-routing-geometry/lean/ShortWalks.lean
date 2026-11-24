import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

namespace SparsePermanent.ShortWalks
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- A walk whose edges follow the specified orientation of the graph. -/
inductive Follows (E : V→V→Prop) : {a b : V}→G.Walk a b→Prop
 | nil (a : V) : Follows E (Walk.nil (u:=a))
 | cons {a b c : V} {edge : G.Adj a b} {p : G.Walk b c} :
     E a b→Follows E p→Follows E (.cons edge p)

theorem Follows.chain {E : V→V→Prop} (asym : ∀⦃x y⦄,E x y→¬ E y x)
    {a b : V} {p : G.Walk a b} (h : Follows E p) : List.IsChain (·≠·) p.edges := by
  induction h with
  | nil=>simp
  | @cons a b c edge p ab hp ih=>
    cases hp with
    | nil=>simp
    | @cons _ d _ bd q hd _=>
      rw [Walk.edges_cons,Walk.edges_cons,List.isChain_cons_cons]
      refine ⟨?_,ih⟩
      intro e
      rcases Sym2.eq_iff.mp e with he|he
      · exact edge.ne he.1
      · exact asym ab (he.1.symm ▸ hd)

theorem Follows.induce {E : V→V→Prop} {a b : V} {p : G.Walk a b}
    (h : Follows E p) (S : Set V) (inside : ∀x∈p.support,x∈S) :
    Follows (fun x y : S=>E x.val y.val) (p.induce S inside) := by
  induction h with
  | nil=>exact .nil _
  | cons ab rest ih=>exact .cons ab (ih _)

theorem small_acyclic [Fintype V] (S : Finset V) (short : (S.card : ℕ∞)<G.egirth) :
    (G.induce (S : Set V)).IsAcyclic := by
  intro a p hp
  have embedded : (p.map (Embedding.induce (G:=G) (S : Set V)).toHom).IsCycle := hp.map (Embedding.induce (G:=G) (S : Set V)).injective
  have lo := embedded.egirth_le_length
  rw [Walk.length_map] at lo
  have hi := hp.length_le_enatCard
  have size : ENat.card (S : Set V)=S.card := by simp
  rw [size] at hi
  exact (not_le_of_gt short) (lo.trans hi)

/-- In high girth, a consistently oriented walk of at most R edges is a
simple path whenever R+1 is smaller than the girth. -/
theorem Follows.path [Fintype V] {E : V→V→Prop} (asym : ∀⦃x y⦄,E x y→¬E y x)
    {a b : V} {p : G.Walk a b} (h : Follows E p) (short : (p.length+1 : ℕ)<G.egirth) : p.IsPath := by
  classical
  let S:=p.support.toFinset
  have card : S.card≤p.length+1:=by simpa using p.support.toFinset_card_le
  have ac:=small_acyclic (G:=G) S (lt_of_le_of_lt (by exact_mod_cast card) short)
  have inside (x : V) (hx : x∈p.support) : x∈(S : Set V):=by simpa [S]
  have lifted:=h.induce (S : Set V) inside
  exact Walk.isPath_induce.mp ((ac.isPath_iff_isChain _).2 (lifted.chain (fun ⦃_ _⦄ hh=>asym hh)))

/-- Equal endpoints force equality of short directed walks even when their
orientations differ, provided each individual orientation is asymmetric. -/
theorem unique [Fintype V] {E D : V→V→Prop} {a b : V} {p q : G.Walk a b}
    (hE : ∀⦃x y⦄,E x y→¬E y x) (hD : ∀⦃x y⦄,D x y→¬D y x)
    (fp : Follows E p) (fq : Follows D q) {R : ℕ}
    (plen : p.length≤R) (qlen : q.length≤R) (short : (2*R+1 : ℕ)<G.egirth) : p=q := by
  have lo : (R+1 : ℕ)≤(2*R+1 : ℕ∞) := by exact_mod_cast (by omega : R+1≤2*R+1)
  have hp:=fp.path hE (lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right plen 1) (lo.trans_lt short))
  have hq:=fq.path hD (lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right qlen 1) (lo.trans_lt short))
  by_contra different
  obtain ⟨_,_,_,c,hc,len⟩:=hp.exists_isCycle_length_le_add_of_ne hq different
  have limit:c.length≤2*R+1:=by omega
  exact (not_le_of_gt short) (hc.egirth_le_length.trans (by exact_mod_cast limit))

end SparsePermanent.ShortWalks
#print axioms SparsePermanent.ShortWalks.unique
