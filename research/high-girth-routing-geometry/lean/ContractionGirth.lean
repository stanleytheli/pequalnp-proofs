import FlowCycle
import Mathlib.Tactic

namespace SparsePermanent.Contract
open Finset SimpleGraph
variable {I : Type} [Fintype I] [DecidableEq I]

def underlying (E : I→I→Prop) : SimpleGraph I where
  Adj a b:=a≠b ∧ (E a b ∨ E b a)
  symm:=⟨fun _ _ h=>⟨h.1.symm,h.2.symm⟩⟩
  loopless:=⟨fun _ h=>h.1 rfl⟩

private def embedding {A : Type} (f : A↪I) (E : I→I→Prop) :
    bipGraph (fun x y : A=>E (f x) (f y)) ↪g bipGraph E where
  toFun:=Sum.map f f
  inj':=Sum.map_injective.mpr ⟨f.injective,f.injective⟩
  map_rel_iff':=by rintro (a|a) (b|b) <;> rfl

/-- At least 2|A| distinct allowed bipartite entries on a set of |A| pairs
force a physical cycle of length at most 2|A|. -/
theorem dense_patch {A J : Type} [Fintype A] [Nonempty A] [Fintype J]
    (f : A↪I) (E : I→I→Prop) (entries : J↪A×A)
    (valid : ∀j,E (f (entries j).1) (f (entries j).2))
    (large : 2*Fintype.card A≤Fintype.card J) :
    (bipGraph E).egirth≤((2*Fintype.card A : ℕ) : ℕ∞) := by
  classical
  let G:=bipGraph (fun x y : A=>E (f x) (f y))
  let edge (j : J) : G.edgeSet:=
    ⟨s(Sum.inl (entries j).1,Sum.inr (entries j).2),valid j⟩
  have inj : Function.Injective edge := by
    intro i j h
    have eq:=Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases eq with h|h
    · exact entries.injective (Prod.ext (Sum.inl.inj h.1) (Sum.inr.inj h.2))
    · cases h.1
  have card : Fintype.card J≤G.edgeSet.ncard := by
    simpa [Nat.card_eq_fintype_card,Set.ncard_eq_toFinset_card'] using Nat.card_le_card_of_injective edge inj
  obtain ⟨a,p,hp⟩:=G.exists_isCycle_of_card_le (by simpa [Nat.card_eq_fintype_card,two_mul] using large.trans card)
  let emb:=embedding f E
  have lift : (p.map emb.toHom).IsCycle:=hp.map emb.injective
  have upper:p.length≤2*Fintype.card A:=by simpa [Nat.card_eq_fintype_card,two_mul] using hp.length_le_natCard
  rw [←p.length_map emb.toHom] at upper
  exact lift.egirth_le_length.trans (by exact_mod_cast upper)

private theorem cycle_support {G : SimpleGraph I} {a : I} (p : G.Walk a a) (hp : p.IsCycle) :
    ∀ x∈p.support,x∈p.support.tail := by
  cases p with
  | nil=>exact (hp.ne_nil rfl).elim
  | @cons a b _ ab q=>
    intro x h
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ q.end_mem_support
    · exact h

/-- A simple cycle after perfect matching contraction yields a physical cycle
of length at most twice its length. It suffices to count the matching edges
and the distinct off-matching edges on that cycle's pairs. -/
theorem cycle_lifts (E : I→I→Prop) (matching : ∀x,E x x) {a : I}
    (p : (underlying E).Walk a a) (hp : p.IsCycle) :
    (bipGraph E).egirth≤((2*p.length : ℕ) : ℕ∞) := by
  classical
  let S:=p.support.tail.toFinset
  let A:=p.edges.toFinset
  have membership (x : I) (hx:x∈p.support) : x∈S:=by simpa [S] using cycle_support p hp x hx
  have cardS : S.card=p.length := by simp [S,List.toFinset_card_of_nodup hp.support_nodup]
  have cardA : A.card=p.length := by simp [A,List.toFinset_card_of_nodup hp.edges_nodup]
  let f : S↪I:=Function.Embedding.subtype _
  have data (e : A) : ∃xy : S×S,xy.1≠xy.2 ∧ E xy.1 xy.2 ∧ s(xy.1.val,xy.2.val)=e.val := by
    have listed : e.val∈p.edges:=List.mem_toFinset.mp e.prop
    have reason (e' : Sym2 I) (mem:e'∈p.edges) :
        ∃xy : S×S,xy.1≠xy.2 ∧ E xy.1 xy.2 ∧ s(xy.1.val,xy.2.val)=e' := by
      induction e' using Sym2.inductionOn with
      | _ x y=>
        have adjacent := p.edges_subset_edgeSet mem
        have ok : x≠y ∧ (E x y ∨ E y x):=adjacent
        have xs := membership x (p.mem_support_of_mem_edges mem (Sym2.mem_mk_left _ _))
        have ys := membership y (p.mem_support_of_mem_edges mem (Sym2.mem_mk_right _ _))
        rcases ok.2 with d|d
        · exact ⟨(⟨x,xs⟩,⟨y,ys⟩),fun h=>ok.1 (congrArg Subtype.val h),d,rfl⟩
        · exact ⟨(⟨y,ys⟩,⟨x,xs⟩),fun h=>ok.1 (congrArg Subtype.val h).symm,d,Sym2.eq_swap⟩
    exact reason e.val listed
  choose xy distinct allowed origin using data
  let pair : S⊕A→S×S:=Sum.elim (fun x=>(x,x)) xy
  have inj : Function.Injective pair := by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl (congrArg Prod.fst h)
    · exact (distinct j ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))).elim
    · exact (distinct i ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)).elim
    · apply congrArg Sum.inr
      apply Subtype.ext
      rw [←origin i,←origin j]
      exact congrArg (fun q : S×S=>s(q.1.val,q.2.val)) h
  have existsS:Nonempty S:=⟨⟨a,membership a p.start_mem_support⟩⟩
  have result:=dense_patch f E ⟨pair,inj⟩ (by rintro (x|e);exact matching _;exact allowed e) (by simp [cardS,cardA,two_mul])
  simpa [cardS] using result

theorem girth (E : I→I→Prop) (matching:∀x,E x x) (r : ℕ)
    (h : ((2*r : ℕ) : ℕ∞)<(bipGraph E).egirth) : (r : ℕ∞)<(underlying E).egirth := by
  by_contra! small
  by_cases ac:(underlying E).IsAcyclic
  · simp [ac.egirth_eq_top] at small
  obtain ⟨a,p,hp,eq⟩:=SimpleGraph.exists_egirth_eq_length.mpr ac
  rw [eq] at small
  have c:p.length≤r:=by exact_mod_cast small
  exact (not_le_of_gt h) ((cycle_lifts E matching p hp).trans (by exact_mod_cast Nat.mul_le_mul_left 2 c))

end SparsePermanent.Contract
#print axioms SparsePermanent.Contract.girth
