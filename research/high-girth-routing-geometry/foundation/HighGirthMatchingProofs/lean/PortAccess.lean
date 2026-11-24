import DirectedGrowth

namespace SparsePermanent.DirectedGrowth
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Route.mono {E : V→V→Prop} {F G : Finset V} {a b : V} {t : ℕ}
    (r : Route E F a b t) (small : G⊆F) : Route E G a b t := by
  induction r with
  | nil safe=>exact .nil (fun h=>safe (small h))
  | snoc _ edge safe ih=>exact .snoc ih edge (fun h=>safe (small h))

/-- One may reserve only the at most t+1 vertices of an avoiding walk. -/
theorem Route.support {E : V→V→Prop} {F : Finset V} {a b : V} {t : ℕ}
    (r : Route E F a b t) : ∃ S : Finset V, Disjoint S F ∧ S.card≤t+1 ∧ Route E (univ\S) a b t := by
  classical
  induction r with
  | nil safe=>
    exact ⟨{_},by simpa using safe,by simp,.nil (by simp)⟩
  | @snoc b c t w edge safe ih=>
    obtain ⟨S,sf,sz,inside⟩:=ih
    refine ⟨insert c S,disjoint_insert_left.mpr ⟨safe,sf⟩,?_,?_⟩
    · have le:=card_insert_le c S; omega
    · exact .snoc (inside.mono (sdiff_subset_sdiff_right univ (subset_insert ..))) edge (by simp)

/-- A port can reach leaves through its private protected trunk and one of L
pairwise-disjoint terminal subtrees. Every such subtree has at least W leaves
outside the common protected region; branches are directed toward the leaves.
For an incoming port use the reverse digraph. -/
structure Port (E : V→V→Prop) (P : Finset V) (L W r : ℕ) where
  origin : V
  trunk : Finset V
  trunk_in : trunk⊆P
  group : Fin L→Finset V
  leaves : Fin L→Finset V
  separate : Pairwise (fun i j=>Disjoint (group i) (group j))
  in_group : ∀ i,leaves i⊆group i
  many : ∀ i,W≤(leaves i).card
  out_P : ∀ i,Disjoint (leaves i) P
  clear : ∀ i,(group i)∩P ⊆ trunk
  access : ∀ i y,y∈leaves i → ∃ t≤r,Route E (univ\(trunk∪group i)) origin y t

namespace Port
variable {E : V→V→Prop} {P : Finset V} {L W r : ℕ} (p : Port E P L W r)

noncomputable def good (U : Finset V) : Finset (Fin L) := by
  classical exact univ.filter (fun i=>Disjoint (p.group i) U)
noncomputable def available (U : Finset V) : Finset V := (p.good U).biUnion p.leaves

private theorem good_size (U : Finset V) : L-U.card≤(p.good U).card := by
  classical
  let bad:=(univ:Finset (Fin L))\p.good U
  have choice (i : bad) : ∃ x,x∈U ∧ x∈p.group i.val := by
    have ng: i.val∉p.good U := (mem_sdiff.mp i.prop).2
    have nd : ¬Disjoint (p.group i.val) U := fun h=>ng (mem_filter.mpr ⟨mem_univ _,h⟩)
    obtain ⟨x,hx,hy⟩:=not_disjoint_iff.mp nd
    exact ⟨x,hy,hx⟩
  choose witness hu hi using choice
  let f (i : bad) : U := ⟨witness i,hu i⟩
  have injective : Function.Injective f := by
    intro i j e
    apply Subtype.ext
    by_contra ij
    have same : witness i=witness j := congrArg Subtype.val e
    exact disjoint_left.mp (p.separate ij) (hi i) (same ▸ hi j)
  have bound:=card_le_card_of_injective injective
  have diff : bad.card=L-(p.good U).card := by simp [bad,card_sdiff_of_subset]
  have cap : (p.good U).card≤L := by simpa using card_le_univ (p.good U)
  omega

theorem sufficient (U : Finset V) : (L-U.card)*W≤(p.available U).card := by
  classical
  have dis : ((p.good U : Finset (Fin L)) : Set (Fin L)).PairwiseDisjoint p.leaves := by
    intro i _ j _ ne
    exact (p.separate ne).mono (p.in_group i) (p.in_group j)
  rw [available,card_biUnion dis]
  calc
    _ ≤ (p.good U).card*W := Nat.mul_le_mul_right _ (good_size p U)
    _ = ∑ _i∈p.good U,W := by simp
    _ ≤ _ := sum_le_sum (fun i _=>p.many i)

theorem clean (U : Finset V) : Disjoint (p.available U) (P∪U) := by
  classical
  apply disjoint_left.mpr
  intro x hx forbid
  obtain ⟨i,good,leaf⟩:=mem_biUnion.mp hx
  rcases mem_union.mp forbid with prot|used
  · exact disjoint_left.mp (p.out_P i) leaf prot
  · exact disjoint_left.mp (mem_filter.mp good).2 (p.in_group i leaf) used

theorem approach (U : Finset V) (tu : Disjoint p.trunk U) {y : V} (hy : y∈p.available U) :
    ∃ t≤r,Route E (U∪(P\p.trunk)) p.origin y t := by
  classical
  obtain ⟨i,good,leaf⟩:=mem_biUnion.mp hy
  have cleanGroup : Disjoint (p.group i) U := (mem_filter.mp good).2
  obtain ⟨t,ht,ride⟩:=p.access i y leaf
  refine ⟨t,ht,ride.mono ?_⟩
  intro z hz
  refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
  rcases mem_union.mp hz with used|prot
  · intro member
    rcases mem_union.mp member with trunk|group
    · exact disjoint_left.mp tu trunk used
    · exact disjoint_left.mp cleanGroup group used
  · obtain ⟨prot,no⟩:=mem_sdiff.mp prot
    intro member
    rcases mem_union.mp member with trunk|group
    · exact no trunk
    · exact no (p.clear i (mem_inter.mpr ⟨group,prot⟩))

end Port

/-- Join two still-free ports while avoiding all previous routes and all
protected vertices outside the two selected trunks. The reserved support is
small enough to enter the next step of the all-pairs routing induction. -/
theorem link {E : V→V→Prop} {P : Finset V} {L W r k : ℕ} (a : Port E P L W r)
    (b : Port (fun x y=>E y x) P L W r) (U : Finset V) (hk : 0<k)
    (outE : Expands E k) (inE : Expands (fun x y=>E y x) k)
    (af : Disjoint a.trunk U) (bf : Disjoint b.trunk U)
    (capacity : 2*k*(P∪U).card≤(L-U.card)*W) (positive : 0<(L-U.card)*W) :
    ∃ S : Finset V,Disjoint S U ∧ S∩P⊆a.trunk∪b.trunk ∧
      ∃ t≤2*r+4*k*(Nat.log 2 (Fintype.card V)+1), S.card≤t+1 ∧ Route E (univ\S) a.origin b.origin t := by
  classical
  have aa:=a.sufficient U
  have bb:=b.sufficient U
  obtain ⟨i,hi,j,hj,d,hd,mid⟩:=connect E (P∪U) (a.available U) (b.available U) hk outE inE
    (capacity.trans aa) (capacity.trans bb) (positive.trans_le aa) (positive.trans_le bb) (a.clean U) (b.clean U)
  obtain ⟨ra,hra,rootA⟩:=a.approach U af hi
  obtain ⟨rb,hrb,rootB⟩:=b.approach U bf hj
  let F:=U∪(P\(a.trunk∪b.trunk))
  have left : F⊆U∪(P\a.trunk) := union_subset_union_right (sdiff_subset_sdiff_right P subset_union_left)
  have right : F⊆U∪(P\b.trunk) := union_subset_union_right (sdiff_subset_sdiff_right P subset_union_right)
  have middle : F⊆P∪U := by
    intro z hz
    rcases mem_union.mp hz with used|prot
    · exact mem_union_right _ used
    · exact mem_union_left _ (mem_sdiff.mp prot).1
  have w:=((rootA.mono left).trans (mid.mono middle)).trans ((rootB.mono right).reverse)
  obtain ⟨S,sf,sz,inside⟩:=w.support
  refine ⟨S,sf.mono_right subset_union_left,?_,_,by omega,sz,inside⟩
  intro z hz
  obtain ⟨member,hp⟩:=mem_inter.mp hz
  by_contra out
  exact disjoint_left.mp sf member (mem_union_right _ (mem_sdiff.mpr ⟨hp,out⟩))

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.link
