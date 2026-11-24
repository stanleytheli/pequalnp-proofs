import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Push

/-! Strict Hall expansion of a connected matching-covered bipartite support graph.
Only existence of an edge over each allowed cell matters in these Hall arguments;
parallel edge IDs can be chosen separately after extending prescribed cells. -/
namespace PositivePermanent.HallBlocks

open Finset
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def adjacency (N : A → Finset B) : Sum A B → Sum A B → Prop
  | .inl i, .inr j => j∈N i
  | .inr j, .inl i => j∈N i
  | _, _ => False

def graph (N : A → Finset B) : SimpleGraph (Sum A B) where
  Adj := adjacency N
  symm := ⟨by rintro (i|j) (k|l) <;> simp [adjacency]⟩
  loopless := ⟨by rintro (i|j) <;> simp [adjacency]⟩

abbrev Allowed (N : A → Finset B) : Prop :=
  ∀ i, ∀ j∈N i, ∃ p : A ≃ B, p i=j ∧ ∀ a, p a∈N a

abbrev PlusTwo (N : A → Finset B) : Prop :=
  ∀ S : Finset A, S.Nonempty → S.card+2≤Fintype.card A →
    S.card+2≤(S.biUnion N).card

private lemma path_keeps {V : Type*} (G : SimpleGraph V) (P : V → Prop)
    (same : ∀ x y, G.Adj x y → P x → P y) {x y} (h : G.Reachable x y) : P x → P y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact id
  | tail _ hxy ih => exact fun hx => same _ _ hxy (ih hx)

omit [Fintype B] [DecidableEq A] in
/-- If every present edge is in a perfect matching, equality in Hall's bound
separates S and N(S) from the rest of the graph. Connectedness forbids equality. -/
theorem strict_hall (N : A → Finset B) (conn : (graph N).Preconnected) (allowed : Allowed N)
    (S : Finset A) (nonempty : S.Nonempty) (proper : S≠univ) :
    S.card < (S.biUnion N).card := by
  classical
  by_contra! small
  let T:=S.biUnion N
  have inside (i : A) (j : B) (edge : j∈N i) : i∈S ↔ j∈T := by
    refine ⟨fun hi => mem_biUnion.mpr ⟨i,hi,edge⟩,?_⟩
    intro hj
    obtain ⟨p,hp,live⟩ := allowed i j edge
    have sub : S.image p ⊆ T := by
      rintro _ hz
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
      exact mem_biUnion.mpr ⟨a,ha,live a⟩
    have eq : S.image p=T := eq_of_subset_of_card_le sub (by
      rw [card_image_of_injective S p.injective]
      exact small)
    obtain ⟨a,ha,he⟩ := mem_image.mp (show j∈S.image p from eq ▸ hj)
    exact p.injective (he.trans hp.symm) ▸ ha
  let P : Sum A B → Prop := Sum.elim (·∈S) (·∈T)
  have same (u v : Sum A B) (h : (graph N).Adj u v) : P u → P v := by
    rcases u with i|j <;> rcases v with a|b
    · exact False.elim h
    · exact (inside i b h).mp
    · exact (inside a j h).mpr
    · exact False.elim h
  obtain ⟨i,hi⟩ := nonempty
  obtain ⟨a,_,ha⟩ := exists_mem_notMem_of_card_lt_card ((card_lt_iff_ne_univ S).mpr proper)
  exact ha (path_keeps _ P same (conn (.inl i) (.inl a)) hi)

omit [Fintype B] [DecidableEq A] in
/-- A connected matching-covered support either has a nontrivial Hall-plus-one block
or has Hall-plus-two expansion for all row sets leaving at least two rows outside. -/
theorem split_or_plus_two (N : A → Finset B) (conn : (graph N).Preconnected)
    (allowed : Allowed N) :
    (∃ S : Finset A, S.Nonempty ∧ S.card+2≤Fintype.card A ∧ (S.biUnion N).card=S.card+1) ∨ PlusTwo N := by
  classical
  by_cases h : PlusTwo N
  · exact Or.inr h
  · unfold PlusTwo at h
    push Not at h
    obtain ⟨S,hn,hs,hbad⟩ := h
    have proper : S≠univ := by
      rintro rfl
      simp only [card_univ] at hs
      omega
    have lower := strict_hall N conn allowed S hn proper
    exact Or.inl ⟨S,hn,hs,by omega⟩

/-- Both children of a Hall-plus-one split have balanced shores and strictly smaller
order. Their orders minus one add to the parent order minus one. -/
theorem split_dimensions (N : A → Finset B) (balance : Fintype.card A=Fintype.card B)
    (S : Finset A) (hn : S.Nonempty) (room : S.card+2≤Fintype.card A)
    (size : (S.biUnion N).card=S.card+1) :
    (univ \ S).card=(univ \ S.biUnion N).card+1 ∧
    2≤(S.biUnion N).card ∧ (S.biUnion N).card<Fintype.card A ∧
    2≤(univ \ S).card ∧ (univ \ S).card<Fintype.card A ∧
    ((S.biUnion N).card-1)+((univ \ S).card-1)=Fintype.card A-1 := by
  have hA := card_sdiff_add_card_eq_card (subset_univ S)
  have hB := card_sdiff_add_card_eq_card (subset_univ (S.biUnion N))
  simp only [card_univ] at hA hB
  have hs := card_pos.mpr hn
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Hall-plus-two permits simultaneous extension of any two allowed cells in
distinct rows and distinct columns to a single perfect matching. -/
theorem extend_two (N : A → Finset B) (balance : Fintype.card A=Fintype.card B)
    (plus : PlusTwo N) (a b : A) (x y : B) (ab : a≠b) (xy : x≠y)
    (ax : x∈N a) (by_ : y∈N b) :
    ∃ p : A ≃ B, p a=x ∧ p b=y ∧ ∀ i, p i∈N i := by
  classical
  let I : Finset A:={a,b}
  let J : Finset B:={x,y}
  let Outside := {i : A // i∉I}
  let available (u : Outside) := N u.val \ J
  have ni : I.card=2 := by simp [I,ab]
  have nj : J.card=2 := by simp [J,xy]
  have hall (T : Finset Outside) : T.card ≤ (T.biUnion available).card := by
    by_cases h0 : T=∅
    · simp [h0]
    let U := T.image Subtype.val
    have cu : U.card=T.card := card_image_of_injective _ Subtype.val_injective
    have us : U ⊆ univ \ I := by
      rintro _ h
      obtain ⟨t,_,rfl⟩ := mem_image.mp h
      exact mem_sdiff.mpr ⟨mem_univ _,t.prop⟩
    have room : U.card+2≤Fintype.card A := by
      have h := card_le_card us
      have eq := card_sdiff_add_card_eq_card (subset_univ I)
      rw [ni,card_univ] at eq
      omega
    have une : U.Nonempty := card_pos.mp (cu ▸ card_pos.mpr (nonempty_iff_ne_empty.mpr h0))
    have large := plus U une room
    have eq : T.biUnion available = U.biUnion N \ J := by
      ext z
      simp [U,available,mem_biUnion]
      aesop
    have delete := card_le_card_sdiff_add_card (s:=U.biUnion N) (t:=J)
    rw [eq]
    omega
  obtain ⟨q,qi,qp⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' available).mp hall
  let pin (u : I) := if u.val=a then x else y
  have pinI (u : I) : pin u∈J := by dsimp [pin];split <;> simp [J]
  have freeJ (u : Outside) : q u∉J := (mem_sdiff.mp (qp u)).2
  have pinInj : Function.Injective pin := by
    intro u v h
    have cases (z : I) : z.val=a ∨ z.val=b :=
      (mem_insert.mp (show z.val∈({a,b}:Finset A) from z.prop)).imp_right mem_singleton.mp
    have hu := cases u
    have hv := cases v
    apply Subtype.ext
    rcases hu with hu|hu <;> rcases hv with hv|hv <;> simp_all [pin,Ne.symm ab,Ne.symm xy]
  let f (i : A) := if h : i∈I then pin ⟨i,h⟩ else q ⟨i,h⟩
  have inj : Function.Injective f := by
    intro u v h
    by_cases hu : u∈I <;> by_cases hv : v∈I
    · exact congrArg Subtype.val (pinInj (by simpa [f,hu,hv] using h))
    · have he : pin ⟨u,hu⟩=q ⟨v,hv⟩ := by simpa [f,hu,hv] using h
      exact False.elim (freeJ ⟨v,hv⟩ (he ▸ pinI ⟨u,hu⟩))
    · have he : q ⟨u,hu⟩=pin ⟨v,hv⟩ := by simpa [f,hu,hv] using h
      exact False.elim (freeJ ⟨u,hu⟩ (he.symm ▸ pinI ⟨v,hv⟩))
    · exact congrArg Subtype.val (qi (by simpa [f,hu,hv] using h))
  let p := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,balance⟩)
  refine ⟨p,?_,?_,?_⟩
  · change f a=x
    simp [f,pin,I]
  · change f b=y
    simp [f,pin,I,ab.symm]
  · intro i
    change f i∈N i
    by_cases hi : i∈I
    · have cases : i=a ∨ i=b := by simpa [I] using hi
      rcases cases with rfl|rfl
      · simpa [f,pin,I] using ax
      · simpa [f,pin,I,ab.symm] using by_
    · simpa [f,hi] using (mem_sdiff.mp (qp ⟨i,hi⟩)).1

omit [Fintype B] in
/-- The precise local degree bounds used to avoid every two-by-two rectangle. -/
theorem brace_degrees (N : A → Finset B) (large : 4 ≤ Fintype.card A) (plus : PlusTwo N) :
    (∀ i, 3≤(N i).card) ∧ (∀ i j, i≠j → 4≤(N i ∪ N j).card) := by
  classical
  constructor
  · intro i
    simpa using plus {i} (by simp) (by simp;omega)
  · intro i j ne
    simpa [ne] using plus {i,j} (by simp) (by simp [ne];omega)

/-- A matching of a bipartite multigraph specifies a physical edge for each row
and uses every column just once. -/
def PhysicalMatching {E : Type*} [DecidableEq E] (row : E→A) (col : E→B) (M : Finset E) : Prop :=
  ∃ p : A≃B, ∃ w : A→E, (∀ i, row (w i)=i ∧ col (w i)=p i) ∧ M=univ.image w

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem allowed_of_used {E : Type*} [DecidableEq E] (row : E→A) (col : E→B) (N : A→Finset B)
    (cells : ∀ i j, j∈N i ↔ ∃ e, row e=i ∧ col e=j)
    (used : ∀ e, ∃ M, PhysicalMatching row col M ∧ e∈M) : Allowed N := by
  classical
  intro i j h
  obtain ⟨e,ri,cj⟩ := (cells i j).mp h
  obtain ⟨M,⟨p,w,hp,rfl⟩,em⟩ := used e
  obtain ⟨a,_,wa⟩ := mem_image.mp em
  have ai : a=i := (hp a).1.symm.trans ((congrArg row wa).trans ri)
  refine ⟨p,?_,fun a => (cells a (p a)).mpr ⟨w a,(hp a).1,(hp a).2⟩⟩
  rw [←ai]
  exact (hp a).2.symm.trans ((congrArg col wa).trans cj)

/-- Choosing parallel copies need not alter the two preassigned physical edge IDs. -/
theorem extend_two_physical {E : Type*} [DecidableEq E] (row : E→A) (col : E→B) (N : A→Finset B)
    (cells : ∀ i j, j∈N i ↔ ∃ e, row e=i ∧ col e=j)
    (balance : Fintype.card A=Fintype.card B) (plus : PlusTwo N) (e f : E)
    (rr : row e≠row f) (cc : col e≠col f) :
    ∃ M, PhysicalMatching row col M ∧ e∈M ∧ f∈M := by
  classical
  obtain ⟨p,pe,pf,ok⟩ := extend_two N balance plus (row e) (row f) (col e) (col f) rr cc
    ((cells _ _).mpr ⟨e,rfl,rfl⟩) ((cells _ _).mpr ⟨f,rfl,rfl⟩)
  have pick i := (cells i (p i)).mp (ok i)
  choose w hw hc using pick
  let v (i : A) := if i=row e then e else if i=row f then f else w i
  refine ⟨univ.image v,⟨p,v,?_,rfl⟩,?_,?_⟩
  · intro i
    by_cases a : i=row e
    · subst i; simp [v,pe]
    · by_cases b : i=row f
      · subst i; simp [v,a,pf]
      · simp [v,a,b,hw,hc]
  · exact mem_image.mpr ⟨row e,mem_univ _,by simp [v]⟩
  · exact mem_image.mpr ⟨row f,mem_univ _,by simp [v,rr.symm]⟩

omit [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem physical_independent {E : Type*} [DecidableEq E] {row : E→A} {col : E→B}
    {M : Finset E} (hm : PhysicalMatching row col M) {e f} (em : e∈M) (fm : f∈M) (ne : e≠f) :
    row e≠row f ∧ col e≠col f := by
  classical
  obtain ⟨p,w,h,rfl⟩ := hm
  obtain ⟨i,_,he⟩ := mem_image.mp em
  obtain ⟨j,_,hf⟩ := mem_image.mp fm
  subst e;subst f
  simpa only [(h i).1,(h j).1,(h i).2,(h j).2,p.injective.ne_iff] using
    And.intro (fun eq => ne (congrArg w eq)) (fun eq => ne (congrArg w eq))

#print axioms strict_hall
#print axioms split_or_plus_two
#print axioms extend_two
#print axioms extend_two_physical

end PositivePermanent.HallBlocks
