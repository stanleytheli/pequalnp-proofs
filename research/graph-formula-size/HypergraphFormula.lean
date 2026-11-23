import FormulaRank

/-! Incidence bounds for finite linear hypergraphs with no Berge cycles of length three or four. -/
namespace WeightedFormula.Hypergraph
open Finset Sym2

private theorem oriented_occurrences {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (f : Formula V) (edge : E → Finset V) (target : E → V) (owner : ∀ e, target e∈edge e)
    (pos neg : E → V → Bool) (priv : V → V → Bool)
    (diag : ∀ e, f.label (f.route (pos e) (neg e))=some (target e))
    (offDiag : ∀ v e j, (v∈edge e) → (v∈edge j) →
      e≠j → f.label (f.route (pos e) (neg j))=some v)
    (privateCol : ∀ v e, (v∈edge e) →
      f.label (f.route (pos e) (priv v))=some v) (v : V) :
    (Finset.univ.filter (fun e => v∈edge e ∧ target e≠v)).card +
      (if v∈Finset.univ.image target then 1 else 0) ≤ (f.occSet v).card := by
  classical
  let away (v : V) := Finset.univ.filter (fun e => v∈edge e ∧ target e≠v)
  let cover := (Finset.univ : Finset E).image target
  have hlocal (v : V) : (away v).card + (if v∈cover then 1 else 0) ≤ (f.occSet v).card := by
    have away_iff (e : E) : e ∈ away v ↔ (v∈edge e ∧ target e≠v) := by simp [away]
    have gen (S : Finset E) (hS : ∀ e∈S, v∈edge e)
        (unique : ∀ e∈S, ∀ j∈S, target e=v → target j=v → e=j) :
        S.card ≤ (f.occSet v).card := by
      let miss := Finset.univ.filter (fun i : S => target i.val ≠ v)
      let x (i : S) := pos i.val
      let A := f.eventMatrix v x
      have hbase : (fun _ : S => (1:ℚ)) ∈ LinearMap.range A.mulVecLin := by
        convert f.event_range v x (priv v) using 1
        ext i
        simp [x,privateCol v i.val (hS _ i.property)]
      have hu : ∀ i j : S, i∉miss → j∉miss → i=j := by
        intro i j hi hj
        apply Subtype.ext
        exact unique i.val i.property j.val j.property (by simpa [miss] using hi) (by simpa [miss] using hj)
      have hm (i : S) (hi : i∈miss) :
          (fun j : S => if j=i then (0:ℚ) else 1) ∈ LinearMap.range A.mulVecLin := by
        have nd : target i.val≠v := by simpa [miss] using hi
        convert f.event_range v x (neg i.val) using 1
        ext j
        by_cases ji : j=i
        · subst j
          simp [x,diag,nd]
        · have ne : j.val≠i.val := fun e => ji (Subtype.ext e)
          simp [x,ji,offDiag v j.val i.val (hS _ j.property) (hS _ i.property) ne]
      simpa using rank_from_columns A miss hu hbase hm
    by_cases hv : v∈cover
    · obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hv
      have px : p ∉ away v := by
        intro h
        exact ((away_iff p).mp h).2 hp
      have bound := gen (insert p (away v)) (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · simpa [hp] using owner e
        · exact ((away_iff e).mp he).1) (by
        intro e he j hj heq hjq
        have only (y) (hy : y ∈ insert p (away v)) (hyq : target y=v) : y=p := by
          rcases Finset.mem_insert.mp hy with hy | hy
          · exact hy
          · exact False.elim (((away_iff y).mp hy).2 hyq)
        exact (only e he heq).trans (only j hj hjq).symm)
      simpa [hv,px] using bound
    · have bound := gen (away v) (fun e he => ((away_iff e).mp he).1)
          (fun e he _ _ heq _ => False.elim (((away_iff e).mp he).2 heq))
      simpa [hv] using bound
  exact hlocal v

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
/-- Distinct hyperedges intersect in at most one vertex. The other two fields exclude
Berge triangles and quadrangles, with distinct vertices and edges in each cycle. -/
structure Sparse (edge : E → Finset V) : Prop where
  two : ∀ e, ∃ x∈edge e, ∃ y∈edge e, x≠y
  linear : ∀ {e j x y}, x∈edge e → x∈edge j → y∈edge e → y∈edge j → x≠y → e=j
  triangle : ∀ {i j k : E} {a b c : V}, [i,j,k].Nodup →
    [a,b,c].Nodup → a∈edge i → a∈edge j → b∈edge j → b∈edge k → c∈edge k → c∈edge i → False
  quadrangle : ∀ {i j k l : E} {a b c d : V}, [i,j,k,l].Nodup →
    [a,b,c,d].Nodup → a∈edge i → a∈edge j → b∈edge j → b∈edge k →
    c∈edge k → c∈edge l → d∈edge l → d∈edge i → False

def petals (edge : E → Finset V) (e : E) (x : V) : Prop :=
  x∉edge e ∧ ∃ a∈edge e, ∃ j, a∈edge j ∧ x∈edge j
def neighbors (edge : E → Finset V) (a x : V) : Prop :=
  a≠x ∧ ∃ j, a∈edge j ∧ x∈edge j

omit [Fintype V] [Fintype E] in
private theorem petal_negative (edge : E → Finset V) (H : Sparse edge) (e k : E) :
    ¬∀ x∈edge k, petals edge e x := by
  intro pos
  obtain ⟨x,hx,y,hy,xy⟩ := H.two k
  obtain ⟨xe,a,ae,j,aj,xj⟩ := pos x hx
  obtain ⟨ye,b,be,l,bl,yl⟩ := pos y hy
  have ak : a∉edge k := fun ha => (pos a ha).1 ae
  have bk : b∉edge k := fun hb => (pos b hb).1 be
  have jl : j≠l := by
    rintro rfl
    exact ak ((H.linear hx xj hy yl xy).symm ▸ aj)
  by_cases ab : a=b
  · subst b
    apply H.triangle (i:=j) (j:=k) (k:=l) (a:=x) (b:=y) (c:=a)
    all_goals first | assumption | (simp; grind)
  · apply H.quadrangle (i:=e) (j:=j) (k:=k) (l:=l) (a:=a) (b:=x) (c:=y) (d:=b)
    all_goals first | assumption | (simp; grind)

omit [Fintype V] [Fintype E] [DecidableEq V] in
private theorem neighbor_negative (edge : E → Finset V) (H : Sparse edge) (a : V) (k : E) :
    ¬∀ x∈edge k, neighbors edge a x := by
  intro pos
  obtain ⟨x,hx,y,hy,xy⟩ := H.two k
  obtain ⟨ax,j,aj,xj⟩ := pos x hx
  obtain ⟨ay,l,al,yl⟩ := pos y hy
  have ak : a∉edge k := fun ha => (pos a ha).1 rfl
  have jl : j≠l := by
    rintro rfl
    exact ak ((H.linear hx xj hy yl xy).symm ▸ aj)
  apply H.triangle (i:=j) (j:=k) (k:=l) (a:=x) (b:=y) (c:=a)
  all_goals first | assumption | (simp; grind)

theorem hypergraph_orientation (edge : E → Finset V) (H : Sparse edge) (f : Formula V)
    (correct : ∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) :
    ∃ target : E → V, (∀ e, target e∈edge e) ∧ ∀ v,
      (univ.filter (fun e => v∈edge e ∧ target e≠v)).card+
        (if v∈univ.image target then 1 else 0) ≤ (f.occSet v).card := by
  classical
  let pos (e : E) (v : V) : Bool := decide (v∈edge e)
  let neg (e : E) (v : V) : Bool := decide (petals edge e v)
  let priv (a v : V) : Bool := decide (neighbors edge a v)
  have hp (e : E) : f.eval (pos e)=true := (correct _).mpr ⟨e,fun v hv => by simp [pos,hv]⟩
  have hn (e : E) : f.eval (neg e)=false := by
    cases h : f.eval (neg e) with
    | false => rfl
    | true =>
      obtain ⟨k,hk⟩ := (correct _).mp h
      exact (petal_negative edge H e k (fun v hv => of_decide_eq_true (hk v hv))).elim
  have hq (a : V) : f.eval (priv a)=false := by
    cases h : f.eval (priv a) with
    | false => rfl
    | true =>
      obtain ⟨k,hk⟩ := (correct _).mp h
      exact (neighbor_negative edge H a k (fun v hv => of_decide_eq_true (hk v hv))).elim
  choose target diag hpos hneg using fun e => f.route_valid (pos e) (neg e) (hp e) (hn e)
  have own (e : E) : target e∈edge e := of_decide_eq_true (hpos e)
  refine ⟨target,own,?_⟩
  intro v
  apply oriented_occurrences f edge target own pos neg priv diag
  · intro a e j ae aj ej
    obtain ⟨w,hw,pw,nw⟩ := f.route_valid _ _ (hp e) (hn j)
    have we : w∈edge e := of_decide_eq_true pw
    suffices w=a by simpa [this] using hw
    by_contra wa
    have wj : w∉edge j := fun t => ej (H.linear we t ae aj wa)
    exact (of_decide_eq_false nw) ⟨wj,a,aj,e,ae,we⟩
  · intro a e ae
    obtain ⟨w,hw,pw,nw⟩ := f.route_valid _ _ (hp e) (hq a)
    suffices w=a by simpa [this] using hw
    by_contra wa
    exact (of_decide_eq_false nw) ⟨Ne.symm wa,e,ae,of_decide_eq_true pw⟩
private theorem join_list {V I : Type*} (S : Finset I) (g : I→Formula V)
    (hs : S.Nonempty) : ∃ f : Formula V,
      (∀ x, f.eval x=true ↔ ∃ i∈S, (g i).eval x=true) ∧ f.leaves=∑ i∈S, (g i).leaves := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert i S hi ih =>
    by_cases h : S.Nonempty
    · obtain ⟨z,hz,hl⟩ := ih h
      refine ⟨.join (g i) z,fun x => ?_,?_⟩
      · simp [Formula.eval,hz]
      · simp [Formula.leaves,hl,hi]
    · have eq : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst S
      exact ⟨g i,by simp,by simp⟩

omit [Fintype V] in
private theorem meet_vars (S : Finset V) (hs : S.Nonempty) : ∃ f : Formula V,
    (∀ x, f.eval x=true ↔ ∀ v∈S, x v=true) ∧ f.leaves=S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert a S ha ih =>
    by_cases h : S.Nonempty
    · obtain ⟨z,hz,hl⟩ := ih h
      exact ⟨.meet (.var a) z,fun x => by simp [Formula.eval,hz],by simp [Formula.leaves,hl,ha,Nat.add_comm]⟩
    · have eq : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst S
      exact ⟨.var a,by simp [Formula.eval],by simp [Formula.leaves]⟩

theorem hypergraph_lower (edge : E → Finset V) (H : Sparse edge) (f : Formula V)
    (correct : ∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) :
    ∃ T : Finset V, (∀ e, ∃ v∈edge e, v∈T) ∧
       (∑ e, ((edge e).card-1)) + T.card ≤ f.gates + 1 := by
  classical
  obtain ⟨owner,own,localBound⟩ := hypergraph_orientation edge H f correct
  let T := univ.image owner
  refine ⟨T,fun e => ⟨owner e,own e,mem_image_of_mem owner (mem_univ _)⟩,?_⟩
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => localBound v)
  rw [Finset.sum_add_distrib] at sum
  have a : (∑ v, (univ.filter (fun e => v∈edge e ∧ owner e≠v)).card) =
          ∑ e, ((edge e).card-1) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have eq : univ.filter (fun v => v∈edge e ∧ owner e≠v) = (edge e).erase (owner e) := by
      ext v
      simp [and_comm,ne_comm]
    rw [←Finset.card_filter,eq,Finset.card_erase_of_mem (own e)]
  have count : (∑ v : V, if v∈T then 1 else 0) = T.card := by simp
  have leaves : (∑ v : V, (f.occSet v).card) ≤ f.leaves := by
    simp only [Formula.occSet,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm, ← f.card_leaf,← Finset.card_univ,Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro l _
    cases f.label l <;> simp
  rw [←f.leaves_eq]
  simpa [a,count,T] using sum.trans leaves

omit [Fintype V] in
theorem hypergraph_upper [Nonempty E] (edge : E → Finset V) (H : Sparse edge)
    (owner : E → V) (own : ∀ e, owner e∈edge e) :
    ∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) ∧
      f.gates+1 = (∑ e, ((edge e).card-1))+(univ.image owner).card := by
  classical
  have tail_nonempty (e : E) : ((edge e).erase (owner e)).Nonempty := by
    obtain ⟨a,ha,b,hb,ne⟩ := H.two e
    by_cases av : a=owner e
    · exact ⟨b,Finset.mem_erase.mpr ⟨by grind,hb⟩⟩
    · exact ⟨a,Finset.mem_erase.mpr ⟨av,ha⟩⟩
  choose tail ht hl using fun e => meet_vars ((edge e).erase (owner e)) (tail_nonempty e)
  let T := univ.image owner
  let fibre (v : V) := univ.filter (fun e => owner e=v)
  have group (v : V) (hv : v∈T) : (fibre v).Nonempty := by
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hv
    exact ⟨e,by simp [fibre,he]⟩
  let inner (v : V) := if hv : v∈T then (join_list (fibre v) tail (group v hv)).choose else .const false
  have spec (v : V) (hv : v∈T) : (∀ x, (inner v).eval x=true ↔ ∃ e∈fibre v, (tail e).eval x=true) ∧
      (inner v).leaves=∑ e∈fibre v, (tail e).leaves := by
    simpa [inner,hv] using (join_list (fibre v) tail (group v hv)).choose_spec
  let star (v : V) := Formula.meet (.var v) (inner v)
  have non : T.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨f,ev,ln⟩ := join_list T star non
  refine ⟨f,?_,?_⟩
  · intro x
    rw [ev]
    constructor
    · rintro ⟨v,hv,ok⟩
      change (x v && (inner v).eval x)=true at ok
      obtain ⟨xv,inside⟩ := Bool.and_eq_true_iff.mp ok
      obtain ⟨e,he,te⟩ := ((spec v hv).1 x).mp inside
      have ownv : owner e=v := (Finset.mem_filter.mp he).2
      refine ⟨e,fun a ha => ?_⟩
      by_cases av : a=owner e
      · simpa [av,ownv] using xv
      · exact (ht e x).mp te a (Finset.mem_erase.mpr ⟨av,ha⟩)
    · rintro ⟨e,alltrue⟩
      have hv : owner e∈T := Finset.mem_image_of_mem _ (mem_univ _)
      refine ⟨owner e,hv,?_⟩
      apply Bool.and_eq_true_iff.mpr
      exact ⟨alltrue _ (own e),((spec _ hv).1 x).mpr ⟨e,by simp [fibre],(ht e x).mpr (fun a ha => alltrue a (Finset.mem_erase.mp ha).2)⟩⟩
  · rw [←f.leaves_eq,ln]
    have starL (v : V) (hv : v∈T) : (star v).leaves=1+∑ e∈fibre v, ((edge e).card-1) := by
      change 1+(inner v).leaves=_
      rw [(spec v hv).2]
      simp_rw [hl,fun e => Finset.card_erase_of_mem (own e)]
    rw [Finset.sum_congr rfl (fun v hv => starL v hv),Finset.sum_add_distrib]
    have maps : (↑(univ : Finset E) : Set E).MapsTo owner T :=
      fun _ _ => Finset.mem_image_of_mem _ (mem_univ _)
    simp only [fibre,Finset.sum_fiberwise_of_maps_to maps]
    simp [T,Nat.add_comm]

theorem exact_hypergraph_size [Nonempty E] (edge : E → Finset V) (H : Sparse edge) (k : ℕ)
    (lower : ∀ T : Finset V, (∀ e, ∃ v∈edge e, v∈T) → k≤T.card)
    (attained : ∃ T : Finset V, (∀ e, ∃ v∈edge e, v∈T) ∧ T.card=k) :
    (∀ f : Formula V, (∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) →
      (∑ e, ((edge e).card-1))+k≤f.gates+1) ∧
    ∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) ∧
      f.gates+1=(∑ e, ((edge e).card-1))+k := by
  classical
  have lb (f : Formula V) (hf : ∀ x, f.eval x=true ↔ ∃ e, ∀ v∈edge e, x v=true) : (∑ e, ((edge e).card-1))+k ≤ f.gates+1 := by
    obtain ⟨T,hit,bound⟩ := hypergraph_lower edge H f hf
    exact (Nat.add_le_add_left (lower T hit) _).trans bound
  refine ⟨lb,?_⟩
  obtain ⟨T,hit,sz⟩ := attained
  choose owner own belongs using hit
  obtain ⟨f,hf,count⟩ := hypergraph_upper edge H owner own
  have sub : univ.image owner ⊆ T := by
    intro v hv
    obtain ⟨e,_,rfl⟩ := mem_image.mp hv
    exact belongs e
  have lim := Finset.card_le_card sub
  exact ⟨f,hf,by have h := lb f hf; omega⟩
end WeightedFormula.Hypergraph
#print axioms WeightedFormula.Hypergraph.hypergraph_orientation
#print axioms WeightedFormula.Hypergraph.exact_hypergraph_size
