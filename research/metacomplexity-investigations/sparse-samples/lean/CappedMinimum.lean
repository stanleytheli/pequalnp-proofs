import ReadBudgets

/-! Minimum gate count under nonuniform named-variable read caps. -/
namespace WeightedFormula.CappedMinimum
open Finset Sym2 WeightedFormula.Pointwise WeightedFormula.Budgets

private theorem sum_reads_le {V : Type*} [Fintype V] (f : Formula V) :
    (∑ v : V, (f.occSet v).card) ≤ f.leaves := by
  classical
  simp only [Formula.occSet,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm, ← f.card_leaf,← Finset.card_univ,Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro l _
  cases f.label l <;> simp

private theorem join_leaves {V E : Type*} [DecidableEq E] {atom : E → Formula V}
    {S : Finset E} {f : Formula V} (h : JoinFamily atom S f) (hs : S.Nonempty) :
    f.leaves = ∑ i∈S, (atom i).leaves := by
  induction h with
  | empty => simp at hs
  | single i => simp
  | insert hi hn _ ih => simp [Formula.leaves,ih hn,hi]

private theorem star_leaves {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E] [Nonempty E]
    {a b : E → V} {f : Formula V} (hf : IsStarFormula a b f) :
    f.leaves = Fintype.card E + (univ.image a).card := by
  classical
  obtain ⟨star,tree,arms⟩ := hf
  rw [join_leaves tree (Finset.univ_nonempty.image a)]
  let T := univ.image a
  let fibre (v : V) := univ.filter (fun e => a e=v)
  have one (v) (hv : v ∈ T) : (star v).leaves=1+(fibre v).card := by
    obtain ⟨tail,ht,eq⟩ := arms v hv
    have ne : (fibre v).Nonempty := by
      obtain ⟨e,_,he⟩ := Finset.mem_image.mp hv
      exact ⟨e,by simp [fibre,he]⟩
    simp [eq,Formula.leaves,join_leaves ht ne,fibre]
  rw [Finset.sum_congr rfl one,Finset.sum_add_distrib]
  have cover : (↑(univ : Finset E) : Set E).MapsTo a T :=
    fun _ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have mass : ∑ v∈T, (fibre v).card = Fintype.card E := by
    simp only [fibre,Finset.card_eq_sum_ones]
    rw [Finset.sum_fiberwise_of_maps_to cover]
    simp
  simpa [T,Nat.add_comm] using congrArg (fun k => T.card+k) mass

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
private theorem endpoints {a b : Edges G → V} (ends : ∀ e, e.val=s(a e,b e)) :
    ∀ e, G.Adj (a e) (b e) := by
  intro e
  have h := e.property
  rwa [ends,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at h

private theorem split_degree {a b : Edges G → V} (ends : ∀ e, e.val=s(a e,b e)) (v : V) :
    (incident G v).card = (univ.filter (fun e => a e=v)).card+
        (univ.filter (fun e => b e=v)).card := by
  classical
  have eq : incident G v = (univ.filter (fun e => a e=v)) ∪ (univ.filter (fun e => b e=v)) := by
    ext e
    simp [incident,ends e,eq_comm]
  rw [eq,Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (by
    intro e x y
    simp only [mem_filter,mem_univ,true_and] at x y
    exact (endpoints G ends e).ne (x.trans y.symm))

private theorem cap_iff {a b : Edges G → V} (ends : ∀ e, e.val=s(a e,b e)) (r : V → ℕ) (v : V) :
    (univ.filter (fun e => b e=v)).card + (if v∈univ.image a then 1 else 0) ≤ r v ↔
      demand (incident G v).card (r v) ≤ (univ.filter (fun e => a e=v)).card := by
  classical
  have hd := split_degree G ends v
  have nz : v∈univ.image a ↔ 0<(univ.filter (fun e => a e=v)).card := by
    rw [Finset.card_pos]
    simp [Finset.Nonempty]
  simp only [nz]
  unfold demand
  split_ifs <;> omega

def Valid (r : V → ℕ) (f : Formula V) : Prop :=
  (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
  ∀ v, (f.occSet v).card ≤ r v

def Admissible (r : V → ℕ) (I : Finset V) : Prop :=
  (∀ v∈I, (incident G v).card ≤ r v) ∧
  (∀ u∈I, ∀ v∈I, ¬G.Adj u v)

private theorem unowned {a b : Edges G → V} (ends : ∀ e, e.val=s(a e,b e)) (r : V → ℕ)
    (paid : ∀ v, demand (incident G v).card (r v) ≤ (univ.filter (fun e => a e=v)).card) :
    Admissible G r (univ \ univ.image a) := by
  classical
  constructor
  · intro v hv
    have miss := (Finset.mem_sdiff.mp hv).2
    have zero : univ.filter (fun e => a e=v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have eq := (Finset.mem_filter.mp he).2
      exact miss (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,eq⟩)
    have hd := paid v
    rw [zero,Finset.card_empty] at hd
    unfold demand at hd
    split_ifs at hd <;> omega
  · intro u hu v hv adj
    let e : Edges G := ⟨s(u,v),by simpa using adj⟩
    have he : s(u,v)=s(a e,b e) := ends e
    rw [Sym2.eq_iff] at he
    have inf := Finset.mem_image_of_mem a (Finset.mem_univ e)
    rcases he with h|h
    · exact (Finset.mem_sdiff.mp hu).2 (h.1 ▸ inf)
    · exact (Finset.mem_sdiff.mp hv).2 (h.2 ▸ inf)

private theorem leaves_lower {a b : Edges G → V} (f : Formula V)
    (counts : ∀ v, (univ.filter (fun e => b e=v)).card+
      (if v∈univ.image a then 1 else 0) ≤ (f.occSet v).card) :
    G.edgeFinset.card+(univ.image a).card ≤ f.leaves := by
  classical
  have sum := Finset.sum_le_sum (s:=univ) (fun v _ => counts v)
  rw [Finset.sum_add_distrib] at sum
  have mass : ∑ v : V, (univ.filter (fun e => b e=v)).card = G.edgeFinset.card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have heads : (∑ v : V, if v ∈ univ.image a then 1 else 0) = (univ.image a).card := by
    rw [←Finset.card_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [mass,heads] at sum
  exact sum.trans (sum_reads_le f)

/-- An independent subset of the vertices whose read allowance reaches degree
can be avoided by every head without decreasing any positive demand. -/
private theorem avoid (I : Finset V) (r : V → ℕ) (pick : Admissible G r I)
    {a b : Edges G → V} (ends : ∀ e, e.val=s(a e,b e))
    (paid : ∀ v, demand (incident G v).card (r v) ≤ (univ.filter (fun e => a e=v)).card) :
    ∃ c d : Edges G → V, (∀ e, e.val=s(c e,d e)) ∧
      (∀ v, demand (incident G v).card (r v) ≤ (univ.filter (fun e => c e=v)).card) ∧
      I ⊆ univ \ univ.image c := by
  classical
  let c (e : Edges G) := if a e∈I then b e else a e
  let d (e : Edges G) := if a e∈I then a e else b e
  refine ⟨c,d,?_,?_,?_⟩
  · intro e
    by_cases h : a e∈I
    · simpa [c,d,h,Sym2.eq_swap] using ends e
    · simpa [c,d,h] using ends e
  · intro v
    by_cases hv : v∈I
    · simp [demand,not_lt_of_ge (pick.1 v hv)]
    · apply (paid v).trans
      apply Finset.card_le_card
      intro e he
      have eq := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [c,eq,hv]⟩
  · intro v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    rintro h
    obtain ⟨e,_,ee⟩ := Finset.mem_image.mp h
    by_cases ha : a e∈I
    · have he : b e=v := by simpa [c,ha] using ee
      exact pick.2 _ ha _ (he ▸ hv) (endpoints G ends e)
    · have he : a e=v := by simpa [c,ha] using ee
      exact ha (he ▸ hv)

/-- Full-function optimal size for a feasible read-budget vector, expressed
without subtraction. A maximum-cardinality admissible set is given as I. -/
theorem exact_capped_gates (r : V → ℕ) (I : Finset V) (pick : Admissible G r I)
    (largest : ∀ J : Finset V, Admissible G r J → J.card ≤ I.card)
    (nonempty : G.edgeFinset.Nonempty)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (feasible : ∃ f : Formula V, Valid G r f) :
    (∀ f : Formula V, Valid G r f →
       G.edgeFinset.card+Fintype.card V ≤ f.gates+1+I.card) ∧
    ∃ f : Formula V, Valid G r f ∧
       f.gates+1+I.card=G.edgeFinset.card+Fintype.card V := by
  classical
  let _ : Nonempty (Edges G) := ⟨⟨nonempty.choose,nonempty.choose_spec⟩⟩
  have ccard (a : Edges G → V) :
      (univ \ univ.image a).card+(univ.image a).card = Fintype.card V := by
    exact (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)).trans (Finset.card_univ)
  constructor
  · intro f ok
    obtain ⟨a,b,ends,_,counts⟩ := occurrence_orientation G girth f ok.1
    have paid (v) := (cap_iff G ends r v).mp ((counts v).trans (ok.2 v))
    have missing := largest _ (unowned G ends r paid)
    have sum := leaves_lower G f counts
    have cc := ccard a
    rw [f.leaves_eq] at sum
    omega
  · obtain ⟨f,ok⟩ := feasible
    obtain ⟨a,b,ends,_,counts⟩ := occurrence_orientation G girth f ok.1
    have paid (v) := (cap_iff G ends r v).mp ((counts v).trans (ok.2 v))
    obtain ⟨c,d,ec,pc,sub⟩ := avoid G I r pick ends paid
    have eq : (univ \ univ.image c).card=I.card :=
      Nat.le_antisymm (largest _ (unowned G ec r pc)) (Finset.card_le_card sub)
    obtain ⟨z,star,sem,occ⟩ := star_formula_spec c d
    refine ⟨z,⟨?_,?_⟩,?_⟩
    · intro x
      rw [sem]
      constructor
      · rintro ⟨e,hc,hd⟩
        exact ⟨c e,d e,endpoints G ec e,hc,hd⟩
      · rintro ⟨u,v,uv,hu,hv⟩
        let e : Edges G := ⟨s(u,v),by simpa using uv⟩
        have he : s(u,v)=s(c e,d e) := ec e
        rw [Sym2.eq_iff] at he
        exact ⟨e,by grind⟩
    · intro v
      rw [occ]
      exact (cap_iff G ec r v).mpr (pc v)
    · have h := star_leaves star
      rw [z.leaves_eq,Fintype.card_coe] at h
      have cc := ccard c
      omega

end WeightedFormula.CappedMinimum

#print axioms WeightedFormula.CappedMinimum.exact_capped_gates
