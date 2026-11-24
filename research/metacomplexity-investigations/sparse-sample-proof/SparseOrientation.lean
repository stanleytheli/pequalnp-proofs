import CappedMinimum

/-! Pointwise replacement from two sparse examples per edge at minimum degree two. -/
namespace WeightedFormula.Sparse
open Finset Sym2 WeightedFormula.Budgets WeightedFormula.Pointwise

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

private theorem off_one {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Matrix I J ℚ) (two : 2 ≤ Fintype.card I)
    (h : ∀ i : I, (fun j : I => if j=i then (0:ℚ) else 1) ∈ LinearMap.range A.mulVecLin) :
    (fun _ : I => (1:ℚ)) ∈ LinearMap.range A.mulVecLin := by
  classical
  have total := Submodule.sum_mem (LinearMap.range A.mulVecLin) (fun i (_ : i∈(univ : Finset I)) => h i)
  have nz : (Fintype.card I:ℚ)-1≠0 := by exact_mod_cast (show (Fintype.card I:ℤ)-1≠0 by omega)
  convert (LinearMap.range A.mulVecLin).smul_mem ((Fintype.card I:ℚ)-1)⁻¹ total using 1
  ext j
  have eq (i : I) : (if j=i then (0:ℚ) else 1) = 1-(if j=i then 1 else 0) := by
    split <;> simp
  simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,eq,Finset.sum_sub_distrib]
  simp [nz]

private theorem sparse_counts {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (f : Formula V) (a b : E → V) (ne : ∀ e, a e ≠ b e)
    (pos neg : E → V → Bool)
    (diag : ∀ e, f.label (f.route (pos e) (neg e))=some (a e))
    (off : ∀ v e j, (v=a e ∨ v=b e) → (v=a j ∨ v=b j) → e≠j →
      f.label (f.route (pos e) (neg j))=some v)
    (single : ∀ v, v∉univ.image a → (univ.filter (fun e => b e=v)).card=1 →
      1 ≤ (f.occSet v).card)
    (v : V) : (univ.filter (fun e => b e=v)).card+
        (if v∈univ.image a then 1 else 0) ≤ (f.occSet v).card := by
  classical
  let away := univ.filter (fun e => b e=v)
  have away_mem (e : E) : e ∈ away ↔ b e=v := by simp [away]
  let prove (S : Finset E) (inc : ∀ e∈S, v=a e ∨ v=b e)
      (unique : ∀ e∈S, ∀ j∈S, a e=v → a j=v → e=j)
      (base : (∃ i∈S, a i=v) ∨ 2≤S.card) :
      S.card ≤ (f.occSet v).card := by
    let missing := univ.filter (fun e : S => a e.val≠v)
    let xx := fun e : S => pos e.val
    let A := f.eventMatrix v xx
    have col (i : S) : (fun j : S => if j=i then (if a i.val=v then (1:ℚ) else 0) else 1)
        ∈ LinearMap.range A.mulVecLin := by
      convert f.event_range v xx (neg i.val) using 1
      ext j
      by_cases h : j=i
      · subst j
        simp [xx,diag]
      · have d : j.val≠i.val := fun eq => h (Subtype.ext eq)
        simp [xx,h,off v j.val i.val (inc _ j.property) (inc _ i.property) d]
    have unit : (fun _ : S => (1:ℚ)) ∈ LinearMap.range A.mulVecLin := by
      by_cases hit : ∃ i : S, a i.val=v
      · obtain ⟨i,hi⟩ := hit
        simpa [hi] using col i
      · have two : 2≤Fintype.card S := by
          rcases base with ⟨i,hi,eq⟩|bound
          · exact (hit ⟨⟨i,hi⟩,eq⟩).elim
          · simpa using bound
        apply off_one A two
        intro i
        simpa [show a i.val ≠ v from fun eq => hit ⟨i,eq⟩] using col i
    have hu : ∀ i j : S, i∉missing → j∉missing → i=j := by
      intro i j hi hj
      exact Subtype.ext (unique _ i.property _ j.property (by simpa [missing] using hi)
        (by simpa [missing] using hj))
    have hm (i : S) (hi : i∈missing) :
        (fun j : S => if j=i then (0:ℚ) else 1) ∈ LinearMap.range A.mulVecLin := by
      simpa [show a i.val≠v by simpa [missing] using hi] using col i
    simpa using rank_from_columns A missing hu unit hm
  by_cases hv : v∈univ.image a
  · obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hv
    have skip : p∉away := fun h => ne p (hp.trans ((away_mem _).mp h).symm)
    have only (x) (hx : x∈insert p away) (eq : a x=v) : x=p := by
      rcases Finset.mem_insert.mp hx with rfl|hx
      · rfl
      · exact (ne x (eq.trans ((away_mem _).mp hx).symm)).elim
    have h := prove (insert p away) (by
      intro e he
      rcases Finset.mem_insert.mp he with rfl|he
      · exact Or.inl hp.symm
      · exact Or.inr ((away_mem _).mp he).symm) (by
      intro x hx y hy xx yy
      exact (only x hx xx).trans (only y hy yy).symm)
      (Or.inl ⟨p,Finset.mem_insert_self _ _,hp⟩)
    simpa [hv,skip,away] using h
  · by_cases two : 2 ≤ away.card
    · have h := prove away (fun e he => Or.inr ((away_mem _).mp he).symm)
          (fun e _ _ _ eq _ => (hv (eq ▸ Finset.mem_image_of_mem a (Finset.mem_univ e))).elim)
          (Or.inr two)
      simpa [hv,away] using h
    · change away.card+(if v∈univ.image a then 1 else 0) ≤ _
      rw [ite_eq_right hv,Nat.add_zero]
      by_cases zero : away.card=0
      · simp [zero]
      · have eq : away.card=1 := by omega
        simpa [eq] using single v hv eq


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Fits (f : Formula V) : Prop := ∀ a b, G.Adj a b →
    f.eval (fun v => decide (v=a ∨ v=b))=true ∧
    f.eval (fun v => decide ((G.Adj a v ∧ v≠b) ∨ (G.Adj b v ∧ v≠a)))=false

def FitsLeaves (f : Formula V) : Prop := ∀ v a, G.Adj v a → (incident G v).card=1 →
    f.eval (fun w => decide (w=a))=false

theorem sampled_orientation (f : Formula V) (fits : Fits G f)
    (leaf : FitsLeaves G f) :
    ∃ owner other : Edges G → V,
      (∀ e, e.val=s(owner e,other e)) ∧ (∀ e, owner e≠other e) ∧
      ∀ v, (univ.filter (fun e => other e=v)).card+
        (if v∈univ.image owner then 1 else 0) ≤ (f.occSet v).card := by
  classical
  let E := ↥G.edgeFinset
  have rep (e : E) : ∃ a b, e.val=s(a,b) :=
    Sym2.inductionOn e.val (fun a b => ⟨a,b,rfl⟩)
  choose a b hrep using rep
  have ab (e : E) : G.Adj (a e) (b e) := by
    have H := e.property
    rwa [hrep,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at H
  let inc (e : E) (v : V) := v=a e ∨ v=b e
  let pos (e : E) (v : V) : Bool := decide (v=a e ∨ v=b e)
  let neg (e : E) (v : V) : Bool :=
    decide ((G.Adj (a e) v ∧ v≠b e) ∨ (G.Adj (b e) v ∧ v≠a e))

  have hp (e : E) : f.eval (pos e)=true := (fits _ _ (ab e)).1
  have hn (e : E) : f.eval (neg e)=false := (fits _ _ (ab e)).2
  have hits (e : E) := f.route_valid (pos e) (neg e) (hp e) (hn e)
  choose target diag hpos hneg using hits
  have hin (e) : inc e (target e) := of_decide_eq_true (hpos e)
  let other (e : E) := if target e=a e then b e else a e
  have diff (e : E) : target e≠other e := by
    have he := hin e
    have ne := (ab e).ne
    simp only [inc] at he
    dsimp [other]
    split <;> grind
  have hEnds (e : E) (v : V) : v=target e ∨ v=other e ↔ inc e v := by
    have he := hin e
    simp only [inc] at he ⊢
    dsimp [other]
    split <;> grind
  have adj_of_ends (e : E) (u v : V) (hu : inc e u) (hv : inc e v) (ne : u≠v) :
      G.Adj u v := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> grind [ab e,(ab e).symm]
  have same (e j : E) (u v : V) (hu : inc e u) (hv : inc e v)
      (ju : inc j u) (jv : inc j v) (ne : u≠v) : e=j := by
    apply Subtype.ext
    rw [hrep,hrep,Sym2.eq_iff]
    simp only [inc] at *
    grind
  have off (v : V) (e j : E) (ev : inc e v) (jv : inc j v) (ej : e≠j) :
      f.label (f.route (pos e) (neg j))=some v := by
    obtain ⟨w,hw,pw,nw⟩ := f.route_valid _ _ (hp e) (hn j)
    have ew : inc e w := of_decide_eq_true pw
    suffices w=v by simpa [this] using hw
    by_contra wv
    have edge := adj_of_ends e _ _ ev ew (Ne.symm wv)
    have jw : ¬inc j w := fun h => ej (same e j v w ev ew jv h (Ne.symm wv))
    simp only [neg,decide_eq_false_iff_not] at nw
    rcases jv with h | h
    · exact nw (Or.inl ⟨h ▸ edge,fun q => jw (Or.inr q)⟩)
    · exact nw (Or.inr ⟨h ▸ edge,fun q => jw (Or.inl q)⟩)

  have ends (e : E) : e.val=s(target e,other e) := by
    rw [hrep,Sym2.eq_iff]
    have ins := hin e
    dsimp [inc] at ins
    by_cases h : target e=a e <;> simp [other,h]
    grind
  refine ⟨target,other,ends,diff,sparse_counts f target other diff pos neg diag ?_ ?_⟩
  · exact fun v e j he hj nej => off v e j ((hEnds e v).mp he) ((hEnds j v).mp hj) nej
  · intro v miss one
    have eq : incident G v = univ.filter (fun e => other e=v) := by
      ext e
      have avoid : target e≠v := fun h => miss (h ▸ Finset.mem_image_of_mem target (Finset.mem_univ e))
      simp [incident,ends e,Ne.symm avoid,eq_comm]
    have hdegree : (incident G v).card=1 := by simpa [eq] using one
    have posdeg : 0<(incident G v).card := by omega
    obtain ⟨e,he⟩ := Finset.card_pos.mp posdeg
    have vin : v∈e.val := (Finset.mem_filter.mp he).2
    let w := Sym2.Mem.other vin
    have rep : e.val=s(v,w) := (Sym2.other_spec vin).symm
    have vw := e.property
    rw [rep,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at vw
    let x (j : V) := decide (j=v ∨ j=w)
    let y (j : V) := decide (j=w)
    have goodx : f.eval x=true := (fits v w vw).1
    have goody : f.eval y=false := leaf _ _ vw hdegree
    obtain ⟨z,label,hx,hy⟩ := f.route_valid x y goodx goody
    have hh : z=v := by
      simp only [x,decide_eq_true_eq] at hx
      simp only [y,decide_eq_false_iff_not] at hy
      exact hx.resolve_right hy
    exact Finset.card_pos.mpr ⟨f.route x y,(Formula.mem_occ f v _).mpr (hh ▸ label)⟩

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


/-- The unweighted paired examples and the leaf singletons suffice for
pointwise and gate-count replacement by an exact full-cube star formula. -/
theorem sampled_full (f : Formula V) (hp : Fits G f) (hs : FitsLeaves G f)
    (nonempty : G.edgeFinset.Nonempty) :
    ∃ z : Formula V, (∀ x, z.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      (∀ v, (z.occSet v).card≤(f.occSet v).card) ∧ z.gates≤f.gates := by
  classical
  let _ : Nonempty (Edges G) := ⟨⟨nonempty.choose,nonempty.choose_spec⟩⟩
  obtain ⟨a,b,ends,_,counts⟩ := sampled_orientation G f hp hs
  obtain ⟨z,star,sem,occ⟩ := star_formula_spec a b
  refine ⟨z,?_,fun v => (occ v).le.trans (counts v),?_⟩
  · intro x
    rw [sem]
    constructor
    · rintro ⟨e,he,ke⟩
      have adj := e.property
      rw [ends,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at adj
      exact ⟨a e,b e,adj,he,ke⟩
    · rintro ⟨v,w,adj,hv,hw⟩
      let e : Edges G := ⟨s(v,w),by simpa using adj⟩
      have he : s(v,w)=s(a e,b e) := ends e
      rw [Sym2.eq_iff] at he
      exact ⟨e,by grind⟩
  · have lb := leaves_lower G f counts
    have eq := star_leaves star
    rw [f.leaves_eq] at lb
    rw [z.leaves_eq,Fintype.card_coe] at eq
    omega

/-- A variable omitted by the classifier and retained at a single incident
edge forces both errors on every other incident edge. -/
theorem double_error {W : Type*} [DecidableEq W] (f : Finset W → Prop) (mono : Monotone f)
    (v a w : W) (Ie Ij : Finset W) (absent : ∀ X, f (insert v X) ↔ f X)
    (pe : f {v,a}) (ne : ¬ f Ie) (wa : w∈Ie) (aj : a∈Ij) :
    ¬f {v,w} ∧ f Ij := by
  have p : f {a} := (absent _).mp pe
  exact ⟨fun h => ne (mono (Finset.singleton_subset_iff.mpr wa) ((absent _).mp h)),
         mono (Finset.singleton_subset_iff.mpr aj) p⟩

end WeightedFormula.Sparse
#print axioms WeightedFormula.Sparse.sampled_orientation
#print axioms WeightedFormula.Sparse.sampled_full
#print axioms WeightedFormula.Sparse.double_error
