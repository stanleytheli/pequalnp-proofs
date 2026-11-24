import FormulaRank

/-! The vertexwise orientation estimate underlying the sharp formula theorem. -/
namespace WeightedFormula.Pointwise
open Finset Sym2

private theorem oriented_occurrences {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (f : Formula V) (target other : E → V) (hne : ∀ e, target e ≠ other e)
    (pos neg : E → V → Bool) (priv : V → V → Bool)
    (diag : ∀ e, f.label (f.route (pos e) (neg e))=some (target e))
    (offDiag : ∀ v e j, (v=target e ∨ v=other e) → (v=target j ∨ v=other j) →
      e≠j → f.label (f.route (pos e) (neg j))=some v)
    (privateCol : ∀ v e, (v=target e ∨ v=other e) →
      f.label (f.route (pos e) (priv v))=some v) (v : V) :
    (Finset.univ.filter (fun e => other e=v)).card +
      (if v∈Finset.univ.image target then 1 else 0) ≤ (f.occSet v).card := by
  classical
  let away (v : V) := Finset.univ.filter (fun e => other e=v)
  let cover := (Finset.univ : Finset E).image target
  have hlocal (v : V) : (away v).card + (if v∈cover then 1 else 0) ≤ (f.occSet v).card := by
    have away_iff (e : E) : e ∈ away v ↔ other e = v := by simp [away]
    have gen (S : Finset E) (hS : ∀ e∈S, v=target e ∨ v=other e)
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
        exact hne p (hp.trans ((away_iff p).mp h).symm)
      have bound := gen (insert p (away v)) (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he
        · exact Or.inl hp.symm
        · exact Or.inr ((away_iff e).mp he).symm) (by
        intro e he j hj heq hjq
        have only (y) (hy : y ∈ insert p (away v)) (hyq : target y=v) : y=p := by
          rcases Finset.mem_insert.mp hy with hy | hy
          · exact hy
          · exact False.elim (hne y (hyq.trans ((away_iff y).mp hy).symm))
        exact (only e he heq).trans (only j hj hjq).symm)
      simpa [hv,px] using bound
    · have bound := gen (away v) (fun e he => Or.inr ((away_iff e).mp he).symm)
          (fun e he _ _ heq _ => False.elim (hne e (heq.trans ((away_iff e).mp he).symm)))
      simpa [hv] using bound
  exact hlocal v

theorem occurrence_orientation_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangle : ∀ {a b c}, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (square : ∀ {a b c d}, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (f : Formula V)
    (correct : ∀ x, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ owner other : ↥G.edgeFinset → V,
      (∀ e, e.val=s(owner e,other e)) ∧ (∀ e, owner e≠other e) ∧
      ∀ v, (Finset.univ.filter (fun e => other e=v)).card +
        (if v∈Finset.univ.image owner then 1 else 0) ≤ (f.occSet v).card := by
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
  let priv (v w : V) : Bool := decide (G.Adj v w)
  have hp (e : E) : f.eval (pos e)=true :=
    (correct _).mpr ⟨a e,b e,ab e,by simp [pos],by simp [pos]⟩
  have hn (e : E) : f.eval (neg e)=false := by
    cases h : f.eval (neg e) with
    | false => rfl
    | true =>
      obtain ⟨u,v,uv,hu,hv⟩ := (correct _).mp h
      simp only [neg,decide_eq_true_eq] at hu hv
      exfalso
      rcases hu with ⟨au,ub⟩ | ⟨bu,ua⟩ <;> rcases hv with ⟨av,vb⟩ | ⟨bv,va⟩
      · exact triangle au uv av.symm
      · rcases square au uv bv.symm (ab e).symm with eq | eq
        · exact va eq.symm
        · exact ub eq
      · rcases square bu uv av.symm (ab e) with eq | eq
        · exact vb eq.symm
        · exact ua eq
      · exact triangle bu uv bv.symm
  have hpriv (v : V) : f.eval (priv v)=false := by
    cases h : f.eval (priv v) with
    | false => rfl
    | true =>
      obtain ⟨u,w,uw,hu,hw⟩ := (correct _).mp h
      exact (triangle (of_decide_eq_true hu) uw
        (SimpleGraph.Adj.symm (of_decide_eq_true hw))).elim
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
  have own (v : V) (e : E) (ev : inc e v) :
      f.label (f.route (pos e) (priv v))=some v := by
    obtain ⟨w,hw,pw,nw⟩ := f.route_valid _ _ (hp e) (hpriv v)
    have ew : inc e w := of_decide_eq_true pw
    suffices w=v by simpa [this] using hw
    by_contra wv
    exact (of_decide_eq_false nw) (adj_of_ends e _ _ ev ew (Ne.symm wv))
  refine ⟨target,other,?_,diff,?_⟩
  · intro e
    rw [hrep,Sym2.eq_iff]
    have ins := hin e
    dsimp [inc] at ins
    by_cases h : target e=a e <;> simp [other,h]
    grind
  · exact oriented_occurrences f target other diff pos neg priv diag
      (fun v e j he hj nej => off v e j ((hEnds e v).mp he) ((hEnds j v).mp hj) nej)
      (fun v e he => own v e ((hEnds e v).mp he))

private theorem no_triangle {V : Type*} (G : SimpleGraph V)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  let p : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
  have cyc : p.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).mpr
    refine ⟨?_,by simp [p]⟩
    simp [p,SimpleGraph.Walk.isPath_def]
    grind [ab.ne,bc.ne,ca.ne]
  have h := girth a p cyc
  simp [p] at h

private theorem no_square {V : Type*} (G : SimpleGraph V)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    {a b c d : V} (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (da : G.Adj d a) :
    a=c ∨ b=d := by
  by_contra bad
  push Not at bad
  let p : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
  have cyc : p.IsCycle := by
    apply (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).mpr
    refine ⟨?_,by simp [p]⟩
    simp [p,SimpleGraph.Walk.isPath_def]
    grind [ab.ne,bc.ne,cd.ne,da.ne]
  have h := girth a p cyc
  simp [p] at h

theorem occurrence_orientation {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (f : Formula V)
    (correct : ∀ x, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ owner other : ↥G.edgeFinset → V,
      (∀ e, e.val=s(owner e,other e)) ∧ (∀ e, owner e≠other e) ∧
      ∀ v, (Finset.univ.filter (fun e => other e=v)).card +
        (if v∈Finset.univ.image owner then 1 else 0) ≤ (f.occSet v).card :=
  occurrence_orientation_local G (fun ab bc ca => no_triangle G girth ab bc ca)
    (fun ab bc cd da => no_square G girth ab bc cd da) f correct

end WeightedFormula.Pointwise

#print axioms WeightedFormula.Pointwise.occurrence_orientation
