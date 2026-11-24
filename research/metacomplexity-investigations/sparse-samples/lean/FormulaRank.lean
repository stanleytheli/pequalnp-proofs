import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Push

/-!
# Exact monotone formula size of the edge function at girth at least five

The two players' deterministic path through an AND/OR formula partitions pairs of
positive and negative inputs into leaf rectangles. An edge and the neighborhood
of a different edge meeting it have a unique positive-to-negative witness at
their common vertex. Assigning the diagonal pairs to their terminal vertices
therefore orients the graph. A local rank bound at each vertex counts the
unassigned incident edges and one extra occurrence for every used vertex. The
used vertices cover all edges. Conversely every vertex cover gives a star formula.

The edge-neighborhood test inputs also appear in Stasys Jukna's
*Boolean Function Complexity*, Section 7.2, Theorem 7.2.
-/

namespace WeightedFormula

inductive Formula (V : Type*) where
  | var (v : V)
  | const (b : Bool)
  | meet (a b : Formula V)
  | join (a b : Formula V)

namespace Formula

def eval {V} (x : V → Bool) : Formula V → Bool
  | .var v => x v
  | .const b => b
  | .meet a b => eval x a && eval x b
  | .join a b => eval x a || eval x b

def leaves {V} : Formula V → ℕ
  | .var _ | .const _ => 1
  | .meet a b | .join a b => a.leaves+b.leaves

def gates {V} : Formula V → ℕ
  | .var _ | .const _ => 0
  | .meet a b | .join a b => a.gates+b.gates+1

theorem leaves_eq {V} (f : Formula V) : f.leaves=f.gates+1 := by
  induction f <;> simp_all [leaves,gates] <;> omega

end Formula

namespace Formula

def Leaf {V} : Formula V → Type
  | .var _ | .const _ => Unit
  | .meet a b | .join a b => a.Leaf ⊕ b.Leaf

noncomputable instance leafFintype {V} : (f : Formula V) → Fintype f.Leaf
  | .var _ | .const _ => inferInstanceAs (Fintype Unit)
  | .meet a b | .join a b => @instFintypeSum _ _ (leafFintype a) (leafFintype b)

theorem card_leaf {V} (f : Formula V) : Fintype.card f.Leaf = f.leaves := by
  induction f with
  | var | const => exact Fintype.card_unit
  | meet a b ha hb | join a b ha hb =>
    change Fintype.card (a.Leaf ⊕ b.Leaf) = a.leaves+b.leaves
    simp [ha,hb]

def label {V} : (f : Formula V) → f.Leaf → Option V
  | .var v, _ => some v
  | .const _, _ => none
  | .meet a b, l | .join a b, l => Sum.elim a.label b.label l

def route {V} (x y : V → Bool) : (f : Formula V) → f.Leaf
  | .var _ | .const _ => ()
  | .meet a b => if a.eval y then .inr (b.route x y) else .inl (a.route x y)
  | .join a b => if a.eval x then .inl (a.route x y) else .inr (b.route x y)

theorem route_valid {V} (x y : V → Bool) (f : Formula V)
    (hx : f.eval x = true) (hy : f.eval y = false) :
    ∃ v, f.label (f.route x y) = some v ∧ x v = true ∧ y v = false := by
  induction f with
  | var v => exact ⟨v,rfl,hx,hy⟩
  | const b => simp_all [eval]
  | meet a b ha hb =>
    cases h : a.eval y <;> simp [route,label,h]
    · exact ha (by simpa [eval] using (Bool.and_eq_true_iff.mp hx).1) h
    · exact hb (Bool.and_eq_true_iff.mp hx).2 (by simpa [eval,h] using hy)
  | join a b ha hb =>
    cases h : a.eval x <;> simp [route,label,h]
    · exact hb (by simpa [eval,h] using hx) (Bool.or_eq_false_iff.mp hy).2
    · exact ha h (Bool.or_eq_false_iff.mp hy).1

theorem route_rectangle {V} (f : Formula V) (l : f.Leaf) :
    ∃ (P Q : (V → Bool) → Prop), ∀ x y, f.route x y = l ↔ P x ∧ Q y := by
  induction f with
  | var v | const v =>
    exact ⟨fun _ => True, fun _ => True, fun _ _ => by cases l; simp [route]; rfl⟩
  | meet a b ha hb =>
    cases l with
    | inl l =>
      obtain ⟨P,Q,h⟩ := ha l
      exact ⟨P,fun y => a.eval y=false ∧ Q y, fun x y => by
        cases q : a.eval y <;> simp [route,q]
        exact ⟨fun e => (h x y).mp (Sum.inl.inj e), fun e => congrArg Sum.inl ((h x y).mpr e)⟩⟩
    | inr l =>
      obtain ⟨P,Q,h⟩ := hb l
      exact ⟨P,fun y => a.eval y=true ∧ Q y, fun x y => by
        cases q : a.eval y <;> simp [route,q]
        exact ⟨fun e => (h x y).mp (Sum.inr.inj e), fun e => congrArg Sum.inr ((h x y).mpr e)⟩⟩
  | join a b ha hb =>
    cases l with
    | inl l =>
      obtain ⟨P,Q,h⟩ := ha l
      exact ⟨fun x => a.eval x=true ∧ P x,Q,fun x y => by
        cases q : a.eval x <;> simp [route,q]
        exact ⟨fun e => (h x y).mp (Sum.inl.inj e), fun e => congrArg Sum.inl ((h x y).mpr e)⟩⟩
    | inr l =>
      obtain ⟨P,Q,h⟩ := hb l
      exact ⟨fun x => a.eval x=false ∧ P x,Q,fun x y => by
        cases q : a.eval x <;> simp [route,q]
        exact ⟨fun e => (h x y).mp (Sum.inr.inj e), fun e => congrArg Sum.inr ((h x y).mpr e)⟩⟩

end Formula
end WeightedFormula

namespace WeightedFormula
namespace Formula

noncomputable def rowTest {V} (f : Formula V) (l : f.Leaf) : (V→Bool)→Prop :=
  (f.route_rectangle l).choose

noncomputable def columnTest {V} (f : Formula V) (l : f.Leaf) : (V→Bool)→Prop :=
  (f.route_rectangle l).choose_spec.choose

theorem route_iff_tests {V} (f : Formula V) (l : f.Leaf) (x y : V→Bool) :
    f.route x y=l ↔ f.rowTest l x ∧ f.columnTest l y :=
  (f.route_rectangle l).choose_spec.choose_spec x y

noncomputable def occSet {V} (f : Formula V) (v : V) : Finset f.Leaf := by
  classical
  exact Finset.univ.filter (fun l => f.label l=some v)

abbrev Occ {V} (f : Formula V) (v : V) := ↥(f.occSet v)

@[simp] theorem mem_occ {V} (f : Formula V) (v : V) (l : f.Leaf) :
    l ∈ f.occSet v ↔ f.label l = some v := by classical simp [occSet]

noncomputable def eventMatrix {V R} (f : Formula V) (v : V) (x : R → V → Bool) :
    Matrix R (f.Occ v) ℚ := by
  classical
  exact fun i l => if f.rowTest l.val (x i) then 1 else 0

theorem event_range {V R} [DecidableEq V] (f : Formula V) (v : V) (x : R → V → Bool) (y : V → Bool) :
    (fun i => if f.label (f.route (x i) y)=some v then (1:ℚ) else 0) ∈
      LinearMap.range (f.eventMatrix v x).mulVecLin := by
  classical
  use fun l => if f.columnTest l.val y then 1 else 0
  funext i
  simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct]
  have cell (l : f.Occ v) :
      f.eventMatrix v x i l * (if f.columnTest l.val y then 1 else 0) =
        (if f.route (x i) y = l.val then (1:ℚ) else 0) := by
    rw [f.route_iff_tests]
    by_cases a : f.rowTest l.val (x i) <;> by_cases b : f.columnTest l.val y <;>
      simp [eventMatrix,a,b]
  simp_rw [cell]
  by_cases h : f.label (f.route (x i) y)=some v
  · let l : f.Occ v := ⟨_,(f.mem_occ _ _).mpr h⟩
    rw [Finset.sum_eq_single l]
    · simp [h,l]
    · intro j _ hj
      have ne : f.route (x i) y ≠ j.val := fun e => hj (Subtype.ext e.symm)
      simp [ne]
    · simp
  · have ne (j : f.Occ v) : f.route (x i) y ≠ j.val :=
      fun e => h (e ▸ (f.mem_occ _ _).mp j.property)
    simp [h,ne]

end Formula

theorem rank_from_columns {R L : Type*} [Fintype R] [Fintype L] [DecidableEq R]
    (A : Matrix R L ℚ) (miss : Finset R)
    (unique : ∀ i j, i∉miss → j∉miss → i=j)
    (hbase : (fun _ : R => (1:ℚ)) ∈ LinearMap.range A.mulVecLin)
    (hmiss : ∀ i∈miss, (fun j => if j=i then (0:ℚ) else 1) ∈ LinearMap.range A.mulVecLin) :
    Fintype.card R ≤ Fintype.card L := by
  classical
  let K := LinearMap.range A.mulVecLin
  have hu (i : R) (hi : i∈miss) : Pi.single i (1:ℚ) ∈ K := by
    have h := K.sub_mem hbase (hmiss i hi)
    convert h using 1
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [hji]
  have unit (i : R) : Pi.single i (1:ℚ) ∈ K := by
    by_cases hi : i∈miss
    · exact hu i hi
    have hs : (∑ j∈miss, Pi.single j (1:ℚ)) ∈ K :=
      K.sum_mem fun j hj => hu j hj
    have h := K.sub_mem hbase hs
    convert h using 1
    ext j
    by_cases hj : j∈miss
    · have ne : j≠i := fun e => hi (e ▸ hj)
      simp [Finset.sum_apply,Pi.single_apply,hj,ne]
    · have eq := unique i j hi hj
      subst j
      simp [Finset.sum_apply,Pi.single_apply,hi]
  have top : K = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℚ R).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa using unit i
  have sur : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp top
  simpa using LinearMap.finrank_le_finrank_of_surjective sur

end WeightedFormula

namespace WeightedFormula
open Finset

theorem oriented_bound {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (f : Formula V) (target other : E → V) (hne : ∀ e, target e ≠ other e)
    (pos neg : E → V → Bool) (priv : V → V → Bool)
    (diag : ∀ e, f.label (f.route (pos e) (neg e))=some (target e))
    (offDiag : ∀ v e j, (v=target e ∨ v=other e) → (v=target j ∨ v=other j) →
      e≠j → f.label (f.route (pos e) (neg j))=some v)
    (privateCol : ∀ v e, (v=target e ∨ v=other e) →
      f.label (f.route (pos e) (priv v))=some v) :
    Fintype.card E + (Finset.univ.image target).card ≤ f.leaves := by
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
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => hlocal v)
  rw [Finset.sum_add_distrib] at total
  have sa : ∑ v : V, (away v).card = Fintype.card E := by
    simp only [away,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have sc : (∑ v : V, if v∈cover then 1 else 0) = cover.card := by simp
  have sl : (∑ v : V, (f.occSet v).card) ≤ f.leaves := by
    simp only [Formula.occSet,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm, ← f.card_leaf,← Finset.card_univ,Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro l _
    cases f.label l <;> simp
  simpa [sa,sc,cover] using total.trans sl

end WeightedFormula

namespace WeightedFormula
open Sym2

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

/-- A cover recovered from a formula and its deterministic communication protocol. -/
theorem cover_of_formula_local {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (triangle : ∀ {a b c}, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (square : ∀ {a b c d}, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (f : Formula V)
    (correct : ∀ x, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ T : Finset V, (∀ u v, G.Adj u v → u∈T ∨ v∈T) ∧
      G.edgeFinset.card + T.card ≤ f.leaves := by
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
  use Finset.univ.image target
  constructor
  · intro u v uv
    let e : E := ⟨s(u,v),by simpa using uv⟩
    have hpair : s(u,v) = s(a e,b e) := hrep e
    have he := hin e
    have ht : target e ∈ Finset.univ.image target := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    simp only [inc] at he
    rw [Sym2.eq_iff] at hpair
    grind
  · have bound := oriented_bound f target other diff pos neg priv diag
        (fun v e j he hj nej => off v e j ((hEnds e v).mp he) ((hEnds j v).mp hj) nej)
        (fun v e he => own v e ((hEnds e v).mp he))
    rwa [show Fintype.card E = G.edgeFinset.card from Fintype.card_coe _] at bound

theorem cover_of_formula {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (f : Formula V)
    (correct : ∀ x, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ T : Finset V, (∀ u v, G.Adj u v → u∈T ∨ v∈T) ∧
      G.edgeFinset.card + T.card ≤ f.leaves :=
  cover_of_formula_local G (fun ab bc ca => no_triangle G girth ab bc ca)
    (fun ab bc cd da => no_square G girth ab bc cd da) f correct

theorem graph_formula_gate_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (k : ℕ) (lower : ∀ T : Finset V, (∀ u v, G.Adj u v → u∈T ∨ v∈T) → k≤T.card)
    (f : Formula V) (correct : ∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    G.edgeFinset.card+k ≤ f.gates+1 := by
  obtain ⟨T,hT,h⟩ := cover_of_formula G girth f correct
  rw [← f.leaves_eq]
  exact (Nat.add_le_add_left (lower T hT) _).trans h

end WeightedFormula

namespace WeightedFormula

private theorem or_finite {V I : Type*} (S : Finset I) (g : I→Formula V)
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

/-- The standard construction assigning each edge once to the star of its chosen endpoint. -/
theorem oriented_upper {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V] [Nonempty I]
    (center other : I → V) :
    ∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ i, x (center i)=true ∧ x (other i)=true) ∧
      f.leaves = Fintype.card I + (Finset.univ.image center).card := by
  classical
  let T := (Finset.univ : Finset I).image center
  let fibre (v : V) := Finset.univ.filter (fun e => center e=v)
  have haveStar (v : V) (hv : v∈T) : ∃ f : Formula V,
      (∀ x, f.eval x=true ↔ x v=true ∧ ∃ i∈fibre v, x (other i)=true) ∧
      f.leaves=1+(fibre v).card := by
    obtain ⟨p,hp,hc⟩ := Finset.mem_image.mp hv
    have hnon : (fibre v).Nonempty := ⟨p,by simp [fibre,hc]⟩
    obtain ⟨z,hz,hl⟩ := or_finite (fibre v) (fun i => Formula.var (other i)) hnon
    refine ⟨.meet (.var v) z,fun x => ?_,?_⟩
    · simp [Formula.eval,hz]
    · simp [Formula.leaves,hl]
  let star (v : V) := if hv : v∈T then (haveStar v hv).choose else Formula.const false
  have spec (v : V) (hv : v∈T) := (haveStar v hv).choose_spec
  have hnT : T.Nonempty := Finset.univ_nonempty.image center
  obtain ⟨g,hg,hl⟩ := or_finite T star hnT
  refine ⟨g,fun x => ?_,?_⟩
  · rw [hg]
    constructor
    · rintro ⟨v,hv,h⟩
      simp only [star,dite_eq_left hv] at h
      obtain ⟨xv,e,he,xe⟩ := ((spec v hv).1 x).mp h
      have eq : center e=v := by simpa [fibre] using he
      exact ⟨e,eq ▸ xv,xe⟩
    · rintro ⟨e,hc,ho⟩
      have hv : center e∈T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact ⟨center e,hv,by
        simp only [star,dite_eq_left hv]
        exact ((spec _ hv).1 x).mpr ⟨hc,e,by simp [fibre],ho⟩⟩
  · rw [hl,Finset.sum_congr rfl fun v hv => show (star v).leaves = 1+(fibre v).card by
        simpa [star,hv] using (spec v hv).2, Finset.sum_add_distrib]
    have mass : ∑ v∈T, (fibre v).card = Fintype.card I := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=T) (f:=center)
        (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp [mass,T,Nat.add_comm]

end WeightedFormula

namespace WeightedFormula
open Sym2

theorem formula_of_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (nonempty : G.edgeFinset.Nonempty)
    (T : Finset V) (cover : ∀ u v, G.Adj u v → u∈T ∨ v∈T) :
    ∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      f.leaves ≤ G.edgeFinset.card+T.card := by
  classical
  let E := ↥G.edgeFinset
  let _inst : Nonempty E := by obtain ⟨e,he⟩ := nonempty; exact ⟨⟨e,he⟩⟩
  have rep (e : E) : ∃ a b, e.val=s(a,b) :=
    Sym2.inductionOn e.val (fun a b => ⟨a,b,rfl⟩)
  choose a b hr using rep
  have ab (e : E) : G.Adj (a e) (b e) := by
    have H := e.property
    rwa [hr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at H
  let c (e : E) := if a e∈T then a e else b e
  let o (e : E) := if a e∈T then b e else a e
  have cs (e) : c e∈T := by
    have h := cover _ _ (ab e)
    by_cases z : a e∈T <;> simp_all [c]
  obtain ⟨f,hf,hl⟩ := oriented_upper c o
  use f
  constructor
  · intro x
    rw [hf]
    constructor
    · rintro ⟨e,h1,h2⟩
      use a e,b e,ab e
      by_cases z : a e∈T <;> simp_all [c,o]
    · rintro ⟨u,v,uv,hu,hv⟩
      let e : E := ⟨s(u,v),by simpa using uv⟩
      have hpair : s(u,v) = s(a e,b e) := hr e
      rw [Sym2.eq_iff] at hpair
      refine ⟨e,?_⟩
      by_cases z : a e∈T <;> simp [c,o,z] <;> grind
  · rw [hl]
    have sub : Finset.univ.image c ⊆ T := by
      intro v hv
      obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hv
      exact cs e
    rw [show Fintype.card E = G.edgeFinset.card from Fintype.card_coe _]
    exact Nat.add_le_add_left (Finset.card_le_card sub) _

/-- The minimum cover's star formula attains the proved bound. -/
theorem exact_formula_size {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (nonempty : G.edgeFinset.Nonempty)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (T : Finset V) (cov : ∀ u v, G.Adj u v → u∈T ∨ v∈T)
    (minimum : ∀ U : Finset V, (∀ u v, G.Adj u v → u∈U ∨ v∈U) → T.card≤U.card) :
    ∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      f.leaves = G.edgeFinset.card+T.card ∧ f.gates+1 = G.edgeFinset.card+T.card := by
  obtain ⟨f,hf,upper⟩ := formula_of_cover G nonempty T cov
  have lower := graph_formula_gate_bound G girth T.card minimum f hf
  rw [← f.leaves_eq] at lower
  have eq := le_antisymm upper lower
  exact ⟨f,hf,eq,f.leaves_eq.symm.trans eq⟩

end WeightedFormula

#print axioms WeightedFormula.graph_formula_gate_bound
#print axioms WeightedFormula.formula_of_cover

#print axioms WeightedFormula.exact_formula_size
