import PointwiseFormula

/-! Read-preserving replacement by a disjunction of stars for girth-five graphs. -/
namespace WeightedFormula.Pointwise
open Finset Sym2

/-- A binary OR tree whose leaves are exactly the indicated family of formulas.
The empty disjunction is the constant false. -/
inductive JoinFamily {V I : Type*} [DecidableEq I] (atom : I → Formula V) :
    Finset I → Formula V → Prop where
  | empty : JoinFamily atom ∅ (.const false)
  | single (i : I) : JoinFamily atom {i} (atom i)
  | insert {i : I} {S : Finset I} {f : Formula V} : i ∉ S → S.Nonempty →
      JoinFamily atom S f → JoinFamily atom (insert i S) (.join (atom i) f)

theorem card_occ_var {V : Type*} [DecidableEq V] (u v : V) :
    ((Formula.var u).occSet v).card = if u=v then 1 else 0 := by
  classical
  by_cases h : u=v <;> simp [Formula.occSet, Formula.label, h]
  exact Finset.card_univ.trans Fintype.card_unit

theorem card_occ_const {V : Type*} (b : Bool) (v : V) :
    ((Formula.const b).occSet v).card = 0 := by
  classical
  simp [Formula.occSet, Formula.label]

theorem card_occ_join {V : Type*} (a b : Formula V) (v : V) :
    ((a.join b).occSet v).card = (a.occSet v).card + (b.occSet v).card := by
  classical
  have eq : (a.join b).occSet v = (a.occSet v).disjSum (b.occSet v) := by
    ext x
    rw [Formula.mem_occ]
    cases x with
    | inl l => exact (Formula.mem_occ a v l).symm.trans Finset.inl_mem_disjSum.symm
    | inr l => exact (Formula.mem_occ b v l).symm.trans Finset.inr_mem_disjSum.symm
  exact (congrArg Finset.card eq).trans (Finset.card_disjSum ..)

theorem card_occ_meet {V : Type*} (a b : Formula V) (v : V) :
    ((a.meet b).occSet v).card = (a.occSet v).card + (b.occSet v).card := by
  classical
  have eq : (a.meet b).occSet v = (a.occSet v).disjSum (b.occSet v) := by
    ext x
    rw [Formula.mem_occ]
    cases x with
    | inl l => exact (Formula.mem_occ a v l).symm.trans Finset.inl_mem_disjSum.symm
    | inr l => exact (Formula.mem_occ b v l).symm.trans Finset.inr_mem_disjSum.symm
  exact (congrArg Finset.card eq).trans (Finset.card_disjSum ..)

namespace JoinFamily
theorem exists_for {V I : Type*} [DecidableEq I] (atom : I → Formula V) (S : Finset I) :
    ∃ f, JoinFamily atom S f := by
  induction S using Finset.induction_on with
  | empty => exact ⟨_,.empty⟩
  | @insert i S hi ih =>
    by_cases h : S.Nonempty
    · obtain ⟨f,hf⟩ := ih
      exact ⟨_,.insert hi h hf⟩
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp h
      exact ⟨_,.single i⟩

theorem eval_iff {V I : Type*} [DecidableEq I] {atom : I → Formula V} {S : Finset I}
    {f : Formula V} (h : JoinFamily atom S f) (x : V → Bool) :
    f.eval x=true ↔ ∃ i∈S, (atom i).eval x=true := by
  induction h with
  | empty => simp [Formula.eval]
  | single i => simp
  | insert hi hn hs ih => simp [Formula.eval,ih]

theorem card_occ {V I : Type*} [DecidableEq I] {atom : I → Formula V} {S : Finset I}
    {f : Formula V} (h : JoinFamily atom S f) (v : V) :
    (f.occSet v).card = ∑ i∈S, ((atom i).occSet v).card := by
  induction h with
  | empty => simp [card_occ_const]
  | single i => simp
  | insert hi hn hs ih => simp [card_occ_join,hi,ih]
end JoinFamily

/-- Each center occurs once in its star. Each edge contributes its other endpoint
as a single leaf inside the star. The stars themselves form a disjunction. -/
def IsStarFormula {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (owner other : I → V) (f : Formula V) : Prop :=
  ∃ star : V → Formula V, JoinFamily star (Finset.univ.image owner) f ∧
    ∀ a∈Finset.univ.image owner, ∃ tail,
      JoinFamily (fun e => Formula.var (other e)) (Finset.univ.filter (fun e => owner e=a)) tail ∧
      star a = .meet (.var a) tail

theorem star_formula_spec {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (owner other : I → V) :
    ∃ f : Formula V, IsStarFormula owner other f ∧
      (∀ x, f.eval x=true ↔ ∃ e, x (owner e)=true ∧ x (other e)=true) ∧
      ∀ v, (f.occSet v).card = (Finset.univ.filter (fun e => other e=v)).card +
        if v∈Finset.univ.image owner then 1 else 0 := by
  classical
  let T := Finset.univ.image owner
  let fibre (c : V) := Finset.univ.filter (fun e => owner e=c)
  choose tail ht using (fun c => JoinFamily.exists_for (fun e => Formula.var (other e)) (fibre c))
  let star (c : V) := Formula.meet (.var c) (tail c)
  obtain ⟨f,hf⟩ := JoinFamily.exists_for star T
  refine ⟨f,⟨star,hf,fun a _ => ⟨tail a,ht a,rfl⟩⟩,?_,?_⟩
  · intro x
    rw [hf.eval_iff]
    constructor
    · rintro ⟨c,_,hc⟩
      obtain ⟨xc,he⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨e,mem,xe⟩ := ((ht c).eval_iff x).mp he
      have eq : owner e=c := by simpa [fibre] using mem
      exact ⟨e,eq ▸ xc,xe⟩
    · rintro ⟨e,xc,xe⟩
      refine ⟨owner e,Finset.mem_image_of_mem _ (Finset.mem_univ _),Bool.and_eq_true_iff.mpr ⟨xc,?_⟩⟩
      exact ((ht (owner e)).eval_iff x).mpr ⟨e,by simp [fibre],xe⟩
  · intro v
    have hs (c : V) : ((star c).occSet v).card =
        (if c=v then 1 else 0) + ∑ e∈fibre c, (if other e=v then 1 else 0) := by
      simp [star,card_occ_meet,card_occ_var,(ht c).card_occ]
    rw [hf.card_occ,Finset.sum_congr rfl (fun c _ => hs c),Finset.sum_add_distrib]
    have maps : (↑(Finset.univ : Finset I) : Set I).MapsTo owner T :=
      fun _ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have mass : (∑ c∈T, ∑ e∈fibre c, (if other e=v then 1 else 0)) =
        (Finset.univ.filter (fun e => other e=v)).card := by
      dsimp [fibre]
      rw [Finset.sum_fiberwise_of_maps_to maps]
      exact (Finset.card_filter ..).symm
    rw [mass,Nat.add_comm]
    simp [T]

/-- Any formula for the edge predicate of a graph of girth at least five can
be replaced by an explicitly factored star formula without increasing the
number of occurrences of any input. Includes edgeless graphs. -/
theorem pointwise_star_replacement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (f : Formula V)
    (correct : ∀ x, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) :
    ∃ (owner other : ↥G.edgeFinset → V) (z : Formula V),
      (∀ e, e.val=s(owner e,other e)) ∧ (∀ e, owner e≠other e) ∧
      IsStarFormula owner other z ∧ (∀ x, z.eval x = f.eval x) ∧
      ∀ v, (z.occSet v).card ≤ (f.occSet v).card := by
  classical
  obtain ⟨owner,other,ends,diff,occ⟩ := occurrence_orientation G girth f correct
  obtain ⟨z,hz,ev,cnt⟩ := star_formula_spec owner other
  refine ⟨owner,other,z,ends,diff,hz,?_,fun v => (cnt v).trans_le (occ v)⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [ev,correct]
  constructor
  · rintro ⟨e,ha,hb⟩
    have H := e.property
    rw [ends e,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at H
    exact ⟨owner e,other e,H,ha,hb⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    let e : ↥G.edgeFinset := ⟨s(u,v),by simpa using uv⟩
    have he : s(u,v)=s(owner e,other e) := ends e
    rw [Sym2.eq_iff] at he
    exact ⟨e,by grind⟩

end WeightedFormula.Pointwise

#print axioms WeightedFormula.Pointwise.pointwise_star_replacement
