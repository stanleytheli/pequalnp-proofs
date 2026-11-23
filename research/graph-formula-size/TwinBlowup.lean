import ReadOptimal

/-! Fiber substitution and read-preserving biclique formulas on independent-twin blowups. -/
namespace WeightedFormula
namespace Formula

/-- Replace each variable leaf by a fresh copy of its assigned formula. -/
def subst {V W : Type*} (σ : V → Formula W) : Formula V → Formula W
  | .var v => σ v
  | .const b => .const b
  | .meet a b => .meet (subst σ a) (subst σ b)
  | .join a b => .join (subst σ a) (subst σ b)

theorem eval_subst {V W : Type*} (σ : V → Formula W) (f : Formula V) (x : W → Bool) :
    (f.subst σ).eval x = f.eval (fun v => (σ v).eval x) := by
  induction f <;> simp_all [subst,eval]

/-- The occurrence counts of substitutions compose by matrix multiplication. -/
theorem card_occ_subst {V W : Type*} [Fintype V] [DecidableEq V]
    (σ : V → Formula W) (f : Formula V) (w : W) :
    ((f.subst σ).occSet w).card = ∑ v : V, (f.occSet v).card * ((σ v).occSet w).card := by
  classical
  induction f with
  | var v => simp [subst,Pointwise.card_occ_var]
  | const b => simp [subst,Pointwise.card_occ_const]
  | meet a b ha hb =>
    simp [subst,Pointwise.card_occ_meet,ha,hb,Nat.add_mul,Finset.sum_add_distrib]
  | join a b ha hb =>
    simp [subst,Pointwise.card_occ_join,ha,hb,Nat.add_mul,Finset.sum_add_distrib]

end Formula

namespace Pointwise
open Finset Sym2

/-- The syntactic biclique formula produced by substitution. The left side of each
biclique is a full class. The right side is the disjunction of the classes of the
other endpoints of the edges owned by its center. -/
def IsBlownStarFormula {V W I : Type*} [Fintype W] [Fintype I] [DecidableEq V] [DecidableEq I]
    [DecidableEq W] (π : W → V) (owner other : I → V) (g : Formula W) : Prop :=
  ∃ (z : Formula V) (classes : V → Formula W),
    IsStarFormula owner other z ∧
    (∀ v, JoinFamily Formula.var (Finset.univ.filter (fun w => π w=v)) (classes v)) ∧
    g = z.subst classes

/-- Replacing each variable in a normalized star formula by the OR of its
independent twin class produces a biclique formula dominating every formula
for the blowup in the pointwise read order. The class map is surjective. -/
theorem twin_blowup_replacement {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length)
    (π : W → V) (onto : Function.Surjective π) (f : Formula W)
    (correct : ∀ x, f.eval x = true ↔
      ∃ a b, G.Adj (π a) (π b) ∧ x a=true ∧ x b=true) :
    ∃ (owner other : ↥G.edgeFinset → V) (g : Formula W),
      (∀ e, e.val=s(owner e,other e)) ∧ (∀ e, owner e≠other e) ∧
      IsBlownStarFormula π owner other g ∧ (∀ x, g.eval x = f.eval x) ∧
      ∀ w, (g.occSet w).card ≤ (f.occSet w).card := by
  classical
  let fibre (v : V) := Finset.univ.filter (fun w => π w=v)
  have rep_exists (v : V) : ∃ w, π w=v ∧
      ∀ u, π u=v → (f.occSet w).card ≤ (f.occSet u).card := by
    obtain ⟨w,hw⟩ := onto v
    have nonempty : (fibre v).Nonempty := ⟨w,by simp [fibre,hw]⟩
    obtain ⟨k,hk,hm⟩ := (fibre v).exists_min_image (fun i => (f.occSet i).card) nonempty
    exact ⟨k,by simpa [fibre] using hk,fun u hu => hm u (by simp [fibre,hu])⟩
  choose rep rep_eq rep_min using rep_exists
  let keep (w : W) : Formula V := if rep (π w)=w then .var (π w) else .const false
  let base := f.subst keep
  have keep_eval (x : V → Bool) (w : W) :
      (keep w).eval x=true ↔ rep (π w)=w ∧ x (π w)=true := by
    by_cases h : rep (π w)=w <;> simp [keep,h,Formula.eval]
  have base_correct (x : V → Bool) :
      base.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
    rw [show base.eval x = _ from Formula.eval_subst keep f x,correct]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      exact ⟨π a,π b,hab,((keep_eval x a).mp ha).2,((keep_eval x b).mp hb).2⟩
    · rintro ⟨u,v,huv,xu,xv⟩
      refine ⟨rep u,rep v,by simpa only [rep_eq] using huv,?_,?_⟩
      · exact (keep_eval x _).mpr (by simp [rep_eq,xu])
      · exact (keep_eval x _).mpr (by simp [rep_eq,xv])
  have read_keep (v : V) : (base.occSet v).card = (f.occSet (rep v)).card := by
    have how (w : W) : ((keep w).occSet v).card = if w=rep v then 1 else 0 := by
      by_cases h : rep (π w)=w
      · have eqf : keep w = .var (π w) := by simp [keep,h]
        rw [eqf,card_occ_var]
        by_cases eq : π w=v
        · have same : w=rep v := h.symm.trans (congrArg rep eq)
          simp [same,rep_eq]
        · have diff : w≠rep v := fun wv => eq ((congrArg π wv).trans (rep_eq v))
          simp [eq,diff]
      · have diff : w≠rep v := by
          rintro rfl
          exact h (congrArg rep (rep_eq v))
        have eqf : keep w = .const false := by simp [keep,h]
        rw [eqf,card_occ_const]
        simp [diff]
    simp [base,Formula.card_occ_subst,how]
  obtain ⟨owner,other,z,ends,diff,shape,zeval,zread⟩ :=
    pointwise_star_replacement G girth base base_correct
  choose classes hc using (fun v => JoinFamily.exists_for Formula.var (fibre v))
  refine ⟨owner,other,z.subst classes,ends,diff,⟨z,classes,shape,hc,rfl⟩,?_,?_⟩
  · intro x
    rw [Formula.eval_subst,zeval]
    apply Bool.eq_iff_iff.mpr
    rw [base_correct,correct]
    have cls (v : V) : (classes v).eval x=true ↔ ∃ w, π w=v ∧ x w=true := by
      simp [(hc v).eval_iff,fibre,Formula.eval]
    constructor
    · rintro ⟨u,v,uv,hu,hv⟩
      obtain ⟨a,ha,xa⟩ := (cls u).mp hu
      obtain ⟨b,hb,xb⟩ := (cls v).mp hv
      exact ⟨a,b,ha ▸ hb ▸ uv,xa,xb⟩
    · rintro ⟨a,b,ab,xa,xb⟩
      exact ⟨π a,π b,ab,(cls _).mpr ⟨a,rfl,xa⟩,(cls _).mpr ⟨b,rfl,xb⟩⟩
  · intro w
    have counts (v : V) : ((classes v).occSet w).card = if π w=v then 1 else 0 := by
      rw [(hc v).card_occ]
      simp [card_occ_var,fibre]
    have ct : ((z.subst classes).occSet w).card = (z.occSet (π w)).card := by
      simp [Formula.card_occ_subst,counts]
    exact ct.le.trans ((zread (π w)).trans ((read_keep (π w)).le.trans (rep_min (π w) w rfl)))

end Pointwise
end WeightedFormula

#print axioms WeightedFormula.Pointwise.twin_blowup_replacement
