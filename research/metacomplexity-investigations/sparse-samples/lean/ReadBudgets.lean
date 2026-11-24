import ReadOptimal
import Mathlib.Combinatorics.Hall.Finite
namespace WeightedFormula.Budgets
open Finset Sym2
open WeightedFormula.Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev Edges := ↥G.edgeFinset
noncomputable def incident (v : V) : Finset (Edges G) :=
  Finset.univ.filter (fun e => v∈e.val)
def demand (degree budget : ℕ) : ℕ := if budget < degree then degree-budget+1 else 0
abbrev Slots (b : V → ℕ) := (v : V) × Fin (demand (incident G v).card (b v))

private theorem degree_split (owner other : Edges G → V)
    (ends : ∀ e, e.val=s(owner e,other e)) (diff : ∀ e, owner e≠other e) (v : V) :
    (incident G v).card = (univ.filter (fun e => owner e=v)).card + (univ.filter (fun e => other e=v)).card := by
  classical
  have h : incident G v = (univ.filter (fun e => owner e=v)) ∪ (univ.filter (fun e => other e=v)) := by
    ext e
    simp [incident,ends e,eq_comm]
  rw [h,Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (by intro e a b; simp only [mem_filter,mem_univ,true_and] at a b; exact diff e (a.trans b.symm))

private theorem feasibility (owner other : Edges G → V)
    (ends : ∀ e, e.val=s(owner e,other e)) (diff : ∀ e, owner e≠other e) (b : V → ℕ) (v : V) :
    (univ.filter (fun e => other e=v)).card + (if v∈univ.image owner then 1 else 0) ≤ b v ↔
      demand (incident G v).card (b v) ≤ (univ.filter (fun e => owner e=v)).card := by
  classical
  have h := degree_split G owner other ends diff v
  have nz : v∈univ.image owner ↔ 0 < (univ.filter (fun e => owner e=v)).card := by
    rw [Finset.card_pos]
    simp [Finset.Nonempty]
  simp only [nz]
  unfold demand
  split_ifs <;> omega

theorem read_budgets_iff_hall (b : V → ℕ)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length) :
    (∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      ∀ v, (f.occSet v).card ≤ b v) ↔
    ∀ S : Finset (Slots G b), S.card ≤ (S.biUnion (fun i => incident G i.1)).card := by
  classical
  rw [Finset.all_card_le_biUnion_card_iff_existsInjective']
  constructor
  · rintro ⟨f,corr,budget⟩
    obtain ⟨owner,other,ends,diff,counts⟩ := occurrence_orientation G girth f corr
    let owned (v : V) := univ.filter (fun e => owner e=v)
    have enough (v : V) : demand (incident G v).card (b v) ≤ Fintype.card ↥(owned v) := by
      simpa only [Fintype.card_coe,owned] using (feasibility G owner other ends diff b v).mp ((counts v).trans (budget v))
    let pick (v : V) := (Fin.castLEEmb (enough v)).trans (Fintype.equivFin ↥(owned v)).symm.toEmbedding
    have head (v : V) (i : Fin (demand (incident G v).card (b v))) : owner (pick v i).val=v := by
      exact (Finset.mem_filter.mp (pick v i).property).2
    refine ⟨fun s => (pick s.1 s.2).val,?_,?_⟩
    · rintro ⟨v,i⟩ ⟨w,j⟩ he
      change (pick v i).val=(pick w j).val at he
      have vw := (head v i).symm.trans ((congrArg owner he).trans (head w j))
      subst w
      have ij := (pick v).injective (Subtype.ext he)
      cases ij
      rfl
    · rintro ⟨v,i⟩
      simp only [incident,mem_filter,mem_univ,true_and]
      change v∈(pick v i).val.val
      rw [ends,head]
      exact Sym2.mem_mk_left _ _
  · rintro ⟨matchEdge,inj,valid⟩
    have any (e : Edges G) : ∃ v, v∈e.val :=
      Sym2.inductionOn e.val (fun a b => ⟨a,Sym2.mem_mk_left a b⟩)
    let owner (e : Edges G) := if h : ∃ i, matchEdge i=e then h.choose.1 else (any e).choose
    have matched (i : Slots G b) : owner (matchEdge i)=i.1 := by
      have h : ∃ j, matchEdge j=matchEdge i := ⟨i,rfl⟩
      simp only [owner,dite_eq_left h]
      rw [inj h.choose_spec]
    have internal (e : Edges G) : owner e∈e.val := by
      dsimp only [owner]
      split
      next h =>
        have hi := valid h.choose
        simpa only [incident,mem_filter,mem_univ,true_and,h.choose_spec] using hi
      next h => exact (any e).choose_spec
    let other (e : Edges G) := Sym2.Mem.other (internal e)
    have ends (e : Edges G) : e.val=s(owner e,other e) := (Sym2.other_spec (internal e)).symm
    have diff (e : Edges G) : owner e ≠ other e := by
      have good := e.property
      rw [ends,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at good
      exact good.ne
    obtain ⟨f,_,ev,cnt⟩ := star_formula_spec owner other
    refine ⟨f,?_,?_⟩
    · intro x
      rw [ev]
      constructor
      · rintro ⟨e,ha,hb⟩
        have good := e.property
        rw [ends,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at good
        exact ⟨owner e,other e,good,ha,hb⟩
      · rintro ⟨u,v,uv,hu,hv⟩
        let e : Edges G := ⟨s(u,v),by simpa using uv⟩
        have he : s(u,v)=s(owner e,other e) := ends e
        rw [Sym2.eq_iff] at he
        exact ⟨e,by grind⟩
    · intro v
      rw [cnt,feasibility G owner other ends diff b]
      let owned := univ.filter (fun e => owner e=v)
      let g (i : Fin (demand (incident G v).card (b v))) : ↥owned :=
        ⟨matchEdge ⟨v,i⟩,by simp [owned,matched]⟩
      have ginj : Function.Injective g := by
        intro i j h
        have hs := inj (congrArg Subtype.val h)
        simpa using hs
      simpa only [Fintype.card_fin,Fintype.card_coe,owned] using Fintype.card_le_of_injective g ginj
end WeightedFormula.Budgets
#print axioms WeightedFormula.Budgets.read_budgets_iff_hall
