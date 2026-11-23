import ProjectivePlane650
import PointwiseFormula

namespace ProjectivePlane650
open WeightedFormula WeightedFormula.Pointwise Finset Sym2

theorem matching_reaches : ∀ i j : Fin 13, ∃ a b : Fin 13,
    matched a∈N (point i) ∧ matched b∈N (point a) ∧ matched j∈N (point b) := by
  decide +kernel

theorem matching_exhausts : ∀ v : V, (∃ i, point i=v) ∨ (∃ i, matched i=v) := by decide +kernel

private theorem matched_out : ∀ i, matched i∉allPoints := by decide +kernel

/-- Every minimum cover of the order-three incidence graph is one complete side. -/
theorem unique_cover_sides (T : Finset V) (cov : ∀ u v, G.Adj u v → u∈T ∨ v∈T)
    (card : T.card=13) : T=allPoints ∨ T=Finset.univ \ allPoints := by
  classical
  let pick (i : Fin 13) := if point i∈T then point i else matched i
  have mem (i : Fin 13) : pick i∈T := by
    have h := cov _ _ (match_data.1 i)
    by_cases hi : point i∈T <;> simp_all [pick]
  have inj : Function.Injective pick := by
    intro i j eq
    by_cases hi : point i∈T <;> by_cases hj : point j∈T <;> simp [pick,hi,hj] at eq
    · exact point_injective eq
    · exact (match_data.2.2 i j eq).elim
    · exact (match_data.2.2 j i eq.symm).elim
    · exact match_data.2.1 i j eq
  have img : Finset.univ.image pick=T := Finset.eq_of_subset_of_card_le
    (fun v hv => by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv; exact mem i)
    (by simp [Finset.card_image_of_injective _ inj,card])
  have opposite (i : Fin 13) : matched i∈T ↔ point i∉T := by
    constructor
    · intro ha hb
      have hm := img ▸ ha
      obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hm
      by_cases hj : point j∈T
      · simp only [pick,ite_eq_left hj] at eq
        exact match_data.2.2 j i eq
      · have eqj : j=i := match_data.2.1 j i (by simpa [pick,hj] using eq)
        exact hj (eqj ▸ hb)
    · intro h
      exact (cov _ _ (match_data.1 i)).resolve_left h
  have step (i j : Fin 13) (adj : matched j∈N (point i)) (hi : point i∉T) : point j∉T :=
    (opposite j).mp ((cov _ _ adj).resolve_left hi)
  by_cases all : ∀ i, point i∈T
  · left
    ext v
    rcases matching_exhausts v with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · simp [all,allPoints]
    · simp [matched_out,opposite,all]
  · right
    push Not at all
    obtain ⟨i,hi⟩ := all
    have none (j : Fin 13) : point j∉T := by
      obtain ⟨a,b,h1,h2,h3⟩ := matching_reaches i j
      exact step _ _ h3 (step _ _ h2 (step _ _ h1 hi))
    ext v
    rcases matching_exhausts v with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · simp [none,allPoints]
    · simp [matched_out,opposite,none]

/-- In every minimum formula, either every point occurs once or every line occurs once. -/
theorem optimal_reads (f : Formula V) (correct : ∀ x, f.eval x=true ↔ accepts x)
    (short : f.leaves≤65) :
    (∀ v∈allPoints, (f.occSet v).card=1) ∨
      (∀ v∈Finset.univ \ allPoints, (f.occSet v).card=1) := by
  classical
  obtain ⟨own,other,ends,diff,occ⟩ := occurrence_orientation_local G (@triangle) (@square) f
    (fun x => (correct x).trans (accepts_iff x))
  let E := ↥G.edgeFinset
  let T := Finset.univ.image own
  let away (v : V) := Finset.univ.filter (fun e => other e=v)
  let bound (v : V) := (away v).card + if v∈T then 1 else 0
  have cov (a b : V) (ab : G.Adj a b) : a∈T ∨ b∈T := by
    let e : E := ⟨s(a,b),by simpa using ab⟩
    have h : s(a,b)=s(own e,other e) := ends e
    rw [Sym2.eq_iff] at h
    have mem : own e∈T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    grind
  have sa : (∑ v : V, (away v).card)=52 := by
    simp only [away,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    simpa using num_edges
  have total : (∑ v : V, bound v)=52+T.card := by
    simp [bound,Finset.sum_add_distrib,sa]
  have raw : (∑ v : V, (f.occSet v).card) ≤ f.leaves := by
    simp only [Formula.occSet,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm,← f.card_leaf,← Finset.card_univ,Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro l _
    cases f.label l <;> simp
  have pts (v : V) : bound v≤(f.occSet v).card := occ v
  have lower := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => pts v)
  have min := min_cover T cov
  have eqsum : (∑ v : V, bound v) = ∑ v : V, (f.occSet v).card := by omega
  have eqs : ∀ v : V, bound v = (f.occSet v).card :=
    fun v => (Finset.sum_eq_sum_iff_of_le (fun i _ => pts i)).mp eqsum v (Finset.mem_univ v)
  have tc : T.card=13 := by omega
  have sides := unique_cover_sides T cov tc
  have bip : ∀ u v : V, v∈N u → (u∈allPoints ↔ v∉allPoints) := by decide +kernel
  have independent {u v : V} (uv : G.Adj u v) (hu : u∈T) (hv : v∈T) : False := by
    have B := bip u v uv
    rcases sides with h | h
    · rw [h] at hu hv
      exact (B.mp hu) hv
    · rw [h] at hu hv
      simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hu hv
      exact hu (B.mpr hv)
  have one (v : V) (hv : v∈T) : (f.occSet v).card=1 := by
    rw [← eqs v]
    have emp : away v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have ev : other e=v := by simpa [away] using he
      have edge := e.property
      rw [ends e,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at edge
      exact independent edge (Finset.mem_image_of_mem _ (Finset.mem_univ _)) (ev ▸ hv)
    simp [bound,emp,hv]
  rcases sides with ht | ht
  · exact Or.inl (ht ▸ one)
  · exact Or.inr (ht ▸ one)

end ProjectivePlane650

#print axioms ProjectivePlane650.optimal_reads
