import ReadBudgets
namespace WeightedFormula.Budgets
open Finset Sym2
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem slots_iff_vertex_hall (b : V → ℕ) :
    (∀ T : Finset (Slots G b), T.card ≤ (T.biUnion (fun i => incident G i.1)).card) ↔
    ∀ S : Finset V, (∑ v∈S, demand (incident G v).card (b v)) ≤ (S.biUnion (incident G)).card := by
  classical
  let slots (S : Finset V) : Finset (Slots G b) := S.sigma (fun _ => Finset.univ)
  have count (S : Finset V) : (slots S).card=∑ v∈S, demand (incident G v).card (b v) := by
    simp [slots,Finset.card_sigma]
  constructor
  · intro h S
    rw [←count]
    apply (h (slots S)).trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨i,hi,ie⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨i.1,(Finset.mem_sigma.mp hi).1,ie⟩
  · intro h T
    let S := T.image Sigma.fst
    have sub : T ⊆ slots S := by
      intro i hi
      exact Finset.mem_sigma.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_univ _⟩
    have eq : S.biUnion (incident G) = T.biUnion (fun i => incident G i.1) := by
      ext e
      simp [S]
    rw [←eq]
    exact (Finset.card_le_card sub).trans ((count S).le.trans (h S))

noncomputable def inside (S : Finset V) : Finset (Edges G) :=
  univ.filter (fun e => ∀ v∈e.val, v∈S)

theorem incidence_count (S : Finset V) :
    (∑ v∈S, (incident G v).card) = (S.biUnion (incident G)).card + (inside G S).card := by
  classical
  have hits : S.biUnion (incident G) = univ.filter (fun e : Edges G => ∃ v∈S, v∈e.val) := by
    ext e
    simp [incident]
  rw [hits,inside,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
  simp_rw [incident,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  obtain ⟨a,b,ab⟩ : ∃ a b, e.val=s(a,b) := Sym2.inductionOn e.val (fun a b => ⟨a,b,rfl⟩)
  have h := e.property
  rw [ab,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] at h
  have ne := h.ne
  rw [ab]
  have atom (x : V) : (if x∈s(a,b) then 1 else 0 : ℕ) = (if x=a then 1 else 0)+(if x=b then 1 else 0) := by
    simp only [Sym2.mem_iff]
    split_ifs <;> grind
  simp_rw [atom]
  rw [Finset.sum_add_distrib]
  by_cases a∈S <;> by_cases b∈S <;> simp_all <;> grind

theorem read_budgets_iff_density (b : V → ℕ)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length) :
    (∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      ∀ v, (f.occSet v).card ≤ b v) ↔
    ∀ S : Finset V, (∀ v∈S, b v < (incident G v).card) →
      (inside G S).card + S.card ≤ ∑ v∈S, b v := by
  classical
  rw [read_budgets_iff_hall G b girth,slots_iff_vertex_hall]
  have high (S : Finset V) (hi : ∀ v∈S, b v < (incident G v).card) :
      (∑ v∈S, demand (incident G v).card (b v)) ≤ (S.biUnion (incident G)).card ↔
      (inside G S).card+S.card ≤ ∑ v∈S, b v := by
    have eq : (∑ v∈S, demand (incident G v).card (b v))+(∑ v∈S, b v) =
        (∑ v∈S, (incident G v).card)+S.card := by
      calc
        _ = ∑ v∈S, (demand (incident G v).card (b v) + b v) := (Finset.sum_add_distrib).symm
        _ = ∑ v∈S, ((incident G v).card+1) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hlt := hi v hv
          simp only [demand,ite_eq_left hlt]
          omega
        _ = _ := by simp [Finset.sum_add_distrib]
    have cnt := incidence_count G S
    omega
  constructor
  · intro h S hi
    exact (high S hi).mp (h S)
  · intro h S
    let T := S.filter (fun v => b v < (incident G v).card)
    have ht (v) (hv : v∈T) := (Finset.mem_filter.mp hv).2
    have eq : (∑ v∈T, demand (incident G v).card (b v)) = ∑ v∈S, demand (incident G v).card (b v) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro v hv hnot
      have hle : ¬b v<(incident G v).card := fun hh => hnot (Finset.mem_filter.mpr ⟨hv,hh⟩)
      simp [demand,hle]
    rw [←eq]
    apply ((high T ht).mpr (h T ht)).trans
    apply Finset.card_le_card
    intro e he
    obtain ⟨v,hv,ve⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨v,(Finset.mem_filter.mp hv).1,ve⟩
end WeightedFormula.Budgets
#print axioms WeightedFormula.Budgets.read_budgets_iff_density
