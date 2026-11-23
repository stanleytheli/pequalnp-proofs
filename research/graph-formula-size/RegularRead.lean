import ReadDensity
namespace WeightedFormula.Budgets
open Finset Sym2
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem regular_readability (d b : ℕ) (two : 2 ≤ d)
    (regular : ∀ v, (incident G v).card = d)
    (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5≤p.length) :
    (∃ f : Formula V, (∀ x, f.eval x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true) ∧
      ∀ v, (f.occSet v).card ≤ b) ↔ (d+1)/2+1 ≤ b := by
  classical
  rw [read_budgets_iff_density G (fun _ => b) girth]
  have incid (S : Finset V) := incidence_count G S
  simp only [regular,Finset.sum_const,smul_eq_mul] at incid
  have touched : (univ : Finset V).biUnion (incident G) = univ := by
    ext e
    simp only [mem_biUnion,mem_univ,true_and,iff_true]
    obtain ⟨v,hv⟩ : ∃ v, v∈e.val := Sym2.inductionOn e.val (fun a c => ⟨a,Sym2.mem_mk_left a c⟩)
    exact ⟨v,Finset.mem_filter.mpr ⟨mem_univ _,hv⟩⟩
  have allInside : inside G univ = univ := by ext e; simp [inside]
  constructor
  · intro feasible
    by_contra h
    have small : b<d := by omega
    have cap := feasible (univ : Finset V) (fun v _ => (regular v).symm ▸ small)
    have full := incid (univ : Finset V)
    rw [touched,allInside] at full
    simp only [allInside,Finset.sum_const,smul_eq_mul] at cap
    have pos : 0 < (univ : Finset V).card := Finset.card_pos.mpr Finset.univ_nonempty
    have scaled := Nat.mul_lt_mul_of_pos_right (show 2*b<d+2 by omega) pos
    nlinarith
  · intro enough S _
    have sub : inside G S ⊆ S.biUnion (incident G) := by
      intro e he
      have h := (Finset.mem_filter.mp he).2
      obtain ⟨v,hv⟩ : ∃ v, v∈e.val := Sym2.inductionOn e.val (fun a c => ⟨a,Sym2.mem_mk_left a c⟩)
      exact Finset.mem_biUnion.mpr ⟨v,h v hv,Finset.mem_filter.mpr ⟨mem_univ _,hv⟩⟩
    have c := Finset.card_le_card sub
    have total := incid S
    have scaled := Nat.mul_le_mul_right S.card (show d+2 ≤ 2*b by omega)
    simp only [Finset.sum_const,smul_eq_mul]
    nlinarith
end WeightedFormula.Budgets
#print axioms WeightedFormula.Budgets.regular_readability
