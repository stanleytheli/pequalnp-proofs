import OracleFlow
import MatchingFace
import PermanentAmplitudes

/-! A fractional matching on a graph with pinned zero entries decomposes over
permutations of that very graph, including when previous gates occupy several slots. -/
namespace PositivePermanent.Flow
open Finset Matrix
open scoped BigOperators
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem masked_decomposition (P : Matrix I I ℝ) (hP : P∈doublyStochastic ℝ I)
    (allowed : I→I→Prop) (zeros : ∀ i j, ¬allowed i j → P i j=0) :
    ∃ w : Equiv.Perm I → ℝ, (∀ p,0≤w p) ∧ (∑ p,w p)=1 ∧
      (∑ p,w p • p.permMatrix ℝ)=P ∧ ∀ p,0<w p → ∀ i,allowed i (p i) := by
  classical
  obtain ⟨w,nn,one,rep⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  refine ⟨w,nn,one,rep,?_⟩
  intro p pos i
  by_contra missing
  have e := congrArg (fun M : Matrix I I ℝ => M i (p i)) rep
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,zeros i (p i) missing] at e
  have lb : w p * (p.permMatrix ℝ) i (p i) ≤
      ∑ q : Equiv.Perm I, w q * (q.permMatrix ℝ) i (p i) := by
    apply Finset.single_le_sum (f:=fun q : Equiv.Perm I=>w q*(q.permMatrix ℝ) i (p i)) _ (Finset.mem_univ p)
    intro q _
    apply mul_nonneg (nn q)
    simp [Equiv.toPEquiv_apply,PEquiv.toMatrix_apply,Option.mem_def]
    split <;> norm_num
  rw [e] at lb
  simp [Equiv.toPEquiv_apply,PEquiv.toMatrix_apply,Option.mem_def] at lb
  linarith

theorem normalized_gate_limit {X : Type*}
    (c : ℕ→ℝ) (a : ℕ→I→I→ℝ) (w : Equiv.Perm I→ℝ)
    (p : ℕ→I→I→X→ℝ) (q : I→I→X→ℝ)
    (lim : ∀ s, Filter.Tendsto (fun t => c t * ∏ i, a t i (s i)) Filter.atTop (nhds (w s)))
    (nonneg : ∀ s,0≤w s) (survives : ∃ s,0<w s)
    (children : ∀ i j x, Filter.Tendsto (fun t => p t i j x) Filter.atTop (nhds (q i j x))) :
    ∃ b : ℝ, 0 < b ∧ ∃ d : I→I→ℝ, (∀ i j, 0≤d i j) ∧ ∀ x,
      Filter.Tendsto (fun t => ∑ s : Equiv.Perm I,
        (c t * ∏ i,a t i (s i)) * ∏ i,p t i (s i) x) Filter.atTop
        (nhds (b * ∑ s : Equiv.Perm I, ∏ i,d i (s i) * q i (s i) x)) := by
  apply PositivePermanent.normalized_permanent_limit c a w p q lim nonneg _ children
  exact PositivePermanent.limit_face c a w lim nonneg survives

end
end PositivePermanent.Flow
#print axioms PositivePermanent.Flow.masked_decomposition
#print axioms PositivePermanent.Flow.normalized_gate_limit
