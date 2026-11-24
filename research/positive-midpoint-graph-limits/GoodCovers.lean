import BipartiteHelly
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Midpoint
open Filter
open scoped Topology BigOperators
noncomputable section
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

/-- `a` lists the omitted vertices. They can be omitted from a cover exactly
when no crossing edge joins the two omitted sets. -/
def Legal (edge : L→R→Prop) (a : Omitted L R) := ∀ l∈a.1, ∀ r∈a.2, ¬edge l r

theorem legal_closed (edge : L→R→Prop) : Closed {a | Legal edge a} where
  left a ha b hb := by
    intro l hl r hr
    rcases Finset.mem_union.mp hl with x|x
    · exact ha l x r (Finset.mem_inter.mp hr).1
    · exact hb l x r (Finset.mem_inter.mp hr).2
  right a ha b hb := by
    intro l hl r hr
    rcases Finset.mem_union.mp hr with x|x
    · exact ha l (Finset.mem_inter.mp hl).1 r x
    · exact hb l (Finset.mem_inter.mp hl).2 r x

def factor {I : Type*} [Fintype I] [DecidableEq I] (a : Finset I) (u : I→ℝ) : ℝ :=
  ∏ i, if i∈a then 1 else u i

lemma factor_uncross {I : Type*} [Fintype I] [DecidableEq I] (a b : Finset I) (u : I→ℝ) :
    factor a u * factor b u = factor (a∪b) u * factor (a∩b) u := by
  simp only [factor,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases ha : i∈a <;> by_cases hb : i∈b <;> simp [ha,hb]

def event (a : Omitted L R) (u : L→ℝ) (v : R→ℝ) : ℝ := factor a.1 u * factor a.2 v

theorem event_uncross (a b : Omitted L R) (u : L→ℝ) (v : R→ℝ) (c : ℝ) :
    (c * event a u v) * (c * event b u v) =
    (c * event (leftUnion a b) u v) * (c * event (rightUnion a b) u v) := by
  unfold event leftUnion rightUnion
  dsimp only
  have l := factor_uncross a.1 b.1 u
  have r := factor_uncross a.2 b.2 v
  calc
    _ = (c*c)*(factor a.1 u*factor b.1 u)*(factor a.2 v*factor b.2 v) := by ring
    _ = _ := by rw [l,r]; ring

/-- The positive covers at the midpoint form a sublattice once all the
rescaled event probabilities have a common convergent subsequence. -/
theorem positive_closed (edge : L→R→Prop) (c : ℕ→ℝ) (u : ℕ→L→ℝ) (v : ℕ→R→ℝ)
    (w : Omitted L R→ℝ) (lim : ∀ a, Legal edge a →
      Tendsto (fun j => c j * event a (u j) (v j)) atTop (𝓝 (w a)))
    (nonneg : ∀ a, Legal edge a → 0≤w a) : Closed {a | Legal edge a ∧ 0<w a} := by
  have both (a b : Omitted L R) (ha : Legal edge a) (hb : Legal edge b)
      (pa : 0<w a) (pb : 0<w b) : 0<w (leftUnion a b) ∧ 0<w (rightUnion a b) := by
    have hl := (legal_closed edge).left a ha b hb
    have hr := (legal_closed edge).right a ha b hb
    have eq : w a*w b = w (leftUnion a b)*w (rightUnion a b) := by
      apply tendsto_nhds_unique ((lim a ha).mul (lim b hb))
      apply ((lim _ hl).mul (lim _ hr)).congr'
      exact Filter.Eventually.of_forall (fun j => (event_uncross a b (u j) (v j) (c j)).symm)
    have pos := mul_pos pa pb
    rw [eq] at pos
    exact ⟨pos_of_mul_pos_left pos (nonneg _ hr),pos_of_mul_pos_right pos (nonneg _ hl)⟩
  exact ⟨fun a ha b hb => ⟨(legal_closed edge).left a ha.1 b hb.1,(both a b ha.1 hb.1 ha.2 hb.2).1⟩,
    fun a ha b hb => ⟨(legal_closed edge).right a ha.1 b hb.1,(both a b ha.1 hb.1 ha.2 hb.2).2⟩⟩

end
end Midpoint
#print axioms Midpoint.positive_closed
