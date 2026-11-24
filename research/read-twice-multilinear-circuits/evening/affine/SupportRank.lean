import CutRank
import Mathlib.Data.Fintype.Powerset

/-! Any matrix with the disjointness zero pattern and nonzero complementary
pairs has full rank. Values on the other feasible pairs may be arbitrary. -/
namespace CutRank
noncomputable section
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem subset_support_rank (M : Matrix (Finset I) (Finset I) K)
    (zeros : ∀ a b, ¬a⊆b → M a b=0) (diag : ∀ a, M a a≠0) :
    M.rank = 2^Fintype.card I := by
  classical
  have det : M.det = ∏ a, M a a := by
    rw [Matrix.det_apply,Finset.sum_eq_single (1 : Equiv.Perm (Finset I))]
    · simp
    · intro σ _ ne
      have outside : ∃ a, ¬σ a⊆a := by
        by_contra! all
        apply ne
        ext a : 1
        change σ a=a
        apply Finset.eq_of_subset_of_card_le (all a)
        by_contra! lt
        have strict := Finset.sum_lt_sum (s:=Finset.univ)
          (fun j _ => Finset.card_le_card (all j)) ⟨a,Finset.mem_univ _,lt⟩
        have total := Equiv.sum_comp σ (fun j : Finset I => j.card)
        omega
      obtain ⟨j,hj⟩ := outside
      rw [Finset.prod_eq_zero (f:=fun i => M (σ i) i) (Finset.mem_univ j) (zeros _ _ hj),smul_zero]
    · simp
  have nz : M.det ≠ 0 := det ▸ Finset.prod_ne_zero_iff.mpr (fun a _ => diag a)
  rw [Matrix.rank_of_det_ne_zero nz,Fintype.card_finset]

/-- If rows and columns of a larger flattening restrict to a subset-support
matrix, its rank is at least the full power of two. -/
theorem support_cut_lower {A B : Type*} [Fintype A] [Fintype B]
    (T : Matrix A B K) (left : Finset I→A) (right : Finset I→B)
    (zeros : ∀ a b, ¬a⊆b → T (left a) (right b)=0)
    (diag : ∀ a, T (left a) (right a)≠0) : 2^Fintype.card I ≤ T.rank := by
  have h := subset_support_rank (T.submatrix left right) zeros diag
  rw [← h]
  exact T.rank_submatrix_le _ _

end
end CutRank
#print axioms CutRank.support_cut_lower
