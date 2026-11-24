import Mathlib

/-! A crossing induced matching gives an invertible submatrix of the
independent-set truth tensor in every characteristic, including characteristic 2. -/
namespace CutRank
open scoped BigOperators
noncomputable section

def edge {K : Type*} [Zero K] [One K] (a b : Bool) : K := if a && b then 0 else 1

def inverse {K : Type*} [Ring K] (a b : Bool) : K :=
  if a then (if b then -1 else 1) else (if b then 1 else 0)

lemma local_inverse {K : Type*} [CommRing K] (a b : Bool) :
    (∑ c : Bool, (edge a c : K) * inverse c b) = if a=b then 1 else 0 := by
  cases a <;> cases b <;> simp [edge,inverse]

variable {I : Type*} [Fintype I] [DecidableEq I]

def disjointness (I K : Type*) [Fintype I] [Field K] : Matrix (I → Bool) (I → Bool) K :=
  fun x y => ∏ i, edge (x i) (y i)

def leftInverse (I K : Type*) [Fintype I] [Field K] : Matrix (I → Bool) (I → Bool) K :=
  fun x y => ∏ i, inverse (x i) (y i)

theorem invertible_tensor (K : Type*) [Field K] :
    disjointness I K * leftInverse I K = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply,disjointness,leftInverse,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i bit => (edge (x i) bit : K) * inverse bit (y i))]
  simp_rw [local_inverse]
  by_cases he : x=y
  · subst y
    simp [Matrix.one_apply]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [Matrix.one_apply,he]

theorem matching_rank (K : Type*) [Field K] :
    (disjointness I K).rank = 2 ^ Fintype.card I := by
  classical
  have h := Matrix.rank_mul_le_left (disjointness I K) (leftInverse I K)
  rw [invertible_tensor,Matrix.rank_one,Fintype.card_fun,Fintype.card_bool] at h
  exact h.antisymm' (by simpa using (disjointness I K).rank_le_card_width)

theorem rank_add_le {A B K : Type*} [Fintype A] [Fintype B] [Field K]
    (X Y : Matrix A B K) : (X+Y).rank ≤ X.rank+Y.rank := by
  classical
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem constant_rank_le_one {A B K : Type*} [Fintype A] [Fintype B] [Field K] :
    Matrix.rank ((fun (_ : A) (_ : B) => (1 : K)) : Matrix A B K) ≤ 1 := by
  have h := Matrix.rank_vecMulVec_le (fun _ : A => (1 : K)) (fun _ : B => (1 : K))
  have mat : Matrix.vecMulVec (fun _ : A => (1 : K)) (fun _ : B => (1 : K)) =
      (fun _ _ => (1 : K)) := by ext i j; simp [Matrix.vecMulVec]
  rwa [mat] at h

/-- Restricting both parties to the endpoints of an induced matching gives
this submatrix. Every coordinate outside the matching is set to zero. -/
theorem independent_cut_lower {A B K : Type*} [Fintype A] [Fintype B] [Field K]
    (T : Matrix A B K) (left : (I → Bool) → A) (right : (I → Bool) → B)
    (witness : T.submatrix left right = disjointness I K) :
    2 ^ Fintype.card I ≤ T.rank := by
  rw [← matching_rank (I:=I) K,← witness]
  exact T.rank_submatrix_le _ _

/-- Complementing a Boolean output subtracts its truth tensor from the
all-ones matrix, so at most one dimension is lost. -/
theorem edge_cut_lower {A B K : Type*} [Fintype A] [Fintype B] [Field K]
    (T : Matrix A B K) (left : (I → Bool) → A) (right : (I → Bool) → B)
    (witness : T.submatrix left right = disjointness I K) :
    2 ^ Fintype.card I ≤ Matrix.rank ((fun a b => (1 : K)-T a b) : Matrix A B K)+1 := by
  classical
  let J : Matrix A B K := fun _ _ => 1
  let Q : Matrix A B K := fun a b => 1-T a b
  have eq : T = J + (-Q) := by ext a b; change T a b = 1 + -(1-T a b); ring
  have neg : (-Q).rank ≤ Q.rank := by
    let D : Matrix B B K := -1
    have mul : -Q = Q*D := by simp [D]
    rw [mul]
    exact Matrix.rank_mul_le_left _ _
  have cut := independent_cut_lower T left right witness
  rw [eq] at cut
  have h := rank_add_le J (-Q)
  have j : J.rank ≤ 1 := constant_rank_le_one
  change 2 ^ Fintype.card I ≤ Q.rank+1
  omega

end
end CutRank
#print axioms CutRank.independent_cut_lower
#print axioms CutRank.edge_cut_lower
