import SubdivisionPath
import StarForest
import SubdivisionUpper
import SevenLayout

namespace Subdivision.Layout
open Finset PEqualNP.MetaComplexity
variable {n m : ℕ} (B : Subdivision.Layout n m)

/-- The lower bound permits arbitrary sharing and unary NOT, in the project circuit model. -/
theorem circuit_lower (k s : ℕ) (many : 2 ≤ m)
    (coverLower : ∀ T : Finset (Fin n), (∀ e, B.left e∈T ∨ B.right e∈T) → k ≤ T.card)
    (o : Fin m → Bool) (size : HasCircuitSize n (B.board univ o) s) :
    3 * (∑ e, B.half e) + m + k ≤ s+1 := by
  classical
  obtain ⟨z,p,pay,term⟩ := B.reduce_all univ many o s size
  let own (e : Fin m) := B.head e (p e)
  let tip (e : Fin m) := B.inner e (B.first e)
  have inj : Function.Injective tip := by
    intro a b eq
    by_contra ab
    exact B.apart (B.first a) (B.first b) ab eq
  have disj (i j : Fin m) : own i ≠ tip j := by
    dsimp [own,tip,head]
    split <;> first | exact (B.notLeft _ _ _).symm | exact (B.notRight _ _ _).symm
  have sem (x : Subdivision.Assignment n) : B.board ∅ p x=true ↔
      ∃ i, x (own i)=true ∧ x (tip i)=true := by simp [board,active,own,tip]
  have cost := Subdivision.StarForest.general_lower own tip inj disj sem term
  have covers (e : Fin m) : B.left e∈univ.image own ∨ B.right e∈univ.image own := by
    have mem := mem_image_of_mem own (mem_univ e)
    dsimp [own,head] at mem
    split at mem
    · exact Or.inl mem
    · exact Or.inr mem
  have bound := coverLower _ covers
  rw [←Finset.mul_sum] at pay
  omega
end Subdivision.Layout
#print axioms Subdivision.Layout.circuit_lower

namespace Subdivision.Layout
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n m : ℕ} (B : Subdivision.Layout n m)

/-- A vertex cover of the original graph, using the endpoints before subdivision. -/
def Covers (T : Finset (Fin n)) : Prop := ∀ e,B.left e∈T ∨ B.right e∈T

private theorem exists_cover : ∃ k : ℕ,∃ T : Finset (Fin n),B.Covers T ∧ T.card≤k :=
  ⟨n,univ,fun _=>Or.inl (mem_univ _),by simp⟩

/-- Minimum vertex-cover size of the original graph. -/
noncomputable def coverNumber : ℕ:=by classical exact Nat.find B.exists_cover

theorem coverNumber_spec : ∃ T : Finset (Fin n),B.Covers T ∧ T.card≤B.coverNumber := by
  classical exact Nat.find_spec B.exists_cover

theorem coverNumber_le (T : Finset (Fin n)) (h:B.Covers T) : B.coverNumber≤T.card := by
  classical exact Nat.find_min' B.exists_cover ⟨T,h,le_rfl⟩

noncomputable def gateCount : ℕ := 3*(∑ e,B.half e)+m+B.coverNumber-1

/-- Exact threshold for arbitrary shared fan-in-two De Morgan circuits. -/
theorem hasCircuitSize_iff (many : 2 ≤ m) (o : Fin m→Bool) (s : ℕ) :
    HasCircuitSize n (B.board univ o) s ↔ B.gateCount ≤ s := by
  constructor
  · intro size
    have h:=B.circuit_lower B.coverNumber s many (fun T h=>B.coverNumber_le T h) o size
    unfold gateCount;omega
  · intro bound
    obtain ⟨T,covers,le⟩:=B.coverNumber_spec
    obtain ⟨C,fan,small,ok⟩:=B.circuit_upper T covers (by omega) o
    exact ⟨C,fan,small.trans (by unfold gateCount at bound;omega),ok⟩

/-- A physical circuit attains the exact gate count. -/
theorem minimum_attained (many : 2 ≤ m) (o : Fin m→Bool) :
    ∃ C : Circuit,FanInTwo C ∧ C.size=B.gateCount ∧ ∀ x : Assignment n,C.eval (List.ofFn x)=B.board univ o x := by
  obtain ⟨C,fan,ub,correct⟩:=(B.hasCircuitSize_iff many o B.gateCount).mpr le_rfl
  have lb: B.gateCount≤C.size := (B.hasCircuitSize_iff many o C.size).mp ⟨C,fan,le_rfl,correct⟩
  exact ⟨C,fan,Nat.le_antisymm ub lb,correct⟩

/-- The circuit-size threshold and vertex-cover threshold agree after an explicit offset. -/
theorem threshold_iff_cover (many : 2 ≤ m) (o : Fin m→Bool) (k : ℕ) :
    HasCircuitSize n (B.board univ o) (3*(∑ e,B.half e)+m+k-1) ↔
      ∃ T : Finset (Fin n),B.Covers T ∧ T.card≤k := by
  rw [B.hasCircuitSize_iff many]
  unfold gateCount
  constructor
  · intro bound
    obtain ⟨T,h,le⟩:=B.coverNumber_spec
    exact ⟨T,h,by omega⟩
  · rintro ⟨T,h,le⟩
    have l:=B.coverNumber_le T h
    omega

/-- Specializing to seven-edge paths gives the linear gate threshold used in the reduction. -/
theorem seven_edge_threshold (many : 2 ≤ m) (lengths:∀ e,B.half e=3) (o : Fin m→Bool) (k : ℕ) :
    HasCircuitSize n (B.board univ o) (10*m+k-1) ↔
      ∃ T : Finset (Fin n),B.Covers T ∧ T.card≤k := by
  have sum : (∑ e,B.half e)=m*3:=by simp [lengths]
  have eq:3*(∑ e,B.half e)+m+k-1=10*m+k-1:=by rw [sum];omega
  rw [←eq]
  exact B.threshold_iff_cover many o k

end Subdivision.Layout

#print axioms Subdivision.Layout.hasCircuitSize_iff
#print axioms Subdivision.Layout.minimum_attained
#print axioms Subdivision.Layout.threshold_iff_cover

#print axioms Subdivision.Layout.seven_edge_threshold

namespace Subdivision.Seven
open Finset PEqualNP.MetaComplexity

/-- Direct decision reduction from finite Vertex Cover to the project's physical circuit model. -/
theorem seven_edge_reduction {v m : ℕ} (l r : Fin m → Fin v) (d : ∀ e,l e ≠ r e)
    (many : 2 ≤ m) (k : ℕ) :
    HasCircuitSize (v+m*6) ((layout l r d).board univ (fun _ => false)) (10*m+k-1) ↔
      ∃ T : Finset (Fin v), (∀ e,l e ∈ T ∨ r e ∈ T) ∧ T.card ≤ k := by
  have halfSum : (∑ e,(layout l r d).half e)=m*3 := by simp [layout]
  have threshold := (layout l r d).threshold_iff_cover many (fun _ => false) k
  rw [halfSum,show 3*(m*3)+m+k-1=10*m+k-1 by omega] at threshold
  exact threshold.trans (covers_iff l r d k)

end Subdivision.Seven
#print axioms Subdivision.Seven.seven_edge_reduction

