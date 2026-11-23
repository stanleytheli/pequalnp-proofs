import Mathlib
namespace GraphProbability
open Finset
variable {V E I A : Type*} [Fintype V] [DecidableEq V]
def independent (l r : E→V) (S : Finset V) := ∀ e, ¬(l e∈S ∧ r e∈S)
noncomputable def probability (l r : E→V) (q : V→ℝ) : ℝ := by
  classical
  exact ∑ S : Finset V, if independent l r S then ∏ v, if v∈S then q v else 1-q v else 0

/-- The no-edge event has positive probability precisely when its forced vertices
form an independent set. This also allows probability-zero vertices. -/
theorem probability_pos (l r : E→V) (q : V→ℝ) (bounded : ∀ v,0≤q v ∧ q v≤1) :
    0<probability l r q ↔ ∀ e, ¬(q (l e)=1 ∧ q (r e)=1) := by
  classical
  let weight (S : Finset V) (v : V) := if v∈S then q v else 1-q v
  have weight_nonneg (S : Finset V) (v : V) : 0≤weight S v := by
    unfold weight
    split
    · exact (bounded v).1
    · linarith [(bounded v).2]
  have nonneg (S : Finset V) : 0≤(if independent l r S then ∏ v,weight S v else 0) :=
    by split <;> first | exact Finset.prod_nonneg fun v _=>weight_nonneg S v | rfl
  change 0<(∑ S : Finset V,if independent l r S then ∏ v,weight S v else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg (fun s _=>nonneg s)]
  constructor
  · rintro ⟨S,_,hs⟩
    by_cases ok : independent l r S
    · rw [ite_eq_left ok] at hs
      have forced (v : V) (hv : q v=1) : v∈S := by
        by_contra no
        have zero : weight S v=0 := by simp [weight,no,hv]
        rw [Finset.prod_eq_zero (mem_univ v) zero] at hs
        exact (lt_irrefl _ hs)
      exact fun e h=>ok e ⟨forced _ h.1,forced _ h.2⟩
    · simp [ok] at hs
  · intro h
    let T := univ.filter (fun v=>q v=1)
    have ok : independent l r T := by simpa [independent,T] using h
    refine ⟨T,mem_univ _,?_⟩
    rw [ite_eq_left ok]
    apply Finset.prod_pos
    intro v _
    by_cases hit : q v=1
    · simp [weight,T,hit]
    · have small : q v<1 := lt_of_le_of_ne (bounded v).2 hit
      simp [weight,T,hit,small]

def affine [DecidableEq A] (c : ℝ) (w : A→ℝ) (x : Finset A) := c+∑ i∈x,w i

theorem affine_union_max [DecidableEq A] (c : ℝ) (w : A→ℝ) (x y : Finset A)
    (up : ∀ z,affine c w z≤1) (hx : affine c w x=1) (hy : affine c w y=1) :
    affine c w (x∪y)=1 := by
  have modular : (∑ i∈x∪y,w i)+(∑ i∈x∩y,w i)=(∑i∈x,w i)+(∑i∈y,w i) := Finset.sum_union_inter
  have ux:=up (x∪y)
  have ix:=up (x∩y)
  dsimp [affine] at *
  linarith

/-- Every pairwise-join family of zeros requires a different graph edge per
member whenever the target is modeled by actual independent probabilities
which are affine functions on the full input cube. -/
theorem lower_of_join_family [Fintype E] [Fintype I] [DecidableEq A]
    (l r : E→V) (c : V→ℝ) (w : V→A→ℝ) (x : I→Finset A)
    (bounded : ∀ v z,0≤affine (c v) (w v) z ∧ affine (c v) (w v) z≤1)
    (fail : ∀ i,¬0<probability l r (fun v=>affine (c v) (w v) (x i)))
    (pass : ∀ i j,i≠j → 0<probability l r (fun v=>affine (c v) (w v) (x i∪x j))) :
    Fintype.card I≤Fintype.card E := by
  classical
  have witness (i : I) : ∃ e, affine (c (l e)) (w (l e)) (x i)=1 ∧ affine (c (r e)) (w (r e)) (x i)=1 := by
    by_contra! no
    have h := (probability_pos l r _ (fun v=>bounded v (x i))).mpr (fun e he=>no e he.1 he.2)
    exact fail i h
  let tag (i : I) := (witness i).choose
  have inj : Function.Injective tag := by
    intro i j eq
    by_contra ne
    have hi := (witness i).choose_spec
    have hj := (witness j).choose_spec
    change affine (c (l (tag i))) (w (l (tag i))) (x i)=1 ∧ affine (c (r (tag i))) (w (r (tag i))) (x i)=1 at hi
    change affine (c (l (tag j))) (w (l (tag j))) (x j)=1 ∧ affine (c (r (tag j))) (w (r (tag j))) (x j)=1 at hj
    rw [←eq] at hj
    have h := (probability_pos l r _ (fun v=>bounded v (x i∪x j))).mp (pass i j ne) (tag i)
    exact h ⟨affine_union_max _ _ _ _ (fun z=>(bounded _ z).2) hi.1 hj.1,
      affine_union_max _ _ _ _ (fun z=>(bounded _ z).2) hi.2 hj.2⟩
  exact Fintype.card_le_of_injective _ inj
end GraphProbability
#print axioms GraphProbability.probability_pos
#print axioms GraphProbability.lower_of_join_family
