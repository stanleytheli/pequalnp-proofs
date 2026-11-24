import GenericParameters
import GraphContraction

/-! The complete network specialization, including all nonvanishing
hypotheses, uniform over all fields. -/
namespace SparseAffine
noncomputable section
open scoped BigOperators

abbrev Extension (F : Type*) [Field F] := RatFunc (RatFunc F)

private theorem good_t (F : Type*) [Field F] :
    let t : RatFunc F := RatFunc.X
    t ≠ 0 ∧ 1+t ≠ 0 ∧ cont t 4 ≠ 0 ∧ cont t 5 ≠ 0 ∧ cont t 6 ≠ 0 := by
  exact ⟨RatFunc.X_ne_zero,cont_variable_ne_zero F 1,cont_variable_ne_zero F 4,
    cont_variable_ne_zero F 5,cont_variable_ne_zero F 6⟩

theorem generic_wire (F : Type*) [Field F] (data : Bool) :
    let t : Extension F := RatFunc.C RatFunc.X
    let u : Extension F := RatFunc.X
    let s := if data then 1 else u
    let pins := (activityList t u s).map parameter
    let k := pathScale t u s
    k ≠ 0 ∧ ∀ a b : Bool, bern a pins b = k * wire u s a b := by
  dsimp only
  obtain ⟨ht,hp,h4,h5,h6⟩ := good_t F
  obtain ⟨good,nk⟩ := generic_activities (RatFunc.X : RatFunc F) ht hp h4 h5 h6 data
  refine ⟨nk,?_⟩
  intro a b
  have hC : cont (RatFunc.C (RatFunc.X : RatFunc F)) 5 ≠ 0 := by
    intro he
    apply h5
    apply RatFunc.C_injective
    rw [map_zero]
    have hm : RatFunc.C (cont (RatFunc.X : RatFunc F) 5) =
        cont (RatFunc.C (RatFunc.X : RatFunc F)) 5 := by
      simp [cont]
    rwa [hm]
  have hs : (if data then 1 else (RatFunc.X : Extension F)) ≠ 0 := by
    cases data <;> simp [RatFunc.X_ne_zero]
  exact ten_edge_signature _ _ _ hC RatFunc.X_ne_zero hs a b good

/-- For any seed, the explicit ten-edge parameters specialize the network
to its desired weighted independent-set polynomial times a nonzero constant.
Only leaf data x can vary; in the physical network each appears as 1-x. -/
theorem all_field_specialization (F : Type*) [Field F] {V E L : Type*}
    [Fintype V] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq L]
    (src dst : E → V) (owner : L → V) (positive : ∀ v, rootDegree src dst owner v ≠ 0)
    (c : V → RatFunc F) :
    let t : Extension F := RatFunc.C RatFunc.X
    let u : Extension F := RatFunc.X
    let p := fun v => RatFunc.C (c v)/(u^rootDegree src dst owner v+RatFunc.C (c v))
    let ordinary := (activityList t u u).map parameter
    let leaf := (activityList t u 1).map parameter
    ∃ scalar : Extension F, scalar ≠ 0 ∧ ∀ x : L → Extension F,
      network src dst owner p x (fun _ => ordinary) (fun _ => leaf) =
      scalar * partition src dst (fun v => RatFunc.C (c v)*owned owner x v) := by
  classical
  intro t u p ordinary leaf
  obtain ⟨ko,ho⟩ := generic_wire F false
  obtain ⟨kl,hl⟩ := generic_wire F true
  let k := pathScale t u u
  let h := pathScale t u 1
  have nd (v : V) := root_denom_ne_zero (c v) (rootDegree src dst owner v) (positive v)
  refine ⟨(∏ _ : E, k)*(∏ _ : L, h)*∏ v, (1-p v),?_,?_⟩
  · apply mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ => ko))
      (Finset.prod_ne_zero_iff.mpr (fun _ _ => kl)))
    apply Finset.prod_ne_zero_iff.mpr
    intro v _ he
    have hu : u^rootDegree src dst owner v ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
    have denom : u^rootDegree src dst owner v + RatFunc.C (c v) ≠ 0 := nd v
    have eq : RatFunc.C (c v)/(u^rootDegree src dst owner v + RatFunc.C (c v)) = 1 :=
      (sub_eq_zero.mp he).symm
    have numerator := (div_eq_iff denom).mp eq
    apply hu
    linear_combination -numerator
  · intro x
    exact specialize_network src dst owner u (fun v => RatFunc.C (c v)) x
      (fun _ => ordinary) (fun _ => leaf) (fun _ => k) (fun _ => h)
      (fun _ => ho) (fun _ => hl) nd

end
end SparseAffine
#print axioms SparseAffine.generic_wire
#print axioms SparseAffine.all_field_specialization
