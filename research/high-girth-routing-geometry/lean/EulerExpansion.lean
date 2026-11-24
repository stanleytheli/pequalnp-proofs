import DirectedGrowth

namespace SparsePermanent.DirectedGrowth
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def weight (E : V→V→Prop) (x y : V) : ℕ := by classical exact if E x y then 1 else 0
noncomputable def cross (E : V→V→Prop) (A B : Finset V) := ∑ x∈A,∑ y∈B,weight E x y

private theorem partition (E : V→V→Prop) (S : Finset V) :
    cross E S S+cross E S Sᶜ=∑ x∈S,∑y,weight E x y := by
  simp only [cross,←sum_add_distrib]
  exact sum_congr rfl (fun x _=>sum_add_sum_compl _ _)

private theorem transpose (E : V→V→Prop) (A B : Finset V) :
    cross (fun x y=>E y x) B A=cross E A B := by
  unfold cross
  rw [sum_comm]
  rfl

/-- A directed graph with equal incoming and outgoing degree at each vertex
has the same number of edges crossing every cut in either direction. -/
theorem euler_balanced (E : V→V→Prop) (S : Finset V)
    (balanced : ∀x,(∑ y,weight E x y)=∑y,weight E y x) :
    cross E S Sᶜ=cross E Sᶜ S := by
  have f:=partition E S
  have b:=partition (fun x y=>E y x) S
  rw [transpose E S S,transpose E (Sᶜ) S] at b
  have sides : (∑ x∈S,∑ y,weight E x y)=∑ x∈S,∑ y,weight (fun u v=>E v u) x y :=
    sum_congr rfl (fun x _=>balanced x)
  omega

/-- A bound d on incoming degree divides the outward edge boundary into at
least (boundary edges)/d distinct outside vertices. -/
theorem cross_le_boundary (E : V→V→Prop) (S : Finset V) {d : ℕ}
    (incoming : ∀y,(∑ x,weight E x y)≤d) : cross E S Sᶜ≤d*(boundary E S).card := by
  classical
  have subtotal (y : V) : (∑ x∈S,weight E x y)≤d :=
    (sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)).trans (incoming _)
  have sub : boundary E S ⊆ Sᶜ := by
    intro y hy
    exact mem_compl.mpr (mem_filter.mp hy).2.1
  calc
    _ = ∑ y∈Sᶜ,∑ x∈S,weight E x y := sum_comm
    _ ≤ ∑ y∈Sᶜ,if y∈boundary E S then d else 0 := by
      apply sum_le_sum
      intro y hy
      by_cases hit : y∈boundary E S
      · simpa [hit] using subtotal y
      · rw [if_neg hit]
        apply Nat.le_zero.mpr
        apply sum_eq_zero
        intro x hx
        have no : ¬E x y:=fun h=>hit (mem_filter.mpr ⟨mem_univ _,mem_compl.mp hy,x,hx,h⟩)
        simp [weight,no]
    _ = (boundary E S).card*d := by
      rw [←sum_filter]
      have eq : Sᶜ.filter (·∈boundary E S)=boundary E S := by
        ext y; simp only [mem_filter];exact and_iff_right_of_imp (fun h=>sub h)
      simp [eq]
    _ = _ := Nat.mul_comm _ _

/-- Undirected edge expansion on all unions of matching pairs gives both
directions of vertex expansion after contracting those pairs. The hypothesis
2|S| ≤ K·(out+in) uses the original two physical vertices per pair. -/
theorem expands_contraction (E : V→V→Prop) (K d : ℕ)
    (balanced : ∀x,(∑ y,weight E x y)=∑y,weight E y x)
    (incoming : ∀y,(∑ x,weight E x y)≤d)
    (cut : ∀S : Finset V,2*S.card≤Fintype.card V→
      2*S.card≤K*(cross E S Sᶜ+cross E Sᶜ S)) :
    Expands E (K*d) ∧ Expands (fun x y=>E y x) (K*d) := by
  have lower (S : Finset V) (h:2*S.card≤Fintype.card V) : S.card≤K*cross E S Sᶜ := by
    have z:=cut S h
    rw [←euler_balanced E S balanced,Nat.mul_add] at z
    omega
  constructor
  · intro S small
    exact (lower S small).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K (cross_le_boundary E S incoming))
  · intro S small
    have x:=lower S small
    have eq:=euler_balanced E S balanced
    rw [eq,←transpose E Sᶜ S] at x
    apply x.trans
    have bk:=cross_le_boundary (fun x y=>E y x) S (d:=d) (fun y=>(balanced y).le.trans (incoming y))
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K bk

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.expands_contraction
