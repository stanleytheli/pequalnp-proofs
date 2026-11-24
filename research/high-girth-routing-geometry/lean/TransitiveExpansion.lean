import OrbitCounting
import DirectedGrowth
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace SparsePermanent.OrbitCounting
open Finset SimpleGraph DirectedGrowth
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]

private def indicatorAt (S : Finset V) (x : V) : ℕ:=if x∈S then 1 else 0

private theorem exits (G : SimpleGraph V) (S : Finset V) (f : V→V)
    (auto : ∀⦃x y⦄,G.Adj x y→G.Adj (f x) (f y)) {a b : V} (p : G.Walk a b)
    (start : f a∈S) (finish : f b∉S) : ∃x∈p.support,f x∈boundary G.Adj S := by
  classical
  induction p with
  | nil=>exact (finish start).elim
  | @cons a v b edge q ih=>
    by_cases inside:f v∈S
    · obtain ⟨x,hx,h⟩:=ih inside finish
      exact ⟨x,List.mem_cons_of_mem _ hx,h⟩
    · exact ⟨v,List.mem_cons_of_mem _ q.start_mem_support,mem_filter.mpr ⟨mem_univ _,inside,f a,start,auto edge⟩⟩

/-- A transitive averaging bound with an absolute constant, independent of
the group size or the number of vertices. A path from a single root to every
vertex of length at most d suffices. -/
theorem expands (G : SimpleGraph V) (act : J→Equiv.Perm V)
    (aut : ∀g : J,∀⦃x y⦄,G.Adj x y→G.Adj (act g x) (act g y)) (c : ℕ) (positive : 0<c)
    (uniform : ∀x y,(univ.filter (fun g=>act g x=y)).card=c)
    (a : V) (d : ℕ) (short : ∀x,∃p : G.Walk a x,p.length≤d) :
    Expands G.Adj (2*(d+1)) := by
  classical
  choose p len using short
  let W (x:V):=(p x).support.toFinset
  have size (x : V) : (W x).card≤d+1 := by
    calc
      _ ≤ (p x).support.length := (p x).support.toFinset_card_le
      _ = _ := (p x).length_support
      _ ≤ _ := Nat.add_le_add_right (len x) _
  intro S small
  let T:=boundary G.Adj S
  have mark (x : V) (U : Finset V) : (∑g : J,indicatorAt U (act g x))=U.card*c :=
    indicator act uniform x U
  have mass (g:J) : (∑x : V,indicatorAt Sᶜ (act g x))=Sᶜ.card := by
    rw [Equiv.sum_comp (act g) (indicatorAt Sᶜ)]
    change (∑x : V,if x∈Sᶜ then 1 else 0)=Sᶜ.card
    rw [←card_filter]
    apply congrArg Finset.card
    ext x
    simp
  have low : (∑ x : V,∑ g : J, indicatorAt S (act g a)*indicatorAt Sᶜ (act g x))=
      S.card*c*Sᶜ.card := by
    rw [sum_comm]
    simp only [←mul_sum,mass,←sum_mul,mark]
  have one (x : V) (g : J) : indicatorAt S (act g a)*indicatorAt Sᶜ (act g x) ≤
      ∑z∈W x,indicatorAt T (act g z) := by
    by_cases ha : act g a∈S
    · by_cases hx : act g x∈S
      · simp [indicatorAt,ha,hx]
      · obtain ⟨z,hz,reach⟩:=exits G S (act g) (aut g) (p x) ha hx
        have h:=single_le_sum (f:=fun z=>indicatorAt T (act g z)) (fun z _=>Nat.zero_le _) (show z∈W x from List.mem_toFinset.mpr hz)
        simpa [indicatorAt,ha,hx,show act g z∈T from reach] using h
    · simp [indicatorAt,ha]
  have high (x : V) : (∑g : J,∑z∈W x,indicatorAt T (act g z)) ≤ (d+1)*(T.card*c) := by
    rw [sum_comm]
    simp only [mark,sum_const,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (size x)
  have both : S.card*c*Sᶜ.card ≤ Fintype.card V*((d+1)*(T.card*c)) := by
    rw [←low]
    calc
      _ ≤ ∑x : V,∑g : J,∑z∈W x,indicatorAt T (act g z) := sum_le_sum (fun x _=>sum_le_sum (fun g _=>one x g))
      _ ≤ ∑_x : V,(d+1)*(T.card*c) := sum_le_sum (fun x _=>high x)
      _ = _ := by simp
  have cancel : (S.card*Sᶜ.card)*c ≤ (Fintype.card V*((d+1)*T.card))*c := by
    convert both using 1 <;> ring
  have h:=Nat.le_of_mul_le_mul_right cancel positive
  have npos : 0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨a⟩
  have comp:=card_compl S
  have sBound : Fintype.card V≤2*Sᶜ.card := by omega
  have multi : S.card*Fintype.card V≤(2*(d+1)*T.card)*Fintype.card V := by
    calc
      _ ≤ S.card*(2*Sᶜ.card) := Nat.mul_le_mul_left _ sBound
      _ = 2*(S.card*Sᶜ.card) := by ring
      _ ≤ 2*(Fintype.card V*((d+1)*T.card)) := Nat.mul_le_mul_left _ h
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right multi npos

end SparsePermanent.OrbitCounting
#print axioms SparsePermanent.OrbitCounting.expands
