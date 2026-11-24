import DirectedPacking
import ResourceBounds

namespace SparsePermanent.DirectedGrowth
open Finset BinaryWords SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {E : V→V→Prop}

private theorem tip_route {D : V→V→Prop} (T : Branches G D) (x : V) (w : Word) :
    Route D ∅ x (T.tip x w) w.length := by
  induction w generalizing x with
  | nil=>exact .nil (by simp)
  | cons b w ih=>
    have step : Route D ∅ x (T.next x b) 1 := .snoc (.nil (by simp)) (T.arc _ _) (by simp)
    simpa [Nat.add_comm,Branches.tip] using step.trans (ih (T.next x b))

/-- Binary trees separated by directed balls. This permits center packing
using two-neighbor growth in each direction. -/
def Forest.from_boxes {m R : ℕ} (center : Fin m→V) (front : Branches G E)
    (back : Branches G (fun x y=>E y x)) (asym : ∀ ⦃x y⦄,E x y→¬E y x)
    (girth : (2*R+1 : ℕ)<G.egirth)
    (apart : ∀i j,i≠j→Disjoint (twoWays E R (center i)) (twoWays E R (center j))) :
    Forest (@oriented V E m) R := by
  let arm (b : Bool) : Branches G (fun x y=>if b then E y x else E x y) :=
    match b with | false=>front | true=>back
  have inside (i : Fin m) (b : Bool) (w : Word) (len:w.length≤R) :
      (arm b).tip (center i) w∈twoWays E R (center i) := by
    classical
    cases b
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_univ _,w.length,len,tip_route front _ _⟩
    · apply mem_union_right
      exact mem_filter.mpr ⟨mem_univ _,w.length,len,tip_route back _ _⟩
  refine ⟨fun i w=>(arm i.2).tip (center i.1) w,?_,?_,?_⟩
  · rintro ⟨i,b⟩ u v lu lv e;cases b
    · exact front.inject asym girth lu lv e
    · exact back.inject (fun ⦃_ _⦄ h h'=>asym h h') girth lu lv e
  · rintro ⟨i,b⟩ ⟨j,c⟩ ne u v pos lu lv e
    by_cases same : i=j
    · subst j
      cases b <;> cases c
      · exact ne rfl
      · exact front.opposite back asym girth pos lu lv e
      · exact back.opposite front (fun ⦃_ _⦄ h h'=>asym h h') girth pos lu lv e
      · exact ne rfl
    · exact Finset.disjoint_left.mp (apart i j same) (inside i b u lu) (e ▸ inside j c v lv)
  · rintro ⟨i,b⟩ w _ c
    rw [Branches.tip_append]
    exact (arm b).arc _ _

namespace Forest

/-- Exact finite capacity for arbitrary reserve depth s. It suffices to
allocate m²(M+1+18k) groups, where M is the maximum route length. -/
theorem tight_pairs {m R l s k M : ℕ} (T : Forest (@oriented V E m) R)
    (width : m≤2^l) (size : 2^l≤2*m) (lp : 0<l) (sp : 0<s) (depth : l+2*s≤R)
    (hk : 0<k) (fwd : Expands E k) (bwd : Expands (fun x y=>E y x) k)
    (time : M=4*s+4*k*(Nat.log 2 (Fintype.card V)+1))
    (room : m^2*(M+1+18*k)≤2^s) :
    ∃U,Packed E (T.core (l+s)) (2^s) (2^s) (2*s) M (T.demands width sp depth) U := by
  let S:=2^s
  let B:=m^2*(M+1)
  have mm:0<m:=by
    have pos:0<2^l:=by positivity
    omega
  have m2:1≤m^2:=pow_pos mm _
  have core:(T.core (l+s)).card≤8*m^2*S := by
    have c:=T.core_card (l+s)
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,pow_succ,pow_add] at c
    calc
      _ ≤ m*2*(2^l*S*2) := c
      _ ≤ m*2*((2*m)*S*2) := by gcongr
      _ = _ := by ring
  have spare : B+18*k*m^2≤S := by convert room using 1 <;> dsimp [B,S] <;> ring
  have cap : 2*k*((T.core (l+s)).card+B)≤(S-B)*S := by
    have coarse:B≤m^2*S:=calc
      _ ≤ S := by omega
      _ = 1*S := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ m2
    calc
      _ ≤ 2*k*(8*m^2*S+m^2*S) := Nat.mul_le_mul_left _ (Nat.add_le_add core coarse)
      _ = (18*k*m^2)*S := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have positive : 0<(S-B)*S := by
    have nonempty : 0<18*k*m^2:=by positivity
    have : 0<S-B:=by omega
    exact Nat.mul_pos this (pow_pos (by decide) _)
  exact T.pack_pairs width sp depth lp hk fwd bwd time rfl cap positive

end Forest
end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Forest.from_boxes
#print axioms SparsePermanent.DirectedGrowth.Forest.tight_pairs
