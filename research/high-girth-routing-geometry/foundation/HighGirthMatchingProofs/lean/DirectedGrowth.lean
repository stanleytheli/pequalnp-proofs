import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace SparsePermanent.DirectedGrowth
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def boundary (E : V→V→Prop) (S : Finset V) : Finset V := by
  classical exact univ.filter (fun y=>y∉S ∧ ∃ x∈S,E x y)

/-- A denominator k in the directed small-set vertex-expansion bound. -/
def Expands (E : V→V→Prop) (k : ℕ) := ∀ S : Finset V,
  2*S.card≤Fintype.card V → S.card≤k*(boundary E S).card

noncomputable def next (E : V→V→Prop) (F S : Finset V) := S ∪ (boundary E S \ F)
noncomputable def ball (E : V→V→Prop) (F S : Finset V) : ℕ→Finset V
  | 0=>S
  | t+1=>next E F (ball E F S t)

private theorem next_card (E : V→V→Prop) (F S : Finset V) :
    (next E F S).card=S.card+(boundary E S \ F).card := by
  classical
  apply card_union_of_disjoint
  apply disjoint_left.mpr
  intro x hx h
  exact (mem_filter.mp (show x∈univ.filter (fun y=>y∉S ∧ ∃ z∈S,E z y) from (mem_sdiff.mp h).1)).2.1 hx

private theorem inflation (E : V→V→Prop) (F S : Finset V) : Monotone (fun t=>(ball E F S t).card) := by
  apply monotone_nat_of_le_succ
  intro i
  exact card_le_card (subset_union_left : ball E F S i⊆next E F (ball E F S i))

private theorem block (E : V→V→Prop) (F S : Finset V) {k : ℕ} (hk : 0<k) (exp : Expands E k)
    (safe : 2*k*F.card≤S.card) (small : 2*(ball E F S (2*k)).card≤Fintype.card V) :
    2*S.card≤(ball E F S (2*k)).card := by
  let B:=ball E F S
  have mono:=inflation E F S
  have size (t : ℕ) : S.card≤(B t).card := mono (Nat.zero_le t)
  have advance (t : ℕ) (ht : t≤2*k) : S.card+2*k*(B t).card≤2*k*(B (t+1)).card := by
    have st : 2*(B t).card≤Fintype.card V := (Nat.mul_le_mul_left 2 (mono ht)).trans small
    have wide:=exp (B t) st
    have discarded : (boundary E (B t)).card≤(boundary E (B t)\F).card+F.card := by
      calc
        _ ≤ ((boundary E (B t)\F)∪F).card := card_le_card (by intro x hx; by_cases xf:x∈F <;> simp [hx,xf])
        _ ≤ _ := card_union_le ..
    have twice: 2*(B t).card≤2*k*(boundary E (B t)\F).card+2*k*F.card := by
      have s:=Nat.mul_le_mul_left (2*k) discarded
      rw [Nat.mul_add] at s
      exact (show 2*(B t).card≤2*k*(boundary E (B t)).card by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 wide).trans s
    change _≤2*k*(next E F (B t)).card
    rw [next_card,Nat.mul_add]
    have lower:=size t
    omega
  have totals (t : ℕ) (ht:t≤2*k) : 2*k*S.card+t*S.card≤2*k*(B t).card := by
    induction t with
    | zero=>simp [B,ball]
    | succ t ih =>
      have h:=advance t (by omega)
      have prev:=ih (by omega)
      rw [Nat.succ_mul t S.card]
      omega
  have total:=totals (2*k) le_rfl
  have conv : 2*k*(2*S.card)≤2*k*(B (2*k)).card := by
    rw [show 2*S.card=S.card+S.card by omega,Nat.mul_add]
    exact total
  exact Nat.le_of_mul_le_mul_left conv (by positivity)

private theorem ball_add (E : V→V→Prop) (F S : Finset V) (t r : ℕ) :
    ball E F S (t+r)=ball E F (ball E F S t) r := by
  induction r with
  | zero =>rfl
  | succ r ih=>exact congrArg (next E F) ih

/-- After 2k(log₂ n+1) rounds the surviving ball has over half the vertices.
The assumptions permit removal of any forbidden set of the indicated size. -/
theorem many (E : V→V→Prop) (F S : Finset V) {k : ℕ} (hk : 0<k) (exp : Expands E k)
    (safe : 2*k*F.card≤S.card) (start : 0<S.card) :
    Fintype.card V<2*(ball E F S ((2*k)*(Nat.log 2 (Fintype.card V)+1))).card := by
  by_contra! small
  let T:=Nat.log 2 (Fintype.card V)+1
  have mono:=inflation E F S
  have iter (h : ℕ) (ht:h≤T) : 2^h≤(ball E F S ((2*k)*h)).card := by
    induction h with
    | zero => simpa [ball] using start
    | succ h ih =>
      have prev:=ih (by omega)
      let S':=ball E F S (2*k*h)
      have initial : S.card≤S'.card := mono (Nat.zero_le _)
      have small' : 2*(ball E F S' (2*k)).card≤Fintype.card V := by
        rw [←ball_add]
        have le : 2*k*h+2*k≤2*k*T := by rw [←Nat.mul_succ]; exact Nat.mul_le_mul_left _ ht
        exact (Nat.mul_le_mul_left 2 (mono le)).trans small
      have doubled := block E F S' hk exp (safe.trans initial) small'
      rw [Nat.mul_succ,ball_add,pow_succ]
      change _≤(ball E F S' (2*k)).card
      rw [Nat.mul_comm (2^h) 2]
      exact (Nat.mul_le_mul_left 2 prev).trans doubled
  have lower:=iter T le_rfl
  have cap:=card_le_univ (ball E F S (2*k*T))
  have strict:=Nat.lt_pow_succ_log_self (by decide : 1<2) (Fintype.card V)
  change Fintype.card V<2^T at strict
  omega

/-- A directed walk records its exact length, every internal vertex and both
endpoints avoid F. -/
inductive Route (E : V→V→Prop) (F : Finset V) : V→V→ℕ→Prop
  | nil {a : V} (safe : a∉F) : Route E F a a 0
  | snoc {a b c : V} {t : ℕ} (w : Route E F a b t) (edge : E b c) (safe : c∉F) : Route E F a c (t+1)

theorem Route.trans {E : V→V→Prop} {F : Finset V} {a b c : V} {i j : ℕ}
    (l : Route E F a b i) (r : Route E F b c j) : Route E F a c (i+j) := by
  induction r with
  | nil=>exact l
  | snoc _ edge safe ih=>exact .snoc ih edge safe

theorem Route.start {E : V→V→Prop} {F : Finset V} {a b : V} {i : ℕ}
    (l : Route E F a b i) : a∉F := by
  induction l with
  | nil safe=>exact safe
  | snoc _ _ _ ih=>exact ih

theorem Route.reverse {E : V→V→Prop} {F : Finset V} {a b : V} {i : ℕ}
    (l : Route E F a b i) : Route (fun x y=>E y x) F b a i := by
  induction l with
  | nil safe=>exact .nil safe
  | @snoc b c i w edge safe ih=>
    have bs : b∉F:=ih.start
    have step : Route (fun x y=>E y x) F c b 1 := .snoc (.nil safe) edge bs
    simpa [Nat.add_comm] using step.trans ih

private theorem route_of_mem (E : V→V→Prop) (F S : Finset V) (clean : Disjoint S F) (t : ℕ)
    {b : V} (hit : b∈ball E F S t) : ∃ a∈S, ∃ j≤t,Route E F a b j := by
  classical
  induction t generalizing b with
  | zero=>exact ⟨b,hit,0,le_rfl,.nil (disjoint_left.mp clean hit)⟩
  | succ t ih=>
    rcases mem_union.mp hit with old|new
    · obtain ⟨a,ha,j,hj,w⟩:=ih old
      exact ⟨a,ha,j,by omega,w⟩
    · obtain ⟨inside,bf⟩:=mem_sdiff.mp new
      obtain ⟨_,z,hz,edge⟩:=(mem_filter.mp inside).2
      obtain ⟨a,ha,j,hj,w⟩:=ih hz
      exact ⟨a,ha,j+1,by omega,.snoc w edge bf⟩

/-- Robust directed routing from two large leaf sets. -/
theorem connect (E : V→V→Prop) (F A B : Finset V) {k : ℕ} (hk : 0<k)
    (outE : Expands E k) (inE : Expands (fun x y=>E y x) k)
    (asize : 2*k*F.card≤A.card) (bsize : 2*k*F.card≤B.card)
    (apos : 0<A.card) (bpos : 0<B.card) (af : Disjoint A F) (bf : Disjoint B F) :
    ∃ a∈A, ∃ b∈B, ∃ t≤4*k*(Nat.log 2 (Fintype.card V)+1),Route E F a b t := by
  classical
  let h:=2*k*(Nat.log 2 (Fintype.card V)+1)
  let X:=ball E F A h
  let Y:=ball (fun x y=>E y x) F B h
  have xl : Fintype.card V<2*X.card :=many E F A hk outE asize apos
  have yl : Fintype.card V<2*Y.card :=many _ F B hk inE bsize bpos
  have non : ¬Disjoint X Y := by
    intro dis
    have un:=card_le_univ (X∪Y)
    rw [card_union_of_disjoint dis] at un
    omega
  obtain ⟨z,hx,hy⟩:=not_disjoint_iff.mp non
  obtain ⟨a,ha,i,hi,aw⟩:=route_of_mem E F A af h hx
  obtain ⟨b,hb,j,hj,bw⟩:=route_of_mem (fun x y=>E y x) F B bf h hy
  refine ⟨a,ha,b,hb,i+j,?_,aw.trans bw.reverse⟩
  calc
    _ ≤ h+h := Nat.add_le_add hi hj
    _ = _ := by dsimp [h];ring

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.connect
