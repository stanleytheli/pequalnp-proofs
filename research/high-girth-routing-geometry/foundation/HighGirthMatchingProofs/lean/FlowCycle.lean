import FlowStep
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace SparsePermanent
open Finset
variable {I : Type} [Fintype I] [DecidableEq I]

def bipAdj (E : I → I → Prop) : I⊕I → I⊕I → Prop
  | .inl x,.inr y => E x y
  | .inr y,.inl x => E x y
  | _,_ => False

/-- The ordinary undirected simple graph with the two disjoint bipartition classes. -/
def bipGraph (E : I → I → Prop) : SimpleGraph (I⊕I) where
  Adj := bipAdj E
  symm := ⟨by rintro (x|x) (y|y) h <;> exact h⟩
  loopless := ⟨by rintro (x|x) h <;> exact h⟩

namespace CycleFlow
variable {E : I→I→Prop}

private def impulse : I⊕I → I⊕I → I→I→ℤ
  | .inl a,.inr b,x,y => if x=a then (if y=b then 1 else 0) else 0
  | .inr b,.inl a,x,y => if x=a then (if y=b then -1 else 0) else 0
  | _,_,_,_ => 0

private theorem row_impulse {u v : I⊕I} (h : (bipGraph E).Adj u v) (x : I) :
    ∑ y, impulse u v x y = (if u=Sum.inl x then 1 else 0) - (if v=Sum.inl x then 1 else 0) := by
  rcases u with a|a <;> rcases v with b|b
  · exact h.elim
  · by_cases e : x=a <;> simp [impulse,e,eq_comm]
  · by_cases e : x=b <;> simp [impulse,e,eq_comm]
  · exact h.elim

private theorem col_impulse {u v : I⊕I} (h : (bipGraph E).Adj u v) (y : I) :
    ∑ x, impulse u v x y = (if v=Sum.inr y then 1 else 0) - (if u=Sum.inr y then 1 else 0) := by
  rcases u with a|a <;> rcases v with b|b
  · exact h.elim
  · by_cases e : y=b <;> simp [impulse,e,eq_comm]
  · by_cases e : y=a <;> simp [impulse,e,eq_comm]
  · exact h.elim

private theorem mass_impulse {u v : I⊕I} (h : (bipGraph E).Adj u v) :
    (∑ x, ∑ y,(impulse u v x y).natAbs)=1 := by
  rcases u with a|a <;> rcases v with b|b
  · exact h.elim
  · simp [impulse,apply_ite Int.natAbs,Finset.sum_ite_irrel]
  · simp [impulse,apply_ite Int.natAbs,Finset.sum_ite_irrel]
  · exact h.elim

private theorem absent_impulse {u v : I⊕I} {x y:I} (absent : s((Sum.inl x : I⊕I),Sum.inr y)≠s(u,v)) :
    impulse u v x y=0 := by
  rcases u with a|a <;> rcases v with b|b
  · rfl
  · by_cases hx : x=a <;> by_cases hy : y=b <;> simp [impulse,hx,hy] <;> exact absent (by simp [hx,hy])
  · by_cases hx : x=b <;> by_cases hy : y=a <;> simp [impulse,hx,hy] <;> exact absent (by simpa [hx,hy] using (Sym2.eq_swap (a:=(Sum.inl b : I⊕I)) (b:=Sum.inr a)))
  · rfl

private def flux : {u v : I⊕I} → (bipGraph E).Walk u v → I→I→ℤ
  | _,_,.nil,_,_ => 0
  | u,_,.cons (v:=v) _ p,x,y => impulse u v x y+flux p x y

private theorem flux_missing {u v : I⊕I} (p : (bipGraph E).Walk u v) (x y : I)
    (h : s((Sum.inl x : I⊕I),Sum.inr y)∉p.edges) : flux p x y=0 := by
  induction p with
  | nil => rfl
  | @cons u v w adj p ih =>
    rw [SimpleGraph.Walk.edges_cons,List.mem_cons,not_or] at h
    change impulse u v x y + flux p x y=0
    rw [absent_impulse h.1,ih h.2,add_zero]

private theorem flux_off {u v : I⊕I} (p : (bipGraph E).Walk u v) (x y : I) (absent : ¬E x y) :
    flux p x y=0 := by
  apply flux_missing
  intro mem
  have edge := p.edges_subset_edgeSet mem
  exact absent ((bipGraph E).mem_edgeSet.mp edge)

private theorem flux_left {u v : I⊕I} (p : (bipGraph E).Walk u v) (x : I) :
    ∑ y,flux p x y=(if u=Sum.inl x then 1 else 0)-(if v=Sum.inl x then 1 else 0) := by
  induction p with
  | nil => simp [flux]
  | @cons u v w adj p ih =>
    simp only [flux,sum_add_distrib,row_impulse adj,ih]
    omega

private theorem flux_right {u v : I⊕I} (p : (bipGraph E).Walk u v) (y : I) :
    ∑ x,flux p x y=(if v=Sum.inr y then 1 else 0)-(if u=Sum.inr y then 1 else 0) := by
  induction p with
  | nil => simp [flux]
  | @cons u v w adj p ih =>
    simp only [flux,sum_add_distrib,col_impulse adj,ih]
    omega

def ofClosedWalk {u : I⊕I} (p : (bipGraph E).Walk u u) : Flow E where
  val := flux p
  leftZero x := by rw [flux_left,sub_self]
  rightZero y := by rw [flux_right,sub_self]
  off := flux_off p

private theorem mass_le {u v : I⊕I} (p : (bipGraph E).Walk u v) :
    (∑ x,∑ y,(flux p x y).natAbs)≤p.length := by
  induction p with
  | nil => simp [flux]
  | @cons u v w adj p ih =>
    change (∑ x,∑ y,(impulse u v x y+flux p x y).natAbs)≤p.length+1
    calc
      _ ≤ ∑ x, ∑ y, ((impulse u v x y).natAbs + (flux p x y).natAbs) :=
        sum_le_sum (fun x _=>sum_le_sum (fun y _=>Int.natAbs_add_le ..))
      _ = 1 + ∑ x,∑ y,(flux p x y).natAbs := by simp only [sum_add_distrib,mass_impulse adj]
      _ ≤ p.length + 1 := by omega

private theorem flow_pos {u : I⊕I} (p : (bipGraph E).Walk u u) (cycle : p.IsCycle) :
    0 < (ofClosedWalk p).mass := by
  have someEdge : ∃ x y,flux p x y≠0 := by
    cases p with
    | nil => exact (cycle.ne_nil rfl).elim
    | @cons _ v _ adj p =>
      have no := (List.nodup_cons.mp (by simpa only [SimpleGraph.Walk.edges_cons] using cycle.edges_nodup)).1
      rcases u with a|a <;> rcases v with b|b
      · exact adj.elim
      · exact ⟨a,b,by simp [flux,impulse,flux_missing p a b no]⟩
      · have rev : s((Sum.inl b : I⊕I),Sum.inr a)∉p.edges := by rwa [Sym2.eq_swap]
        exact ⟨b,a,by simp [flux,impulse,flux_missing p b a rev]⟩
      · exact adj.elim
  obtain ⟨x,y,live⟩:=someEdge
  have a := single_le_sum (f:=fun j=>(flux p x j).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ y)
  have b := single_le_sum (f:=fun i=>∑ j,(flux p i j).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ x)
  exact (Int.natAbs_pos.mpr live).trans_le (a.trans b)

/-- From a lower bound on every nonzero integral circulation to Mathlib's
ordinary shortest-cycle length, taking value infinity for forests. -/
theorem le_egirth {g : ℕ} (lower : ∀ Z : Flow E, 0<Z.mass → g≤Z.mass) :
    (g : ℕ∞)≤(bipGraph E).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro a p hp
  exact_mod_cast (lower (ofClosedWalk p) (flow_pos p hp)).trans (mass_le p)

end CycleFlow
end SparsePermanent
#print axioms SparsePermanent.CycleFlow.le_egirth
