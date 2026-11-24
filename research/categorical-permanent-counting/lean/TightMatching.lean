import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! A bipartite multigraph split at N(S) with |N(S)|=|S|+1. Separate types
for individual edges preserve parallel edge identities through contractions.
A matching of the full graph is equivalent to two contracted perfect
matchings choosing the same crossing edge. -/
namespace PositivePermanent.TightMatching
open Finset

structure Cut (A B L R I J C : Type*) where
  sourceI : I→A
  targetI : I→B
  sourceJ : J→L
  targetJ : J→R
  sourceC : C→L
  targetC : C→B

namespace Cut
variable {A B L R I J C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq L] [DecidableEq R]
    [DecidableEq C] (G : Cut A B L R I J C)

def degree {E V : Type*} [DecidableEq V] (s : Finset E) (endpoint : E→V) (v : V) : ℕ :=
  (s.filter (fun e=>endpoint e=v)).card

structure Full where
  crossings : Finset C
  inner : Finset I
  outer : Finset J
  innerLeft : ∀a,degree inner G.sourceI a=1
  innerRight : ∀b,degree inner G.targetI b+degree crossings G.targetC b=1
  outerLeft : ∀l,degree outer G.sourceJ l+degree crossings G.sourceC l=1
  outerRight : ∀r,degree outer G.targetJ r=1

/-- The dummy left vertex is matched through `port`; every true vertex has
degree exactly one. -/
structure Inner where
  port : C
  chosen : Finset I
  left : ∀a,degree chosen G.sourceI a=1
  right : ∀b,degree chosen G.targetI b+(if G.targetC port=b then 1 else 0)=1

/-- The dummy right vertex is matched through `port`. -/
structure Outer where
  port : C
  chosen : Finset J
  left : ∀l,degree chosen G.sourceJ l+(if G.sourceC port=l then 1 else 0)=1
  right : ∀r,degree chosen G.targetJ r=1

def Compatible := {p:G.Inner×G.Outer // p.1.port=p.2.port}

private theorem sum_degree {E V : Type*} [Fintype V] [DecidableEq V] (s : Finset E) (endpoint : E→V) :
    (∑v,degree s endpoint v)=s.card := by
  exact (card_eq_sum_card_fiberwise (t:=univ) (f:=endpoint) (fun _ _=>mem_univ _)).symm

private theorem one_degree {E V : Type*} [DecidableEq V] (endpoint : E→V) (e:E) (v:V) :
    degree {e} endpoint v=if endpoint e=v then 1 else 0 := by
  classical
  by_cases h:endpoint e=v <;> simp [degree,filter_singleton,h]

variable [Fintype A] [Fintype B]

theorem crossings_one (size:Fintype.card B=Fintype.card A+1) (m:G.Full) : m.crossings.card=1 := by
  have ai : m.inner.card=Fintype.card A := calc
    _ = ∑a,degree m.inner G.sourceI a := (sum_degree ..).symm
    _ = ∑_a:A,1 := sum_congr rfl (fun a _=>m.innerLeft a)
    _ = _ := by simp
  have br : m.inner.card+m.crossings.card=Fintype.card B := calc
    _ = ∑b,(degree m.inner G.targetI b+degree m.crossings G.targetC b) := by rw [sum_add_distrib,sum_degree,sum_degree]
    _ = ∑_b:B,1 := sum_congr rfl (fun b _=>m.innerRight b)
    _ = _ := by simp
  omega

private noncomputable def port (size:Fintype.card B=Fintype.card A+1) (m:G.Full) : C:=
  (card_eq_one.mp (G.crossings_one size m)).choose

private theorem port_exact (size:Fintype.card B=Fintype.card A+1) (m:G.Full) :
    m.crossings={G.port size m} := (card_eq_one.mp (G.crossings_one size m)).choose_spec

noncomputable def split (size:Fintype.card B=Fintype.card A+1) (m:G.Full) : G.Compatible := by
  let e:=G.port size m
  have eq:m.crossings={e}:=G.port_exact size m
  let a : G.Inner := ⟨e,m.inner,m.innerLeft,fun b=>by simpa only [eq,one_degree] using m.innerRight b⟩
  let b : G.Outer := ⟨e,m.outer,fun l=>by simpa only [eq,one_degree] using m.outerLeft l,m.outerRight⟩
  exact ⟨(a,b),rfl⟩

/-- Two component matchings using the same port glue without a choice. -/
def glue (p:G.Compatible) : G.Full where
  crossings:={p.val.1.port}
  inner:=p.val.1.chosen
  outer:=p.val.2.chosen
  innerLeft:=p.val.1.left
  innerRight:=fun b=>by rw [one_degree];exact p.val.1.right b
  outerLeft:=fun l=>by rw [one_degree,p.prop];exact p.val.2.left l
  outerRight:=p.val.2.right

private theorem Full.eq {p q:G.Full} (a:p.crossings=q.crossings) (b:p.inner=q.inner) (c:p.outer=q.outer) : p=q := by
  cases p;cases q;simp_all

private theorem Inner.eq {p q:G.Inner} (a:p.port=q.port) (b:p.chosen=q.chosen) : p=q := by
  cases p;cases q;simp_all

private theorem Outer.eq {p q:G.Outer} (a:p.port=q.port) (b:p.chosen=q.chosen) : p=q := by
  cases p;cases q;simp_all

/-- Exact tight-cut matching bijection, with its crossing edge preserved
as one individual edge ID in each factor. -/
noncomputable def matchingEquiv (size:Fintype.card B=Fintype.card A+1) : G.Full ≃ G.Compatible where
  toFun:=G.split size
  invFun:=G.glue
  left_inv:=fun m=>Full.eq G (G.port_exact size m).symm rfl rfl
  right_inv:=by
    intro p
    have eq:G.port size (G.glue p)=p.val.1.port := by
      apply Finset.singleton_injective
      exact (G.port_exact size (G.glue p)).symm
    apply Subtype.ext
    exact Prod.ext (Inner.eq G eq rfl) (Outer.eq G (eq.trans p.prop) rfl)

end Cut
end PositivePermanent.TightMatching
#print axioms PositivePermanent.TightMatching.Cut.crossings_one
#print axioms PositivePermanent.TightMatching.Cut.matchingEquiv
