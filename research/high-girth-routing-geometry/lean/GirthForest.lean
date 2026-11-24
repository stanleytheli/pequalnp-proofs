import ForestRouting
import ShortWalks

namespace SparsePermanent.DirectedGrowth
open SimpleGraph BinaryWords ShortWalks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Two labelled children at each vertex, all followed in one orientation. -/
structure Branches (G : SimpleGraph V) (E : V→V→Prop) where
  next : V→Bool→V
  different : ∀ a,Function.Injective (next a)
  adj : ∀ a b,G.Adj a (next a b)
  arc : ∀ a b,E a (next a b)

namespace Branches
variable {E : V→V→Prop} (T : Branches G E)

def tip (T : Branches G E) : V→Word→V
  | a,[]=>a
  | a,b::w=>T.tip (T.next a b) w

theorem tip_append (a : V) (w z : Word) : T.tip a (w++z)=T.tip (T.tip a w) z := by
  induction w generalizing a with
  | nil=>rfl
  | cons b w ih=>exact ih _

def trace (T : Branches G E) : (a : V)→(w : Word)→G.Walk a (T.tip a w)
  | _,[]=>.nil
  | a,b::w=>.cons (T.adj a b) (T.trace (T.next a b) w)

theorem follows (a : V) (w : Word) : Follows E (T.trace a w) := by
  induction w generalizing a with
  | nil=>exact .nil _
  | cons b w ih=>exact .cons (T.arc _ _) (ih _)

theorem trace_length (a : V) (w : Word) : (T.trace a w).length=w.length := by
  induction w generalizing a with
  | nil=>rfl
  | cons b w ih=>exact congrArg Nat.succ (ih _)

private def decode (T : Branches G E) (a : V) : List V→Word
  | []=>[]
  | y::ys=>decide (y=T.next a true)::T.decode y ys

private theorem decode_trace (a : V) (w : Word) : T.decode a (T.trace a w).support.tail=w := by
  induction w generalizing a with
  | nil=>rfl
  | cons b w ih=>
    have support:= (T.trace (T.next a b) w).cons_tail_support
    change T.decode a (T.trace (T.next a b) w).support=b::w
    rw [←support]
    change _::_ = _::_
    congr 1
    · cases b <;> simp [T.different _ |>.eq_iff]
    · exact ih _

private theorem follows_copy {D : V→V→Prop} {a x y : V} (p : G.Walk a x) (e:x=y) (h:Follows D p) :
    Follows D (p.copy rfl e) := by subst y;exact h

theorem same_support {D : V→V→Prop} (U : Branches G D) (a : V) (w z : Word) {R : ℕ}
    (asym : ∀ ⦃x y⦄,E x y→¬E y x) (asym' : ∀ ⦃x y⦄,D x y→¬D y x)
    (girth : (2*R+1 : ℕ)<G.egirth) (lw:w.length≤R) (lz:z.length≤R)
    (hit:T.tip a w=U.tip a z) : (T.trace a w).support=(U.trace a z).support := by
  let p:=(T.trace a w).copy rfl hit
  have ep:Follows E p:=follows_copy _ hit (T.follows a w)
  have bound:p.length≤R:=by simpa [p,T.trace_length] using lw
  have eq:=ShortWalks.unique asym asym' ep (U.follows a z) bound (by simpa [U.trace_length] using lz) girth
  simpa [p] using congrArg Walk.support eq

theorem inject {a : V} {w z : Word} {R : ℕ} (asym : ∀ ⦃x y⦄,E x y→¬E y x)
    (girth : (2*R+1 : ℕ)<G.egirth) (lw:w.length≤R) (lz:z.length≤R)
    (hit:T.tip a w=T.tip a z) : w=z := by
  have eq:=T.same_support T a w z asym asym girth lw lz hit
  simpa [T.decode_trace] using congrArg (fun xs : List V=>T.decode a xs.tail) eq

theorem opposite (U : Branches G (fun x y=>E y x)) {a : V} {w z : Word} {R : ℕ}
    (asym : ∀ ⦃x y⦄,E x y→¬E y x) (girth : (2*R+1 : ℕ)<G.egirth)
    (positive:0<w.length) (lw:w.length≤R) (lz:z.length≤R) (hit:T.tip a w=U.tip a z) : False := by
  have eq:=T.same_support U a w z asym (fun ⦃_ _⦄ h h'=>asym h h') girth lw lz hit
  cases w with
  | nil=>simp at positive
  | cons b w=>
    cases z with
    | nil=>
      have len:=congrArg List.length eq
      simp [T.trace_length,U.trace_length] at len
    | cons c z=>
      have left:=(T.trace (T.next a b) w).cons_tail_support
      have right:=(U.trace (U.next a c) z).cons_tail_support
      change a::(T.trace (T.next a b) w).support = a::(U.trace (U.next a c) z).support at eq
      replace eq := (List.cons.inj eq).2
      have hfirst := congrArg List.head? eq
      rw [←left,←right] at hfirst
      have e : T.next a b=U.next a c:=Option.some.inj hfirst
      exact asym (T.arc a b) (e ▸ U.arc a c)

theorem too_far {D : V→V→Prop} (U : Branches G D) {a b : V} {w z : Word} {R : ℕ}
    (far:2*R<G.dist a b) (lw:w.length≤R) (lz:z.length≤R) (hit:T.tip a w=U.tip b z) : False := by
  let walk:=((T.trace a w).copy rfl hit).append (U.trace b z).reverse
  have near:=G.dist_le walk
  simp [walk,T.trace_length,U.trace_length] at near
  omega

end Branches

/-- Outgoing and incoming trees around separated centers of a high-girth
orientation, using the two guaranteed neighbors on each side. -/
def Forest.from_girth {E : V→V→Prop} {m R : ℕ} (center : Fin m→V)
    (front : Branches G E) (back : Branches G (fun x y=>E y x))
    (asym : ∀ ⦃x y⦄,E x y→¬E y x) (girth : (2*R+1 : ℕ)<G.egirth)
    (apart : ∀ i j,i≠j→2*R<G.dist (center i) (center j)) :
    Forest (@oriented V E m) R := by
  let arm (b : Bool) : Branches G (fun x y=>if b then E y x else E x y) :=
    match b with | false=>front | true=>back
  refine ⟨fun i w=>(arm i.2).tip (center i.1) w,?_,?_,?_⟩
  · rintro ⟨i,b⟩ u v lu lv e
    cases b
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
    · exact (arm b).too_far (arm c) (apart i j same) lu lv e
  · rintro ⟨i,b⟩ w _ c
    rw [Branches.tip_append]
    exact (arm b).arc _ _

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Branches.inject
#print axioms SparsePermanent.DirectedGrowth.Branches.opposite
#print axioms SparsePermanent.DirectedGrowth.Forest.from_girth
