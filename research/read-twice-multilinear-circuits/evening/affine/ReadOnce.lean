import Mathlib

/-! Exact probabilities of read-once formulas over independent inputs, as
polynomial identities over every commutative ring. The product and complement
rules yield a linear arithmetic circuit by traversing the formula tree. -/
namespace ReadOnce
noncomputable section
open scoped BigOperators

def bernoulli {K : Type*} [CommRing K] (p : K) (b : Bool) : K := if b then p else 1-p

def indicator {K : Type*} [CommRing K] (b : Bool) : K := if b then 1 else 0

def weight {V K : Type*} [Fintype V] [CommRing K] (p : V → K) (s : V → Bool) : K :=
  ∏ v, bernoulli (p v) (s v)

def expectation {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K]
    (p : V → K) (eval : (V → Bool) → Bool) : K :=
  ∑ s, weight p s * indicator (eval s)

theorem weight_total {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K] (p : V → K) :
    (∑ s, weight p s) = 1 := by
  unfold weight
  rw [← Fintype.prod_sum (fun v b => bernoulli (p v) b)]
  simp [Fintype.sum_bool,bernoulli]

theorem complement {V K : Type*} [Fintype V] [DecidableEq V] [CommRing K] (p : V → K)
    (a : (V → Bool) → Bool) : expectation p (fun s => !(a s)) = 1 - expectation p a := by
  unfold expectation
  rw [← weight_total p,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  dsimp only
  cases h : a s <;> simp [h,indicator]

theorem conjunction {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [CommRing K] (p : A ⊕ B → K) (f : (A → Bool) → Bool) (g : (B → Bool) → Bool) :
    expectation p (fun s => f (s ∘ Sum.inl) && g (s ∘ Sum.inr)) =
      expectation (p ∘ Sum.inl) f * expectation (p ∘ Sum.inr) g := by
  classical
  let E := Equiv.sumArrowEquivProdArrow A B Bool
  unfold expectation
  rw [← E.symm.sum_comp,Fintype.sum_prod_type,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  have hx : E.symm (x,y) ∘ Sum.inl = x := rfl
  have hy : E.symm (x,y) ∘ Sum.inr = y := rfl
  have hm : weight p (E.symm (x,y)) = weight (p ∘ Sum.inl) x * weight (p ∘ Sum.inr) y := by
    unfold weight
    rw [Fintype.prod_sum_type]
    rfl
  dsimp only
  rw [hx,hy,hm]
  cases f x <;> cases g y <;> simp [indicator]

/-- Leaves in opposite branches belong to disjoint types. This enforces the
read-once condition intrinsically. -/
inductive Tree
  | input
  | neg (a : Tree)
  | both (a b : Tree)
  | either (a b : Tree)
  deriving DecidableEq

@[reducible] def Leaf : Tree → Type
  | .input => PUnit
  | .neg a => Leaf a
  | .both a b | .either a b => Leaf a ⊕ Leaf b

@[reducible] instance leafFinite : (t : Tree) → Fintype (Leaf t)
  | .input => inferInstanceAs (Fintype PUnit)
  | .neg a => leafFinite a
  | .both a b | .either a b => by
    letI := leafFinite a
    letI := leafFinite b
    exact inferInstanceAs (Fintype (Leaf a ⊕ Leaf b))

@[reducible] instance leafEq : (t : Tree) → DecidableEq (Leaf t)
  | .input => inferInstanceAs (DecidableEq PUnit)
  | .neg a => leafEq a
  | .both a b | .either a b => by
    letI := leafEq a
    letI := leafEq b
    exact inferInstanceAs (DecidableEq (Leaf a ⊕ Leaf b))

def evaluate : (t : Tree) → (Leaf t → Bool) → Bool
  | .input,s => s PUnit.unit
  | .neg a,s => !(evaluate a s)
  | .both a b,s => evaluate a (s ∘ Sum.inl) && evaluate b (s ∘ Sum.inr)
  | .either a b,s => evaluate a (s ∘ Sum.inl) || evaluate b (s ∘ Sum.inr)

/-- Uses one multiplication for AND and at most three subtractions and one
multiplication for OR. The definition works directly in a polynomial ring. -/
def arithmetic {K : Type*} [CommRing K] : (t : Tree) → (Leaf t → K) → K
  | .input,p => p PUnit.unit
  | .neg a,p => 1-arithmetic a p
  | .both a b,p => arithmetic a (p ∘ Sum.inl) * arithmetic b (p ∘ Sum.inr)
  | .either a b,p => 1-(1-arithmetic a (p ∘ Sum.inl))*(1-arithmetic b (p ∘ Sum.inr))

theorem disjunction {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [CommRing K] (p : A ⊕ B → K) (f : (A → Bool) → Bool) (g : (B → Bool) → Bool) :
    expectation p (fun s => f (s ∘ Sum.inl) || g (s ∘ Sum.inr)) =
     1-(1-expectation (p ∘ Sum.inl) f)*(1-expectation (p ∘ Sum.inr) g) := by
  have hf (s : A ⊕ B → Bool) :
      (f (s ∘ Sum.inl) || g (s ∘ Sum.inr)) = !(!(f (s ∘ Sum.inl)) && !(g (s ∘ Sum.inr))) := by
    cases f (s ∘ Sum.inl) <;> cases g (s ∘ Sum.inr) <;> decide
  rw [show (fun s => f (s ∘ Sum.inl) || g (s ∘ Sum.inr)) =
      (fun s => !(!(f (s ∘ Sum.inl)) && !(g (s ∘ Sum.inr)))) from funext hf]
  rw [complement,conjunction p (fun s => !(f s)) (fun s => !(g s)),complement,complement]

theorem read_once_exact {K : Type*} [CommRing K] (t : Tree) (p : Leaf t → K) :
    expectation p (evaluate t) = arithmetic t p := by
  classical
  induction t with
  | input =>
    unfold expectation
    simp only [evaluate,arithmetic]
    let E : (Leaf .input → Bool) ≃ Bool := Equiv.funUnique PUnit Bool
    refine (E.symm.sum_comp (fun s => weight p s * indicator (s PUnit.unit))).symm.trans ?_
    simp [Fintype.sum_bool,E,weight,bernoulli,indicator]
  | neg t ih =>
    change expectation p (fun s => !(evaluate t s)) = 1-arithmetic t p
    exact (complement p (evaluate t)).trans (congrArg (fun z : K => 1-z) (ih p))
  | both a b ha hb =>
    exact (conjunction (A:=Leaf a) (B:=Leaf b) p (evaluate a) (evaluate b)).trans
      (congrArg₂ (fun x y : K => x*y) (ha (p ∘ Sum.inl)) (hb (p ∘ Sum.inr)))
  | either a b ha hb =>
    exact (disjunction (A:=Leaf a) (B:=Leaf b) p (evaluate a) (evaluate b)).trans
      (congrArg₂ (fun x y : K => 1-(1-x)*(1-y)) (ha (p ∘ Sum.inl)) (hb (p ∘ Sum.inr)))

end
end ReadOnce
#print axioms ReadOnce.read_once_exact
