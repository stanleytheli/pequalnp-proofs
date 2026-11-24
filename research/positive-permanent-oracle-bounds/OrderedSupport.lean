import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic.NormNum

/-! The weak total-order axioms as printed in Grochow's paper allow positive
zero divisors. The predicate `live` gives a Boolean specialization on the
nonnegative cone which preserves one and therefore all positive integer
coefficients. It needs no maximal-ideal existence principle. -/
namespace PositivePermanent.OrderedSupport
open Finset Matrix
variable {R : Type*} [CommSemiring R] [LinearOrder R]

structure WeakOrder (R : Type*) [CommSemiring R] [LinearOrder R] : Prop where
  add_left (c : R) {a b : R} : a≤b→c+a≤c+b
  mul_left (c : R) : 0≤c→∀{a b : R},a≤b→c*a≤c*b

def live (x : R) : Prop:=∃r:R,0≤r ∧ 1≤r*x

namespace WeakOrder
variable (w : WeakOrder R)
include w

lemma add_nn {a b : R} (ha:0≤a) (hb:0≤b) : 0≤a+b := by
  exact ha.trans (by simpa using w.add_left a hb)

lemma mul_nn {a b : R} (ha:0≤a) (hb:0≤b) : 0≤a*b := by
  simpa using w.mul_left a ha hb

theorem live_zero (one : (0:R)<1) : ¬live (0:R) := by
  rintro ⟨r,_,h⟩
  exact one.not_ge (by simpa using h)

theorem live_one (one : (0:R)≤1) : live (1:R) := ⟨1,one,by simp⟩

lemma live_mono {a b : R} (e:a≤b) (h:live a) : live b := by
  obtain ⟨r,pos,cert⟩:=h
  exact ⟨r,pos,cert.trans (w.mul_left r pos e)⟩

theorem live_add {a b : R} (ha:0≤a) (hb:0≤b) : live (a+b) ↔ live a ∨ live b := by
  constructor
  · rintro ⟨r,rpos,h⟩
    rcases le_total a b with e|e
    · right
      have bound:a+b≤b+b:=by simpa only [add_comm b a] using w.add_left b e
      exact ⟨r+r,w.add_nn rpos rpos,(h.trans (w.mul_left r rpos bound)).trans_eq (by rw [add_mul,mul_add])⟩
    · left
      exact ⟨r+r,w.add_nn rpos rpos,(h.trans (w.mul_left r rpos (w.add_left a e))).trans_eq (by rw [add_mul,mul_add])⟩
  · rintro (h|h)
    · exact w.live_mono (by simpa using w.add_left a hb) h
    · exact w.live_mono (by simpa only [add_zero,add_comm b a] using w.add_left b ha) h

theorem live_mul (one : (0:R)≤1) {a b : R} (ha:0≤a) (hb:0≤b) : live (a*b) ↔ live a ∧ live b := by
  constructor
  · rintro ⟨r,pos,h⟩
    exact ⟨⟨r*b,w.mul_nn pos hb,by simpa only [mul_assoc,mul_comm b a] using h⟩,
      ⟨r*a,w.mul_nn pos ha,by simpa only [mul_assoc] using h⟩⟩
  · rintro ⟨⟨u,upos,hu⟩,⟨v,vpos,hv⟩⟩
    refine ⟨u*v,w.mul_nn upos vpos,?_⟩
    calc
      (1:R) ≤ u*a := hu
      _ ≤ (u*a)*(v*b) := by simpa only [mul_one] using w.mul_left (u*a) (one.trans hu) hv
      _ = _ := by ac_rfl

variable {ι : Type*}

lemma sum_nn (s : Finset ι) (f : ι→R) (nn : ∀i∈s,0≤f i) : 0≤∑i∈s,f i := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert a s as ih=>rw [sum_insert as];exact w.add_nn (nn _ (by simp)) (ih (fun i hi=>nn i (mem_insert_of_mem hi)))

lemma prod_nn (one : (0:R)≤1) (s : Finset ι) (f : ι→R) (nn : ∀i∈s,0≤f i) : 0≤∏i∈s,f i := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using one
  | @insert a s as ih=>rw [prod_insert as];exact w.mul_nn (nn _ (by simp)) (ih (fun i hi=>nn i (mem_insert_of_mem hi)))

theorem live_sum (one : (0:R)<1) (s : Finset ι) (f : ι→R) (nn : ∀i∈s,0≤f i) :
    live (∑i∈s,f i) ↔ ∃i∈s,live (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp [w.live_zero one]
  | @insert a s as ih=>
    have pos:=fun i (hi:i∈s)=>nn i (mem_insert_of_mem hi)
    rw [sum_insert as,w.live_add (nn _ (by simp)) (w.sum_nn s f pos),ih pos]
    simp

theorem live_prod (one : (0:R)≤1) (s : Finset ι) (f : ι→R) (nn : ∀i∈s,0≤f i) :
    live (∏i∈s,f i) ↔ ∀i∈s,live (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp [w.live_one one]
  | @insert a s as ih=>
    have pos:=fun i (hi:i∈s)=>nn i (mem_insert_of_mem hi)
    rw [prod_insert as,w.live_mul one (nn _ (by simp)) (w.prod_nn one s f pos),ih pos]
    simp

/-- Boolean specialization commutes with one arbitrary permanent oracle. -/
theorem live_permanent (one : (0:R)<1) {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I R) (nn : ∀i j,0≤A i j) :
    live A.permanent ↔ ∃p : Equiv.Perm I,∀i,live (A (p i) i) := by
  classical
  unfold Matrix.permanent
  rw [w.live_sum one _ _ (fun p _=>w.prod_nn one.le _ _ (fun i _=>nn _ _))]
  simp only [mem_univ,true_and]
  apply exists_congr
  intro p
  simpa only [mem_univ,forall_const] using w.live_prod one.le univ (fun i=>A (p i) i) (fun i _=>nn _ _)

/-- In the reversed orientation allowed by the printed weak axioms, the
only permissible circuit constant is zero. -/
theorem nonpositive_orientation (h : (1:R)≤0) {x : R} (hx : 0≤x) : x=0 := by
  exact le_antisymm (by simpa using w.mul_left x hx h) hx

theorem casts_negative (h : (1:R)<0) (n : ℕ) : (((n+1:ℕ):R))<0 := by
  induction n with
  | zero=>simpa using h
  | succ n ih=>
    exact lt_of_le_of_lt (by simpa only [Nat.cast_add,Nat.cast_one,add_zero] using w.add_left (((n+1:ℕ):R)) h.le) ih

end WeakOrder
end PositivePermanent.OrderedSupport
#print axioms PositivePermanent.OrderedSupport.WeakOrder.live_permanent
#print axioms PositivePermanent.OrderedSupport.WeakOrder.casts_negative
