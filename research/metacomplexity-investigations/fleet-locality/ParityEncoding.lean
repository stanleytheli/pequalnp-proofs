import PEqualNP.Defs.MetaComplexityLocal
import LocalThreshold
import Mathlib.Data.List.GetD

namespace ParityEncoding
open PEqualNP.MetaComplexity MetaComplexity.LocalThreshold

theorem code_bits (T : List (Option Bool)) (i : ℕ) :
    (encodePartial T).getD (2*i) false = present (T.getD i none) ∧
    (encodePartial T).getD (2*i+1) false = value (T.getD i none) := by
  induction T generalizing i with
  | nil => simp [encodePartial,present,value]
  | cons o T ih =>
    cases i with
    | zero => cases o <;> simp [encodePartial,present,value]
    | succ i =>
      have h0 : 2*(i+1) = (2*i)+1+1 := by omega
      have h1 : 2*(i+1)+1 = (2*i+1)+1+1 := by omega
      cases o <;> simpa [encodePartial,h1,h0] using ih i

theorem drop_header (s i : ℕ) (T : List (Option Bool)) :
    (List.replicate s true ++ false :: encodePartial T).getD (s+1+i) false =
      (encodePartial T).getD i false := by
  rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_replicate]
  rw [show s+1+i-s=i+1 by omega]
  rfl

theorem fixed_locality {n q s : ℕ} (w : (Fin n→Bool)→List Bool)
    (T : (Fin n→Bool)→List (Option Bool)) (loc : QueryLocal n q w)
    (fmt : ∀ x, w x=List.replicate s true ++ false :: encodePartial (T x))
    (x : Fin n→Bool) (i : ℕ) :
    LocalAt q (fun z=>present ((T z).getD i none)) x ∧
    LocalAt q (fun z=>value ((T z).getD i none)) x := by
  have pos (r : ℕ) : LocalAt q (fun z=>(encodePartial (T z)).getD r false) x := by
    obtain ⟨S,hs,h⟩ := loc (s+1+r) x
    refine ⟨S,hs,fun y hy=>?_⟩
    have e := congrArg (fun o : Option Bool=>o.getD false) (h y hy)
    change (w y).getD (s+1+r) false = (w x).getD (s+1+r) false at e
    simpa only [fmt,drop_header] using e
  constructor
  · simpa only [(code_bits _ _).1] using pos (2*i)
  · simpa only [(code_bits _ _).2] using pos (2*i+1)

theorem circuit_aggregate {n n' q s : ℕ} (w : (Fin n→Bool)→List Bool)
    (T : (Fin n→Bool)→List (Option Bool)) (loc : QueryLocal n q w)
    (fmt : ∀ x, w x=List.replicate s true ++ false :: encodePartial (T x))
    (x : Fin n→Bool) (J : Finset (Fin n)) (card : J.card=3*q+1)
    (C : Fin n→PEqualNP.CircuitLowerBounds.Circuit)
    (ok : ∀ i∈J, Consistent n' (T (flip x i)) (fun y=> (C i).eval (List.ofFn y))) :
    Consistent n' (T x) (fun y=>decide (2*q+1 ≤
      (J.filter fun i=>(C i).eval (List.ofFn y)=true).card)) := by
  intro y b hb
  exact aggregate q J card x (fun z y' => (T z).getD (tableIndex y') none)
    (fun y' => (fixed_locality w T loc fmt x (tableIndex y')).1)
    (fun y' => (fixed_locality w T loc fmt x (tableIndex y')).2)
    (fun i y'=>(C i).eval (List.ofFn y')) ok y b hb

end ParityEncoding
#print axioms ParityEncoding.fixed_locality
#print axioms ParityEncoding.circuit_aggregate
