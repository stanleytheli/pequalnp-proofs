import ParityEncoding
import PEqualNP.MetaComplexity.Helpers.LocalMajorityQ

namespace ParityEncoding
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.LocalMajority
open PEqualNP.MetaComplexity.Helpers.LocalMajorityQ
open MetaComplexity.LocalThreshold

/-- A fixed-format q-local map satisfying the fleet parity promise on at least
3q+1 positions has a completing circuit for every image. The explicit gate
count uses the public fleet's already-proved unary counter. -/
theorem every_table {n m s q : ℕ} (hn : 3*q+1 ≤ n)
    (w : (Fin n→Bool)→List Bool) (T : (Fin n→Bool)→List (Option Bool))
    (loc : QueryLocal n q w)
    (fmt : ∀ x, w x=List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length=2^m)
    (red : ∀ x, (Finset.univ.filter fun i : Fin n=>x i=true).card % 2=1 ↔ w x∈PartialMCSP)
    (x : Fin n→Bool) :
    ∃ f, Consistent m (T x) f ∧ HasCircuitSize m f (1+(3*q+1)*(s+1+2*(2*q+1))) := by
  classical
  by_cases hx : (Finset.univ.filter fun i : Fin n=>x i=true).card % 2 = 1
  · obtain ⟨f,hf,hs⟩ := odd_witness n m s w T fmt red x hx
    exact ⟨f,hf,hasCircuitSize_mono (by nlinarith [Nat.zero_le (q*s),Nat.zero_le (q*q)]) hs⟩
  · have wit (i : Fin n) : ∃ f, Consistent m (T (flip x i)) f ∧ HasCircuitSize m f s :=
      odd_witness n m s w T fmt red _ (flip_odd x i hx)
    choose f hc hs using wit
    let e := Fin.castLEEmb hn
    let J := Finset.univ.map e
    let F : Fin (3*q+1) → (Fin m→Bool)→Bool := fun l => f (e l)
    let fs := List.ofFn F
    refine ⟨fun z=>decide (2*q+1 ≤ (fs.map fun g=>g z).count true),?_,?_⟩
    · intro z b hz
      have agg := aggregate q J (by simp [J]) x (fun v z' => (T v).getD (tableIndex z') none)
        (fun z' => (fixed_locality w T loc (fun a=>(fmt a).1) x (tableIndex z')).1)
        (fun z' => (fixed_locality w T loc (fun a=>(fmt a).1) x (tableIndex z')).2)
        f (fun i _ =>hc i) z b hz
      rw [Finset.filter_map, Finset.card_map] at agg
      simpa only [fs,F,List.map_ofFn,List.count_ofFn,Function.comp_apply] using agg
    · have bound := thr_size m s (2*q+1) fs
        (by intro g hg; obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hg; exact hs _) (by omega)
      simpa only [fs,List.length_ofFn] using bound

end ParityEncoding
#print axioms ParityEncoding.every_table
