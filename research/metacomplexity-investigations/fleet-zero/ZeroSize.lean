import PEqualNP.Defs.MetaComplexity

namespace ParityEncoding
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem size_zero_iff {a : ℕ} (f : (Fin a → Bool) → Bool) :
    HasCircuitSize a f 0 ↔ f=(fun _=>false) ∨ ∃ i:Fin a, f=(fun x=>x i) := by
  constructor
  · rintro ⟨⟨gs,out⟩,_,size,spec⟩
    have h : gs=[] := List.length_eq_zero_iff.mp (by simpa [Circuit.size] using size)
    subst gs
    have ev (x : Fin a→Bool) : (List.ofFn x).getD out false = f x := spec x
    by_cases inside : out<a
    · right
      refine ⟨⟨out,inside⟩,funext fun x => ?_⟩
      rw [← ev x]
      simp [List.getD_eq_getElem?_getD,inside]
    · left
      funext x
      rw [← ev x]
      simp [List.getD_eq_getElem?_getD,inside]
  · rintro (rfl|⟨i,rfl⟩)
    · refine ⟨⟨[],a⟩,by simp [FanInTwo],by simp [Circuit.size],fun x=>?_⟩
      change (List.ofFn x).getD a false=false
      simp [List.getD_eq_getElem?_getD]
    · refine ⟨⟨[],i.val⟩,by simp [FanInTwo],by simp [Circuit.size],fun x=>?_⟩
      change (List.ofFn x).getD i.val false=x i
      simp [List.getD_eq_getElem?_getD,i.isLt]

end ParityEncoding
#print axioms ParityEncoding.size_zero_iff
