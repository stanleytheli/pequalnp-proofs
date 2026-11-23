import SubdivisionLayout

namespace Subdivision
open Finset

namespace Seven
variable {v m : ℕ}

def tip (e : Fin m) (i : Fin 6) : Fin (v + m*6) :=
  Fin.natAdd v (finProdFinEquiv (e,i))

private theorem tip_inj {a b : Fin m} {i j : Fin 6}
    (h : tip (v:=v) a i=tip b j) : (a,i)=(b,j) :=
  finProdFinEquiv.injective ((Fin.natAdd_inj v).mp h)

private theorem tip_ne_base (e : Fin m) (i : Fin 6) (w : Fin v) :
    tip (v:=v) e i ≠ Fin.castAdd _ w := by
  intro h
  have hv := congrArg Fin.val h
  change v+(finProdFinEquiv (e,i)).val=w.val at hv
  omega

/-- Canonical numbering of a graph with six new private vertices for each edge. -/
def layout (l r : Fin m → Fin v) (distinct : ∀ e,l e ≠ r e) : Layout (v + m*6) m where
  left e := Fin.castAdd _ (l e)
  right e := Fin.castAdd _ (r e)
  distinct e h := distinct e ((Fin.castAdd_inj).mp h)
  half _ := 3
  long _ := le_rfl
  inner e := ⟨tip e,fun _ _ h => congrArg Prod.snd (tip_inj h)⟩
  apart _ _ ne eq := ne (congrArg Prod.fst (tip_inj eq))
  notLeft e i j := tip_ne_base e i (l j)
  notRight e i j := tip_ne_base e i (r j)

theorem covers_iff (l r : Fin m → Fin v) (d : ∀ e,l e ≠ r e) (k : ℕ) :
    (∃ U : Finset (Fin (v + m*6)), (∀ e,(layout l r d).left e ∈ U ∨ (layout l r d).right e ∈ U) ∧ U.card ≤ k) ↔
    ∃ T : Finset (Fin v), (∀ e,l e ∈ T ∨ r e ∈ T) ∧ T.card ≤ k := by
  classical
  let f (w : Fin v) : Fin (v+m*6) := Fin.castAdd _ w
  have inj : Function.Injective f := Fin.castAdd_injective _ _
  constructor
  · rintro ⟨U,hu,hk⟩
    let T := univ.filter (fun w => f w ∈ U)
    refine ⟨T,fun e => ?_,?_⟩
    · simpa [T,f,layout] using hu e
    · have sub : T.image f ⊆ U := by
        intro w hw
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hw
        exact (mem_filter.mp ha).2
      rw [←card_image_of_injective T inj]
      exact (card_le_card sub).trans hk
  · rintro ⟨T,ht,hk⟩
    refine ⟨T.image f,fun e => ?_,by rwa [card_image_of_injective T inj]⟩
    rcases ht e with h|h
    · exact Or.inl (mem_image_of_mem f h)
    · exact Or.inr (mem_image_of_mem f h)
end Seven
end Subdivision
#print axioms Subdivision.Seven.covers_iff
