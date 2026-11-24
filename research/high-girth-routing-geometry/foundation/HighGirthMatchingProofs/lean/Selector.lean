import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic

namespace SparsePermanent

/-- A matching saturating the internal vertices of a path with k gaps and k+1 ports.
Gap j can only match its left or its right port. -/
structure Selector (k : ℕ) where
  port : Fin k ↪ Fin (k+1)
  adjacent : ∀ j, port j = j.castSucc ∨ port j = j.succ

namespace Selector
variable {k : ℕ}

@[ext]
theorem ext {u v : Selector k} (h : ∀ j, u.port j = v.port j) : u = v := by
  cases u with | mk u hu =>
    cases v with | mk v hv =>
      have : u = v := Function.Embedding.ext h
      subst v
      rfl

def atHole (p : Fin (k+1)) : Selector k where
  port := ⟨p.succAbove, Fin.succAbove_right_injective⟩
  adjacent j := by
    by_cases h : j.castSucc < p
    · exact Or.inl (Fin.succAbove_of_castSucc_lt p j h)
    · exact Or.inr (Fin.succAbove_of_le_castSucc p j (le_of_not_gt h))

theorem strict_port (a : Selector k) : StrictMono a.port := by
  intro i j hij
  have ne : a.port i ≠ a.port j := fun eq => hij.ne (a.port.injective eq)
  apply lt_of_le_of_ne _ ne
  obtain ha | ha := a.adjacent i <;> obtain hb | hb := a.adjacent j <;>
    simp only [ha,hb,Fin.le_def,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] at * <;> omega

theorem exists_atHole (a : Selector k) : ∃ p : Fin (k+1), a = atHole p := by
  classical
  let I := Finset.univ.map a.port
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show I.card < (Finset.univ : Finset (Fin (k+1))).card by simp [I])
  have hs : I ⊆ Finset.univ.erase p := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨fun eq => hp (eq ▸ hi), Finset.mem_univ _⟩
  have eq : I = Finset.univ.erase p := Finset.eq_of_subset_of_card_le hs (by simp [I])
  have ca : (Finset.univ.erase p).card = k := by simp
  have aeq := Finset.orderEmbOfFin_unique ca (f := a.port) (fun i => eq ▸ Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    a.strict_port
  have beq := Finset.orderEmbOfFin_unique ca (f := p.succAbove) (fun i => Finset.mem_erase.mpr ⟨Fin.succAbove_ne _ _, Finset.mem_univ _⟩)
    (Fin.strictMono_succAbove p)
  exact ⟨p, ext (fun i => congrFun (aeq.trans beq.symm) i)⟩

theorem unused_iff (p c : Fin (k+1)) : (¬∃ j, (atHole p).port j = c) ↔ c = p := by
  change c ∉ Set.range p.succAbove ↔ c = p
  rw [Fin.range_succAbove]
  simp

theorem atHole_injective : Function.Injective (atHole (k:=k)) := by
  intro p q eq
  apply (unused_iff q p).1
  rw [←eq]
  exact (unused_iff p p).2 rfl

/-- The unmatched port parametrizes all internal matching choices bijectively. -/
noncomputable def equivPort : Selector k ≃ Fin (k+1) :=
  (Equiv.ofBijective atHole ⟨atHole_injective, fun a => by
    obtain ⟨p,h⟩ := exists_atHole a
    exact ⟨p,h.symm⟩⟩).symm

@[simp] theorem atHole_equivPort (a : Selector k) : atHole (equivPort a) = a :=
  equivPort.symm_apply_apply a

@[simp] theorem equivPort_atHole (p : Fin (k+1)) : equivPort (atHole p) = p :=
  equivPort.apply_symm_apply p

theorem unused (a : Selector k) (p : Fin (k+1)) :
    (¬∃ j, a.port j = p) ↔ p = equivPort a := by
  conv_lhs => rw [←atHole_equivPort a]
  exact unused_iff _ _

end Selector
end SparsePermanent

#print axioms SparsePermanent.Selector.equivPort
