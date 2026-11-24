import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace SparsePermanent.BinaryWords
open Finset
abbrev Word := List Bool

noncomputable def words (n : ℕ) : Finset Word := univ.image (@List.ofFn Bool n)

@[simp] theorem mem_words {w : Word} {n : ℕ} : w∈words n ↔ w.length=n := by
  classical
  constructor
  · rintro h
    obtain ⟨f,_,rfl⟩:=mem_image.mp h
    simp
  · rintro rfl
    exact mem_image.mpr ⟨w.get,mem_univ _,List.ofFn_get w⟩

@[simp] theorem card_words (n : ℕ) : (words n).card=2^n := by
  rw [words,card_image_of_injective _ List.ofFn_injective]
  simp [Fintype.card_pi_const]

noncomputable def through : ℕ→ Finset Word
  | 0=>words 0
  | n+1=>through n∪words (n+1)

@[simp] theorem mem_through {w : Word} {n : ℕ} : w∈through n ↔ w.length≤n := by
  induction n with
  | zero=>simp [through]
  | succ n ih=>
    simp only [through,mem_union,ih,mem_words]
    omega

theorem card_through (n : ℕ) : (through n).card≤2^(n+1) := by
  induction n with
  | zero=>simp [through]
  | succ n ih=>
    have c:=card_union_le (through n) (words (n+1))
    rw [card_words] at c
    change (through n∪words (n+1)).card≤2^(n+1+1)
    rw [pow_succ]
    omega

noncomputable def enumerate (n : ℕ) : Fin (2^n) ≃ (words n) :=
  Fintype.equivOfCardEq (by simp)

theorem prefix_eq {u v a b : Word} (size : u.length=v.length) (same : u++a=v++b) : u=v := by
  have eq:=congrArg (List.take u.length) same
  rw [List.take_append_of_le_length (by omega),List.take_append_of_le_length (by omega)] at eq
  rw [List.take_of_length_le le_rfl,List.take_of_length_le size.ge] at eq
  exact eq

end SparsePermanent.BinaryWords
#print axioms SparsePermanent.BinaryWords.card_words
