import ZeroSize

namespace ParityEncoding
open PEqualNP.MetaComplexity

/-- Once table rows and their prescribed labels are specified, the available
zero-gate signatures are exactly the columns of their Boolean matrix and the
all-false vector. Rows may repeat and the family need not be finite. -/
theorem zero_matrix {a : ℕ} {I : Type*} (row : I→Fin a→Bool) (label : I→Bool) :
    (∃ f : (Fin a→Bool)→Bool, HasCircuitSize a f 0 ∧ ∀ i, f (row i)=label i) ↔
      (∀ i, label i=false) ∨ ∃ j : Fin a, ∀ i, label i=row i j := by
  constructor
  · rintro ⟨f,sz,ev⟩
    rcases (size_zero_iff f).mp sz with rfl|⟨j,rfl⟩
    · exact .inl (fun i=>(ev i).symm)
    · exact .inr ⟨j,fun i=>(ev i).symm⟩
  · rintro (z|⟨j,proj⟩)
    · exact ⟨fun _=>false,(size_zero_iff _).mpr (.inl rfl),fun i=>(z i).symm⟩
    · exact ⟨fun x=>x j,(size_zero_iff _).mpr (.inr ⟨j,rfl⟩),fun i=>(proj i).symm⟩

/-- Equivalently, for a literal fleet partial table, the all-zero candidate
fits all specified entries, or one input column does. -/
theorem zero_table {a : ℕ} (T : List (Option Bool)) :
    (∃ f, Consistent a T f ∧ HasCircuitSize a f 0) ↔
      Consistent a T (fun _=>false) ∨ ∃ j : Fin a, Consistent a T (fun x=>x j) := by
  constructor
  · rintro ⟨f,h,sz⟩
    rcases (size_zero_iff f).mp sz with rfl|⟨j,rfl⟩
    · exact .inl h
    · exact .inr ⟨j,h⟩
  · rintro (h|⟨j,h⟩)
    · exact ⟨_,h,(size_zero_iff _).mpr (.inl rfl)⟩
    · exact ⟨_,h,(size_zero_iff _).mpr (.inr ⟨j,rfl⟩)⟩

/-- A table contains exactly the specified matrix rows, in the sense that
every nonempty entry is represented and each chosen row carries its label.
This yields the native project's Consistent semantics from the signatures. -/
theorem zero_table_matrix {a : ℕ} {I : Type*} (T : List (Option Bool))
    (row : I→Fin a→Bool) (label : I→Bool)
    (listed : ∀ i, T.getD (tableIndex (row i)) none=some (label i))
    (covers : ∀ y b, T.getD (tableIndex y) none=some b → ∃ i, y=row i ∧ b=label i) :
    (∃ f, Consistent a T f ∧ HasCircuitSize a f 0) ↔
      (∀ i, label i=false) ∨ ∃ j : Fin a, ∀ i, label i=row i j := by
  rw [←zero_matrix row label]
  constructor
  · rintro ⟨f,h,sz⟩
    exact ⟨f,sz,fun i=>h _ _ (listed i)⟩
  · rintro ⟨f,sz,h⟩
    refine ⟨f,fun y b hb=>?_,sz⟩
    rcases covers y b hb with ⟨i,rfl,rfl⟩
    exact h i

end ParityEncoding
#print axioms ParityEncoding.zero_matrix
#print axioms ParityEncoding.zero_table_matrix
