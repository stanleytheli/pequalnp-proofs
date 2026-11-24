import ZeroMatrix
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace ParityEncoding
open PEqualNP.MetaComplexity

variable {I : Type*} [Fintype I]

def nonzeroColumns (A : Finset (I→Bool)) := A.erase (fun _=>false)

noncomputable def rowsOf (A : Finset (I→Bool)) (i : I)
    (j : Fin (Fintype.card ↥(nonzeroColumns A))) : Bool :=
  ((Fintype.equivFin ↥(nonzeroColumns A)).symm j).val i

/-- Any finite Boolean code containing zero is the signature family of the
zero-gate functions on the indicated row matrix; no target variable is spent
on the all-zero codeword. Distinct matrix rows are needed only when prescribing
conflicting labels in a literal table. -/
theorem code_rows (A : Finset (I→Bool)) (hz : (fun _=>false)∈A) (w : I→Bool) :
    (∃ f, HasCircuitSize (Fintype.card ↥(nonzeroColumns A)) f 0 ∧
      ∀ i, f (rowsOf A i)=w i) ↔ w∈A := by
  rw [zero_matrix]
  constructor
  · rintro (z|⟨j,h⟩)
    · have e : w=(fun _=>false) := funext z
      simpa only [e] using hz
    · let v := (Fintype.equivFin ↥(nonzeroColumns A)).symm j
      have e : w=v.val := funext h
      exact e ▸ Finset.mem_of_mem_erase v.property
  · intro h
    by_cases zero : w=fun _=>false
    · exact .inl (fun i=>congrFun zero i)
    · let v : ↥(nonzeroColumns A) := ⟨w,Finset.mem_erase.mpr ⟨zero,h⟩⟩
      refine .inr ⟨Fintype.equivFin _ v,fun i=>?_⟩
      simp [rowsOf,v]

theorem code_arity (A : Finset (I→Bool)) (hz : (fun _=>false)∈A) :
    Fintype.card ↥(nonzeroColumns A)=A.card-1 := by
  rw [Fintype.card_coe]
  exact Finset.card_erase_of_mem hz

/-- The checksum code has one codeword for each unrestricted assignment to
the first m bits; it has exactly 2^m-1 nonzero columns when the checksum of
the all-zero assignment is false. In particular the checksum may be parity. -/
def checksumCode {m : ℕ} (check : (Fin m→Bool)→Bool) : Finset (Fin (m+1)→Bool) :=
  Finset.univ.image fun u : Fin m→Bool => Fin.snoc u (check u)

theorem checksum_arity {m : ℕ} (check : (Fin m→Bool)→Bool)
    (zero : check (fun _=>false)=false) :
    Fintype.card ↥(nonzeroColumns (checksumCode check))=2^m-1 := by
  have hz : (fun _=>false)∈checksumCode check := by
    apply Finset.mem_image.mpr
    refine ⟨fun _=>false,Finset.mem_univ _,?_⟩
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa [Fin.snoc] using zero
    · simp
  rw [code_arity _ hz]
  unfold checksumCode
  rw [Finset.card_image_of_injective]
  · simp
  · intro u v eq
    funext i
    simpa using congrFun eq (Fin.castSucc i)

end ParityEncoding
#print axioms ParityEncoding.code_rows
#print axioms ParityEncoding.checksum_arity
