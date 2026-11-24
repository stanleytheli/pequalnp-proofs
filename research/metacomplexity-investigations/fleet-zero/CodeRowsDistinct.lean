import CodeRows
import Mathlib.Data.Fintype.Fin

namespace ParityEncoding
open Finset

theorem rows_injective {I : Type*} [Fintype I] (A : Finset (I→Bool))
    (sep : ∀ i j : I, i≠j → ∃ v∈A, v i≠v j) : Function.Injective (rowsOf A) := by
  intro i j h
  by_contra bad
  obtain ⟨v,good,diff⟩ := sep i j bad
  have nonzero : v≠(fun _=>false) := by rintro rfl; exact diff rfl
  let c : ↥(nonzeroColumns A) := ⟨v,Finset.mem_erase.mpr ⟨nonzero,good⟩⟩
  apply diff
  simpa only [rowsOf,Equiv.symm_apply_apply] using congrFun h (Fintype.equivFin _ c)

def evenCode (m : ℕ) : Finset (Fin m→Bool) :=
  univ.filter fun w=>(univ.filter fun i=>w i=true).card % 2=0

theorem even_rows_distinct {m : ℕ} (hm : 3≤m) : Function.Injective (rowsOf (evenCode m)) := by
  apply rows_injective
  intro i j ij
  have proper : ({i,j}:Finset (Fin m)) ≠ univ := by
    intro e
    have h := congrArg Finset.card e
    simp [ij] at h
    omega
  have missing : ∃ k : Fin m, k ∉ ({i,j}:Finset (Fin m)) := by
    by_contra! all
    exact proper (Finset.eq_univ_iff_forall.mpr all)
  obtain ⟨k,out⟩ := missing
  have ki : k≠i := by rintro rfl; exact out (by simp)
  have kj : k≠j := by rintro rfl; exact out (by simp)
  let w : Fin m→Bool := fun x=>decide (x=i ∨ x=k)
  have lit : (univ.filter fun x=>w x=true)=({i,k}:Finset (Fin m)) := by
    ext x
    simp [w]
  refine ⟨w,?_,?_⟩
  · simp [evenCode,lit,Ne.symm ki]
  · simp [w,Ne.symm ij,Ne.symm kj]

theorem even_arity (m : ℕ) :
    Fintype.card ↥(nonzeroColumns (evenCode (m+1)))=2^m-1 := by
  let par (u : Fin m→Bool) := decide ((univ.filter fun i=>u i=true).card % 2=1)
  let make (u : Fin m→Bool) : Fin (m+1)→Bool := Fin.cons (par u) u
  have membership (w : Fin (m+1)→Bool) : w∈evenCode (m+1) ↔ w 0=par (fun i=>w i.succ) := by
    simp only [evenCode,mem_filter,mem_univ,true_and]
    rw [Fin.card_filter_univ_succ]
    cases e : w 0 <;> simp [par]
    omega
  have families : evenCode (m+1)=univ.image make := by
    ext w
    rw [membership,mem_image]
    constructor
    · intro condition
      refine ⟨fun i=>w i.succ,mem_univ _,?_⟩
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · simpa [make] using condition.symm
      · simp [make]
    · rintro ⟨u,_,rfl⟩
      simp [make]
  rw [code_arity _ (by simp [evenCode]),families]
  rw [Finset.card_image_of_injective]
  · simp
  · intro u v eq
    funext i
    simpa [make] using congrFun eq i.succ

end ParityEncoding
#print axioms ParityEncoding.rows_injective
#print axioms ParityEncoding.even_rows_distinct
#print axioms ParityEncoding.even_arity
