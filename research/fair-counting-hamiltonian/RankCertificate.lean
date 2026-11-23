import Mathlib

/-! Unique position labels recognize a directed Hamiltonian cycle. -/
namespace SparseHamiltonian

open Function Equiv Fin.NatCast

variable {n : ℕ} [NeZero n]

def RankCertificate (f : Fin n → Fin n) (r : Fin n → Fin n) : Prop :=
  r 0 = 0 ∧ ∀ x, r (f x) = r x + 1

private theorem rank_iterate (f r : Fin n → Fin n) (h : RankCertificate f r)
    (k : ℕ) : r ((f^[k]) 0) = (k : Fin n) := by
  induction k with
  | zero => simpa using h.1
  | succ k ih => rw [iterate_succ_apply', h.2, ih, Nat.cast_succ]

private def orbit (f : Fin n → Fin n) (i : Fin n) := (f^[i.val]) 0

private theorem rank_orbit {f r : Fin n → Fin n} (h : RankCertificate f r) :
    LeftInverse r (orbit f) := by
  intro i
  simpa [orbit] using rank_iterate f r h i.val

theorem unique_rank {f r s : Fin n → Fin n} (hr : RankCertificate f r) (hs : RankCertificate f s) :
    r = s := by
  have surj := Finite.surjective_of_injective (rank_orbit hr).injective
  funext x
  obtain ⟨i,rfl⟩ := surj x
  rw [rank_orbit hr i, rank_orbit hs i]

/-- A function having position labels is bijective, even without an indegree hypothesis. -/
theorem bijective_of_rank {f r : Fin n → Fin n} (h : RankCertificate f r) : Bijective f := by
  have hr : Injective r := Finite.injective_iff_surjective.mpr (rank_orbit h).surjective
  have hf : Injective f := by
    intro x y eq
    apply hr
    simpa [h.2] using congrArg r eq
  exact ⟨hf, Finite.surjective_of_injective hf⟩

private theorem isCycleOn_of_rank {f : Perm (Fin n)} {r : Fin n → Fin n}
    (h : RankCertificate f r) : f.IsCycleOn Set.univ := by
  have surj := Finite.surjective_of_injective (rank_orbit h).injective
  have same (x : Fin n) : f.SameCycle 0 x := by
    obtain ⟨i,rfl⟩ := surj x
    exact ⟨(i.val : ℤ), by simp [orbit, Perm.coe_pow]⟩
  exact ⟨Set.bijOn_univ.mpr f.bijective, fun x _ y _ => (same x).symm.trans (same y)⟩

/-- The anchored rank exists exactly for a single directed cycle on all vertices. -/
theorem certificate_iff_cycle (f : Perm (Fin n)) :
    (∃! r, RankCertificate f r) ↔ f.IsCycleOn Set.univ := by
  constructor
  · rintro ⟨r,hr,_⟩
    exact isCycleOn_of_rank hr
  intro h
  have cyc : f.IsCycleOn (Finset.univ : Finset (Fin n)) := by simpa using h
  have surj : Surjective (orbit (f : Fin n → Fin n)) := by
    intro x
    obtain ⟨k,hk,hx⟩ := cyc.exists_pow_eq (a := 0) (Finset.mem_univ _) (Finset.mem_univ x)
    simp only [Finset.card_univ, Fintype.card_fin] at hk
    exact ⟨⟨k,hk⟩, by simpa [orbit, Perm.coe_pow] using hx⟩
  let e := Equiv.ofBijective (orbit (f : Fin n → Fin n)) ⟨Finite.injective_iff_surjective.mpr surj, surj⟩
  have re (i : Fin n) : e.symm (orbit f i) = i := e.symm_apply_apply i
  have hx (x : Fin n) : (f ^ (e.symm x).val) 0 = x := by
    rw [Perm.coe_pow]
    exact e.apply_symm_apply x
  have cert : RankCertificate f e.symm := by
    refine ⟨?_,?_⟩
    · simpa [orbit] using re (0 : Fin n)
    intro x
    have eq : (f ^ (e.symm (f x)).val) 0 = (f ^ ((e.symm x).val+1)) 0 := by
      rw [hx, pow_succ', Perm.mul_apply, hx]
    have hm := (cyc.pow_apply_eq_pow_apply (a := 0) (Finset.mem_univ _)).mp eq
    apply Fin.ext
    simpa [Nat.ModEq, Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (e.symm (f x)).isLt] using hm
  exact ⟨_, cert, fun _ hr => unique_rank hr cert⟩

end SparseHamiltonian

#print axioms SparseHamiltonian.bijective_of_rank
#print axioms SparseHamiltonian.certificate_iff_cycle
