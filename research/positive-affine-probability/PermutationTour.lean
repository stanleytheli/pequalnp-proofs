import HamiltonianCuts
namespace GraphProbability.Hamiltonian
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
def HasCyclePermutation (E : Finset (V×V)) : Prop :=
  ∃ p : Equiv.Perm V, p.IsCycleOn Set.univ ∧ ∀ v,(v,p v)∈E

theorem permutation_of_tour (E : Finset (V×V)) (tour : HasTour E) : HasCyclePermutation E := by
  classical
  obtain ⟨a,b,mid,nd,all,chain,close⟩:=tour
  let L := (a::mid)++[b]
  have len : 2≤L.length := by simp [L]
  have ndup : L.Nodup := nd
  have all' (v : V) : v∈L := all v
  have cy := List.isCycle_formPerm ndup len
  have moved (v : V) : L.formPerm v≠v := (List.formPerm_apply_mem_ne_self_iff L ndup v (all' v)).mpr len
  have eqSet : {v | L.formPerm v≠v}=Set.univ := by
    ext v
    simp [moved]
  refine ⟨L.formPerm,eqSet ▸ cy.isCycleOn,?_⟩
  intro v
  obtain ⟨i,hi,hv⟩:=List.mem_iff_getElem.mp (all' v)
  rw [←hv]
  by_cases next : i+1<L.length
  · rw [List.formPerm_apply_lt_getElem L ndup i next]
    exact chain.getElem i next
  · have last : i=L.length-1 := by omega
    have e : L[i]=b := by
      subst i
      simp [L]
    rw [e]
    simpa [L] using close

/-- A transitive permutation cannot remain inside a proper nonempty set forever. -/
theorem no_perm_on_cut (S : Finset V) (hs : S.Nonempty) (hc : ∃ v,v∉S) :
    ¬HasCyclePermutation (cutEdges S) := by
  rintro ⟨p,cy,arc⟩
  let U : Finset V:=univ
  have cy' : p.IsCycleOn (U : Set V) := by simpa [U] using cy
  have stay (v : V) (h : v∈S) : p v∈S := by
    have e := arc v
    simpa [cutEdges,h] using e
  obtain ⟨s,inside⟩:=hs
  obtain ⟨t,outside⟩:=hc
  obtain ⟨j,_,turn⟩ := cy'.exists_pow_eq (show s∈U from mem_univ _) (show t∈U from mem_univ _)
  have all (j : ℕ) : (p^j) s∈S := by
    induction j with
    | zero => simpa using inside
    | succ j ih => simpa [pow_succ',Equiv.Perm.mul_apply] using stay _ ih
  exact outside (turn ▸ all j)
end GraphProbability.Hamiltonian
#print axioms GraphProbability.Hamiltonian.permutation_of_tour
#print axioms GraphProbability.Hamiltonian.no_perm_on_cut
