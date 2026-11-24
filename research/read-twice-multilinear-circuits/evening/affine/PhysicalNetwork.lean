import GraphContraction

/-! Expansion of every contracted edge as an ordinary spin sum on its physical
path. The sum is over every internal vertex exactly once. -/
namespace SparseAffine
open scoped BigOperators
noncomputable section

variable {K : Type*} [CommRing K]

/-- Product of one Bernoulli weight per internal vertex and one hard constraint
per physical edge, for a specified assignment to the internal path. -/
def pathTerm (left : Bool) : (ps : List K) → Bool → (Fin ps.length → Bool) → K
  | [],right,_ => hard left right
  | p::ps,right,spins => hard left (spins 0) * mass p (spins 0) *
      pathTerm (spins 0) ps right (fun i => spins i.succ)

theorem expand_path (l : Bool) (ps : List K) (r : Bool) :
    bern l ps r = ∑ spins, pathTerm l ps r spins := by
  induction ps generalizing l with
  | nil => simp [bern,pathTerm,hard]
  | cons p ps ih =>
    let eqv := Fin.consEquiv (n := ps.length) (fun _ => Bool)
    refine Eq.trans ?_ (eqv.sum_comp (pathTerm l (p::ps) r))
    rw [Fintype.sum_prod_type]
    simp only [eqv,Fin.consEquiv_apply,pathTerm,Fin.cons_zero,Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ← ih]
    cases l <;> simp [Fintype.sum_bool,bern,hard,mass] <;> ring

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L]
variable [DecidableEq V] [DecidableEq E] [DecidableEq L]

/-- Enumerate roots, leaves, nine (or any number of) private spins per ordinary
path and the private spins on leaf paths. This is the Bernoulli probability of
no occupied edge on the unsubsumed, physical graph. -/
def fullNetwork (src dst : E → V) (owner : L → V) (p : V → K) (x : L → K)
    (ordinary : E → List K) (leaves : L → List K) : K :=
  ∑ b : V → Bool, ∑ bits : L → Bool,
    ∑ interior : (e : E) → Fin (ordinary e).length → Bool,
      ∑ terminal : (j : L) → Fin (leaves j).length → Bool,
        (∏ v, mass (p v) (b v)) * (∏ j, mass (1-x j) (bits j)) *
        (∏ e, pathTerm (b (src e)) (ordinary e) (b (dst e)) (interior e)) *
        (∏ j, pathTerm (b (owner j)) (leaves j) (bits j) (terminal j))

theorem expand_network (src dst : E → V) (owner : L → V) (p : V → K) (x : L → K)
    (ordinary : E → List K) (leaves : L → List K) :
    fullNetwork src dst owner p x ordinary leaves = network src dst owner p x ordinary leaves := by
  classical
  unfold fullNetwork network
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bits _
  simp_rw [expand_path]
  rw [Finset.prod_mul_distrib]
  rw [Fintype.prod_sum (fun e bits => pathTerm (b (src e)) (ordinary e) (b (dst e)) bits)]
  rw [Fintype.prod_sum (fun j spins => pathTerm (b (owner j)) (leaves j) (bits j) spins)]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

end
end SparseAffine
#print axioms SparseAffine.expand_path
#print axioms SparseAffine.expand_network
