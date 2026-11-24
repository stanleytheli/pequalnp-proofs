import SplitCertificate

namespace SparsePermanent.SplitCertificate

/-- A cubic bipartite graph recorded along a fixed matching. Row i retains its
diagonal pair and has two further allowed neighbors in the other part. -/
def board {n : ℕ} (neighbors : Array (ℕ×ℕ)) (i j : Fin n) : Prop :=
  i=j ∨ (neighbors[i.val]?.any (fun p=>p.1==j.val || p.2==j.val))=true

instance {n : ℕ} (neighbors : Array (ℕ×ℕ)) (i j : Fin n) : Decidable (board neighbors i j) :=
  inferInstanceAs (Decidable (_ ∨ _))

def check (n : ℕ) [NeZero n] (neighbors : Array (ℕ×ℕ)) (roots : List ℕ) (steps : List Step) : Bool :=
  match replay (initial roots) steps with
  | none=>false
  | some u=>u.names.all (fun k=>k<n) &&
      u.wires.all (fun p=>decide (board neighbors (Fin.ofNat n p.1) (Fin.ofNat n p.2)))

theorem check_sound (n : ℕ) [NeZero n] (neighbors : Array (ℕ×ℕ)) (roots : List ℕ) (steps : List Step)
    (yes : check n neighbors roots steps=true) :
    ∃u,replay (initial roots) steps=some u ∧
      (∀p∈u.wires,board neighbors (Fin.ofNat n p.1) (Fin.ofNat n p.2)) ∧
      ∀a∈u.names,∀b∈u.names,Fin.ofNat n a=Fin.ofNat n b→a=b := by
  unfold check at yes
  cases run:replay (initial roots) steps with
  | none=>simp [run] at yes
  | some u=>
    simp only [run,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at yes
    refine ⟨u,rfl,yes.2,?_⟩
    intro i hi j hj eq
    have iv:=yes.1 i hi
    have jv:=yes.1 j hj
    have value:=congrArg Fin.val eq
    simpa [Fin.ofNat,Nat.mod_eq_of_lt iv,Nat.mod_eq_of_lt jv] using value

end SparsePermanent.SplitCertificate
#print axioms SparsePermanent.SplitCertificate.check_sound
