import PortAccess

namespace SparsePermanent.DirectedGrowth
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : V→V→Prop} {P : Finset V} {L W r k : ℕ}

structure Demand (E : V→V→Prop) (P : Finset V) (L W r : ℕ) where
  forward : Port E P L W r
  backward : Port (fun x y=>E y x) P L W r

def Demand.trunks (d : Demand E P L W r) := d.forward.trunk∪d.backward.trunk

private theorem protected_subset (d : Demand E P L W r) : d.trunks⊆P :=
  union_subset d.forward.trunk_in d.backward.trunk_in

/-- The output keeps a separate support and avoiding route for every ordered
demand, plus disjointness of all supports and protected-skeleton ownership. -/
inductive Packed (E : V→V→Prop) (P : Finset V) (L W r M : ℕ) : List (Demand E P L W r)→Finset V→Prop
  | nil : Packed E P L W r M [] ∅
  | cons {job : Demand E P L W r} {jobs : List (Demand E P L W r)} {S T : Finset V} {t : ℕ}
      (route : Route E (univ\S) job.forward.origin job.backward.origin t) (len : t≤M)
      (size : S.card≤t+1) (own : S∩P⊆job.trunks) (tail : Packed E P L W r M jobs T)
      (separate : Disjoint S T) : Packed E P L W r M (job::jobs) (S∪T)

private theorem recur (hk : 0<k) (fwd : Expands E k) (bwd : Expands (fun x y=>E y x) k)
    (B : ℕ) (cap : 2*k*(P.card+B)≤(L-B)*W) (positive : 0<(L-B)*W) :
    ∀ (jobs : List (Demand E P L W r)) (U : Finset V),
      jobs.Pairwise (fun a b=>Disjoint a.trunks b.trunks) →
      U.card+jobs.length*((2*r+4*k*(Nat.log 2 (Fintype.card V)+1))+1)≤B →
      (∀ j∈jobs,Disjoint U j.trunks) →
      ∃ T, Packed E P L W r (2*r+4*k*(Nat.log 2 (Fintype.card V)+1)) jobs T ∧ Disjoint T U := by
  let M:=2*r+4*k*(Nat.log 2 (Fintype.card V)+1)
  intro jobs
  induction jobs with
  | nil=>intro U _ _ _; exact ⟨∅,.nil,disjoint_empty_left _⟩
  | cons job jobs ih=>
    intro U sep room untouched
    change U.card+(job::jobs).length*(M+1)≤B at room
    have smaller : U.card≤B:=by omega
    have leaf : (L-B)*W≤(L-U.card)*W :=
      Nat.mul_le_mul_right _ (Nat.sub_le_sub_left smaller L)
    have unionBound : (P∪U).card≤P.card+B := (card_union_le ..).trans (Nat.add_le_add_left smaller _)
    have no:= (untouched job List.mem_cons_self).symm
    obtain ⟨S,su,own,t,ht,sz,walk⟩:=link job.forward job.backward U hk fwd bwd
      (no.mono_left subset_union_left) (no.mono_left subset_union_right)
      (((Nat.mul_le_mul_left (2*k) unionBound).trans cap).trans leaf) (positive.trans_le leaf)
    have leftFree : ∀ j∈jobs,Disjoint (U∪S) j.trunks := by
      intro j mem
      apply disjoint_union_left.mpr
      refine ⟨untouched j (List.mem_cons_of_mem _ mem),?_⟩
      apply disjoint_left.mpr
      intro x xs xj
      exact disjoint_left.mp ((List.pairwise_cons.mp sep).1 j mem)
        (own (mem_inter.mpr ⟨xs,protected_subset j xj⟩)) xj
    have room' : (U∪S).card+jobs.length*(M+1)≤B := by
      have c:=card_union_le U S
      change t≤M at ht
      simp only [List.length_cons,Nat.add_mul,one_mul] at room
      omega
    obtain ⟨T,tail,tu⟩:=ih (U∪S) (List.pairwise_cons.mp sep).2 room' leftFree
    exact ⟨S∪T,.cons walk ht sz own tail (tu.mono_right subset_union_right).symm,
      disjoint_union_left.mpr ⟨su,tu.mono_right subset_union_left⟩⟩

/-- Greedy all-pairs routing from finite port data, with numeric capacity that
can be discharged once for the entire list, including the last demand. -/
theorem pack (jobs : List (Demand E P L W r)) (hk : 0<k)
    (fwd : Expands E k) (bwd : Expands (fun x y=>E y x) k)
    (separate : jobs.Pairwise (fun a b=>Disjoint a.trunks b.trunks))
    {M B : ℕ} (time : M=2*r+4*k*(Nat.log 2 (Fintype.card V)+1))
    (space : B=jobs.length*(M+1)) (capacity : 2*k*(P.card+B)≤(L-B)*W)
    (positive : 0<(L-B)*W) : ∃T,Packed E P L W r M jobs T := by
  subst M
  obtain ⟨T,ok,_⟩:=recur hk fwd bwd B capacity positive jobs ∅ separate
    (by simp [space]) (fun _ _=>disjoint_empty_left _)
  exact ⟨T,ok⟩

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.pack
