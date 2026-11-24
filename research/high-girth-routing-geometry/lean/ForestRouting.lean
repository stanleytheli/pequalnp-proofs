import GreedyRouting
import PortTrees

namespace SparsePermanent.DirectedGrowth
open Finset BinaryWords
variable {V : Type*} [Fintype V] [DecidableEq V]

def oriented (E : V→V→Prop) {m : ℕ} (i : Fin m×Bool) (x y : V) : Prop :=
  if i.2 then E y x else E x y

namespace Forest
variable {E : V→V→Prop} {m R l s k : ℕ} (T : Forest (@oriented V E m) R)
variable (width : m≤2^l) (positive : 0<s) (depth : l+2*s≤R)

private noncomputable def code (i : Fin m) (l : ℕ) (width : m≤2^l) : Word :=
  ((enumerate l) (i.castLE width)).val

private theorem code_length (i : Fin m) : (code i l width).length=l :=
  mem_words.mp ((enumerate l) (i.castLE width)).property

private theorem code_injective : Function.Injective (fun i : Fin m=>code i l width) := by
  intro i j h
  have H:= (enumerate l).injective (Subtype.ext h)
  exact Fin.ext (congrArg (Fin.val (n:=2^l)) H)

noncomputable def demand (p : Fin m×Fin m) :
    Demand E (T.core (l+s)) (2^s) (2^s) (2*s) where
  forward:=T.port (p.1,false) (code p.2 l width) l s (code_length width _) positive depth
  backward:=T.port (p.2,true) (code p.1 l width) l s (code_length width _) positive depth

private theorem distinct_trunks (p q : Fin m×Fin m) (ne : p≠q) (lp : 0<l) :
    Disjoint (T.demand width positive depth p).trunks (T.demand width positive depth q).trunks := by
  rcases p with ⟨i,j⟩
  rcases q with ⟨i',j'⟩
  unfold Demand.trunks
  apply disjoint_union_left.mpr
  constructor <;> apply disjoint_union_right.mpr
  · constructor
    · apply T.port_disjoint (code_length width _) (code_length width _) lp positive depth
      by_cases first : i=i'
      · right
        intro e
        exact ne (Prod.ext first (code_injective width e))
      · exact Or.inl (fun e=>first (congrArg Prod.fst e))
    · apply T.port_disjoint (code_length width _) (code_length width _) lp positive depth
      exact Or.inl (by simp)
  · constructor
    · apply T.port_disjoint (code_length width _) (code_length width _) lp positive depth
      exact Or.inl (by simp)
    · apply T.port_disjoint (code_length width _) (code_length width _) lp positive depth
      by_cases second : j=j'
      · right
        intro e
        exact ne (Prod.ext (code_injective width e) second)
      · exact Or.inl (fun e=>second (congrArg Prod.fst e))

/-- One protected outgoing port and one protected incoming port for every
ordered pair of centers, indexed by different binary words in each tree. -/
noncomputable def demands := (univ : Finset (Fin m×Fin m)).toList.map (T.demand width positive depth)

theorem count_demands : (T.demands width positive depth).length=m^2 := by
  simp [demands,pow_two]

/-- Every ordered pair has a directed route of bounded length. Their supports
are pairwise disjoint, and each touches only its own protected port trunks. -/
theorem pack_pairs (lp : 0<l) (hk : 0<k) (fwd : Expands E k) (bwd : Expands (fun x y=>E y x) k)
    {M B : ℕ} (time : M=4*s+4*k*(Nat.log 2 (Fintype.card V)+1)) (volume : B=m^2*(M+1))
    (capacity : 2*k*((T.core (l+s)).card+B)≤(2^s-B)*2^s) (avail : 0<(2^s-B)*2^s) :
    ∃U,Packed E (T.core (l+s)) (2^s) (2^s) (2*s) M (T.demands width positive depth) U := by
  apply pack _ hk fwd bwd _ (by omega) _ capacity avail
  · apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun {p q} ne=>T.distinct_trunks width positive depth p q ne lp)
      (Finset.nodup_toList _)
  · rw [T.count_demands,volume]

end Forest
end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Forest.pack_pairs
