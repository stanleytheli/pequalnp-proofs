import Mathlib
namespace GraphProbability.Hamiltonian
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutEdges (S : Finset V) :=
  (univ : Finset (V×V)).filter (fun e=>e.1∉S ∨ e.2∈S)

/-- A closed directed tour through an enumeration of every vertex exactly once.
The two distinguished ends allow a separate closing arc; suitable for orders ≥2. -/
def HasTour (E : Finset (V×V)) :=
  ∃ (a b : V) (middle : List V), ((a::middle)++[b]).Nodup ∧
    (∀ v,v∈(a::middle)++[b]) ∧ ((a::middle)++[b]).IsChain (fun x y=>(x,y)∈E) ∧ (b,a)∈E

private theorem tour_false (S : Finset V) (occupied : S.Nonempty) (outside : ∃ v,v∉S) :
    ¬HasTour (cutEdges S) := by
  rintro ⟨a,b,mid,_,all,chain,close⟩
  let rel (u v : V) := u∉S ∨ v∈S
  let : Trans rel rel rel := ⟨by intro x y z; dsimp [rel]; tauto⟩
  have path : ((a::mid)++[b]).IsChain rel := chain.imp (by intro x y h; simpa [cutEdges,rel] using h)
  have p:=path.pairwise
  have back : rel b a := by simpa [rel,cutEdges] using close
  obtain ⟨u,hu⟩:=occupied
  obtain ⟨v,hv⟩:=outside
  have ub : b∈S := by
    rcases List.mem_append.mp (all u) with h|h
    · have r := (List.pairwise_append.mp p).2.2 u h b (by simp)
      exact r.resolve_left (not_not.mpr hu)
    · simpa using (List.mem_singleton.mp h ▸ hu : b∈S)
  have ha : a∈S := back.resolve_left (not_not.mpr ub)
  change (a::(mid++[b])).Pairwise rel at p
  rcases List.mem_cons.mp (all v) with h|h
  · exact hv (h ▸ ha)
  · exact hv ((List.rel_of_pairwise_cons p h).resolve_left (not_not.mpr ha))

/-- Adding any missing arc restores a Hamiltonian tour. Start at its outside
endpoint, enumerate the rest of the outside, then the inside, and close. -/
theorem restore_arc (S : Finset V) (u v : V) (hu : u∈S) (hv : v∉S) (E : Finset (V×V))
    (contains : cutEdges S⊆E) (back : (u,v)∈E) : HasTour E := by
  classical
  let O := ((univ\S).erase v).toList
  let I := (S.erase u).toList
  have inO (w : V) : w∈O ↔ w≠v ∧ w∉S := by simp [O]
  have inI (w : V) : w∈I ↔ w≠u ∧ w∈S := by simp [I]
  have out (w : V) (h : w∈v::O) : w∉S := by
    rcases List.mem_cons.mp h with e|e
    · simpa [e] using hv
    · exact ((inO w).mp e).2
  have inside (w : V) (h : w∈I++[u]) : w∈S := by
    rcases List.mem_append.mp h with e|e
    · exact ((inI w).mp e).2
    · simpa [List.mem_singleton.mp e] using hu
  have od : (v::O).Nodup := List.nodup_cons.mpr ⟨by simp [O], Finset.nodup_toList _⟩
  have id : (I++[u]).Nodup := List.nodup_append'.mpr ⟨Finset.nodup_toList _,by simp,by
    intro w hw hw'
    exact ((inI w).mp hw).1 (List.mem_singleton.mp hw')⟩
  have dis : (v::O).Disjoint (I++[u]) := by
    intro z hz ht
    exact out z hz (inside z ht)
  have nd : ((v::O)++(I++[u])).Nodup := List.nodup_append'.mpr ⟨od,id,dis⟩
  have total (w : V) : w∈(v::O)++(I++[u]) := by
    by_cases ws : w∈S
    · apply List.mem_append_right
      by_cases wu : w=u
      · simp [wu]
      · exact List.mem_append_left _ ((inI w).mpr ⟨wu,ws⟩)
    · apply List.mem_append_left
      by_cases wv : w=v
      · simp [wv]
      · exact List.mem_cons_of_mem _ ((inO w).mpr ⟨wv,ws⟩)
  let rel (x y : V) := (x,y)∈E
  have withinO : (v::O).Pairwise rel := List.pairwise_of_forall_mem_list fun a ha b _ =>
    contains (by simp [cutEdges,out a ha])
  have withinI : (I++[u]).Pairwise rel := List.pairwise_of_forall_mem_list fun a _ b hb =>
    contains (by simp [cutEdges,inside b hb])
  have both : ((v::O)++(I++[u])).Pairwise rel := List.pairwise_append.mpr
    ⟨withinO,withinI,fun a ha b _=>contains (by simp [cutEdges,out a ha])⟩
  exact ⟨v,u,O++I,by simpa [List.append_assoc] using nd,
    fun w=>by simpa [List.append_assoc] using total w,by simpa [List.append_assoc] using both.isChain,back⟩

theorem tour_union (S T : Finset V) (hu : S.Nonempty) (hv : ∃ i,i∉S) (different : S≠T) :
    HasTour (cutEdges S ∪ cutEdges T) := by
  classical
  have crossing : ∃ u∈S,∃ v∉S,(u,v)∈cutEdges T := by
    by_contra! no
    have no' (u : V) (uS : u∈S) (v : V) (vS : v∉S) : u∈T ∧ v∉T := by
      simpa [cutEdges] using no u uS v vS
    apply different
    apply le_antisymm
    · intro w hw
      obtain ⟨v,hv⟩:=hv
      exact (no' _ hw _ hv).1
    · intro w hw
      by_contra ws
      obtain ⟨u,h⟩:=hu
      exact (no' _ h _ ws).2 hw
  obtain ⟨u,us,v,vs,arc⟩:=crossing
  exact restore_arc S u v us vs _ subset_union_left (mem_union_right _ arc)

theorem cut_has_no_tour (S : Finset V) (hu : S.Nonempty) (hv : ∃ v,v∉S) : ¬HasTour (cutEdges S) :=
  tour_false S hu hv
end GraphProbability.Hamiltonian
#print axioms GraphProbability.Hamiltonian.tour_union
