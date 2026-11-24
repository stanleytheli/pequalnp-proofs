import GateLeaves

namespace AlgebraicMeta.GateLeaves
open Finset Function

/-- At equality in the generic essential gate bound, there are no free scalar
leaves, unused gates, or wire fanouts. The statement applies to any method
that proves the required variable leaves occur in the root's dependency cone. -/
theorem saturated_cone {I V R W : Type*} [Fintype I] [Fintype W]
    (net : W → Gate V R W) (root : W) (labels : I ↪ V)
    (needed : ∀ i, ∃ w, Reach net root w ∧ net w=.var (labels i))
    (size : Fintype.card W+1=2*Fintype.card I) :
    (∀ w, Reach net root w) ∧
    (∀ w,(net w).binary=false → ∃ i,net w=.var (labels i)) ∧
    (∀ w, w≠root → ∃! p : W×Bool, (net p.1).binary=true ∧ (net p.1).operand root p.2=w) ∧
    (∀ p : W×Bool, (net p.1).binary=true → (net p.1).operand root p.2≠root) := by
  classical
  let live := univ.filter (Reach net root)
  let bins := live.filter (fun w => (net w).binary)
  let leaves := live \ bins
  have hb : bins ⊆ live := filter_subset _ _
  have liveRoot : root∈live := by simp [live,Relation.ReflTransGen.refl]
  choose pick hp using needed
  have leavesPick (i) : pick i∈leaves := by
    apply mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,(hp i).1⟩,?_⟩
    intro bad
    have e := (mem_filter.mp bad).2
    rw [(hp i).2] at e
    contradiction
  let pick' (i : I) : {w // w∈leaves} := ⟨pick i,leavesPick i⟩
  have inj : Injective pick' := by
    intro a b e
    have e' : pick a=pick b := congrArg Subtype.val e
    apply labels.injective
    exact Gate.var.inj ((hp a).2.symm.trans (e' ▸ (hp b).2))
  have lb : Fintype.card I ≤ leaves.card := by simpa using Fintype.card_le_of_injective pick' inj
  let ports := bins ×ˢ (univ : Finset Bool)
  let atPort (x : W × Bool) := (net x.1).operand root x.2
  have cover : live.erase root ⊆ ports.image atPort := by
    intro w hw
    obtain ⟨ne,hw⟩ := mem_erase.mp hw
    have reach := (mem_filter.mp hw).2
    cases reach with
    | refl => exact (ne rfl).elim
    | @tail t z lead step =>
      cases kg : net t with
      | var _ | scalar _ => rw [kg] at step;cases step
      | add a b | mul a b =>
        have tb : t∈bins := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,lead⟩,by rw [kg];rfl⟩
        rw [kg] at step
        rcases step with rfl|rfl
        · exact mem_image.mpr ⟨⟨t,false⟩,mem_product.mpr ⟨tb,mem_univ _⟩,by simp [atPort,kg,Gate.operand]⟩
        · exact mem_image.mpr ⟨⟨t,true⟩,mem_product.mpr ⟨tb,mem_univ _⟩,by simp [atPort,kg,Gate.operand]⟩
  have src := card_le_card cover
  have dst := card_image_le (s:=ports) (f:=atPort)
  have decomp : leaves.card+bins.card=live.card := card_sdiff_add_card_eq_card hb
  have big := card_le_univ live
  have pc : ports.card=bins.card*2 := by simp [ports]
  have ec : (live.erase root).card=live.card-1 := card_erase_of_mem liveRoot
  have all : live=univ := eq_of_subset_of_card_le (subset_univ _) (by rw [card_univ];omega)
  have allReach (w : W) : Reach net root w :=
    (mem_filter.mp (show w∈live by rw [all];exact mem_univ _)).2
  have allLeaves := ((Fintype.bijective_iff_injective_and_card pick').mpr
    ⟨inj,by simp only [Fintype.card_coe];omega⟩).2
  have portSet : live.erase root=ports.image atPort := eq_of_subset_of_card_le cover (by omega)
  have portInj : Set.InjOn atPort (↑ports : Set (W×Bool)) :=
    card_image_iff.mp (by omega)
  have inPorts (p : W×Bool) : p∈ports ↔ (net p.1).binary=true := by
    simp [ports,bins,all]
  refine ⟨allReach,?_,?_,?_⟩
  · intro w hw
    have leaf : w∈leaves := by simp [leaves,bins,all,hw]
    obtain ⟨i,hi⟩ := allLeaves ⟨w,leaf⟩
    have e : pick i=w := congrArg Subtype.val hi
    exact ⟨i,e ▸ (hp i).2⟩
  · intro w hw
    have has : w∈ports.image atPort := by rw [←portSet,all];simp [hw]
    obtain ⟨p,hp',ep⟩ := mem_image.mp has
    refine ⟨p,⟨(inPorts p).mp hp',ep⟩,?_⟩
    intro q hq
    exact portInj ((inPorts q).mpr hq.1) hp' (hq.2.trans ep.symm)
  · intro p hp' bad
    have has : root∈ports.image atPort := mem_image.mpr ⟨p,(inPorts p).mpr hp',bad⟩
    rw [←portSet] at has
    exact notMem_erase _ _ has

end AlgebraicMeta.GateLeaves
#print axioms AlgebraicMeta.GateLeaves.saturated_cone
