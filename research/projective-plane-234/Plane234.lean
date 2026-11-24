import Plane233
import Reader997
import PhysicalSkip997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
theorem plane57_threshold234 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (Y : Finset (Fin 57)) (hon : value (prefix997 C t) (bits Y) (head997 57 C t)=true)
    (hoff : ∀ Z : Finset (Fin 57), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 57 C t)=false) :
    234 ≤ C.size := by
  classical
  by_contra! bad
  let d := (Finset.univ.filter (fun i => Disjoint (plane57 i) Y)).card
  obtain ⟨hL,hH⟩ := threshold_bounds997 C plane57 o t ht hg (by decide : 2≤8) plane57_size plane57_linear hc Y hon hoff
  change Y.card+57*(min Y.card 8-1) ≤ C.size at hL
  change Y.card+(d*(8-1)+(57-d)) ≤ C.size at hH
  have num := plane57_disjoint_bound Y
  change 57 ≤ d+7*Y.card+1 at num
  have hdu : d ≤ 57 := (Finset.card_filter_le _ _).trans (by simp)
  have hnot5 : Y.card≠5 := by
    intro h5
    have full := full_one_row997 C plane57 o t ht hg plane57_linear hc Y (0 : Fin 57) hon (by omega) hoff
    simp only [h5,plane57_size] at full
    have eval : (∑ i : Fin 57, ((if i=0 then 8 else min 5 8)-1))=231 := by decide +kernel
    omega
  have hk : Y.card=4 := by omega
  have hd : d=28 := by omega
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0<Y.card)
  have hem := hoff ∅ (by simp [hk])
  by_cases read : ∃ j : Fin C.gates.length, t<j ∧ 57+t.val ∈ C.gates[j].inputs
  swap
  · have none (j : Fin C.gates.length) (hj : t<j) : 57+t.val ∉ C.gates[j].inputs :=
      fun h => read ⟨j,hj,h⟩
    have hmiss (i) : o i≠57+t.val := by
      intro he
      have hz : value C (bits (∅ : Finset (Fin 57))) (o i)=false := by simp [hc,bits]
      have hp := pin_on997 C t ht (bits (∅ : Finset (Fin 57))) false hem (o i)
      rw [he,pin_wire997] at hp
      exact Bool.false_ne_true ((he ▸ hz).symm.trans hp)
    have lowcomp : computes997 (pin997 C t false) plane57 o := by
      intro i x
      have eq := no_readers997 C t none x (o i) (hmiss i)
      have orig := pin_eval997 C t ht x (o i)
      cases hh : value (prefix997 C t) x (head997 57 C t) <;> simp only [hh,Bool.not_false,Bool.not_true] at orig
      · exact eq.trans (orig.symm.trans (hc i x))
      · exact orig.symm.trans (hc i x)
    have boom := monotone_full997 _ plane57 o (pin_mono997 C t hg false) plane57_size plane57_linear lowcomp
    rw [pin_size997] at boom
    omega
  obtain ⟨j,hj,hr⟩ := read
  have hupp : 57+j.val<57+C.size := Nat.add_lt_add_left j.isLt 57
  have hpos : 57+t.val<57+j.val := Nat.add_lt_add_left hj 57
  have nonempty (i) : (plane57 i).Nonempty := Finset.card_pos.mp (by rw [plane57_size];decide)
  have skip := reader_transparent997 C t j hj hg hr
  have ne := reader_not_output997 C plane57 o t j hj ht hg hr hc Y hon hem nonempty
  have cert := physical_sparse_skip997 C plane57 o t ht hg (by decide : 2≤8) plane57_size plane57_linear hc
    Y hon hoff _ hpos hupp skip ne y hy
  change C.size<Y.card+(8-2)+(d*(8-1)+(57-d)) → _ at cert
  obtain ⟨U,hu,shape,force⟩ := cert (by omega)
  change U.card+Y.card+(d*(8-1)+(57-d))+1 ≤ C.size at hu
  have huc : U.card ≤ 3 := by omega
  let D := insert y (U.biUnion id)
  let P := Finset.univ \ D
  have hYP : y ∉ P := by simp [P,D]
  have sep (T) (hT : T ∈ U) : Disjoint T P := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hw
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨T,hT,hp⟩))

  have geo := sparse_geometry57 U huc (by
    intro T hT
    rcases shape T hT with rfl|⟨i,_,rfl⟩|⟨p,_,rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inr ⟨i,rfl⟩
    · exact Or.inl (by simp))
  have hins := Finset.card_insert_le y (U.biUnion id)
  change D.card ≤ _ at hins
  have hco : P.card+D.card=57 := by
    simpa [P] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  have hquiet := force P hYP sep
  rcases geo with hsmall|⟨hsize,hthree⟩
  · have total := regional_total57 C o t ht hg hc Y P hon hoff hquiet
    omega
  · have total := three_gain57 C o t ht hg hc Y P hk hon hoff hquiet _ hthree
      (fun i hi => sep _ (Finset.mem_filter.mp hi).2)
    omega

theorem plane57_one_not_234 (C : Circuit) (o : Fin 57 → ℕ)
    (hops : ∀ g ∈ C.gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2)
    (hunique : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C plane57 o) : 234 ≤ C.size := by
  classical
  by_cases hnot : ∃ t : Fin C.gates.length, C.gates[t].op=.not
  · obtain ⟨t,ht⟩ := hnot
    have hg : others997 C t := by
      intro i hit
      obtain ⟨hop,hlen⟩ := hops C.gates[i] (List.getElem_mem _)
      exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun hn => False.elim (hit (hunique i t hn ht)))),hlen⟩
    let P := prefix997 C t
    let h := head997 57 C t
    let F := Finset.univ.filter (fun A : Finset (Fin 57) => value P (bits A) h = true)
    by_cases hF : F.Nonempty
    · obtain ⟨Y,hY,hmin⟩ := Finset.exists_min_image F Finset.card hF
      have hoff (Z : Finset (Fin 57)) (hz : Z.card < Y.card) : value P (bits Z) h = false := by
        apply Bool.eq_false_iff.mpr
        intro hon
        exact (not_le_of_gt hz) (hmin Z (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hon⟩))
      exact plane57_threshold234 C o t ht hg hc Y (Finset.mem_filter.mp hY).2 hoff
    · have off (x : Fin 57 → Bool) : value P x h = false := by
        apply Bool.eq_false_iff.mpr
        intro hx
        let X := Finset.univ.filter (fun p => x p=true)
        have he : bits X = x := by
          funext p
          cases hp : x p <;> simp [bits,X,hp]
        apply hF
        exact ⟨X,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hx⟩⟩
      have hh : computes997 (pin997 C t true) plane57 o := by
        intro i x
        have he := pin_on997 C t ht x false (off x) (o i)
        exact he.symm.trans (hc i x)
      have hb := monotone_full997 (pin997 C t true) plane57 o (pin_mono997 C t hg true) plane57_size plane57_linear hh
      simp only [pin_size997] at hb
      omega
  · have hmono : monoG C := by
      intro g hmem
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hmem
      obtain ⟨hop,hlen⟩ := hops C.gates[i] (List.getElem_mem _)
      exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun hn => False.elim (hnot ⟨⟨i,hi⟩,hn⟩))),hlen⟩
    have bound := monotone_full997 C plane57 o hmono plane57_size plane57_linear hc
    omega

#print axioms plane57_one_not_234
end PEqualNP.Outside.Window997
