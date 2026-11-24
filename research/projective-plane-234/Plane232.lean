import PhysicalSparse997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
lemma sum_ground997 {m n} (S : Fin m → Finset (Fin n)) (P : Finset (Fin n)) :
    ∑ i, ((S i) ∩ P).card = ∑ p ∈ P, (Finset.univ.filter (fun i => p ∈ S i)).card := by
  classical
  calc
    _ = ∑ i, ∑ p ∈ P, (if p∈S i then 1 else 0 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_boole]
      congr 1
      ext p
      simp [and_comm]
    _ = ∑ p ∈ P, ∑ i, (if p∈S i then 1 else 0 : ℕ) := Finset.sum_comm
    _ = _ := by simp [Finset.sum_boole]

theorem regional_total57 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (Y P : Finset (Fin 57)) (hon : value (prefix997 C t) (bits Y) (head997 57 C t)=true)
    (hoff : ∀ Z : Finset (Fin 57), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 57 C t)=false)
    (hp : value (prefix997 C t) (bits P) (head997 57 C t)=false) :
    Y.card + 8*P.card ≤ C.size+57 := by
  have h := nested_first997 C plane57 o t ht hg plane57_linear hc Y P hon hoff hp
  have row (i) : ((plane57 i) ∩ P).card ≤ (max (min Y.card (plane57 i).card) ((plane57 i) ∩ P).card-1)+1 := by omega
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 57))) => row i)
  have hreg := sum_ground997 plane57 P
  change _ = ∑ p ∈ P, (incident57 p).card at hreg
  simp only [incident57_size,Finset.sum_const,smul_eq_mul] at hreg
  rw [hreg] at hs
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
  omega

theorem plane57_threshold232 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (Y : Finset (Fin 57)) (hon : value (prefix997 C t) (bits Y) (head997 57 C t)=true)
    (hoff : ∀ Z : Finset (Fin 57), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 57 C t)=false) :
    232 ≤ C.size := by
  classical
  by_contra! bad
  let d := (Finset.univ.filter (fun i => Disjoint (plane57 i) Y)).card
  obtain ⟨hL,hH⟩ := threshold_bounds997 C plane57 o t ht hg (by decide : 2≤8) plane57_size plane57_linear hc Y hon hoff
  change Y.card+57*(min Y.card 8-1) ≤ C.size at hL
  change Y.card+(d*(8-1)+(57-d)) ≤ C.size at hH
  have num := plane57_disjoint_bound Y
  change 57 ≤ d+7*Y.card+1 at num
  have hdu : d ≤ 57 := (Finset.card_filter_le _ _).trans (by simp)
  have hk : Y.card=4 := by omega
  have hd : d=28 := by omega
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0<Y.card)
  have cert := physical_sparse997 C plane57 o t ht hg (by decide : 2≤8) plane57_size plane57_linear hc Y hon hoff y hy
  change C.size<Y.card+(8-2)+(d*(8-1)+(57-d)) → _ at cert
  obtain ⟨U,hu,shape,force⟩ := cert (by omega)
  change U.card+Y.card+(d*(8-1)+(57-d)) ≤ C.size at hu
  have huc : U.card ≤ 2 := by omega
  let D := insert y (U.biUnion id)
  let P := Finset.univ \ D
  have hYP : y ∉ P := by simp [P,D]
  have sep (T) (hT : T ∈ U) : Disjoint T P := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hw
    exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨T,hT,hp⟩))
  have hsz (T) (hT : T ∈ U) : (id T).card ≤ 8 := by
    rcases shape T hT with rfl|⟨i,_,rfl⟩|⟨p,_,rfl⟩
    · simp
    · simp [plane57_size]
    · simp
  have h0 := Finset.card_biUnion_le_card_mul U id 8 hsz
  have h1 : D.card ≤ 17 := by
    have hh := Finset.card_insert_le y (U.biUnion id)
    change D.card ≤ _ at hh
    omega
  have h2 : P.card+D.card=57 := by
    simpa [P] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  have total := regional_total57 C o t ht hg hc Y P hon hoff (force P hYP sep)
  omega

theorem plane57_one_not_232 (C : Circuit) (o : Fin 57 → ℕ)
    (hops : ∀ g ∈ C.gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2)
    (hunique : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C plane57 o) : 232 ≤ C.size := by
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
      exact plane57_threshold232 C o t ht hg hc Y (Finset.mem_filter.mp hY).2 hoff
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

#print axioms plane57_one_not_232
end PEqualNP.Outside.Window997
