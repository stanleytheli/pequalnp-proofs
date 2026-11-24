import Plane232
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
theorem extra_full997 {m n} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (t : Fin C.gates.length) (ht : C.gates[t].op=.not) (hg : others997 C t)
    (hl : linear997 S) (hc : computes997 C S o) (Y P : Finset (Fin n)) (j : Fin m)
    (hon : value (prefix997 C t) (bits Y) (head997 n C t)=true)
    (hoff : ∀ Z : Finset (Fin n), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 n C t)=false)
    (hP : value (prefix997 C t) (bits P) (head997 n C t)=false) :
    Y.card + ∑ i, ((if i=j then (S i).card else max (min Y.card (S i).card) ((S i) ∩ P).card)-1) ≤ C.size := by
  classical
  let whole (i) := ((S i) ∩ P).card ≤ min Y.card (S i).card
  let D (i) := if i=j then P ∪ S i else if whole i then Finset.univ else P
  let K (i) := if i=j then (S i).card else if whole i then Y.card else (S i).card
  have chain (i l : Fin m) : D i ⊆ D l ∨ D l ⊆ D i := by
    by_cases hi : i=j <;> by_cases he : l=j <;> by_cases wi : whole i <;> by_cases wl : whole l <;> simp [D,hi,he,wi,wl]
  have below (Z : Finset (Fin n)) (hz : Z⊆P) : value (prefix997 C t) (bits Z) (head997 n C t)=false := by
    apply Bool.eq_false_iff.mpr
    intro hx
    exact Bool.false_ne_true (hP.symm.trans (mono_bits _ (prefix_mono997 C t hg) hz _ hx))
  have local_off (i) (Z : Finset (Fin n)) (hz : Z ⊆ D i) (hk : Z.card < K i) (hd : Disjoint Z (S i)) :
      value (prefix997 C t) (bits Z) (head997 n C t)=false := by
    by_cases he : i=j
    · apply below
      intro p hp
      have hs : p∈P ∪ S i := by simpa only [D,ite_eq_left he] using hz hp
      rcases Finset.mem_union.mp hs with h|h
      · exact h
      · exact False.elim (Finset.disjoint_left.mp hd hp h)
    · by_cases hw : whole i
      · exact hoff Z (by simpa [K,he,hw] using hk)
      · exact below Z (by simpa [D,he,hw] using hz)
  have total := chain_first997 C S D o K t ht hg hl hc Y hon hoff chain local_off
  convert total using 2
  apply Finset.sum_congr rfl
  intro i _
  by_cases he : i=j
  · simp [D,K,he]
  · by_cases hw : whole i
    · have hh : ((S i) ∩ P).card ≤ min Y.card (S i).card := hw
      simp [D,K,he,hw,max_eq_left hh]
    · have hh : min Y.card (S i).card ≤ ((S i) ∩ P).card := le_of_not_ge hw
      have hc' : ((S i) ∩ P).card ≤ (S i).card := Finset.card_le_card Finset.inter_subset_left
      simp [D,K,he,hw,max_eq_right hh,min_eq_right hc']

set_option maxHeartbeats 2000000 in
private theorem common_zero_line57 : ∀ i : Fin 57, (plane57 0 ∩ plane57 i).Nonempty := by decide +kernel

theorem common_line57 (i j : Fin 57) : (plane57 i ∩ plane57 j).Nonempty := by
  obtain ⟨p,hp⟩ := common_zero_line57 (j-i)
  obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hp
  exact ⟨p+i,Finset.mem_inter.mpr ⟨by simpa using (shift57 p 0 i).mpr h1,
    by simpa using (shift57 p (j-i) i).mpr h2⟩⟩

lemma line_inj57 : Function.Injective plane57 := by
  intro i j h
  by_contra hn
  have hh := plane57_linear i j hn
  rw [h,Finset.inter_self,plane57_size] at hh
  omega

lemma union_lines57 (U : Finset (Finset (Fin 57))) (hu : ∀ T ∈ U, ∃ i, T=plane57 i) :
    (U.biUnion id).card ≤ 7*U.card+1 := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert T U hT ih =>
    have hin := ih (fun V hV => hu V (Finset.mem_insert_of_mem hV))
    obtain ⟨i,rfl⟩ := hu T (Finset.mem_insert_self _ _)
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hT]
    by_cases hnon : U.Nonempty
    · obtain ⟨V,hV⟩ := hnon
      obtain ⟨j,rfl⟩ := hu V (Finset.mem_insert_of_mem hV)
      obtain ⟨p,hp⟩ := common_line57 i j
      obtain ⟨hi,hj⟩ := Finset.mem_inter.mp hp
      have hmem : p ∈ plane57 i ∩ U.biUnion id :=
        Finset.mem_inter.mpr ⟨hi,Finset.mem_biUnion.mpr ⟨_,hV,hj⟩⟩
      have hpos := Finset.card_pos.mpr (show (plane57 i ∩ U.biUnion id).Nonempty from ⟨p,hmem⟩)
      have hh := Finset.card_union_add_card_inter (plane57 i) (U.biUnion id)
      rw [plane57_size] at hh
      change ((plane57 i) ∪ U.biUnion id).card ≤ _
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnon]
      simp [plane57_size]

lemma sparse_geometry57 (U : Finset (Finset (Fin 57))) (hU : U.card ≤ 3)
    (shape : ∀ T ∈ U, T.card ≤ 1 ∨ ∃ i, T=plane57 i) :
    (U.biUnion id).card ≤ 19 ∨
    ((U.biUnion id).card ≤ 22 ∧ (Finset.univ.filter (fun i => plane57 i ∈ U)).card=3) := by
  classical
  let L := U.filter (fun T => ∃ i, T=plane57 i)
  let V := U \ L
  have hL : ∀ T ∈ L, ∃ i, T=plane57 i := fun _ h => (Finset.mem_filter.mp h).2
  have lv (T) (hT : T ∈ V) : (id T).card ≤ 1 := by
    have h := Finset.mem_sdiff.mp hT
    rcases shape T h.1 with hh|hh
    · exact hh
    · exact False.elim (h.2 (Finset.mem_filter.mpr ⟨h.1,hh⟩))
  have usub : U.biUnion id ⊆ L.biUnion id ∪ V.biUnion id := by
    intro p hp
    obtain ⟨T,hT,he⟩ := Finset.mem_biUnion.mp hp
    by_cases ht : T ∈ L
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨T,ht,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨T,Finset.mem_sdiff.mpr ⟨hT,ht⟩,he⟩)
  have h1 := (Finset.card_le_card usub).trans (Finset.card_union_le _ _)
  have h2 := union_lines57 L hL
  have h3 := Finset.card_biUnion_le_card_mul V id 1 lv
  simp only [mul_one] at h3
  have cardV := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun T => ∃ i, T=plane57 i) U)
  change V.card + L.card=U.card at cardV
  by_cases small : L.card≤2
  · exact Or.inl (by omega)
  · right
    have hL3 : L.card=3 := by omega
    refine ⟨by omega,?_⟩
    let I := Finset.univ.filter (fun i => plane57 i ∈ U)
    have him : I.image plane57=L := by
      ext T
      simp only [I,L,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,hi,rfl⟩
        exact ⟨hi,i,rfl⟩
      · rintro ⟨hT,i,rfl⟩
        exact ⟨i,hT,rfl⟩
    have hh := Finset.card_image_of_injective I line_inj57
    rw [him,hL3] at hh
    exact hh.symm

lemma three_gain57 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (Y P : Finset (Fin 57)) (hk : Y.card=4)
    (hon : value (prefix997 C t) (bits Y) (head997 57 C t)=true)
    (hoff : ∀ Z : Finset (Fin 57), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 57 C t)=false)
    (hp : value (prefix997 C t) (bits P) (head997 57 C t)=false)
    (I : Finset (Fin 57)) (hi : I.card=3) (hs : ∀ i ∈ I, Disjoint (plane57 i) P) :
    4+8*P.card+16 ≤ C.size+57 := by
  classical
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < I.card)
  let c (i : Fin 57) := (if i=j then (plane57 i).card else max (min Y.card (plane57 i).card) ((plane57 i) ∩ P).card)-1
  have bound := extra_full997 C plane57 o t ht hg plane57_linear hc Y P j hon hoff hp
  change Y.card+∑ i, c i ≤ C.size at bound
  have row (i : Fin 57) : ((plane57 i) ∩ P).card + (if i∈I then 4 else 0) + (if i=j then 4 else 0) ≤ c i+1 := by
    by_cases he : i=j
    · subst i
      have hem : plane57 j ∩ P = ∅ := Finset.disjoint_iff_inter_eq_empty.mp (hs j hj)
      simp [hem,c,hj,plane57_size]
    · by_cases hh : i∈I
      · have hem := Finset.disjoint_iff_inter_eq_empty.mp (hs i hh)
        simp [hem,c,hh,he,plane57_size,hk]
      · simp only [ite_eq_right he,ite_eq_right hh,add_zero,c,plane57_size,hk] 
        omega
  have summed := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 57))) => row i)
  have reg := sum_ground997 plane57 P
  change _ = ∑ p ∈ P, (incident57 p).card at reg
  simp only [incident57_size,Finset.sum_const,smul_eq_mul] at reg
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at summed
  rw [reg] at summed
  have hcI : (∑ i : Fin 57, if i∈I then 4 else 0 : ℕ)=12 := by simp [hi]
  have hcj : (∑ i : Fin 57, if i=j then 4 else 0 : ℕ)=4 := by simp
  rw [hcI,hcj] at summed
  omega

theorem plane57_threshold233 (C : Circuit) (o : Fin 57 → ℕ) (t : Fin C.gates.length)
    (ht : C.gates[t].op=.not) (hg : others997 C t) (hc : computes997 C plane57 o)
    (Y : Finset (Fin 57)) (hon : value (prefix997 C t) (bits Y) (head997 57 C t)=true)
    (hoff : ∀ Z : Finset (Fin 57), Z.card < Y.card → value (prefix997 C t) (bits Z) (head997 57 C t)=false) :
    233 ≤ C.size := by
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

theorem plane57_one_not_233 (C : Circuit) (o : Fin 57 → ℕ)
    (hops : ∀ g ∈ C.gates, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length ≤ 2)
    (hunique : ∀ i j : Fin C.gates.length, C.gates[i].op=.not → C.gates[j].op=.not → i=j)
    (hc : computes997 C plane57 o) : 233 ≤ C.size := by
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
      exact plane57_threshold233 C o t ht hg hc Y (Finset.mem_filter.mp hY).2 hoff
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

#print axioms plane57_one_not_233
end PEqualNP.Outside.Window997
