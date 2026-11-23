import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_516_aux

def Next {W : ℕ} (w : Finset (BitVec W)) (z : BitVec W) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨
    (∃ a ∈ w, ∃ b ∈ w, a ≠ b ∧ (z = a &&& b ∨ z = a ||| b))

def Reach {W : ℕ} (w : Finset (BitVec W)) : ℕ → BitVec W → Prop
  | 0, t => t ∈ w
  | j + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧
      z ≠ ~~~(0 : BitVec W) ∧ Next w z ∧ Reach (insert z w) j t

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

def cand (ws : List (BitVec W)) : List (BitVec W) :=
  let raw := ws.map (fun a => ~~~a) ++
    ws.flatMap (fun a => ws.flatMap fun b => [a &&& b, a ||| b])
  raw.eraseDups.filter fun z => !(ws.contains z) && z != 0 && z != ~~~(0 : BitVec W)

theorem cand_complete {ws : List (BitVec W)} {z : BitVec W}
    (h : Next ws.toFinset z) (hn : z ∉ ws)
    (h0 : z ≠ 0) (h1 : z ≠ ~~~(0 : BitVec W)) : z ∈ cand ws := by
  simp only [cand, List.mem_filter, List.mem_eraseDups, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, by simp [hn]; exact ⟨h0, by simpa using h1⟩⟩
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, _, hab | hab⟩
  · exact Or.inl ⟨a, List.mem_toFinset.mp ha, rfl⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inl hab⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inr hab⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

theorem next_mono {w v : Finset (BitVec W)} {z : BitVec W}
    (hw : w ⊆ v) (h : Next w z) : Next v z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact Or.inl ⟨a, hw ha, hz⟩
  · exact Or.inr ⟨a, hw ha, b, hw hb, hab, hz⟩

theorem reach_succ {w : Finset (BitVec W)} {j : ℕ} {t : BitVec W}
    (h : Reach w j t) : Reach w (j+1) t := by
  induction j generalizing w with
  | zero => exact Or.inl h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl ht
    · exact Or.inr ⟨z, hzw, hz0, hz1, hnext, ih hr⟩

theorem reach_mono {w v : Finset (BitVec W)} {j : ℕ} {t : BitVec W}
    (hw : w ⊆ v) (h : Reach w j t) : Reach v j t := by
  induction j generalizing w v with
  | zero => exact hw h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl (hw ht)
    · by_cases hzv : z ∈ v
      · exact reach_succ (ih (Finset.insert_subset hzv hw) hr)
      · exact Or.inr ⟨z, hzv, hz0, hz1, next_mono hw hnext,
          ih (Finset.insert_subset_insert _ hw) hr⟩

private theorem next_small {w : Finset (BitVec W)} {z : BitVec W}
    (h : Next w z) : ∃ p ⊆ w, p.card ≤ 2 ∧ Next p z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact ⟨{a}, by simpa, by simp, Or.inl ⟨a, by simp, hz⟩⟩
  · refine ⟨{a,b}, ?_, ?_, Or.inr ⟨a, by simp, b, by simp, hab, hz⟩⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    · simp [hab]

theorem reach_support {w : Finset (BitVec W)} {k : ℕ} {t : BitVec W}
    (h : Reach w k t) : ∃ u ⊆ w, u.card ≤ k+1 ∧ Reach u k t := by
  induction k generalizing w with
  | zero => exact ⟨{t}, Finset.singleton_subset_iff.mpr h, by simp, Finset.mem_singleton_self _⟩
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hn, hr⟩
    · exact ⟨{t}, Finset.singleton_subset_iff.mpr ht, by simp, Or.inl (Finset.mem_singleton_self _)⟩
    · obtain ⟨u, hus, hcard, hu⟩ := ih hr
      by_cases hzu : z ∈ u
      · obtain ⟨p, hpw, hpcard, hpnext⟩ := next_small hn
        let v := u.erase z ∪ p
        have hvw : v ⊆ w := by
          intro x hx
          rcases Finset.mem_union.mp hx with he | hp
          · obtain ⟨hne,hxu⟩ := Finset.mem_erase.mp he
            exact (Finset.mem_insert.mp (hus hxu)).resolve_left hne
          · exact hpw hp
        have huv : u ⊆ insert z v := by
          intro x hx
          by_cases he : x = z
          · exact Finset.mem_insert.mpr (Or.inl he)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hx⟩)))
        have hvsize := Finset.card_union_le (u.erase z) p
        have herase := Finset.card_erase_of_mem hzu
        have hpositive : 0 < u.card := Finset.card_pos.mpr ⟨z,hzu⟩
        refine ⟨v, hvw, ?_, Or.inr ⟨z, fun hz => hzw (hvw hz), hz0, hz1,
            next_mono (Finset.subset_union_right : p ⊆ v) hpnext, reach_mono huv hu⟩⟩
        dsimp [v]
        omega
      · refine ⟨u, ?_, by omega, reach_succ hu⟩
        intro x hx
        rcases Finset.mem_insert.mp (hus hx) with he | hw
        · exact False.elim (hzu (he ▸ hx))
        · exact hw

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

def sepBlock : List (BitVec W) → BitVec W → BitVec W → Bool
  | [], b, t => (b &&& t == 0) || (b &&& ~~~t == 0)
  | w :: ws, b, t =>
    if (b &&& t == 0) || (b &&& ~~~t == 0) then true
    else sepBlock ws (b &&& w) t && sepBlock ws (b &&& ~~~w) t

def sep (ws : List (BitVec W)) (t : BitVec W) : Bool :=
  sepBlock ws (~~~(0 : BitVec W)) t

theorem reach_row {w : Finset (BitVec W)} {k : ℕ} {t : BitVec W}
    (h : Reach w k t) (i j : Fin W)
    (eqw : ∀ a ∈ w, a.getLsbD i.val = a.getLsbD j.val) :
    t.getLsbD i.val = t.getLsbD j.val := by
  induction k generalizing w with
  | zero => exact eqw t h
  | succ k ih =>
    rcases h with ht | ⟨z, _, _, _, hn, hr⟩
    · exact eqw t ht
    · apply ih hr
      intro wire hwire
      rcases Finset.mem_insert.mp hwire with rfl | hw
      · rcases hn with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, _, hz | hz⟩
        · simp only [hz, BitVec.getLsbD_not, i.isLt, j.isLt, eqw a ha]
        · simp only [hz, BitVec.getLsbD_and, eqw a ha, eqw b hb]
        · simp only [hz, BitVec.getLsbD_or, eqw a ha, eqw b hb]
      · exact eqw wire hw

private def sameBlock (ws : List (BitVec W)) (b t : BitVec W) : Prop :=
  ∀ i j : Fin W, b.getLsbD i = true → b.getLsbD j = true →
    (∀ a ∈ ws, a.getLsbD i = a.getLsbD j) → t.getLsbD i = t.getLsbD j

private theorem sepBlock_complete {ws : List (BitVec W)} {b t : BitVec W}
    (h : sameBlock ws b t) : sepBlock ws b t = true := by
  induction ws generalizing b with
  | nil =>
    by_cases hpos : ∃ i : Fin W, b.getLsbD i = true ∧ t.getLsbD i = true
    · obtain ⟨i, hbi, hti⟩ := hpos
      have hz : b &&& ~~~t = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        by_cases hbj : b.getLsbD j = true
        · have hsame := h i ⟨j,hj⟩ hbi hbj (by simp)
          have htj : t.getLsbD j = true := hsame.symm.trans hti
          simp [hj, htj]
        · simp [Bool.eq_false_iff.mpr hbj]
      simp [sepBlock, hz]
    · have hz : b &&& t = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        by_cases hbj : b.getLsbD j = true
        · have htj : t.getLsbD j ≠ true := fun ht => hpos ⟨⟨j,hj⟩, hbj, ht⟩
          simp [Bool.eq_false_iff.mpr htj]
        · simp [Bool.eq_false_iff.mpr hbj]
      simp [sepBlock, hz]
  | cons a ws ih =>
    simp only [sepBlock]
    split
    · rfl
    · rw [Bool.and_eq_true]
      constructor
      · apply ih
        intro i j hi hj hrest
        have hi' : b.getLsbD i = true ∧ a.getLsbD i = true := by simpa using hi
        have hj' : b.getLsbD j = true ∧ a.getLsbD j = true := by simpa using hj
        apply h i j hi'.1 hj'.1
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hi'.2.trans hj'.2.symm
        · exact hrest z hz
      · apply ih
        intro i j hi hj hrest
        have hi' : b.getLsbD i = true ∧ a.getLsbD i = false := by simpa [i.isLt] using hi
        have hj' : b.getLsbD j = true ∧ a.getLsbD j = false := by simpa [j.isLt] using hj
        apply h i j hi'.1 hj'.1
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hi'.2.trans hj'.2.symm
        · exact hrest z hz

theorem reach_sep {ws : List (BitVec W)} {k : ℕ} {t : BitVec W}
    (h : Reach ws.toFinset k t) : sep ws t = true := by
  apply sepBlock_complete
  intro i j _ _ hrow
  exact reach_row h i j fun a ha => hrow a (List.mem_toFinset.mp ha)

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

theorem reach_advance {ws : List (BitVec W)} {k : ℕ} {t : BitVec W}
    (h : Reach ws.toFinset (k+1) t) (hw : ws.Nodup) (ht : t ∉ ws) :
    ∃ z ∈ cand ws, ∃ us ∈ List.sublistsLen (min (k+1) (z::ws).length) (z::ws),
      us.Nodup ∧ Reach us.toFinset k t ∧ sep us t = true := by
  rcases h with hnow | ⟨z, hzw, hz0, hz1, hn, hr⟩
  · exact False.elim (ht (List.mem_toFinset.mp hnow))
  · have hz : z ∉ ws := by simpa using hzw
    have hw' : (z :: ws).Nodup := List.nodup_cons.mpr ⟨hz,hw⟩
    have hr' : Reach (z :: ws).toFinset k t := by simpa using hr
    obtain ⟨u, hsub, hsmall, hur⟩ := reach_support hr'
    let size := min (k+1) (z::ws).length
    have hle : u.card ≤ size :=
      le_min hsmall ((Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup hw'))
    have hlen : size ≤ (z::ws).toFinset.card := by
      rw [List.toFinset_card_of_nodup hw']
      exact min_le_right _ _
    obtain ⟨v, huv, hvw, hvcard⟩ := Finset.exists_subsuperset_card_eq hsub hle hlen
    let us := (z::ws).filter (fun a => a ∈ v)
    have hsubl : List.Sublist us (z::ws) := List.filter_sublist
    have hus : us.toFinset = v := by
      ext a
      simp only [us, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hvw ha),ha⟩⟩
    have hd : us.Nodup := hsubl.nodup hw'
    have huslen : us.length = size := by
      rw [← List.toFinset_card_of_nodup hd, hus]
      exact hvcard
    have husreach : Reach us.toFinset k t := by
      rw [hus]
      exact reach_mono huv hur
    exact ⟨z, cand_complete hn hz hz0 hz1, us,
      List.mem_sublistsLen.mpr ⟨hsubl,huslen⟩, hd, husreach, reach_sep husreach⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

def mixedMask (b t : BitVec W) : Bool :=
  (b &&& t != 0) && (b &&& ~~~t != 0)

def mixedBlocks : List (BitVec W) → BitVec W → List (BitVec W)
  | [], t => if mixedMask (~~~0) t then [~~~0] else []
  | a :: ws, t =>
    (mixedBlocks ws t).flatMap fun b => [b &&& a, b &&& ~~~a].filter fun p => mixedMask p t

def compatibleMask (b z t : BitVec W) : Bool :=
  let d := z ^^^ t
  (b &&& d == 0) || (b &&& ~~~d == 0)

def groupCheck (w : List (BitVec W)) (k : ℕ) (t : BitVec W)
    (cover : List (BitVec W) → Bool) : Bool :=
  let take := min (k+1) (w.length+1)
  ((List.sublistsLen take w).all fun u => if (mixedBlocks u t).isEmpty then cover u else true) &&
  ((List.sublistsLen (take-1) w).all fun u =>
    let bs := mixedBlocks u t
    (cand w).all fun z => if bs.all (fun b => compatibleMask b z t) then cover (z::u) else true)

private def fixedRows (ws : List (BitVec W)) (b : BitVec W) : Prop :=
  ∀ i j : Fin W, b.getLsbD i = true → b.getLsbD j = true →
    ∀ a ∈ ws, a.getLsbD i = a.getLsbD j

private theorem block_info {ws : List (BitVec W)} {b t : BitVec W} (hb : b ∈ mixedBlocks ws t) :
    mixedMask b t = true ∧ fixedRows ws b := by
  induction ws generalizing b with
  | nil =>
    simp only [mixedBlocks] at hb
    split at hb
    next hm =>
      obtain rfl := List.mem_singleton.mp hb
      exact ⟨hm, fun _ _ _ _ _ ha => False.elim (List.not_mem_nil ha)⟩
    next => exact False.elim (List.not_mem_nil hb)
  | cons a ws ih =>
    obtain ⟨m, hmem, hpart⟩ := List.mem_flatMap.mp hb
    obtain ⟨hp, hmixed⟩ := List.mem_filter.mp hpart
    have hold := (ih hmem).2
    refine ⟨hmixed,?_⟩
    intro i j hi hj e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · have h1 : m.getLsbD i = true ∧ a.getLsbD i = true := by simpa using hi
      have h2 : m.getLsbD j = true ∧ a.getLsbD j = true := by simpa using hj
      rcases List.mem_cons.mp he with rfl | he
      · exact h1.2.trans h2.2.symm
      · exact hold i j h1.1 h2.1 e he
    · have h1 : m.getLsbD i = true ∧ a.getLsbD i = false := by simpa [i.isLt] using hi
      have h2 : m.getLsbD j = true ∧ a.getLsbD j = false := by simpa [j.isLt] using hj
      rcases List.mem_cons.mp he with rfl | he
      · exact h1.2.trans h2.2.symm
      · exact hold i j h1.1 h2.1 e he

private theorem posRow {b : BitVec W} (h : b ≠ 0) : ∃ i : Fin W, b.getLsbD i = true := by
  by_contra hn
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hfalse : b.getLsbD i = false := Bool.eq_false_iff.mpr (fun htrue => hn ⟨⟨i,hi⟩,htrue⟩)
  simp [hfalse]

private theorem oppositeRows {b t : BitVec W} (h : mixedMask b t = true) :
    ∃ i j : Fin W, b.getLsbD i = true ∧ b.getLsbD j = true ∧
      t.getLsbD i = false ∧ t.getLsbD j = true := by
  simp [mixedMask] at h
  obtain ⟨i,hi⟩ := posRow h.2
  obtain ⟨j,hj⟩ := posRow h.1
  have hi' : b.getLsbD i = true ∧ t.getLsbD i = false := by simpa [i.isLt] using hi
  have hj' : b.getLsbD j = true ∧ t.getLsbD j = true := by simpa using hj
  exact ⟨i,j,hi'.1,hj'.1,hi'.2,hj'.2⟩

private theorem no_mixed_reach {ws : List (BitVec W)} {t : BitVec W} {k : ℕ}
    (hr : Reach ws.toFinset k t) : mixedBlocks ws t = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b hb
  obtain ⟨hm,hs⟩ := block_info hb
  obtain ⟨i,j,hbi,hbj,hti,htj⟩ := oppositeRows hm
  have h := reach_row hr i j (fun a ha => hs i j hbi hbj a (List.mem_toFinset.mp ha))
  exact Bool.false_ne_true (hti.symm.trans (h.trans htj))

private theorem compatible_const {b z t : BitVec W} (c : Bool)
    (h : ∀ i : Fin W, b.getLsbD i = true → (z ^^^ t).getLsbD i = c) :
    compatibleMask b z t = true := by
  cases c with
  | false =>
    have he : b &&& (z ^^^ t) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hb : b.getLsbD i = true
      · simp only [BitVec.getLsbD_and, h ⟨i,hi⟩ hb, Bool.and_false]
        simp
      · simp [Bool.eq_false_iff.mpr hb]
    simp [compatibleMask,he]
  | true =>
    have he : b &&& ~~~(z ^^^ t) = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hb : b.getLsbD i = true
      · simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,h ⟨i,hi⟩ hb]
        simp
      · simp [Bool.eq_false_iff.mpr hb]
    simp [compatibleMask,he]

private theorem compatible_reach {ws : List (BitVec W)} {b z t : BitVec W} {k : ℕ}
    (hr : Reach (z::ws).toFinset k t) (hb : b ∈ mixedBlocks ws t) :
    compatibleMask b z t = true := by
  obtain ⟨hm,hs⟩ := block_info hb
  obtain ⟨i,j,hbi,hbj,hti,htj⟩ := oppositeRows hm
  have same (a d : Fin W) (ha : b.getLsbD a = true) (hd : b.getLsbD d = true)
      (hz : z.getLsbD a = z.getLsbD d) : t.getLsbD a = t.getLsbD d := by
    apply reach_row hr a d
    intro y hy
    rcases List.mem_cons.mp (List.mem_toFinset.mp hy) with rfl | hy
    · exact hz
    · exact hs a d ha hd y hy
  have hne : z.getLsbD i ≠ z.getLsbD j := by
    intro he
    have hc := same i j hbi hbj he
    exact Bool.false_ne_true (hti.symm.trans (hc.trans htj))
  apply compatible_const (z.getLsbD i)
  intro a ha
  simp only [BitVec.getLsbD_xor]
  by_cases hei : z.getLsbD a = z.getLsbD i
  · have hta := (same a i ha hbi hei).trans hti
    rw [hta,hei]
    exact Bool.xor_false _
  · have hej : z.getLsbD a = z.getLsbD j := by
      cases h1 : z.getLsbD a <;> cases h2 : z.getLsbD i <;> cases h3 : z.getLsbD j <;> simp_all
    have hta := (same a j ha hbj hej).trans htj
    cases h1 : z.getLsbD a <;> cases h2 : z.getLsbD i <;> simp_all

theorem groupCheck_sound {w : List (BitVec W)} {k : ℕ} {t : BitVec W}
    {cover : List (BitVec W) → Bool} (hr : Reach w.toFinset (k+1) t)
    (hd : w.Nodup) (ht : t ∉ w) (hg : groupCheck w k t cover = true) :
    ∃ u, cover u = true ∧ Reach u.toFinset k t := by
  obtain ⟨z,hz,us,hus,_,hu,_⟩ := reach_advance hr hd ht
  simp only [groupCheck, Bool.and_eq_true] at hg
  have htake : 0 < min (k+1) (w.length+1) := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero htake.ne'
  simp only [List.length_cons, hn, List.sublistsLen_succ_cons, List.mem_append, List.mem_map] at hus
  rcases hus with halone | ⟨u,hmem,he⟩
  · have hc := List.all_eq_true.mp hg.1 us (hn ▸ halone)
    exact ⟨us, by simpa [no_mixed_reach hu] using hc, hu⟩
  · subst us
    have hmem' : u ∈ List.sublistsLen (min (k+1) (w.length+1)-1) w := by simpa [hn] using hmem
    have hpass : (mixedBlocks u t).all (fun b => compatibleMask b z t) = true :=
      List.all_eq_true.mpr (fun b hb => compatible_reach hu hb)
    have hc := List.all_eq_true.mp (List.all_eq_true.mp hg.2 u hmem') z hz
    exact ⟨z::u, by simpa only [hpass,ite_true] using hc, hu⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

inductive MergeReach : Finset (BitVec W) → BitVec W → Prop where
  | done {s t} : t ∈ s → MergeReach s t
  | step {s t a b z} : a ∈ s → b ∈ s → a ≠ b → (z = a &&& b ∨ z = a ||| b) →
      MergeReach (insert z ((s.erase a).erase b)) t → MergeReach s t

theorem reach_support_merge {w : Finset (BitVec W)} {k : ℕ} {t : BitVec W}
    (h : Reach w k t) : ∃ u ⊆ w, u.card ≤ k+1 ∧ Reach u k t ∧
      (u.card = k+1 → MergeReach u t) := by
  induction k generalizing w with
  | zero =>
    exact ⟨{t},Finset.singleton_subset_iff.mpr h,by simp,by simpa [Reach],fun _ => .done (by simp)⟩
  | succ j ih =>
    rcases h with ht | ⟨z,hzw,hz0,hz1,hn,hr⟩
    · exact ⟨{t},Finset.singleton_subset_iff.mpr ht,by simp,Or.inl (by simp),fun _ => .done (by simp)⟩
    obtain ⟨u,hus,hcard,hu,htree⟩ := ih hr
    by_cases hzu : z ∈ u
    · let e := u.erase z
      have he : e ⊆ w := by
        intro a ha
        obtain ⟨haz,hau⟩ := Finset.mem_erase.mp ha
        exact (Finset.mem_insert.mp (hus hau)).resolve_left haz
      have heu : insert z e = u := Finset.insert_erase hzu
      have hecard : e.card + 1 = u.card := Finset.card_erase_add_one hzu
      have hbuild (v : Finset (BitVec W)) (hew : e ⊆ v) (hvw : v ⊆ w) (hnext : Next v z) :
          Reach v (j+1) t :=
        Or.inr ⟨z,fun hz => hzw (hvw hz),hz0,hz1,hnext,
          reach_mono (by rw [← heu]; exact Finset.insert_subset_insert _ hew) hu⟩
      rcases hn with ⟨a,ha,hz⟩ | ⟨a,ha,b,hb,hab,hz⟩
      · let v := insert a e
        have hvw : v ⊆ w := Finset.insert_subset ha he
        have hvcard : v.card ≤ e.card+1 := Finset.card_insert_le _ _
        refine ⟨v,hvw,by omega,hbuild v (Finset.subset_insert _ _) hvw (Or.inl ⟨a,by simp [v],hz⟩),?_⟩
        omega
      · let v := insert a (insert b e)
        have hvw : v ⊆ w := Finset.insert_subset ha (Finset.insert_subset hb he)
        have hvcard : v.card ≤ (insert b e).card+1 := Finset.card_insert_le _ _
        have hbcard : (insert b e).card ≤ e.card+1 := Finset.card_insert_le _ _
        have ha' : a ∈ v := by simp [v]
        have hb' : b ∈ v := by simp [v]
        have huse : Reach v (j+1) t := hbuild v (fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)) hvw
          (Or.inr ⟨a,ha',b,hb',hab,hz⟩)
        refine ⟨v,hvw,by omega,huse,?_⟩
        intro hmax
        have hau : a ∉ insert b e := by
          intro hm
          have hh : v = insert b e := Finset.insert_eq_of_mem hm
          rw [hh] at hmax
          omega
        have hbu : b ∉ e := by
          intro hm
          rw [Finset.insert_eq_of_mem hm] at hvcard
          omega
        have hrest : (v.erase a).erase b = e := by
          rw [show v = insert a (insert b e) from rfl,Finset.erase_insert hau,Finset.erase_insert hbu]
        apply MergeReach.step ha' hb' hab hz
        rw [hrest,heu]
        exact htree (by omega)
    · refine ⟨u,?_,by omega,reach_succ hu,?_⟩
      · intro a ha
        exact (Finset.mem_insert.mp (hus ha)).resolve_left (fun he => hzu (he ▸ ha))
      · omega

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

private theorem selectSized {ws : List (BitVec W)} {u : Finset (BitVec W)} {n : Nat}
    (hsub : u ⊆ ws.toFinset) (hw : ws.Nodup) (hc : u.card ≤ n) (hn : n ≤ ws.length) :
    ∃ us ∈ List.sublistsLen n ws, u ⊆ us.toFinset := by
  have hlen : n ≤ ws.toFinset.card := by simpa only [List.toFinset_card_of_nodup hw] using hn
  obtain ⟨v, huv, hvw, hvcard⟩ := Finset.exists_subsuperset_card_eq hsub hc hlen
  let us := ws.filter (fun a => a ∈ v)
  have hsubl : List.Sublist us ws := List.filter_sublist
  have hus : us.toFinset = v := by
    ext a
    simp only [us, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hvw ha),ha⟩⟩
  have hd : us.Nodup := hsubl.nodup hw
  exact ⟨us, List.mem_sublistsLen.mpr ⟨hsubl, by rw [← List.toFinset_card_of_nodup hd,hus,hvcard]⟩, hus ▸ huv⟩

private theorem group_member {w : List (BitVec W)} {m q : ℕ} {t z : BitVec W}
    {cover : List (BitVec W) → Bool} {us : List (BitVec W)}
    (hg : groupCheck w m t cover = true) (hz : z ∈ cand w)
    (hus : us ∈ List.sublistsLen (min (m+1) (z::w).length) (z::w))
    (hu : Reach us.toFinset q t) : cover us = true := by
  simp only [groupCheck, Bool.and_eq_true] at hg
  have htake : 0 < min (m+1) (w.length+1) := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero htake.ne'
  simp only [List.length_cons, hn, List.sublistsLen_succ_cons, List.mem_append, List.mem_map] at hus
  rcases hus with halone | ⟨u,hmem,he⟩
  · have hc := List.all_eq_true.mp hg.1 us (hn ▸ halone)
    simpa [no_mixed_reach hu] using hc
  · subst us
    have hmem' : u ∈ List.sublistsLen (min (m+1) (w.length+1)-1) w := by simpa [hn] using hmem
    have hpass : (mixedBlocks u t).all (fun b => compatibleMask b z t) = true :=
      List.all_eq_true.mpr (fun b hb => compatible_reach hu hb)
    have hc := List.all_eq_true.mp (List.all_eq_true.mp hg.2 u hmem') z hz
    simpa only [hpass,ite_true] using hc

def tightGroupCheck (w : List (BitVec W)) (k : ℕ) (t : BitVec W)
    (ordinary tree : List (BitVec W) → Bool) : Bool :=
  groupCheck w (k-1) t ordinary &&
    (if k ≤ w.length then groupCheck w k t tree else true)

theorem tightGroup_sound {w : List (BitVec W)} {k : ℕ} {t : BitVec W}
    {ordinary tree : List (BitVec W) → Bool} (hk : 0 < k)
    (hr : Reach w.toFinset (k+1) t) (hd : w.Nodup) (ht : t ∉ w)
    (hg : tightGroupCheck w k t ordinary tree = true) :
    (∃ u, ordinary u = true ∧ Reach u.toFinset k t) ∨
      (∃ u, tree u = true ∧ MergeReach u.toFinset t) := by
  rcases hr with hn | ⟨z,hzw,hz0,hz1,hn,hr⟩
  · exact False.elim (ht (List.mem_toFinset.mp hn))
  have hz : z ∉ w := by simpa using hzw
  have hw : (z::w).Nodup := List.nodup_cons.mpr ⟨hz,hd⟩
  have hzmem := cand_complete hn hz hz0 hz1
  have hr' : Reach (z::w).toFinset k t := by simpa using hr
  obtain ⟨u,hsub,hcard,hreach,htree⟩ := reach_support_merge hr'
  have hull : u.card ≤ (z::w).length := (Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup hw)
  obtain ⟨ho,hg'⟩ := Bool.and_eq_true_iff.mp hg
  by_cases hsmall : u.card ≤ k
  · let n := min ((k-1)+1) (z::w).length
    obtain ⟨us,hs,hu⟩ := selectSized (n := n) hsub hw (le_min (by omega) hull) (min_le_right _ _)
    have hrus := reach_mono hu hreach
    exact Or.inl ⟨us,group_member ho hzmem hs hrus,hrus⟩
  · have hl : u.card = k+1 := by omega
    have hlw : k ≤ w.length := by simp only [List.length_cons] at hull; omega
    have hc : groupCheck w k t tree = true := by simpa only [hlw,ite_true] using hg'
    let n := min (k+1) (z::w).length
    have heq : n = u.card := by dsimp [n]; omega
    obtain ⟨us,hs,hu⟩ := selectSized (n := n) hsub hw (by omega) (min_le_right _ _)
    obtain ⟨hsu,hln⟩ := List.mem_sublistsLen.mp hs
    have hsame : u = us.toFinset := Finset.eq_of_subset_of_card_le hu (by rw [List.toFinset_card_of_nodup (hsu.nodup hw),hln,heq])
    have hrus := reach_mono hu hreach
    exact Or.inr ⟨us, group_member hc hzmem hs hrus, hsame ▸ htree hl⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

def PermutesRows {W : ℕ} (f : BitVec W → BitVec W) : Prop :=
  ∃ r : Fin W → Fin W, Function.Surjective r ∧
    ∀ (a : BitVec W) (i : Fin W), (f a).getLsbD i.val = a.getLsbD (r i).val

abbrev ShuffleOp (W : ℕ) := ℕ × BitVec W × BitVec W

def shuffleOne {W : ℕ} (op : ShuffleOp W) (x : BitVec W) : BitVec W :=
  let d := op.1
  let lo := op.2.1
  let hi := op.2.2
  (x &&& ~~~(lo ||| hi)) ||| ((x <<< d) &&& hi) ||| ((x >>> d) &&& lo)

private def shuffleSrc {W : ℕ} (op : ShuffleOp W) (j : ℕ) : ℕ :=
  if op.2.1.getLsbD j then op.1 + j else if op.2.2.getLsbD j then j-op.1 else j

abbrev ShuffleOK {W : ℕ} (op : ShuffleOp W) : Prop :=
  ∀ j : Fin W, (op.2.1.getLsbD j = true → op.2.2.getLsbD j = false) ∧
    (op.2.2.getLsbD j = true → op.1 ≤ j.val) ∧
    shuffleSrc op j < W ∧ shuffleSrc op (shuffleSrc op j) = j.val

private theorem shuffleOne_perm {W : ℕ} (op : ShuffleOp W) (h : ShuffleOK op) :
    PermutesRows (shuffleOne op) := by
  let r (i : Fin W) : Fin W := ⟨shuffleSrc op i, (h i).2.2.1⟩
  refine ⟨r, ?_, ?_⟩
  · intro i
    exact ⟨r i, Fin.ext (h i).2.2.2⟩
  · intro a i
    change (shuffleOne op a).getLsbD i = a.getLsbD (shuffleSrc op i)
    rcases h i with ⟨hdis,hlo,_,_⟩
    by_cases hl : op.2.1.getLsbD i = true
    · have hh := hdis hl
      simp only [shuffleOne, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, shuffleSrc, hl, hh, i.isLt]
      simp
    · have hlf := Bool.eq_false_iff.mpr hl
      by_cases hh : op.2.2.getLsbD i = true
      · have hge := Nat.not_lt_of_ge (hlo hh)
        simp only [shuffleOne, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, shuffleSrc, hlf, hh, i.isLt, hge]
        simp
      · have hhf := Bool.eq_false_iff.mpr hh
        simp only [shuffleOne, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
          BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, shuffleSrc, hlf, hhf, i.isLt]
        simp

def shuffleWord {W : ℕ} : List (ShuffleOp W) → BitVec W → BitVec W
  | [], x => x
  | op :: ops, x => shuffleWord ops (shuffleOne op x)

theorem shuffleWord_perm {W : ℕ} {ops : List (ShuffleOp W)}
    (h : ∀ op ∈ ops, ShuffleOK op) : PermutesRows (shuffleWord ops) := by
  induction ops with
  | nil => exact ⟨id, Function.surjective_id, fun _ _ => rfl⟩
  | cons op ops ih =>
    obtain ⟨r,hr,er⟩ := shuffleOne_perm op (h op (by simp))
    obtain ⟨s,hs,es⟩ := ih (fun o ho => h o (List.mem_cons_of_mem _ ho))
    refine ⟨r ∘ s, hr.comp hs, ?_⟩
    intro a i
    exact (es (shuffleOne op a) i).trans (er a (s i))

theorem reach_shuffle {W : ℕ} {f : BitVec W → BitVec W} (h : PermutesRows f)
    {w : Finset (BitVec W)} {k : ℕ} {t : BitVec W} (hr : Reach w k t) :
    Reach (w.image f) k (f t) := by
  obtain ⟨r,hs,hbit⟩ := h
  have hinj : Function.Injective f := by
    intro a b hab
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨j,hj⟩ := hs ⟨i,hi⟩
    have eq := congrArg (fun x : BitVec W => x.getLsbD j) hab
    simpa only [hbit, hj] using eq
  have h0 : f 0 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hzero (j : ℕ) : (0 : BitVec W).getLsbD j = false := by simp
    exact (hbit 0 ⟨i,hi⟩).trans ((hzero _).trans (hzero i).symm)
  have hnot (a : BitVec W) : f (~~~a) = ~~~(f a) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hri := (r ⟨i,hi⟩).isLt
    have ha := hbit a ⟨i,hi⟩
    have hh := hbit (~~~a) ⟨i,hi⟩
    simp only [BitVec.getLsbD_not, hi, hri, decide_true, Bool.true_and] at hh ⊢
    exact hh.trans (congrArg Bool.not ha.symm)
  have hand (a b : BitVec W) : f (a &&& b) = f a &&& f b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    calc
      _ = (a &&& b).getLsbD (r ⟨i,hi⟩) := hbit _ _
      _ = _ := by simp only [BitVec.getLsbD_and]; rw [hbit a ⟨i,hi⟩,hbit b ⟨i,hi⟩]
  have hor (a b : BitVec W) : f (a ||| b) = f a ||| f b := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    calc
      _ = (a ||| b).getLsbD (r ⟨i,hi⟩) := hbit _ _
      _ = _ := by simp only [BitVec.getLsbD_or]; rw [hbit a ⟨i,hi⟩,hbit b ⟨i,hi⟩]
  have h1 : f (~~~(0 : BitVec W)) = ~~~0 := by rw [hnot,h0]
  induction k generalizing w with
  | zero => exact Finset.mem_image_of_mem _ hr
  | succ k ih =>
    rcases hr with ht | ⟨z,hzw,hz0,hz1,hn,hsuf⟩
    · exact Or.inl (Finset.mem_image_of_mem _ ht)
    · have hznew : f z ∉ w.image f := by
        intro hm
        obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hm
        exact hzw (hinj he ▸ ha)
      have hnext : Next (w.image f) (f z) := by
        rcases hn with ⟨a,ha,hz⟩ | ⟨a,ha,b,hb,hab,hz⟩
        · exact Or.inl ⟨f a,Finset.mem_image_of_mem _ ha,hz ▸ hnot a⟩
        · refine Or.inr ⟨f a,Finset.mem_image_of_mem _ ha,f b,Finset.mem_image_of_mem _ hb,
            fun he => hab (hinj he),?_⟩
          rcases hz with hz | hz
          · exact Or.inl (hz ▸ hand a b)
          · exact Or.inr (hz ▸ hor a b)
      have htail := ih hsuf
      rw [Finset.image_insert] at htail
      exact Or.inr ⟨f z, hznew, fun he => hz0 (hinj (he.trans h0.symm)),
        fun he => hz1 (hinj (he.trans h1.symm)), hnext, htail⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

private def thetaMove01 : ShuffleOp 256 :=
  (1, 0x2222222222222222222222222222222222222222222222222222222222222222, 0x4444444444444444444444444444444444444444444444444444444444444444)

private def thetaMove23 : ShuffleOp 256 :=
  (4, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00)

private def thetaMove24 : ShuffleOp 256 :=
  (12, 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000)

private def thetaMove25 : ShuffleOp 256 :=
  (28, 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000)

private def thetaMove26 : ShuffleOp 256 :=
  (60, 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000)

private def thetaMove27 : ShuffleOp 256 :=
  (124, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000)

private def thetaMove34 : ShuffleOp 256 :=
  (8, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000)

private def thetaMove35 : ShuffleOp 256 :=
  (24, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000)

private def thetaMove36 : ShuffleOp 256 :=
  (56, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000)

private def thetaMove37 : ShuffleOp 256 :=
  (120, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000)

private def thetaMove45 : ShuffleOp 256 :=
  (16, 0xffff000000000000ffff000000000000ffff000000000000ffff0000, 0xffff000000000000ffff000000000000ffff000000000000ffff00000000)

private def thetaMove46 : ShuffleOp 256 :=
  (48, 0xffff0000ffff00000000000000000000ffff0000ffff0000, 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000)

private def thetaMove47 : ShuffleOp 256 :=
  (112, 0xffff0000ffff0000ffff0000ffff0000, 0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000)

private def thetaMove56 : ShuffleOp 256 :=
  (32, 0xffffffff000000000000000000000000ffffffff00000000, 0xffffffff000000000000000000000000ffffffff0000000000000000)

private def thetaMove57 : ShuffleOp 256 :=
  (96, 0xffffffff00000000ffffffff00000000, 0xffffffff00000000ffffffff00000000000000000000000000000000)

private def thetaMove67 : ShuffleOp 256 :=
  (64, 0xffffffffffffffff0000000000000000, 0xffffffffffffffff00000000000000000000000000000000)

def thetaPerms : List (List (ShuffleOp 256)) :=
  [[],
   [thetaMove46,thetaMove57],
   [thetaMove24,thetaMove35],
   [thetaMove24,thetaMove35,thetaMove26,thetaMove37],
   [thetaMove26,thetaMove37,thetaMove24,thetaMove35],
   [thetaMove26,thetaMove37],
   [thetaMove01,thetaMove23,thetaMove45,thetaMove67],
   [thetaMove01,thetaMove23,thetaMove47,thetaMove56],
   [thetaMove01,thetaMove25,thetaMove34,thetaMove67],
   [thetaMove01,thetaMove25,thetaMove34,thetaMove37,thetaMove26,thetaMove23],
   [thetaMove01,thetaMove27,thetaMove36,thetaMove34,thetaMove25,thetaMove45],
   [thetaMove01,thetaMove27,thetaMove36,thetaMove45]]

set_option maxRecDepth 16384 in
private theorem thetaMovesValid :
    thetaPerms.all (fun ops => ops.all (fun op => decide (ShuffleOK op))) = true := by
  decide +kernel

theorem theta_perm_ok {ops : List (ShuffleOp 256)} (h : ops ∈ thetaPerms) :
    PermutesRows (shuffleWord ops) := by
  apply shuffleWord_perm
  intro op hop
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp thetaMovesValid ops h) op hop)

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

abbrev PackedSlots := Nat × Nat × Array Nat
abbrev Layer := Nat × Nat × Array Nat × PackedSlots × PackedSlots

def slotVal (packed : PackedSlots) (i : Nat) : Nat :=
  let width := packed.2.1
  let count := max 1 (512 / width)
  let block := packed.2.2[i / count]?.getD 0
  (block >>> ((i % count) * width)) % (2^width)

def basisColumns : List (BitVec 256) :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def stateAt (alpha : Array (BitVec 256)) (lay : Layer) (i : Nat) : List (BitVec 256) :=
  let size := lay.1
  let width := lay.2.1
  let code := lay.2.2.1[i]?.getD 0
  let raw := (List.range 8).filterMap fun j =>
    if code.testBit j then basisColumns[j]? else none
  raw ++ (List.range (size - raw.length)).map fun j =>
    alpha[(code >>> (8 + width*j)) % (2^width)]?.getD 0

def stateCount (lay : Layer) : Nat := lay.2.2.1.size

def fingerprint (us : List (BitVec 256)) : Nat :=
  let p := 2^255 - 19
  (us.foldl (fun h a => h + ((a.toNat + 104729)^7 % p)) 0) % p

def findHint (us : List (BitVec 256)) (lay : Layer) (numPerms : Nat) : Nat × Nat :=
  let h := fingerprint us
  let d := lay.2.2.2.1
  let slots := lay.2.2.2.2
  let g := slotVal d (h % d.1)
  let packed := slotVal slots ((h / d.1 + g) % slots.1)
  (packed / numPerms, packed % numPerms)

def validHint (alpha : Array (BitVec 256)) (ps : List (List (ShuffleOp 256)))
    (lay : Layer) (us : List (BitVec 256)) (i g : Nat) : Bool :=
  if i < stateCount lay then
    if hg : g < ps.length then
      let rep := stateAt alpha lay i
      let f := shuffleWord ps[g]
      us.all fun a => rep.contains (f a)
    else false
  else false

def covers (alpha : Array (BitVec 256)) (ps : List (List (ShuffleOp 256))) (lay : Layer)
    (us : List (BitVec 256)) : Bool :=
  let h := findHint us lay ps.length
  validHint alpha ps lay us h.1 h.2

theorem validHint_sound {alpha : Array (BitVec 256)} {ps : List (List (ShuffleOp 256))}
    {lay : Layer} {us : List (BitVec 256)} {i g k : Nat} {t : BitVec 256}
    (valid : ∀ p ∈ ps, PermutesRows (shuffleWord p))
    (fixed : ∀ p ∈ ps, shuffleWord p t = t)
    (hc : validHint alpha ps lay us i g = true) (hr : Reach us.toFinset k t) :
    ∃ j < stateCount lay, Reach (stateAt alpha lay j).toFinset k t := by
  by_cases hi : i < stateCount lay
  · by_cases hg : g < ps.length
    · simp only [validHint,hi,hg,if_true,dif_pos] at hc
      have hp : ps[g] ∈ ps := List.getElem_mem hg
      have hh := reach_shuffle (valid _ hp) hr
      rw [fixed _ hp] at hh
      refine ⟨i,hi,reach_mono ?_ hh⟩
      intro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact List.mem_toFinset.mpr (by simpa using List.all_eq_true.mp hc b (List.mem_toFinset.mp hb))
    · simp [validHint,hi,hg] at hc
  · simp [validHint,hi] at hc

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

def alphabet : Array (BitVec 256) :=
  ([
0xffffffffffffffff,
   0xffffffff00000000ffffffff,
   0xffff0000ffff0000ffff0000ffff,
   0xffffffffffff0000ffffffffffff,
   0x33333333333333333333333333333333,
   0x33333333ffffffff33333333ffffffff,
   0x55555555555555555555555555555555,
   0x5555555555555555ffffffffffffffff,
   0x55555555ffffffff55555555ffffffff,
   0x5555ffff5555ffff5555ffff5555ffff,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00,
   0xffffffffffffffff0000000000000000,
   0xffffffffffffffffcccccccccccccccc,
   0xffffffffffffffffffffffffffffffff,
   0x333333333333333333333333333333333333333333333333,
   0x3333333333333333ffffffffffffffffffffffffffffffff,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xffffffffffffffff0000000000000000ffffffffffffffff,
   0xffffffffffffffffffffffffffffffffffffffffffffffff,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff,
   0xffffffff00000000ffffffffffffffffffffffffffffffffffffffff,
   0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,
   0x1111111111111111111111111111111111111111111111111111111111111111,
   0x1111111111111111111111111111111155555555555555555555555555555555,
   0x2222222222222222222222222222222222222222222222222222222222222222,
   0x22222222222222222222222222222222aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0x3030303030303030303030303030303030303030303030303030303030303030,
   0x30303030303030303030303030303030f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0x3030303030303030f0f0f0f0f0f0f0f03030303030303030f0f0f0f0f0f0f0f0,
   0x30f030f030f030f030f030f030f030f030f030f030f030f030f030f030f030f0,
   0x3300330033003300330033003300330033003300330033003300330033003300,
   0x33003300330033003300330033003300ff00ff00ff00ff00ff00ff00ff00ff00,
   0x3333333333333333333333333333333333333333333333333333333333333333,
   0x33333333333333333333333333333333ffffffffffffffffffffffffffffffff,
   0x3333333333333333ffffffffffffffff3333333333333333ffffffffffffffff,
   0x5555555555555555555555555555555555555555555555555555555555555555,
   0x7777777777777777777777777777777777777777777777777777777777777777,
   0x8080808080808080808080808080808080808080808080808080808080808080,
   0x8888888888888888888888888888888888888888888888888888888888888888,
   0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a000,
   0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000,
   0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a000000000,
   0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,
   0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0ffffffffffffffffffffffffffffffff,
   0xa0a0a0a0a0a0a0a0ffffffffffffffffa0a0a0a0a0a0a0a0ffffffffffffffff,
   0xa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ff,
   0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8,
   0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa0000000000,
   0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00,
   0xaa00aa00aa00aa00aa00aa00aa00aa00ffffffffffffffffffffffffffffffff,
   0xaa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88,
   0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0,
   0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,
   0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00,
   0xaaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00aaaaaaaaaa00aa00,
   0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa0000000000000000,
   0xaaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0aaaaaaaaaaaaaaaaaaaaa0a0aaaaa0a0,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa00000000000000000000000000000000,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffffffffffffffffff,
   0xaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffff,
   0xb0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0,
   0xb3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3b3,
   0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,
   0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,
   0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00,
   0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000,
   0xcccccccccccccccccccccccccccccccc00000000000000000000000000000000,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffff,
   0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0,
   0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea,
   0xeccceccceccceccceccceccceccceccceccceccceccceccceccceccceccceccc,
   0xececccccececccccececccccececccccececccccececccccececccccececcccc,
   0xececececccccccccececececccccccccececececccccccccececececcccccccc,
   0xecececececececececececececececececececececececececececececececec,
   0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa,
   0xeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeecec,
   0xeeeeeeeeeeeeeeeecccccccccccccccceeeeeeeeeeeeeeeecccccccccccccccc,
   0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee,
   0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000,
   0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000,
   0xf000f000f000f000f000f000f000f000ff00ff00ff00ff00ff00ff00ff00ff00,
   0xf000f000f000f000f000f000f000f000ffffffffffffffffffffffffffffffff,
   0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0,
   0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0,
   0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0,
   0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000,
   0xf0f00000f0f00000f0f00000f0f0000000000000000000000000000000000000,
   0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000,
   0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0,
   0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0,
   0xf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000,
   0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0,
   0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f000000000,
   0xf0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0f0f0f0f0a0a0a0a0,
   0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0,
   0xf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000,
   0xf0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0f0f0f0f0f0a0f0a0,
   0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000,
   0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f00000000000000000,
   0xf0f0f0f0f0f0f0f0f0f00000f0f00000f0f0f0f0f0f0f0f0f0f00000f0f00000,
   0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f000000000,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f000000000,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0ffffffffffffffffffffffffffffffff,
   0xf0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0ffffffffffffffff,
   0xf0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0ff,
   0xf333f333f333f333f333f333f333f333f333f333f333f333f333f333f333f333,
   0xf3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3f3,
   0xf5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5,
   0xf8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8f8,
   0xfaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaa,
   0xfaf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0faf0,
   0xfafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaa,
   0xfafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0,
   0xfafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaa,
   0xfafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0,
   0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,
   0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00,
   0xfcccccccfcccccccfcccccccfcccccccfcccccccfcccccccfcccccccfccccccc,
   0xfcccfcccccccccccfcccfcccccccccccfcccfcccccccccccfcccfccccccccccc,
   0xfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfccc,
   0xfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcecfcec,
   0xfcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0,
   0xfcfcccccfcfcccccccccccccccccccccfcfcccccfcfccccccccccccccccccccc,
   0xfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfccccc,
   0xfcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0,
   0xfcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0,
   0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,
   0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe,
   0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff0000000000,
   0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000,
   0xff00ff00ff00ff00ff00ff00ff00ff0000000000000000000000000000000000,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffff,
   0xff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33ff33,
   0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,
   0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,
   0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc,
   0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0fff0f0f0,
   0xfff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00,
   0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0,
   0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0,
   0xffffaaaaffffaaaaffff0000ffff0000ffffaaaaffffaaaaffff0000ffff0000,
   0xffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0,
   0xffffcc00ffffcc00ffffcc00ffffcc00ffffcc00ffffcc00ffffcc00ffffcc00,
   0xffffcccceeeeccccffffcccceeeeccccffffcccceeeeccccffffcccceeeecccc,
   0xffffccccffff0000ffffccccffff0000ffffccccffff0000ffffccccffff0000,
   0xffffccccffffccccffff0000ffff0000ffffccccffffccccffff0000ffff0000,
   0xffffccccffffccccffffccccffffccccffff0000ffff0000ffff0000ffff0000,
   0xfffff000fffff000fffff000fffff000fffff000fffff000fffff000fffff000,
   0xfffff0f0fffff0f0f0f0f0f0f0f0f0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0,
   0xfffff0f0fffff0f0fffff0f0fffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0,
   0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa,
   0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc,
   0xffffff00ffffff00ff00ff00ff00ff00ffffff00ffffff00ff00ff00ff00ff00,
   0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00,
   0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa,
   0xfffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0,
   0xffffffffaa00aa00ffffffffaa00aa00ffffffffaa00aa00ffffffffaa00aa00,
   0xffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000ffffffffaaaa0000,
   0xffffffffaaaaaaaaffffffff00000000ffffffffaaaaaaaaffffffff00000000,
   0xffffffffaaaaaaaaffffffffaaaaaaaaffffffff00000000ffffffff00000000,
   0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa,
   0xffffffffcc00cc00ffffffffcc00cc00ffffffffcc00cc00ffffffffcc00cc00,
   0xffffffffccccccccffffffffccccccccffffffff00000000ffffffff00000000,
   0xfffffffff000f000fffffffff000f000fffffffff000f000fffffffff000f000,
   0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,
   0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00,
   0xffffffffffffffff000000000000000000000000000000000000000000000000,
   0xffffffffffffffff0000000000000000aaaaaaaaaaaaaaaa0000000000000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffff0000000000000000fffffffffffffffff0f0f0f0f0f0f0f0,
   0xffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffff,
   0xffffffffffffffffa0a0a0a0a0a0a0a0ffffffffffffffffa0a0a0a0a0a0a0a0,
   0xffffffffffffffffaaaa0000aaaa0000ffffffffffffffffaaaa0000aaaa0000,
   0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa,
   0xffffffffffffffffc0c0c0c0c0c0c0c0ffffffffffffffffc0c0c0c0c0c0c0c0,
   0xffffffffffffffffcc00cc00cc00cc00ffffffffffffffffcc00cc00cc00cc00,
   0xffffffffffffffffccccccccccccccccaaaaaaaaaaaaaaaa0000000000000000,
   0xffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc,
   0xffffffffffffffffcccccccccccccccceeeeeeeeeeeeeeeecccccccccccccccc,
   0xffffffffffffffffccccccccccccccccffffffffffffffff0000000000000000,
   0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc,
   0xfffffffffffffffff000f000f000f000fffffffffffffffff000f000f000f000,
   0xfffffffffffffffff0a0f0a0f0a0f0a0fffffffffffffffff0a0f0a0f0a0f0a0,
   0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0,
   0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,
   0xffffffffffffffffffff000000000000ffffffffffffffffffff000000000000,
   0xffffffffffffffffffff0000aaaa0000ffffffffffffffffffff0000aaaa0000,
   0xffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffffffffffffffffcccc00000000ffffffffffffffffffffcccc00000000,
   0xfffffffffffffffffffff0f0fffff0f0fffffffffffffffffffff0f0fffff0f0,
   0xffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00,
   0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffffffffffff00000000ffffffffaaaaaaaaffffffff00000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000003333333333333333,
   0xffffffffffffffffffffffffffffffff0000000000000000ff00ff00ff00ff00,
   0xffffffffffffffffffffffffffffffff22222222222222222222222222222222,
   0xffffffffffffffffffffffffffffffff80808080808080808080808080808080,
   0xffffffffffffffffffffffffffffffff88008800880088008800880088008800,
   0xffffffffffffffffffffffffffffffff88888888888888880000000000000000,
   0xffffffffffffffffffffffffffffffffa000a000a000a000a000a000a000a000,
   0xffffffffffffffffffffffffffffffffa0a00000a0a00000a0a00000a0a00000,
   0xffffffffffffffffffffffffffffffffa0a0a0a000000000a0a0a0a000000000,
   0xffffffffffffffffffffffffffffffffa0a0a0a0a0a0a0a00000000000000000,
   0xffffffffffffffffffffffffffffffffa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,
   0xffffffffffffffffffffffffffffffffaa00aa0000000000aa00aa0000000000,
   0xffffffffffffffffffffffffffffffffaa00aa00aa00aa000000000000000000,
   0xffffffffffffffffffffffffffffffffaa00aa00aa00aa00aa00aa00aa00aa00,
   0xffffffffffffffffffffffffffffffffaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0,
   0xffffffffffffffffffffffffffffffffaaaa0000aaaa0000aaaa0000aaaa0000,
   0xffffffffffffffffffffffffffffffffaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0,
   0xffffffffffffffffffffffffffffffffaaaaaa00aaaaaa00aaaaaa00aaaaaa00,
   0xffffffffffffffffffffffffffffffffaaaaaaaaaa00aa00aaaaaaaaaa00aa00,
   0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa0000000000000000,
   0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaa0a0a0a0a0a0a0a0,
   0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaa00aa00aa00aa00,
   0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xffffffffffffffffffffffffffffffffc000c000c000c000c000c000c000c000,
   0xffffffffffffffffffffffffffffffffc0c0c0c000000000c0c0c0c000000000,
   0xffffffffffffffffffffffffffffffffcc00cc0000000000cc00cc0000000000,
   0xffffffffffffffffffffffffffffffffcc00cc00cc00cc000000000000000000,
   0xffffffffffffffffffffffffffffffffcc00cc00cc00cc00cc00cc00cc00cc00,
   0xffffffffffffffffffffffffffffffffcccccccc00000000cccccccc00000000,
   0xffffffffffffffffffffffffffffffffcccccccccc00cc00cccccccccc00cc00,
   0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc,
   0xffffffffffffffffffffffffffffffffee00ee00ee00ee00ee00ee00ee00ee00,
   0xfffffffffffffffffffffffffffffffff0000000f0000000f0000000f0000000,
   0xfffffffffffffffffffffffffffffffff000f00000000000f000f00000000000,
   0xfffffffffffffffffffffffffffffffff000f000f000f0000000000000000000,
   0xfffffffffffffffffffffffffffffffff000f000f000f000f000f000f000f000,
   0xfffffffffffffffffffffffffffffffff0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0,
   0xfffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xfffffffffffffffffffffffffffffffffa00fa00fa00fa00fa00fa00fa00fa00,
   0xfffffffffffffffffffffffffffffffffc00fc00fc00fc00fc00fc00fc00fc00,
   0xffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,
   0xffffffffffffffffffffffffffffffffffffcccc00000000ffffcccc00000000,
   0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000,
   0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
] : List (BitVec 256)).toArray

def level6 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (0, 9, ([] : List Nat).toArray,
   (1, 1, ([0x0] : List Nat).toArray),
   (1, 1, ([0x0] : List Nat).toArray))

def level7 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (7, 9, ([0x1e05c73, 0xc33f, 0x1fccf1f, 0x1f88375, 0x1d0c53d, 0x1a6c59d, 0x1889bad, 0x19a9ead] : List Nat).toArray,
   (41, 4, ([0x117f048102a0e0002675028074830002010003000] : List Nat).toArray),
   (102, 7, ([0x1ebe70280300e54574d204986fd0066e3645501357d1a64225cac65e0000980310001ea44f4000001390db04c1f473aaad220002600002ec2801183cfa431759, 0x95a8d5dd5804442a95d48abc6a0800001b2500002003e0259b] : List Nat).toArray))

def level8 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (8, 9, ([0x37f, 0x57f, 0x77f, 0x87f, 0x97f, 0xf7f, 0x5c2a101f, 0x9c2a103d, 0x2a103f, 0x6c2e1057, 0x702e105b, 0x9c2e105d, 0xa82e105e, 0x2e105f, 0x9c34106d, 0x34106f, 0xa84e107c, 0x4e107d, 0x54107e, 0xb41077, 0xb8107b, 0x1001077, 0x172103f, 0x107f, 0x176103f, 0x17a103f, 0x182103f, 0x184103f, 0x18c103f, 0x190103f, 0x15a105f, 0x15c105f, 0x15e105f, 0x160105f, 0x162105f, 0x166105f, 0x168105f, 0x16a105f, 0x1a4105f, 0x134106f, 0x136106f, 0x138106f, 0x13a106f, 0x13e106f, 0x140106f, 0x142106f, 0x144106f, 0x19c106f, 0xa4107d, 0xaa107d, 0x106107d, 0x188107d, 0xa6107e, 0xac107e, 0xf2107e, 0x17e107e, 0x11fd, 0x127f, 0x13fe, 0x14fb, 0x1efe, 0x20fe, 0x22fb, 0x23fb, 0x24fb, 0x26f7, 0x5427fc, 0x8827f9, 0xb827f9, 0x10027f5, 0x27fd, 0x1ae277d, 0x1be277d, 0x1c4277d, 0x1d0277d, 0x1e0277d, 0x1f0277d, 0x17a27bd, 0x18227bd, 0x18427bd, 0x18c27bd, 0x19027bd, 0xa627fc, 0xf227fc, 0x10031f3, 0x10631f9, 0x327f, 0x33bf, 0x34f7, 0x387f, 0x3ffe, 0x44fb, 0x45fd, 0x1e05977, 0x5af7, 0x5b7f, 0x5cfb, 0x1f25c7b, 0x1925cbb, 0x1245cf3, 0x16e5cf3, 0x5efb, 0x65fb, 0x6afb, 0xff, 0xd57f, 0xd67f, 0xd77f, 0xd87f, 0xd97f, 0xda7f, 0xdb7f, 0xdc7f, 0xdd7f, 0xde7f, 0xdf7f, 0xe07f, 0xe17f, 0xe27f, 0xe37f, 0xe57f, 0xe67f, 0xe77f, 0xe87f, 0xe97f, 0xea7f, 0xec7f, 0xed7f, 0xee7f, 0xef7f, 0xf07f, 0xf27f, 0xf47f, 0xf57f, 0xf67f, 0xf77f, 0xf87f, 0xf97f, 0xfb7f, 0xfc7f, 0x1bebd3f, 0x1d6c63f, 0x1f0c83f, 0x1bead5f, 0x17aad9f, 0x1c4ae5f, 0x1c8af5f, 0x17caf9f, 0x18eb09f, 0x1d6b15f, 0x1e2b25f, 0x1e0b35f, 0x1e6b45f, 0x1f0b55f, 0x190b59f, 0x1fecc9f, 0x4ffd, 0x50fd, 0x51fd, 0x52fd, 0x1be527d, 0x17a52bd, 0x12452f5, 0x54fd, 0x1085cf9, 0x75fd, 0x10680f5, 0x81fd, 0x82fd, 0x83fd, 0x1f0837d, 0x19083bd, 0x16e83f5, 0x84fd, 0x86fd, 0x194c4bd, 0x200c4bd, 0x1e6c6bd, 0x10679fc] : List Nat).toArray,
   (827, 6, ([0x118300002700010108000000000504204104210608f0800400410401800010c10000800000430000010060410840c1000082000086083080043001042002180, 0x418100004044d0c20021800000011401800800450400030030401920830000c00000000010001800001c200024100100000004000000300030804420a040002, 0x31040800c00800000000131090030803000920011000401c0040040002080001004007005141040ac70400000892d50c10c03010c910600f0c00c0383000280, 0x70020c00c00002400060437832c600100604104004a0030812c240304024d2c21840110c71402050000c108400200c0000840401c000700004500600110c080, 0x1c304810158000000108000c08108904004000408600004b0c01860810022450000850c50c3082200102002003000000340045043145000142007040084000, 0x884820000891410c000001400500100108704d0c00152400c02801c00400000050400000880010c71c05410810520023400c10000070010010823032806c2, 0x2401042c920c08804000028500558119d0023806c300024010b25c0150401980000000830400020c000724000204104304014510000000f04300308a300008, 0x10801c008a3830030002180072001010003800004431400440402471800400821804000801401824070010031410c008314b0129800c9080000045009002180, 0x1000000000001d44a4013000cc0126401461850cc1c00c00034ab00400000000800410508304308d0000080c90c40811c90440074401450400401c31490111c0, 0x1c00182830c11cb0811910400c10097010460850062830000002c02c028004114100000a2c00060c40401d208008a] : List Nat).toArray),
   (2068, 12, ([0x37e1dd23d66203a0a93aa77c0004714b215713356b2bc2281ce0000282252d758165c7c500000012877604a0003ab0000001187475361ca7270001c178e30e, 0x86283f21f034258d1b807b74f5d663c1b21416f259d16a2d11bf6f563d1a43e41400ee4cb6f14463cc7954a040253c6b44477050403ac36213e5387ce7b8, 0x6c832d0024f618f00000019800a60e64e7121247942eb3035e327b1bb8525f54d52987e34df6007662386da56c68176d3184d715d5865136e06df4144191f1, 0x29456741011e00036704e3c100048c3d46dd0001270000001ae3602366e658945800000000016500026320c2ef5981a70000dc05b3900005bf28259b0005a6, 0x158f2ec3c47fa62120922b2e200000b1141906fa83f0001fd00001146b00073c4684350000000144b40001c800000010236b72225c6ad6764d479e1044fd, 0x53a56212027840457e1e474a2230006134fc0002d01a165b64000000000028b04f19f0000000ff0000000008413680002cc2b26493b35df72f10f5aa2911de, 0x38837864d2885c53120d357a60d49b15c1ea7fd54a83e6113700340003586e14527a152f00011568c26e13a5ad2aa0480005971645e12480000001c3154210, 0x1842923db49d21163238d0000007b022f41d5b80004990000d80003af33c3650006380005f121848d29e57472c70684a13b0863bd17050a45666457d0586de, 0x6fb4c92751f20b06572e648f3093a10875f969d5d15226b640f51d72425a4760001732896354b53d76917900000005d022964702900013203054f18d732373, 0x3a773946e45c56578b83a1df3be17b64b1637f41ba1314a42b963158422270751274d00018930d0000a40466832047480d92e00003065294ff19c3f300021c, 0x4600007fb2453b178d39d00000015185b2063d67e71691bd42d40c1477cb4a141c7dd6f04a712c66835a3c76596f66ca7aa1b65043a37710998092652fd, 0x5376a939e77a4632071e570170d1d500783b59202e3e70004b620b5db70968a1e90006396877d43ad0000000000000000004887ef0535247b32195f20aa5b1, 0x51a1d88240eb00041a00000000021a0000000000004956e50ab2497747e508c6ed6cc1a62f000013d3481c70006966b744c00000051b0f40f717641b20104c, 0x2d660f1812b00001b36d44220007d585a55f00004d5d703364c2f841830f19b19639827c6c58022f63862fe6750000006861f67d800053b6c318e0fc05a756, 0x1484751757dc2735183bc55c0e537681a00084400300078359516b1a80ae7d165e0fd0e86733ed00080600079256f71d06c5e87347033381e25010002c2, 0x2fc00000017d58e6617974ac00068f4a31060811c50007e26c002f1d724c78a00078f3de35532c0ea8283141fe00d63f15a2b80005474832607ca39618a384, 0x2124d32462433d278026867e11b0006524613b72d40000006c669869c5be1b76eb68963e0000005eb0007881d46a83242614ba80a7440f90000001b43d0, 0x781e701e80f38723235e24a3fe7bc00047a65300012d3178150005ae61700000027a00012e01900031300000016045e0000004704f24650510130006bc5de, 0x5773d31e13726f46f967b0008162c981f0b85b44a60006720006bd0000006468114cc6650004165a00000001ef00000080b70800000034578c0de73839c276, 0x5d30005258386196c95680000000000000006e41940000000420006c20005444c20ad0006671fa17259c0000ca16e46f46258372825f1a965a5705ff143, 0x7862036db4bc55321f13003c6fe29b8100ef0c63c60003cf21b0000000001d10003a049c3b21b105e74c55b42f62a5dc46d28f0000000005f661d000000000, 0x1a50001af02d3b45ed12966b83522d4c860c0000000000e64330267d036e22a00073d00072b36c7ff22e6501ff75d2583364267298034d258b12b4a2, 0x6d54f94ec12a02466302c2ce22000050b00049300000c57f5502591788341ab0000004be13576a0007f50000000004894110a20000003f900080d000000397, 0x67f4aa57147f5fb0a83f61252a000000000000080c59963a00061230000017a0006ba79831637c1b04083c04d81914982f90000605350004e003b237723624, 0x6e25665760005e007a0002ad2804b739b0b26700b55902e86921b903842c7b96cb38b1221c27ae5916aa5a14fe42970f3107b67682085603306ac7fc33223c, 0xe34e51671175c00035b5fd1f37172a40001e83d538c0000000000d00002305020001d620a40b08a0553391da7f237770e2000000006667e900000000010c, 0x4926603754d94ce73b4b13262c70001e36365b300032777055500065421600600000000000004b6fd1ad4c43da5e70840000b300039200023481e0006dc217, 0x68d2c400050e61520d56444a6e910e5402793b62f115f5cb1874785567fe5520001c600026256d0006947ee37114447b7ea2741c02dc2210000003b8227244, 0x82200036d1826441fc2f210383c4945ce8041f961e1506250c44ed25683d5582a100019972a5f42f500040970b0397df6820000000fa66c14937423a554000, 0x19d3ec00000066f0004796415b674e29a0000000f80005b00000002865f70f20f00000000000e200019e3630000000006580435bc5464170007214b082e, 0x1090f119732a6ee7e866e0495c40005a461c5a723b37f2b33a95085f37f814c3ba5ea3695dd06458c16d28347700017c00000018339f00000000075220562b, 0x5948370007c458855177d46938201545038a7e101f2727731f81952422be4304361d92150d25e464a7eb56948649a6043157697ab09e3f82cd0052530005e9, 0x23f00083683968800067d5af80719a4db24d0001db00009f55a6f72dd6c42ac6231627f90005b74cd37900000000001600010765600000081700068b30881c, 0x55d0000a500000014d2ff84c0000003a640a6167772fb4b981968079a7db4157a41451465397131856905fa6486f80b18004727100c027d1c900f1a22fa000, 0x5575b20986932cf3ae5960b675000018c7c87e04cf2ea21d61f0c12ee00000003d02a0000001743bf65d7840005151775825870100922f31884de64372e000, 0x53f5611f405238f5112c55191673ce71462042847c0220ec1e057c09335480556378160a6ef0000003615930001a34320002bf0000000e43e6311000000510, 0x9c4f808d41314e59f2240e722c0008563e10000f60005fe0000007d97be00054c33e2ca0004900000000000b78401d31567891dc00000028c0000000001ec, 0x7e60002f40000004741be7b256e3441807450000002e325d0af0172b600000010084725240d47e53d13916676f20f6a212f4381373d861a6a03ca59a1eb46c, 0x5ac4c54b32507202ed6180004647250005da0007530000000000000006a682545f78200016c7870000004204910003f03024d130c13c0000000001f7000000, 0x904441aa6fc00014b66a0000000002330000000003b926b4d06ce4730003e07ec3b516f51f0fb1cb03607252c0006104234375056c15d87c200000064570c, 0x26a00052754e4124f036a6955e51687636744dd6e87de3a428a1a08180093334d672605071a53245d1d01cf01c1cc74651c49e52600000046a70059e5e2523, 0x310804317494973a26ea85861b02b17e79b0004340004dc0f57a070411a00063b2931212470000003910253a80007a515e00003752000017f4964fb000000, 0x65149f39a53e6772772352a640540e3ea48e1340006371ee5007606336c72f70002706e31260001cd2140001d28127580df2022950fe43e2647855d94b8, 0x67803225e0278015215340ed27180800000000062200073a25b00000000060600070267a71c0b900000076280e2405fc7357910d60cc2da0005b90002c8, 0x5d27a82415f828e62e8465d45ee3a566d22668468e0cd76b7967936ec0000000000006693cd74b6072135ec4fa81b3956306ab0ac58017123e45900052e4bb, 0x5e61927590007725d58500000000004530006a36e754d56a29069a6f33893942394bf5410126d819358a7bf3851c40c718b3645141f54672e910564f21e716, 0x6970000005ca5ef47d1bc13813f00038e0000006550001fb0e92a75033fc0002c612355936f1b54da8146994ad1864f310851e76e84d6717d600014a, 0x20e6d90358130006014801360000000000b433f09669b5c200000065f6ff70a3991420f368517900076c5b55176d26425853ff1e67da3d10005c8000466000, 0x42e00044d67924b7d736600028d41e6141012cb00407e0000000000540000004ca23185314f1123b05280000000180001ed00000016100000039341f55e482, 0x6167c7e46cf1ac5f06340003bb000] : List Nat).toArray))

def level9 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (9, 9, ([0xff, 0x1ff, 0x2ff, 0x4ff, 0x6ff, 0x200a7f, 0xaff, 0x200b7f, 0xbff, 0x200c7f, 0xcff, 0x200d7f, 0xdff, 0x200e7f, 0xeff, 0x2a107f, 0x2e107f, 0x34107f, 0x4e107f, 0x4e10fd, 0x54107f, 0x5410fe, 0x5a107f, 0x62107f, 0x6e107f, 0x7c107f, 0x80107f, 0x84107f, 0x8e107f, 0x90107f, 0x92107f, 0x94107f, 0x98107f, 0xae107f, 0xb2107f, 0xc2107f, 0xcc107f, 0xd8107f, 0xde107f, 0xe4107f, 0xfe107f, 0x114107f, 0x118107f, 0x11a107f, 0x11c107f, 0x120107f, 0x126107f, 0x128107f, 0x12e107f, 0x14a107f, 0x152107f, 0x16e107f, 0x170107f, 0x178107f, 0x180107f, 0x18e107f, 0x194107f, 0x196107f, 0x10ff, 0x1d6107f, 0x1e6107f, 0x1f4107f, 0x1fa107f, 0x200107f, 0x16ff, 0x18ff, 0x19ff, 0x1dff, 0x4e1ffd, 0x1fff, 0x4e21fd, 0x21ff, 0x4e25fd, 0x25ff, 0x5427fd, 0x5a27fd, 0x6227fd, 0x6e27fd, 0x8c27fd, 0x8e27fd, 0x9027fd, 0x27ff, 0xae27fd, 0xb227fd, 0xc227fd, 0xcc27fd, 0xec27fd, 0xfe27fd, 0x11427fd, 0x11827fd, 0x12227fd, 0x12627fd, 0x12827fd, 0x12e27fd, 0x14a27fd, 0x15227fd, 0x16e27fd, 0x28ff, 0x29ff, 0x2bff, 0x2cff, 0x2dff, 0xae2dfd, 0x2eff, 0x2fff, 0x30ff, 0xb231fb, 0x31ff, 0x1be317f, 0x17a31bf, 0x12431f7, 0xfe31fb, 0x11431fb, 0xa431fd, 0xfe31fe, 0x35ff, 0x36ff, 0x37ff, 0x1c4377f, 0x12637f7, 0x12637fe, 0x39ff, 0x3aff, 0x3bff, 0x3cff, 0x3dff, 0x42ff, 0x43ff, 0x46ff, 0x4dff, 0x4eff, 0x52ff, 0x57ff, 0x58ff, 0x59ff, 0x1f0597f, 0x12e59f7, 0x16e59f7, 0x5cff, 0x1265cfb, 0x5dff, 0x5fff, 0x60ff, 0x61ff, 0x14a61ef, 0x62ff, 0x63ff, 0x64ff, 0x66ff, 0x16c66df, 0x67ff, 0x68ff, 0x69ff, 0x6bff, 0x6dff, 0x6eff, 0x70ff, 0x72ff, 0x73ff, 0x74ff, 0x76ff, 0x77ff, 0x78ff, 0x79ff, 0x7aff, 0x7bff, 0x7cff, 0x7dff, 0x7eff, 0x7fff, 0x85ff, 0x87ff, 0x88ff, 0x89ff, 0x8aff, 0x8bff, 0x95ff, 0x96ff, 0x97ff, 0x98ff, 0xa2ff, 0xa3ff, 0xa4ff, 0xa5ff, 0xa6ff, 0xa7ff, 0xa8ff, 0xa9ff, 0xaaff, 0xabff, 0xd0ff, 0xd1ff, 0x1f4eb7f, 0x1faeb7f, 0x200eb7f, 0x1faf37f, 0x1fafa7f, 0x11457fd, 0x10659fd, 0x1288afd] : List Nat).toArray,
   (757, 6, ([0x100008500e00304318200408014104200a0410822c00000000400000400810450000833050400460920820000480000000000000c80c100524000b0412c0000, 0x100000804038014304204304328818c08700118c0000010031410c20030000c10c00c004000301700500008e0000010024800c20c80570080012c0006001, 0x330000000040000034118000e0420c12010403402440002030000001071410800020800810c50411c000b040040082084140000005000080340004080040089, 0x520104400014004004004124d0431411441441040001431405800020005020413410000030040000000c4000147245000009540189246040052041380148443, 0x32020000000010c03000c70002030433c608000104020100004400404700900000c0430010050140442280000400000c1040081081341001102000006103100, 0x50020000820423c608308b00000a0082000021c02820801400020850032cc0001c10470c3003007203319ac63c304905714010a0060060c3085002103143002, 0x103cd0000820010001010001c15040401c44140400480020000430010001cd0001000411400430460472111527804057450800800c008100a0ca180, 0x12093040d70401410412c004414004f08004d00a04026a41a4c320200101f15804404000e5430060140040010402810823000002140000000c20c10000400c0, 0x308eaca1cd1401010400000081e63c018010058001000a5a100074400704300a0c000218699d2000012c420020c0c160105700304000800024a] : List Nat).toArray),
   (1893, 12, ([0x43b2240002c207f89100024000000019874552b1695ec92d7ac4682a600059c0000004506456e90007e92336301da5e00002921d96c675058c5112466ff000, 0x4f100089218d56a1f200000000000000093991000058810c21c2061815ac83670a2e803d4ec4044932e10c43480003c00b290e0000005c054f7197c871008c, 0x26362626a77a35a64a92e22875863d11633c71582a8d98df0a067700000092b00092841c0000000000005300000860d110262a5af11972a90a69847f1d2484, 0x4a411a24c7017e354c87f5f48376200d48c91a300000031d07576139977023488f72268600000000013f00002e00000044a7f575c7d387a0cf767414, 0x3427021b700043367b6d45228c54bc2713c61552952b84400008212600000007dd15c5fa11f57676484100000000025f0000002a821a84e0003157d615688d, 0x58d3984e60ac54362c2af27c82724b0c921b6cd78f1f595c55e71d5900b434a2ea5d890f23a0000002b093b0007170007c65544642371e506790622c4b37d1, 0x88a7d840646f2591091fc8534ef5c80c10000000005e80002f37b60000008b000e3bc8250000000008268752bf50772384a7da65c0188663ea8a4788, 0x1e958561a36035c9278799337e08104f68478db70777607e11742d6932cb2ab6602386e500076842c00089300000070c00084900004300073a0002fe000814, 0x57400000000073700000029e00041a47771a1e46e20008c68235a21258307ef79266d74f65e0806a978c8528d093e9008545193b65d960e3c846c5bb4260b5, 0x9111300002f26c87b925d6e11aa3961db7042610003ff7de63e0dc2091d10005b40001cc10f0d30005200000003190004fb00000000000000000000094a000, 0x8741605d69298510e89424f77f48b87a10ea2dd1e32c576d7861362f07bc7ce09648d8ad4c80847d459a8846fe16500074412827d4476be1c21061532a087c, 0x30414b74a4221ce7668e180b00005887e4748aa0bb0ca00058921900012430f6c05188288710000df2a26ac88200039c0000006df2b21721f82564fe5b5210, 0x2d10004ee7a46f17299263cc0006f20000008702044320000006dc0007b229a06e0c87400000000002da02b0463ed0000002130008a157f5d27ee52877d2dc, 0x8440c283d0e404200093400053a00000002588c3a88c08e816c6d774c55a2b309a9326d07478851ed7e12c44b000085a0002ec03649208f50454678e512727, 0x7942051b11c555200009c25857e3937e55f80008185d023002a0000000003686156cc50c46564101b30c2896ee1208728ee7ad0285911f18c1400123708193, 0x81a0008a737871f00000079b0000007cb0711e05130d95172084620007e765581d8898552f55234a26927e40000820009094870731d61158e70647dc49c72e, 0xba48a13967e1c75f55822772d74e16d81c66ae49915910e7ca49825c61205e20c8051758160772e289a6468b66140e57a60000000003f43f78125403f6, 0x47673e36e2e500000004800059d79a81393a1c000049058e07b1cf00000004000000063c26e29882b19d1ca17a47b00000000000072b12a4b80007125ba696, 0x7c351b6f005415191c5b220f4b972d0d25150003d858a01c2186c989077c1614867fb8ba0005d32e90040de8ac65a7e60ae6e43572e752500084349e5e6690, 0x72c0007218c80000240885705ae0004724e01f706f3ba0c08fa0a66e31ef9560002441c110014a5771be61e05b0000f00000004f836f07d4b2000000, 0x3662b61920000a965704c7d993600000064b56c2f80be2747418e400000015273290878025e3510144f46ec7527bd0007536fd7b847c5d16ca9318dd000, 0x2df83c94e85600090245300090118c76c0005e90000001871270000005000007b03300002321df50d6b43e68784d42ed94851c2a71b579e4565ca1c9, 0x8bb65658b6b509d0ce59453119b7cc23d74b6ea6db07888e11829b81f2c80700000000000000004790000000000008d281b0000001297282310008dc711000, 0xf7828e264828281584c8d45661a014577150166e23c7d51bb15f2a46e816e0000000004759043840d68a08201bd09478380400085b28300009980180a93f, 0x937e866360c0fd2b41865d41a50987fa24361b19a06684d6da2b51d489b1ee91f6f56680006c44dd17810381e2d486400086d28e4d68581678de00084069c, 0x71c1990975067003a407c84b21f00000000000c00024d22f2de0d048092a1dc0d77c220276e8fc76a71609221e0e24f03ae6af71328f7622685272d01b654e, 0x92289472400000066f7b30000c67f27985142ac3b726574e1087cd7367599171cb00000093c03118000095736914e0000000000000617d785724192c82e, 0x12d2292526540000003541964fa6d608d00054200052150a0005e367812c0cc82451f4032fb0005dc79570600016334b2e61b94170004466474380870000f7, 0x16f2a17770000000000004300002455552350724f519f0001262be4961441332226589370005be00052a00000000000000074d71b00042989e76530e0ee055, 0x56444c6622801686243ec7fe8886732a500015d0000002d60004520000000000741f40000005cb0000520007f872690d00000000020d5da00013e000000000, 0x39f5619450cd08b6c700023e4161a228617b1f330000025a4d73123186717e221428868071841d8e022a09b6667052eb8b395d34e714916420597, 0x45e1e887747d0fc3908733562b10003fd26292503a00000064408a7693fe00000067a00087b0001e71c46a80005a90000001eb00000025000071e215000000, 0x8e568d6720000001128da9030eb4ea3c92362b70000000007204e400000000057a1cd91e4b622e11b00000000000085033637438a6fc58f87621240700062d, 0x6d58d50f693500068701a6ba13801d00000039e43a4ed0900cb8486b200075f06a7df91249f51a1dd0005a30001ec89551641020b5923e46187748b23c2703, 0x11400062773b0002aa1a11c88d70000d81b21d77cf8d32e008155b4112484ce8f789870e73188b7a700043636c6996bb1625a607953403413c1e222181720a, 0x12b65b47a73060f1582116846f366911d45907a65d91919e4286d328c3b408974611c86c14243e66c6708c751e21786a3922423a5905350914000000000000, 0x5c47481ff81c64272f5ce8d82496751225c554883100000036206d2a300023f3de0000000001f67aa2231f99156766d26d915e0000000000000001d0000423, 0xa82208d67a01b304e00000036362101903025b40e3fc7d01642bc0918a657c6a25587d283a9383fa5c168c1d85dd0150015965367731b47345db819000510, 0x4084dc5a07ec6c15263721502536e08f40000001ab00047874956722b1c367486756d2ca75e22700035d2642471e68c48089441ae51d9136de26b90b04f6c3, 0x15b0000000f47ea1de3f04f20af90770f2ce3e73bd2f15490856eb1216c25719508be03784663f76b0a24580c51a82943140c353c5b84da52e1841ea09531a, 0x1e12e400094b0fa8221b020e6e60000009180000000006c573376048c8e36f456073540584f76347e95a15403c2266dd4023c31b87eb2ad37e7567c9951600, 0x5930000000000d580e0003010002ae27600000053d0005e23f100040b08e1900000008f673800077231b9305d745f24a0000006cf1d36ef2ef17e76f000000, 0x5a81a48d178908370d15a90c0c75ef2e332418a45c11e1320b822d27a6592076b87095fe81175d4691486402a94413d268a0001571fe000537000000000060, 0x23b3750000000002160009540002fa0006d100000058400046e7db0008421ba2706ce68131c5ee40a5f24f34817c01744015d570b07621d8006cb2b9606, 0x8456e71bf0009240128341bc16605a4e792f8e62ee6430f16ed06c44d4442f40a31d504919c0000001f00005245fb0000007250003a200022500065f000000, 0x8fd000239] : List Nat).toArray))

def level10 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (9, 9, ([0x10ff, 0x27ff, 0x2dff, 0x31ff, 0x37ff, 0x57ff, 0x59ff, 0x61ff, 0x66ff, 0x7fff, 0x8aff, 0x97ff, 0xa5ff, 0xa9ff] : List Nat).toArray,
   (32, 4, ([0x441410622e0507021035501120001272] : List Nat).toArray),
   (82, 8, ([0x38484a045e000a62326e96004b0678009c2d619400008100009036750084729d0c6507306c00a18654a0007e9a187b002c00645b5a60003900009e803301129f, 0x2763242a87000058746f7a973c9100005526] : List Nat).toArray))

def level11 : Nat × Nat × Array Nat × PackedSlots × PackedSlots :=
  (8, 9, ([0xff] : List Nat).toArray,
   (1, 1, ([0x0] : List Nat).toArray),
   (2, 1, ([0x0] : List Nat).toArray))

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

private def JoinWire (andGate : Bool) (a b : BitVec W) : BitVec W :=
  if andGate then a &&& b else a ||| b

private def Branch (andGate value : Bool) (a b : BitVec W) (row : Nat) (x : BitVec W) : Prop :=
  if andGate = value then x = a ∨ x = b else x = if a.getLsbD row = value then a else b

private theorem branch_mem {g v : Bool} {a b x : BitVec W} {i : ℕ}
    (h : Branch g v a b i x) : x = a ∨ x = b := by
  unfold Branch at h
  split at h
  · exact h
  · split at h <;> simp [h]

private theorem branch_at {g v : Bool} {a b x : BitVec W} {i : ℕ}
    (hv : (JoinWire g a b).getLsbD i = v) (hx : Branch g v a b i x) : x.getLsbD i = v := by
  cases g <;> cases v <;> cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;>
    simp [JoinWire,Branch,ha,hb] at hv hx ⊢ <;> grind

private theorem branch_forces {g v : Bool} {a b : BitVec W} {i j : ℕ}
    (h : ∀ x, Branch g v a b i x → x.getLsbD j = v) : (JoinWire g a b).getLsbD j = v := by
  have ha := h a
  have hb := h b
  cases g <;> cases v <;> cases h0 : a.getLsbD i <;>
    simp [JoinWire,Branch,h0] at ha hb ⊢ <;> grind

private theorem branch_unique {g : Bool} {a b x y : BitVec W} {i j : ℕ}
    (xp : Branch g true a b i x) (xn : Branch g false a b j x)
    (yp : Branch g true a b i y) (yn : Branch g false a b j y) : x = y := by
  cases g <;> simp [Branch] at * <;> grind

def RowCertificate (P : BitVec W → Prop) (v : Bool) (i : Nat) (t : BitVec W) : Prop :=
  (∀ x, P x → x.getLsbD i = v) ∧ (∀ j, (∀ x, P x → x.getLsbD j = v) → t.getLsbD j = v)

private def Expanded (P : BitVec W → Prop) (z : BitVec W) (B : BitVec W → Prop)
    (x : BitVec W) : Prop := (x ≠ z ∧ P x) ∨ (P z ∧ B x)

private theorem expand_cert {P : BitVec W → Prop} {g v : Bool} {a b t : BitVec W} {i : ℕ}
    (h : RowCertificate P v i t) :
    RowCertificate (Expanded P (JoinWire g a b) (Branch g v a b i)) v i t := by
  constructor
  · rintro x (⟨_,hx⟩ | ⟨hz,hx⟩)
    · exact h.1 x hx
    · exact branch_at (h.1 _ hz) hx
  · intro j hj
    apply h.2 j
    intro x hx
    by_cases he : x = JoinWire g a b
    · subst x
      exact branch_forces (fun y hy => hj y (Or.inr ⟨hx,hy⟩))
    · exact hj x (Or.inl ⟨he,hx⟩)

private theorem expand_contained {s : Finset (BitVec W)} {a b z x : BitVec W}
    {P B : BitVec W → Prop} (ha : a ∈ s) (hb : b ∈ s)
    (hP : ∀ y, P y → y ∈ insert z ((s.erase a).erase b)) (hB : ∀ y, B y → y=a ∨ y=b)
    (hx : Expanded P z B x) : x ∈ s := by
  rcases hx with ⟨hne,hx⟩ | ⟨_,hx⟩
  · have h := hP x hx
    simp only [Finset.mem_insert, Finset.mem_erase] at h
    grind
  · rcases hB x hx with rfl | rfl <;> assumption

private theorem expand_unique {s : Finset (BitVec W)} {a b z : BitVec W}
    {P N BP BN : BitVec W → Prop}
    (hP : ∀ x, P x → x ∈ insert z ((s.erase a).erase b))
    (hN : ∀ x, N x → x ∈ insert z ((s.erase a).erase b))
    (bP : ∀ x, BP x → x=a ∨ x=b) (bN : ∀ x, BN x → x=a ∨ x=b)
    (hu : ∀ x y, P x → N x → P y → N y → x=y)
    (bu : ∀ x y, BP x → BN x → BP y → BN y → x=y) :
    ∀ x y, Expanded P z BP x → Expanded N z BN x →
      Expanded P z BP y → Expanded N z BN y → x=y := by
  intro x y hxp hxn hyp hyn
  have freeP (u : BitVec W) (hu : P u) (hne : u ≠ z) : u ≠ a ∧ u ≠ b := by
    have hm := (Finset.mem_insert.mp (hP u hu)).resolve_left hne
    simp only [Finset.mem_erase] at hm
    exact ⟨hm.2.1,hm.1⟩
  have freeN (u : BitVec W) (hu : N u) (hne : u ≠ z) : u ≠ a ∧ u ≠ b := by
    have hm := (Finset.mem_insert.mp (hN u hu)).resolve_left hne
    simp only [Finset.mem_erase] at hm
    exact ⟨hm.2.1,hm.1⟩
  unfold Expanded at hxp hxn hyp hyn
  grind

theorem merge_certificates {s : Finset (BitVec W)} {t : BitVec W} (h : MergeReach s t)
    (i j : ℕ) (hp : t.getLsbD i = true) (hn : t.getLsbD j = false) :
    ∃ P N : BitVec W → Prop,
      (∀ x, P x → x ∈ s) ∧ (∀ x, N x → x ∈ s) ∧
      RowCertificate P true i t ∧ RowCertificate N false j t ∧
      (∀ x y, P x → N x → P y → N y → x = y) := by
  induction h with
  | @done s t ht =>
    refine ⟨(· = t),(· = t),?_,?_,?_,?_,?_⟩
    · rintro x rfl; exact ht
    · rintro x rfl; exact ht
    · exact ⟨fun x hx => hx ▸ hp,fun _ h => h t rfl⟩
    · exact ⟨fun x hx => hx ▸ hn,fun _ h => h t rfl⟩
    · grind
  | @step s t a b z ha hb hab hz hr ih =>
    obtain ⟨P,N,hP,hN,cp,cn,hu⟩ := ih hp hn
    obtain ⟨g,rfl⟩ : ∃ g, z = JoinWire g a b := hz.elim (fun h => ⟨true,h⟩) (fun h => ⟨false,h⟩)
    refine ⟨Expanded P _ (Branch g true a b i),Expanded N _ (Branch g false a b j),?_,?_,
      expand_cert cp,expand_cert cn,?_⟩
    · exact fun _ => expand_contained ha hb hP (fun _ h => branch_mem h)
    · exact fun _ => expand_contained ha hb hN (fun _ h => branch_mem h)
    · exact expand_unique hP hN (fun _ h => branch_mem h) (fun _ h => branch_mem h) hu
        (fun _ _ xp xn yp yn => branch_unique xp xn yp yn)

private theorem positive_diff {P : BitVec W → Prop} {i n : ℕ} {t : BitVec W}
    (h : RowCertificate P true i t) (hn : t.getLsbD n = false) :
    ∃ x, P x ∧ x.getLsbD i = true ∧ x.getLsbD n = false := by
  by_contra! bad
  have ht := h.2 n (by
    intro x hx
    cases he : x.getLsbD n
    · exact False.elim (bad x hx (h.1 x hx) he)
    · rfl)
  simp [hn] at ht

private theorem negative_diff {N : BitVec W → Prop} {j p : ℕ} {t : BitVec W}
    (h : RowCertificate N false j t) (hp : t.getLsbD p = true) :
    ∃ x, N x ∧ x.getLsbD p = true ∧ x.getLsbD j = false := by
  by_contra! bad
  have ht : t.getLsbD p = false := h.2 p (by
    intro x hx
    cases he : x.getLsbD p
    · rfl
    · have ho := bad x hx he
      simp [h.1 x hx] at ho)
  simp [hp] at ht

theorem merge_no_dominance {s : Finset (BitVec W)} {t : BitVec W} {p n : ℕ}
    (hp : t.getLsbD p = true) (hn : t.getLsbD n = false)
    (h : ∀ x ∈ s, x.getLsbD p = true → x.getLsbD n = true) : ¬ MergeReach s t := by
  intro reach
  obtain ⟨P,_,hP,_,cp,_,_⟩ := merge_certificates reach p n hp hn
  obtain ⟨x,hx,hxp,hxn⟩ := positive_diff cp hn
  simpa [hxn] using h x (hP x hx) hxp

private def LocalOnly (ws : List (BitVec W)) (p n : Nat) (a : BitVec W) : Bool :=
  ws.all fun x => decide (x.getLsbD p = true → x.getLsbD n = false → x = a)

private theorem localOnly_elim {ws : List (BitVec W)} {p n : Nat} {a x : BitVec W}
    (h : LocalOnly ws p n a = true) (hx : x ∈ ws.toFinset)
    (hp : x.getLsbD p = true) (hn : x.getLsbD n = false) : x = a := by
  have hz := List.all_eq_true.mp h x (List.mem_toFinset.mp hx)
  exact of_decide_eq_true hz hp hn

theorem merge_no_double {ws : List (BitVec W)} {t a b : BitVec W} {p n na nb pa pb : ℕ}
    (hab : a ≠ b) (hp : t.getLsbD p = true) (hn : t.getLsbD n = false)
    (hna : t.getLsbD na = false) (hnb : t.getLsbD nb = false)
    (hpa : t.getLsbD pa = true) (hpb : t.getLsbD pb = true)
    (PN₁ : LocalOnly ws p na a = true) (PN₂ : LocalOnly ws p nb b = true)
    (NP₁ : LocalOnly ws pa n a = true) (NP₂ : LocalOnly ws pb n b = true) :
    ¬ MergeReach ws.toFinset t := by
  intro reach
  obtain ⟨P,N,hP,hN,cp,cn,hu⟩ := merge_certificates reach p n hp hn
  have posForce (v : BitVec W) (r : ℕ) (hr : t.getLsbD r = false)
      (only : LocalOnly ws p r v = true) : P v := by
    obtain ⟨x,hx,hxp,hxr⟩ := positive_diff cp hr
    exact localOnly_elim only (hP x hx) hxp hxr ▸ hx
  have negForce (v : BitVec W) (r : ℕ) (hr : t.getLsbD r = true)
      (only : LocalOnly ws r n v = true) : N v := by
    obtain ⟨x,hx,hxr,hxn⟩ := negative_diff cn hr
    exact localOnly_elim only (hN x hx) hxr hxn ▸ hx
  exact hab (hu a b (posForce a na hna PN₁) (negForce a pa hpa NP₁)
    (posForce b nb hnb PN₂) (negForce b pb hpb NP₂))

inductive LocalWitness where
  | dominance (p n : Nat)
  | double (p n npA npB ppA ppB aIndex bIndex : Nat)

def localReject (ws : List (BitVec W)) (t : BitVec W) : LocalWitness → Bool
  | .dominance p n => decide (t.getLsbD p = true ∧ t.getLsbD n = false ∧
      (ws.all fun x => decide (x.getLsbD p = true → x.getLsbD n = true)) = true)
  | .double p n na nb pa pb ai bi =>
    match ws[ai]?, ws[bi]? with
    | some a, some b => decide (a ≠ b ∧ t.getLsbD p = true ∧ t.getLsbD n = false ∧
        t.getLsbD na = false ∧ t.getLsbD nb = false ∧ t.getLsbD pa = true ∧ t.getLsbD pb = true ∧
        LocalOnly ws p na a = true ∧ LocalOnly ws p nb b = true ∧
        LocalOnly ws pa n a = true ∧ LocalOnly ws pb n b = true)
    | _, _ => false

theorem localReject_sound {ws : List (BitVec W)} {t : BitVec W} {witness : LocalWitness}
    (h : localReject ws t witness = true) : ¬ MergeReach ws.toFinset t := by
  cases witness with
  | dominance p n =>
    obtain ⟨hp,hn,hall⟩ := of_decide_eq_true h
    exact merge_no_dominance hp hn (fun x hx => of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_toFinset.mp hx)))
  | double p n na nb pa pb ai bi =>
    cases ha : ws[ai]? with
    | none => simp [localReject,ha] at h
    | some a =>
      cases hb : ws[bi]? with
      | none => simp [localReject,ha,hb] at h
      | some b =>
        simp only [localReject,ha,hb,decide_eq_true_eq] at h
        obtain ⟨hab,hp,hn,hna,hnb,hpa,hpb,pna,pnb,npa,npb⟩ := h
        exact merge_no_double hab hp hn hna hnb hpa hpb pna pnb npa npb

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

inductive RowTemplate where
  | dm (p n : Nat)
  | db (p n u v i j : Nat)

def RowTemplate.check {W : Nat} (ws : List (BitVec W)) (t : BitVec W) : RowTemplate → Bool
  | .dm p n => localReject ws t (.dominance p n)
  | .db p n u v i j =>
    let first := fun r => ws.findIdx (fun a => a.getLsbD p && !a.getLsbD r)
    localReject ws t (.double p n u v i j (first u) (first v))

def thetaTemplates : List RowTemplate :=
  [.db 12 3 84 88 11 7, .db 48 3 168 152 19 35, .db 65 132 96 161 133 196,
   .db 130 96 132 70 98 224, .dm 65 1, .dm 130 2, .db 65 152 88 137 153 216,
   .dm 10 2, .dm 17 1, .db 130 88 152 82 90 216, .db 10 132 24 22 134 140,
   .db 17 104 88 41 105 120, .db 192 3 84 148 131 67, .dm 5 1,
   .db 5 24 132 137 25 28, .dm 5 4, .dm 10 8, .db 10 100 104 70 102 108,
   .db 5 152 148 137 153 156, .db 5 104 100 41 105 108, .db 34 148 164 22 150 180,
   .db 12 3 168 164 7 11, .dm 34 2, .db 34 24 96 82 26 56]

def templateHint {W : Nat} (ws : List (BitVec W)) (t : BitVec W) : Bool :=
  thetaTemplates.any (RowTemplate.check ws t)

theorem templateHint_sound {W : Nat} {ws : List (BitVec W)} {t : BitVec W}
    (h : templateHint ws t = true) : ¬MergeReach ws.toFinset t := by
  obtain ⟨r,_,hr⟩ := List.any_eq_true.mp h
  cases r <;> simp only [RowTemplate.check] at hr <;> exact localReject_sound hr

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

variable {W : ℕ}

def diffLane (d : Nat) (a : BitVec W) : Nat :=
  (a.toNat ^^^ (a.toNat >>> d)) % (2^(W-d))

def pairKey : List Nat → BitVec W → Nat
  | [], _ => 0
  | d::ds, a => diffLane d a ||| (pairKey ds a <<< W)

private theorem lane_bit (d j : ℕ) (a : BitVec W) :
    (diffLane d a).testBit j = true ↔
      j+d < W ∧ a.getLsbD j ≠ a.getLsbD (j+d) := by
  simp only [diffLane, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d j]
  change (j < W-d ∧ (a.getLsbD j ^^ a.getLsbD (j+d)) = true) ↔ _
  rw [show j < W-d ↔ j+d < W by omega]
  cases a.getLsbD j <;> cases a.getLsbD (j+d) <;> simp

private theorem pair_key_witness {ws : List (BitVec W)} {t : BitVec W} {k : ℕ}
    (hr : Reach ws.toFinset k t) (ds : List Nat) (j : Nat)
    (hj : (pairKey ds t).testBit j = true) : ∃ a ∈ ws, (pairKey ds a).testBit j = true := by
  induction ds generalizing j with
  | nil => simp [pairKey] at hj
  | cons d ds ih =>
    simp only [pairKey,Nat.testBit_or,Bool.or_eq_true] at hj ⊢
    rcases hj with h | h
    · obtain ⟨hv,hd⟩ := (lane_bit d j t).mp h
      obtain ⟨a,ha,hh⟩ : ∃ a ∈ ws, a.getLsbD j ≠ a.getLsbD (j+d) := by
        by_contra! hbad
        exact hd (reach_row hr ⟨j,by omega⟩ ⟨j+d,hv⟩ (fun a ha => hbad a (List.mem_toFinset.mp ha)))
      exact ⟨a,ha,Or.inl ((lane_bit d j a).mpr ⟨hv,hh⟩)⟩
    · rw [Nat.testBit_shiftLeft] at h
      obtain ⟨hle,hb⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨a,ha,hj⟩ := ih _ hb
      exact ⟨a,ha,Or.inr (by simp [Nat.testBit_shiftLeft,of_decide_eq_true hle,hj])⟩

def keyUnion : List (BitVec W × Nat) → Nat
  | [] => 0
  | x::xs => x.2 ||| keyUnion xs

private theorem keyUnion_bit {j : ℕ} {xs : List (BitVec W × Nat)} {a : BitVec W × Nat}
    (h : a ∈ xs) (hb : a.2.testBit j = true) : (keyUnion xs).testBit j = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [keyUnion,Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl hb
    · exact Or.inr (ih h)

abbrev annotate (ds : List Nat) (a : BitVec W) := (a,pairKey ds a)

private theorem keyUnion_covers {xs : List (BitVec W × Nat)} {k : ℕ} {t : BitVec W} {ds : List Nat}
    (hr : Reach (xs.map Prod.fst).toFinset k t)
    (ok : ∀ a ∈ xs, a.2 = pairKey ds a.1) :
    pairKey ds t &&& keyUnion xs = pairKey ds t := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and]
  cases hv : (pairKey ds t).testBit j with
  | false => rfl
  | true =>
    obtain ⟨a,ha,hb⟩ := pair_key_witness hr ds j hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact keyUnion_bit hx (by simpa [ok x hx] using hb)

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux
variable {W : ℕ}

private theorem seen_covers {ws : List (BitVec W)} {q : ℕ} {t : BitVec W}
    (ds : List Nat) (hu : Reach ws.toFinset q t) :
    pairKey ds t &&& keyUnion (ws.map (annotate ds)) = pairKey ds t := by
  apply keyUnion_covers (k := q)
  · simpa [Function.comp_def] using hu
  · intro x hx
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
    rfl

def quickGroup (ds : List Nat) (w : List (BitVec W)) (m : Nat) (t : BitVec W)
    (cover : List (BitVec W) → Bool) : Bool :=
  let n := min (m+1) (w.length+1)
  let goal := pairKey ds t
  let candidates := (cand w).map (annotate ds)
  ((List.sublistsLen n w).all fun u =>
    let seen := keyUnion (u.map (annotate ds))
    if goal &&& seen == goal then cover u else true) &&
  ((List.sublistsLen (n-1) w).all fun u =>
    let seen := keyUnion (u.map (annotate ds))
    candidates.all fun az =>
      if goal &&& (az.2 ||| seen) == goal then cover (az.1 :: u) else true)

private theorem quick_member {ds : List Nat} {w : List (BitVec W)} {m q : ℕ} {t z : BitVec W}
    {cover : List (BitVec W) → Bool} {us : List (BitVec W)}
    (hg : quickGroup ds w m t cover = true) (hz : z ∈ cand w)
    (hus : us ∈ List.sublistsLen (min (m+1) (z::w).length) (z::w))
    (hu : Reach us.toFinset q t) : cover us = true := by
  simp only [quickGroup, Bool.and_eq_true] at hg
  have htake : 0 < min (m+1) (w.length+1) := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero htake.ne'
  simp only [List.length_cons, hn, List.sublistsLen_succ_cons, List.mem_append, List.mem_map] at hus
  rcases hus with halone | ⟨u,hmem,he⟩
  · have hc := List.all_eq_true.mp hg.1 us (hn ▸ halone)
    simpa [seen_covers ds hu] using hc
  · subst us
    have hmem' : u ∈ List.sublistsLen (min (m+1) (w.length+1)-1) w := by simpa [hn] using hmem
    have hc := List.all_eq_true.mp (List.all_eq_true.mp hg.2 u hmem') (annotate ds z)
      (List.mem_map_of_mem hz)
    have hp : pairKey ds t &&& (pairKey ds z ||| keyUnion (u.map (annotate ds))) = pairKey ds t :=
      seen_covers ds hu
    simpa only [annotate, hp, beq_self_eq_true, ite_true] using hc

def quickTightCheck (ds : List Nat) (w : List (BitVec W)) (k : ℕ) (t : BitVec W)
    (ordinary tree : List (BitVec W) → Bool) : Bool :=
  quickGroup ds w (k-1) t ordinary &&
    (if k ≤ w.length then quickGroup ds w k t tree else true)

theorem quickTight_sound {ds : List Nat} {w : List (BitVec W)} {k : ℕ} {t : BitVec W}
    {ordinary tree : List (BitVec W) → Bool} (hk : 0 < k)
    (hr : Reach w.toFinset (k+1) t) (hd : w.Nodup) (ht : t ∉ w)
    (hg : quickTightCheck ds w k t ordinary tree = true) :
    (∃ u, ordinary u = true ∧ Reach u.toFinset k t) ∨
      (∃ u, tree u = true ∧ MergeReach u.toFinset t) := by
  rcases hr with hn | ⟨z,hzw,hz0,hz1,hn,hr⟩
  · exact False.elim (ht (List.mem_toFinset.mp hn))
  have hz : z ∉ w := by simpa using hzw
  have hw : (z::w).Nodup := List.nodup_cons.mpr ⟨hz,hd⟩
  have hzmem := cand_complete hn hz hz0 hz1
  have hr' : Reach (z::w).toFinset k t := by simpa using hr
  obtain ⟨u,hsub,hcard,hreach,htree⟩ := reach_support_merge hr'
  have hull : u.card ≤ (z::w).length := (Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup hw)
  obtain ⟨ho,hg'⟩ := Bool.and_eq_true_iff.mp hg
  by_cases hsmall : u.card ≤ k
  · let n := min ((k-1)+1) (z::w).length
    obtain ⟨us,hs,hu⟩ := selectSized (n := n) hsub hw (le_min (by omega) hull) (min_le_right _ _)
    have hrus := reach_mono hu hreach
    exact Or.inl ⟨us,quick_member ho hzmem hs hrus,hrus⟩
  · have hl : u.card = k+1 := by omega
    have hlw : k ≤ w.length := by simp only [List.length_cons] at hull; omega
    have hc : quickGroup ds w k t tree = true := by simpa only [hlw,ite_true] using hg'
    let n := min (k+1) (z::w).length
    have heq : n = u.card := by dsimp [n]; omega
    obtain ⟨us,hs,hu⟩ := selectSized (n := n) hsub hw (by omega) (min_le_right _ _)
    obtain ⟨hsu,hln⟩ := List.mem_sublistsLen.mp hs
    have hsame : u = us.toFinset := Finset.eq_of_subset_of_card_le hu (by rw [List.toFinset_card_of_nodup (hsu.nodup hw),hln,heq])
    have hrus := reach_mono hu hreach
    exact Or.inr ⟨us, quick_member hc hzmem hs hrus, hsame ▸ htree hl⟩

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

def tableGoal : BitVec 256 := 0xfffffffffffffffffffffcecfeeefcecfffffeeefeaafeaafffffcecfeaafca0

def thetaOffsets : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 3, 7, 12, 28, 126, 127, 6, 24, 62, 120, 15, 96, 129, 130, 132, 136, 192, 63, 60, 56, 10, 124, 112, 31]

def checkTheta (cur nxt : Layer) (k i : Nat) : Bool :=
  let w := stateAt alphabet cur i
  decide w.Nodup && !w.contains tableGoal &&
    quickTightCheck thetaOffsets w k tableGoal (covers alphabet thetaPerms nxt) (fun u => templateHint u tableGoal)

private theorem layerStep516 {cur nxt : Layer} {k : ℕ} (hk : 0 < k)
    (fixed : ∀ p ∈ thetaPerms, shuffleWord p tableGoal = tableGoal)
    (check : ∀ i < stateCount cur, checkTheta cur nxt k i = true)
    (rest : ∀ j < stateCount nxt, ¬Reach (stateAt alphabet nxt j).toFinset k tableGoal) :
    ∀ i < stateCount cur, ¬Reach (stateAt alphabet cur i).toFinset (k+1) tableGoal := by
  intro i hi hr
  have hc := check i hi
  obtain ⟨hnt,hg⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hn,ht⟩ := Bool.and_eq_true_iff.mp hnt
  rcases quickTight_sound hk hr (of_decide_eq_true hn) (by simpa using ht) hg with
    ⟨u,hu,hur⟩ | ⟨u,hu,hur⟩
  · obtain ⟨j,hj,hrj⟩ := validHint_sound (fun _ hp => theta_perm_ok hp) fixed hu hur
    exact rest j hj hrj
  · exact templateHint_sound hu hur

set_option maxRecDepth 32768 in
private theorem fixedGoal : ∀ p ∈ thetaPerms, shuffleWord p tableGoal = tableGoal := by decide +kernel

private def Span (f : Nat → Bool) (base len : Nat) : Prop :=
  ∀ i < len, f (i+base) = true

private theorem fromSpan {f : Nat → Bool} {base len : Nat}
    (h : (List.range len).all (fun i => f (i+base)) = true) : Span f base len :=
  fun i hi => List.all_eq_true.mp h i (List.mem_range.mpr hi)

private theorem joinSpan {f : Nat → Bool} {base a b : Nat}
    (h1 : Span f base a) (h2 : Span f (base+a) b) : Span f base (a+b) := by
  intro i hi
  by_cases ha : i < a
  · exact h1 i ha
  · have h := h2 (i-a) (by omega)
    rwa [show i-a+(base+a) = i+base by omega] at h

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece7x0 : Span (checkTheta level7 level6 6) 0 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece7x3 : Span (checkTheta level7 level6 6) 3 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece7x6 : Span (checkTheta level7 level6 6) 6 2 := fromSpan (by decide +kernel)

private theorem checkLayer7 : ∀ i < stateCount level7, checkTheta level7 level6 6 i = true := (joinSpan (joinSpan piece7x0 piece7x3) piece7x6)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x0 : Span (checkTheta level8 level7 7) 0 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x3 : Span (checkTheta level8 level7 7) 3 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x6 : Span (checkTheta level8 level7 7) 6 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x9 : Span (checkTheta level8 level7 7) 9 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x12 : Span (checkTheta level8 level7 7) 12 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x15 : Span (checkTheta level8 level7 7) 15 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x18 : Span (checkTheta level8 level7 7) 18 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x21 : Span (checkTheta level8 level7 7) 21 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x24 : Span (checkTheta level8 level7 7) 24 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x27 : Span (checkTheta level8 level7 7) 27 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x30 : Span (checkTheta level8 level7 7) 30 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x33 : Span (checkTheta level8 level7 7) 33 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x36 : Span (checkTheta level8 level7 7) 36 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x39 : Span (checkTheta level8 level7 7) 39 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x42 : Span (checkTheta level8 level7 7) 42 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x45 : Span (checkTheta level8 level7 7) 45 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x48 : Span (checkTheta level8 level7 7) 48 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x51 : Span (checkTheta level8 level7 7) 51 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x54 : Span (checkTheta level8 level7 7) 54 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x57 : Span (checkTheta level8 level7 7) 57 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x60 : Span (checkTheta level8 level7 7) 60 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x63 : Span (checkTheta level8 level7 7) 63 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x66 : Span (checkTheta level8 level7 7) 66 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x69 : Span (checkTheta level8 level7 7) 69 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x72 : Span (checkTheta level8 level7 7) 72 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x75 : Span (checkTheta level8 level7 7) 75 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x78 : Span (checkTheta level8 level7 7) 78 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x81 : Span (checkTheta level8 level7 7) 81 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x84 : Span (checkTheta level8 level7 7) 84 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x87 : Span (checkTheta level8 level7 7) 87 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x90 : Span (checkTheta level8 level7 7) 90 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x93 : Span (checkTheta level8 level7 7) 93 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x96 : Span (checkTheta level8 level7 7) 96 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x99 : Span (checkTheta level8 level7 7) 99 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x102 : Span (checkTheta level8 level7 7) 102 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x105 : Span (checkTheta level8 level7 7) 105 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x108 : Span (checkTheta level8 level7 7) 108 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x111 : Span (checkTheta level8 level7 7) 111 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x114 : Span (checkTheta level8 level7 7) 114 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x117 : Span (checkTheta level8 level7 7) 117 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x120 : Span (checkTheta level8 level7 7) 120 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x123 : Span (checkTheta level8 level7 7) 123 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x126 : Span (checkTheta level8 level7 7) 126 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x129 : Span (checkTheta level8 level7 7) 129 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x132 : Span (checkTheta level8 level7 7) 132 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x135 : Span (checkTheta level8 level7 7) 135 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x138 : Span (checkTheta level8 level7 7) 138 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x141 : Span (checkTheta level8 level7 7) 141 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x144 : Span (checkTheta level8 level7 7) 144 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x147 : Span (checkTheta level8 level7 7) 147 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x150 : Span (checkTheta level8 level7 7) 150 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x153 : Span (checkTheta level8 level7 7) 153 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x156 : Span (checkTheta level8 level7 7) 156 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x159 : Span (checkTheta level8 level7 7) 159 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x162 : Span (checkTheta level8 level7 7) 162 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x165 : Span (checkTheta level8 level7 7) 165 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x168 : Span (checkTheta level8 level7 7) 168 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x171 : Span (checkTheta level8 level7 7) 171 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x174 : Span (checkTheta level8 level7 7) 174 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece8x177 : Span (checkTheta level8 level7 7) 177 2 := fromSpan (by decide +kernel)

private theorem checkLayer8 : ∀ i < stateCount level8, checkTheta level8 level7 7 i = true := (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan piece8x0 piece8x3) (joinSpan piece8x6 piece8x9)) (joinSpan (joinSpan piece8x12 piece8x15) (joinSpan piece8x18 piece8x21))) (joinSpan (joinSpan (joinSpan piece8x24 piece8x27) (joinSpan piece8x30 piece8x33)) (joinSpan (joinSpan piece8x36 piece8x39) (joinSpan piece8x42 piece8x45)))) (joinSpan (joinSpan (joinSpan (joinSpan piece8x48 piece8x51) (joinSpan piece8x54 piece8x57)) (joinSpan (joinSpan piece8x60 piece8x63) (joinSpan piece8x66 piece8x69))) (joinSpan (joinSpan (joinSpan piece8x72 piece8x75) (joinSpan piece8x78 piece8x81)) (joinSpan (joinSpan piece8x84 piece8x87) (joinSpan piece8x90 piece8x93))))) (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan piece8x96 piece8x99) (joinSpan piece8x102 piece8x105)) (joinSpan (joinSpan piece8x108 piece8x111) (joinSpan piece8x114 piece8x117))) (joinSpan (joinSpan (joinSpan piece8x120 piece8x123) (joinSpan piece8x126 piece8x129)) (joinSpan (joinSpan piece8x132 piece8x135) (joinSpan piece8x138 piece8x141)))) (joinSpan (joinSpan (joinSpan (joinSpan piece8x144 piece8x147) (joinSpan piece8x150 piece8x153)) (joinSpan (joinSpan piece8x156 piece8x159) (joinSpan piece8x162 piece8x165))) (joinSpan (joinSpan piece8x168 piece8x171) (joinSpan piece8x174 piece8x177)))))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x0 : Span (checkTheta level9 level8 8) 0 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x3 : Span (checkTheta level9 level8 8) 3 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x6 : Span (checkTheta level9 level8 8) 6 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x9 : Span (checkTheta level9 level8 8) 9 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x12 : Span (checkTheta level9 level8 8) 12 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x15 : Span (checkTheta level9 level8 8) 15 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x18 : Span (checkTheta level9 level8 8) 18 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x21 : Span (checkTheta level9 level8 8) 21 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x24 : Span (checkTheta level9 level8 8) 24 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x27 : Span (checkTheta level9 level8 8) 27 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x30 : Span (checkTheta level9 level8 8) 30 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x33 : Span (checkTheta level9 level8 8) 33 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x36 : Span (checkTheta level9 level8 8) 36 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x39 : Span (checkTheta level9 level8 8) 39 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x42 : Span (checkTheta level9 level8 8) 42 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x45 : Span (checkTheta level9 level8 8) 45 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x48 : Span (checkTheta level9 level8 8) 48 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x51 : Span (checkTheta level9 level8 8) 51 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x54 : Span (checkTheta level9 level8 8) 54 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x57 : Span (checkTheta level9 level8 8) 57 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x60 : Span (checkTheta level9 level8 8) 60 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x63 : Span (checkTheta level9 level8 8) 63 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x66 : Span (checkTheta level9 level8 8) 66 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x69 : Span (checkTheta level9 level8 8) 69 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x72 : Span (checkTheta level9 level8 8) 72 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x75 : Span (checkTheta level9 level8 8) 75 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x78 : Span (checkTheta level9 level8 8) 78 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x81 : Span (checkTheta level9 level8 8) 81 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x84 : Span (checkTheta level9 level8 8) 84 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x87 : Span (checkTheta level9 level8 8) 87 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x90 : Span (checkTheta level9 level8 8) 90 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x93 : Span (checkTheta level9 level8 8) 93 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x96 : Span (checkTheta level9 level8 8) 96 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x99 : Span (checkTheta level9 level8 8) 99 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x102 : Span (checkTheta level9 level8 8) 102 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x105 : Span (checkTheta level9 level8 8) 105 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x108 : Span (checkTheta level9 level8 8) 108 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x111 : Span (checkTheta level9 level8 8) 111 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x114 : Span (checkTheta level9 level8 8) 114 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x117 : Span (checkTheta level9 level8 8) 117 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x120 : Span (checkTheta level9 level8 8) 120 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x123 : Span (checkTheta level9 level8 8) 123 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x126 : Span (checkTheta level9 level8 8) 126 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x129 : Span (checkTheta level9 level8 8) 129 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x132 : Span (checkTheta level9 level8 8) 132 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x135 : Span (checkTheta level9 level8 8) 135 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x138 : Span (checkTheta level9 level8 8) 138 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x141 : Span (checkTheta level9 level8 8) 141 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x144 : Span (checkTheta level9 level8 8) 144 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x147 : Span (checkTheta level9 level8 8) 147 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x150 : Span (checkTheta level9 level8 8) 150 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x153 : Span (checkTheta level9 level8 8) 153 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x156 : Span (checkTheta level9 level8 8) 156 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x159 : Span (checkTheta level9 level8 8) 159 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x162 : Span (checkTheta level9 level8 8) 162 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x165 : Span (checkTheta level9 level8 8) 165 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x168 : Span (checkTheta level9 level8 8) 168 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x171 : Span (checkTheta level9 level8 8) 171 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x174 : Span (checkTheta level9 level8 8) 174 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x177 : Span (checkTheta level9 level8 8) 177 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x180 : Span (checkTheta level9 level8 8) 180 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x183 : Span (checkTheta level9 level8 8) 183 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x186 : Span (checkTheta level9 level8 8) 186 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x189 : Span (checkTheta level9 level8 8) 189 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x192 : Span (checkTheta level9 level8 8) 192 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x195 : Span (checkTheta level9 level8 8) 195 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece9x198 : Span (checkTheta level9 level8 8) 198 2 := fromSpan (by decide +kernel)

private theorem checkLayer9 : ∀ i < stateCount level9, checkTheta level9 level8 8 i = true := (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan piece9x0 piece9x3) (joinSpan piece9x6 piece9x9)) (joinSpan (joinSpan piece9x12 piece9x15) (joinSpan piece9x18 piece9x21))) (joinSpan (joinSpan (joinSpan piece9x24 piece9x27) (joinSpan piece9x30 piece9x33)) (joinSpan (joinSpan piece9x36 piece9x39) (joinSpan piece9x42 piece9x45)))) (joinSpan (joinSpan (joinSpan (joinSpan piece9x48 piece9x51) (joinSpan piece9x54 piece9x57)) (joinSpan (joinSpan piece9x60 piece9x63) (joinSpan piece9x66 piece9x69))) (joinSpan (joinSpan (joinSpan piece9x72 piece9x75) (joinSpan piece9x78 piece9x81)) (joinSpan (joinSpan piece9x84 piece9x87) (joinSpan piece9x90 piece9x93))))) (joinSpan (joinSpan (joinSpan (joinSpan (joinSpan piece9x96 piece9x99) (joinSpan piece9x102 piece9x105)) (joinSpan (joinSpan piece9x108 piece9x111) (joinSpan piece9x114 piece9x117))) (joinSpan (joinSpan (joinSpan piece9x120 piece9x123) (joinSpan piece9x126 piece9x129)) (joinSpan (joinSpan piece9x132 piece9x135) (joinSpan piece9x138 piece9x141)))) (joinSpan (joinSpan (joinSpan (joinSpan piece9x144 piece9x147) (joinSpan piece9x150 piece9x153)) (joinSpan (joinSpan piece9x156 piece9x159) (joinSpan piece9x162 piece9x165))) (joinSpan (joinSpan (joinSpan piece9x168 piece9x171) (joinSpan piece9x174 piece9x177)) (joinSpan (joinSpan piece9x180 piece9x183) (joinSpan piece9x186 piece9x189)))))) (joinSpan (joinSpan piece9x192 piece9x195) piece9x198))

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece10x0 : Span (checkTheta level10 level9 9) 0 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece10x3 : Span (checkTheta level10 level9 9) 3 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece10x6 : Span (checkTheta level10 level9 9) 6 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece10x9 : Span (checkTheta level10 level9 9) 9 3 := fromSpan (by decide +kernel)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece10x12 : Span (checkTheta level10 level9 9) 12 2 := fromSpan (by decide +kernel)

private theorem checkLayer10 : ∀ i < stateCount level10, checkTheta level10 level9 9 i = true := (joinSpan (joinSpan (joinSpan piece10x0 piece10x3) (joinSpan piece10x6 piece10x9)) piece10x12)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 6000000 in
private theorem piece11x0 : Span (checkTheta level11 level10 10) 0 1 := fromSpan (by decide +kernel)

private theorem checkLayer11 : ∀ i < stateCount level11, checkTheta level11 level10 10 i = true := piece11x0

private theorem excluded6 : ∀ i < stateCount level6, ¬ Reach (stateAt alphabet level6 i).toFinset 6 tableGoal := by
  intro i hi
  change i < 0 at hi
  omega

private theorem excluded7 : ∀ i < stateCount level7, ¬ Reach (stateAt alphabet level7 i).toFinset 7 tableGoal :=
  layerStep516 (by decide) fixedGoal checkLayer7 excluded6

private theorem excluded8 : ∀ i < stateCount level8, ¬ Reach (stateAt alphabet level8 i).toFinset 8 tableGoal :=
  layerStep516 (by decide) fixedGoal checkLayer8 excluded7

private theorem excluded9 : ∀ i < stateCount level9, ¬ Reach (stateAt alphabet level9 i).toFinset 9 tableGoal :=
  layerStep516 (by decide) fixedGoal checkLayer9 excluded8

private theorem excluded10 : ∀ i < stateCount level10, ¬ Reach (stateAt alphabet level10 i).toFinset 10 tableGoal :=
  layerStep516 (by decide) fixedGoal checkLayer10 excluded9

private theorem excluded11 : ∀ i < stateCount level11, ¬ Reach (stateAt alphabet level11 i).toFinset 11 tableGoal :=
  layerStep516 (by decide) fixedGoal checkLayer11 excluded10

theorem rootExcluded : ¬ Reach (stateAt alphabet level11 0).toFinset 11 tableGoal := excluded11 0 (by decide)

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {W : ℕ}

private def Known (w : Finset (BitVec W)) (a : (BitVec W)) : Prop :=
  a = 0 ∨ a = BitVec.allOnes W ∨ a ∈ w

private def wordOp (op : GateOp) (as : List (BitVec W)) : (BitVec W) :=
  match op, as with
  | .and, [] => BitVec.allOnes W
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes W
  | .not, a :: _ => ~~~a
  | _, _ => 0

private def wordStep (w : List (BitVec W)) (g : Gate) : (BitVec W) :=
  wordOp g.op (g.inputs.map fun i => w.getD i 0)

private def wordRun (w : List (BitVec W)) (gs : List Gate) : List (BitVec W) :=
  gs.foldl (fun ws g => ws ++ [wordStep ws g]) w

private def bits (w : List (BitVec W)) (j : ℕ) : List Bool :=
  w.map (fun a => a.getLsbD j)

private lemma bits_get (w : List (BitVec W)) (j i : ℕ) :
    (bits w j).getD i false = (w.getD i 0).getLsbD j := by
  simpa [bits] using (List.getD_map (l := w) (d := 0) (n := i)
    (fun a : (BitVec W) => a.getLsbD j))

private def Allowed (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

private theorem wordOp_bits (op : GateOp) (as : List (BitVec W)) (j : ℕ) (hj : j < W)
    (h : Allowed op) (hlen : as.length ≤ 2) :
    (wordOp op as).getLsbD j = op.eval (bits as j) := by
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      simp only [wordOp, GateOp.eval, bits, List.map_nil, List.all_nil,
        List.any_nil, List.headD_nil, BitVec.getLsbD_allOnes,
        hj, decide_true, Bool.not_false]
      all_goals exact BitVec.getLsbD_zero
    | cons a rest =>
      cases rest with
      | nil => simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil,
          List.all_cons, List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
      | cons b tail =>
        have ht : tail = [] := by simpa using hlen
        subst tail
        simp only [wordOp, GateOp.eval, bits, List.map_cons, List.map_nil, List.all_cons,
          List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil, Bool.and_true,
          Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj,
          decide_true, Bool.true_and]

private theorem wordStep_bits (g : Gate) (w : List (BitVec W)) (j : ℕ) (hj : j < W)
    (h : Allowed g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep w g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits w j).getD i false) := by
  rw [wordStep, wordOp_bits _ _ _ hj h (by simpa)]
  simp only [bits, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (bits_get w j i).symm

private theorem wordRun_bits (gs : List Gate) (ws : List (BitVec W)) (j : ℕ) (hj : j < W)
    (hok : ∀ g ∈ gs, Allowed g.op ∧ g.inputs.length ≤ 2) :
    bits (wordRun ws gs) j =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (bits ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change bits (wordRun (ws ++ [wordStep ws g]) gs) j = _
    rw [ih _ (fun g hg => hok g (List.mem_cons_of_mem _ hg))]
    simp only [List.foldl_cons]
    congr 1
    have hg := hok g List.mem_cons_self
    unfold bits
    rw [List.map_append]
    exact congrArg (fun a => (ws.map (fun b => b.getLsbD j)) ++ [a])
      (wordStep_bits g ws j hj hg.1 hg.2)

private theorem known_get {ws : List (BitVec W)} {w : Finset (BitVec W)}
    (hknown : ∀ a ∈ ws, Known w a) (i : ℕ) : Known w (ws.getD i 0) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hknown _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

private theorem andGate {w : Finset (BitVec W)} {a b : (BitVec W)}
    (ha : Known w a) (hb : Known w b) : Known w (a &&& b) ∨ Next w (a &&& b) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inl BitVec.zero_and)
  · simpa only [BitVec.allOnes_and] using Or.inl (b := Next w b) hb
  rcases hb with rfl | rfl | hb
  · exact Or.inl (Or.inl BitVec.and_zero)
  · exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_allOnes] using ha)))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inl rfl⟩)

private theorem orGate {w : Finset (BitVec W)} {a b : (BitVec W)}
    (ha : Known w a) (hb : Known w b) : Known w (a ||| b) ∨ Next w (a ||| b) := by
  rcases ha with rfl | rfl | ha
  · rw [show (0 : (BitVec W)) ||| b = b from BitVec.zero_or]
    exact Or.inl hb
  · exact Or.inl (Or.inr (Or.inl BitVec.allOnes_or))
  rcases hb with rfl | rfl | hb
  · rw [show a ||| (0 : (BitVec W)) = a from BitVec.or_zero]
    exact Or.inl (Or.inr (Or.inr ha))
  · exact Or.inl (Or.inr (Or.inl BitVec.or_allOnes))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.or_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inr rfl⟩)

private theorem notGate {w : Finset (BitVec W)} {a : (BitVec W)} (ha : Known w a) :
    Known w (~~~a) ∨ Next w (~~~a) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inr (Or.inl BitVec.not_zero))
  · exact Or.inl (Or.inl BitVec.not_allOnes)
  · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)

private theorem wordOp_next (w : Finset (BitVec W)) (op : GateOp) (as : List (BitVec W))
    (hknown : ∀ a ∈ as, Known w a) (hop : Allowed op) :
    Known w (wordOp op as) ∨ Next w (wordOp op as) := by
  rcases hop with rfl | rfl | rfl <;>
    cases as with
    | nil => first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr (Or.inl rfl))
    | cons a rest =>
      have ha := hknown a List.mem_cons_self
      cases rest with
      | nil => first | exact Or.inl ha | exact notGate ha
      | cons b tail =>
        have hb := hknown b (List.mem_cons_of_mem a List.mem_cons_self)
        first | exact andGate ha hb | exact orGate ha hb | exact notGate ha

private theorem reachable (w : Finset (BitVec W)) (ws : List (BitVec W)) (gs : List Gate)
    (k : ℕ) (o : ℕ) (t : (BitVec W)) (hk : gs.length ≤ k)
    (hknown : ∀ a ∈ ws, Known w a)
    (hok : ∀ g ∈ gs, Allowed g.op) (hzero : t ≠ 0) (hone : t ≠ BitVec.allOnes W)
    (ht : (wordRun ws gs).getD o 0 = t) : Reach w k t := by
  induction gs generalizing ws w k with
  | nil =>
    change ws.getD o 0 = t at ht
    have h := known_get hknown o
    rw [ht] at h
    have hmem := (h.resolve_left hzero).resolve_left hone
    cases k with
    | zero => exact hmem
    | succ k => exact Or.inl hmem
  | cons g gs ih =>
    let z := wordStep ws g
    change (wordRun (ws ++ [z]) gs).getD o 0 = t at ht
    have hrest := fun g' (hg' : g' ∈ gs) => hok g' (List.mem_cons_of_mem g hg')
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases h : Known w z
      · apply ih w (ws ++ [z]) (k+1) (by omega) _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hknown a ha
        · exact h
      · have hz : Known w z ∨ Next w z :=
          wordOp_next w g.op _ (by
            intro a ha
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact known_get hknown i) (hok g List.mem_cons_self)
        refine Or.inr ⟨z, fun hm => h (Or.inr (Or.inr hm)), fun h0 => h (Or.inl h0),
          fun h1 => h (Or.inr (Or.inl (h1.trans BitVec.not_zero))), hz.resolve_left h, ?_⟩
        apply ih (insert z w) (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · rcases hknown a ha with h0 | h1 | hm
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem hm))
        · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))


def row {n W : ℕ} (columns : Fin n → BitVec W) (j : ℕ) (i : Fin n) : Bool :=
  (columns i).getLsbD j

theorem table_reach {n W k : ℕ} (columns : Fin n → BitVec W) (w : Finset (BitVec W))
    {f : (Fin n → Bool) → Bool} {t : BitVec W}
    (hc : ∀ i, columns i = 0 ∨ columns i = BitVec.allOnes W ∨ columns i ∈ w)
    (hf : HasCircuitSize n f k) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes W)
    (hb : ∀ j : Fin W, f (row columns j.val) = t.getLsbD j.val) : Reach w k t := by
  obtain ⟨C, hok, hs, hev⟩ := hf
  have hok' : ∀ g ∈ C.gates, Allowed g.op ∧ g.inputs.length ≤ 2 := hok
  refine reachable w (List.ofFn columns) C.gates k C.output t hs ?_ (fun g hg => (hok' g hg).1) h0 h1 ?_
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hc i
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← bits_get, wordRun_bits _ _ _ hj hok']
    have hinput : bits (List.ofFn columns) j = List.ofFn (row columns j) := by
      unfold bits
      rw [List.map_ofFn]
      rfl
    rw [hinput]
    exact (hev (row columns j)).trans (hb ⟨j, hj⟩)

end PEqualNP.Outside.L_meta_516_aux

namespace PEqualNP.Outside.L_meta_516_aux

open PEqualNP.MetaComplexity

def inputSet516 : Finset (BitVec 256) :=
  {0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000}

def columns516 : Fin 8 → BitVec 256 :=
  ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]

def target516 : BitVec 256 := 0xfffffffffffffffffffffcecfeeefcecfffffeeefeaafeaafffffcecfeaafca0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem table_lower516 (h : ¬ Reach inputSet516 11 target516) :
    ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) 11 := by
  intro hf
  apply h
  exact table_reach columns516 inputSet516 (by decide) hf (by decide) (by decide) (by decide)

end PEqualNP.Outside.L_meta_516_aux

open PEqualNP.Outside.L_meta_516_aux

theorem PEqualNP.Outside.L_meta_516 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s := by
  intro s hs
  by_contra! hlt
  have hi : inputSet516 = (stateAt alphabet level11 0).toFinset := by decide
  have noTable : ¬ Reach inputSet516 11 target516 := by
    rw [hi]
    exact rootExcluded
  apply table_lower516 noTable
  obtain ⟨C,hf,hsize,he⟩ := hs
  exact ⟨C,hf,by omega,he⟩
