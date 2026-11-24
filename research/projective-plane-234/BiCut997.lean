import WindowCore997
namespace PEqualNP.Outside.Window997
open PEqualNP.CircuitLowerBounds
/-- Expand a family of physical wires. Only members of Q can add a second
frontier slot; every other expanded gate uses at most one predecessor. -/
theorem asymmetric_cut997 {α : Type*} (lab : ℕ → Prop) (val : α → ℕ → Prop)
    (G Q : Finset ℕ)
    (step : ∀ w ∈ G, lab w → ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ Q → P.card ≤ 1) ∧
      (∀ r ∈ P, r < w ∧ lab r) ∧ ∀ x, (∀ r ∈ P, val x r) → val x w)
    (t : ℕ) (F : Finset ℕ) (live : ∀ w ∈ F, lab w) (earlier : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ (∀ w ∈ B, lab w) ∧ B.card ≤ F.card + (Q.filter (· < t)).card ∧
      ∀ x, (∀ w ∈ B, val x w) → ∀ w ∈ F, val x w := by
  classical
  induction t generalizing F with
  | zero =>
    exact ⟨F,Finset.disjoint_left.mpr (fun w hw hg => by have := earlier w hw hg; omega),
      live,Nat.le_add_right ..,fun _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P,h2,h1,hp,forward⟩ := step t hex.2 (live _ hex.1)
      let F' := F.erase t ∪ P
      have live' (w) (hw : w ∈ F') : lab w := by
        rcases Finset.mem_union.mp hw with hw|hw
        · exact live w (Finset.mem_erase.mp hw).2
        · exact (hp w hw).2
      have earlier' (w) (hw : w ∈ F') (hg : w ∈ G) : w < t := by
        rcases Finset.mem_union.mp hw with hw|hw
        · obtain ⟨hne,hw⟩ := Finset.mem_erase.mp hw
          have := earlier w hw hg
          omega
        · exact (hp w hw).1
      obtain ⟨B,hd,hl,hc,ht⟩ := ih F' live' earlier'
      have hcount := Finset.card_union_le (F.erase t) P
      change F'.card ≤ _ at hcount
      have he := Finset.card_erase_add_one hex.1
      refine ⟨B,hd,hl,?_,?_⟩
      · by_cases hq : t ∈ Q
        · have hh : Q.filter (· < t+1) = insert t (Q.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter,Finset.mem_insert]
            constructor
            · rintro ⟨hw,le⟩; by_cases h : w=t
              · exact Or.inl h
              · exact Or.inr ⟨hw,by omega⟩
            · rintro (rfl|⟨hw,le⟩)
              · exact ⟨hq,by omega⟩
              · exact ⟨hw,by omega⟩
          rw [hh,Finset.card_insert_of_notMem (by simp)]
          omega
        · have hsmall := h1 hq
          have hl' : (Q.filter (· < t)).card ≤ (Q.filter (· < t+1)).card :=
            Finset.card_le_card (fun w hw => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2;omega⟩)
          omega
      · intro x hx w hw
        by_cases heq : w=t
        · subst w
          exact forward x (fun r hr => ht x hx _ (Finset.mem_union_right _ hr))
        · exact ht x hx w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq,hw⟩))
    · have earlier' (w) (hw : w ∈ F) (hg : w ∈ G) : w < t := by
        have hne : w ≠ t := fun eq => hex ⟨eq ▸ hw,eq ▸ hg⟩
        have := earlier w hw hg
        omega
      obtain ⟨B,hd,hl,hc,ht⟩ := ih F live earlier'
      have hl' : (Q.filter (· < t)).card ≤ (Q.filter (· < t+1)).card :=
        Finset.card_le_card (fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2;omega⟩)
      exact ⟨B,hd,hl,by omega,ht⟩

noncomputable def branch997 {n : ℕ} (C : Circuit) (G : Finset ℕ) (b : Bool) : Finset ℕ := by
  classical
  exact G.filter fun w => ∃ i : Fin C.gates.length, n+i.val=w ∧ C.gates[i].op=(if b then .and else .or)

lemma gate_certificate997 {n} (C : Circuit) (hG : monoG C) (G : Finset ℕ) (b : Bool)
    (x : Fin n → Bool) (w : ℕ) (hwG : w ∈ G) (hn : n ≤ w) (hw : w < n+C.size) (truth : value C x w = b) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ branch997 (n:=n) C G b → P.card ≤ 1) ∧
      (∀ r ∈ P, r < w ∧ value C x r = b) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ P, value C y r = b) → value C y w = b := by
  classical
  let i : Fin C.gates.length := ⟨w-n,by change w-n < C.size;omega⟩
  let g := C.gates[i]
  obtain ⟨hOp,hlen⟩ := hG g (List.getElem_mem _)
  let bitsAt (y : Fin n → Bool) (r : ℕ) := if r < w then value C y r else false
  have eqn (y) : value C y w = g.op.eval (g.inputs.map (bitsAt y)) := gate_value C y w hn hw
  rw [eqn] at truth
  let inputs := g.inputs.toFinset.filter (· < w)
  have hsize : inputs.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
  have present {r} (hr : r ∈ g.inputs) (hlt : r < w) : r ∈ inputs :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hlt⟩
  have atInput {r} (hr : r ∈ inputs) : r ∈ g.inputs ∧ r < w :=
    ⟨List.mem_toFinset.mp (Finset.mem_filter.mp hr).1,(Finset.mem_filter.mp hr).2⟩
  have branch (hb : g.op=(if b then .and else .or)) : w ∈ branch997 (n:=n) C G b :=
    Finset.mem_filter.mpr ⟨hwG,i,by dsimp [i];omega,hb⟩
  cases b with
  | true =>
    rcases hOp with hop|hop
    · have hbr := branch hop
      simp only [hop,GateOp.eval,List.all_eq_true,id_eq] at truth
      refine ⟨inputs,hsize,fun h => False.elim (h hbr),?_,?_⟩
      · intro r hr
        obtain ⟨hrg,hlt⟩ := atInput hr
        exact ⟨hlt,by simpa [bitsAt,hlt] using truth _ (List.mem_map.mpr ⟨r,hrg,rfl⟩)⟩
      · intro y hy
        rw [eqn]
        simp only [hop,GateOp.eval,List.all_eq_true,id_eq]
        intro f hf
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
        have hlt : r < w := by
          by_contra hh
          have h := truth _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
          simp [bitsAt,hh] at h
        simpa [bitsAt,hlt] using hy r (present hr hlt)
    · simp only [hop,GateOp.eval,List.any_eq_true,id_eq] at truth
      obtain ⟨bb,hbb,hv⟩ := truth
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hbb
      have hlt : r < w := by by_contra h;simp [bitsAt,h] at hv
      refine ⟨{r},by simp,by simp,?_,?_⟩
      · intro t ht
        obtain rfl := Finset.mem_singleton.mp ht
        exact ⟨hlt,by simpa [bitsAt,hlt] using hv⟩
      · intro y hy
        rw [eqn]
        simp only [hop,GateOp.eval,List.any_eq_true,id_eq]
        exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,by simpa [bitsAt,hlt] using hy r (Finset.mem_singleton_self _)⟩
  | false =>
    rcases hOp with hop|hop
    · have hbad : ∃ r ∈ g.inputs, bitsAt x r=false := by
        by_contra! h
        have htrue : g.op.eval (g.inputs.map (bitsAt x)) = true := by
          simp only [hop,GateOp.eval,List.all_eq_true,id_eq]
          intro f hf
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
          cases hv : bitsAt x r with
          | false => exact False.elim ((h r hr) hv)
          | true => rfl
        exact Bool.false_ne_true (truth.symm.trans htrue)
      obtain ⟨r,hr,hv⟩ := hbad
      have conclude (y) (hy : bitsAt y r=false) : value C y w=false := by
        apply Bool.eq_false_iff.mpr
        intro htrue
        rw [eqn] at htrue
        simp only [hop,GateOp.eval,List.all_eq_true,id_eq] at htrue
        exact Bool.false_ne_true (hy.symm.trans (htrue _ (List.mem_map.mpr ⟨r,hr,rfl⟩)))
      by_cases hlt : r < w
      · refine ⟨{r},by simp,by simp,?_,?_⟩
        · intro t ht
          obtain rfl := Finset.mem_singleton.mp ht
          exact ⟨hlt,by simpa [bitsAt,hlt] using hv⟩
        · intro y hy
          exact conclude y (by simpa [bitsAt,hlt] using hy r (Finset.mem_singleton_self _))
      · exact ⟨∅,by simp,by simp,by simp,fun y _ => conclude y (by simp [bitsAt,hlt])⟩
    · have hbr := branch hop
      have hall {r} (hr : r ∈ g.inputs) : bitsAt x r = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have htrue : g.op.eval (g.inputs.map (bitsAt x))=true := by
          simp only [hop,GateOp.eval,List.any_eq_true,id_eq]
          exact ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,h⟩
        exact Bool.false_ne_true (truth.symm.trans htrue)
      refine ⟨inputs,hsize,fun h => False.elim (h hbr),?_,?_⟩
      · intro r hr
        obtain ⟨hrg,hlt⟩ := atInput hr
        exact ⟨hlt,by simpa [bitsAt,hlt] using hall hrg⟩
      · intro y hy
        apply Bool.eq_false_iff.mpr
        intro htrue
        rw [eqn] at htrue
        simp only [hop,GateOp.eval,List.any_eq_true,id_eq] at htrue
        obtain ⟨f,hf,hb⟩ := htrue
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hf
        by_cases hlt : r < w
        · have hh := hy r (present hr hlt)
          simp [bitsAt,hlt,hh] at hb
        · simp [bitsAt,hlt] at hb

theorem gate_witness997 {n} (C : Circuit) (hg : monoG C) (G : Finset ℕ)
    (hG : ∀ w ∈ G, n ≤ w ∧ w < n+C.size) (b : Bool) (x : Fin n → Bool) (w : ℕ) (h : value C x w = b) :
    ∃ B : Finset ℕ, Disjoint B G ∧ (∀ r ∈ B, value C x r=b) ∧
      B.card ≤ 1+(branch997 (n:=n) C G b).card ∧
      ∀ y : Fin n → Bool, (∀ r ∈ B, value C y r=b) → value C y w=b := by
  obtain ⟨B,hd,hl,hc,hf⟩ := asymmetric_cut997
    (fun r => value C x r=b) (fun y r => value C y r=b) G (branch997 (n:=n) C G b)
    (fun r hr hv => gate_certificate997 C hg G b x r hr (hG r hr).1 (hG r hr).2 hv)
    (n+C.size) {w} (by simpa using h) (fun r _ hr => (hG r hr).2)
  have hh := Finset.card_filter_le (branch997 (n:=n) C G b) (· < n+C.size)
  simp only [Finset.card_singleton] at hc
  exact ⟨B,hd,hl,by omega,fun y hy => hf y hy _ (Finset.mem_singleton_self _)⟩

#print axioms gate_witness997
end PEqualNP.Outside.Window997
