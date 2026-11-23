import TaintedOR

namespace TaintedOR
open Finset
open scoped Classical

/-- A finite straight-line OR table. Free wires carry at most one raw label. -/
structure Table (V : Type*) [DecidableEq V] where
  nodes : Finset ℕ
  S : ℕ → Finset V
  l : ℕ → ℕ
  r : ℕ → ℕ
  split : ∀ g∈nodes, l g<g ∧ r g<g ∧ S g=S (l g)∪S (r g)
  primary : ∀ g, g∉nodes → (S g).card≤1

namespace Table
variable {V I : Type*} [DecidableEq V] (D : Table V) (Q : Queries V I)

def projected (i : I) (g : ℕ) := D.S g∩Q.need i

noncomputable def charge (i : I) (g : ℕ) : ℕ :=
  if Q.major i (D.S (D.l g)) (D.S (D.r g)) then 2 else
  if Q.minor i (D.S (D.l g)) (D.S (D.r g)) then 1 else 0

def sound (i : I) (g : ℕ) : Prop :=
  g∈D.nodes ∧ Q.useful i (D.S (D.l g)) (D.S (D.r g))

private theorem resolve (i : I) (g : ℕ) (bound : D.S g⊆Q.supply i)
    (wide : 2≤(D.projected Q i g).card) :
    ∃ w, D.sound Q i w ∧ D.projected Q i w=D.projected Q i g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    have gn : g∈D.nodes := by
      by_contra h
      have s := D.primary _ h
      have t : (D.projected Q i g).card ≤ (D.S g).card := Finset.card_le_card Finset.inter_subset_left
      omega
    obtain ⟨le,ri,un⟩ := D.split g gn
    have ll : D.S (D.l g)⊆D.S g := un ▸ Finset.subset_union_left
    have rr : D.S (D.r g)⊆D.S g := un ▸ Finset.subset_union_right
    by_cases bl : D.projected Q i g=D.projected Q i (D.l g)
    · obtain ⟨w,h,eq⟩ := ih (D.l g) le (ll.trans bound) (bl ▸ wide)
      exact ⟨w,h,eq.trans bl.symm⟩
    by_cases br : D.projected Q i g=D.projected Q i (D.r g)
    · obtain ⟨w,h,eq⟩ := ih (D.r g) ri (rr.trans bound) (br ▸ wide)
      exact ⟨w,h,eq.trans br.symm⟩
    refine ⟨g,⟨gn,un ▸ bound,?_,?_⟩,rfl⟩
    · by_contra! bad
      apply br
      ext x
      simp only [projected,un,Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨h,hn⟩
        rcases h with xl | xr
        · exact ⟨by_contra fun no => bad x (Finset.mem_sdiff.mpr ⟨xl,no⟩) hn,hn⟩
        · exact ⟨xr,hn⟩
      · exact fun h => ⟨Or.inr h.1,h.2⟩
    · by_contra! bad
      apply bl
      ext x
      simp only [projected,un,Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨h,hn⟩
        rcases h with xl | xr
        · exact ⟨xl,hn⟩
        · exact ⟨by_contra fun no => bad x (Finset.mem_sdiff.mpr ⟨xr,no⟩) hn,hn⟩
      · exact fun h => ⟨Or.inl h.1,h.2⟩

private theorem projected_split {i : I} {g : ℕ} (h : D.sound Q i g) :
    D.projected Q i g=D.projected Q i (D.l g)∪D.projected Q i (D.r g) ∧
    (D.projected Q i (D.l g)).card<(D.projected Q i g).card ∧
    (D.projected Q i (D.r g)).card<(D.projected Q i g).card ∧ D.S g⊆Q.supply i := by
  obtain ⟨gn,raw,⟨a,ha,an⟩,⟨b,hb,bn⟩⟩ := h
  have un := (D.split _ gn).2.2
  have eq : D.projected Q i g=D.projected Q i (D.l g)∪D.projected Q i (D.r g) := by
    ext x
    simp only [projected,un,Finset.mem_union,Finset.mem_inter]
    tauto
  refine ⟨eq,Finset.card_lt_card ?_,Finset.card_lt_card ?_,un ▸ raw⟩
  · rw [eq]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left,?_⟩
    intro same
    have mem : b∈D.projected Q i (D.l g)∪D.projected Q i (D.r g) :=
      Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hb).1,bn⟩)
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp (same.symm ▸ mem)).1
  · rw [eq]
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right,?_⟩
    intro same
    have mem : a∈D.projected Q i (D.l g)∪D.projected Q i (D.r g) :=
      Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp ha).1,an⟩)
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp (same.symm ▸ mem)).1

private theorem charge_small {i : I} {g : ℕ} (h : D.sound Q i g) (err : Q.err i≤1) :
    (if Q.err i=0 ∨ 3≤(D.projected Q i g).card then 2 else 1) ≤ D.charge Q i g := by
  have hm : Q.minor i (D.S (D.l g)) (D.S (D.r g)) := ⟨err,h.2⟩
  by_cases hs : Q.err i=0 ∨ 3≤(D.projected Q i g).card
  · have big : Q.major i (D.S (D.l g)) (D.S (D.r g)) := Or.inr ⟨hm,by
      simpa only [projected,(D.split _ h.1).2.2] using hs⟩
    simp [charge,hs,big]
  · by_cases big : Q.major i (D.S (D.l g)) (D.S (D.r g)) <;> simp [charge,hs,big,hm]

private theorem sum_three (i : I) {a b c : ℕ} (ha : a∈D.nodes) (hb : b∈D.nodes)
    (hc : c∈D.nodes) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    D.charge Q i a+D.charge Q i b+D.charge Q i c≤∑ j∈D.nodes,D.charge Q i j := by
  have sub : {a,b,c}⊆D.nodes := by intro j hj; simp only [Finset.mem_insert,Finset.mem_singleton] at hj; grind
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f:=D.charge Q i) sub (by simp)
  simpa [ab,ac,bc,Nat.add_assoc] using h

private theorem sum_two (i : I) {a b : ℕ} (ha : a∈D.nodes) (hb : b∈D.nodes) (ab : a≠b) :
    D.charge Q i a+D.charge Q i b≤∑ j∈D.nodes,D.charge Q i j := by
  have sub : {a,b}⊆D.nodes := by intro j hj; simp only [Finset.mem_insert,Finset.mem_singleton] at hj; grind
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f:=D.charge Q i) sub (by simp)
  simpa [ab] using h

private theorem child_with_two {i : I} {w : ℕ} (h : D.sound Q i w)
    (hw : 3=(D.projected Q i w).card) : ∃ g, D.sound Q i g ∧ (D.projected Q i g).card=2 := by
  obtain ⟨eq,l,r,sub⟩ := D.projected_split Q h
  have lim := Finset.card_union_le (D.projected Q i (D.l w)) (D.projected Q i (D.r w))
  rw [← eq] at lim
  have lin := (D.split w h.1).2.2
  by_cases left : 2≤(D.projected Q i (D.l w)).card
  · obtain ⟨g,hg,ge⟩ := D.resolve Q i (D.l w) (Finset.subset_union_left.trans (lin ▸ sub)) left
    exact ⟨g,hg,by rw [ge]; omega⟩
  · have right : 2≤(D.projected Q i (D.r w)).card := by omega
    obtain ⟨g,hg,ge⟩ := D.resolve Q i (D.r w) (Finset.subset_union_right.trans (lin ▸ sub)) right
    exact ⟨g,hg,by rw [ge]; omega⟩

private theorem children_of_four {i : I} {w : ℕ} (h : D.sound Q i w)
    (hw : (D.projected Q i w).card=4) :
    ∃ a b, D.sound Q i a ∧ D.sound Q i b ∧ w≠a ∧ w≠b ∧ a≠b ∧
      2≤(D.projected Q i a).card ∧ 2≤(D.projected Q i b).card := by
  obtain ⟨eq,ls,rs,sub⟩ := D.projected_split Q h
  have le := Finset.card_union_le (D.projected Q i (D.l w)) (D.projected Q i (D.r w))
  rw [← eq] at le
  have lin := (D.split w h.1).2.2
  have lsub : D.S (D.l w)⊆Q.supply i := Finset.subset_union_left.trans (lin ▸ sub)
  have rsub : D.S (D.r w)⊆Q.supply i := Finset.subset_union_right.trans (lin ▸ sub)
  have three (v : ℕ) (sv : D.S v⊆Q.supply i) (vc : (D.projected Q i v).card=3) :
      ∃ a b, D.sound Q i a ∧ D.sound Q i b ∧ w≠a ∧ w≠b ∧ a≠b ∧
        2≤(D.projected Q i a).card ∧ 2≤(D.projected Q i b).card := by
    obtain ⟨a,ha,ae⟩ := D.resolve Q i v sv (by omega)
    have ca : (D.projected Q i a).card=3 := ae ▸ vc
    obtain ⟨b,hb,cb⟩ := D.child_with_two Q ha ca.symm
    exact ⟨a,b,ha,hb,fun e => by rw [e] at hw; omega,fun e => by rw [e] at hw; omega,
      fun e => by rw [e] at ca; omega,by omega,by omega⟩
  by_cases cl : (D.projected Q i (D.l w)).card=3
  · exact three _ lsub cl
  by_cases cr : (D.projected Q i (D.r w)).card=3
  · exact three _ rsub cr
  have cl2 : (D.projected Q i (D.l w)).card=2 := by omega
  have cr2 : (D.projected Q i (D.r w)).card=2 := by omega
  obtain ⟨a,ha,ae⟩ := D.resolve Q i (D.l w) lsub cl2.ge
  obtain ⟨b,hb,be⟩ := D.resolve Q i (D.r w) rsub cr2.ge
  have ca : (D.projected Q i a).card=2 := ae ▸ cl2
  have cb : (D.projected Q i b).card=2 := be ▸ cr2
  have distinct : a≠b := by
    rintro rfl
    rw [← ae,← be,Finset.union_idempotent] at eq
    exact (by omega : (D.projected Q i a).card≠4) (eq ▸ hw)
  exact ⟨a,b,ha,hb,fun e => by rw [e] at hw; omega,fun e => by rw [e] at hw; omega,
    distinct,ca.ge,cb.ge⟩

private theorem local_budget (i : I) (out : ℕ) (sup : D.S out=Q.supply i) :
    2*((Q.need i).card-1-Q.err i) ≤ ∑ j∈D.nodes,D.charge Q i j := by
  have all : D.projected Q i out=Q.need i := by
    simp [projected,sup,Finset.inter_eq_right.mpr (Q.sub i)]
  have small := Q.small i
  by_cases active : 0<(Q.need i).card-1-Q.err i
  · have wide : 2≤(D.projected Q i out).card := by rw [all]; omega
    by_cases ee : Q.err i≤1
    · obtain ⟨w,hw,eq⟩ := D.resolve Q i out sup.le wide
      have cw : (D.projected Q i w).card=(Q.need i).card := congrArg Finset.card (eq.trans all)
      have single := Finset.single_le_sum (f:=D.charge Q i) (fun _ _ => Nat.zero_le _) hw.1
      have charge := D.charge_small Q hw ee
      by_cases two : (Q.need i).card=2
      · have er : Q.err i=0 := by omega
        simp [er] at charge
        omega
      by_cases three : (Q.need i).card=3
      · obtain ⟨a,ha,ca⟩ := D.child_with_two Q hw (by omega)
        have wa : w≠a := fun e => by rw [e] at cw; omega
        have sa := D.sum_two Q i hw.1 ha.1 wa
        have a1 := D.charge_small Q ha ee
        by_cases er : Q.err i=0 <;> simp [er,cw,three,ca] at charge a1 <;> omega
      · have four : (Q.need i).card=4 := by omega
        obtain ⟨a,b,ha,hb,wa,wb,ab,ca,cb⟩ := D.children_of_four Q hw (by omega)
        have hs := D.sum_three Q i hw.1 ha.1 hb.1 wa wb ab
        have ac := D.charge_small Q ha ee
        have bc := D.charge_small Q hb ee
        by_cases er : Q.err i=0
        · simp [er] at charge ac bc
          omega
        · simp [er,cw,four] at charge
          split at ac <;> split at bc <;> omega
    · have er : Q.err i=2 := by omega
      have four : (Q.need i).card=4 := by omega
      have gn : out∈D.nodes := by
        by_contra no
        have no := D.primary _ no
        have t : (D.projected Q i out).card≤(D.S out).card := Finset.card_le_card Finset.inter_subset_left
        omega
      have u := (D.split _ gn).2.2
      have big : Q.major i (D.S (D.l out)) (D.S (D.r out)) := Or.inl ⟨four,er,u.symm.trans sup⟩
      have h := Finset.single_le_sum (f:=D.charge Q i) (fun _ _ => Nat.zero_le _) gn
      have co : D.charge Q i out = 2 := by simp [charge,big]
      rw [co] at h
      omega
  · omega

/-- Error-tolerant counting for a collection of C4-free OR queries of width at most four. -/
theorem approximate_queries [Fintype I] (out : I → ℕ) (sup : ∀ i, D.S (out i)=Q.supply i) :
    (∑ i : I, ((Q.need i).card-1-Q.err i)) ≤ D.nodes.card := by
  classical
  have lo := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => D.local_budget Q i (out i) (sup i))
  rw [← Finset.mul_sum,Finset.sum_comm] at lo
  have per (w : ℕ) : (∑ i : I, D.charge Q i w) ≤ 2 := by
    let A := D.S (D.l w)
    let B := D.S (D.r w)
    have identity (i : I) : D.charge Q i w =
        (if Q.major i A B then 2 else 0) +
        (if Q.minor i A B ∧ ¬Q.major i A B then 1 else 0) := by
      by_cases h : Q.major i A B <;> by_cases m : Q.minor i A B <;> simp [charge,A,B] at * <;> simp_all
    simp_rw [identity]
    rw [Finset.sum_add_distrib]
    have c2 : (∑ i : I, if Q.major i A B then 2 else 0) =
        2*(Finset.univ.filter (fun i => Q.major i A B)).card := by
      rw [← Finset.sum_filter]
      simp [Nat.mul_comm]
    rw [c2]
    simpa using Q.gate_budget A B
  have hi := Finset.sum_le_sum (s:=D.nodes) (fun w _ => per w)
  simp at hi
  omega

end Table
end TaintedOR

#print axioms TaintedOR.Table.approximate_queries
