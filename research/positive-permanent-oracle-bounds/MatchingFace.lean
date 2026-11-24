import RegularMatchings
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.Ring

namespace PositivePermanent
open Filter Finset
open scoped Topology BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

def value (a : I→I→ℝ) (s : Equiv.Perm I) : ℝ := ∏ i,a i (s i)

def monomial (a : I→I→ℝ) (m : I→I→ℕ) : ℝ := ∏ i,∏ j,(a i j)^(m i j)

omit [DecidableEq I] in
lemma monomial_add (a : I→I→ℝ) (m n : I→I→ℕ) :
    monomial a (fun i j=>m i j+n i j)=monomial a m*monomial a n := by
  simp [monomial,pow_add,Finset.prod_mul_distrib]

lemma monomial_inc (a : I→I→ℝ) (s : Equiv.Perm I) : monomial a (incidence s)=value a s := by
  unfold monomial value
  apply Finset.prod_congr rfl
  intro i _
  have eq (j : I) : (a i j)^(incidence s i j) = if s i=j then a i j else 1 := by
    by_cases h : s i=j <;> simp [incidence,h]
  simp_rw [eq]
  simp [Finset.prod_ite_eq]

lemma multiset_weight (c : ℝ) (a : I→I→ℝ) (ss : List (Equiv.Perm I)) :
    (ss.map (fun s=>c*value a s)).prod = c^ss.length*monomial a (counts ss) := by
  induction ss with
  | nil => simp [counts,monomial]
  | cons s ss ih =>
    have eq : counts (s::ss) = fun i j=>incidence s i j+counts ss i j := funext fun i=>funext fun j=>counts_cons s ss i j
    simp only [List.map_cons,List.prod_cons,ih,List.length_cons,pow_succ,eq,monomial_add,monomial_inc]
    ring

omit [Fintype I] in
lemma counts_pos {ss : List (Equiv.Perm I)} {s : Equiv.Perm I} (h : s∈ss) (i : I) :
    0<counts ss i (s i) := by
  induction ss with
  | nil => simp at h
  | cons t ts ih =>
    rw [counts_cons]
    rcases List.mem_cons.mp h with e|m
    · subst t; simp [incidence]
    · have := ih m; omega

lemma replace_matching (ss : List (Equiv.Perm I)) (s : Equiv.Perm I)
    (ne : 0<ss.length) (admiss : ∀ i,0<counts ss i (s i)) :
    ∃ tail : List (Equiv.Perm I), (s::tail).length=ss.length ∧ counts (s::tail)=counts ss := by
  have n : ss.length=ss.length-1+1 := by omega
  obtain ⟨N,reg,split⟩ := remove_regular (counts ss) s (n ▸ counts_regular ss) admiss
  obtain ⟨tail,len,eq⟩ := decompose N _ reg
  exact ⟨tail,by simp [len]; omega,funext fun i=>funext fun j=>by rw [counts_cons,eq,←split]⟩

omit [Fintype I] [DecidableEq I] in
lemma list_lim (ss : List (Equiv.Perm I)) (weights : ℕ→Equiv.Perm I→ℝ) (w : Equiv.Perm I→ℝ)
    (lim : ∀ s,Tendsto (fun j=>weights j s) atTop (𝓝 (w s))) :
    Tendsto (fun j=>(ss.map (weights j)).prod) atTop (𝓝 ((ss.map w).prod)) := by
  induction ss with
  | nil => simp
  | cons s ts ih => exact (lim s).mul ih

/-- If there is at least one positive limiting permutation, all permutations
supported on their edge union have positive limiting midpoint weight. -/
theorem limit_face (c : ℕ→ℝ) (a : ℕ→I→I→ℝ) (w : Equiv.Perm I→ℝ)
    (lim : ∀ s,Tendsto (fun j=>c j*value (a j) s) atTop (𝓝 (w s)))
    (nonneg : ∀ s,0≤w s) (ne : ∃ s,0<w s) (s : Equiv.Perm I)
    (support : ∀ i,∃ t,0<w t ∧ t i=s i) : 0<w s := by
  classical
  let ss := (Finset.univ.filter (fun t : Equiv.Perm I=>0<w t)).toList
  have mem (t : Equiv.Perm I) : t∈ss ↔ 0<w t := by simp [ss]
  obtain ⟨s0,positive⟩ := ne
  have length_pos : 0<ss.length := List.length_pos_of_mem ((mem s0).mpr positive)
  have allowed (i) : 0<counts ss i (s i) := by
    obtain ⟨t,pt,e⟩ := support i
    rw [←e]; exact counts_pos ((mem t).mpr pt) i
  obtain ⟨rest,len,eq⟩ := replace_matching ss s length_pos allowed
  let weights := fun j (t : Equiv.Perm I)=>c j*value (a j) t
  have equal (j : ℕ) : (ss.map (weights j)).prod=((s::rest).map (weights j)).prod := by
    dsimp only [weights]; rw [multiset_weight,multiset_weight,len,eq]
  have pos : 0<(ss.map w).prod := by
    apply List.prod_pos
    intro v hv
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hv
    exact (mem t).mp ht
  have e : (ss.map w).prod=((s::rest).map w).prod := tendsto_nhds_unique
    (list_lim ss weights w lim) ((list_lim (s::rest) weights w lim).congr' (Filter.Eventually.of_forall (fun j=>(equal j).symm)))
  rw [e,List.map_cons,List.prod_cons] at pos
  exact lt_of_le_of_ne (nonneg s) (fun z=>by rw [←z,zero_mul] at pos; exact lt_irrefl _ pos)

end
end PositivePermanent
#print axioms PositivePermanent.limit_face
