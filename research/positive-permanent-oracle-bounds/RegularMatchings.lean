import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Integral regular bipartite multigraphs decompose into perfect matchings.
All variables index labeled rows and columns. -/
namespace PositivePermanent
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

def incidence (s : Equiv.Perm I) (i j : I) : ℕ := if s i=j then 1 else 0

def Regular (M : I→I→ℕ) (k : ℕ) : Prop :=
  (∀ i, ∑ j,M i j=k) ∧ (∀ j,∑ i,M i j=k)

lemma incidence_regular (s : Equiv.Perm I) : Regular (incidence s) 1 := by
  constructor
  · intro i; simp [incidence,Finset.sum_ite_eq]
  · intro j; simp [incidence,←s.eq_symm_apply,Finset.sum_ite_eq']

lemma regular_has_matching (M : I→I→ℕ) {k : ℕ} (pos : 0<k) (h : Regular M k) :
    ∃ s : Equiv.Perm I, ∀ i, 0<M i (s i) := by
  classical
  let f := fun i=>Finset.univ.filter (fun j=>0<M i j)
  have hall (S : Finset I) : S.card≤(S.biUnion f).card := by
    let T := S.biUnion f
    have row (i : I) (hi : i∈S) : ∑ j∈T,M i j=k := by
      rw [←h.1 i]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have absent : j∉f i := fun present=>hj (Finset.mem_biUnion.mpr ⟨i,hi,present⟩)
      simpa [f] using absent
    have total : S.card*k ≤ T.card*k := calc
      S.card*k = ∑ i∈S,∑ j∈T,M i j := by simp [Finset.sum_congr rfl row]
      _ = ∑ j∈T,∑ i∈S,M i j := Finset.sum_comm
      _ ≤ ∑ j∈T,∑ i,M i j := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
      _ = T.card*k := by simp [h.2]
    exact Nat.le_of_mul_le_mul_right total pos
  obtain ⟨g,hg,admiss⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective f).mp hall
  let s := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  exact ⟨s,fun i=>(Finset.mem_filter.mp (admiss i)).2⟩

def counts (ss : List (Equiv.Perm I)) (i j : I) : ℕ :=
  (ss.map (fun s=>incidence s i j)).sum

omit [Fintype I] in
lemma counts_cons (s : Equiv.Perm I) (ss : List (Equiv.Perm I)) (i j : I) :
    counts (s::ss) i j=incidence s i j+counts ss i j := by simp [counts]

lemma counts_regular (ss : List (Equiv.Perm I)) : Regular (counts ss) ss.length := by
  induction ss with
  | nil => simp [Regular,counts]
  | cons s ss ih =>
    constructor
    · intro i
      simp only [counts_cons,Finset.sum_add_distrib,(incidence_regular s).1,ih.1,List.length_cons]
      omega
    · intro j
      simp only [counts_cons,Finset.sum_add_distrib,(incidence_regular s).2,ih.2,List.length_cons]
      omega

lemma remove_regular (M : I→I→ℕ) (s : Equiv.Perm I) {k : ℕ} (h : Regular M (k+1))
    (cover : ∀ i,0<M i (s i)) :
    ∃ N : I→I→ℕ, Regular N k ∧ ∀ i j, M i j=incidence s i j + N i j := by
  let N := fun i j=>M i j-incidence s i j
  have split (i j) : M i j=incidence s i j+N i j := by
    have le_ : incidence s i j≤M i j := by
      by_cases e : s i=j
      · subst j; simp [incidence]; exact Nat.succ_le_of_lt (cover i)
      · simp [incidence,e]
    exact (Nat.add_sub_of_le le_).symm
  refine ⟨N,⟨?_,?_⟩,split⟩
  · intro i
    have eq := h.1 i
    simp_rw [split i,Finset.sum_add_distrib,(incidence_regular s).1] at eq
    omega
  · intro j
    have eq := h.2 j
    simp_rw [fun i=>split i j,Finset.sum_add_distrib,(incidence_regular s).2] at eq
    omega

theorem decompose (M : I→I→ℕ) (k : ℕ) (h : Regular M k) :
    ∃ ss : List (Equiv.Perm I), ss.length=k ∧ counts ss=M := by
  induction k generalizing M with
  | zero =>
    refine ⟨[],rfl,funext fun i=>funext fun j=>?_⟩
    have le_ : M i j≤∑ a,M i a := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
    simpa [counts,h.1 i] using (show 0=M i j from by rw [h.1 i] at le_; omega)
  | succ k ih =>
    obtain ⟨s,admiss⟩ := regular_has_matching M (Nat.zero_lt_succ k) h
    obtain ⟨N,reg,split⟩ := remove_regular M s h admiss
    obtain ⟨ss,len,eq⟩ := ih N reg
    refine ⟨s::ss,by simp [len],funext fun i=>funext fun j=>?_⟩
    rw [counts_cons,eq,←split]

end PositivePermanent
#print axioms PositivePermanent.decompose
