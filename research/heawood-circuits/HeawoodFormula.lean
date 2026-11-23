import Mathlib

namespace WeightedFormula

inductive Formula (V : Type*) where
  | var (v : V)
  | const (b : Bool)
  | meet (a b : Formula V)
  | join (a b : Formula V)

namespace Formula

def eval {V} (x : V → Bool) : Formula V → Bool
  | .var v => x v
  | .const b => b
  | .meet a b => eval x a && eval x b
  | .join a b => eval x a || eval x b

def leaves {V} : Formula V → ℕ
  | .var _ | .const _ => 1
  | .meet a b | .join a b => a.leaves+b.leaves

def gates {V} : Formula V → ℕ
  | .var _ | .const _ => 0
  | .meet a b | .join a b => a.gates+b.gates+1

theorem leaves_eq {V} (f : Formula V) : f.leaves=f.gates+1 := by
  induction f <;> simp_all [leaves,gates] <;> omega

end Formula

def weight {P Q : Type*} (W : P → Q → ℤ) (A : Finset P) (B : Finset Q) : ℤ :=
  ∑ i∈A, ∑ j∈B, W i j

theorem split_rows {P Q : Type*} (W : P → Q → ℤ) (A : Finset P) (B : Finset Q)
    (p : P → Prop) [DecidablePred p] :
    weight W (A.filter p) B + weight W (A.filter (fun i => ¬p i)) B = weight W A B :=
  Finset.sum_filter_add_sum_filter_not _ _ _

theorem split_columns {P Q : Type*} (W : P → Q → ℤ) (A : Finset P) (B : Finset Q)
    (q : Q → Prop) [DecidablePred q] :
    weight W A (B.filter q) + weight W A (B.filter (fun j => ¬q j)) = weight W A B := by
  unfold weight
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_filter_add_sum_filter_not _ _ _)

theorem rectangle_bound {P Q V : Type*} (pos : P → V → Bool) (neg : Q → V → Bool)
    (W : P → Q → ℤ) (cap : ℤ) (hc : 0≤cap)
    (atomic : ∀ v (A : Finset P) (B : Finset Q),
      (∀ i∈A, pos i v=true) → (∀ j∈B, neg j v=false) → weight W A B≤cap)
    (f : Formula V) (A : Finset P) (B : Finset Q)
    (yes : ∀ i∈A, f.eval (pos i)=true) (no : ∀ j∈B, f.eval (neg j)=false) :
    weight W A B≤cap*f.leaves := by
  classical
  induction f generalizing A B with
  | var v => simpa [Formula.leaves] using atomic v A B yes no
  | const b =>
    cases b
    · have e : A=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi; have h := yes i hi; simp [Formula.eval] at h
      simpa [e,weight,Formula.leaves] using hc
    · have e : B=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj; have h := no j hj; simp [Formula.eval] at h
      simpa [e,weight,Formula.leaves] using hc
  | join a b ia ib =>
    let p := fun i => a.eval (pos i)=true
    have left := ia (A.filter p) B (by intro i hi; exact (Finset.mem_filter.mp hi).2) (by
      intro j hj; exact (Bool.or_eq_false_iff.mp (no j hj)).1)
    have right := ib (A.filter (fun i => ¬p i)) B (by
      intro i hi
      obtain ⟨mem,ha⟩ := Finset.mem_filter.mp hi
      have h : a.eval (pos i)=true ∨ b.eval (pos i)=true := by simpa [Formula.eval] using yes i mem
      exact h.resolve_left ha) (by
      intro j hj; exact (Bool.or_eq_false_iff.mp (no j hj)).2)
    rw [←split_rows W A B p,Formula.leaves,Nat.cast_add,mul_add]
    exact add_le_add left right
  | meet a b ia ib =>
    let q := fun j => a.eval (neg j)=false
    have left := ia A (B.filter q) (by
      intro i hi; exact (Bool.and_eq_true_iff.mp (yes i hi)).1) (by
      intro j hj; exact (Finset.mem_filter.mp hj).2)
    have right := ib A (B.filter (fun j => ¬q j)) (by
      intro i hi; exact (Bool.and_eq_true_iff.mp (yes i hi)).2) (by
      intro j hj
      obtain ⟨mem,ha⟩ := Finset.mem_filter.mp hj
      have h := no j mem
      change (a.eval (neg j) && b.eval (neg j))=false at h
      cases eq : a.eval (neg j) <;> simp_all [q])
    rw [←split_columns W A B q,Formula.leaves,Nat.cast_add,mul_add]
    exact add_le_add left right

end WeightedFormula


namespace HeawoodFormula
open WeightedFormula
abbrev V := Fin 14
abbrev E := Fin 21

def ends : E → V × V := ![(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]
def neighborBits : V → ℕ := ![1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22]
def adjacent (u v : V) : Bool := (neighborBits u).testBit v.val
def yes (e : E) (v : V) : Bool := decide (v=(ends e).1 ∨ v=(ends e).2)
def no (z v : V) : Bool :=
  decide (v=z ∨ ((z.val<7 ↔ 7≤v.val) ∧ adjacent z v=false))
def W (e : E) (z : V) : ℤ :=
  if yes e z then 2 else if adjacent z (if z.val<7 then (ends e).2 else (ends e).1) then -1 else 1
def accepts (x : V → Bool) := ∃ e : E, x (ends e).1=true ∧ x (ends e).2=true

def incident (v : V) : Finset E := Finset.univ.filter (fun e => yes e v=true)
def allowed (v : V) : Finset V := Finset.univ.filter (fun z => no z v=false)
def maxWeight (v : V) (A : Finset E) : ℤ :=
  ∑ z ∈ allowed v, max 0 (∑ e ∈ A, W e z)

def localRow : V → Fin 3 → E := ![
  ![0, 1, 2],
  ![3, 4, 5],
  ![6, 7, 8],
  ![9, 10, 11],
  ![12, 13, 14],
  ![15, 16, 17],
  ![18, 19, 20],
  ![0, 3, 9],
  ![1, 6, 18],
  ![4, 15, 19],
  ![2, 12, 16],
  ![10, 13, 20],
  ![7, 11, 17],
  ![5, 8, 14]]

theorem incident_local : ∀ v e, yes e v=true ↔ ∃ k, localRow v k=e := by decide +kernel

def LocalCertificate (v : V) :=
  ∀ T : Finset (Fin 3), maxWeight v (T.image (localRow v))≤6

theorem local_bound (v : V) (A : Finset E) (ha : ∀ e∈A, yes e v=true)
    (certificate : LocalCertificate v) : maxWeight v A≤6 := by
  classical
  let T : Finset (Fin 3) := Finset.univ.filter (fun k => localRow v k∈A)
  have eq : T.image (localRow v)=A := by
    ext e; constructor
    · intro h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hk).2
    · intro h
      obtain ⟨k,hk⟩ := (incident_local v e).mp (ha e h)
      exact Finset.mem_image.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk ▸ h⟩,hk⟩
  rw [←eq]; exact certificate _
set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem totalCertificate : weight W Finset.univ Finset.univ=168 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem contextCertificate : (∀ e : E, accepts (yes e)) ∧ (∀ z : V, ¬accepts (no z)) := by
  unfold accepts
  decide +kernel

theorem atomic_bound (certificates : ∀ v, LocalCertificate v) (v : V) (A : Finset E) (B : Finset V)
    (ha : ∀ i∈A, yes i v=true) (hb : ∀ j∈B, no j v=false) : weight W A B≤6 := by
  have ia : A⊆incident v := by
    intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha _ hi⟩
  have ib : B⊆allowed v := by
    intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb _ hj⟩
  unfold weight
  rw [Finset.sum_comm]
  calc
    ∑ j∈B, ∑ i∈A, W i j ≤ ∑ j∈B, max 0 (∑ i∈A, W i j) :=
      Finset.sum_le_sum (fun _ _ => le_max_right _ _)
    _ ≤ maxWeight v A := Finset.sum_le_sum_of_subset_of_nonneg ib (by intro _ _ _; exact le_max_left _ _)
    _ ≤ 6 := local_bound v A ha (certificates v)

theorem gate_lower_bound_of (certificates : ∀ v, LocalCertificate v) (f : Formula V) (correct : ∀ x, f.eval x=true ↔ accepts x) :
    27≤f.gates := by
  have pos (e : E) (_ : e∈(Finset.univ : Finset E)) : f.eval (yes e)=true :=
    (correct _).mpr (contextCertificate.1 e)
  have neg (z : V) (_ : z∈(Finset.univ : Finset V)) : f.eval (no z)=false := by
    cases h : f.eval (no z)
    · rfl
    · exact (contextCertificate.2 z ((correct _).mp h)).elim
  have h := rectangle_bound yes no W 6 (by decide) (atomic_bound certificates) f Finset.univ Finset.univ pos neg
  rw [totalCertificate,Formula.leaves_eq] at h
  omega
end HeawoodFormula

namespace HeawoodFormula
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_0 : LocalCertificate 0 := by
  unfold LocalCertificate
  decide +kernel
end HeawoodFormula

namespace HeawoodFormula
set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_1 : LocalCertificate 1 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_2 : LocalCertificate 2 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_3 : LocalCertificate 3 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_4 : LocalCertificate 4 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_5 : LocalCertificate 5 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_6 : LocalCertificate 6 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_7 : LocalCertificate 7 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_8 : LocalCertificate 8 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_9 : LocalCertificate 9 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_10 : LocalCertificate 10 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_11 : LocalCertificate 11 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_12 : LocalCertificate 12 := by
  unfold LocalCertificate
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem local_13 : LocalCertificate 13 := by
  unfold LocalCertificate
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem gate_lower_bound (f : WeightedFormula.Formula V) (correct : ∀ x, f.eval x=true ↔ accepts x) : 27≤f.gates := by
  refine gate_lower_bound_of ?_ f correct
  intro v
  fin_cases v
  · exact local_0
  · exact local_1
  · exact local_2
  · exact local_3
  · exact local_4
  · exact local_5
  · exact local_6
  · exact local_7
  · exact local_8
  · exact local_9
  · exact local_10
  · exact local_11
  · exact local_12
  · exact local_13
end HeawoodFormula
#print axioms HeawoodFormula.gate_lower_bound
