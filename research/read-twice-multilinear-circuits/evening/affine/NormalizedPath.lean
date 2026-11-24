import Mathlib

/-! Exact two-spin signatures for the normalized independent-set polynomial. -/
namespace SparseAffine

/-- Activity partition function of a path with its two endpoint bits fixed.
Only the internal vertices contribute activity factors. -/
def path {R : Type*} [CommRing R] (left : Bool) : List R → Bool → R
  | [], right => if left && right then 0 else 1
  | z::zs, right => path false zs right + if left then 0 else z * path true zs right

/-- The same edge constraint with Bernoulli input parameters. -/
def bern {R : Type*} [CommRing R] (left : Bool) : List R → Bool → R
  | [], right => if left && right then 0 else 1
  | p::ps, right => (1-p)*bern false ps right + if left then 0 else p*bern true ps right

def wire {R : Type*} [Zero R] [One R] (r s : R) (left right : Bool) : R :=
  if left then (if right then 0 else r) else (if right then s else 1)

private theorem append_one {R : Type*} [CommRing R] (xs : List R) (b : R) (l r : Bool) :
    path l (xs++[b]) r = path l xs false + if r then 0 else b*path l xs true := by
  induction xs generalizing l with
  | nil => cases l <;> cases r <;> simp [path]
  | cons a xs ih => cases l <;> cases r <;> simp [path,ih] <;> ring

/-- Continuants for a free path of j identical activities. -/
def cont {K : Type*} [CommRing K] (t : K) : ℕ → K
  | 0 => 1
  | 1 => 1+t
  | j+2 => cont t (j+1)+t*cont t j

private theorem cassini {K : Type*} [CommRing K] (t : K) :
    (cont t 5)^2 - cont t 6*cont t 4 = t^6 := by simp [cont]; ring

def middle {K : Type*} (t w : K) := [t,t,t,t,t,t,w]

private theorem core {K : Type*} [CommRing K] (t w : K) :
    path false (middle t w) false=cont t 6+w*cont t 5 ∧
    path false (middle t w) true=cont t 6 ∧
    path true (middle t w) false=cont t 5+w*cont t 4 ∧
    path true (middle t w) true=cont t 5 := by
  constructor
  · simp [path,middle,cont]; ring
  constructor
  · simp [path,middle,cont]
  constructor <;> simp [path,middle,cont] <;> ring

/-- Tuning the seventh middle activity makes the 00 entry vanish. -/
theorem middle_signature {K : Type*} [Field K] (t : K) (hc : cont t 5 ≠ 0) :
    let B := cont t 6
    let C := cont t 5
    let A := t^6/C
    let xs := middle t (-B/C)
    path false xs false=0 ∧ path false xs true=B ∧ path true xs false=A ∧ path true xs true=C := by
  dsimp only
  obtain ⟨a,b,c,d⟩ := core t (-(cont t 6)/(cont t 5))
  refine ⟨?_,b,?_,d⟩
  · rw [a]; field_simp; ring
  · rw [c]; field_simp; linear_combination cassini t

/-- Sandwiching an interior signature by a vertex at either end programs
both nonzero entries adjacent to the 00 entry independently. -/
theorem program_ends {K : Type*} [Field K] (xs : List K) (A B C r s : K)
    (h0 : path false xs false=0) (h1 : path false xs true=B)
    (h2 : path true xs false=A) (h3 : path true xs true=C)
    (nc : C ≠ 0) (nr : r ≠ 0) (ns : s ≠ 0) (l h : Bool) :
    let a := (1-r-s)*B/(r*C)
    let b := (1-r-s)*A/(s*C)
    let D := (1-r-s)*A*B/(r*s*C)
    path l (a::(xs++[b])) h = D*wire r s l h := by
  cases l <;> cases h <;> simp [path,append_one,h0,h1,h2,h3,wire] <;> field_simp <;> ring

noncomputable def parameter {K : Type*} [Field K] (z : K) := z/(1+z)
noncomputable def normFactor {K : Type*} [Field K] (z : K) := (1+z)⁻¹

/-- Converting each activity to a normalized Bernoulli parameter contributes
one scalar independent of both end spins. -/
theorem normalize_path {K : Type*} [Field K] (zs : List K) (good : ∀ z∈zs, 1+z ≠ 0) (l r : Bool) :
    bern l (zs.map parameter) r = (zs.map normFactor).prod * path l zs r := by
  induction zs generalizing l with
  | nil => simp [bern,path]
  | cons z zs ih =>
    have hn := good z (by simp)
    have ht : ∀ v∈zs, 1+v ≠ 0 := fun v h => good v (by simp [h])
    have un : 1-parameter z=normFactor z := by unfold parameter normFactor; field_simp; ring
    have occ : parameter z=normFactor z*z := by simp [parameter,normFactor,div_eq_inv_mul]
    cases l <;> simp only [List.map_cons,bern,path,List.prod_cons,ih ht] <;>
      rw [un] <;> simp [occ] <;> ring

/-- Explicit normalized ten-edge path. All parameter hypotheses are satisfied
by the rational-function choices discussed in the accompanying manuscript. -/
theorem ten_edge_signature {K : Type*} [Field K] (t r s : K)
    (hc : cont t 5 ≠ 0) (nr : r ≠ 0) (ns : s ≠ 0) (l h : Bool) :
    let B := cont t 6
    let C := cont t 5
    let A := t^6/C
    let a := (1-r-s)*B/(r*C)
    let b := (1-r-s)*A/(s*C)
    let xs := a::(middle t (-B/C)++[b])
    let D := (1-r-s)*A*B/(r*s*C)
    (∀ z∈xs, 1+z ≠ 0) → bern l (xs.map parameter) h = ((xs.map normFactor).prod*D)*wire r s l h := by
  dsimp only
  intro good
  obtain ⟨h0,h1,h2,h3⟩ := middle_signature t hc
  rw [normalize_path _ good]
  rw [program_ends _ _ _ _ r s h0 h1 h2 h3 hc nr ns]
  ring

end SparseAffine
#print axioms SparseAffine.middle_signature
#print axioms SparseAffine.program_ends
#print axioms SparseAffine.normalize_path
#print axioms SparseAffine.ten_edge_signature
