import NormalizedPath

/-! Independent sets with normalized vertex parameters. The vertices of each
substituted path have been summed out by the recursion in NormalizedPath. -/
namespace SparseAffine
open scoped BigOperators
noncomputable section

def occ {K : Type*} [One K] (x : K) (bit : Bool) : K := if bit then x else 1

def mass {K : Type*} [Ring K] (p : K) (bit : Bool) : K := if bit then p else 1-p

def hard {K : Type*} [Zero K] [One K] (a b : Bool) : K :=
  if a && b then 0 else 1

theorem wire_factors {K : Type*} [CommRing K] (r s : K) (a b : Bool) :
    wire r s a b = hard a b * occ r a * occ s b := by
  cases a <;> cases b <;> simp [wire,hard,occ]

theorem leaf_sum {K : Type*} [CommRing K] (u x : K) (b : Bool) :
    (∑ l : Bool, mass (1-x) l * wire u 1 b l) = occ (u*x) b := by
  cases b <;> simp [Fintype.sum_bool,mass,wire,occ] <;> ring

theorem occ_mul {K : Type*} [MulOneClass K] (x y : K) (b : Bool) :
    occ (x*y) b = occ x b * occ y b := by cases b <;> simp [occ]

variable {V E L K : Type*} [Fintype V] [Fintype E] [Fintype L]
variable [DecidableEq V] [DecidableEq L]

/-- Products of selected variables grouped by their owner. -/
def owned [CommMonoid K] {I : Type*} [Fintype I] (f : I → V) (x : I → K) (v : V) : K :=
  ∏ i : {i // f i = v}, x i

theorem group_owned [CommMonoid K] {I : Type*} [Fintype I] (f : I → V) (x : I → K) (b : V → Bool) :
    (∏ i, occ (x i) (b (f i))) = ∏ v, occ (owned f x v) (b v) := by
  rw [← Fintype.prod_fiberwise f (fun i => occ (x i) (b (f i)))]
  apply Finset.prod_congr rfl
  intro v _
  have h : (∏ i : {i // f i = v}, occ (x i) (b (f i))) =
      ∏ i : {i // f i = v}, occ (x i) (b v) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [i.property]
  rw [h]
  cases b v <;> simp [occ,owned]

def ports {I : Type*} [Fintype I] (f : I → V) (v : V) : ℕ := Fintype.card {i // f i = v}

theorem group_uniform [CommMonoid K] {I : Type*} [Fintype I] (f : I → V) (u : K) (b : V → Bool) :
    (∏ i, occ u (b (f i))) = ∏ v, occ (u ^ ports f v) (b v) := by
  rw [group_owned f (fun _ => u) b]
  simp [owned,ports]

def rootDegree (src dst : E → V) (owner : L → V) (v : V) : ℕ :=
  ports src v + ports dst v + ports owner v

theorem recover_root [Field K] (u c : K) (d : ℕ) (hd : u^d+c ≠ 0) (b : Bool) :
    mass (c/(u^d+c)) b * occ (u^d) b =
      (1-c/(u^d+c))*occ c b := by
  cases b <;> simp [mass,occ] <;> field_simp <;> ring

/-- A weighted, unnormalized independent-set partition function. Edges may be
arbitrarily oriented. Leaf data have been multiplied into their owners. -/
def partition [CommRing K] (src dst : E → V) (a : V → K) : K :=
  ∑ b : V → Bool, (∏ e, hard (b (src e)) (b (dst e)) : K) * ∏ v, occ (a v) (b v)

/-- The normalized partition function of the network after path contraction.
Every path carries only the parameters of its internal vertices. -/
def network [CommRing K] (src dst : E → V) (owner : L → V) (p : V → K) (x : L → K)
    (ordinary : E → List K) (leaves : L → List K) : K :=
  ∑ b : V → Bool, (∏ v, mass (p v) (b v)) *
    (∏ e, bern (b (src e)) (ordinary e) (b (dst e))) *
    ∑ bits : L → Bool, ∏ j, mass (1-x j) (bits j) * bern (b (owner j)) (leaves j) (bits j)

/-- Exact affine specialization. The only nonconstant inputs are 1-x at the
leaves. Repetitions among these variables are permitted. -/
theorem specialize_network [Field K] (src dst : E → V) (owner : L → V) (u : K) (c : V → K) (x : L → K)
    (ordinary : E → List K) (leaves : L → List K) (k : E → K) (h : L → K)
    (ho : ∀ e a b, bern a (ordinary e) b = k e * wire u u a b)
    (hl : ∀ j a b, bern a (leaves j) b = h j * wire u 1 a b)
    (hd : ∀ v, u ^ rootDegree src dst owner v + c v ≠ 0) :
    let p := fun v => c v / (u ^ rootDegree src dst owner v + c v)
    network src dst owner p x ordinary leaves =
      ((∏ e, k e)*(∏ j, h j)*(∏ v, (1-p v))) *
      partition src dst (fun v => c v * owned owner x v) := by
  classical
  dsimp only
  unfold network partition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have leaffactor : (∑ bits : L → Bool, ∏ j,
      mass (1-x j) (bits j) * bern (b (owner j)) (leaves j) (bits j)) =
      (∏ j, h j) * (∏ j, occ u (b (owner j))) * ∏ j, occ (x j) (b (owner j)) := by
    rw [← Fintype.prod_sum (fun j bit => mass (1-x j) bit * bern (b (owner j)) (leaves j) bit)]
    have oneLeaf (j : L) : (∑ bit : Bool, mass (1-x j) bit * bern (b (owner j)) (leaves j) bit) =
        h j * (occ u (b (owner j)) * occ (x j) (b (owner j))) := by
      rw [← occ_mul, ← leaf_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun bit _ => by rw [hl]; ring)
    simp_rw [oneLeaf]
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    ring
  have edgefactor : (∏ e, bern (b (src e)) (ordinary e) (b (dst e))) =
      (∏ e, k e) * (∏ e, hard (b (src e)) (b (dst e)) : K) *
      (∏ e, occ u (b (src e))) * ∏ e, occ u (b (dst e)) := by
    simp_rw [ho, wire_factors,Finset.prod_mul_distrib]
    ring
  rw [leaffactor,edgefactor,group_uniform src,group_uniform dst,group_uniform owner,group_owned owner]
  have roots : (∏ v, mass (c v / (u^rootDegree src dst owner v+c v)) (b v)) *
      (∏ v, occ (u^ports src v) (b v)) * (∏ v, occ (u^ports dst v) (b v)) *
      (∏ v, occ (u^ports owner v) (b v)) * (∏ v, occ (owned owner x v) (b v)) =
      (∏ v, (1-c v/(u^rootDegree src dst owner v+c v))) *
      ∏ v, occ (c v * owned owner x v) (b v) := by
    simp only [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    have hr := recover_root u (c v) (rootDegree src dst owner v) (hd v) (b v)
    rw [show u^rootDegree src dst owner v =
      u^ports src v * u^ports dst v * u^ports owner v by simp [rootDegree,pow_add]] at hr
    -- Collect incidence factors before combining the data held at this root.
    simp only [occ_mul] at hr ⊢
    simpa only [rootDegree,pow_add,mul_assoc] using congrArg (fun a => a * occ (owned owner x v) (b v)) hr
  linear_combination (∏ e, k e) * (∏ j, h j) *
    (∏ e, hard (b (src e)) (b (dst e)) : K) * roots

end
end SparseAffine
#print axioms SparseAffine.specialize_network
