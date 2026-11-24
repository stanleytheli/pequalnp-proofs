import ExplicitSpecialization
import PhysicalNetwork
import Mathlib.Algebra.MvPolynomial.Funext

/-! An exact identity of formal polynomials with one indeterminate per data port. -/
namespace SparseAffine
open MvPolynomial
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

lemma map_mass (φ : R →+* S) (p : R) (b : Bool) : φ (mass p b) = mass (φ p) b := by
  cases b <;> simp [mass]

lemma map_occ (φ : R →+* S) (p : R) (b : Bool) : φ (occ p b) = occ (φ p) b := by
  cases b <;> simp [occ]

lemma map_hard (φ : R →+* S) (a b : Bool) : φ (hard a b) = (hard a b : S) := by
  cases a <;> cases b <;> simp [hard]

lemma map_bern (φ : R →+* S) (a : Bool) (ps : List R) (b : Bool) :
    φ (bern a ps b) = bern a (ps.map φ) b := by
  induction ps generalizing a with
  | nil => cases a <;> cases b <;> simp [bern]
  | cons p ps ih => cases a <;> simp [bern,ih]

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq L]

lemma map_network (φ : R →+* S) (src dst : E→V) (owner : L→V) (p : V→R) (x : L→R)
    (ord : E→List R) (leaf : L→List R) :
    φ (network src dst owner p x ord leaf) = network src dst owner (φ ∘ p) (φ ∘ x)
      (fun e => (ord e).map φ) (fun j => (leaf j).map φ) := by
  classical
  simp [network,map_mass,map_bern,Function.comp_def]

lemma map_partition (φ : R →+* S) (src dst : E→V) (a : V→R) :
    φ (partition src dst a) = partition src dst (φ ∘ a) := by
  classical
  simp [partition,map_hard,map_occ,Function.comp_def]

/-- Distinct leaf indeterminates. The identity continues to hold after arbitrary
identifications of the leaf variables by a polynomial homomorphism. -/
theorem polynomial_specialization (F : Type*) [Field F] (src dst : E→V) (owner : L→V)
    (positive : ∀ v, rootDegree src dst owner v ≠ 0) (c : V → RatFunc F) :
    let t : Extension F := RatFunc.C RatFunc.X
    let u : Extension F := RatFunc.X
    let p := fun v => RatFunc.C (c v)/(u^rootDegree src dst owner v+RatFunc.C (c v))
    let ordinary := (activityList t u u).map parameter
    let leaf := (activityList t u 1).map parameter
    ∃ scalar : Extension F, scalar≠0 ∧
      network src dst owner (fun v => C (p v)) X
        (fun _ => ordinary.map C) (fun _ => leaf.map C) =
      C scalar * partition src dst (fun v => C (RatFunc.C (c v)) * owned owner X v) := by
  classical
  intro t u p ordinary leaf
  obtain ⟨scalar,nonzero,ident⟩ := all_field_specialization F src dst owner positive c
  refine ⟨scalar,nonzero,?_⟩
  letI : Infinite (Extension F) := Infinite.of_injective _ (RatFunc.algebraMap_injective (RatFunc F))
  apply MvPolynomial.funext
  intro x
  rw [map_network,map_mul,map_partition]
  have cancel (ps : List (Extension F)) : (ps.map (C : Extension F →+* MvPolynomial L (Extension F))).map (eval x) = ps := by
    simp [List.map_map,Function.comp_def]
  simpa [Function.comp_def,owned,cancel,p,ordinary,leaf,t,u] using ident x

end
end SparseAffine
#print axioms SparseAffine.polynomial_specialization
