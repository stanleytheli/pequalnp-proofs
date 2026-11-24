import BorderTransfer
import CircuitNetwork

namespace SparseAffine
open MvPolynomial Circuits
noncomputable section

lemma border_scale {W F : Type*} [Field F] (z : F) {p : MvPolynomial W F} {s : ℕ}
    (h : BorderFits p s) : BorderFits (C z*p) (s+2) := by
  obtain ⟨w,small,residue⟩ := h
  refine ⟨C (PowerSeries.C z)*w,?_,?_⟩
  · simp only [map_mul,MvPolynomial.map_C]
    exact scale_fits _ small
  · simp [residue]

variable {V E L : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq L]

/-- A coefficientwise Laurent approximation for the physical network over F
yields one for the seed over F(t,u), with at most 2|L|+4 additional nodes. -/
theorem border_seed_circuit (F : Type*) [Field F] (src dst : E→V) (owner : L→V)
    (positive : ∀ v, rootDegree src dst owner v≠0) (c : V→RatFunc F) {s : ℕ}
    (hf : BorderFits (physicalPolynomial F src dst owner 9 9) s) :
    BorderFits (partition src dst (fun v => C (RatFunc.C (c v) : Extension F) * owned owner X v))
      (2+2*Fintype.card L+s+2) := by
  classical
  let t : Extension F := RatFunc.C RatFunc.X
  let u : Extension F := RatFunc.X
  let p := fun v => RatFunc.C (c v)/(u^rootDegree src dst owner v+RatFunc.C (c v))
  let ord := (activityList t u u).map parameter
  let leaf := (activityList t u 1).map parameter
  let phi : F→+*Extension F := RatFunc.C.comp RatFunc.C
  have hs : BorderFits (physicalPolynomial F src dst owner ord.length leaf.length) s := hf
  have translated := Circuits.border_substitute phi (siteInput (E:=E) p id ord leaf) hs
  unfold Circuits.project at translated
  rw [physical_substitute phi src dst owner p id ord leaf] at translated
  obtain ⟨scalar,nonzero,ident⟩ := polynomial_specialization F src dst owner positive c
  change network src dst owner (fun v => C (p v)) X (fun _ => ord.map C) (fun _ => leaf.map C) = _ at ident
  change BorderFits (network src dst owner (fun v => C (p v)) X (fun _ => ord.map C) (fun _ => leaf.map C)) _ at translated
  rw [ident] at translated
  have scaled := border_scale scalar⁻¹ translated
  rwa [←mul_assoc,←map_mul,inv_mul_cancel₀ nonzero,map_one,one_mul] at scaled

end
end SparseAffine
#print axioms SparseAffine.border_seed_circuit
