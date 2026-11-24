import AffineCircuit
import Mathlib.RingTheory.LaurentSeries

/-! Transport coefficientwise Laurent approximation across a field embedding and
constant, variable or complemented-variable substitutions. -/
namespace SparseAffine.Circuits
open MvPolynomial
noncomputable section

variable {V W : Type*} {A B D E : Type*} [CommRing A] [CommRing B] [CommRing D] [CommRing E]

def Input.push (φ : A→+*B) : Input W A→Input W B
  | .const a => .const (φ a)
  | .direct w => .direct w
  | .complement w => .complement w

def project (φ : A→+*B) (r : V→Input W B) : MvPolynomial V A→+*MvPolynomial W B :=
  eval₂Hom (C.comp φ) (fun v => (r v).poly)

lemma project_square (f : A→+*B) (g : D→+*E) (p : A→+*D) (q : B→+*E)
    (comm : q.comp f = g.comp p) (r : V→Input W B) (P : MvPolynomial V A) :
    MvPolynomial.map q (project f r P) = project g (fun v => (r v).push q) (MvPolynomial.map p P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [project] using congrArg (C : E→+*MvPolynomial W E) (RingHom.congr_fun comm a)
  | add x y hx hy => simp only [map_add,hx,hy]
  | mul_X x v hx =>
    simp only [map_mul,hx,MvPolynomial.map_X]
    congr 1
    cases h : r v <;> simp [project,h,Input.push,Input.poly]

variable {F K : Type*} [Field F] [Field K]

abbrev powerIn (F : Type*) [Field F] := HahnSeries.ofPowerSeries ℤ F

def extendLaurent (φ : F→+*K) : LaurentSeries F →+* LaurentSeries K where
  toFun x := x.map φ
  map_zero' := by ext; simp
  map_one' := HahnSeries.map_one φ.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add φ.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul φ.toNonUnitalRingHom

lemma coeff_neg_power (p : PowerSeries F) {i : ℤ} (hi : i<0) : (powerIn F p).coeff i=0 := by
  have h := (LaurentSeries.val_le_one_iff_eq_coe F (powerIn F p)).mpr ⟨p,rfl⟩
  rw [LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero F one_ne_zero,WithZero.log_one,neg_zero] at h
  exact h _ hi

lemma extend_power (φ : F→+*K) : (powerIn K).comp (PowerSeries.map φ) = (extendLaurent φ).comp (powerIn F) := by
  apply RingHom.ext
  intro p
  ext i
  cases i with
  | ofNat n =>
    change ((HahnSeries.ofPowerSeries ℤ K) (PowerSeries.map φ p)).coeff (n:ℤ) =
      φ (((HahnSeries.ofPowerSeries ℤ F) p).coeff (n:ℤ))
    rw [HahnSeries.ofPowerSeries_apply_coeff,HahnSeries.ofPowerSeries_apply_coeff,PowerSeries.coeff_map]
  | negSucc n =>
    change (powerIn K (PowerSeries.map φ p)).coeff (Int.negSucc n) = φ ((powerIn F p).coeff (Int.negSucc n))
    rw [coeff_neg_power _ (by omega),coeff_neg_power _ (by omega),map_zero]

lemma residue_square (φ : F→+*K) : PowerSeries.constantCoeff.comp (PowerSeries.map φ) = φ.comp PowerSeries.constantCoeff := by
  apply RingHom.ext
  intro p
  change PowerSeries.constantCoeff (PowerSeries.map φ p)=φ (PowerSeries.constantCoeff p)
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using PowerSeries.coeff_map φ 0 p

/-- Equivalent to the regular Laurent-coefficient definition. The intermediate
power-series lift is finite in the polynomial variables. -/
def BorderFits (P : MvPolynomial V F) (s : ℕ) : Prop :=
  ∃ w : MvPolynomial V (PowerSeries F), Fits (MvPolynomial.map (powerIn F) w) s ∧
    MvPolynomial.map PowerSeries.constantCoeff w=P

theorem border_substitute [Fintype W] (φ : F→+*K) (r : V→Input W K) {P : MvPolynomial V F}
    {s : ℕ} (small : BorderFits P s) : BorderFits (project φ r P) (2+2*Fintype.card W+s) := by
  obtain ⟨w,low,residue⟩ := small
  let rP := fun v => (r v).push (PowerSeries.C (R:=K))
  let rL := fun v => (r v).push (HahnSeries.C (Γ:=ℤ) (R:=K))
  have fromPower (v : V) : (rP v).push (powerIn K) = rL v := by
    cases h : r v <;> simp [rP,rL,h,Input.push,powerIn,HahnSeries.ofPowerSeries_C]
  have fromZero (v : V) : (rP v).push PowerSeries.constantCoeff = r v := by
    cases h : r v <;> simp [rP,h,Input.push]
  refine ⟨project (PowerSeries.map φ) rP w,?_,?_⟩
  · rw [project_square _ _ _ _ (extend_power φ),show (fun v => (rP v).push (powerIn K))=rL from funext fromPower]
    exact substitute (extendLaurent φ) rL low
  · rw [project_square _ _ _ _ (residue_square φ),show (fun v => (rP v).push PowerSeries.constantCoeff)=r from funext fromZero,residue]

end
end SparseAffine.Circuits
#print axioms SparseAffine.Circuits.border_substitute
