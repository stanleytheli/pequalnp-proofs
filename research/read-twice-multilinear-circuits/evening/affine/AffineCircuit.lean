import Mathlib

/-! Affine input substitution for arithmetic straight-line circuits, including
the cost of every input variable and every constant as a circuit node. -/
namespace SparseAffine.Circuits
open MvPolynomial
noncomputable section

/-- The list-of-polynomials circuit representation. -/
def Fits {V R : Type*} [CommSemiring R] (f : MvPolynomial V R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial V R,
    (∀ k < s, (∃ v, l k=X v) ∨ (∃ a, l k=C a) ∨
      (∃ i < k, ∃ j < k, l k=l i+l j) ∨ (∃ i < k, ∃ j < k, l k=l i*l j)) ∧
      ∃ k<s, l k=f

inductive Input (W S : Type*) where
  | const (a : S)
  | direct (w : W)
  | complement (w : W)

def Input.poly {W S : Type*} [CommRing S] : Input W S → MvPolynomial W S
  | .const c => C c
  | .direct w => X w
  | .complement w => 1-X w

private def header {W : Type*} (S : Type*) [CommRing S] [Fintype W] (k : ℕ) :
    MvPolynomial W S :=
  if k=0 then 1 else if k=1 then -1 else if h : (k-2)/2 < Fintype.card W then
    let w := (Fintype.equivFin W).symm ⟨(k-2)/2,h⟩
    if k%2=0 then X w else (-1)*X w
  else 0

private theorem header0 {W S : Type*} [CommRing S] [Fintype W] :
    header (W:=W) S 0 = 1 := by simp [header]

private theorem header1 {W S : Type*} [CommRing S] [Fintype W] :
    header (W:=W) S 1 = -1 := by simp [header]

private theorem header_at {W S : Type*} [CommRing S] [Fintype W] (w : W) :
    let i := ((Fintype.equivFin W) w).val
    header S (2*i+2) = (X w : MvPolynomial W S) ∧ header S (2*i+3) = (-1)*X w := by
  let i := ((Fintype.equivFin W) w).val
  have hi : i < Fintype.card W := ((Fintype.equivFin W) w).isLt
  have h2 : (2*i+2-2)/2=i := by omega
  have h3 : (2*i+3-2)/2=i := by omega
  have ew (h : i < Fintype.card W) : (Fintype.equivFin W).symm ⟨i,h⟩ = w := by
    exact (Fintype.equivFin W).symm_apply_apply w
  change header S (2*i+2)=X w ∧ header S (2*i+3)=(-1)*X w
  simp [header,h2,h3,hi,ew,show (2*i+1)/2=i by omega,
    show (2*i+2)%2=0 by omega,show (2*i+3)%2≠0 by omega]

/-- A header shares the variables and all their negatives. Every translated
source gate contributes just one further node. -/
theorem substitute {V W R S : Type*} [Fintype W] [CommSemiring R] [CommRing S]
    (φ : R →+* S) (r : V → Input W S) {f : MvPolynomial V R} {s : ℕ} (hf : Fits f s) :
    let Φ := eval₂Hom (C.comp φ) (fun v => (r v).poly)
    Fits (Φ f) (2+2*Fintype.card W+s) := by
  classical
  intro Φ
  obtain ⟨l,valid,out,hout,answer⟩ := hf
  let P := 2+2*Fintype.card W
  let lines := fun k => if k<P then header S k else Φ (l (k-P))
  refine ⟨lines,?_,P+out,by change P+out<P+s; omega,?_⟩
  · intro k hk
    change k<P+s at hk
    by_cases pre : k<P
    · have hh (a : ℕ) (h : a<P) : lines a = header S a := if_pos h
      by_cases z : k=0
      · subst k; exact Or.inr (Or.inl ⟨1,by rw [hh _ pre,header0]; simp⟩)
      by_cases o : k=1
      · subst k; exact Or.inr (Or.inl ⟨-1,by rw [hh _ pre,header1]; simp⟩)
      have bound : (k-2)/2 < Fintype.card W := by dsimp [P] at pre; omega
      let w := (Fintype.equivFin W).symm ⟨(k-2)/2,bound⟩
      have idx : ((Fintype.equivFin W) w).val = (k-2)/2 := by simp [w]
      obtain ⟨ev,od⟩ := header_at (S:=S) w
      rw [idx] at ev od
      by_cases even : k%2=0
      · have a : 2*((k-2)/2)+2=k := by omega
        rw [a] at ev
        exact Or.inl ⟨w,(hh _ pre).trans ev⟩
      · refine Or.inr (Or.inr (Or.inr ⟨1,by omega,k-1,by omega,?_⟩))
        rw [hh _ pre,hh 1 (by omega),header1,hh (k-1) (by omega)]
        have a : 2*((k-2)/2)+2=k-1 := by omega
        have b : 2*((k-2)/2)+3=k := by omega
        rw [a] at ev
        rwa [b,← ev] at od
    · let j := k-P
      have hj : j<s := by dsimp [j]; omega
      have now : lines k=Φ (l j) := if_neg pre
      have earlier (a : ℕ) : lines (P+a)=Φ (l a) := by simp [lines]
      have small {a : ℕ} (ha : a<j) : P+a<k := by dsimp [j] at ha; omega
      rcases valid j hj with ⟨v,hv⟩|⟨a,ha⟩|⟨a,ha,b,hb,add⟩|⟨a,ha,b,hb,mul⟩
      · rw [now,hv]
        have pv : Φ (X v)=(r v).poly := by simp [Φ]
        rw [pv]
        cases r v with
        | const c => exact Or.inr (Or.inl ⟨c,rfl⟩)
        | direct w => exact Or.inl ⟨w,rfl⟩
        | complement w =>
          let i := ((Fintype.equivFin W) w).val
          have hi : i < Fintype.card W := ((Fintype.equivFin W) w).isLt
          have hp : 2*i+3<P := by dsimp [P]; omega
          refine Or.inr (Or.inr (Or.inl ⟨0,by dsimp [P] at pre; omega,2*i+3,by omega,?_⟩))
          have l0 : lines 0=1 := by simp [lines,P,header0]
          have ln : lines (2*i+3)=(-1)*X w := (if_pos hp).trans (header_at w).2
          rw [l0,ln]
          simp [Input.poly,sub_eq_add_neg]
      · exact Or.inr (Or.inl ⟨φ a,by rw [now,ha]; simp [Φ]⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨P+a,small ha,P+b,small hb,by rw [now,add,map_add,earlier,earlier]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨P+a,small ha,P+b,small hb,by rw [now,mul,map_mul,earlier,earlier]⟩))
  · simp [lines,answer]

end
end SparseAffine.Circuits
#print axioms SparseAffine.Circuits.substitute
