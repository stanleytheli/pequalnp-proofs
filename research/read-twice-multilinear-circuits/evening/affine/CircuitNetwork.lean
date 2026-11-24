import PolynomialNetwork
import AffineCircuit

/-! A circuit on the physical path variables yields a circuit for the
weighted seed polynomial with an explicit number of additional nodes. -/
namespace SparseAffine
open MvPolynomial Circuits
noncomputable section

abbrev Site (V E L : Type*) (a b : ℕ) := V ⊕ L ⊕ (E × Fin a) ⊕ (L × Fin b)

variable {V E L W : Type*} [Fintype V] [Fintype E] [Fintype L] [DecidableEq V] [DecidableEq L]

def physicalPolynomial (R : Type*) [CommRing R] (src dst : E→V) (owner : L→V) (a b : ℕ) :
    MvPolynomial (Site V E L a b) R :=
  network src dst owner (fun v => X (.inl v)) (fun j => 1-X (.inr (.inl j)))
    (fun e => List.ofFn fun i : Fin a => X (.inr (.inr (.inl (e,i)))))
    (fun j => List.ofFn fun i : Fin b => X (.inr (.inr (.inr (j,i)))))

def siteInput {S : Type*} (p : V→S) (data : L→W) (ord leaf : List S) :
    Site V E L ord.length leaf.length → Input W S
  | .inl v => .const (p v)
  | .inr (.inl j) => .complement (data j)
  | .inr (.inr (.inl (_,i))) => .const (ord.get i)
  | .inr (.inr (.inr (_,i))) => .const (leaf.get i)

theorem physical_substitute {R S : Type*} [CommRing R] [CommRing S] (φ : R→+*S)
    (src dst : E→V) (owner : L→V) (p : V→S) (data : L→W) (ord leaf : List S) :
    eval₂Hom (C.comp φ) (fun v => (siteInput (E:=E) p data ord leaf v).poly)
      (physicalPolynomial R src dst owner ord.length leaf.length) =
    network src dst owner (fun v => C (p v)) (fun j => X (data j))
      (fun _ => ord.map C) (fun _ => leaf.map C) := by
  classical
  unfold physicalPolynomial
  rw [map_network]
  have reassemble (xs : List S) : List.ofFn (fun i : Fin xs.length => (C (xs.get i) : MvPolynomial W S)) = xs.map C := by
    rw [List.ofFn_comp' xs.get (C : S →+* MvPolynomial W S),List.ofFn_get]
  simp [Function.comp_def,List.map_ofFn,siteInput,Input.poly,reassemble]

theorem scale_fits {W S : Type*} [CommRing S] (u : S) {f : MvPolynomial W S} {s : ℕ}
    (small : Fits f s) : Fits (C u*f) (s+2) := by
  obtain ⟨l,ok,o,ho,result⟩ := small
  let ls := fun k => if k<s then l k else if k=s then C u else C u*f
  have old {k} (h : k<s) : ls k=l k := if_pos h
  have scalar : ls s=C u := by simp [ls]
  have answer : ls (s+1)=C u*f := by simp [ls]
  refine ⟨ls,?_,s+1,by omega,answer⟩
  intro k hk
  by_cases small : k<s
  · rcases ok k small with ⟨v,e⟩ | ⟨a,e⟩ | ⟨i,hi,j,hj,e⟩ | ⟨i,hi,j,hj,e⟩
    · exact Or.inl ⟨v,(old small).trans e⟩
    · exact Or.inr (Or.inl ⟨a,(old small).trans e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i,hi,j,hj,by rwa [old small,old (hi.trans small),old (hj.trans small)]⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨i,hi,j,hj,by rwa [old small,old (hi.trans small),old (hj.trans small)]⟩))
  · by_cases eq : k=s
    · subst k; exact Or.inr (Or.inl ⟨u,scalar⟩)
    · have eq : k=s+1 := by omega
      subst k
      exact Or.inr (Or.inr (Or.inr ⟨s,by omega,o,by omega,by rw [answer,scalar,old ho,result]⟩))

/-- A circuit for the normalized physical graph polynomial over an arbitrary
field yields one for the seed over F(t,u), at cost at most 2|L|+4 new nodes. -/
theorem seed_circuit (F : Type*) [Field F] (src dst : E→V) (owner : L→V)
    (positive : ∀ v, rootDegree src dst owner v≠0) (c : V→RatFunc F) {s : ℕ}
    (hf : Fits (physicalPolynomial F src dst owner 9 9) s) :
    Fits (partition src dst (fun v => C (RatFunc.C (c v) : Extension F) * owned owner X v))
      (2+2*Fintype.card L+s+2) := by
  classical
  let t : Extension F := RatFunc.C RatFunc.X
  let u : Extension F := RatFunc.X
  let p := fun v => RatFunc.C (c v)/(u^rootDegree src dst owner v+RatFunc.C (c v))
  let ord := (activityList t u u).map parameter
  let leaf := (activityList t u 1).map parameter
  let phi : F→+*Extension F := RatFunc.C.comp RatFunc.C
  have hs : Fits (physicalPolynomial F src dst owner ord.length leaf.length) s := hf
  have translated := Circuits.substitute phi (siteInput (E:=E) p id ord leaf) hs
  dsimp only at translated
  rw [physical_substitute phi src dst owner p id ord leaf] at translated
  obtain ⟨scalar,nonzero,ident⟩ := polynomial_specialization F src dst owner positive c
  change network src dst owner (fun v => C (p v)) X (fun _ => ord.map C) (fun _ => leaf.map C) = _ at ident
  change Fits (network src dst owner (fun v => C (p v)) X (fun _ => ord.map C) (fun _ => leaf.map C)) _ at translated
  rw [ident] at translated
  have scaled := scale_fits scalar⁻¹ translated
  rwa [←mul_assoc,←map_mul,inv_mul_cancel₀ nonzero,map_one,one_mul] at scaled

end
end SparseAffine
#print axioms SparseAffine.seed_circuit
