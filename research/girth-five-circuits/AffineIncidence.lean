import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.LinearCombination

namespace PEqualNP.Outside.Affine608
open SimpleGraph Sym2

abbrev Vertex (K : Type*) := (K × K) ⊕ (K × K)

def lies {K : Type*} [Field K] (p l : K×K) := p.2=l.1*p.1+l.2

def incidence {K : Type*} [Field K] : Vertex K → Vertex K → Prop
  | .inl p, .inr l => lies p l
  | .inr l, .inl p => lies p l
  | _, _ => False

def graph (K : Type*) [Field K] : SimpleGraph (Vertex K) where
  Adj := incidence
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

private theorem intersection {K : Type*} [Field K] (p u l m : K×K)
    (pl : lies p l) (ul : lies u l) (pm : lies p m) (um : lies u m) :
    p=u ∨ l=m := by
  rcases p with ⟨x,y⟩; rcases u with ⟨z,w⟩
  rcases l with ⟨a,b⟩; rcases m with ⟨c,d⟩
  change y=a*x+b at pl; change w=a*z+b at ul
  change y=c*x+d at pm; change w=c*z+d at um
  have factor : (a-c)*(x-z)=0 := by linear_combination -pl+ul+pm-um
  rcases mul_eq_zero.mp factor with ac|xz
  · right
    have same : a=c := sub_eq_zero.mp ac
    subst c
    exact Prod.ext rfl (by linear_combination -pl+pm)
  · left
    have same : x=z := sub_eq_zero.mp xz
    subst z
    exact Prod.ext rfl (by linear_combination pl-ul)

theorem no_triangle {K : Type*} [Field K] (a b c : Vertex K) :
    incidence a b → incidence b c → incidence c a → False := by
  cases a <;> cases b <;> cases c <;> simp [incidence]

theorem no_square {K : Type*} [Field K] (a b c d : Vertex K)
    (ab : incidence a b) (bc : incidence b c) (cd : incidence c d) (da : incidence d a) :
    a=c ∨ b=d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all only [incidence,Sum.inl.injEq,Sum.inr.injEq]
  · exact intersection _ _ _ _ ab bc da cd
  · exact (intersection _ _ _ _ ab da bc cd).symm

/-- The absence of triangles and simple squares in a graph rules out all cycles of length below five. -/
theorem girth_five {V : Type*} (G : SimpleGraph V)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (sq : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d)
    (v : V) (p : G.Walk v v) (cyc : p.IsCycle) : 5 ≤ p.length := by
  have lo := cyc.three_le_length
  by_contra h
  have adj (i : ℕ) (hi : i<p.length) := p.adj_getVert_succ hi
  have ends : p.getVert p.length = p.getVert 0 := by simp
  have casesLen : p.length=3 ∨ p.length=4 := by omega
  rcases casesLen with three|four
  · rw [three] at ends
    exact tri _ _ _ (adj 0 (by omega)) (adj 1 (by omega)) (ends ▸ adj 2 (by omega))
  · rw [four] at ends
    rcases sq _ _ _ _ (adj 0 (by omega)) (adj 1 (by omega)) (adj 2 (by omega))
      (ends ▸ adj 3 (by omega)) with eq|eq
    · have bad := cyc.getVert_injOn' (x₁:=0) (x₂:=2) (by simp [four]) (by simp [four]) eq
      omega
    · have bad := cyc.getVert_injOn' (x₁:=1) (x₂:=3) (by simp [four]) (by simp [four]) eq
      omega

def numbered {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n) := (graph K).comap e.symm

theorem numbered_girth {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n)
    (v : Fin n) (p : (numbered e).Walk v v) (hc : p.IsCycle) : 5 ≤ p.length :=
  girth_five (numbered e) (fun a b c => no_triangle (e.symm a) (e.symm b) (e.symm c))
    (fun a b c d ab bc cd da => by
      rcases no_square (e.symm a) (e.symm b) (e.symm c) (e.symm d) ab bc cd da with eq|eq
      · exact Or.inl (e.symm.injective eq)
      · exact Or.inr (e.symm.injective eq))
    v p hc

private def edgeLabel {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n) (t : K×K×K) :=
  s(e (.inl (t.1,t.2.1*t.1+t.2.2)),e (.inr t.2))

private theorem edgeLabel_injective {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n) :
    Function.Injective (edgeLabel e) := by
  rintro ⟨x,a,b⟩ ⟨y,c,d⟩ eq
  simp only [edgeLabel,Sym2.eq_iff,EmbeddingLike.apply_eq_iff_eq,Sum.inl.injEq,Sum.inr.injEq,
    Prod.mk.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,false_and,or_false] at eq
  exact Prod.ext eq.1.1 (Prod.ext eq.2.1 eq.2.2)

private theorem edgeLabel_mem {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n) (t : K×K×K) :
    edgeLabel e t ∈ (numbered e).edgeSet := by
  change incidence (e.symm (e (.inl _))) (e.symm (e (.inr _)))
  simp [incidence,lies]

private theorem edgeLabel_hits {K : Type*} [Field K] {n : ℕ} (e : Vertex K ≃ Fin n)
    (z : Sym2 (Fin n)) (hz : z∈(numbered e).edgeSet) : ∃ t, edgeLabel e t=z := by
  induction z using Sym2.inductionOn with
  | _ i j =>
    obtain ⟨u,rfl⟩ := e.surjective i
    obtain ⟨v,rfl⟩ := e.surjective j
    change incidence (e.symm (e u)) (e.symm (e v)) at hz
    simp only [Equiv.symm_apply_apply] at hz
    cases u with
    | inl point =>
      cases v with
      | inl other => exact hz.elim
      | inr line =>
        rcases point with ⟨x,y⟩; rcases line with ⟨a,b⟩
        change y=a*x+b at hz
        subst y
        exact ⟨(x,a,b),rfl⟩
    | inr line =>
      cases v with
      | inr other => exact hz.elim
      | inl point =>
        rcases point with ⟨x,y⟩; rcases line with ⟨a,b⟩
        change y=a*x+b at hz
        subst y
        exact ⟨(x,a,b),Sym2.eq_swap⟩

theorem edge_count_exact {K : Type*} [Field K] [Fintype K] {n : ℕ} (e : Vertex K ≃ Fin n)
    [DecidableRel (numbered e).Adj] : (Fintype.card K)^3 = (numbered e).edgeFinset.card := by
  classical
  have subset : Finset.univ.image (edgeLabel e) ⊆ (numbered e).edgeFinset := by
    intro z hz
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact SimpleGraph.mem_edgeFinset.mpr (edgeLabel_mem e t)
  have all : Finset.univ.image (edgeLabel e) = (numbered e).edgeFinset := by
    apply Finset.Subset.antisymm subset
    intro z hz
    obtain ⟨t,eq⟩ := edgeLabel_hits e z (SimpleGraph.mem_edgeFinset.mp hz)
    exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,eq⟩
  have card := congrArg Finset.card all
  rw [Finset.card_image_of_injective _ (edgeLabel_injective e)] at card
  simpa [Fintype.card_prod,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using card

/-- Read the point from either endpoint of the matching (x,y) ~ (x,y−x²). -/
private def owner {K : Type*} [Field K] : Vertex K → K×K
  | .inl p => p
  | .inr (a,b) => (a,a*a+b)

theorem cover_count {K : Type*} [Field K] [Fintype K] {n : ℕ} (e : Vertex K ≃ Fin n)
    (T : Finset (Fin n)) (cover : ∀ i j, (numbered e).Adj i j → i∈T ∨ j∈T) :
    (Fintype.card K)^2 ≤ T.card := by
  classical
  have all : Finset.univ ⊆ T.image (fun j => owner (e.symm j)) := by
    rintro ⟨x,y⟩ _
    let a := e (.inl (x,y))
    let b := e (.inr (x,y-x*x))
    have edge : (numbered e).Adj a b := by
      change incidence (e.symm a) (e.symm b)
      simp [a,b,incidence,lies]
    rcases cover a b edge with ha|hb
    · exact Finset.mem_image.mpr ⟨a,ha,by simp [a,owner]⟩
    · exact Finset.mem_image.mpr ⟨b,hb,by simp [b,owner]⟩
  have card := le_trans (Finset.card_le_card all) (Finset.card_image_le (s:=T))
  simpa [Fintype.card_prod,pow_two] using card

theorem vertex_count (K : Type*) [Fintype K] : Fintype.card (Vertex K) = 2*(Fintype.card K)^2 := by
  simp [Vertex,Fintype.card_sum,Fintype.card_prod,two_mul,pow_two]

end PEqualNP.Outside.Affine608

namespace PEqualNP.Outside.Affine608
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The exact external L608 statement specialized to an explicitly described incidence family.
Every numbering of the 2q² input variables gives the same q³+q²−1 gate lower bound. -/
theorem consequence
    (bound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
        G.edgeFinset.card + T.card ≤ D.size + 1)
    {K : Type*} [Field K] [Fintype K]
    (e : Vertex K ≃ Fin (2*(Fintype.card K)^2)) [DecidableRel (numbered e).Adj]
    (D : Circuit) (mono : Monotone2 D)
    (computes : circuitFun _ D = fun x => decide (∃ i j, (numbered e).Adj i j ∧ x i=true ∧ x j=true)) :
    (Fintype.card K)^3 + (Fintype.card K)^2 ≤ D.size+1 := by
  obtain ⟨T,cover,lower⟩ := bound _ (numbered e) (numbered_girth e) D mono computes
  exact (Nat.add_le_add (edge_count_exact e).le (cover_count e T cover)).trans lower

end PEqualNP.Outside.Affine608
