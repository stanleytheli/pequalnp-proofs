import FormulaRank

namespace ProjectivePlane650
open WeightedFormula

abbrev V := Fin 26

/-- Ordered point–line incidences from L-meta-650. -/
def edges : List (ℕ × ℕ) := [
  (0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

def N : V → Finset V := ![
  {13, 14, 16, 22},
  {13, 15, 21, 25},
  {14, 20, 24, 25},
  {13, 19, 23, 24},
  {18, 22, 23, 25},
  {17, 21, 22, 24},
  {16, 20, 21, 23},
  {15, 19, 20, 22},
  {14, 18, 19, 21},
  {13, 17, 18, 20},
  {16, 17, 19, 25},
  {15, 16, 18, 24},
  {14, 15, 17, 23},
  {0, 1, 3, 9},
  {0, 2, 8, 12},
  {1, 7, 11, 12},
  {0, 6, 10, 11},
  {5, 9, 10, 12},
  {4, 8, 9, 11},
  {3, 7, 8, 10},
  {2, 6, 7, 9},
  {1, 5, 6, 8},
  {0, 4, 5, 7},
  {3, 4, 6, 12},
  {2, 3, 5, 11},
  {1, 2, 4, 10}]

theorem symmetric : ∀ a b : V, b ∈ N a ↔ a ∈ N b := by decide +kernel
theorem irreflexive : ∀ a : V, a ∉ N a := by decide +kernel

def G : SimpleGraph V where
  Adj a b := b ∈ N a
  symm := by constructor; intro a b h; exact (symmetric a b).mp h
  loopless := ⟨irreflexive⟩

instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (b∈N a))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem inc_table : ∀ a b : V, b∈N a ↔
    (a.val,b.val)∈edges ∨ (b.val,a.val)∈edges := by decide +kernel

theorem disjoint_neighbors : ∀ a b : V, b∈N a → Disjoint (N a) (N b) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
theorem common_neighbors : ∀ a b : V, a≠b → ((N a)∩(N b)).card ≤ 1 := by decide +kernel

theorem triangle {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False :=
  (Finset.disjoint_left.mp (disjoint_neighbors a b ab)) ((symmetric c a).mp ca) bc

theorem square {a b c d : V} (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (da : G.Adj d a) : a=c ∨ b=d := by
  by_cases ac : a=c
  · exact Or.inl ac
  apply Or.inr
  apply Finset.card_le_one.mp (common_neighbors a c ac) b
    (Finset.mem_inter.mpr ⟨ab,(symmetric b c).mp bc⟩) d
    (Finset.mem_inter.mpr ⟨(symmetric d a).mp da,cd⟩)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem num_edges : G.edgeFinset.card=52 := by decide +kernel

def point (i : Fin 13) : V := ⟨i.val,by omega⟩
def matched : Fin 13 → V := ![13, 15, 14, 19, 18, 17, 16, 22, 21, 20, 25, 24, 23]

theorem point_injective : Function.Injective point := by
  intro a b h
  exact Fin.ext (congrArg (fun z : V => z.val) h)

theorem match_data : (∀ i, matched i∈N (point i)) ∧
    (∀ i j, matched i=matched j → i=j) ∧ (∀ i j, point i ≠ matched j) := by decide +kernel

theorem min_cover (T : Finset V) (cov : ∀ a b, G.Adj a b → a∈T ∨ b∈T) : 13≤T.card := by
  classical
  let pick (i : Fin 13) : V := if point i∈T then point i else matched i
  have mem (i) : pick i∈T := by
    have h := cov (point i) (matched i) (match_data.1 i)
    by_cases hi : point i∈T <;> simp_all [pick]
  have inj : Function.Injective (fun i => (⟨pick i,mem i⟩ : T)) := by
    intro i j h
    have eq : pick i=pick j := congrArg Subtype.val h
    by_cases hi : point i∈T <;> by_cases hj : point j∈T <;> simp [pick,hi,hj] at eq
    · exact point_injective eq
    · exact (match_data.2.2 i j eq).elim
    · exact (match_data.2.2 j i eq.symm).elim
    · exact match_data.2.1 i j eq
  simpa using Fintype.card_le_of_injective _ inj

def accepts (x : V→Bool) := ∃ u v : V, (u.val,v.val)∈edges ∧ x u=true ∧ x v=true

theorem accepts_iff (x : V→Bool) :
    accepts x ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,(inc_table u v).mpr (Or.inl h),hu,hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    rcases (inc_table u v).mp h with h | h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩

theorem lower (f : Formula V) (correct : ∀ x, f.eval x=true ↔ accepts x) : 64≤f.gates := by
  obtain ⟨T,hT,hl⟩ := cover_of_formula_local G (@triangle) (@square) f
    (fun x => (correct x).trans (accepts_iff x))
  have h := min_cover T hT
  rw [num_edges,f.leaves_eq] at hl
  omega

def allPoints := Finset.univ.image point

theorem point_cover : (∀ u v : V, v∈N u → u∈allPoints ∨ v∈allPoints) ∧ allPoints.card=13 := by
  decide +kernel

theorem exact_size : ∃ f : Formula V, (∀ x, f.eval x=true ↔ accepts x) ∧ f.gates=64 := by
  have hn : G.edgeFinset.Nonempty := Finset.card_pos.mp (num_edges ▸ by decide)
  obtain ⟨f,h,hl⟩ := formula_of_cover G hn allPoints point_cover.1
  have hc (x) := (h x).trans (accepts_iff x).symm
  have min := lower f hc
  rw [num_edges,point_cover.2,f.leaves_eq] at hl
  exact ⟨f,hc,by omega⟩

end ProjectivePlane650

#print axioms ProjectivePlane650.lower
#print axioms ProjectivePlane650.exact_size
