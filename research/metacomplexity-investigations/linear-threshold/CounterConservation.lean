import Mathlib.Data.List.Count

namespace LinearThreshold

def xor4 (a b : Bool) : Bool := (a || b) && !(a && b)
def low (a b c : Bool) : Bool := xor4 (xor4 a b) c
def high (a b c : Bool) : Bool := (a && b) || ((xor4 a b) && c)

inductive Column : List Bool → Bool → List Bool → ℕ → ℕ → Prop
  | one (a : Bool) : Column [a] a [] 0 0
  | two (a b : Bool) : Column [a,b] (xor4 a b) [a && b] 0 1
  | triple (a b c : Bool) (xs : List Bool) {v : Bool} {cs : List Bool} {f h : ℕ}
      (rest : Column (low a b c::xs) v cs f h) :
      Column (a::b::c::xs) v (high a b c::cs) (f+1) h

theorem column_mass {xs v cs f h} (run : Column xs v cs f h) :
    xs.count true = v.toNat + 2 * cs.count true := by
  induction run with
  | one a => cases a <;> decide
  | two a b => cases a <;> cases b <;> decide
  | triple a b c xs rest ih =>
    cases a <;> cases b <;> cases c <;>
      simp [low,high,xor4] at ih ⊢ <;> omega

theorem column_shape {xs v cs f h} (run : Column xs v cs f h) :
    xs.length = cs.length + f + 1 ∧ cs.length = xs.length / 2 ∧ h ≤ 1 ∧
    (cs.length = 0 → h=0) := by
  induction run with
  | one => simp
  | two => simp
  | triple a b c xs rest ih =>
    simp only [List.length_cons] at *
    obtain ⟨eq,cv,hb,_⟩ := ih
    exact ⟨by omega,by omega,hb,by omega⟩

theorem column_exists : ∀ xs : List Bool, xs ≠ [] → ∃ v cs f h, Column xs v cs f h
  | [], ha => (ha rfl).elim
  | [a], _ => ⟨_,_,_,_,.one a⟩
  | [a,b], _ => ⟨_,_,_,_,.two a b⟩
  | a::b::c::xs, _ => by
      obtain ⟨v,cs,f,h,rest⟩ := column_exists (low a b c::xs) (by simp)
      exact ⟨v,_,_,h,.triple a b c xs rest⟩
termination_by xs => xs.length
decreasing_by simp_wf

inductive CountColumns : List Bool → List Bool → ℕ → ℕ → Prop
  | empty : CountColumns [] [] 0 0
  | next {xs v cs f h bs g j} (head : Column xs v cs f h) (rest : CountColumns cs bs g j) :
      CountColumns xs (v::bs) (f+g) (h+j)

def number : List Bool → ℕ
  | [] => 0
  | a::as => a.toNat + 2*number as

theorem mass {xs bs f h} (run : CountColumns xs bs f h) : xs.count true=number bs := by
  induction run with
  | empty => rfl
  | next head _ ih => rw [column_mass head,ih,number]

theorem counts {xs bs f h} (run : CountColumns xs bs f h) :
    xs.length = f + bs.length ∧ h ≤ bs.length ∧ (xs≠[] → h < bs.length) := by
  induction run with
  | empty => simp
  | @next xs v cs f h bs g j head rest ih =>
    obtain ⟨eq,_,hb,zero⟩ := column_shape head
    obtain ⟨tailEq,le,lt⟩ := ih
    simp only [List.length_cons]
    refine ⟨by omega,by omega,fun _=>?_⟩
    by_cases empty : cs=[]
    · subst cs
      simp at tailEq
      have := zero rfl
      omega
    · have := lt empty
      omega

theorem counter_exists (xs : List Bool) : ∃ bs f h, CountColumns xs bs f h := by
  by_cases e : xs=[]
  · subst xs; exact ⟨_,_,_,.empty⟩
  · obtain ⟨v,cs,f,h,head⟩ := column_exists xs e
    have bound := (column_shape head).1
    obtain ⟨bs,g,j,tail⟩ := counter_exists cs
    exact ⟨_,_,_,.next head tail⟩
termination_by xs.length
decreasing_by omega

/-- One constant gate for arbitrary dangling reads, 9/full, 4/half and at
most B-1 for the comparison against a fixed positive B-bit threshold. -/
theorem gate_budget {xs bs f h} (run : CountColumns xs bs f h) (ne : xs≠[]) :
    1+9*f+4*h+(bs.length-1) ≤ 9*xs.length-8 := by
  obtain ⟨n,_,hn⟩ := counts run
  have := hn ne
  omega

theorem comparison_step (target data : Bool) (place lowerTarget lowerData : ℕ)
    (a : lowerTarget < place) (b : lowerData < place) :
    decide (place*target.toNat+lowerTarget ≤ place*data.toNat+lowerData) =
    if target then data && decide (lowerTarget≤lowerData)
    else data || decide (lowerTarget≤lowerData) := by
  cases target <;> cases data <;> simp <;> omega

end LinearThreshold
#print axioms LinearThreshold.counter_exists
#print axioms LinearThreshold.mass
#print axioms LinearThreshold.gate_budget
#print axioms LinearThreshold.comparison_step
