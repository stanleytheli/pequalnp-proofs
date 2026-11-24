import CircuitPins
import WindowCore997

/-! Transfer the descending-word window to the collaboration's raw gate list.
This file is checked only in the disposable guest with the project definitions. -/
namespace LimitedNegation.Project
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside

def allowed (g : Gate) : Prop := g.op = .and ∨ g.op = .or ∨ g.op = .not

def vector (xs : List Bool) : Wires := fun i => xs.getD i false

theorem vector_append (xs : List Bool) (b : Bool) :
    vector (xs++[b]) = Function.update (vector xs) xs.length b := by
  funext i
  by_cases hi : i < xs.length
  · simp only [vector,List.getD_append _ _ _ _ hi,Function.update_of_ne (Nat.ne_of_lt hi)]
  by_cases eq : i=xs.length
  · subst i
    simp [vector,List.getD_eq_getElem,Function.update_self]
  · have ho : (xs++[b]).length ≤ i := by simp; omega
    have hp : xs.length ≤ i := by omega
    simp only [vector,Function.update_of_ne eq,List.getD_eq_default _ _ ho,List.getD_eq_default _ _ hp]

def allW (l : List ℕ) : Wires →o Bool where
  toFun w := l.all w
  monotone' := by
    intro x y xy
    rw [Bool.le_iff_imp]
    intro hx
    exact List.all_eq_true.mpr (fun i hi => (Bool.le_iff_imp.mp (xy i)) (List.all_eq_true.mp hx i hi))

def anyW (l : List ℕ) : Wires →o Bool where
  toFun w := l.any w
  monotone' := by
    intro x y xy
    rw [Bool.le_iff_imp]
    intro hx
    obtain ⟨i,hi,hx⟩ := List.any_eq_true.mp hx
    exact List.any_eq_true.mpr ⟨i,hi,Bool.le_iff_imp.mp (xy i) hx⟩

def firstW : List ℕ → Wires →o Bool
  | [] => OrderHom.const _ false
  | j::_ => ⟨fun w => w j, fun _ _ h => h j⟩

def translate (offset : ℕ) (g : Gate) : Stage :=
  match g.op with
  | .not => .negative offset (firstW g.inputs)
  | .and => .positive offset (allW g.inputs)
  | _ => .positive offset (anyW g.inputs)

def stages : ℕ → List Gate → List Stage
  | _,[] => []
  | i,g::gs => translate i g :: stages (i+1) gs

def constGate (b : Bool) : Gate := ⟨if b then .and else .or, []⟩

lemma constGate_value (b : Bool) (x : List Bool) :
    (constGate b).op.eval ((constGate b).inputs.map (vector x)) = b := by
  cases b <;> rfl

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def frozen : List Gate → List Bool → List Gate
  | [],_ => []
  | g::gs,bits => if isNot g.op then constGate (bits.headD false) :: frozen gs bits.tail
      else g :: frozen gs bits

theorem frozen_len (gs : List Gate) (bits : List Bool) : (frozen gs bits).length=gs.length := by
  induction gs generalizing bits with
  | nil => rfl
  | cons g gs ih => by_cases h : isNot g.op=true <;> simp [frozen,h,ih]

theorem translated_count (gs : List Gate) (n : ℕ) :
    negations (stages n gs) = gs.countP (fun g => isNot g.op) := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | mk op ids =>
      cases op <;> simp [stages,translate,negations,ih,List.countP_cons,isNot]

theorem run_list (gs : List Gate) (valid : ∀ g∈gs, allowed g) (x : List Bool) :
    LimitedNegation.run (stages x.length gs) (vector x) = vector (Window997.run gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have tail : ∀ e∈gs, allowed e := fun e h => valid e (by simp [h])
    have h := valid g (by simp)
    obtain ⟨op,ids⟩ := g
    rcases h with h|h|h <;> change op=_ at h <;> subst op
    · rw [Window997.run_cons, ← ih tail,vector_append]
      simp [stages,translate,LimitedNegation.run,allW,GateOp.eval,vector] <;> rfl
    · rw [Window997.run_cons, ← ih tail,vector_append]
      simp [stages,translate,LimitedNegation.run,anyW,GateOp.eval,vector] <;> rfl
    · rw [Window997.run_cons, ← ih tail,vector_append]
      cases ids <;> simp [stages,translate,LimitedNegation.run,firstW,GateOp.eval,vector] <;> rfl

theorem pin_list (gs : List Gate) (valid : ∀ g∈gs, allowed g) (x : List Bool) (bits : List Bool) :
    LimitedNegation.pin (stages x.length gs) bits (vector x) = vector (Window997.run (frozen gs bits) x) := by
  induction gs generalizing x bits with
  | nil => rfl
  | cons g gs ih =>
    have tail : ∀ e∈gs, allowed e := fun e h => valid e (by simp [h])
    have h := valid g (by simp)
    obtain ⟨op,ids⟩ := g
    rcases h with h|h|h <;> change op=_ at h <;> subst op
    · simp only [frozen,isNot,Bool.false_eq_true,ite_false,Window997.run_cons]
      rw [← ih tail,vector_append]
      simp [stages,translate,LimitedNegation.pin,allW,GateOp.eval,vector] <;> rfl
    · simp only [frozen,isNot,Bool.false_eq_true,ite_false,Window997.run_cons]
      rw [← ih tail,vector_append]
      simp [stages,translate,LimitedNegation.pin,anyW,GateOp.eval,vector] <;> rfl
    · simp only [frozen,isNot,ite_true,Window997.run_cons]
      rw [← ih tail,vector_append]
      simp only [stages,translate,LimitedNegation.pin,List.length_append,List.length_singleton]
      change LimitedNegation.pin _ _ (Function.update _ _ _) =
        LimitedNegation.pin _ _ (Function.update _ _ ((constGate (bits.headD false)).op.eval
          ((constGate (bits.headD false)).inputs.map (vector x))))
      rw [constGate_value]

end LimitedNegation.Project
#print axioms LimitedNegation.Project.run_list
#print axioms LimitedNegation.Project.pin_list
