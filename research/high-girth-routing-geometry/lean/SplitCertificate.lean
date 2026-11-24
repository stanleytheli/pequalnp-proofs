import RoutedModel
import Mathlib.Data.List.OfFn

namespace SparsePermanent.SplitCertificate
open RoutedModel
variable {R : Type*} [CommSemiring R]

abbrev Wire := ℕ×ℕ

structure Step where
  outgoing : Bool
  parent : ℕ
  fresh : ℕ
  moved : List ℕ
deriving Repr

def shift (s : Step) (w : Wire) : Wire :=
  if w.1=s.parent ∧ w.2∈s.moved then (s.fresh,w.2) else w

def outWires (s : Step) (w : List Wire) : List Wire :=
  (s.fresh,s.fresh)::(s.parent,s.fresh)::w.map (shift s)

def stepWires (s : Step) (w : List Wire) : List Wire :=
  if s.outgoing then outWires s w else (outWires s (w.map Prod.swap)).map Prod.swap

def Covered {n : ℕ} (B : Matrix (Fin n) (Fin n) R) (id : Fin n→ℕ) (w : List Wire) :=
  ∀ i j,B j i≠0→(id i,id j)∈w

private theorem cover_out {n : ℕ} (B : Matrix (Fin n) (Fin n) R) (id : Fin n→ℕ) (v : Fin n)
    (s : Step) (w : List Wire) (valid : Covered B id w) (inj : Function.Injective id)
    (parent : id v=s.parent) :
    Covered (numbered (DirectedSplit.outgoing B v (fun i=>id i∈s.moved)))
      (Fin.cons s.fresh id) (outWires s w) := by
  intro i j
  refine Fin.cases ?_ (fun x=>?_) i <;> refine Fin.cases ?_ (fun y=>?_) j
  · intro _;exact List.mem_cons_self
  · simp only [numbered,Matrix.submatrix_apply,finSuccEquiv_zero,finSuccEquiv_succ,
      DirectedSplit.outgoing,Fin.cons_zero,Fin.cons_succ]
    intro nz
    by_cases target : id y∈s.moved
    · have e:=valid v y (by simpa [target] using nz)
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨_,e,by simp [shift,parent,target]⟩
    · simp [target] at nz
  · simp only [numbered,Matrix.submatrix_apply,finSuccEquiv_zero,finSuccEquiv_succ,
      DirectedSplit.outgoing,Fin.cons_zero,Fin.cons_succ]
    intro nz
    by_cases eq:x=v
    · subst x; simp [outWires,parent]
    · simp [eq] at nz
  · simp only [numbered,Matrix.submatrix_apply,finSuccEquiv_succ,DirectedSplit.outgoing,Fin.cons_succ]
    intro nz
    by_cases choose : x=v ∧ id y∈s.moved
    · simp [choose] at nz
    · have old:=valid x y (by simpa [choose] using nz)
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨_,old,by
        have no : ¬(id x=s.parent ∧ id y∈s.moved):=fun e=>choose ⟨inj (e.1.trans parent.symm),e.2⟩
        simp [shift,no]⟩

private theorem swap_covered {n : ℕ} {B : Matrix (Fin n) (Fin n) R} {id : Fin n→ℕ} {w : List Wire}
    (ok : Covered B id w) : Covered B.transpose id (w.map Prod.swap) :=
  fun i j nz=>List.mem_map.mpr ⟨_,ok j i nz,rfl⟩

structure State where
  names : List ℕ
  wires : List Wire

def advance (s : Step) (t : State) : Option State :=
  if s.parent∈t.names ∧ s.fresh∉t.names then some ⟨s.fresh::t.names,stepWires s t.wires⟩ else none

def replay (s : State) : List Step→Option State
  | []=>some s
  | t::ts=>(advance t s).bind (fun u=>replay u ts)

def Realized {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (t : State) : Prop :=
  ∃ n,∃ B : Matrix (Fin n) (Fin n) R,∃id : Fin n→ℕ,
    Generated A B ∧ Function.Injective id ∧ List.ofFn id=t.names ∧ Covered B id t.wires

private theorem one {m : ℕ} {A : Matrix (Fin m) (Fin m) R} {t u : State} (s : Step)
    (before : Realized A t) (ok : advance s t=some u) : Realized A u := by
  classical
  unfold advance at ok
  split at ok
  next good=>
    cases ok
    obtain ⟨n,B,id,model,inj,listed,cover⟩:=before
    obtain ⟨v,eq⟩:=List.mem_ofFn.mp (listed ▸ good.1)
    have next_id : Function.Injective (Fin.cons s.fresh id) := by
      intro i j
      refine Fin.cases ?_ (fun x=>?_) i <;> refine Fin.cases ?_ (fun y=>?_) j
      · intro _;rfl
      · intro e; exact (good.2 (listed ▸ List.mem_ofFn.mpr ⟨y,e.symm⟩)).elim
      · intro e; exact (good.2 (listed ▸ List.mem_ofFn.mpr ⟨x,e⟩)).elim
      · intro e; exact congrArg Fin.succ (inj e)
    have names : List.ofFn (Fin.cons s.fresh id)=s.fresh::t.names := by rw [List.ofFn_succ];simp [listed]
    let group:=Finset.univ.filter (fun i=>id i∈s.moved)
    have eqGroup (D : Matrix (Fin n) (Fin n) R) : DirectedSplit.outgoing D v (·∈group)=
        DirectedSplit.outgoing D v (fun i=>id i∈s.moved) := by
      ext x y;cases x <;> cases y <;> simp [DirectedSplit.outgoing,group]
    by_cases o:s.outgoing=true
    · refine ⟨n+1,_,_,model.outgoing v group,next_id,names,?_⟩
      simpa only [stepWires,o,if_true,eqGroup] using cover_out B id v s t.wires cover inj eq
    · refine ⟨n+1,_,_,model.incoming v group,next_id,names,?_⟩
      have result:=swap_covered (cover_out B.transpose id v s _ (swap_covered cover) inj eq)
      simpa [stepWires,o,DirectedSplit.incoming,numbered,Matrix.transpose_submatrix,eqGroup] using result
  next=>simp at ok

theorem replay_sound {m : ℕ} {A : Matrix (Fin m) (Fin m) R} (steps : List Step) {t u : State}
    (start : Realized A t) (passed : replay t steps=some u) : Realized A u := by
  induction steps generalizing t with
  | nil=>cases passed;exact start
  | cons s rest ih=>
    simp only [replay] at passed
    cases e:advance s t with
    | none=>simp [e] at passed
    | some v=>exact ih (one s start e) (by simpa [e] using passed)

def initial (names : List ℕ) : State:=
  ⟨names,names.flatMap (fun i=>names.map (fun j=>(i,j)))⟩

theorem start {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (centers : Fin m→ℕ)
    (distinct : Function.Injective centers) : Realized A (initial (List.ofFn centers)) := by
  refine ⟨m,A,centers,.base,distinct,rfl,?_⟩
  intro i j _
  exact List.mem_flatMap.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩⟩

end SparsePermanent.SplitCertificate
#print axioms SparsePermanent.SplitCertificate.replay_sound
