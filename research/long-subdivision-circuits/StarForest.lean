import PEqualNP.Defs
import Mathlib

/-! Essential-input and terminal-star bounds for the physical circuit model. -/
namespace Subdivision.StarForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Finset

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map (fun i => xs.getD i false))]

private def back (n : ℕ) : List Gate → Finset ℕ → Finset ℕ
  | [], S => S
  | g::gs, S =>
    let T := back (n+1) gs S
    if n∈T then T.erase n ∪ g.inputs.toFinset else T

private theorem back_card (n : ℕ) (gs : List Gate) (S : Finset ℕ)
    (fanin : ∀ g∈gs, g.inputs.length≤2) :
    (back n gs S).card ≤ S.card+gs.length := by
  induction gs generalizing n with
  | nil => simp [back]
  | cons g gs ih =>
    have hg := fanin g (by simp)
    have h := ih (n+1) (fun k hk => fanin k (by simp [hk]))
    by_cases mem : n∈back (n+1) gs S
    · have ce := Finset.card_erase_add_one mem
      have cu := Finset.card_union_le ((back (n+1) gs S).erase n) g.inputs.toFinset
      have ci := List.toFinset_card_le g.inputs
      simp only [back,ite_eq_left mem,List.length_cons]
      omega
    · simp [back,mem]
      omega

private def agree (S : Finset ℕ) (x y : List Bool) :=
  ∀ i∈S, x.getD i false=y.getD i false

private theorem step_get (x : List Bool) (g : Gate) (i : ℕ) (ne : i≠x.length) :
    (step x g).getD i false=x.getD i false := by
  by_cases lt : i<x.length
  · exact List.getD_append _ _ _ _ lt
  · have gt : x.length < i := by omega
    rw [List.getD_eq_default, List.getD_eq_default]
    · simp [gt.le]
    · simp [step]
      omega

private theorem back_agree (gs : List Gate) (n : ℕ) (S : Finset ℕ) (x y : List Bool)
    (lx : x.length=n) (ly : y.length=n) (same : agree (back n gs S) x y) :
    agree S (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing n x y with
  | nil => exact same
  | cons g gs ih =>
    let T := back (n+1) gs S
    apply ih (n+1) (step x g) (step y g) (by simp [step,lx]) (by simp [step,ly])
    intro i hi
    change i∈T at hi
    by_cases nm : n∈T
    · have pre : agree (T.erase n ∪ g.inputs.toFinset) x y := by simpa [back,T,nm] using same
      by_cases eq : i=n
      · subst i
        have vals : g.inputs.map (fun j => x.getD j false)=g.inputs.map (fun j => y.getD j false) := by
          apply List.map_congr_left
          intro j hj
          exact pre j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
        simp [step,lx,ly]
        simpa only [List.getD_eq_getElem?_getD] using congrArg g.op.eval vals
      · rw [step_get _ _ _ (lx ▸ eq),step_get _ _ _ (ly ▸ eq)]
        exact pre i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩))
    · have pre : agree T x y := by simpa [back,T,nm] using same
      have eq : i≠n := fun h => nm (h ▸ hi)
      rw [step_get _ _ _ (lx ▸ eq),step_get _ _ _ (ly ▸ eq)]
      exact pre i hi

/-- Every fan-in-two size-s physical circuit depends on at most s+1 input coordinates;
forward and out-of-range reads are allowed, as in the project semantics. -/
theorem support_of_size {N s : ℕ} {f : (Fin N→Bool)→Bool} (h : HasCircuitSize N f s) :
    ∃ U : Finset (Fin N), U.card≤ s+1 ∧ ∀ x y, (∀ u∈U, x u=y u) → f x=f y := by
  classical
  obtain ⟨C,fan,size,sem⟩ := h
  let S := back N C.gates {C.output}
  let U : Finset (Fin N) := Finset.univ.filter (fun i => i.val∈S)
  have c1 : U.card≤S.card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin N => i.val)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro _ _ _ _ h
      exact Fin.ext h
  have c2 := back_card N C.gates {C.output} (fun g hg => (fan g hg).2)
  change C.gates.length≤ s at size
  refine ⟨U,by simp only [Finset.card_singleton] at c2; dsimp [S] at c1; omega,?_⟩
  intro x y hyp
  rw [← sem x,← sem y]
  change (C.gates.foldl step (List.ofFn x)).getD C.output false =
    (C.gates.foldl step (List.ofFn y)).getD C.output false
  apply back_agree C.gates N {C.output} _ _ (by simp) (by simp) _ C.output (by simp)
  intro i hi
  by_cases good : i<N
  · have h := hyp ⟨i,good⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
    simpa [List.getD_eq_getElem?_getD,good] using h
  · rw [List.getD_eq_default,List.getD_eq_default] <;> simp <;> omega

/-- A forest of pendant vertices, one distinct tip per edge and no shared vertex
between the tips and the owner set, needs one fewer gate than its essential vertices. -/
theorem general_lower {N m s : ℕ} (owner tip : Fin m → Fin N) (inj : Function.Injective tip)
    (disj : ∀ i j, owner i≠tip j) {f : (Fin N→Bool)→Bool}
    (sem : ∀ x, f x=true ↔ ∃ i, x (owner i)=true ∧ x (tip i)=true)
    (h : HasCircuitSize N f s) :
    m+(Finset.univ.image owner).card≤ s+1 := by
  classical
  obtain ⟨U,uca,ins⟩ := support_of_size h
  have both (a b : Fin N) (hit : ∃ i, (owner i=a ∧ tip i=b) ∨ (owner i=b ∧ tip i=a)) :
      a∈U := by
    by_contra au
    let x (v : Fin N) := decide (v=a ∨ v=b)
    let y (v : Fin N) := decide (v=b)
    have same : f x = f y := ins x y (by
      intro u hu
      have ne : u≠a := fun eq => au (eq ▸ hu)
      simp [x,y,ne])
    have yes : f x=true := (sem x).mpr (by
      obtain ⟨i,⟨h1,h2⟩ | ⟨h1,h2⟩⟩ := hit
      · exact ⟨i,by simp [x,h1],by simp [x,h2]⟩
      · exact ⟨i,by simp [x,h1],by simp [x,h2]⟩)
    obtain ⟨i,ha,hb⟩ := (sem y).mp (same ▸ yes)
    have a1 : owner i=b := of_decide_eq_true ha
    have b1 : tip i=b := of_decide_eq_true hb
    exact disj i i (a1.trans b1.symm)
  have owners : Finset.univ.image owner ⊆ U := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact both _ _ ⟨i,Or.inl ⟨rfl,rfl⟩⟩
  have tips : Finset.univ.image tip ⊆ U := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact both _ _ ⟨i,Or.inr ⟨rfl,rfl⟩⟩
  have d : Disjoint (Finset.univ.image tip) (Finset.univ.image owner) := by
    apply Finset.disjoint_left.mpr
    rintro v hv ho
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ho
    exact disj j i (hj.trans hi.symm)
  have lower := (Finset.card_le_card (Finset.union_subset tips owners)).trans uca
  simpa [Finset.card_union_of_disjoint d,Finset.card_image_of_injective _ inj] using lower

/-- The staged terminal form with the old vertices followed by its private leaves. -/
theorem starForest_lower {n m s : ℕ} (owner : Fin m → Fin n)
    (h : HasCircuitSize (n+m) (fun x => decide (∃ i, x ((owner i).castAdd m)=true ∧
      x (Fin.natAdd n i)=true)) s) :
    m+(Finset.univ.image owner).card≤ s+1 := by
  let own (i : Fin m) := (owner i).castAdd m
  have out := general_lower own (Fin.natAdd n) (Fin.natAdd_injective m n)
      (fun i j eq => by have hv := congrArg Fin.val eq; dsimp [own] at hv; omega)
      (f:=fun x => decide (∃ i, x (own i)=true ∧ x (Fin.natAdd n i)=true))
      (fun x => by simp) h
  have eq : Finset.univ.image own = (Finset.univ.image owner).image (Fin.castAdd m) := by
    simp [own,Finset.image_image,Function.comp_def]
  rw [eq,Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)] at out
  exact out

end Subdivision.StarForest

#print axioms Subdivision.StarForest.support_of_size
#print axioms Subdivision.StarForest.starForest_lower
