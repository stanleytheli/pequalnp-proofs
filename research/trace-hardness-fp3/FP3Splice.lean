import FP3Override
namespace FiniteOverride
open Turing PEqualNP.Library

abbrev Short (n : ℕ) := {w : List Bool // w.length<n}

private def shortCode (n : ℕ) (w : Short n) : Fin n × (Fin n→Bool) :=
  (⟨w.val.length,w.property⟩,fun j=>w.val.getD j.val false)

noncomputable instance shortFintype (n : ℕ) : Fintype (Short n) :=
  Fintype.ofInjective (shortCode n) (by
    intro x y h
    apply Subtype.ext
    apply List.ext_getElem
    · exact congrArg (fun a : Fin n × (Fin n→Bool)=>a.1.val) h
    · intro j hx hy
      have b:=congrFun (congrArg Prod.snd h) ⟨j,hx.trans x.property⟩
      simpa [shortCode,List.getD,hx,hy] using b)

def shortState (n : ℕ) (w : List Bool) : Option (Short n) :=
  if h:w.length<n then some ⟨w,h⟩ else none

def keep (n : ℕ) : Option (Short n)→In→Option (Short n)
  | some w,.inl b=>shortState n (w.val++[b])
  | q,.inr _=>q
  | none,.inl _=>none

theorem on_left (n : ℕ) (p : List Bool) (b : Bool) :
    keep n (shortState n p) (.inl b)=shortState n (p++[b]) := by
  by_cases h:p.length<n
  · simp [shortState,h,keep]
  · have big:¬(p++[b]).length<n:=by simp;omega
    simp [shortState,h,big,keep];omega

theorem flag_stream (n : ℕ) (x w : List Bool) :
    (encodePair (x,w)).foldl (keep n) (shortState n [])=shortState n x := by
  have left (p : List Bool) : (x.map Sum.inl).foldl (keep n) (shortState n p)=shortState n (p++x) := by
    induction x generalizing p with
    | nil=>simp
    | cons b bs ih=>simp only [List.map_cons,List.foldl_cons,on_left,ih,List.append_assoc,List.singleton_append]
  have right (q : Option (Short n)) : (w.map Sum.inr).foldl (keep n) q=q := by
    induction w generalizing q with
    | nil=>rfl
    | cons b bs ih=>cases q <;>simp [keep,ih]
  simp only [encodePair,List.foldl_append,left,right,List.nil_append]

noncomputable def override (L : Language Bool) (n : ℕ) : Option (Short n)→Keep :=
  by classical exact fun v=>v.map (fun w=>decide (w.val∈L))

private theorem agrees (L : Language Bool) (n : ℕ) (p : List Bool×List Bool) (b : Bool) :
    (override L n ((encodePair p).foldl (keep n) (shortState n []))).getD b=true ↔
      if p.1.length<n then p.1∈L else b=true := by
  classical
  rcases p with ⟨x,w⟩
  rw [flag_stream]
  by_cases h:x.length<n <;>simp [shortState,override,h]

private theorem alt_congr (j s : ℕ) (P Q : List Bool→Prop) (eqv : ∀ w,P w↔Q w) :
    Alt j s P↔Alt j s Q := by
  induction j generalizing P Q with
  | zero=>exact eqv []
  | succ j ih=>
    change (∃ y,y.length=s ∧ ¬Alt j s (fun w=>¬P (y++w))) ↔
      ∃ y,y.length=s ∧ ¬Alt j s (fun w=>¬Q (y++w))
    exact exists_congr fun y=>and_congr_right fun _=>not_congr (ih _ _ (fun w=>not_congr (eqv (y++w))))

private theorem alt_constant (j s : ℕ) (P : Prop) : Alt j s (fun _=>P)↔P := by
  classical
  induction j generalizing P with
  | zero=>rfl
  | succ j ih=>
    change (∃ y : List Bool,y.length=s ∧ ¬Alt j s (fun _=>¬P)) ↔ P
    rw [ih,not_not]
    exact ⟨fun ⟨_,_,hp⟩=>hp,fun hp=>⟨List.replicate s false,by simp,hp⟩⟩

/-- The official linear-time, fixed-alternation verifier classes are closed
under changing arbitrary answers on a bounded set of input lengths. -/
theorem finite_changes (L L' : Language Bool) (N j : ℕ) (s : ℕ→ℕ)
    (long:∀ x : List Bool,N≤x.length → (x∈L ↔ x∈L')) (source:L∈SigmaV j s) : L'∈SigmaV j s := by
  classical
  obtain ⟨R,K,⟨f,hf,c,clock⟩,game⟩:=source
  let flags:=override L' N
  let newR:Set (List Bool×List Bool):={p | (flags ((encodePair p).foldl (keep N) (shortState N []))).getD (f p)=true}
  have check:=decidable c K clock (keep N) flags (shortState N [])
  have tests (x w : List Bool) : (x,w)∈newR ↔ if x.length<N then x∈L' else (x,w)∈R := by
    change (override L' N ((encodePair (x,w)).foldl (keep N) (shortState N []))).getD (f (x,w))=true ↔ _
    have h:=agrees L' N (x,w) (f (x,w))
    by_cases small:x.length<N
    · simpa only [small,ite_true] using h
    · simpa only [small,ite_false,←hf] using h
  refine ⟨newR,K+32,check,fun x=>?_⟩
  by_cases small:x.length<N
  · exact (alt_constant j (s x.length) (x∈L')).symm.trans
      (alt_congr j (s x.length) _ _ (fun w=>(by simpa [small] using (tests x w).symm)))
  · exact (long x (by omega)).symm.trans ((game x).trans
      (alt_congr j (s x.length) _ _ (fun w=>(by simpa [small] using (tests x w).symm))))

end FiniteOverride

#print axioms FiniteOverride.finite_changes
