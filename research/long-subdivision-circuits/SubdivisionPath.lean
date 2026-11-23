import SubdivisionLayout
import PEqualNP.Outside.L_meta_575
namespace Subdivision.Layout
open Finset PEqualNP.MetaComplexity
variable {n m : ℕ} (B : Layout n m)

private theorem same_decide (p : Prop) (a b : Decidable p) :
    @decide p a = @decide p b := by rw [Subsingleton.elim a b]

private theorem head_free (e : Fin m) (i : Fin (2*B.half e)) (j : Fin m) (b : Bool) :
    B.inner e i≠B.head j b := by cases b <;> simp [head,B.notLeft,B.notRight]

private theorem singleton_false (S : Finset (Fin m)) (o : Fin m → Bool) (w : Fin n) (e : Fin m) :
    ¬ B.active S o e (fun v => decide (v=w)) := by
  classical
  unfold active
  split
  · rintro ⟨i,hi,⟨_,hl⟩|⟨_,hr⟩|⟨j,next,hj⟩⟩
    · exact B.notLeft e i e ((of_decide_eq_true hi).trans (of_decide_eq_true hl).symm)
    · exact B.notRight e i e ((of_decide_eq_true hi).trans (of_decide_eq_true hr).symm)
    · have eq := (B.inner e).injective ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
      subst j
      omega
  · rintro ⟨a,b⟩
    exact B.head_free _ _ _ _ ((of_decide_eq_true b).trans (of_decide_eq_true a).symm)

private theorem zeros (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) :
    B.outside S o e (fun _ => false)=false := by
  classical
  simp [outside,active,chain]
private theorem ones (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) (many : 2 ≤ m) :
    B.outside S o e (fun _ => true)=true := by
  classical
  let _ : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr many
  obtain ⟨j,hj⟩ := exists_ne e
  simp only [outside,decide_eq_true_eq]
  refine ⟨j,hj,?_⟩
  unfold active
  split
  · exact ⟨B.first j,rfl,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨rfl,rfl⟩

private noncomputable def move (e : Fin m) (w : Fin n) : Fin (n+2*B.half e) :=
  by classical exact if h : ∃ i, B.inner e i=w then Fin.natAdd n h.choose else Fin.castAdd _ w
private theorem move_inner (e : Fin m) (i : Fin (2*B.half e)) : B.move e (B.inner e i)=Fin.natAdd n i := by
  classical
  have h : ∃ j, B.inner e j=B.inner e i := ⟨i,rfl⟩
  simp only [move,dite_eq_left h,(B.inner e).injective h.choose_spec]
private theorem fixed (e : Fin m) (w : Fin n) (h : ∀ i, B.inner e i≠w) :
    B.move e w=Fin.castAdd _ w := by
  classical
  have hn : ¬∃ i, B.inner e i=w := by simpa using h
  simp [move,hn]
private theorem outside_move (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) (x : Assignment (n+2*B.half e)) :
    B.outside S o e (x ∘ B.move e)=B.outside S o e (fun v => x (Fin.castAdd _ v)) := by
  classical
  unfold outside
  congr 1
  apply propext
  apply exists_congr
  intro j
  apply and_congr_right
  intro je
  have hi (t) := B.fixed e (B.inner j t) (fun i => B.apart i t je.symm)
  have hl := B.fixed e (B.left j) (fun i => B.notLeft e i j)
  have hr := B.fixed e (B.right j) (fun i => B.notRight e i j)
  have hh := B.fixed e (B.head j (o j)) (fun i => B.head_free e i j (o j))
  simp [active,hi,hl,hr,hh]

theorem pay_one (S : Finset (Fin m)) (o : Fin m → Bool) (e : Fin m) (he : e∈S)
    (many : 2 ≤ m) (s : ℕ) (size : HasCircuitSize n (B.board S o) s) :
    ∃ s' b, 3*B.half e+s' ≤ s ∧ HasCircuitSize n (B.board (S.erase e) (Function.update o e b)) s' := by
  classical
  let g := B.outside S o e
  have splitBoard (x : Assignment n) : B.board S o x = (g x || decide (B.active S o e x)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [board,g,outside,Bool.or_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj⟩
      by_cases je : j=e
      · exact Or.inr (je ▸ hj)
      · exact Or.inl ⟨j,je,hj⟩
    · rintro (⟨j,_,hj⟩|hj)
      · exact ⟨j,hj⟩
      · exact ⟨e,hj⟩
  have eq : (fun x : Assignment (n+2*B.half e) => B.board S o (x ∘ B.move e)) =
      (fun x => g (fun v => x (Fin.castAdd _ v)) || decide
        (chain (x (Fin.castAdd _ (B.left e))) (x (Fin.castAdd _ (B.right e))) (fun i => x (Fin.natAdd n i)))) := by
    funext x
    rw [splitBoard]
    rw [show g (x ∘ B.move e)=g (fun v => x (Fin.castAdd _ v)) from B.outside_move S o e x]
    simp only [active,ite_eq_left he,Function.comp_def,B.move_inner,
      B.fixed e (B.left e) (fun i => B.notLeft e i e),B.fixed e (B.right e) (fun i => B.notRight e i e)]
  have up := PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs.relabel_size (B.move e) _ s size
  rw [eq] at up
  have witnesses (u : Fin n) (b : Bool) : ∃ x : Assignment n, x u=b ∧ g x=false := by
    cases b with
    | false => exact ⟨fun _ => false,rfl,B.zeros S o e⟩
    | true =>
      refine ⟨fun v => decide (v=u),by simp,?_⟩
      simp [g,outside,B.singleton_false]
  have non : ∃ x y : Assignment n, g x≠g y := by
    refine ⟨fun _ => false,fun _ => true,?_⟩
    change B.outside S o e (fun _ => false) ≠ B.outside S o e (fun _ => true)
    rw [B.zeros S o e,B.ones S o e many]
    decide
  obtain ⟨s',pay,hpend⟩ := PEqualNP.Outside.L_meta_575 n (B.half e) (B.left e) (B.right e) g (B.distinct e) (B.long e)
    non (witnesses _ false) (witnesses _ true) (witnesses _ false) (witnesses _ true) s (by
      convert up using 1
      funext x
      apply congrArg (fun b : Bool => g (fun v => x (Fin.castAdd _ v)) || b)
      exact same_decide _ _ _)
  let p : Fin (n+1) → Fin n := Fin.lastCases (B.inner e (B.first e)) id
  have back (b : Bool) (hs : HasCircuitSize (n+1) (fun x => g (fun v => x v.castSucc) ||
      (x (B.head e b).castSucc && x (Fin.last n))) s') :
      HasCircuitSize n (B.board (S.erase e) (Function.update o e b)) s' := by
    have re := PEqualNP.MetaComplexity.L575Proof.Helpers.PermInputs.relabel_size p _ s' hs
    convert re using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [board,decide_eq_true_eq,Function.comp_apply,p,Fin.lastCases_castSucc,Fin.lastCases_last,id_eq,g,outside,
      Bool.or_eq_true,Bool.and_eq_true]
    constructor
    · rintro ⟨j,hj⟩
      by_cases je : j=e
      · subst j
        exact Or.inr (by simpa [active] using hj)
      · exact Or.inl ⟨j,je,by simpa [active,je,Function.update_of_ne,Finset.mem_erase] using hj⟩
    · rintro (⟨j,je,hj⟩|hj)
      · exact ⟨j,by simpa [active,je,Function.update_of_ne,Finset.mem_erase] using hj⟩
      · exact ⟨e,by simpa [active] using hj⟩
  rcases hpend with pass|pass
  · exact ⟨s',true,pay,back true (by simpa [head] using pass)⟩
  · exact ⟨s',false,pay,back false (by simpa [head] using pass)⟩

theorem reduce_all (S : Finset (Fin m)) (many : 2 ≤ m) (o : Fin m → Bool) (s : ℕ)
    (size : HasCircuitSize n (B.board S o) s) :
    ∃ s' p, (∑ e∈S, 3*B.half e)+s' ≤ s ∧ HasCircuitSize n (B.board ∅ p) s' := by
  classical
  induction S using Finset.induction_on generalizing o s with
  | empty => exact ⟨s,o,by simp,size⟩
  | @insert e S he ih =>
    obtain ⟨w,b,pay,pass⟩ := B.pay_one (insert e S) o e (by simp) many s size
    rw [Finset.erase_insert he] at pass
    obtain ⟨z,p,saving,cert⟩ := ih _ _ pass
    refine ⟨z,p,?_,cert⟩
    rw [Finset.sum_insert he]
    omega
end Subdivision.Layout
#print axioms Subdivision.Layout.pay_one
#print axioms Subdivision.Layout.reduce_all
