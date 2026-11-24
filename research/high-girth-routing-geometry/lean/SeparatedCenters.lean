import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

namespace SparsePermanent.SeparatedCenters
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def near : ℕ→V→Finset V := by
  classical
  exact fun r=>Nat.rec (fun v=>{v}) (fun _ previous v=>
    insert v ((univ.filter (G.Adj v)).biUnion previous)) r

private def volume : ℕ→ℕ | 0=>1 | r+1=>4*volume r+1

private theorem volume_eq (r : ℕ) : 3*volume r+1=4^(r+1) := by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [pow_succ,←ih];simp [volume];ring

open Classical in
private theorem near_card (degree : ∀ v : V,(univ.filter (G.Adj v)).card≤4) (r : ℕ) (v : V) :
    (near G r v).card≤volume r := by
  classical
  induction r generalizing v with
  | zero=>simp [near,volume]
  | succ r ih=>
    change (insert v ((univ.filter (G.Adj v)).biUnion (near G r))).card≤_
    calc
      _ ≤ ((univ.filter (G.Adj v)).biUnion (near G r)).card+1 := card_insert_le ..
      _ ≤ (∑ x∈univ.filter (G.Adj v), (near G r x).card)+1 := Nat.add_le_add_right card_biUnion_le _
      _ ≤ (∑ _x∈univ.filter (G.Adj v),volume r)+1 := by gcongr with x hx;exact ih x
      _ ≤ 4*volume r+1 := by simp only [sum_const,nsmul_eq_mul];gcongr;exact degree _
      _ = _ := rfl

private theorem center_mem (v : V) (r : ℕ) : v∈near G r v := by cases r <;> simp [near]

private theorem walk_mem {a b : V} (p : G.Walk a b) (r : ℕ) (len : p.length≤r) : b∈near G r a := by
  classical
  induction p generalizing r with
  | nil=>exact center_mem G _ _
  | @cons a b c e q ih=>
    cases r with
    | zero=>simp at len
    | succ r=>
      apply mem_insert_of_mem
      exact mem_biUnion.mpr ⟨b,mem_filter.mpr ⟨mem_univ _,e⟩,ih r (by simpa using len)⟩

open Classical in
/-- Greedy packing of m centers at mutual distance greater than d in a
four-neighbor graph. The n > m·4^(d+1) condition is sufficient. -/
theorem exists_far (connected : G.Connected)
    (degree : ∀ v : V,(univ.filter (G.Adj v)).card≤4) (m d : ℕ)
    (space : m*4^(d+1)<Fintype.card V) :
    ∃ center : Fin m→V,∀ i j,i≠j→d<G.dist (center i) (center j) := by
  classical
  have select (t : ℕ) (small:t≤m) : ∃ S : Finset V,S.card=t ∧
      (∀ a∈S,∀ b∈S,a≠b→d<G.dist a b) := by
    induction t with
    | zero=>exact ⟨∅,by simp,by simp⟩
    | succ t ih=>
      obtain ⟨S,size,far⟩:=ih (by omega)
      let F:=S.biUnion (near G d)
      have cf:F.card≤t*volume d := by
        calc
          _ ≤ ∑ a∈S,(near G d a).card := card_biUnion_le
          _ ≤ ∑ _a∈S,volume d := sum_le_sum (fun a _=>near_card G degree d a)
          _ = _ := by simp [size]
      have enough : F.card<Fintype.card V := cf.trans_lt ((Nat.mul_le_mul (by omega : t≤m)
        (by have h:=volume_eq d;omega : volume d≤4^(d+1))).trans_lt space)
      obtain ⟨v,_,fresh⟩:=exists_mem_notMem_of_card_lt_card (show F.card<(univ : Finset V).card by simpa using enough)
      have remote (a : V) (old:a∈S) : d<G.dist a v := by
        by_contra! no
        obtain ⟨p,eq⟩:=connected.exists_walk_length_eq_dist a v
        exact fresh (mem_biUnion.mpr ⟨a,old,walk_mem G p d (eq.trans_le no)⟩)
      have new : v∉S := by intro hv;have := remote v hv;simp_all
      refine ⟨insert v S,by simp [new,size],?_⟩
      intro a ha b hb diff
      rcases mem_insert.mp ha with ae|oldA
      · have oldB: b∈S := (mem_insert.mp hb).resolve_left (fun be=>diff (ae.trans be.symm))
        rw [ae,G.dist_comm]
        exact remote _ oldB
      · rcases mem_insert.mp hb with be|oldB
        · rw [be];exact remote _ oldA
        · exact far _ oldA _ oldB diff
  obtain ⟨S,size,far⟩:=select m le_rfl
  let e : Fin m≃S:=Fintype.equivOfCardEq (by simp [size])
  exact ⟨fun i=>(e i).val,fun i j ne=>far _ (e i).prop _ (e j).prop (fun h=>ne (e.injective (Subtype.ext h)))⟩

end SparsePermanent.SeparatedCenters
#print axioms SparsePermanent.SeparatedCenters.exists_far
