import GirthForest

namespace SparsePermanent.DirectedGrowth
open Finset BinaryWords
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closed ball for a single direction, including all shorter walks. -/
noncomputable def oneWay (D : V→V→Prop) (r : ℕ) (a : V) : Finset V := by
  classical exact univ.filter (fun b=>∃j≤r,Route D ∅ a b j)

private theorem in_oneWay (D : V→V→Prop) (r : ℕ) (a b : V) :
    b∈oneWay D r a ↔ ∃j≤r,Route D ∅ a b j := by classical simp [oneWay]

open Classical in
private theorem volume_oneWay (D : V→V→Prop) (degree : ∀x,(univ.filter (D x)).card≤2)
    (r : ℕ) (a : V) : (oneWay D r a).card+1≤2^(r+1) := by
  classical
  induction r with
  | zero=>
    have eq:oneWay D 0 a={a}:=by
      ext b
      rw [in_oneWay,mem_singleton]
      constructor
      · rintro ⟨j,hj,p⟩
        have zero:j=0:=by omega
        subst j;cases p;rfl
      · rintro rfl;exact ⟨0,le_rfl,.nil (by simp)⟩
    simp [eq]
  | succ r ih=>
    let B:=oneWay D r a
    let N (x:V):=univ.filter (D x)
    have sub : oneWay D (r+1) a⊆insert a (B.biUnion N) := by
      intro b hb
      obtain ⟨j,hj,walk⟩:=(in_oneWay ..).mp hb
      cases walk with
      | nil=>exact mem_insert_self ..
      | @snoc x y j prev edge _=>
        exact mem_insert_of_mem (mem_biUnion.mpr ⟨x,(in_oneWay ..).mpr ⟨j,by omega,prev⟩,
          mem_filter.mpr ⟨mem_univ _,edge⟩⟩)
    have bound:(B.biUnion N).card≤B.card*2 := by
      calc
        _ ≤ ∑x∈B,(N x).card := card_biUnion_le
        _ ≤ ∑_x∈B,2 := sum_le_sum (fun x _=>degree x)
        _ = _ := by simp
    have inc:=(card_le_card sub).trans (card_insert_le ..)
    change B.card+1≤2^(r+1) at ih
    rw [pow_succ 2 (r+1)]
    omega

/-- Outgoing and incoming directed balls share the center. Membership is
symmetric even when the original relation itself is asymmetric. -/
noncomputable def twoWays (D : V→V→Prop) (r : ℕ) (a : V) : Finset V :=
  oneWay D r a∪oneWay (fun x y=>D y x) r a

private theorem symmetric_twoWays (D : V→V→Prop) (r : ℕ) (a b : V) (h:b∈twoWays D r a) :
    a∈twoWays D r b := by
  rcases mem_union.mp h with f|rev
  · obtain ⟨t,ht,w⟩:=(in_oneWay ..).mp f
    exact mem_union_right _ ((in_oneWay ..).mpr ⟨t,ht,w.reverse⟩)
  · obtain ⟨t,ht,w⟩:=(in_oneWay ..).mp rev
    exact mem_union_left _ ((in_oneWay ..).mpr ⟨t,ht,w.reverse⟩)

private theorem pack_boxes (B : V→Finset V) (reflexive : ∀v,v∈B v)
    (symmetric : ∀x y,y∈B x→x∈B y) (h m : ℕ) (volume : ∀v,(B v).card≤h)
    (space : m*(h*h)<Fintype.card V) :
    ∃ center : Fin m→V,∀i j,i≠j→Disjoint (B (center i)) (B (center j)) := by
  classical
  have choose (t:ℕ) (small:t≤m) : ∃S : Finset V,S.card=t ∧ ∀a∈S,∀b∈S,a≠b→Disjoint (B a) (B b) := by
    induction t with
    | zero=>exact ⟨∅,by simp,by simp⟩
    | succ t ih=>
      obtain ⟨S,num,old⟩:=ih (by omega)
      let U:=S.biUnion B
      let F:=U.biUnion B
      have cost (T:Finset V) : (T.biUnion B).card≤T.card*h := by
        calc
          _ ≤ ∑x∈T,(B x).card := card_biUnion_le
          _ ≤ ∑_x∈T,h := sum_le_sum (fun x _=>volume x)
          _ = _ := by simp
      have cf:F.card≤m*(h*h):=calc
        _ ≤ U.card*h := cost U
        _ ≤ (S.card*h)*h := Nat.mul_le_mul_right _ (cost S)
        _ ≤ m*(h*h) := by rw [num,Nat.mul_assoc];gcongr;omega
      obtain ⟨v,_,free⟩:=exists_mem_notMem_of_card_lt_card (show F.card<(univ : Finset V).card by simpa using cf.trans_lt space)
      have apart (a:V) (ha:a∈S) : Disjoint (B a) (B v) := by
        apply disjoint_left.mpr
        intro x xa xv
        exact free (mem_biUnion.mpr ⟨x,mem_biUnion.mpr ⟨a,ha,xa⟩,symmetric v x xv⟩)
      have fresh:v∉S:=fun hv=>disjoint_left.mp (apart v hv) (reflexive v) (reflexive v)
      refine ⟨insert v S,by simp [fresh,num],?_⟩
      intro a ha b hb ne
      rcases mem_insert.mp ha with rfl|inA
      · exact (apart b ((mem_insert.mp hb).resolve_left (Ne.symm ne))).symm
      · rcases mem_insert.mp hb with rfl|inB
        · exact apart a inA
        · exact old a inA b inB ne
  obtain ⟨S,card,good⟩:=choose m le_rfl
  let e:Fin m≃S:=Fintype.equivOfCardEq (by simp [card])
  exact ⟨fun i=>(e i).val,fun i j ne=>good _ (e i).prop _ (e j).prop (fun h=>ne (e.injective (Subtype.ext h)))⟩

open Classical in
/-- Directed packing uses m·2^(2r+4) vertices, even when the ordinary
four-neighbor distance ball of radius 2r may be considerably larger. -/
theorem pack_twoWays (D : V→V→Prop) (outD : ∀x,(univ.filter (D x)).card≤2)
    (inD : ∀x,(univ.filter (fun y=>D y x)).card≤2) (m r : ℕ) (space : m*2^(2*r+4)<Fintype.card V) :
    ∃ center : Fin m→V,∀i j,i≠j→Disjoint (twoWays D r (center i)) (twoWays D r (center j)) := by
  classical
  apply pack_boxes _ (fun v=>mem_union_left _ ((in_oneWay ..).mpr ⟨0,Nat.zero_le _,.nil (by simp)⟩)) (symmetric_twoWays D r) (2^(r+2)) m
  · intro a
    have f:=volume_oneWay D outD r a
    have b:=volume_oneWay (fun x y=>D y x) inD r a
    have u:=card_union_le (oneWay D r a) (oneWay (fun x y=>D y x) r a)
    rw [pow_succ 2 (r+1)]
    omega
  · simpa only [←pow_add,show r+2+(r+2)=2*r+4 by omega] using space

end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.pack_twoWays
