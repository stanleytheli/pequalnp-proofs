import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! A common integral affine chart for all pure binary edge markings is
preserved by a tight-cut fiber product. The chart of the product simply
concatenates the two fixed child charts. Marker tests may describe a group
of edges so the same result also covers Cartesian products. -/
namespace PositivePermanent.UniversalReadout
open Finset
variable {E A B I J K : Type*} [DecidableEq E] [Fintype I] [Fintype J]

/-- Which color is present in a physical edge set. -/
def hits (s:Finset E) (X:E→Prop) : Prop := ∃e∈s,X e

private theorem hits_union (a b : Finset E) (X : E→Prop) : hits (a∪b) X ↔ hits a X ∨ hits b X := by
  simp only [hits,mem_union]
  aesop

noncomputable def bit (P:Prop) : ℤ := by classical exact if P then 1 else 0

def Pure (s:A→Finset E) (X Y:E→Prop) : Prop := ∀a,hits (s a) X ↔ ¬hits (s a) Y

def Readable (v:A→I→ℤ) (f:A→ℤ) : Prop := ∃w:I→ℤ,∃c:ℤ,∀a,f a=c+∑i,w i*v a i

def Universal (s:A→Finset E) (v:A→I→ℤ) : Prop := ∀X Y,Pure s X Y→Readable v (fun a=>bit (hits (s a) X))

def portMark (P:K→E→Prop) (Q:K→Prop) (e:E) : Prop:=∃k,P k e ∧ Q k

private theorem transfer {rows:A→Finset E} {index:A→K} {P:K→E→Prop}
    (ports:∀a k,hits (rows a) (P k) ↔ index a=k) (Q:K→Prop) (a:A) :
    hits (rows a) (portMark P Q) ↔ Q (index a) := by
  constructor
  · rintro ⟨e,he,k,hk,hq⟩
    exact (ports a k).mp ⟨e,he,hk⟩ ▸ hq
  · intro h
    obtain ⟨e,he,hp⟩:=(ports a (index a)).mpr rfl
    exact ⟨e,he,index a,hp,h⟩

private theorem port_read {rows:A→Finset E} {v:A→I→ℤ} {index:A→K} {P:K→E→Prop}
    (u:Universal rows v) (ports:∀a k,hits (rows a) (P k) ↔ index a=k) (Q:K→Prop) :
    Readable v (fun a=>bit (Q (index a))) := by
  classical
  have exclusive : Pure rows (portMark P Q) (portMark P (fun k=>¬Q k)) := by
    intro a;rw [transfer ports,transfer ports];simp
  obtain ⟨w,c,eq⟩:=u _ _ exclusive
  exact ⟨w,c,fun a=>by simpa only [transfer ports] using eq a⟩

private theorem attach {rows:A→Finset E} {index:A→K} {P:K→E→Prop}
    (ports:∀a k,hits (rows a) (P k) ↔ index a=k) (remote:K→Finset E) (X:E→Prop) (a:A) :
    hits (rows a) (fun e=>X e ∨ portMark P (fun k=>hits (remote k) X) e) ↔ hits (rows a∪remote (index a)) X := by
  rw [hits_union]
  have alt : ∀Q:E→Prop,hits (rows a) (fun e=>X e∨Q e) ↔ hits (rows a) X∨hits (rows a) Q := by
    intro Q;unfold hits;aesop
  rw [alt,transfer ports]

private theorem extended_read {rows:A→Finset E} {v:A→I→ℤ} {index:A→K} {P:K→E→Prop}
    (u:Universal rows v) (ports:∀a k,hits (rows a) (P k) ↔ index a=k) (remote:K→Finset E) (X Y:E→Prop)
    (pure:Pure (fun a=>rows a∪remote (index a)) X Y) :
    Readable v (fun a=>bit (hits (rows a∪remote (index a)) X)) := by
  let aug (Z:E→Prop) (e:E):=Z e ∨ portMark P (fun k=>hits (remote k) Z) e
  have good : Pure rows (aug X) (aug Y) := by
    intro a
    change hits _ (fun e=>_ ∨ _) ↔ ¬hits _ (fun e=>_ ∨ _)
    rw [attach ports,attach ports];exact pure _
  obtain ⟨w,c,eq⟩:=u _ _ good
  refine ⟨w,c,fun a=>?_⟩
  have h:=eq a
  change bit (hits _ (fun e=>X e ∨ portMark P (fun k=>hits (remote k) X) e))=_ at h
  rw [attach ports] at h;exact h

private theorem sum_bit (P Q U V:Prop) (ones:(P∨Q)↔(U∨V)) (zeros:(¬P∨¬Q)↔(¬U∨¬V)) :
    bit P+bit Q=bit U+bit V := by
  classical
  by_cases p:P <;> by_cases q:Q <;> by_cases u:U <;> by_cases v:V <;> simp_all [bit]

private theorem rectangle (a b c d:Finset E) (X Y:E→Prop)
    (pure : ∀p∈[a,c],∀q∈[b,d],hits (p∪q) X ↔ ¬hits (p∪q) Y) :
    bit (hits (a∪b) X)+bit (hits (c∪d) X)=bit (hits (a∪d) X)+bit (hits (c∪b) X) := by
  classical
  apply sum_bit
  · simp only [hits_union];tauto
  · have inverse (p) (hp:p∈[a,c]) (q) (hq:q∈[b,d]) : (¬hits (p∪q) X) ↔ hits (p∪q) Y := by
      rw [pure p hp q hq];simp
    rw [inverse a (by simp) b (by simp),inverse c (by simp) d (by simp),
      inverse a (by simp) d (by simp),inverse c (by simp) b (by simp)]
    simp only [hits_union];tauto

abbrev Fiber (i:A→K) (j:B→K) := {z:A×B // i z.1=j z.2}

def join (sa:A→Finset E) (sb:B→Finset E) {i:A→K} {j:B→K} (p:Fiber i j) := sa p.val.1∪sb p.val.2

def chart (x:A→I→ℤ) (y:B→J→ℤ) {i:A→K} {j:B→K} (p:Fiber i j) : I⊕J→ℤ := Sum.elim (x p.val.1) (y p.val.2)

/-- The same concatenated integer chart works for every pure edge-color
partition after gluing two factors by a common categorical marker. -/
theorem glue (sa:A→Finset E) (sb:B→Finset E) (x:A→I→ℤ) (y:B→J→ℤ) (i:A→K) (j:B→K)
    (ua:Universal sa x) (ub:Universal sb y)
    (pa pb:K→E→Prop) (ap:∀a k,hits (sa a) (pa k) ↔ i a=k) (bp:∀b k,hits (sb b) (pb k) ↔ j b=k)
    (ra:K→A) (rb:K→B) (aa:∀k,i (ra k)=k) (bb:∀k,j (rb k)=k) :
    Universal (join sa sb (i:=i) (j:=j)) (chart x y) := by
  classical
  intro X Y pure
  have atPair (a:A) (b:B) (eq:i a=j b) : hits (sa a∪sb b) X ↔ ¬hits (sa a∪sb b) Y :=
    pure ⟨(a,b),eq⟩
  have la:=extended_read ua ap (fun k=>sb (rb k)) X Y (fun a=>atPair _ _ (bb _).symm)
  have lb:=extended_read ub bp (fun k=>sa (ra k)) X Y (fun b=>by simpa only [union_comm (sb b)] using atPair (ra (j b)) b (aa _))
  have port:=port_read ua ap (fun k=>hits (sa (ra k)∪sb (rb k)) X)
  obtain ⟨wl,cl,hl⟩:=la
  obtain ⟨wr,cr,hr⟩:=lb
  obtain ⟨wm,cm,hm⟩:=port
  refine ⟨Sum.elim (fun z=>wl z-wm z) wr,cl+cr-cm,?_⟩
  rintro ⟨⟨a,b⟩,same⟩
  let k:=i a
  have ar : i (ra k)=i a:=aa k
  have br : j (rb k)=i a:=bb k
  have rect:=rectangle (sa a) (sb b) (sa (ra k)) (sb (rb k)) X Y (by
    intro p hp q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp hq
    rcases hp with rfl|rfl <;> rcases hq with rfl|rfl
    · exact atPair _ _ same
    · exact atPair _ _ br.symm
    · exact atPair _ _ (ar.trans same)
    · exact atPair _ _ (ar.trans br.symm))
  have l:=hl a
  have r:=hr b
  have m:=hm a
  dsimp only at same l r m
  rw [←same,union_comm (sb b)] at r
  dsimp only [k] at rect
  change bit (hits (sa a∪sb b) X)=_
  simp only [chart,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sub_mul,sum_sub_distrib]
  omega

end PositivePermanent.UniversalReadout
#print axioms PositivePermanent.UniversalReadout.glue
