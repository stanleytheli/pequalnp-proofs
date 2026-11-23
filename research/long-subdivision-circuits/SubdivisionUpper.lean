import SubdivisionLayout
import PEqualNP.Defs
namespace Subdivision.Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Expr (n : ℕ) where
  | var (v : Fin n)
  | bin (isAnd : Bool) (a b : Expr n)

def Expr.eval {n} (x : Fin n→Bool) : Expr n→Bool
  | .var i=>x i
  | .bin op a b=>if op then a.eval x && b.eval x else a.eval x || b.eval x

def Expr.leaves {n} : Expr n→ℕ
  | .var _=>1
  | .bin _ a b=>a.leaves+b.leaves

def Expr.nodes {n} : Expr n→ℕ
  | .var _=>0
  | .bin _ a b=>a.nodes+b.nodes+1

theorem Expr.count {n} (f : Expr n) : f.nodes+1=f.leaves := by
  induction f with | var=>rfl | bin op a b ha hb=>simp only [nodes,leaves];omega

def Expr.join {n} (a b : Expr n) := Expr.bin false a b
def Expr.meet {n} (a b : Expr n) := Expr.bin true a b

private def op (b : Bool) : GateOp := if b then .and else .or

def Expr.code {n} : Expr n→ℕ→Circuit
  | .var v,_=>⟨[],v.val⟩
  | .bin g a b,p=>
    let L:=a.code p
    let R:=b.code (p+a.nodes)
    ⟨L.gates++R.gates++[⟨op g,[L.output,R.output]⟩],p+a.nodes+b.nodes⟩

private def tick (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
private def run (gs : List Gate) (w : List Bool) := gs.foldl tick w

private theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil=>simp [run]
  | cons g gs ih=>change (run gs (tick w g)).length=_;rw [ih];simp [tick];omega

private theorem kept (gs : List Gate) (w : List Bool) (i : ℕ) (hi:i<w.length) : (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil=>rfl
  | cons g gs ih=>
    change (run gs (tick w g)).getD i false=_
    rw [ih (tick w g) (by simp [tick];omega)]
    simp [tick,List.getD,List.getElem?_append_left hi]

theorem Expr.code_size {n} (f : Expr n) (p : ℕ) : (f.code p).gates.length=f.nodes := by
  induction f generalizing p with
  | var=>rfl
  | bin g a b la lb=>simp [code,nodes,la,lb,Nat.add_assoc]

theorem Expr.fanin {n} (f : Expr n) (p : ℕ) : FanInTwo (f.code p) := by
  induction f generalizing p with
  | var=>simp [code,FanInTwo]
  | bin g a b la lb=>
    intro h mem
    simp only [code,List.mem_append,List.mem_singleton] at mem
    rcases mem with (h|h)|rfl
    · exact la p _ h
    · exact lb (p+a.nodes) _ h
    · cases g <;>simp [op]

theorem Expr.output_lt {n} (f : Expr n) (p : ℕ) (hp:n≤p) : (f.code p).output<p+f.nodes := by
  cases f with
  | var v=>exact v.isLt.trans_le hp
  | bin=>simp [code,nodes];omega

theorem Expr.emits {n} (f : Expr n) (x : Fin n→Bool) (w : List Bool) (len:n≤w.length)
    (raw:∀ i:Fin n,w.getD i.val false=x i) :
    (run (f.code w.length).gates w).getD (f.code w.length).output false=f.eval x := by
  induction f generalizing w with
  | var i=>exact raw i
  | bin g a b la lb=>
    let L:=a.code w.length
    let left:=run L.gates w
    have lenL:left.length=w.length+a.nodes:=by rw [run_len];simp [L,Expr.code_size]
    let R:=b.code left.length
    let right:=run R.gates left
    have lenR:right.length=w.length+a.nodes+b.nodes:=by rw [run_len,b.code_size,lenL]
    have leftOK:left.getD L.output false=a.eval x:=la w len raw
    have rightOK:right.getD R.output false=b.eval x:=lb left (by omega)
      (fun i=>(kept L.gates w i.val (i.isLt.trans_le len)).trans (raw i))
    have was:L.output<left.length:=by rw [lenL];exact a.output_lt _ len
    have leftStill:right.getD L.output false=a.eval x:=(kept R.gates left L.output was).trans leftOK
    have cat (u v : List Gate) (w' : List Bool) : run (u++v) w'=run v (run u w'):=List.foldl_append
    simp only [code,cat]
    rw [←lenL]
    change (tick right ⟨op g,[L.output,R.output]⟩).getD (left.length+b.nodes) false=_
    have length:right.length=left.length+b.nodes:=by omega
    rw [←length]
    simp only [List.getD] at leftStill rightOK
    cases g <;>simp [tick,List.getD,op,GateOp.eval,leftStill,rightOK,Expr.eval]

theorem Expr.physical {n} (f : Expr n) : HasCircuitSize n f.eval f.nodes := by
  refine ⟨f.code n,f.fanin n,(f.code_size n).le,fun x=>?_⟩
  have emit:=f.emits x (List.ofFn x) (by simp) (fun i=>by simp [List.getD])
  change (run (f.code n).gates (List.ofFn x)).getD (f.code n).output false=f.eval x
  simpa only [List.length_ofFn] using emit

end Subdivision.Upper


namespace Subdivision.Upper

private theorem or_finite {n : ℕ} {I : Type*} (S : Finset I) (g : I→Expr n)
    (hs : S.Nonempty) : ∃ f : Expr n,
      (∀ x, f.eval x=true ↔ ∃ i∈S, (g i).eval x=true) ∧ f.leaves=∑ i∈S, (g i).leaves := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert i S hi ih =>
    by_cases h : S.Nonempty
    · obtain ⟨z,hz,hl⟩ := ih h
      refine ⟨Expr.join (g i) z,fun x => ?_,?_⟩
      · simp [Expr.join,Expr.eval,hz]
      · simp [Expr.join,Expr.leaves,hl,hi]
    · have eq : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst S
      exact ⟨g i,by simp,by simp⟩

/-- The standard construction assigning each edge once to the star of its chosen endpoint. -/
theorem oriented_upper {n : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (center other : I → Fin n) :
    ∃ f : Expr n, (∀ x, f.eval x=true ↔ ∃ i, x (center i)=true ∧ x (other i)=true) ∧
      f.leaves = Fintype.card I + (Finset.univ.image center).card := by
  classical
  let T := (Finset.univ : Finset I).image center
  let fibre (v : Fin n) := Finset.univ.filter (fun e => center e=v)
  have haveStar (v : Fin n) (hv : v∈T) : ∃ f : Expr n,
      (∀ x, f.eval x=true ↔ x v=true ∧ ∃ i∈fibre v, x (other i)=true) ∧
      f.leaves=1+(fibre v).card := by
    obtain ⟨p,hp,hc⟩ := Finset.mem_image.mp hv
    have hnon : (fibre v).Nonempty := ⟨p,by simp [fibre,hc]⟩
    obtain ⟨z,hz,hl⟩ := or_finite (fibre v) (fun i => Expr.var (other i)) hnon
    refine ⟨Expr.meet (.var v) z,fun x => ?_,?_⟩
    · simp [Expr.meet,Expr.eval,hz]
    · simp [Expr.meet,Expr.leaves,hl]
  let star (v : Fin n) := if hv : v∈T then (haveStar v hv).choose else Expr.var v
  have spec (v : Fin n) (hv : v∈T) := (haveStar v hv).choose_spec
  have hnT : T.Nonempty := Finset.univ_nonempty.image center
  obtain ⟨g,hg,hl⟩ := or_finite T star hnT
  refine ⟨g,fun x => ?_,?_⟩
  · rw [hg]
    constructor
    · rintro ⟨v,hv,h⟩
      simp only [star,dite_eq_left hv] at h
      obtain ⟨xv,e,he,xe⟩ := ((spec v hv).1 x).mp h
      have eq : center e=v := by simpa [fibre] using he
      exact ⟨e,eq ▸ xv,xe⟩
    · rintro ⟨e,hc,ho⟩
      have hv : center e∈T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact ⟨center e,hv,by
        simp only [star,dite_eq_left hv]
        exact ((spec _ hv).1 x).mpr ⟨hc,e,by simp [fibre],ho⟩⟩
  · rw [hl,Finset.sum_congr rfl fun v hv => show (star v).leaves = 1+(fibre v).card by
        simpa [star,hv] using (spec v hv).2, Finset.sum_add_distrib]
    have mass : ∑ v∈T, (fibre v).card = Fintype.card I := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (s:=Finset.univ) (t:=T) (f:=center)
        (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp [mass,T,Nat.add_comm]

end Subdivision.Upper

namespace Subdivision.Layout
open PEqualNP.MetaComplexity Finset
variable {n m : ℕ} (B : Layout n m)

private def vertex (e : Fin m) (j : ℕ) : Fin n :=
  if j=0 then B.left e else if h:j≤2*B.half e then B.inner e ⟨j-1,by have:=B.long e;omega⟩ else B.right e

private theorem vertex_left (e : Fin m) : B.vertex e 0=B.left e:=by simp [vertex]
private theorem vertex_right (e : Fin m) : B.vertex e (2*B.half e+1)=B.right e:=by simp [vertex]
private theorem vertex_inner (e : Fin m) (j : Fin (2*B.half e)) : B.vertex e (j.val+1)=B.inner e j := by
  have bound:j.val+1≤2*B.half e:=j.isLt
  simp [vertex,bound]

private abbrev Segments := Σ e : Fin m, Fin (2*B.half e+1)
private abbrev Middle := Σ e : Fin m, Fin (B.half e)

private theorem path_edges (e : Fin m) (x : Assignment n) :
    chain (x (B.left e)) (x (B.right e)) (fun i=>x (B.inner e i)) ↔
       ∃ p : Fin (2*B.half e+1),x (B.vertex e p.val)=true ∧ x (B.vertex e (p.val+1))=true := by
  constructor
  · rintro ⟨i,on,⟨front,left⟩|⟨last,right⟩|⟨j,next,more⟩⟩
    · refine ⟨⟨0,by omega⟩,?_,?_⟩
      · simpa only [vertex_left] using left
      · have h:=B.vertex_inner e i
        rw [front] at h
        simpa only [h] using on
    · refine ⟨⟨i.val+1,by omega⟩,?_,?_⟩
      · simpa only [vertex_inner] using on
      · change x (B.vertex e ((i.val+1)+1))=true
        rwa [last,vertex_right]
    · refine ⟨⟨i.val+1,by omega⟩,?_,?_⟩
      · simpa only [vertex_inner] using on
      · change x (B.vertex e ((i.val+1)+1))=true
        rw [←next,B.vertex_inner]
        exact more
  · rintro ⟨p,left,right⟩
    have h:=B.long e
    by_cases low:p.val=0
    · let i : Fin (2*B.half e):=⟨0,by omega⟩
      refine ⟨i,?_,Or.inl ⟨rfl,?_⟩⟩
      · have v:=B.vertex_inner e i
        change B.vertex e (0+1)=_ at v
        simpa only [low,v] using right
      · simpa only [low,vertex_left] using left
    · let i : Fin (2*B.half e):=⟨p.val-1,by have:=p.isLt;omega⟩
      have ip:i.val+1=p.val:=by dsimp [i];omega
      have on:x (B.inner e i)=true:=by rw [←B.vertex_inner,ip];exact left
      by_cases last:p.val=2*B.half e
      · refine ⟨i,on,Or.inr (Or.inl ⟨ip.trans last,?_⟩)⟩
        simpa only [last,vertex_right] using right
      · let j : Fin (2*B.half e):=⟨p.val,by have:=p.isLt;omega⟩
        refine ⟨i,on,Or.inr (Or.inr ⟨j,ip.symm,?_⟩)⟩
        change x (B.inner e j)=true
        rw [←B.vertex_inner]
        exact right

private def isCenterEdge (T : Finset (Fin n)) (e : Fin m) (j : ℕ) : Prop :=
  if B.left e∈T then j % 2=0 else j % 2=1

private noncomputable def center (T : Finset (Fin n)) (edge : B.Segments) : Fin n := by
  classical exact B.vertex edge.1 (if B.isCenterEdge T edge.1 edge.2.val then edge.2.val else edge.2.val+1)
private noncomputable def partner (T : Finset (Fin n)) (edge : B.Segments) : Fin n := by
  classical exact B.vertex edge.1 (if B.isCenterEdge T edge.1 edge.2.val then edge.2.val+1 else edge.2.val)

private def middle (T : Finset (Fin n)) (j : B.Middle) : Fin n :=
  B.vertex j.1 (if B.left j.1∈T then 2*(j.2.val+1) else 2*j.2.val+1)

private theorem covered (T : Finset (Fin n)) (covers:∀ e,B.left e∈T ∨ B.right e∈T) (edge : B.Segments) :
    B.center T edge∈T∪Finset.univ.image (B.middle T) := by
  classical
  obtain ⟨e,j⟩:=edge
  have hi:=j.isLt
  by_cases le:B.left e∈T
  · let u:=if j.val % 2=0 then j.val else j.val+1
    have center:B.center T ⟨e,j⟩=B.vertex e u:=by simp [Subdivision.Layout.center,isCenterEdge,le,u]
    rw [center]
    have even:u % 2=0:=by dsimp [u];split <;>omega
    have fit:u≤2*B.half e:=by dsimp [u];split <;>omega
    by_cases low:u=0
    · exact Finset.mem_union_left _ (by rwa [low,vertex_left])
    · let i : Fin (B.half e):=⟨u/2-1,by omega⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨⟨e,i⟩,Finset.mem_univ _,?_⟩
      have val:2*(i.val+1)=u:=by dsimp [i];omega
      simp [middle,le,val]
  · have right:= (covers e).resolve_left le
    let u:=if j.val % 2=1 then j.val else j.val+1
    have center:B.center T ⟨e,j⟩=B.vertex e u:=by simp [Subdivision.Layout.center,isCenterEdge,le,u]
    rw [center]
    have odd:u % 2=1:=by dsimp [u];split <;>omega
    have fit:u≤2*B.half e+1:=by dsimp [u];split <;>omega
    by_cases last:u=2*B.half e+1
    · exact Finset.mem_union_left _ (by rwa [last,vertex_right])
    · let i : Fin (B.half e):=⟨u/2,by omega⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨⟨e,i⟩,Finset.mem_univ _,?_⟩
      have val:2*i.val+1=u:=by dsimp [i];omega
      simp [middle,le,val]

private theorem endpoints (T : Finset (Fin n)) (o : Fin m→Bool) (x : Assignment n) :
    B.board Finset.univ o x=true ↔ ∃ j : B.Segments,x (B.center T j)=true ∧ x (B.partner T j)=true := by
  classical
  simp only [board,decide_eq_true_eq,active,Finset.mem_univ,ite_true,B.path_edges]
  constructor
  · rintro ⟨e,j,left,right⟩
    refine ⟨⟨e,j⟩,?_⟩
    by_cases h:B.isCenterEdge T e j.val <;>simp [center,partner,h,left,right]
  · rintro ⟨⟨e,j⟩,given⟩
    refine ⟨e,j,?_⟩
    by_cases h:B.isCenterEdge T e j.val <;>simpa [center,partner,h,and_comm] using given

theorem circuit_upper (T : Finset (Fin n)) (covers:∀ e,B.left e∈T ∨ B.right e∈T)
    (many : 0 < m) (o : Fin m→Bool) :
    HasCircuitSize n (B.board Finset.univ o) (3*(∑e,B.half e)+m+T.card-1) := by
  classical
  let : Nonempty B.Segments:=⟨⟨⟨0,many⟩,⟨0,by omega⟩⟩⟩
  obtain ⟨f,eval,cost⟩:=Subdivision.Upper.oriented_upper (B.center T) (B.partner T)
  have fn : f.eval=B.board Finset.univ o := by
    funext x
    exact Bool.eq_iff_iff.mpr ((eval x).trans (B.endpoints T o x).symm)
  have sub : Finset.univ.image (B.center T) ⊆ T∪Finset.univ.image (B.middle T) := by
    rintro v hv
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hv
    exact B.covered T covers j
  have mc : Fintype.card B.Middle=∑e,B.half e:=by simp [Middle,Fintype.card_sigma]
  have sc : Fintype.card B.Segments=2*(∑e,B.half e)+m:=by
    simp [Segments,Fintype.card_sigma,Finset.sum_add_distrib,Finset.mul_sum]
  have middle_max: (Finset.univ.image (B.middle T)).card≤∑e,B.half e:=by
    simpa only [Finset.card_univ,mc] using Finset.card_image_le (s:=Finset.univ) (f:=B.middle T)
  have size:=((Finset.card_le_card sub).trans (Finset.card_union_le _ _)).trans (Nat.add_le_add_left middle_max T.card)
  obtain ⟨C,fan,small,correct⟩:=f.physical
  rw [fn] at correct
  refine ⟨C,fan,?_,correct⟩
  have nodes:=f.count
  rw [sc] at cost
  omega

end Subdivision.Layout

#print axioms Subdivision.Layout.circuit_upper
