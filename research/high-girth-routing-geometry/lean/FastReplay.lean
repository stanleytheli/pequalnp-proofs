import SparseReplay
import Std.Data.TreeSet.Lemmas

namespace SparsePermanent.SplitCertificate.Fast
open Std
attribute [local instance] lexOrd

structure Snapshot where
  names : TreeSet ℕ
  wires : TreeSet Wire

def key (outgoing:Bool) (a b:ℕ) : Wire := if outgoing then (a,b) else (b,a)

def remove (t:TreeSet Wire) : List Wire→TreeSet Wire
  | []=>t
  | w::ws=>remove (t.erase w) ws

private theorem survives (t:TreeSet Wire) (l:List Wire) (w:Wire) (old:w∈t) (keep:w∉l) : w∈remove t l := by
  induction l generalizing t with
  | nil=>exact old
  | cons a rest ih=>
    apply ih (t.erase a) _ (fun h=>keep (List.mem_cons_of_mem _ h))
    apply TreeSet.mem_erase.mpr
    exact ⟨fun e=>keep (List.mem_cons.mpr (Or.inl (Std.LawfulEqCmp.eq_of_compare e).symm)),old⟩

def stage (s:Step) (a:Snapshot) : Snapshot:=
  let k:=key s.outgoing
  let rest:=remove a.wires (s.moved.map (k s.parent))
  let added:=(s.fresh,s.fresh)::k s.parent s.fresh::s.moved.map (k s.fresh)
  ⟨a.names.insert s.fresh,rest.insertMany added⟩

def Refines (t:State) (a:Snapshot) :=
  (∀i,i∈t.names ↔ i∈a.names) ∧ ∀w∈t.wires,w∈a.wires

private theorem covered (s:Step) (t:State) (a:Snapshot) (old:Refines t a) :
    ∀w∈stepWires s t.wires,w∈(stage s a).wires := by
  have add (w:Wire) (h:w∈(s.fresh,s.fresh)::key s.outgoing s.parent s.fresh::s.moved.map (key s.outgoing s.fresh)) :
      w∈(stage s a).wires :=
    TreeSet.mem_insertMany_list.mpr (Or.inr (List.contains_iff_mem.mpr h))
  have retain (w:Wire) (h:w∈t.wires) (keep:w∉s.moved.map (key s.outgoing s.parent)) :
      w∈(stage s a).wires := TreeSet.mem_insertMany_list.mpr (Or.inl (survives _ _ _ (old.2 _ h) keep))
  intro w hw
  cases mode:s.outgoing with
  | true=>
    simp only [stepWires,mode,if_true,outWires,List.mem_cons,List.mem_map] at hw
    rcases hw with rfl|rfl|⟨⟨b,c⟩,h,rfl⟩
    · exact add _ (by simp)
    · exact add _ (by simp [key,mode])
    · by_cases move:b=s.parent ∧ c∈s.moved
      · rcases move with ⟨rfl,moved⟩
        apply add
        simp [key,mode,shift,moved]
      · rw [show shift s (b,c)=(b,c) by simp [shift,move]]
        apply retain _ h
        simpa [key,mode,eq_comm,and_comm] using move
  | false=>
    simp only [stepWires,mode,Bool.false_eq_true,if_false,outWires,List.map_cons,List.mem_cons,
      List.mem_map,Prod.swap_prod_mk] at hw
    rcases hw with rfl|rfl|⟨u,⟨v,⟨⟨b,c⟩,h,rfl⟩,rfl⟩,rfl⟩
    · exact add _ (by simp)
    · exact add _ (by simp [key,mode])
    · by_cases move:c=s.parent ∧ b∈s.moved
      · rcases move with ⟨rfl,moved⟩
        apply add
        simp [key,mode,shift,moved]
      · rw [show shift s (b,c).swap=(c,b) by simp [shift,move]]
        apply retain _ h
        simpa [key,mode,eq_comm,and_comm] using move

def run (a:Snapshot) : List Step→Option Snapshot
  | []=>some a
  | s::ss=>if s.parent∈a.names ∧ s.fresh∉a.names then run (stage s a) ss else none

theorem run_sound (ss:List Step) (t:State) (a b:Snapshot) (ok:Refines t a) (done:run a ss=some b) :
    ∃u,replay t ss=some u ∧ Refines u b := by
  induction ss generalizing t a with
  | nil=>cases done;exact ⟨t,rfl,ok⟩
  | cons s ss ih=>
    simp only [run] at done
    split at done
    next good=>
      have h:s.parent∈t.names ∧ s.fresh∉t.names:=⟨(ok.1 _).mpr good.1,fun m=>good.2 ((ok.1 _).mp m)⟩
      let u:State:=⟨s.fresh::t.names,stepWires s t.wires⟩
      have valid:Refines u (stage s a) := by
        refine ⟨fun i=>?_,covered s t a ok⟩
        change i∈s.fresh::t.names ↔ i∈a.names.insert s.fresh
        rw [List.mem_cons,TreeSet.mem_insert,Std.LawfulEqOrd.compare_eq_iff_eq,ok.1]
        exact or_congr (Iff.intro Eq.symm Eq.symm) Iff.rfl
      obtain ⟨v,result,hv⟩:=ih u (stage s a) valid done
      exact ⟨v,by simpa [replay,advance,h,u] using result,hv⟩
    next=>simp at done

def beginAt (roots:List ℕ) : Snapshot:=
  ⟨TreeSet.ofList roots,TreeSet.ofList (initial roots).wires⟩

def certify (n:ℕ) [NeZero n] (neighbors:Array (ℕ×ℕ)) (roots:List ℕ) (ss:List Step) : Bool:=
  match run (beginAt roots) ss with
  | none=>false
  | some b=>b.names.toList.all (·<n) && b.wires.toList.all (fun p=>decide (board neighbors (Fin.ofNat n p.1) (Fin.ofNat n p.2)))

theorem certify_sound (n:ℕ) [NeZero n] (neighbors:Array (ℕ×ℕ)) (roots:List ℕ) (ss:List Step)
    (h:certify n neighbors roots ss=true) : check n neighbors roots ss=true := by
  have start:Refines (initial roots) (beginAt roots) := by
    constructor
    · intro i;simp [beginAt,initial,TreeSet.mem_ofList]
    · intro w hw;simpa [beginAt,TreeSet.mem_ofList] using hw
  unfold certify at h
  cases r:run (beginAt roots) ss with
  | none=>simp [r] at h
  | some b=>
    obtain ⟨u,hre,ref⟩:=run_sound ss _ _ b start r
    simp only [r,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
    simp only [check,hre,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
    exact ⟨fun i hi=>h.1 _ (TreeSet.mem_toList.mpr ((ref.1 i).mp hi)),
      fun w hw=>h.2 _ (TreeSet.mem_toList.mpr (ref.2 _ hw))⟩

end SparsePermanent.SplitCertificate.Fast
#print axioms SparsePermanent.SplitCertificate.Fast.certify_sound
