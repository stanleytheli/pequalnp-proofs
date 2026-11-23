import FP3Speedup
namespace StackTrace.Hardwire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire (pre : List Bool) (m i : ℕ) :=
  if i<pre.length then m+(if pre.getD i false then 1 else 0)
  else if i<pre.length+m then i-pre.length else m+2+(i-(pre.length+m))

def mapped (pre : List Bool) (m : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire pre m)⟩

private theorem right_get (a b : List Bool) (i : ℕ) (h : a.length ≤ i) :
    (a++b).getD i false=b.getD (i-a.length) false := by
  simp [List.getD,List.getElem?_append_right h]

private theorem left_get (a b : List Bool) (i : ℕ) (h : i < a.length) :
    (a++b).getD i false=a.getD i false := by
  simp [List.getD,List.getElem?_append_left h]

theorem wire_correct (pre x gates : List Bool) (i : ℕ) :
    (x++([false,true]++gates)).getD (wire pre x.length i) false =
      (pre++(x++gates)).getD i false := by
  unfold wire
  by_cases fixed:i<pre.length
  · rw [if_pos fixed,left_get _ _ _ fixed]
    cases v:pre.getD i false <;> simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero]
    · rw [right_get _ _ _ le_rfl];simp
    · rw [right_get _ _ _ (by omega)];simp
  · rw [if_neg fixed,right_get pre (x++gates) i (by omega)]
    by_cases free:i<pre.length+x.length
    · have less:i-pre.length<x.length:=by omega
      rw [if_pos free,left_get x ([false,true]++gates) _ less,left_get x gates _ less]
    · let j:=i-(pre.length+x.length)
      have old:i-pre.length-x.length=j:=by dsimp [j];omega
      have new:x.length+2+j-x.length=2+j:=by omega
      rw [if_neg free,right_get x ([false,true]++gates) (x.length+2+j) (by omega),
        right_get x gates (i-pre.length) (by omega),old,new,
        right_get [false,true] gates (2+j) (by simp)]
      have last:2+j-[false,true].length=j:=by simp
      rw [last]

private def evalGate (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i=>w.getD i false)
private def snocGate (w : List Bool) (g : Gate) := w++[evalGate w g]

private theorem mapped_value (pre x values : List Bool) (g : Gate) :
    evalGate (x++([false,true]++values)) (mapped pre x.length g)=
      evalGate (pre++(x++values)) g := by
  simp only [evalGate,mapped,List.map_map,Function.comp_def,wire_correct]

private theorem fold_both (pre x values : List Bool) (gs : List Gate) :
    ∃ last : List Bool,
      (gs.map (mapped pre x.length)).foldl snocGate (x++([false,true]++values))=x++([false,true]++last) ∧
      gs.foldl snocGate (pre++(x++values))=pre++(x++last) := by
  induction gs generalizing values with
  | nil=>exact ⟨values,rfl,rfl⟩
  | cons g gs ih=>
    let bit:=evalGate (pre++(x++values)) g
    obtain ⟨last,a,b⟩:=ih (values++[bit])
    refine ⟨last,?_,?_⟩
    · simpa only [List.map_cons,List.foldl_cons,snocGate,mapped_value,List.append_assoc,bit] using a
    · simpa only [List.foldl_cons,snocGate,List.append_assoc,bit] using b

def restrict (pre : List Bool) (m : ℕ) (C : Circuit) : Circuit :=
  ⟨[⟨.or,[]⟩,⟨.and,[]⟩]++C.gates.map (mapped pre m),wire pre m C.output⟩

theorem eval_restrict (pre x : List Bool) (C : Circuit) :
    (restrict pre x.length C).eval x=C.eval (pre++x) := by
  obtain ⟨last,h₁,h₂⟩:=fold_both pre x [] C.gates
  simp only [List.append_nil] at h₁ h₂
  have r : (restrict pre x.length C).wires x=(C.gates.map (mapped pre x.length)).foldl snocGate (x++[false,true]) := by
    change (C.gates.map _).foldl snocGate ((x++[false])++[true]) = _
    rw [List.append_assoc]
    rfl
  simp only [Circuit.eval,r,h₁]
  change _=(C.gates.foldl snocGate (pre++x)).getD C.output false
  rw [h₂]
  exact wire_correct pre x last C.output

theorem fanin (pre : List Bool) (m : ℕ) (C : Circuit) (valid:FanInTwo C) : FanInTwo (restrict pre m C) := by
  intro g hg
  simp only [restrict,List.cons_append,List.nil_append,List.mem_cons,List.mem_map] at hg
  rcases hg with rfl|rfl|⟨g,hg,rfl⟩
  · simp
  · simp
  · simpa [mapped] using valid g hg

/-- Fixing any prefix of input bits costs at most two constant gates and works
even for circuits that read a missing wire, including as their output. -/
theorem specialize {n m G : ℕ} {F : (Fin (n+m)→Bool)→Bool}
    (h:HasCircuitSize (n+m) F G) (pre : Fin n→Bool) :
    HasCircuitSize m (fun u=>F (Fin.append pre u)) (G+2) := by
  obtain ⟨C,valid,lim,computes⟩:=h
  refine ⟨restrict (List.ofFn pre) m C,fanin _ _ C valid,?_,fun u=>?_⟩
  · change ([_,_]++C.gates.map _).length≤G+2
    simp [Circuit.size] at lim ⊢
    omega
  · have result:=eval_restrict (List.ofFn pre) (List.ofFn u) C
    rw [List.length_ofFn] at result
    exact result.trans (by simpa only [List.ofFn_fin_append] using computes (Fin.append pre u))

end StackTrace.Hardwire

#print axioms StackTrace.Hardwire.specialize

namespace TraceBudget.BitOpening

/-- The circuit can be specialized from a larger joint input and pay two new
constant gates. Its word and clock budgets still fit the same exponent. -/
theorem projected_blocks (a C k : ℕ) : ∃ K : ℕ, ∀ n d e M : ℕ, d+e≤M → M≤(5*a+7)*n+C →
    let m:=d+e
    let g:=2^(a*M/(a+1))+2
    let budget:=K*2^((5*a+4)*n)+K
    d+(4+2*k)*(1+d+(4+k)*d)+1≤budget ∧
      m+size m g+1≤budget ∧
      (7*(m+1+1)+23)*size m g+19≤budget := by
  let H:=3*((6+2*k)*(7+k)+5)
  obtain ⟨K,h⟩:=batched a C H 0
  refine ⟨K,fun n d e M embedded dim=>?_⟩
  let m:=d+e
  let G:=2^(a*M/(a+1))
  let W:=size m (G+2)
  let cap:=K*2^((5*a+4)*n)+K
  obtain ⟨_,budget⟩:=h n M dim
  have big:H*cost M G≤cap:=by
    simp only [pow_zero,Nat.mul_one] at budget
    exact budget.trans (Nat.le_add_right _ _)
  have Hge:3≤H:=by dsimp [H];omega
  have base:1≤G:=Nat.one_le_two_pow
  have pay:3*cost M G≤H*cost M G:=Nat.mul_le_mul_right _ Hge
  have small:m≤M:=embedded
  have values : W≤3*size M G := by
    have mono:size m (G+2)≤size M (G+2):=by unfold size;gcongr
    have gap:size M (G+2)≤3*size M G:=by unfold size;nlinarith
    exact mono.trans gap
  have D:M+1≤size M G:=by unfold size;nlinarith
  have tm:(7*(m+1+1)+23)*W+19≤3*cost M G:=by
    calc
      _ ≤ (7*(M+1+1)+23)*(3*size M G)+19:=by gcongr
      _ ≤ _:=by unfold cost;nlinarith
  have first:m+W+1≤3*cost M G:=by
    have mc:(7*(M+1+1)+23)*size M G+19≥m:=by nlinarith
    unfold cost
    omega
  have all:M+1≤cost M G:=by unfold cost;omega
  have ds:d≤M:=by omega
  have uw:d+(4+2*k)*(1+d+(4+k)*d)+1≤H*(M+1):=by
    dsimp [H]
    nlinarith [Nat.mul_le_mul_left k ds,Nat.mul_le_mul_left (k*k) ds]
  exact ⟨(uw.trans (Nat.mul_le_mul_left H all)).trans big,first.trans (pay.trans big),tm.trans (pay.trans big)⟩

end TraceBudget.BitOpening

#print axioms TraceBudget.BitOpening.projected_blocks

namespace StackTrace.OneOpeningGame
open Turing PEqualNP.Library PhysicalSigma CircuitRows RowAddress

variable {f : List Bool→Bool} (c : PhysicalSigma.Decider f)

noncomputable def byLength (bound : ℕ→ℕ) (n : ℕ) (pre : Fin n→Bool) (u : Fin (arity c bound n)→Bool) : Bool :=
  let x:=List.ofFn pre
  table c bound x (fun i=>u (Fin.cast (congrArg (arity c bound) List.length_ofFn) i))

/-- One circuit for each n addresses x and both row coordinates; there is no
per-input choice of a circuit in this premise. -/
noncomputable def joint (bound : ℕ→ℕ) (n : ℕ) (v : Fin (n+arity c bound n)→Bool) : Bool :=
  byLength c bound n (fun i=>v (Fin.castAdd _ i)) (fun i=>v (Fin.natAdd n i))

private theorem table_transport (bound : ℕ→ℕ) {x y : List Bool} (same:x=y)
    (u : Fin (arity c bound y.length)→Bool) (len:x.length=y.length) :
    table c bound x (fun i=>u (Fin.cast (congrArg (arity c bound) len) i))=table c bound y u := by
  subst y;rfl

theorem joint_slice (bound : ℕ→ℕ) (x : List Bool) (u : Fin (arity c bound x.length)→Bool) :
    joint c bound x.length (Fin.append x.get u)=table c bound x u := by
  have left:(fun i : Fin x.length=>Fin.append x.get u (Fin.castAdd _ i))=x.get:=funext (Fin.append_left _ _)
  have right:(fun i : Fin (arity c bound x.length)=>Fin.append x.get u (Fin.natAdd x.length i))=u:=
    funext (Fin.append_right _ _)
  unfold joint
  rw [left,right]
  exact table_transport c bound (List.ofFn_get x) u List.length_ofFn

theorem specialize_joint (bound : ℕ→ℕ) (G : ℕ→ℕ)
    (instanceBound:∀ n,PEqualNP.MetaComplexity.HasCircuitSize (n+arity c bound n) (joint c bound n) (G n))
    (x : List Bool) :
    PEqualNP.MetaComplexity.HasCircuitSize (arity c bound x.length) (table c bound x) (G x.length+2) := by
  simpa only [joint_slice] using Hardwire.specialize (instanceBound x.length) x.get

theorem total_arity (a C : ℕ) : ∃ D : ℕ,∀ n,n+arity c (originalTime a C) n≤(5*a+7)*n+D := by
  let H:=4+@Fintype.card c.tm.K c.tm.kFin
  let A:=Atomic.overhead c.tm*C
  let B:=A+(Atomic.controls c.tm).length+(Atomic.alphabet c.tm).length+@Fintype.card c.tm.K c.tm.kFin+3
  obtain ⟨D,dim⟩:=widths (5*a+5) A B H (by omega)
  refine ⟨D,fun n=>?_⟩
  let t:=capacity c.tm (T c (originalTime a C) n)
  have eq:t=n+A*2^((5*a+5)*n)+B:=by dsimp [t,capacity,T,originalTime,A,B];ring
  have upper:=dim n t eq.le
  change arity c (originalTime a C) n≤(5*a+5+1)*n+D at upper
  calc
    n+arity c (originalTime a C) n ≤ n+((5*a+5+1)*n+D):=Nat.add_le_add_left upper n
    _ = _:=by ring

private theorem overhead_pos (tm : FinTM2) : 1≤Atomic.overhead tm := by
  let _:=tm.ΛFin
  have positive:1≤Atomic.depth (tm.m tm.main):=by cases tm.m tm.main <;> simp [Atomic.depth]
  exact positive.trans (Finset.le_sup (f:=fun l=>Atomic.depth (tm.m l)) (Finset.mem_univ tm.main))

noncomputable def jointGates (a C n : ℕ) :=
  let m:=n+arity c (originalTime a C) n
  2^(a*m/(a+1))

private theorem pad_two (m : ℕ) (h:2≤m) : m+2≤2^m := by
  obtain ⟨v,rfl⟩:=Nat.exists_eq_add_of_le h
  induction v with
  | zero=>decide
  | succ v ih=>
    rw [show 2+(v+1)=2+v+1 by omega,Nat.pow_succ]
    omega

theorem joint_gate_address (a C n : ℕ) (hC:1≤C) :
    arity c (originalTime a C) n+(jointGates c a C n+2)≤2^(arity c (originalTime a C) n+1) := by
  let m:=arity c (originalTime a C) n
  let t:=capacity c.tm (T c (originalTime a C) n)
  have time:2^((5*a+5)*n)≤originalTime a C n:=
    (Nat.le_mul_of_pos_left _ hC).trans (Nat.le_add_right _ _)
  have step:originalTime a C n≤Atomic.overhead c.tm*originalTime a C n:=
    Nat.le_mul_of_pos_left _ (overhead_pos c.tm)
  have lim:2^((5*a+5)*n)≤t:=by unfold t capacity T;omega
  have nonzero:t≠0:=by have : 0<2^((5*a+5)*n):=Nat.two_pow_pos _;omega
  have address:(5*a+5)*n≤t.log2:=(Nat.le_log2 nonzero).mpr lim
  have dim:a*n≤m:=by unfold m arity timeWidth width t at *;nlinarith
  have exponent:a*(n+m)/(a+1)≤m:=Nat.div_le_of_le_mul (by nlinarith)
  have gate:jointGates c a C n≤2^m:=Nat.pow_le_pow_right (by decide) exponent
  have m2:2≤m:=by unfold m arity bitWidth timeWidth width;omega
  have spare:=pad_two m m2
  change m+(jointGates c a C n+2)≤2^(m+1)
  rw [Nat.pow_succ]
  omega

/-- A compression hypothesis about a single jointly indexed row family suffices
for each decider; fixing the input uses the actual circuit model. -/
theorem speedup_of_joint_tables (a C : ℕ) (hC:1≤C) (L : Language Bool) (hL:∀ x,x∈L↔f x=true)
    (clock:∀ n,c.time n≤originalTime a C n)
    (small:∀ n,PEqualNP.MetaComplexity.HasCircuitSize (n+arity c (originalTime a C) n)
      (joint c (originalTime a C) n) (jointGates c a C n))
    (checker:∃ B : ℕ,DecidableInTime encodePair
      (relation c (originalTime a C) (fun n=>jointGates c a C n+2)) (fun n=>B*n+B)) :
    ∃ K : ℕ,1≤K ∧ L∈SigmaV 3 (fun n=>K*2^((5*a+4)*n)+K) := by
  let bound:=originalTime a C
  let k:=@Fintype.card c.tm.K c.tm.kFin
  obtain ⟨D,dim⟩:=total_arity c a C
  obtain ⟨K,resources⟩:=TraceBudget.BitOpening.projected_blocks a D k
  let s:=fun n=>(K+1)*2^((5*a+4)*n)+(K+1)
  have grow (n : ℕ):K*2^((5*a+4)*n)+K≤s n:=
    Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.le_succ _)
  have res (n : ℕ):=resources n (timeWidth c bound n) (bitWidth c bound n) (n+arity c bound n)
    (Nat.le_add_left _ _) (dim n)
  have count:(channels c.tm).length=k:=Finset.length_toList _
  obtain ⟨B,check⟩:=checker
  refine ⟨K+1,Nat.zero_lt_succ _,sigmaV_of_single_opening c L hL s bound (fun n=>jointGates c a C n+2)
    clock (fun n=>joint_gate_address c a C n hC) (fun n=>?_) (fun n=>(res n).2.1.trans (grow n))
    (specialize_joint c bound _ small) B check⟩
  simpa only [count] using (res n).1.trans (grow n)

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.specialize_joint
#print axioms StackTrace.OneOpeningGame.speedup_of_joint_tables
