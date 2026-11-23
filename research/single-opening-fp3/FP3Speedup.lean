import FP3Game
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace TraceBudget

/-- Grouping n into r blocks proves exponential absorption with an explicit constant. -/
theorem polynomial (n r : Nat) : (n+1)^r ≤ max 1 (r^r) * 2^n := by
  cases r with
  | zero => simpa using (Nat.one_le_two_pow (n := n))
  | succ r =>
    let d := r+1
    have hd : 0 < d := Nat.zero_lt_succ _
    have hm := Nat.mod_lt n hd
    have hs := Nat.div_add_mod n d
    have hlinear : n+1 ≤ d*(n/d+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
    have hpow : n/d+1 ≤ 2^(n/d) := Nat.lt_two_pow_self
    have hdn : (n/d)*d ≤ n := Nat.div_mul_le_self _ _
    change (n+1)^d ≤ max 1 (d^d) * 2^n
    calc
      (n+1)^d ≤ (d*(n/d+1))^d := Nat.pow_le_pow_left hlinear _
      _ = d^d*(n/d+1)^d := Nat.mul_pow ..
      _ ≤ d^d*(2^(n/d))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _)
      _ = d^d*2^((n/d)*d) := by rw [Nat.pow_mul]
      _ ≤ _ := Nat.mul_le_mul (le_max_right _ _) (Nat.pow_le_pow_right (by decide) hdn)

/-- The input-length and address overhead in an indexed trace fit within one exponential gap.
Here 1/(a+1) is the hypothetical circuit exponent saving, q = 5a+5 and p = 5a+4. -/
theorem index_bound (a n c m : Nat) (hm : m ≤ (5*a+7)*n+c) :
    a*m/(a+1) ≤ (5*a+3)*n+c := by
  have hcoef : a*(5*a+7) ≤ (a+1)*(5*a+3) := by nlinarith
  apply Nat.div_le_of_le_mul
  calc
    a*m ≤ a*((5*a+7)*n+c) := Nat.mul_le_mul_left _ hm
    _ = (a*(5*a+7))*n+a*c := by ring
    _ ≤ ((a+1)*(5*a+3))*n+(a+1)*c := Nat.add_le_add
      (Nat.mul_le_mul_right _ hcoef) (Nat.mul_le_mul_right _ (Nat.le_succ _))
    _ = _ := by ring

theorem padded_size (a n c r H m : Nat) (hm : m ≤ (5*a+7)*n+c) :
    H*(n+1)^r*2^(a*m/(a+1)) ≤ (H*max 1 (r^r)*2^c)*2^((5*a+4)*n) := by
  have he := index_bound a n c m hm
  calc
    H*(n+1)^r*2^(a*m/(a+1)) ≤ H*(max 1 (r^r)*2^n)*2^((5*a+3)*n+c) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (polynomial n r)) (Nat.pow_le_pow_right (by decide) he)
    _ = (H*max 1 (r^r)*2^c)*(2^n*2^((5*a+3)*n)) := by rw [Nat.pow_add]; ring
    _ = _ := by rw [←Nat.pow_add]; congr 2; ring

end TraceBudget
namespace TraceBudget.BitOpening

/-- Raw bit length of the compiler's honest commitment and each circuit opening. -/
def size (m g : ℕ) := (6*((m+1)+1)+9)*(2+m+g)+2*((m+1)+1)+3

/-- The first-block delimiter, honest opening length and honest verifier clock.
The address width supplied to the compiler is m+1. -/
def cost (m g : ℕ) := size m g+1 + ((7*((m+1)+1)+23)*size m g+19)

private theorem crude (m : ℕ) {g : ℕ} (hg : 1≤g) : cost m g≤3000*(m+1)^3*g := by
  obtain ⟨v,rfl⟩:=Nat.exists_eq_add_of_le hg
  unfold cost size
  ring_nf
  omega

/-- The explicit physical opening cost, paid a polynomial number of times, fits
the stated strictly smaller exponent. The constant is uniform in m and n. -/
theorem batched (a c H r : ℕ) : ∃ K : ℕ, ∀ n m : ℕ, m≤(5*a+7)*n+c →
    let g:=2^(a*m/(a+1))
    m+g≤2^(m+1) ∧ H*(n+1)^r*cost m g ≤ K*2^((5*a+4)*n) := by
  let D:=5*a+7+c+1
  let coeff:=H*3000*D^3
  refine ⟨coeff*max 1 ((r+3)^(r+3))*2^c,fun n m hm=>?_⟩
  let e:=a*m/(a+1)
  let g:=2^e
  have he : e≤m:=Nat.div_le_of_le_mul (by nlinarith)
  have gBound : g≤2^m:=Nat.pow_le_pow_right (by decide) he
  have mh : m≤2^m:=(Nat.lt_two_pow_self (n:=m)).le
  have gp : 1≤g:=Nat.one_le_two_pow
  have lin : m+1≤D*(n+1):=by dsimp [D];nlinarith
  constructor
  · rw [Nat.pow_succ]
    change m+g≤2^m*2
    omega
  · change H*(n+1)^r*cost m g≤_
    calc
      H*(n+1)^r*cost m g ≤ H*(n+1)^r*(3000*(m+1)^3*g) :=
        Nat.mul_le_mul_left _ (crude m gp)
      _ ≤ H*(n+1)^r*(3000*(D*(n+1))^3*g) := by gcongr
      _ = coeff*(n+1)^(r+3)*g := by rw [pow_add];dsimp [coeff];ring
      _ ≤ _ := TraceBudget.padded_size a n c (r+3) coeff m hm

end TraceBudget.BitOpening

#print axioms TraceBudget.BitOpening.batched

namespace TraceBudget.BitOpening

theorem blocks (a C k : ℕ) : ∃ K : ℕ, ∀ n d e : ℕ, d+e≤(5*a+7)*n+C →
    let m:=d+e
    let g:=2^(a*m/(a+1))
    let budget:=K*2^((5*a+4)*n)+K
    m+g≤2^(m+1) ∧
      d+(4+2*k)*(1+d+(4+k)*d)+1≤budget ∧
      m+size m g+1≤budget ∧
      (7*(m+1+1)+23)*size m g+19≤budget := by
  let H:=(6+2*k)*(7+k)+5
  obtain ⟨K,h⟩:=batched a C H 0
  refine ⟨K,fun n d e dim=>?_⟩
  let m:=d+e
  let g:=2^(a*m/(a+1))
  let W:=size m g
  let capacity:=K*2^((5*a+4)*n)+K
  obtain ⟨address,budget⟩:=h n m dim
  have big:H*cost m g≤capacity:=by
    simp only [pow_zero,Nat.mul_one] at budget
    exact budget.trans (Nat.le_add_right _ _)
  have ge:1≤H:=by dsimp [H];omega
  have pay:cost m g≤H*cost m g:=Nat.le_mul_of_pos_left _ ge
  have mx:m+1≤W:=by dsimp [W,size];nlinarith
  have time: (7*(m+1+1)+23)*W+19≤cost m g:=by dsimp [W,cost];omega
  have mxclock:m≤(7*(m+1+1)+23)*W+19:=by nlinarith
  have first:m+W+1≤cost m g:=by exact Nat.add_le_add_right (Nat.add_le_add_right mxclock W) 1 |>.trans_eq (by dsimp [cost,W];ring)
  have ds:d≤m:=Nat.le_add_right _ _
  have uw:d+(4+2*k)*(1+d+(4+k)*d)+1≤H*(m+1):=by dsimp [H];nlinarith [Nat.mul_le_mul_left k ds,Nat.mul_le_mul_left (k*k) ds]
  have entire:m+1≤cost m g:=by omega
  exact ⟨address,(uw.trans (Nat.mul_le_mul_left H entire)).trans big,first.trans (pay.trans big),time.trans (pay.trans big)⟩

end TraceBudget.BitOpening

#print axioms TraceBudget.BitOpening.blocks

namespace StackTrace.OneOpeningGame
open Turing PEqualNP.Library PhysicalSigma CircuitRows RowAddress

def originalTime (a C n : ℕ) := C*2^((5*a+5)*n)+C

noncomputable def traceGates {f : List Bool→Bool} (a : ℕ) (c : PhysicalSigma.Decider f) (C n : ℕ) :=
  let m:=arity c (originalTime a C) n
  2^(a*m/(a+1))

theorem table_arity {f : List Bool→Bool} (a C : ℕ) (c : PhysicalSigma.Decider f) :
    ∃ D : ℕ,∀ n,arity c (originalTime a C) n≤(5*a+7)*n+D := by
  let H:=4+@Fintype.card c.tm.K c.tm.kFin
  let A:=Atomic.overhead c.tm*C
  let B:=A+(Atomic.controls c.tm).length+(Atomic.alphabet c.tm).length+@Fintype.card c.tm.K c.tm.kFin+3
  obtain ⟨D,dim⟩:=widths (5*a+5) A B H (by omega)
  refine ⟨D,fun n=>?_⟩
  let t:=capacity c.tm (T c (originalTime a C) n)
  have eq:t=n+A*2^((5*a+5)*n)+B:=by dsimp [t,capacity,T,originalTime,A,B];ring
  have upper:=dim n t eq.le
  change arity c (originalTime a C) n≤(5*a+5+1)*n+D at upper
  exact upper.trans (Nat.add_le_add_right (Nat.mul_le_mul_right n (by omega)) _)

/-- For one genuine exponential-time decider, the sole remaining hypotheses
are succinct circuits for its actual physical table and one uniform checker
for an explicitly named response relation. All block-size and honest opening
cost inequalities follow from the fixed exponent saving. -/
theorem speedup_of_small_tables {f : List Bool→Bool} (a C : ℕ) (c : PhysicalSigma.Decider f)
    (L : Language Bool) (hL:∀ x,x∈L↔f x=true) (clock:∀ n,c.time n≤originalTime a C n)
    (small:∀ x,PEqualNP.MetaComplexity.HasCircuitSize (arity c (originalTime a C) x.length)
      (table c (originalTime a C) x) (traceGates a c C x.length))
    (checker:∃ B : ℕ,DecidableInTime encodePair (relation c (originalTime a C) (traceGates a c C))
      (fun n=>B*n+B)) :
    ∃ K : ℕ,1≤K ∧ L∈SigmaV 3 (fun n=>K*2^((5*a+4)*n)+K) := by
  let bound:=originalTime a C
  let k:=@Fintype.card c.tm.K c.tm.kFin
  obtain ⟨D,dim⟩:=table_arity a C c
  obtain ⟨K,resources⟩:=TraceBudget.BitOpening.blocks a D k
  let s:=fun n=>(K+1)*2^((5*a+4)*n)+(K+1)
  have grow (n : ℕ):K*2^((5*a+4)*n)+K≤s n:=
    Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ _)) (Nat.le_succ _)
  have resource (n : ℕ):=resources n (timeWidth c bound n) (bitWidth c bound n) (dim n)
  have count:(channels c.tm).length=k:=Finset.length_toList _
  obtain ⟨B,check⟩:=checker
  refine ⟨K+1,Nat.zero_lt_succ _,sigmaV_of_single_opening c L hL s bound (traceGates a c C)
    clock (fun n=>(resource n).1) (fun n=>?_) (fun n=>(resource n).2.2.1.trans (grow n)) small B check⟩
  simpa only [count] using (resource n).2.1.trans (grow n)

/-- A conditional implication into the actual collaboration target FP3. -/
theorem fp3_of_small_tables (a : ℕ)
    (small:∀ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),
      (∀ n,c.time n≤originalTime a C n) →
      ∀ x,PEqualNP.MetaComplexity.HasCircuitSize (arity c (originalTime a C) x.length)
        (table c (originalTime a C) x) (traceGates a c C x.length))
    (checker:∀ (f : List Bool→Bool) (c : PhysicalSigma.Decider f) (C : ℕ),
      (∀ n,c.time n≤originalTime a C n) →
      ∃ B : ℕ,DecidableInTime encodePair (relation c (originalTime a C) (traceGates a c C))
        (fun n=>B*n+B)) :
    FP3 (5*a+4) (5*a+5) := by
  intro L mem
  obtain ⟨C,f,hL,c,clock⟩:=mem
  exact speedup_of_small_tables a C c L hL clock (small f c C clock) (checker f c C clock)

end StackTrace.OneOpeningGame

#print axioms StackTrace.OneOpeningGame.table_arity
#print axioms StackTrace.OneOpeningGame.speedup_of_small_tables
#print axioms StackTrace.OneOpeningGame.fp3_of_small_tables
