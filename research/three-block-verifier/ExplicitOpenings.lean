import PEqualNP.Library.Machines.ComposeRun
import PEqualNP.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Nat


namespace PEqualNP.Outside.Majority567Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) :=
  List.foldl_append

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD, hi]

lemma run_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact getD_snoc_lt _ _ _ hi

end PEqualNP.Outside.Majority567Upper

namespace CutVerification

section
variable {Q Z V : Type*} [Fintype Q] [Fintype Z] [DecidableEq V]

/-- For each source q and offset z, take a length-L path to an ancestor.
At fixed z and time, a vertex belongs to at most one translated path. -/
theorem route_counting (L S : ℕ) (cut : Finset V) (region : Q → Finset V)
    (size : ∀ q, (region q).card ≤ S)
    (path : Q → Z → Fin (L+1) → V)
    (last_injective : ∀ q, Function.Injective (fun z => path q z (Fin.last L)))
    (step_injective : ∀ z i, Function.Injective (fun q => path q z i))
    (covered : ∀ q z, (∀ i, path q z i ∉ cut) → path q z (Fin.last L) ∈ region q) :
    Fintype.card Q * Fintype.card Z ≤ Fintype.card Q * S +
      Fintype.card Z * (L+1) * cut.card := by
  classical
  let slot (q : Q) (v : {v // v ∈ region q}) : Fin S :=
    ⟨((Fintype.equivFin _ v).val), (Fintype.equivFin _ v).isLt.trans_le
      (by simpa only [Fintype.card_coe] using size q)⟩
  have slot_inj (q : Q) : Function.Injective (slot q) := by
    intro x y h
    apply (Fintype.equivFin _).injective
    exact Fin.ext (congrArg (fun v : Fin S => v.val) h)
  let stamp (q : Q) (z : Z) : (Q × Fin S) ⊕ ((Z × Fin (L+1)) × {v // v ∈ cut}) :=
    if h : ∃ i, path q z i ∈ cut then
      .inr ((z,h.choose),⟨path q z h.choose,h.choose_spec⟩)
    else .inl (q,slot q ⟨_,covered q z (fun i hi => h ⟨i,hi⟩)⟩)
  have unique : Function.Injective (fun p : Q × Z => stamp p.1 p.2) := by
    rintro ⟨q,z⟩ ⟨r,w⟩ e
    change stamp q z = stamp r w at e
    unfold stamp at e
    split at e <;> split at e
    · rename_i h j
      have key := congrArg Prod.fst (Sum.inr.inj e)
      have zw : z=w := congrArg Prod.fst key
      subst w
      have ij : h.choose = j.choose := congrArg Prod.snd key
      have loc := congrArg Subtype.val (congrArg Prod.snd (Sum.inr.inj e))
      change path q z h.choose = path r z j.choose at loc
      rw [ij] at loc
      have qr := step_injective z j.choose loc
      simp [qr]
    · contradiction
    · contradiction
    · have qr : q=r := congrArg Prod.fst (Sum.inl.inj e)
      subst r
      have eq := slot_inj q (congrArg Prod.snd (Sum.inl.inj e))
      have zw := last_injective q (congrArg Subtype.val eq)
      simp [zw]
  have h := Fintype.card_le_of_injective _ unique
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] using h

end
end CutVerification

namespace CutVerification.Grid

abbrev Point (d m : ℕ) := Fin d → Fin m

def Step {d m : ℕ} (p q : Point d m) : Prop :=
  ∃ j : Fin d, ∀ i, (p i).val = (q i).val + if i=j then 1 else 0

private def offset (r i z t : ℕ) := r - min z (t-i*r)

private theorem offset_step (r i z t : ℕ) (hz : z ≤ r) :
    offset r i z t = offset r i z (t+1) ∨
    (offset r i z t = offset r i z (t+1)+1 ∧ i*r ≤ t ∧ t < (i+1)*r) := by
  unfold offset
  rw [Nat.succ_mul]
  omega

private def path {d a r : ℕ} (q : Point d a) (z : Point d (r+1))
    (t : Fin (d*r+1)) : Point d (a+r) := fun i =>
  ⟨(q i).val + offset r i.val (z i).val t.val, by
    have h := (q i).isLt
    have e : offset r i.val (z i).val t.val ≤ r := Nat.sub_le _ _
    omega⟩

private theorem path_end_inj {d a r : ℕ} (q : Point d a) :
    Function.Injective (fun z : Point d (r+1) => path q z (Fin.last (d*r))) := by
  intro z w e
  funext i
  apply Fin.ext
  have v := congrArg Fin.val (congrFun e i)
  change (q i).val + offset r i.val (z i).val (d*r) = (q i).val + offset r i.val (w i).val (d*r) at v
  have cap := Nat.mul_le_mul_right r (show i.val+1 ≤ d by omega)
  rw [Nat.succ_mul] at cap
  have hz := (z i).isLt
  have hw := (w i).isLt
  unfold offset at v
  omega

private theorem path_time_inj {d a r : ℕ} (z : Point d (r+1)) (t : Fin (d*r+1)) :
    Function.Injective (fun q : Point d a => path q z t) := by
  intro q q' e
  funext i
  apply Fin.ext
  have h := congrArg Fin.val (congrFun e i)
  exact Nat.add_right_cancel h

private theorem path_step {d a r : ℕ} (q : Point d a) (z : Point d (r+1)) (t : Fin (d*r)) :
    path q z t.castSucc = path q z t.succ ∨ Step (path q z t.castSucc) (path q z t.succ) := by
  classical
  by_cases h : ∀ i : Fin d, offset r i.val (z i).val t.val = offset r i.val (z i).val (t.val+1)
  · exact Or.inl (funext fun i => Fin.ext (congrArg ((q i).val + ·) (h i)))
  · obtain ⟨j,hj⟩ := Classical.not_forall.mp h
    obtain ⟨hd,hlo,hhi⟩ := (offset_step r j.val (z j).val t.val (by have := (z j).isLt; omega)).resolve_left hj
    refine Or.inr ⟨j,fun i => ?_⟩
    change (q i).val + offset r i.val (z i).val t.val =
      (q i).val + offset r i.val (z i).val (t.val+1) + if i=j then 1 else 0
    by_cases he : i=j
    · subst i; simp [hd,Nat.add_assoc]
    · simp only [ite_eq_right he,Nat.add_zero,Nat.add_right_inj]
      rcases offset_step r i.val (z i).val t.val (by have := (z i).isLt; omega) with eq | ⟨_,low,high⟩
      · exact eq
      · rcases lt_or_gt_of_ne (show i.val ≠ j.val from fun e => he (Fin.ext e)) with h | h
        · have bound := Nat.mul_le_mul_right r (show i.val+1 ≤ j.val by omega)
          omega
        · have bound := Nat.mul_le_mul_right r (show j.val+1 ≤ i.val by omega)
          omega

def start {d a : ℕ} (r : ℕ) (q : Point d a) : Point d (a+r) :=
  fun i => ⟨(q i).val+r,Nat.add_lt_add_right (q i).isLt r⟩

private theorem path_start {d a r : ℕ} (q : Point d a) (z : Point d (r+1)) :
    path q z 0 = start r q := by
  funext i; apply Fin.ext; simp [path,offset,start]

theorem local_count (d a r S : ℕ) (cut : Finset (Point d (a+r)))
    (region : Point d a → Finset (Point d (a+r))) (size : ∀ q, (region q).card ≤ S)
    (starts : ∀ q, start r q ∈ region q)
    (closed : ∀ q u v, u ∈ region q → Step u v → v ∉ cut → v ∈ region q) :
    a^d * (r+1)^d ≤ a^d*S + (r+1)^d*(d*r+1)*cut.card := by
  classical
  have included (q : Point d a) (z : Point d (r+1)) (avoids : ∀ t, path q z t ∉ cut) :
      path q z (Fin.last (d*r)) ∈ region q := by
    have all (i : Fin (d*r+1)) : path q z i ∈ region q := by
      induction i using Fin.induction with
      | zero => rw [path_start]; exact starts q
      | succ i ih =>
        rcases path_step q z i with he | he
        · rwa [←he]
        · exact closed q _ _ ih he (avoids _)
    exact all _
  have count := CutVerification.route_counting (d*r) S cut region size path path_end_inj path_time_inj included
  simpa only [Point,Fintype.card_fun,Fintype.card_fin] using count

end CutVerification.Grid



namespace CutVerification

variable {V A : Type*} [DecidableEq V]

/-- Vertices may represent Boolean gates or whole bounded-width machine blocks. -/
structure DAG (V A : Type*) where
  rank : V → ℕ
  pred : V → Finset V
  pred_lt : ∀ {p v}, p ∈ pred v → rank p < rank v
  step : (v : V) → ({p // p ∈ pred v} → A) → A

def Solves (G : DAG V A) (trueValue : V → A) : Prop :=
  ∀ v, trueValue v = G.step v (fun p => trueValue p.1)

/-- For each challenge at the cut, list the vertices that will be opened together.
The boundary of an opening may only refer to the cut's shared labels. -/
structure Scheme (G : DAG V A) where
  cut : Finset V
  region : {v // v ∈ cut} → Finset V
  self_mem : ∀ v, v.1 ∈ region v
  closed : ∀ v w, w ∈ region v → ∀ p ∈ G.pred w, p ∉ cut → p ∈ region v

variable {G : DAG V A} (S : Scheme G)

/-- The parent label is obtained either from the one shared first message or from the
challenge-specific third message. The last prover cannot choose values outside this region. -/
def readParent (first : {v // v ∈ S.cut} → A)
    (v : {v // v ∈ S.cut}) (last : {u // u ∈ S.region v} → A)
    (w : {u // u ∈ S.region v}) (p : {u // u ∈ G.pred w.1}) : A :=
  if hp : p.1 ∈ S.cut then first ⟨p.1,hp⟩ else last ⟨p.1,S.closed v w.1 w.2 p.1 p.2 hp⟩

def Check (first : {v // v ∈ S.cut} → A)
    (v : {v // v ∈ S.cut}) (last : {u // u ∈ S.region v} → A) : Prop :=
  first v = last ⟨v.1,S.self_mem v⟩ ∧
  ∀ w : {u // u ∈ S.region v}, last w = G.step w.1 (readParent S first v last w)

/-- An accepting cut commitment, followed by every vertex challenge and a local opening,
exists precisely for a correct answer at the marked output. -/
theorem threeBlock {truth : V → A} (htruth : Solves G truth)
    (out : {v // v ∈ S.cut}) (accept : A → Prop) :
    accept (truth out.1) ↔
      ∃ first : {v // v ∈ S.cut} → A, accept (first out) ∧
        ∀ v : {v // v ∈ S.cut}, ∃ last : {u // u ∈ S.region v} → A, Check S first v last := by
  constructor
  · intro h
    refine ⟨fun v => truth v.1, h, fun v => ⟨fun u => truth u.1,rfl,?_⟩⟩
    intro w
    change truth w.1 = _
    rw [htruth w.1]
    congr 1
    funext p
    simp [readParent]
  · rintro ⟨first,ha,hcheck⟩
    suffices h : ∀ v : {v // v ∈ S.cut}, first v = truth v.1 by
      simpa only [h out] using ha
    have all (r : ℕ) (v : {v // v ∈ S.cut}) (hv : G.rank v.1 = r) : first v = truth v.1 := by
      induction r using Nat.strong_induction_on generalizing v with
      | ind r ih =>
        obtain ⟨last,hout,hloc⟩ := hcheck v
        have region_correct (d : ℕ) (w : {u // u ∈ S.region v}) (hw : G.rank w.1 = d)
            (hle : d ≤ r) : last w = truth w.1 := by
          induction d using Nat.strong_induction_on generalizing w with
          | ind d lower =>
            rw [hloc w,htruth w.1]
            congr 1
            funext p
            have hlt : G.rank p.1 < d := hw ▸ G.pred_lt p.2
            unfold readParent
            split
            next hp => exact ih (G.rank p.1) (hlt.trans_le hle) ⟨p.1,hp⟩ rfl
            next hp => exact lower (G.rank p.1) hlt _ rfl (hlt.le.trans hle)
        exact hout.trans (region_correct _ _ hv (le_refl _))
    exact fun v => all _ v rfl

end CutVerification

namespace CutVerification.Grid

private theorem place_step {V A : Type*} [DecidableEq V] {G : DAG V A} (S : Scheme G)
    {a b : V} (ha : ∃ c, a ∈ S.region c) (hb : b ∈ G.pred a) : ∃ c, b ∈ S.region c := by
  by_cases h : b ∈ S.cut
  · exact ⟨⟨b,h⟩,S.self_mem ⟨b,h⟩⟩
  · obtain ⟨c,hc⟩ := ha
    exact ⟨c,S.closed c a hc b hb h⟩

/-- Every ancestor of the output is opened in at least one region, possibly rooted at
a cut vertex intermediate on the path to the output. -/
theorem ancestor_covered {V A : Type*} [DecidableEq V] {G : DAG V A} (S : Scheme G)
    (out : {v // v ∈ S.cut}) {a : V}
    (chain : Relation.ReflTransGen (fun u v => v ∈ G.pred u) out.val a) :
    ∃ c, a ∈ S.region c := by
  induction chain with
  | refl => exact ⟨out,S.self_mem out⟩
  | tail _ step ih => exact place_step S ih step

theorem cut_count {A : Type*} (d a r W : ℕ) {G : DAG (Point d (a+r)) A} (S : Scheme G)
    (out : {v // v ∈ S.cut}) (edges : ∀ u v, Step u v → v ∈ G.pred u)
    (reaches : ∀ q : Point d a,
      Relation.ReflTransGen (fun u v => v ∈ G.pred u) out.val (start r q))
    (open_bound : ∀ c, (S.region c).card ≤ W) :
    a^d*(r+1)^d ≤ a^d*W + (r+1)^d*(d*r+1)*S.cut.card := by
  classical
  choose owner membership using (fun q => ancestor_covered S out (reaches q))
  exact local_count d a r W S.cut (fun q => S.region (owner q))
    (fun q => open_bound (owner q)) membership
    (fun q u v hu he hv => S.closed (owner q) u hu v (edges u v he) hv)

private theorem capacity_bound (Q Z L C W : ℕ) (hz : 0 < Z) (room : 2*W ≤ Z)
    (count : Q*Z ≤ Q*W + Z*L*C) : Q ≤ 2*L*C := by
  have half := Nat.mul_le_mul_left Q room
  have h2 : Q*(2*W) = 2*(Q*W) := by ring
  rw [h2] at half
  refine Nat.le_of_mul_le_mul_left ?_ hz
  calc
    Z*Q = Q*Z := Nat.mul_comm .. 
    _ ≤ 2*(Z*L*C) := by omega
    _ = Z*(2*L*C) := by ring

/-- For a side length n^(d+1)+n^d, either the largest opening or the cut
has order n^(d*d). The total vertex count has order n^(d*(d+1)). -/
theorem power_obstruction (d n W C : ℕ) (hn : 0 < n)
    (count : (n^(d+1))^d*(n^d+1)^d ≤
      (n^(d+1))^d*W + (n^d+1)^d*(d*n^d+1)*C) :
    n^(d*d) ≤ 2*W ∨ n^(d*d) ≤ 2*(d+1)*C := by
  by_cases low : n^(d*d) ≤ 2*W
  · exact Or.inl low
  · right
    have zpos : 0 < (n^d+1)^d := pow_pos (Nat.succ_pos _) _
    have powid : (n^d)^d = n^(d*d) := (pow_mul ..).symm
    have room : 2*W ≤ (n^d+1)^d := calc
      2*W ≤ n^(d*d) := by omega
      _ = (n^d)^d := powid.symm
      _ ≤ (n^d+1)^d := Nat.pow_le_pow_left (Nat.le_succ _) _
    have lower := capacity_bound _ _ _ _ _ zpos room count
    have scale : 0 < n^d := pow_pos hn _
    have cost : d*n^d+1 ≤ (d+1)*n^d := by rw [Nat.succ_mul]; omega
    refine Nat.le_of_mul_le_mul_right ?_ scale
    calc
      n^(d*d)*n^d = (n^(d+1))^d := by rw [←pow_add,←pow_mul,Nat.succ_mul]
      _ ≤ 2*(d*n^d+1)*C := lower
      _ ≤ 2*((d+1)*n^d)*C := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ cost)
      _ = 2*(d+1)*C*n^d := by ring

end CutVerification.Grid

namespace CutVerification.Grid

open Finset

/-- A physical DAG may realize a grid edge by several steps. Each intermediate step
is assigned to one of the two endpoint cells. This permits batched memory transfers. -/
structure Embedding {d m : ℕ} {V A : Type*} [DecidableEq V] (G : DAG V A) where
  root : Point d m → V
  injective : Function.Injective root
  owner : V → Point d m
  wire : ∀ u v, Step u v → Relation.ReflTransGen
    (fun x y => y ∈ G.pred x ∧ (owner y = u ∨ owner y = v)) (root u) (root v)

private def lowerNeighbors {d m : ℕ} (u : Point d m) : Finset (Point d m) :=
  Finset.univ.image (fun j : Fin d => Function.update u j ⟨(u j).val-1,
    (Nat.sub_le _ _).trans_lt (u j).isLt⟩)

private theorem lower_mem {d m : ℕ} {u v : Point d m} (h : Step u v) : v ∈ lowerNeighbors u := by
  obtain ⟨j,h⟩ := h
  apply Finset.mem_image.mpr
  refine ⟨j,Finset.mem_univ _,?_⟩
  funext i
  apply Fin.ext
  have e := h i
  by_cases ij : i=j
  · subst i; simp at e; simp [e]
  · simpa [Function.update_of_ne ij,ij] using e

theorem embedded_count {d a r W : ℕ} {V A : Type*} [DecidableEq V] {G : DAG V A}
    (E : Embedding (d:=d) (m:=a+r) G) (S : Scheme G) (out : {v // v ∈ S.cut})
    (reaches : ∀ q, Relation.ReflTransGen (fun x y => y ∈ G.pred x) out.val (E.root (start r q)))
    (size : ∀ c, (S.region c).card ≤ W) :
    a^d*(r+1)^d ≤ a^d*W + (r+1)^d*(d*r+1)*((d+1)*S.cut.card) := by
  classical
  let blocked := S.cut.biUnion (fun p => insert (E.owner p) (lowerNeighbors (E.owner p)))
  have mark (p : V) (hp : p ∈ S.cut) (v : Point d (a+r))
      (hv : E.owner p = v ∨ Step (E.owner p) v) : v ∈ blocked := by
    apply Finset.mem_biUnion.mpr
    refine ⟨p,hp,?_⟩
    rcases hv with e|e
    · exact Finset.mem_insert_self _ _ |> (e ▸ ·)
    · exact Finset.mem_insert_of_mem (lower_mem e)
  have hblocked : blocked.card ≤ (d+1)*S.cut.card := by
    calc
      blocked.card ≤ ∑ p ∈ S.cut, (insert (E.owner p) (lowerNeighbors (E.owner p))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ S.cut, (d+1) := by
        apply Finset.sum_le_sum
        intro p _
        have h : (lowerNeighbors (E.owner p)).card ≤ d := by
          calc
            _ ≤ (Finset.univ : Finset (Fin d)).card := by
              unfold lowerNeighbors
              exact Finset.card_image_le
            _ = d := by simp
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right h 1)
      _ = (d+1)*S.cut.card := by simp [Nat.mul_comm]
  choose pick membership using (fun q => ancestor_covered S out (reaches q))
  let region (q : Point d a) := Finset.univ.filter (fun u => E.root u ∈ S.region (pick q))
  have limit (q : Point d a) : (region q).card ≤ W := by
    refine (Finset.card_le_card_of_injOn E.root ?_ (Set.injOn_of_injective E.injective)).trans (size (pick q))
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have starts (q : Point d a) : start r q ∈ region q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,membership q⟩
  have closed (q : Point d a) (u v : Point d (a+r)) (hu : u ∈ region q) (uv : Step u v) (clear : v ∉ blocked) :
      v ∈ region q := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have chain := E.wire u v uv
    have run {w : V} (hh : Relation.ReflTransGen
        (fun x y => y ∈ G.pred x ∧ (E.owner y = u ∨ E.owner y = v)) (E.root u) w) :
        w ∈ S.region (pick q) := by
      induction hh with
      | refl => exact (Finset.mem_filter.mp hu).2
      | tail _ edge ih =>
        obtain ⟨he,atend⟩ := edge
        apply S.closed _ _ ih _ he
        intro bad
        apply clear
        apply mark _ bad
        rcases atend with h|h
        · exact Or.inr (h ▸ uv)
        · exact Or.inl h
    exact run chain
  exact (local_count d a r W blocked region limit starts closed).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hblocked) _)

end CutVerification.Grid

namespace CutVerification.Grid

def top {d m : ℕ} (hm : 0<m) : Point d m := fun _ => ⟨m-1,by omega⟩

/-- The highest grid vertex sees every translated anchor through actual predecessor steps. -/
theorem top_reaches {d m : ℕ} (hm : 0<m) (v : Point d m) :
    Relation.ReflTransGen Step (top hm) v := by
  classical
  let deficit (z : Point d m) := ∑ i : Fin d, (m-1-(z i).val)
  generalize hl : deficit v = l
  induction l using Nat.strong_induction_on generalizing v with
  | ind l ih =>
    by_cases isTop : v=top hm
    · rw [isTop]
    have someLow : ∃ j : Fin d, (v j).val+1 < m := by
      by_contra! h
      apply isTop
      funext i
      apply Fin.ext
      have := (v i).isLt
      have := h i
      change (v i).val = m-1
      omega
    obtain ⟨j,hj⟩ := someLow
    let u := Function.update v j (⟨(v j).val+1,hj⟩ : Fin m)
    have e (i : Fin d) : (u i).val = (v i).val + if i=j then 1 else 0 := by
      by_cases hi : i=j <;> simp [u,hi]
    have less : deficit u < deficit v := by
      apply Finset.sum_lt_sum
      · intro i _
        apply Nat.sub_le_sub_left
        rw [e i]
        exact Nat.le_add_right _ _
      · refine ⟨j,Finset.mem_univ _,?_⟩
        have h := e j
        simp only [ite_true] at h
        omega
    exact (ih (deficit u) (by omega) u rfl).tail ⟨j,e⟩

end CutVerification.Grid

namespace PascalGrid

variable {α : Type*} [DecidableEq α] [Fintype α]

def total (x : α → ℕ) := ∑ i, x i
def denominator (x : α → ℕ) := ∏ i, (x i).factorial
def ways (x : α → ℕ) := Nat.multinomial Finset.univ x
def down (x : α → ℕ) (i : α) := Function.update x i (x i-1)

omit [DecidableEq α] in
private theorem spec (x : α → ℕ) : denominator x * ways x = (total x).factorial :=
  Nat.multinomial_spec _ _

private theorem weighted_parent (x : α → ℕ) (i : α) (hi : 0<x i) :
    denominator x * ways (down x i) = x i * (total x-1).factorial := by
  have hd : total (down x i) + 1 = total x := by
    unfold total down
    rw [Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) x]
    omega
  have hd' : total (down x i)=total x-1 := by omega
  have prodmap : (fun j => (down x i j).factorial) =
      Function.update (fun j => (x j).factorial) i ((x i-1).factorial) := by
    funext j
    by_cases he : j=i <;> simp [down,he]
  have per : x i*(x i-1).factorial=(x i).factorial := by
    simpa only [show x i-1+1=x i by omega] using (Nat.factorial_succ (x i-1)).symm
  have den : x i * denominator (down x i) = denominator x := by
    unfold denominator
    rw [prodmap,Finset.prod_update_of_mem (Finset.mem_univ i),
      Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i) (fun j => (x j).factorial),
      ←Nat.mul_assoc,per]
  rw [←den,Nat.mul_assoc,spec,hd']

/-- Multidimensional Pascal recurrence. Every nonzero coordinate supplies one parent. -/
theorem pascal (x : α → ℕ) (positive : 0 < total x) :
    ways x = ∑ i, (if 0<x i then ways (down x i) else 0) := by
  have denpos : 0 < denominator x := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left denpos
  rw [spec,Finset.mul_sum]
  calc
    (total x).factorial = total x * (total x-1).factorial := by
      simpa only [show total x-1+1=total x by omega] using Nat.factorial_succ (total x-1)
    _ = ∑ i, x i * (total x-1).factorial := Finset.sum_mul ..
    _ = ∑ i, denominator x * (if 0 < x i then ways (down x i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0<x i
      · simp [h,weighted_parent x i h]
      · simp [show x i=0 by omega]

def digitTest (W n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range W, if k / 2^i % 2 ≤ n / 2^i % 2 then 1 else 0

private theorem digit_small (n k : ℕ) : (n%2).choose (k%2) = if k%2 ≤ n%2 then 1 else 0 := by
  have cn : n%2=0 ∨ n%2=1 := by omega
  have ck : k%2=0 ∨ k%2=1 := by omega
  rcases cn with cn|cn <;> rcases ck with ck|ck <;> simp [cn,ck]

private theorem digit_spec (W n k : ℕ) (hn : n<2^W) (hk : k<2^W) :
    n.choose k ≡ digitTest W n k [MOD 2] := by
  have lucas := Choose.lucas_theorem_nat (p:=2) hn hk
  simpa only [digitTest,digit_small] using lucas

/-- Evaluate the label by progressively choosing each coordinate's positions from
the remaining total. Each binary test reads only W pairs of digits. -/
def reader {α : Type*} [DecidableEq α] (W : ℕ) (x : α → ℕ) : List α → ℕ
  | [] => 1
  | i::is =>
    let n := x i + ∑ j ∈ is.toFinset, x j
    (digitTest W n (x i) * reader W x is) % 2

theorem reader_spec {α : Type*} [DecidableEq α] (W : ℕ) (x : α → ℕ) (is : List α) (nd : is.Nodup)
    (bound : (∑ i ∈ is.toFinset, x i) < 2^W) :
    reader W x is = Nat.multinomial is.toFinset x % 2 := by
  induction is with
  | nil => simp [reader]
  | cons i is ih =>
    obtain ⟨ni,nd'⟩ := List.nodup_cons.mp nd
    have off : i ∉ is.toFinset := by simpa using ni
    rw [List.toFinset_cons,Finset.sum_insert off] at bound
    rw [List.toFinset_cons,Nat.multinomial_insert off]
    unfold reader
    rw [ih nd' (by omega)]
    have mod := digit_spec W (x i+∑ j ∈ is.toFinset,x j) (x i) bound (by omega)
    exact Nat.ModEq.mul mod.symm (Nat.mod_modEq _ _)

theorem reader_grid (d W : ℕ) (x : Fin d → ℕ) (bound : total x < 2^W) :
    reader W x (List.finRange d) = ways x % 2 := by
  have all : (List.finRange d).toFinset = Finset.univ := by ext i; simp
  simpa only [all,ways] using reader_spec W x (List.finRange d) (List.nodup_finRange d)
    (by rw [all]; exact bound)

end PascalGrid
namespace PascalGrid

private def listWays : List ℕ → ℕ
  | [] => 1
  | a::bs => (a+bs.sum).choose a * listWays bs

private def halveAll (xs : List ℕ) := xs.map (·/2)
private def lowCount (xs : List ℕ) := (xs.map (·%2)).sum

private theorem binary_sum (xs : List ℕ) :
    xs.sum = 2*(halveAll xs).sum + lowCount xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [halveAll,List.map_cons,List.sum_cons,lowCount] at *
    omega

private theorem choose_low (a b : ℕ) :
    (a+b).choose a % 2 = if a%2+b%2 ≤ 1 then (a/2+b/2).choose (a/2)%2 else 0 := by
  have luc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n:=a+b) (k:=a) (p:=2)
  change _ % 2 = _ % 2 at luc
  obtain h|h : a%2=0 ∨ a%2=1 := by omega
  all_goals obtain k|k : b%2=0 ∨ b%2=1 := by omega
  all_goals rw [show (a+b)%2 = (a%2+b%2)%2 by omega,h,k] at luc
  all_goals first
    | simpa [h,k,show (a+b)/2=a/2+b/2 by omega] using luc
    | simpa [h,k] using luc

private theorem halve_ways (xs : List ℕ) :
    listWays xs % 2 = if lowCount xs ≤ 1 then listWays (halveAll xs) % 2 else 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have split_sum := binary_sum xs
    change ((a+xs.sum).choose a * listWays xs) % 2 =
      if a%2+lowCount xs ≤ 1 then ((a/2+(halveAll xs).sum).choose (a/2) * listWays (halveAll xs)) % 2 else 0
    have choose := choose_low a xs.sum
    by_cases small : lowCount xs ≤ 1
    · have lo : xs.sum%2 = lowCount xs := by omega
      have hi : xs.sum/2 = (halveAll xs).sum := by omega
      rw [lo,hi] at choose
      rw [ite_eq_left small] at ih
      by_cases clean : a%2+lowCount xs ≤ 1
      · rw [ite_eq_left clean] at choose ⊢
        exact Nat.ModEq.mul (show _ ≡ _ [MOD 2] from choose) (show _ ≡ _ [MOD 2] from ih)
      · rw [ite_eq_right clean] at choose ⊢
        rw [Nat.mul_mod,choose]
        simp
    · rw [ite_eq_right small] at ih
      rw [ite_eq_right (show ¬ a%2+lowCount xs ≤1 by omega),Nat.mul_mod,ih]; simp

/-- Each binary column may contain at most one set bit. -/
def carryFree : ℕ → List ℕ → Bool
  | 0,_ => true
  | W+1,xs => decide (lowCount xs ≤ 1) && carryFree W (halveAll xs)

private theorem zero_list (xs : List ℕ) (h : xs.sum=0) : listWays xs=1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp at h; simp [listWays,h,ih]

theorem lucas_bits (W : ℕ) (xs : List ℕ) (bound : xs.sum<2^W) :
    listWays xs % 2 = (carryFree W xs).toNat := by
  induction W generalizing xs with
  | zero =>
    have hz : xs.sum=0 := by simpa using bound
    rw [zero_list _ hz]; rfl
  | succ W ih =>
    rw [halve_ways]
    have eq := binary_sum xs
    have half : (halveAll xs).sum < 2^W := by rw [pow_succ] at bound; omega
    by_cases clean : lowCount xs≤1 <;> simp [clean,carryFree,ih _ half]

variable {α : Type*} [DecidableEq α]

private theorem index_sum (is : List α) (x : α → ℕ) (nd : is.Nodup) :
    (is.map x).sum = ∑ j ∈ is.toFinset, x j := by
  induction is with
  | nil => simp
  | cons i is ih =>
    obtain ⟨off,other⟩ := List.nodup_cons.mp nd
    simp [off,ih other]

private theorem to_list_ways (is : List α) (x : α → ℕ) (distinct : is.Nodup) :
    listWays (is.map x) = Nat.multinomial is.toFinset x := by
  induction is with
  | nil => simp [listWays]
  | cons i is ih =>
    obtain ⟨off,other⟩ := List.nodup_cons.mp distinct
    have notin : i ∉ is.toFinset := by simpa using off
    rw [List.toFinset_cons,Nat.multinomial_insert notin,List.map_cons,listWays,ih other]
    have sums : (is.map x).sum = ∑ j ∈ is.toFinset,x j := by
      exact index_sum is x other
    rw [sums]

end PascalGrid
namespace PascalGrid

private def decode : (W : ℕ) → (Fin W → Bool) → ℕ
  | 0,_ => 0
  | W+1,bs => (bs 0).toNat + 2*decode W (fun i => bs i.succ)

private theorem decode_bound (W : ℕ) (bs : Fin W → Bool) : decode W bs < 2^W := by
  induction W with
  | zero => simp [decode]
  | succ W ih =>
    have := ih (fun i => bs i.succ)
    simp only [decode,pow_succ]
    cases bs 0 <;> simp <;> omega

private theorem all_zeros (xs : List ℕ) (h : ∀ a∈xs, a=0) : xs.sum=0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem lucas_bits_of_length (W : ℕ) (xs : List ℕ) (bounded : ∀ a∈xs, a<2^W) :
    listWays xs % 2 = (carryFree W xs).toNat := by
  induction W generalizing xs with
  | zero =>
    have hz := all_zeros xs (fun a ha => Nat.eq_zero_of_le_zero (by simpa using bounded a ha))
    rw [zero_list _ hz]; rfl
  | succ W ih =>
    rw [halve_ways]
    have hh (n : ℕ) (hn : n∈halveAll xs) : n<2^W := by
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hn
      have h := bounded a ha
      rw [pow_succ] at h; omega
    by_cases c : lowCount xs ≤1 <;> simp [c,carryFree,ih _ hh]

private def bitValues (d W : ℕ) (bs : Fin d → Fin W → Bool) :=
  (List.finRange d).map fun i => decode W (bs i)

private theorem halve_decode (W : ℕ) (bs : Fin (W+1) → Bool) :
    decode (W+1) bs / 2 = decode W (fun i => bs i.succ) := by
  simp only [decode]
  cases bs 0 <;> simp; omega

private theorem low_decode (W : ℕ) (bs : Fin (W+1) → Bool) :
    decode (W+1) bs % 2 = (bs 0).toNat := by
  simp only [decode]; cases bs 0 <;> simp

private theorem portLow (d W : ℕ) (bs : Fin d → Fin (W+1) → Bool) :
    lowCount (bitValues d (W+1) bs) ≤ 1 ↔
       ∀ i j : Fin d, i<j → bs i 0 = true → bs j 0 = false := by
  have count : lowCount (bitValues d (W+1) bs) = (Finset.univ.filter (fun i => bs i 0 = true)).card := by
    unfold lowCount bitValues
    rw [List.map_map]
    change ((List.finRange d).map (fun i => decode (W+1) (bs i)%2)).sum = _
    simp only [low_decode]
    rw [index_sum (List.finRange d) _ (List.nodup_finRange d)]
    have all : (List.finRange d).toFinset=Finset.univ := by ext; simp
    rw [all]
    have flag (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl
    simp [flag,Finset.sum_boole]
  rw [count,Finset.card_le_one]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro one i j lt hi
    cases hj : bs j 0
    · rfl
    · exact False.elim (lt.ne (one i hi j hj))
  · intro none i hi j hj
    rcases lt_trichotomy i j with a|a|a
    · exact False.elim (by have := none i j a hi; simp_all)
    · exact a
    · exact False.elim (by have := none j i a hj; simp_all)

theorem carryFree_ports (d W : ℕ) (bs : Fin d → Fin W → Bool) :
    carryFree W (bitValues d W bs) = true ↔
      ∀ k : Fin W, ∀ i j : Fin d, i<j → bs i k=true → bs j k=false := by
  induction W with
  | zero => simp [carryFree]
  | succ W ih =>
    have halves : halveAll (bitValues d (W+1) bs) = bitValues d W (fun i k=>bs i k.succ) := by
      unfold halveAll bitValues
      rw [List.map_map]
      apply List.map_congr_left
      exact fun i _ => halve_decode W (bs i)
    rw [carryFree,Bool.and_eq_true,decide_eq_true_eq,portLow,halves,ih,Fin.forall_fin_succ]

theorem pascal_ports (d W : ℕ) (bs : Fin d → Fin W → Bool) :
    ways (fun i => decode W (bs i)) % 2 = 1 ↔
      ∀ k : Fin W, ∀ i j : Fin d, i<j → bs i k=true → bs j k=false := by
  have h := to_list_ways (List.finRange d) (fun i => decode W (bs i)) (List.nodup_finRange d)
  have univ : (List.finRange d).toFinset=Finset.univ := by ext; simp
  rw [univ] at h
  change listWays (bitValues d W bs)=ways (fun i => decode W (bs i)) at h
  rw [←h,lucas_bits_of_length W _ (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    exact decode_bound W (bs i))]
  simpa only [Bool.toNat_eq_one] using carryFree_ports d W bs

end PascalGrid
namespace PascalGrid

open CutVerification
open CutVerification.Grid (Point Step top)

private def coord {d m : ℕ} (p : Point d m) : Fin d → ℕ := fun i => (p i).val

private def parent {d m : ℕ} (p : Point d m) (j : Fin d) : Point d m :=
  Function.update p j ⟨(p j).val-1,(Nat.sub_le _ _).trans_lt (p j).isLt⟩

private theorem parent_coord {d m : ℕ} (p : Point d m) (j : Fin d) :
    coord (parent p j) = down (coord p) j := by
  funext i; by_cases h : i=j <;> simp [parent,coord,down,h]

private def pred {d m : ℕ} (v : Point d m) := (Finset.univ.filter (fun i => 0 < (v i).val)).image (parent v)

private theorem parent_mem {d m : ℕ} (p : Point d m) (j : Fin d) (h : 0 < (p j).val) :
    parent p j ∈ pred p := Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩

private theorem parent_lt {d m : ℕ} (p : Point d m) (j : Fin d) (positive : 0 < (p j).val) :
    total (coord (parent p j)) < total (coord p) := by
  rw [parent_coord]
  unfold total down
  rw [Finset.sum_update_of_mem (Finset.mem_univ j),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j) (coord p)]
  change (p j).val-1+_ < (p j).val+_
  omega

def graph (d m : ℕ) : DAG (Point d m) ℕ where
  rank := fun v => total (coord v)
  pred := pred
  pred_lt := by
    rintro v p h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact parent_lt p j (Finset.mem_filter.mp hj).2
  step p env := if total (coord p)=0 then 1 else
    (∑ j : Fin d, if h : 0 < (p j).val then env ⟨parent p j,parent_mem p j h⟩ else 0) % 2

private theorem zero_ways {α : Type*} [Fintype α] (x : α → ℕ) (h : total x=0) : ways x=1 := by
  have ev : ∀ a, x a=0 := by
    intro a
    have bound : x a ≤ total x := Finset.single_le_sum (fun a _ => Nat.zero_le (x a)) (Finset.mem_univ a)
    omega
  simp [ways,Nat.multinomial,ev]

theorem labels_solve (d m : ℕ) : Solves (graph d m) (fun p => ways (coord p)%2) := by
  intro p
  by_cases zero : total (coord p)=0
  · simp [graph,zero,zero_ways _ zero]
  · change ways (coord p)%2 = _
    simp only [graph,zero,ite_false]
    rw [pascal (coord p) (by omega)]
    apply Nat.ModEq.sum
    intro j _
    by_cases pos : 0 < (p j).val
    · simp only [coord,pos,ite_true,parent_coord]
      exact (Nat.mod_modEq _ _).symm
    · simp [coord,pos,Nat.ModEq.refl]

/-- The same grid topology admits a fixed reader of its exact Pascal labels. -/
theorem compact_solution (d m W : ℕ) (bound : d*m < 2^W) :
    Solves (graph d m) (fun p => reader W (coord p) (List.finRange d)) := by
  have each (p : Point d m) : reader W (coord p) (List.finRange d) = ways (coord p)%2 := by
    refine reader_grid d W _ (lt_of_le_of_lt ?_ bound)
    calc
      total (coord p) ≤ ∑ _i : Fin d, m := Finset.sum_le_sum fun i _ => (p i).isLt.le
      _ = d*m := by simp
  simpa only [each] using labels_solve d m

private theorem grid_edges {d m : ℕ} {u v : Point d m} (h : Step u v) : v ∈ (graph d m).pred u := by
  obtain ⟨j,hj⟩ := h
  have hi := hj j
  simp only [ite_true] at hi
  have equal : parent u j = v := by
    funext i
    apply Fin.ext
    by_cases e : i=j
    · subst i; simp [parent,hi]
    · simpa [parent,e] using hj i
  exact equal ▸ parent_mem u j (by omega)

/-- Explicit cut/opening bounds and a uniform arithmetic label reader for the
same XOR problem. B is a count of disclosed vertex labels. -/
theorem easy_labels_large_openings (d a r W B : ℕ) (hm : 0 < a+r) (width : d*(a+r)<2^W)
    (S : Scheme (graph d (a+r))) (out : top (d:=d) hm ∈ S.cut)
    (opened : ∀ c, (S.region c).card ≤ B) :
    Solves (graph d (a+r)) (fun p => reader W (coord p) (List.finRange d)) ∧
    a^d*(r+1)^d ≤ a^d*B+(r+1)^d*(d*r+1)*S.cut.card := by
  refine ⟨compact_solution _ _ _ width,?_⟩
  apply Grid.cut_count d a r B S ⟨_,out⟩ (fun _ _ e=>grid_edges e) _ opened
  intro q
  have incl : @Step d (a+r) ≤ (fun u v => v ∈ (graph d (a+r)).pred u) := fun _ _ e => grid_edges e
  exact Relation.ReflTransGen.mono incl _ _ (Grid.top_reaches hm (Grid.start r q))

end PascalGrid
namespace PascalCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.Majority567Upper

private def three (acc i j : ℕ) : List Gate :=
  [⟨.and,[i,j]⟩,⟨.not,[acc+1]⟩,⟨.and,[acc,acc+2]⟩]

private def code {n : ℕ} (acc : ℕ) : List (Fin n × Fin n) → List Gate
  | [] => []
  | p::ps => three acc p.1.val p.2.val ++ code (acc+3) ps

private theorem code_len {n : ℕ} (acc : ℕ) (ps : List (Fin n × Fin n)) : (code acc ps).length=3*ps.length := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih => simp [code,three,ih,Nat.mul_succ,Nat.add_comm]; omega

private theorem one_step (w : List Bool) (acc i j : ℕ) (hw : w.length=acc+1) :
    (run (three acc i j) w).getD (acc+3) false =
      (w.getD acc false && !(w.getD i false && w.getD j false)) := by
  let a := w.getD i false && w.getD j false
  have e1 : step w ⟨.and,[i,j]⟩ = w++[a] := by simp [step,GateOp.eval,a]
  have f1 : (w++[a]).getD (acc+1) false = a := hw ▸ getD_snoc_eq w a
  have e2 : step (w++[a]) ⟨.not,[acc+1]⟩ = (w++[a])++[!a] := by
    change (w++[a])++[!((w++[a]).getD (acc+1) false)] = _
    rw [f1]
  have l : (w++[a]).length=acc+2 := by simp [hw]
  have f2 : ((w++[a])++[!a]).getD (acc+2) false = !a := l ▸ getD_snoc_eq (w++[a]) (!a)
  have fa : ((w++[a])++[!a]).getD acc false = w.getD acc false := by
    rw [getD_snoc_lt _ _ _ (by omega),getD_snoc_lt _ _ _ (by omega)]
  have val : GateOp.and.eval ([acc,acc+2].map (fun i => ((w++[a])++[!a]).getD i false)) =
      (w.getD acc false && !a) := by
    change (((w++[a])++[!a]).getD acc false && (((w++[a])++[!a]).getD (acc+2) false && true)) = _
    rw [f2,fa]; simp
  change (step (step (step w _) _) _).getD (acc+3) false = _
  rw [e1,e2]
  have len : ((w++[a])++[!a]).length=acc+3 := by simp [hw]
  change (((w++[a])++[!a])++[_]).getD (acc+3) false = _
  rw [←len,getD_snoc_eq]
  exact val

private theorem scan_eval {n : ℕ} (ps : List (Fin n × Fin n)) (w : List Bool) (acc : ℕ)
    (hw : w.length=acc+1) (hb : n≤acc) :
    (run (code acc ps) w).getD (acc+3*ps.length) false =
      (w.getD acc false && ps.all (fun p => !(w.getD p.1.val false && w.getD p.2.val false))) := by
  induction ps generalizing w acc with
  | nil => simp [code,run]
  | cons p ps ih =>
    let gs := three acc p.1.val p.2.val
    have len : (run gs w).length=acc+3+1 := by rw [run_length,hw]; simp [gs,three]
    have keep (i : Fin n) : (run gs w).getD i.val false = w.getD i.val false :=
      run_getD_of_lt _ _ _ (by have := i.isLt; omega)
    have first := one_step w acc p.1.val p.2.val hw
    simp only [code,run_append,List.length_cons,List.all_cons]
    rw [show acc+3*(ps.length+1) = acc+3+3*ps.length by omega,
      ih (run gs w) (acc+3) len (by omega),first]
    simp only [keep,Bool.and_assoc]

private def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem safe {n : ℕ} (acc : ℕ) (ps : List (Fin n × Fin n)) : ∀ g∈code acc ps, allowed g := by
  induction ps generalizing acc with
  | nil => simp [code]
  | cons p ps ih =>
    intro g hg
    rcases List.mem_append.mp hg with h|h
    · simp [three] at h
      rcases h with rfl|rfl|rfl <;> simp [allowed]
    · exact ih _ _ h

theorem exclude_pairs {n : ℕ} (ps : List (Fin n × Fin n)) :
    HasCircuitSize n (fun x => ps.all (fun p => !(x p.1 && x p.2))) (3*ps.length+1) := by
  let st : Gate := ⟨.and,[]⟩
  let C : Circuit := ⟨st::code n ps,n+3*ps.length⟩
  refine ⟨C,?_,?_,?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl|h
    · simp [st]
    · exact safe _ _ _ h
  · simp [C,Circuit.size,code_len]
  · intro x
    let w := List.ofFn x
    have lens : w.length=n := List.length_ofFn
    have read (i : Fin n) : (w++[true]).getD i.val false=x i := by
      rw [getD_snoc_lt _ _ _ (by rw [lens]; exact i.isLt)]
      exact getD_ofFn _ _ _
    have truth : (w++[true]).getD n false = true := lens ▸ getD_snoc_eq w true
    change (run (code n ps) (step w st)).getD (n+3*ps.length) false = _
    have initial : step w st=w++[true] := rfl
    rw [initial,scan_eval _ _ _ (by simp [lens]) (le_refl _),truth]
    simp only [Bool.true_and,read]

end PascalCircuit
namespace PascalCircuit

open PEqualNP.MetaComplexity

private def pairs (d W : ℕ) : List (Fin (d*W) × Fin (d*W)) :=
  (List.finRange W).flatMap (fun k =>
    (List.finRange d).flatMap (fun i =>
      ((List.finRange d).filter (fun j => decide (i<j))).map
        (fun j => (finProdFinEquiv (i,k),finProdFinEquiv (j,k)))))

private theorem len_flat {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    have := h x
    omega

private theorem num_pairs (d W : ℕ) : (pairs d W).length ≤ W*(d*d) := by
  unfold pairs
  have one (k : Fin W) (i : Fin d) :
      (((List.finRange d).filter (fun j => decide (i<j))).map
        (fun j => (finProdFinEquiv (i,k),finProdFinEquiv (j,k)))).length ≤ d := by
    rw [List.length_map]
    exact (List.length_filter_le ..).trans_eq (List.length_finRange ..)
  have two (k : Fin W) := len_flat (List.finRange d) _ d (one k)
  simpa only [List.length_finRange] using len_flat (List.finRange W) _ (d*d)
    (fun k => by simpa only [List.length_finRange] using two k)

private theorem pair_mem {d W : ℕ} (a b : Fin (d*W)) :
    (a,b) ∈ pairs d W ↔ ∃ (k : Fin W) (i j : Fin d), i<j ∧ finProdFinEquiv (i,k)=a ∧ finProdFinEquiv (j,k)=b := by
  unfold pairs
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp h
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hk
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp hi
    exact ⟨k,i,j,of_decide_eq_true (List.mem_filter.mp hj).2,congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  · rintro ⟨k,i,j,lt,rfl,rfl⟩
    refine List.mem_flatMap.mpr ⟨k,List.mem_finRange _,List.mem_flatMap.mpr ⟨i,List.mem_finRange _,?_⟩⟩
    exact List.mem_map.mpr ⟨j,List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true lt⟩,rfl⟩

private theorem accepted (d W : ℕ) (x : Fin (d*W) → Bool) :
    (pairs d W).all (fun p => !(x p.1 && x p.2)) = true ↔
    ∀ k : Fin W, ∀ i j : Fin d, i<j → x (finProdFinEquiv (i,k))=true → x (finProdFinEquiv (j,k))=false := by
  rw [List.all_eq_true]
  constructor
  · intro h k i j lt hi
    have ok := h _ ((pair_mem _ _).mpr ⟨k,i,j,lt,rfl,rfl⟩)
    simpa [hi] using ok
  · rintro h ⟨a,b⟩ mem
    obtain ⟨k,i,j,lt,rfl,rfl⟩ := (pair_mem _ _).mp mem
    have ok := h k i j lt
    cases hi : x (finProdFinEquiv (i,k)) <;> simp_all

/-- The d-dimensional parity-Pascal label has a fan-in-two De Morgan circuit
on the dW binary coordinate inputs. -/
theorem grid_bit_circuit (d W : ℕ) :
    HasCircuitSize (d*W) (fun x => decide (PascalGrid.ways (fun i =>
      PascalGrid.decode W (fun k => x (finProdFinEquiv (i,k)))) % 2 = 1)) (3*(W*(d*d))+1) := by
  have eq : (fun x : Fin (d*W) → Bool => (pairs d W).all (fun p => !(x p.1 && x p.2))) =
      (fun x => decide (PascalGrid.ways (fun i => PascalGrid.decode W
        (fun k => x (finProdFinEquiv (i,k)))) % 2 = 1)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact (accepted d W x).trans (PascalGrid.pascal_ports d W (fun i k => x (finProdFinEquiv (i,k)))).symm
  obtain ⟨C,shape,size,ev⟩ := eq ▸ exclude_pairs (pairs d W)
  exact ⟨C,shape,size.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (num_pairs d W)) 1),ev⟩

end PascalCircuit
namespace PascalCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CutVerification

private def bitsOf (W n : ℕ) (k : Fin W) := decide (n / 2^k.val % 2 = 1)

private theorem decode_bits (W n : ℕ) (h : n < 2^W) : PascalGrid.decode W (bitsOf W n) = n := by
  induction W generalizing n with
  | zero =>
    have : n=0 := by simpa using h
    exact this.symm
  | succ W ih =>
    have lower : n/2 < 2^W := by rw [pow_succ] at h; omega
    have tail : (fun i : Fin W => bitsOf (W+1) n i.succ) = bitsOf W (n/2) := by
      funext i
      simp [bitsOf,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm]
    rw [PascalGrid.decode,tail,ih _ lower]
    by_cases b : n%2=1 <;> simp [bitsOf,b] <;> omega

def gridInput {d m : ℕ} (W : ℕ) (p : CutVerification.Grid.Point d m) (i : Fin (d*W)) : Bool :=
  let c := finProdFinEquiv.symm i
  bitsOf W (p c.1).val c.2

/-- The exact labels of this physical fan-in-two circuit solve the XOR grid.
The second part applies to every explicit cut/opening scheme on that same grid. -/
theorem finite_separation (d a r W : ℕ) (hm : 0<a+r) (width : a+r ≤ 2^W) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 3*(W*(d*d))+1 ∧
      Solves (PascalGrid.graph d (a+r)) (fun p => (C.eval (List.ofFn (gridInput W p))).toNat) ∧
      ∀ (S : Scheme (PascalGrid.graph d (a+r))) (B : ℕ), Grid.top (d:=d) hm ∈ S.cut →
        (∀ c, (S.region c).card ≤ B) → a^d*(r+1)^d ≤ a^d*B+(r+1)^d*(d*r+1)*S.cut.card := by
  obtain ⟨C,shape,size,eval⟩ := grid_bit_circuit d W
  refine ⟨C,shape,size,?_,?_⟩
  · have labels (p : Grid.Point d (a+r)) :
        (C.eval (List.ofFn (gridInput W p))).toNat = PascalGrid.ways (PascalGrid.coord p)%2 := by
      rw [eval]
      have coordinates (i : Fin d) :
          PascalGrid.decode W (fun k => gridInput W p (finProdFinEquiv (i,k))) = (p i).val := by
        simp only [gridInput,Equiv.symm_apply_apply]
        exact decode_bits W (p i).val ((p i).isLt.trans_le width)
      simp only [coordinates]
      change (decide (PascalGrid.ways (PascalGrid.coord p)%2=1)).toNat = _
      by_cases b : PascalGrid.ways (PascalGrid.coord p)%2=1 <;> simp [b]; omega
    simpa only [labels] using PascalGrid.labels_solve d (a+r)
  · intro S B out opened
    apply Grid.cut_count d a r B S ⟨_,out⟩ (fun _ _ e=>PascalGrid.grid_edges e) _ opened
    intro q
    have incl : @Grid.Step d (a+r) ≤ (fun u v => v ∈ (PascalGrid.graph d (a+r)).pred u) :=
      fun _ _ e => PascalGrid.grid_edges e
    exact Relation.ReflTransGen.mono incl _ _ (Grid.top_reaches hm (Grid.start r q))

end PascalCircuit

namespace StackLayout

abbrev Point (d m : ℕ) := Fin d → Fin m

def reflect (B a u : ℕ) := if a % 2 = 0 then u else B-1-u

def rank {m : ℕ} : (d : ℕ) → Point d m → ℕ
  | 0,_ => 0
  | d+1,p => (p 0).val*m^d + reflect (m^d) (p 0).val (rank d (fun i => p i.succ))

private theorem reflect_lt {B a u : ℕ} (hu : u<B) : reflect B a u < B := by
  unfold reflect
  split <;> omega

private theorem block_lt {a b B i j : ℕ} (hab : a < b) (hi : i<B) :
    a*B+i < b*B+j := by
  have h := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hab)
  rw [Nat.succ_mul] at h
  omega

theorem rank_lt {m : ℕ} (d : ℕ) (p : Point d m) : rank d p < m^d := by
  induction d with
  | zero => simp [rank]
  | succ d ih =>
    rw [rank,pow_succ,Nat.mul_comm (m^d)]
    exact (block_lt (j:=0) (p 0).isLt (reflect_lt (ih _))).trans_le (by simp)

private theorem by_head {d m : ℕ} {p q : Point (d+1) m} (h : p 0 < q 0) :
    rank (d+1) p < rank (d+1) q := by
  apply block_lt h
  exact reflect_lt (rank_lt _ _)

theorem rank_inj {m : ℕ} (d : ℕ) : Function.Injective (rank (m:=m) d) := by
  induction d with
  | zero => intro _ _ _; funext i; exact i.elim0
  | succ d ih =>
    intro p q eq
    have h : p 0 = q 0 := by
      rcases lt_trichotomy (p 0) (q 0) with a|a|a
      · exact False.elim ((by_head a).ne eq)
      · exact a
      · exact False.elim ((by_head a).ne eq.symm)
    have e : rank d (fun i => p i.succ) = rank d (fun i => q i.succ) := by
      simp only [rank,h,Nat.add_right_inj] at eq
      unfold reflect at eq
      split at eq
      · exact eq
      · have := rank_lt d (fun i => p i.succ)
        have := rank_lt d (fun i => q i.succ)
        omega
    funext i
    exact Fin.cases h (fun j => congrFun (ih e) j) i

def Link {d m : ℕ} (i : Fin d) (p q : Point d m) : Prop :=
  (q i).val = (p i).val+1 ∧ ∀ j, j ≠ i → p j=q j

private theorem tail_link {d m : ℕ} {i : Fin d} {p q : Point (d+1) m} (h : Link i.succ p q) :
    Link i (fun j => p j.succ) (fun j => q j.succ) :=
  ⟨h.1, fun _ hj => h.2 _ (fun e => hj (Fin.succ_injective _ e))⟩

/-- Increasing an axis increases time whenever all outer coordinates are even. -/
theorem rank_link {m : ℕ} (d : ℕ) (i : Fin d) (p q : Point d m) (link : Link i p q)
    (even : ∀ j, j < i → (p j).val % 2 = 0) : rank d p < rank d q := by
  induction d with
  | zero => exact i.elim0
  | succ d ih =>
    cases i using Fin.cases with
    | zero => exact by_head (show (p 0).val < (q 0).val by have := link.1; omega)
    | succ i =>
      have h0 := link.2 0 (Fin.succ_ne_zero i).symm
      have he := even 0 (Fin.succ_pos i)
      have ht := ih i _ _ (tail_link link) (fun j hj => even j.succ (Fin.succ_lt_succ_iff.mpr hj))
      simp only [rank,←h0,reflect,he,ite_true,Nat.add_lt_add_iff_left,ht]

def Cross (a b c d : ℕ) : Prop :=
  (min a b < min c d ∧ min c d < max a b ∧ max a b < max c d) ∨
  (min c d < min a b ∧ min a b < max c d ∧ max c d < max a b)

private theorem same_block {a b c d M B h : ℕ} (ha : a<B) (hb : b<B) (hc : c<B) (hd : d<B)
    (non : ¬ Cross a b c d) :
    ¬ Cross (M+reflect B h a) (M+reflect B h b) (M+reflect B h c) (M+reflect B h d) := by
  unfold Cross at *
  unfold reflect
  split <;> omega

private theorem separate {a b c d : ℕ} (h1 : a<c) (h2 : a<d) (h3 : b<c) (h4 : b<d) :
    ¬ Cross a b c d := by unfold Cross; omega

private theorem reverse_cross {a b c d : ℕ} : Cross a b c d ↔ Cross c d a b := or_comm

private theorem even_head_noncross {M B a x y : ℕ} (hx : x<B) (hy : y<B) :
    ¬ Cross (M+reflect B a x) (M+B+reflect B (a+1) x)
      (M+reflect B a y) (M+B+reflect B (a+1) y) := by
  unfold Cross reflect
  by_cases hp : a % 2=0
  · have hq : (a+1) % 2 ≠ 0 := by omega
    simp only [hp,hq,ite_true,ite_false]
    omega
  · have hq : (a+1) % 2 = 0 := by omega
    simp only [hp,hq,ite_true,ite_false]
    omega

/-- Axis and lower-coordinate parity partition the nearest-neighbor grid edges into
noncrossing classes in serpentine time order. -/
theorem pages {m : ℕ} (d : ℕ) (i : Fin d) (p q u v : Point d m)
    (pq : Link i p q) (uv : Link i u v) (color : (p i).val % 2 = (u i).val % 2) :
    ¬ Cross (rank d p) (rank d q) (rank d u) (rank d v) := by
  induction d with
  | zero => exact i.elim0
  | succ d ih =>
    cases i using Fin.cases with
    | zero =>
      have qp := pq.1
      have vu := uv.1
      rcases lt_trichotomy (p 0) (u 0) with low|same|high
      · have e : (q 0).val < (u 0).val := by change (p 0).val < (u 0).val at low; omega
        exact separate (by_head low) (by_head (show (p 0).val < (v 0).val by omega))
          (by_head e) (by_head (show (q 0).val < (v 0).val by omega))
      · have ep : (fun j : Fin d => q j.succ) = (fun j => p j.succ) :=
          funext fun j => (pq.2 j.succ (Fin.succ_ne_zero j)).symm
        have eu : (fun j : Fin d => v j.succ) = (fun j => u j.succ) :=
          funext fun j => (uv.2 j.succ (Fin.succ_ne_zero j)).symm
        simp only [rank,ep,eu,qp,vu,←same,Nat.succ_mul]
        exact even_head_noncross (rank_lt _ _) (rank_lt _ _)
      · have e : (v 0).val < (p 0).val := by change (u 0).val < (p 0).val at high; omega
        rw [reverse_cross]
        exact separate (by_head high) (by_head (show (u 0).val < (q 0).val by omega))
          (by_head e) (by_head (show (v 0).val < (q 0).val by omega))
    | succ i =>
      have hp := pq.2 0 (Fin.succ_ne_zero i).symm
      have hu := uv.2 0 (Fin.succ_ne_zero i).symm
      rcases lt_trichotomy (p 0) (u 0) with low|same|high
      · exact separate (by_head low) (by_head (hu ▸ low)) (by_head (hp ▸ low)) (by_head (hu ▸ hp ▸ low))
      · have prev := ih i _ _ _ _ (tail_link pq) (tail_link uv) color
        simp only [rank,←hp,←hu,←same]
        exact same_block (rank_lt _ _) (rank_lt _ _) (rank_lt _ _) (rank_lt _ _) prev
      · rw [reverse_cross]
        exact separate (by_head high) (by_head (hp ▸ high)) (by_head (hu ▸ high)) (by_head (hp ▸ hu ▸ high))

end StackLayout
namespace StackLayout

private theorem link_outside {d m : ℕ} {j : Fin d} {p q : Point d m} (h : Link j p q)
    {i : Fin d} (hi : i ≠ j) : q i = p i := (h.2 i hi).symm

/-- Within a fixed color, no point is shared by distinct grid edges. -/
theorem page_matching {d m : ℕ} {j : Fin d} {p q u v : Point d m} (pq : Link j p q)
    (uv : Link j u v) (color : (p j).val % 2 = (u j).val % 2)
    (meet : p=u ∨ p=v ∨ q=u ∨ q=v) : p=u ∧ q=v := by
  have hp := pq.1
  have hu := uv.1
  have eq : p j = u j := by
    apply Fin.ext
    rcases meet with e|e|e|e
    · rw [e]
    · have := congrArg Fin.val (congrFun e j); omega
    · have := congrArg Fin.val (congrFun e j); omega
    · have := congrArg Fin.val (congrFun e j); omega
  have outside (i : Fin d) (hne : i≠j) : p i=u i := by
    have a := pq.2 i hne
    have b := uv.2 i hne
    rcases meet with e|e|e|e <;> cases e <;> simp_all
  have all : p=u := funext fun i => by by_cases h : i=j; exact h ▸ eq; exact outside i h
  refine ⟨all,funext fun i => ?_⟩
  by_cases h : i=j
  · subst i
    apply Fin.ext
    rw [hp,hu,eq]
  · exact (pq.2 i h).symm.trans ((outside i h).trans (uv.2 i h))

def advanceEdge {d m : ℕ} (p q : Point d m) : Prop :=
  rank d q < rank d p ∧ ∃ j, Link j q p ∨ Link j p q

noncomputable def graph (d m : ℕ) : CutVerification.DAG (Point d m) Unit := by
  classical
  exact {
    rank := rank d
    pred := fun u => Finset.univ.filter (advanceEdge u)
    pred_lt := fun h => (Finset.mem_filter.mp h).2.1
    step := fun _ _ => ()
  }

private theorem pred_eq {d m : ℕ} (u v : Point d m) :
    v ∈ (graph d m).pred u ↔ advanceEdge u v := by
  classical
  simp [graph]

def twice {d m : ℕ} (p : Point d m) : Point d (2*m) := fun i => ⟨2*(p i).val,by have := (p i).isLt; omega⟩

private def middle {d m : ℕ} (v : Point d m) (j : Fin d) : Point d (2*m) :=
  Function.update (twice v) j ⟨2*(v j).val+1,by have := (v j).isLt; omega⟩

def halve {d m : ℕ} (p : Point d (2*m)) : Point d m := fun i => ⟨(p i).val/2,by have := (p i).isLt; omega⟩

private theorem halve_twice {d m : ℕ} (p : Point d m) : halve (twice p) = p := by
  funext i
  apply Fin.ext
  simp [halve,twice]

private theorem halve_middle {d m : ℕ} (p : Point d m) (j : Fin d) : halve (middle p j) = p := by
  funext i
  apply Fin.ext
  by_cases h : i=j
  · subst i
    simp [middle,halve]; omega
  · simp [middle,halve,twice,h]

noncomputable def even_embedding (d m : ℕ) : CutVerification.Grid.Embedding (d:=d) (m:=m) (graph d (2*m)) := by
  refine ⟨twice,?_,halve,?_⟩
  · intro p q e
    simpa only [halve_twice] using congrArg halve e
  · intro u v edge
    obtain ⟨j,step⟩ := edge
    have first : Link j (twice v) (middle v j) := by
      constructor
      · simp [middle,twice]
      · intro i hi; simp [middle,hi]
    have last : Link j (middle v j) (twice u) := by
      constructor
      · have e := step j
        simp only [ite_true] at e
        simp [middle,twice,e]
        omega
      · intro i hi
        have e := step i
        simp only [ite_eq_right hi,Nat.add_zero] at e
        apply Fin.ext
        simp [middle,twice,hi,e]
    have earlier₁ := rank_link d j _ _ first (fun i _ => by simp [twice])
    have earlier₂ := rank_link d j _ _ last (fun i hi => by simp [middle,twice,Fin.ne_of_lt hi])
    apply Relation.ReflTransGen.tail (b:=middle v j)
    · apply Relation.ReflTransGen.single
      exact ⟨(pred_eq _ _).mpr ⟨earlier₂,j,Or.inl last⟩,Or.inr (halve_middle v j)⟩
    · exact ⟨(pred_eq _ _).mpr ⟨earlier₁,j,Or.inl first⟩,Or.inr (halve_twice v)⟩

end StackLayout

namespace StackLayout

private theorem map_walk {U V : Type*} {r : U → U → Prop} {s : V → V → Prop}
    (f : U → V) (map : ∀ x y, r x y → Relation.ReflTransGen s (f x) (f y))
    {x y : U} (p : Relation.ReflTransGen r x y) : Relation.ReflTransGen s (f x) (f y) := by
  induction p with
  | refl => exact .refl
  | tail _ e h => exact h.trans (map _ _ e)

theorem snake_cut_count (d a r W : ℕ) (hm : 0<a+r)
    (S : CutVerification.Scheme (graph d (2*(a+r))))
    (out : twice (CutVerification.Grid.top (d:=d) hm) ∈ S.cut)
    (bound : ∀ c, (S.region c).card ≤ W) :
    a^d*(r+1)^d ≤ a^d*W+(r+1)^d*(d*r+1)*((d+1)*S.cut.card) := by
  let E := even_embedding d (a+r)
  apply CutVerification.Grid.embedded_count E S ⟨_,out⟩ _ bound
  intro q
  have grid := CutVerification.Grid.top_reaches hm (CutVerification.Grid.start r q)
  apply map_walk E.root _ grid
  intro x y e
  have wire := E.wire x y e
  have forget : (fun h v => v ∈ (graph d (2*(a+r))).pred h ∧ (E.owner v=x ∨ E.owner v=y)) ≤
      (fun h v => v ∈ (graph d (2*(a+r))).pred h) := fun _ _ a => a.1
  exact Relation.ReflTransGen.mono forget _ _ wire

end StackLayout

namespace StackMatching

/-- The key of an edge is the time at which its symbol was pushed. -/
structure Matching where
  stop : ℕ → Option ℕ
  older : ∀ i j, stop i = some j → i < j
  unique : ∀ i j e, stop i = some e → stop j = some e → i=j
  nested : ∀ i k j m, stop i = some j → stop k = some m → i<k → k<j → j<m → False

def Alive (M : Matching) (t i : ℕ) : Prop := i<t ∧ ∃ j, M.stop i = some j ∧ t≤j

/-- Pop a closing interval and then push any interval opening at this tick. Stack entries
are analytical timestamps. A physical push can carry any fixed-size payload instead. -/
noncomputable def run (M : Matching) : ℕ → List ℕ
  | 0 => []
  | t+1 => by
    classical
    let stack := run M t
    let rest := if ∃ i, M.stop i=some t then stack.tail else stack
    exact if (M.stop t).isSome then t::rest else rest

private theorem head_of_end (M : Matching) {t i : ℕ} (h : M.stop i=some t) (s : List ℕ)
    (sorted : s.Pairwise (·>·)) (live : ∀ j, j ∈ s ↔ Alive M t j) : ∃ ss, s=i::ss := by
  have here := (live i).mpr ⟨M.older _ _ h,t,h,Nat.le_refl t⟩
  cases s with
  | nil => simp at here
  | cons k ss =>
    by_cases eq : i=k
    · subst k; exact ⟨ss,rfl⟩
    · have ik : i<k := (List.pairwise_cons.mp sorted).1 i (List.mem_cons.mp here |>.resolve_left eq)
      obtain ⟨kt,m,hm,tm⟩ := (live k).mp List.mem_cons_self
      have mt : m ≠ t := fun em => eq (M.unique i k t h (em ▸ hm))
      exact False.elim (M.nested i k t m h hm ik kt (by omega))

private theorem survive (M : Matching) (t i : ℕ) :
    (Alive M t i ∧ M.stop i ≠ some t) ↔ i<t ∧ ∃ j, M.stop i=some j ∧ t+1≤j := by
  constructor
  · rintro ⟨⟨earlier,j,endj,bound⟩,hne⟩
    have h : j ≠ t := fun e => hne (e ▸ endj)
    exact ⟨earlier,j,endj,by omega⟩
  · rintro ⟨earlier,j,endj,bound⟩
    exact ⟨⟨earlier,j,endj,by omega⟩,by intro he; have := Option.some.inj (endj.symm.trans he); omega⟩

theorem correct (M : Matching) (t : ℕ) :
    (run M t).Pairwise (·>·) ∧ ∀ i, i ∈ run M t ↔ Alive M t i := by
  classical
  induction t with
  | zero => simp [run,Alive]
  | succ t ih =>
    let s := run M t
    let rest := if ∃ i, M.stop i=some t then s.tail else s
    have sorted : s.Pairwise (·>·) := ih.1
    have live (i : ℕ) : i∈s ↔ Alive M t i := ih.2 i
    have mid : rest.Pairwise (·>·) ∧ ∀ i, i∈rest ↔ Alive M t i ∧ M.stop i ≠ some t := by
      dsimp only [rest]
      split_ifs with endp
      · obtain ⟨i,hi⟩ := endp
        obtain ⟨ss,he⟩ := head_of_end M hi s sorted live
        rw [he] at sorted ⊢
        simp only [List.tail_cons,List.pairwise_cons] at sorted ⊢
        refine ⟨sorted.2,fun j => ?_⟩
        constructor
        · intro hj
          refine ⟨(live j).mp (he ▸ List.mem_cons_of_mem _ hj),?_⟩
          intro endj
          have eq := M.unique _ _ _ endj hi
          exact (Nat.ne_of_lt (sorted.1 _ hj)) eq
        · rintro ⟨here,different⟩
          have mem := (live j).mpr here
          rw [he] at mem
          exact (List.mem_cons.mp mem).resolve_left (fun e => different (e ▸ hi))
      · exact ⟨sorted,fun i => (live i).trans ⟨fun h => ⟨h,fun e => endp ⟨i,e⟩⟩,And.left⟩⟩
    have midlive (i : ℕ) : i∈rest ↔ i<t ∧ ∃ j, M.stop i=some j ∧ t+1≤j :=
      (mid.2 i).trans (survive M t i)
    change (if (M.stop t).isSome then t::rest else rest).Pairwise (·>·) ∧
      ∀ i, i ∈ (if (M.stop t).isSome then t::rest else rest) ↔ Alive M (t+1) i
    cases opening : M.stop t with
    | none =>
      simp only [Option.isSome_none,Bool.false_eq_true,ite_false]
      refine ⟨mid.1,fun i => ?_⟩
      rw [midlive]
      unfold Alive
      constructor
      · rintro ⟨lt,j,h,endj⟩; exact ⟨by omega,j,h,endj⟩
      · rintro ⟨lt,j,h,endj⟩
        have ne : i ≠ t := by intro eq; rw [eq,opening] at h; contradiction
        exact ⟨by omega,j,h,endj⟩
    | some k =>
      simp only [Option.isSome_some,ite_true,List.pairwise_cons,List.mem_cons]
      refine ⟨⟨fun i hi => ((midlive i).mp hi).1,mid.1⟩,fun i => ?_⟩
      rw [midlive]
      unfold Alive
      constructor
      · rintro (rfl|sm)
        · exact ⟨by omega,k,opening,M.older _ _ opening⟩
        · exact ⟨by omega,sm.2⟩
      · rintro ⟨lt,rest'⟩
        exact or_iff_not_imp_left.mpr (fun ne => ⟨by omega,rest'⟩)

theorem matching_pop (M : Matching) (i t : ℕ) (h : M.stop i=some t) :
    (run M t).head? = some i := by
  obtain ⟨ss,hs⟩ := head_of_end M h _ (correct M t).1 (correct M t).2
  rw [hs]; rfl

end StackMatching
namespace StackMatching

/-- An ordered page of pairwise disjoint, noncrossing interval endpoints. -/
structure Intervals (E : Type*) where
  beginPos : E → ℕ
  endPos : E → ℕ
  pos : ∀ e, beginPos e < endPos e
  begins : Function.Injective beginPos
  ends : Function.Injective endPos
  laminar : ∀ e f, beginPos e < beginPos f → beginPos f < endPos e → endPos e < endPos f → False

variable {E : Type*} (I : Intervals E)

noncomputable def Intervals.lastAt (I : Intervals E) (t : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ e, I.beginPos e=t then some (I.endPos h.choose) else none

private theorem intervals_spec (t j : ℕ) :
    I.lastAt t = some j ↔ ∃ e, I.beginPos e=t ∧ I.endPos e=j := by
  classical
  unfold Intervals.lastAt
  split
  next h =>
    constructor
    · exact fun eq => ⟨_,h.choose_spec,Option.some.inj eq⟩
    · rintro ⟨e,be,en⟩
      rw [I.begins (h.choose_spec.trans be.symm),en]
  next h =>
    constructor
    · intro impossible; contradiction
    · rintro ⟨_,be,_⟩; exact False.elim (h ⟨_,be⟩)

noncomputable def Intervals.matching (I : Intervals E) : Matching where
  stop := I.lastAt
  older _ _ h := by
    obtain ⟨e,rfl,rfl⟩ := (intervals_spec I _ _).mp h
    exact I.pos e
  unique i j t hi hj := by
    obtain ⟨e,rfl,ee⟩ := (intervals_spec I _ _).mp hi
    obtain ⟨f,rfl,ff⟩ := (intervals_spec I _ _).mp hj
    exact congrArg I.beginPos (I.ends (ee.trans ff.symm))
  nested i k j m p q := by
    obtain ⟨e,rfl,rfl⟩ := (intervals_spec I _ _).mp p
    obtain ⟨f,rfl,rfl⟩ := (intervals_spec I _ _).mp q
    exact I.laminar e f

theorem page_pop (e : E) :
    (run I.matching (I.endPos e)).head? = some (I.beginPos e) :=
  matching_pop _ _ _ ((intervals_spec I _ _).mpr ⟨e,rfl,rfl⟩)

end StackMatching
namespace StackLayout

abbrev Edges (d m : ℕ) (j : Fin d) (b : Fin 2) :=
  {pq : Point d m × Point d m // Link j pq.1 pq.2 ∧ (pq.1 j).val % 2 = b.val}

private def opens {d m : ℕ} {j b} (e : Edges d m j b) := min (rank d e.1.1) (rank d e.1.2)
private def closes {d m : ℕ} {j b} (e : Edges d m j b) := max (rank d e.1.1) (rank d e.1.2)

private theorem edge_touch {d m : ℕ} {j b} {e f : Edges d m j b} {x : ℕ}
    (he : x=rank d e.1.1 ∨ x=rank d e.1.2) (hf : x=rank d f.1.1 ∨ x=rank d f.1.2) : e=f := by
  have coll : e.1.1=f.1.1 ∨ e.1.1=f.1.2 ∨ e.1.2=f.1.1 ∨ e.1.2=f.1.2 := by
    rcases he with he|he <;> rcases hf with hf|hf
    · exact .inl (rank_inj d (he.symm.trans hf))
    · exact .inr (.inl (rank_inj d (he.symm.trans hf)))
    · exact .inr (.inr (.inl (rank_inj d (he.symm.trans hf))))
    · exact .inr (.inr (.inr (rank_inj d (he.symm.trans hf))))
  have both := page_matching e.2.1 f.2.1 (e.2.2.trans f.2.2.symm) coll
  exact Subtype.ext (Prod.ext both.1 both.2)

private theorem open_endpoint {d m : ℕ} {j b} (e : Edges d m j b) :
    opens e=rank d e.1.1 ∨ opens e=rank d e.1.2 := by unfold opens; omega

private theorem close_endpoint {d m : ℕ} {j b} (e : Edges d m j b) :
    closes e=rank d e.1.1 ∨ closes e=rank d e.1.2 := by unfold closes; omega

private def pageIntervals (d m : ℕ) (j : Fin d) (b : Fin 2) :
    StackMatching.Intervals (Edges d m j b) where
  beginPos := opens
  endPos := closes
  pos e := by
    have ne : rank d e.1.1 ≠ rank d e.1.2 := by
      intro h
      have eq := congrArg Fin.val (congrFun (rank_inj d h) j)
      have step := e.2.1.1
      omega
    unfold opens closes
    omega
  begins e f h := edge_touch (open_endpoint e) (h ▸ open_endpoint f)
  ends e f h := edge_touch (close_endpoint e) (h ▸ close_endpoint f)
  laminar e f h1 h2 h3 := (pages d j _ _ _ _ e.2.1 f.2.1 (e.2.2.trans f.2.2.symm)) (Or.inl ⟨h1,h2,h3⟩)

/-- On each one of 2d stacks, popping the stack at the later end of any grid edge
reads exactly the timestamp pushed by the same edge at its earlier end. -/
theorem pop_reads_own_edge {d m : ℕ} (j : Fin d) (b : Fin 2) (e : Edges d m j b) :
    (StackMatching.run (pageIntervals d m j b).matching (max (rank d e.1.1) (rank d e.1.2))).head? =
      some (min (rank d e.1.1) (rank d e.1.2)) :=
  StackMatching.page_pop (pageIntervals d m j b) e

end StackLayout
namespace StackLayout.Wired

open CutVerification
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive Site (d m : ℕ) where
  | main (p : Point d m)
  | relay (p : Point d m) (j : Fin d)
  deriving DecidableEq

def cell {d m : ℕ} : Site d m → Point d m
  | .main p | .relay p _ => p

def location {d m : ℕ} : Site d m → Point d (2*m)
  | .main p => twice p
  | .relay p j => middle p j

private theorem location_cell {d m : ℕ} (s : Site d m) : halve (location s) = cell s := by
  cases s <;> simp [location,cell,halve_twice,halve_middle]

theorem different_sites {d m : ℕ} : Function.Injective (location (d:=d) (m:=m)) := by
  intro s t h
  have coarse := (location_cell s).symm.trans ((congrArg halve h).trans (location_cell t))
  cases s with
  | main p =>
    cases t with
    | main q => exact congrArg Site.main coarse
    | relay q j =>
      have same : p=q := coarse
      subst q
      have := congrArg Fin.val (congrFun h j)
      simp [location,middle,twice] at this
  | relay p j =>
    cases t with
    | main q =>
      have same : p=q := coarse
      subst q
      have := congrArg Fin.val (congrFun h j)
      simp [location,middle,twice] at this
    | relay q k =>
      have same : p=q := coarse
      subst q
      by_cases indices : j=k
      · rw [indices]
      · have := congrArg Fin.val (congrFun h j)
        simp [location,middle,twice,indices] at this

private def inputs {d m : ℕ} : Site d m → Finset (Site d m)
  | .relay p _ => {Site.main p}
  | .main p => (Finset.univ.filter (fun j => 0 < (p j).val)).image (fun j => Site.relay (PascalGrid.parent p j) j)

private theorem from_relay {d m : ℕ} (p : Point d m) (j : Fin d) (h : 0 < (p j).val) :
    Site.relay (PascalGrid.parent p j) j ∈ inputs (.main p) :=
  Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩

private theorem relation {d m : ℕ} {s t : Site d m} (p : t∈inputs s) :
    ∃ j : Fin d, Link j (location t) (location s) ∧ rank d (location t) < rank d (location s) := by
  cases s with
  | relay u j =>
    have eq : t=Site.main u := Finset.mem_singleton.mp p
    subst t
    have edge : Link j (twice u) (middle u j) :=
      ⟨by simp [middle,twice],fun i h=>by simp [middle,h]⟩
    have earlier := rank_link d j _ _ edge (fun i _=>by simp [twice])
    exact ⟨j,edge,earlier⟩
  | main u =>
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp p
    have pos := (Finset.mem_filter.mp hj).2
    change 0 < (u j).val at pos
    have edge : Link j (middle (PascalGrid.parent u j) j) (twice u) := by
      constructor
      · simp [middle,PascalGrid.parent,twice]; omega
      · intro i ne; simp [middle,PascalGrid.parent,twice,ne]
    have earlier := rank_link d j _ _ edge (fun i hi=>by simp [middle,twice,Fin.ne_of_lt hi])
    exact ⟨j,edge,earlier⟩

def graph (d m : ℕ) : DAG (Site d m) ℕ where
  rank s := rank d (location s)
  pred := inputs
  pred_lt h := by obtain ⟨_,_,e⟩ := relation h; exact e
  step
    | .relay p j,env => env ⟨.main p,Finset.mem_singleton_self _⟩
    | .main p,env => if PascalGrid.total (PascalGrid.coord p)=0 then 1 else
        (∑ j : Fin d, if h : 0 < (p j).val then env ⟨_,from_relay p j h⟩ else 0) % 2

theorem mirrored_labels {d m : ℕ} {F : Point d m → ℕ} (h : Solves (PascalGrid.graph d m) F) :
    Solves (graph d m) (fun s => F (cell s)) := by
  intro s
  cases s with
  | main p => exact h p
  | relay p j => rfl

private def embedding (d m : ℕ) : Grid.Embedding (d:=d) (m:=m) (graph d m) := by
  refine ⟨Site.main,(by intro _ _ e; exact Site.main.inj e),cell,?_⟩
  intro u v edge
  obtain ⟨j,h⟩ := edge
  have hj := h j
  simp only [ite_true] at hj
  have eq : PascalGrid.parent u j = v := by
    funext i; apply Fin.ext
    by_cases same : i=j
    · subst i; simp [PascalGrid.parent,hj]
    · simpa [PascalGrid.parent,same] using h i
  have relay := from_relay u j (by omega)
  rw [eq] at relay
  exact (Relation.ReflTransGen.single (b:=Site.relay v j) ⟨relay,Or.inr rfl⟩).tail
    ⟨Finset.mem_singleton_self _,Or.inr rfl⟩

/-- Every required Pascal edge, including each intermediate relay, corresponds to a physical
LIFO read at the receiving vertex. -/
theorem edges_pop {d m : ℕ} {s t : Site d m} (incoming : t ∈ (graph d m).pred s) :
    ∃ (j : Fin d) (b : Fin 2), (StackMatching.run (pageIntervals d (2*m) j b).matching
      (rank d (location s))).head? = some (rank d (location t)) := by
  obtain ⟨j,link,lt⟩ := relation incoming
  let b : Fin 2 := ⟨((location t) j).val % 2,Nat.mod_lt _ (by decide)⟩
  let e : Edges d (2*m) j b := ⟨(location t,location s),link,rfl⟩
  refine ⟨j,b,?_⟩
  simpa only [e,Nat.max_eq_right lt.le,Nat.min_eq_left lt.le] using pop_reads_own_edge j b e

/-- A short physical De Morgan circuit directly computes every live vertex in the
ordered stack schedule, while any explicit cut/opening scheme incurs the grid cost. -/
theorem stack_separation (d a r W : ℕ) (hm : 0<a+r) (width : a+r ≤ 2^W) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 3*(W*(d*d))+1 ∧
      Solves (graph d (a+r)) (fun s => (C.eval (List.ofFn (PascalCircuit.gridInput W (cell s)))).toNat) ∧
      ∀ (S : Scheme (graph d (a+r))) (B : ℕ), Site.main (Grid.top (d:=d) hm) ∈ S.cut →
        (∀ c, (S.region c).card ≤ B) →
        a^d*(r+1)^d ≤ a^d*B+(r+1)^d*(d*r+1)*((d+1)*S.cut.card) := by
  obtain ⟨C,shape,size,labels,_⟩ := PascalCircuit.finite_separation d a r W hm width
  refine ⟨C,shape,size,mirrored_labels labels,?_⟩
  intro S B out opened
  let E := embedding d (a+r)
  apply Grid.embedded_count E S ⟨_,out⟩ _ opened
  intro q
  apply map_walk E.root _ (Grid.top_reaches hm (Grid.start r q))
  intro u v e
  have forget : (fun x y => y ∈ (graph d (a+r)).pred x ∧ (E.owner y=u ∨ E.owner y=v)) ≤
      (fun x y => y ∈ (graph d (a+r)).pred x) := fun _ _ p => p.1
  exact Relation.ReflTransGen.mono forget _ _ (E.wire u v e)

end StackLayout.Wired

namespace StackStream

open Turing

/-- Rows contain one finite instruction per stack. Opcode 0 keeps the stack,
1 pops, 2 pushes false, and 3 pushes true. -/
abbrev Row (k : ℕ) := Fin k → Fin 4

abbrev Alphabet (k : ℕ) : Option (Fin k) → Type
  | none => Row k
  | some _ => Bool

abbrev State (k : ℕ) := Option (Row k)
abbrev Store (k : ℕ) := (i : Option (Fin k)) → List (Alphabet k i)

def memory {k : ℕ} (input : List (Row k)) (S : Fin k → List Bool) : Store k
  | none => input
  | some k => S k

def applyOne (op : Fin 4) (s : List Bool) : List Bool :=
  if op=0 then s else if op=1 then s.tail else (decide (op=3))::s

private def perform {k : ℕ} (j : Fin k) (q : TM2.Stmt (Alphabet k) Unit (State k)) :
    TM2.Stmt (Alphabet k) Unit (State k) :=
  .branch (fun r => decide (r.map (· j)=some 0)) q
    (.branch (fun r => decide (r.map (· j)=some 1)) (.pop (some j) (fun r _ => r) q)
      (.push (some j) (fun r => decide (r.map (· j)=some 3)) q))

private def rows {k : ℕ} : List (Fin k) → TM2.Stmt (Alphabet k) Unit (State k)
  | [] => .load (fun _ => none) (.goto (fun _ => ()))
  | i::is => perform i (rows is)

def bg (k : ℕ) : Unit → TM2.Stmt (Alphabet k) Unit (State k) := fun _ =>
  .pop none (fun _ a => a) (.branch Option.isSome (rows (List.finRange k)) .halt)

def machine (k : ℕ) : FinTM2 where
  K := Option (Fin k)
  k₀ := none
  k₁ := none
  Γ := Alphabet k
  Λ := Unit
  main := ()
  σ := State k
  initialState := none
  m := bg k

private theorem writeStack {k : ℕ} (i : Fin k) (input : List (Row k)) (S : Fin k → List Bool) (s : List Bool) :
    Function.update (memory input S) (some i) s = memory input (Function.update S i s) := by
  funext j
  cases j with
  | none => simp [Function.update,memory]
  | some j =>
    by_cases he : j=i
    · subst j; simp [Function.update,memory]
    · simp [Function.update,memory,he]

private theorem readInput {k : ℕ} (input input' : List (Row k)) (S : Fin k → List Bool) :
    Function.update (memory input S) none input' = memory input' S := by
  funext j; cases j <;> simp [Function.update,memory]

private theorem perform_ok {k : ℕ} (j : Fin k) (x : Row k) (xs : List (Row k)) (S : Fin k → List Bool)
    (q : TM2.Stmt (Alphabet k) Unit (State k)) :
    TM2.stepAux (perform j q) (some x) (memory xs S) =
    TM2.stepAux q (some x) (memory xs (Function.update S j (applyOne (x j) (S j)))) := by
  by_cases h0 : x j=0
  · simp [perform,applyOne,h0,TM2.stepAux]
  · by_cases h1 : x j=1
    · simp [perform,applyOne,h1,TM2.stepAux,writeStack,memory]
    · simp [perform,applyOne,h0,h1,TM2.stepAux,writeStack,memory]

private def updateCells {k : ℕ} (x : Row k) : List (Fin k) → (Fin k → List Bool) → (Fin k → List Bool)
  | [],S => S
  | i::is,S => updateCells x is (Function.update S i (applyOne (x i) (S i)))

private theorem update_spec {k : ℕ} (x : Row k) (is : List (Fin k)) (s : Fin k → List Bool) (nd : is.Nodup) (j : Fin k) :
    updateCells x is s j = if j ∈ is then applyOne (x j) (s j) else s j := by
  induction is generalizing s with
  | nil => simp [updateCells]
  | cons i is ih =>
    obtain ⟨notin,rest⟩ := List.nodup_cons.mp nd
    by_cases eq : j=i
    · subst j; simp [updateCells,ih _ rest,notin]
    · simp [updateCells,ih _ rest,eq]

private theorem rows_spec {k : ℕ} (x : Row k) (is : List (Fin k)) (xs : List (Row k)) (s : Fin k → List Bool) :
    TM2.stepAux (rows is) (some x) (memory xs s) =
      ⟨some (),none,memory xs (updateCells x is s)⟩ := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => rw [rows,perform_ok,ih]; rfl

def frame {k : ℕ} (xs : List (Row k)) (S : Fin k → List Bool) : (machine k).Cfg :=
  ⟨some (),none,memory xs S⟩

theorem executes {k : ℕ} (x : Row k) (xs : List (Row k)) (S : Fin k → List Bool) :
    (machine k).step (frame (x::xs) S) = some (frame xs (fun i => applyOne (x i) (S i))) := by
  have all : updateCells x (List.finRange k) S = fun i => applyOne (x i) (S i) := by
    funext i
    rw [update_spec x _ _ (List.nodup_finRange _)]
    simp
  change TM2.step (bg k) (frame (x::xs) S) = _
  simp [TM2.step,frame,bg,TM2.stepAux,readInput,rows_spec,memory,all]
  rfl

def execute {k : ℕ} (xs : List (Row k)) (S : Fin k → List Bool) := xs.foldl (fun s r i => applyOne (r i) (s i)) S

theorem executes_list {k : ℕ} (xs tail : List (Row k)) (S : Fin k → List Bool) :
    (flip bind (machine k).step)^[xs.length] (some (frame (xs++tail) S)) = some (frame tail (execute xs S)) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (flip bind (machine k).step)^[xs.length] ((machine k).step (frame (x::(xs++tail)) S)) = _
    rw [executes,ih]
    rfl

end StackStream
namespace StackStream

open Turing StackMatching

private noncomputable def token (M : Matching) (tag : ℕ → Bool) (t : ℕ) : Fin 4 := by
  classical
  exact if (M.stop t).isSome then (if tag t then 3 else 2)
    else if ∃ a, M.stop a=some t then 1 else 0

private theorem token_spec (M : Matching) (tag : ℕ → Bool) (t : ℕ)
    (distinct : (M.stop t).isSome → ¬∃ a, M.stop a=some t) :
    applyOne (token M tag t) ((run M t).map tag) = (run M (t+1)).map tag := by
  classical
  cases h : M.stop t with
  | none =>
    by_cases e : ∃ a, M.stop a=some t <;> simp [token,run,h,e,applyOne,List.map_tail]
  | some j =>
    have e := distinct (by simp [h])
    cases ht : tag t <;> simp [token,run,h,e,applyOne,ht]

variable {k : ℕ}
private noncomputable def word (ms : Fin k → Matching) (tag : Fin k → ℕ → Bool) (t : ℕ) : Row k :=
  fun i => token (ms i) (tag i) t

noncomputable def schedule (ms : Fin k → Matching) (tag : Fin k → ℕ → Bool) : ℕ → List (Row k)
  | 0 => []
  | t+1 => schedule ms tag t ++ [word ms tag t]

private theorem schedule_len (ms : Fin k → Matching) (tag : Fin k → ℕ → Bool) (t : ℕ) :
    (schedule ms tag t).length=t := by induction t <;> simp_all [schedule]

private theorem schedule_execute (ms : Fin k → Matching) (tag : Fin k → ℕ → Bool)
    (disjoint : ∀ i t, ((ms i).stop t).isSome → ¬∃ a, (ms i).stop a=some t) (t : ℕ) :
    execute (schedule ms tag t) (fun _=>[]) = fun i => (run (ms i) t).map (tag i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    rw [schedule]
    unfold execute at *
    rw [List.foldl_append,ih]
    exact token_spec _ _ t (disjoint i t)

private theorem input_frame (k : ℕ) (xs : List (Row k)) :
    initList (machine k) xs = frame xs (fun _=>[]) := by
  unfold initList frame
  congr 1
  funext j
  cases j with
  | none => rfl
  | some j => rfl

theorem actual_page_stacks (ms : Fin k → Matching) (tag : Fin k → ℕ → Bool)
    (disjoint : ∀ i t, ((ms i).stop t).isSome → ¬∃ a, (ms i).stop a=some t)
    (t : ℕ) (tail : List (Row k)) :
    (flip bind (machine k).step)^[t] (some (initList (machine k) (schedule ms tag t ++ tail))) =
      some (frame tail (fun i => (run (ms i) t).map (tag i))) := by
  rw [input_frame,←schedule_execute ms tag disjoint t]
  simpa only [schedule_len] using executes_list (schedule ms tag t) tail (fun _=>[])

end StackStream

namespace StackLayout

private theorem endpoint_separate {d m : ℕ} {j b} (e f : Edges d m j b) : opens e ≠ closes f := by
  intro h
  have eq := edge_touch (open_endpoint e) (h ▸ close_endpoint f)
  subst f
  exact ((pageIntervals d m j b).pos e).ne h

private theorem grid_disjoint {d m : ℕ} (j : Fin d) (b : Fin 2) (t : ℕ) :
    (((pageIntervals d m j b).matching).stop t).isSome →
       ¬∃ a, ((pageIntervals d m j b).matching).stop a=some t := by
  intro has ⟨a,close⟩
  let I := pageIntervals d m j b
  obtain ⟨b',end'⟩ := Option.isSome_iff_exists.mp has
  obtain ⟨e,et,_⟩ := (StackMatching.intervals_spec I t b').mp end'
  obtain ⟨f,_,ft⟩ := (StackMatching.intervals_spec I a t).mp close
  exact endpoint_separate e f (et.trans ft.symm)

noncomputable def stacked (d m : ℕ) (s : Fin (d*2)) : StackMatching.Matching :=
  let p := finProdFinEquiv.symm s
  (pageIntervals d m p.1 p.2).matching

theorem grid_on_machine (d m : ℕ) (tags : Fin (d*2) → ℕ → Bool)
    (t : ℕ) (tail : List (StackStream.Row (d*2))) :
    (flip bind (StackStream.machine (d*2)).step)^[t]
      (some (Turing.initList (StackStream.machine (d*2)) (StackStream.schedule (stacked d m) tags t ++ tail))) =
      some (StackStream.frame tail (fun i => (StackMatching.run (stacked d m i) t).map (tags i))) := by
  apply StackStream.actual_page_stacks
  intro i tick
  exact grid_disjoint (m:=m) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 tick

end StackLayout

namespace StackGates

open Turing

abbrev Bits (k : ℕ) := Fin k → Bool
/-- Each command first reads the current stack tips, applies a specified Boolean function,
and pushes its output on every stack marked for push. -/
abbrev Row (k : ℕ) := (Fin k → Fin 3) × (Bits k → Bool)
abbrev Alphabet (k : ℕ) : Option (Fin k) → Type
  | none => Row k
  | some _ => Bool

abbrev State (k : ℕ) := Option (Row k) × Bits k

abbrev Store (k : ℕ) := (i : Option (Fin k)) → List (Alphabet k i)

def memory {k : ℕ} (input : List (Row k)) (S : Fin k → List Bool) : Store k
  | none => input
  | some k => S k

def tips {k : ℕ} (S : Fin k → List Bool) : Bits k := fun i => (S i).head?.getD false

def applyOne (op : Fin 3) (bit : Bool) (s : List Bool) : List Bool :=
  if op=0 then s else if op=1 then s.tail else bit::s

private def blank (k : ℕ) : State k := (none,fun _=>false)

private def perform {k : ℕ} (j : Fin k) (q : TM2.Stmt (Alphabet k) Unit (State k)) :
    TM2.Stmt (Alphabet k) Unit (State k) :=
  .branch (fun r => decide (r.1.map (fun x=>x.1 j)=some 0)) q
    (.branch (fun r => decide (r.1.map (fun x=>x.1 j)=some 1)) (.pop (some j) (fun r _ => r) q)
      (.push (some j) (fun r => (r.1.map (fun x=>x.2 r.2)).getD false) q))

private def writes {k : ℕ} : List (Fin k) → TM2.Stmt (Alphabet k) Unit (State k)
  | [] => .load (fun _ => blank k) (.goto (fun _ => ()))
  | i::is => perform i (writes is)

private def reads {k : ℕ} : List (Fin k) → TM2.Stmt (Alphabet k) Unit (State k)
    → TM2.Stmt (Alphabet k) Unit (State k)
  | [],q => q
  | i::is,q => .peek (some i) (fun r x => (r.1, Function.update r.2 i (x.getD false))) (reads is q)

def bg (k : ℕ) : Unit → TM2.Stmt (Alphabet k) Unit (State k) := fun _ =>
  .pop none (fun r a => (a,r.2)) (.branch (fun r=>r.1.isSome)
    (reads (List.finRange k) (writes (List.finRange k))) .halt)

def machine (k : ℕ) : FinTM2 where
  K := Option (Fin k)
  k₀ := none
  k₁ := none
  Γ := Alphabet k
  Λ := Unit
  main := ()
  σ := State k
  initialState := blank k
  m := bg k

private theorem writeStack {k : ℕ} (i : Fin k) (input : List (Row k)) (S : Fin k → List Bool) (s : List Bool) :
    Function.update (memory input S) (some i) s = memory input (Function.update S i s) := by
  funext j
  cases j with
  | none => simp [Function.update,memory]
  | some j =>
    by_cases he : j=i
    · subst j; simp [Function.update,memory]
    · simp [Function.update,memory,he]

private theorem readInput {k : ℕ} (input input' : List (Row k)) (S : Fin k → List Bool) :
    Function.update (memory input S) none input' = memory input' S := by
  funext j; cases j <;> simp [Function.update,memory]

private theorem perform_ok {k : ℕ} (j : Fin k) (x : Row k) (xs : List (Row k)) (S : Fin k → List Bool)
    (b : Bits k) (q : TM2.Stmt (Alphabet k) Unit (State k)) :
    TM2.stepAux (perform j q) (some x,b) (memory xs S) =
    TM2.stepAux q (some x,b) (memory xs (Function.update S j (applyOne (x.1 j) (x.2 b) (S j)))) := by
  obtain ⟨ops,gate⟩ := x
  by_cases h0 : ops j=0
  · simp [perform,applyOne,h0,TM2.stepAux]
  · by_cases h1 : ops j=1
    · simp [perform,applyOne,h1,TM2.stepAux,writeStack,memory]
    · simp [perform,applyOne,h0,h1,TM2.stepAux,writeStack,memory]

private def updateCells {k : ℕ} (x : Row k) (b : Bits k) : List (Fin k) → (Fin k → List Bool) → (Fin k → List Bool)
  | [],S => S
  | i::is,S => updateCells x b is (Function.update S i (applyOne (x.1 i) (x.2 b) (S i)))

private theorem update_spec {k : ℕ} (x : Row k) (b : Bits k) (is : List (Fin k))
    (s : Fin k → List Bool) (nd : is.Nodup) (j : Fin k) :
    updateCells x b is s j = if j ∈ is then applyOne (x.1 j) (x.2 b) (s j) else s j := by
  induction is generalizing s with
  | nil => simp [updateCells]
  | cons i is ih =>
    obtain ⟨notin,rest⟩ := List.nodup_cons.mp nd
    by_cases eq : j=i
    · subst j; simp [updateCells,ih _ rest,notin]
    · simp [updateCells,ih _ rest,eq]

private theorem writes_spec {k : ℕ} (x : Row k) (b : Bits k) (is : List (Fin k))
    (xs : List (Row k)) (s : Fin k → List Bool) :
    TM2.stepAux (writes is) (some x,b) (memory xs s) =
      ⟨some (),blank k,memory xs (updateCells x b is s)⟩ := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => rw [writes,perform_ok,ih]; rfl

private def capture {k : ℕ} (f : Bits k) : List (Fin k) → Bits k → Bits k
  | [],b => b
  | i::is,b => capture f is (Function.update b i (f i))

private theorem capture_spec {k : ℕ} (f b : Bits k) (is : List (Fin k)) (j : Fin k) :
    capture f is b j = if j∈is then f j else b j := by
  induction is generalizing b with
  | nil => simp [capture]
  | cons i is ih =>
    by_cases eq : j=i <;> by_cases mem : j∈is <;> simp_all [capture]

private theorem reads_spec {k : ℕ} (x : Row k) (b : Bits k) (is : List (Fin k)) (xs : List (Row k))
    (s : Fin k → List Bool) (q : TM2.Stmt (Alphabet k) Unit (State k)) :
    TM2.stepAux (reads is q) (some x,b) (memory xs s) =
    TM2.stepAux q (some x,capture (tips s) is b) (memory xs s) := by
  induction is generalizing b with
  | nil => rfl
  | cons i is ih => exact ih (Function.update b i ((s i).head?.getD false))

def frame {k : ℕ} (xs : List (Row k)) (S : Fin k → List Bool) : (machine k).Cfg :=
  ⟨some (),blank k,memory xs S⟩

def next {k : ℕ} (x : Row k) (S : Fin k → List Bool) : Fin k → List Bool :=
  fun i => applyOne (x.1 i) (x.2 (tips S)) (S i)

theorem executes {k : ℕ} (x : Row k) (xs : List (Row k)) (S : Fin k → List Bool) :
    (machine k).step (frame (x::xs) S) = some (frame xs (next x S)) := by
  have all (b) : updateCells x b (List.finRange k) S = fun i => applyOne (x.1 i) (x.2 b) (S i) := by
    funext i; rw [update_spec x _ _ _ (List.nodup_finRange _)]; simp
  have read (b) : capture (tips S) (List.finRange k) b = tips S := by
    funext i; rw [capture_spec]; simp
  change TM2.step (bg k) (frame (x::xs) S) = _
  simp [TM2.step,frame,bg,TM2.stepAux,readInput,reads_spec,writes_spec,memory,blank,read,all]
  rfl

def execute {k : ℕ} (xs : List (Row k)) (S : Fin k → List Bool) := xs.foldl (fun s r => next r s) S

private theorem executes_list {k : ℕ} (xs tail : List (Row k)) (S : Fin k → List Bool) :
    (flip bind (machine k).step)^[xs.length] (some (frame (xs++tail) S)) = some (frame tail (execute xs S)) := by
  induction xs generalizing S with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (flip bind (machine k).step)^[xs.length] ((machine k).step (frame (x::(xs++tail)) S)) = _
    rw [executes,ih]
    rfl

theorem actual_run {k : ℕ} (xs tail : List (Row k)) :
    (flip bind (machine k).step)^[xs.length] (some (initList (machine k) (xs++tail))) =
      some (frame tail (execute xs (fun _=>[]))) := by
  have init : initList (machine k) (xs++tail) = frame (xs++tail) (fun _=>[]) := by
    unfold initList frame
    congr 1
    funext j
    cases j <;> rfl
  rw [init,executes_list]

end StackGates
namespace StackGates

open StackMatching

private noncomputable def command (M : Matching) (t : ℕ) : Fin 3 := by
  classical
  exact if (M.stop t).isSome then 2 else if ∃ a, M.stop a=some t then 1 else 0

noncomputable def contents {k : ℕ} (ms : Fin k → Matching) (bit : ℕ → Bool) (t : ℕ) : Fin k → List Bool :=
  fun i => (run (ms i) t).map bit

private noncomputable def instruction {k : ℕ} (ms : Fin k → Matching) (gate : ℕ → Bits k → Bool) (t : ℕ) : Row k :=
  (fun i => command (ms i) t,gate t)

noncomputable def program {k : ℕ} (ms : Fin k → Matching) (gate : ℕ → Bits k → Bool) : ℕ → List (Row k)
  | 0 => []
  | t+1 => program ms gate t ++ [instruction ms gate t]

private theorem program_len {k : ℕ} (ms : Fin k → Matching) (gate : ℕ → Bits k → Bool) (t : ℕ) :
    (program ms gate t).length=t := by induction t <;> simp_all [program]

private theorem next_stacks {k : ℕ} (ms : Fin k → Matching) (gate : ℕ → Bits k → Bool) (bit : ℕ → Bool) (t : ℕ)
    (correct : gate t (tips (contents ms bit t)) = bit t)
    (disjoint : ∀ i, ((ms i).stop t).isSome → ¬∃ a, (ms i).stop a=some t) :
    next (instruction ms gate t) (contents ms bit t) = contents ms bit (t+1) := by
  classical
  funext i
  unfold next
  change applyOne _ (gate t (tips (contents ms bit t))) _ = _
  rw [correct]
  cases h : (ms i).stop t with
  | none =>
    by_cases e : ∃ a, (ms i).stop a=some t <;>
      simp [instruction,command,run,contents,h,e,applyOne,List.map_tail]
  | some j =>
    have e := disjoint i (by simp [h])
    simp [instruction,command,run,contents,h,e,applyOne]

theorem program_run {k : ℕ} (ms : Fin k → Matching) (gate : ℕ → Bits k → Bool) (bit : ℕ → Bool)
    (correct : ∀ t, gate t (tips (contents ms bit t)) = bit t)
    (disjoint : ∀ i t, ((ms i).stop t).isSome → ¬∃ a, (ms i).stop a=some t)
    (t : ℕ) (tail : List (Row k)) :
    (flip bind (machine k).step)^[t] (some (Turing.initList (machine k) (program ms gate t ++ tail))) =
    some (frame tail (contents ms bit t)) := by
  have spec (n : ℕ) : execute (program ms gate n) (fun _=>[]) = contents ms bit n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [program]
      unfold execute at *
      rw [List.foldl_append,ih]
      exact next_stacks ms gate bit n (correct n) (fun i=>disjoint i n)
  simpa only [program_len,spec] using actual_run (program ms gate t) tail

end StackGates
namespace StackLayout.Wired

open CutVerification

abbrev tick {d m : ℕ} (s : Site d m) : ℕ := rank d (location s)

private theorem tick_inj {d m : ℕ} : Function.Injective (@tick d m) :=
  fun _ _ h=>different_sites (rank_inj _ h)

private noncomputable def atTick (d m u : ℕ) : Option (Site d m) := by
  classical
  exact if h : ∃ s : Site d m, tick s=u then some h.choose else none

private theorem at_site {d m : ℕ} (s : Site d m) : atTick d m (tick s)=some s := by
  classical
  have existsS : ∃ t : Site d m, tick t=tick s := ⟨s,rfl⟩
  simp only [atTick,dite_eq_left existsS]
  exact congrArg some (tick_inj existsS.choose_spec)

private theorem tip_page {d m : ℕ} {s t : Site d m} (e : t∈(graph d m).pred s) :
    ∃ k : Fin (d*2), (StackMatching.run (stacked d (2*m) k) (tick s)).head?=some (tick t) := by
  obtain ⟨j,b,h⟩ := edges_pop e
  let e : (Fin d × Fin 2) ≃ Fin (d*2) := finProdFinEquiv
  refine ⟨e (j,b),?_⟩
  change (StackMatching.run (pageIntervals d (2*m) (e.symm (e (j,b))).1 (e.symm (e (j,b))).2).matching _).head? = _
  rw [e.symm_apply_apply]
  exact h

private noncomputable def port {d m : ℕ} (s : Site d m) (p : (graph d m).pred s) : Fin (d*2) :=
  (tip_page p.property).choose

/-- A geometric instruction that selects the data dependency to read; it uses
only the graph operations and the incident edge pages. -/
noncomputable def gate (d m u : ℕ) (bits : StackGates.Bits (d*2)) : Bool :=
  match atTick d m u with
  | none => false
  | some s => decide ((graph d m).step s (fun p => (bits (port s p)).toNat) = 1)

noncomputable def payload {d m : ℕ} (value : Site d m → Bool) (u : ℕ) : Bool :=
  ((atTick d m u).map value).getD false

private theorem source_value {d m : ℕ} (value : Site d m → Bool) (s : Site d m) (p : (graph d m).pred s) :
    StackGates.tips (StackGates.contents (stacked d (2*m)) (payload value) (tick s)) (port s p) = value p := by
  have h := (tip_page p.property).choose_spec
  change (StackMatching.run (stacked d (2*m) (port s p)) (tick s)).head? = some (tick p.val) at h
  change (((StackMatching.run _ _).map (payload value)).head?).getD false = _
  rw [List.head?_map,h]
  simp [payload,at_site]

private theorem computed_payload {d m : ℕ} (value : Site d m → Bool)
    (correct : Solves (graph d m) (fun s=>(value s).toNat)) (u : ℕ) :
    gate d m u (StackGates.tips (StackGates.contents (stacked d (2*m)) (payload value) u)) = payload value u := by
  classical
  cases h : atTick d m u with
  | none => simp [gate,payload,h]
  | some s =>
    have eq : tick s=u := by
      unfold atTick at h
      split at h
      next has => exact Option.some.inj h ▸ has.choose_spec
      next => contradiction
    subst u
    simp only [gate,payload,h,Option.map_some,Option.getD_some,source_value]
    have ev := correct s
    change (value s).toNat = (graph d m).step s _ at ev
    rw [←ev]
    cases value s <;> decide

/-- A fixed finite multistack machine derives all written bits by applying the geometric
gate to the data stack tips. Its instruction word depends only on the grid parameters. -/
theorem machine_computes {d m : ℕ} (value : Site d m → Bool)
    (correct : Solves (graph d m) (fun s=>(value s).toNat))
    (u : ℕ) (tail : List (StackGates.Row (d*2))) :
    (flip bind (StackGates.machine (d*2)).step)^[u]
      (some (Turing.initList (StackGates.machine (d*2))
        (StackGates.program (stacked d (2*m)) (gate d m) u ++ tail))) =
    some (StackGates.frame tail (StackGates.contents (stacked d (2*m)) (payload value) u)) := by
  apply StackGates.program_run _ _ _ (computed_payload value correct)
  intro i t
  exact grid_disjoint (m:=2*m) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 t

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- All three bounds hold for the same concrete Pascal grid and the same labelling.
The instruction stack supplies the geometry; intermediate Pascal bits are computed
from previous stack contents. -/
theorem finite_machine_separation (d a r W : ℕ) (hm : 0<a+r) (width : a+r ≤ 2^W) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 3*(W*(d*d))+1 ∧
      (let val : Site d (a+r) → Bool := fun s=>C.eval (List.ofFn (PascalCircuit.gridInput W (cell s)))
       Solves (graph d (a+r)) (fun s=>(val s).toNat) ∧
       (∀ (u : ℕ) (tail : List (StackGates.Row (d*2))),
         (flip bind (StackGates.machine (d*2)).step)^[u]
           (some (Turing.initList (StackGates.machine (d*2))
             (StackGates.program (stacked d (2*(a+r))) (gate d (a+r)) u ++ tail))) =
         some (StackGates.frame tail (StackGates.contents (stacked d (2*(a+r))) (payload val) u))) ∧
       ∀ (S : Scheme (graph d (a+r))) (B : ℕ), Site.main (Grid.top (d:=d) hm) ∈ S.cut →
        (∀ c, (S.region c).card ≤ B) →
        a^d*(r+1)^d ≤ a^d*B+(r+1)^d*(d*r+1)*((d+1)*S.cut.card)) := by
  obtain ⟨C,shape,size,valid,lower⟩ := stack_separation d a r W hm width
  exact ⟨C,shape,size,valid,machine_computes _ valid,lower⟩

end StackLayout.Wired
namespace StackLayout

private theorem reflect_twice (B a u : ℕ) (hu : u<B) :
    reflect B a (reflect B a u) = u := by
  unfold reflect; split <;> omega

/-- Random access to the grid point at a given time, by d quotient/remainder pairs. -/
def pointAt {m : ℕ} : (d : ℕ) → Fin (m^d) → Point d m
  | 0,_ => Fin.elim0
  | d+1,t => by
    have cap : 0 < m^d := by
      have pos : 0 < m^(d+1) := Nat.zero_lt_of_lt t.isLt
      by_contra! h
      rw [pow_succ,show m^d=0 by omega,Nat.zero_mul] at pos
      omega
    have am : t.val / m^d < m := by
      apply (Nat.div_lt_iff_lt_mul cap).mpr
      simpa [pow_succ,Nat.mul_comm] using t.isLt
    let a : Fin m := ⟨t.val/m^d,am⟩
    let r : Fin (m^d) := ⟨reflect (m^d) a.val (t.val % m^d),reflect_lt (Nat.mod_lt _ cap)⟩
    exact Fin.cons a (pointAt d r)

private theorem rank_at {m : ℕ} (d : ℕ) (t : Fin (m^d)) : rank d (pointAt d t) = t.val := by
  induction d with
  | zero => have := t.isLt; simp [rank] at *; omega
  | succ d ih =>
    have cap : 0 < m^d := by
      have pos : 0 < m^(d+1) := Nat.zero_lt_of_lt t.isLt
      by_contra! h
      rw [pow_succ,show m^d=0 by omega,Nat.zero_mul] at pos
      omega
    simp only [pointAt,rank,Fin.cons_zero,Fin.cons_succ,ih]
    rw [reflect_twice _ _ _ (Nat.mod_lt _ cap)]
    exact Nat.div_add_mod' .. 

private def neighborUp {d m : ℕ} (j : Fin d) (p : Point d m) (h : (p j).val+1<m) : Point d m :=
  Function.update p j ⟨(p j).val+1,h⟩

private def neighborDown {d m : ℕ} (j : Fin d) (p : Point d m) : Point d m :=
  Function.update p j ⟨(p j).val-1,(Nat.sub_le _ _).trans_lt (p j).isLt⟩

private def localEdge {d m : ℕ} (j : Fin d) (b : Fin 2) (p : Point d m) : Option (Edges d m j b) :=
  if eq : (p j).val % 2 = b.val then
    if room : (p j).val+1<m then some ⟨(p,neighborUp j p room),by
      refine ⟨⟨by simp [neighborUp],fun i hi => by simp [neighborUp,hi]⟩,eq⟩⟩
    else none
  else if pos : 0 < (p j).val then some ⟨(neighborDown j p,p),by
    refine ⟨⟨by simp [neighborDown]; omega,fun i hi => by simp [neighborDown,hi]⟩,?_⟩
    simp [neighborDown]
    have := b.isLt
    omega⟩
  else none

private theorem local_touches {d m : ℕ} (j : Fin d) (b : Fin 2) (p : Point d m)
    (e : Edges d m j b) (h : localEdge j b p = some e) : p=e.1.1 ∨ p=e.1.2 := by
  unfold localEdge at h
  split at h <;> split at h
  · exact Or.inl (congrArg (fun e : Edges d m j b => e.1.1) (Option.some.inj h))
  · contradiction
  · exact Or.inr (congrArg (fun e : Edges d m j b => e.1.2) (Option.some.inj h))
  · contradiction

private theorem local_finds {d m : ℕ} {j b} (e : Edges d m j b) (p : Point d m)
    (meet : p=e.1.1 ∨ p=e.1.2) : localEdge j b p = some e := by
  have live : (localEdge j b p).isSome := by
    have he := e.2.1.1
    have col := e.2.2
    rcases meet with rfl|rfl
    · have room : (e.1.1 j).val+1<m := he ▸ (e.1.2 j).isLt
      simp [localEdge,col,room]
    · have pos : 0 < (e.1.2 j).val := by omega
      have odd : (e.1.2 j).val % 2 ≠ b.val := by omega
      simp [localEdge,odd,pos]
  obtain ⟨f,found⟩ := Option.isSome_iff_exists.mp live
  have e_time : rank d p=rank d e.1.1 ∨ rank d p=rank d e.1.2 := meet.imp (congrArg _) (congrArg _)
  have f_time : rank d p=rank d f.1.1 ∨ rank d p=rank d f.1.2 :=
    (local_touches j b p f found).imp (congrArg _) (congrArg _)
  exact found.trans (congrArg some (edge_touch f_time e_time))

end StackLayout

namespace StackLayout

private theorem opens_at {d m : ℕ} (j : Fin d) (b : Fin 2) (t : ℕ) :
    ((pageIntervals d m j b).matching.stop t).isSome ↔ ∃ e : Edges d m j b, opens e=t := by
  let I := pageIntervals d m j b
  constructor
  · intro h
    obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨e,start,_⟩ := (StackMatching.intervals_spec I _ _).mp hc
    exact ⟨e,start⟩
  · rintro ⟨e,open_e⟩
    apply Option.isSome_iff_exists.mpr
    exact ⟨closes e,(StackMatching.intervals_spec I _ _).mpr ⟨e,open_e,rfl⟩⟩

private theorem closes_at {d m : ℕ} (j : Fin d) (b : Fin 2) (t : ℕ) :
    (∃ a, (pageIntervals d m j b).matching.stop a=some t) ↔ ∃ e : Edges d m j b, closes e=t := by
  let I := pageIntervals d m j b
  constructor
  · rintro ⟨_,h⟩
    obtain ⟨e,_,en⟩ := (StackMatching.intervals_spec I _ _).mp h
    exact ⟨e,en⟩
  · rintro ⟨e,end_e⟩
    exact ⟨opens e,(StackMatching.intervals_spec I _ _).mpr ⟨e,rfl,end_e⟩⟩

private def localToken {d m : ℕ} (j : Fin d) (b : Fin 2) (tag : ℕ → Bool) (p : Point d m) : Fin 4 :=
  match localEdge j b p with
  | none => 0
  | some e => if opens e = rank d p then (if tag (rank d p) then 3 else 2) else 1

private theorem local_token {d m : ℕ} (j : Fin d) (b : Fin 2) (tag : ℕ → Bool) (p : Point d m) :
    StackStream.token (pageIntervals d m j b).matching tag (rank d p) = localToken j b tag p := by
  classical
  unfold localToken StackStream.token
  have reaches (e : Edges d m j b) (he : opens e=rank d p ∨ closes e=rank d p) : localEdge j b p=some e := by
    apply local_finds
    rcases he with op|cl
    · exact ((op ▸ open_endpoint e) : rank d p=rank d e.1.1 ∨ rank d p=rank d e.1.2).imp (fun h => rank_inj d h) (fun h => rank_inj d h)
    · exact ((cl ▸ close_endpoint e) : rank d p=rank d e.1.1 ∨ rank d p=rank d e.1.2).imp (fun h => rank_inj d h) (fun h => rank_inj d h)
  cases found : localEdge j b p with
  | none =>
    have noOpen : ¬((pageIntervals d m j b).matching.stop (rank d p)).isSome := by
      rintro h
      obtain ⟨e,he⟩ := (opens_at j b _).mp h
      rw [reaches e (.inl he)] at found
      contradiction
    have noClose : ¬∃ a, (pageIntervals d m j b).matching.stop a=some (rank d p) := by
      rintro h
      obtain ⟨e,he⟩ := (closes_at j b _).mp h
      rw [reaches e (.inr he)] at found
      contradiction
    simp [noOpen,noClose]
  | some e =>
    by_cases op : opens e = rank d p
    · have h := (opens_at j b _).mpr ⟨e,op⟩
      simp [h,op]
    · have hcl : closes e = rank d p := by
        obtain meet|meet := local_touches j b p e found <;> subst p <;>
          unfold opens at op <;> unfold closes <;> omega
      have cl := (closes_at j b _).mpr ⟨e,hcl⟩
      have noOpen : ¬((pageIntervals d m j b).matching.stop (rank d p)).isSome :=
        fun o => grid_disjoint j b _ o cl
      simp [noOpen,cl,op]

def rowAt (d m : ℕ) (tag : Fin (d*2) → ℕ → Bool) (t : ℕ) : StackStream.Row (d*2) :=
  if ht : t < m^d then fun i =>
    let p : Fin d × Fin 2 := finProdFinEquiv.symm i
    localToken p.1 p.2 (tag i) (pointAt d ⟨t,ht⟩)
  else fun _ => 0

theorem generated_schedule (d m : ℕ) (tag : Fin (d*2) → ℕ → Bool) (t : ℕ) (ht : t ≤ m^d) :
    StackStream.schedule (stacked d m) tag t = (List.range t).map (rowAt d m tag) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [StackStream.schedule,ih (by omega),List.range_succ,List.map_append,List.map_singleton]
    congr 2
    funext i
    have inRange : t<m^d := by omega
    let v := pointAt (m:=m) d ⟨t,inRange⟩
    have eq : rank d v=t := rank_at d _
    change StackStream.token _ _ _ = _
    simp only [rowAt,dite_eq_left inRange]
    change StackStream.token (pageIntervals d m (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2).matching
      (tag i) t = localToken _ _ _ v
    rw [←eq]
    exact local_token _ _ _ v

end StackLayout
namespace StackLayout

private def orient (forward : Bool) (width pos : ℕ) := if forward then pos else width-1-pos

private def tailDir (forward : Bool) (a : ℕ) := if a%2=0 then forward else !forward

private theorem reverse_block {a m u B : ℕ} (ha : a<m) (hu : u<B) :
    m*B-1-(a*B+u) = (m-1-a)*B+(B-1-u) := by
  have h : (m-1-a+a+1)*B = m*B := by congr 1; omega
  rw [Nat.succ_mul,Nat.add_mul] at h
  omega

private theorem orient_step {d m : ℕ} (p : Point (d+1) m) (dir : Bool) :
    orient dir (m^(d+1)) (rank (d+1) p) =
      orient dir m (p 0).val*m^d + orient (tailDir dir (p 0).val) (m^d) (rank d (fun i => p i.succ)) := by
  have ht := rank_lt d (fun i => p i.succ)
  have h := reflect_lt (a:=(p 0).val) ht
  cases dir
  · simp only [orient,Bool.false_eq_true,ite_false,rank,pow_succ]
    rw [Nat.mul_comm (m^d) m,reverse_block (p 0).isLt h]
    by_cases par : (p 0).val%2=0 <;> simp [reflect,tailDir,par] <;> omega
  · by_cases par : (p 0).val%2=0 <;> simp [orient,rank,reflect,tailDir,par]

private def moveHead {m : ℕ} (forward : Bool) (a : Fin m) : Option (Fin m) :=
  if forward then if h : a.val+1<m then some ⟨a.val+1,h⟩ else none
  else if a.val=0 then none else some ⟨a.val-1,(Nat.sub_le _ _).trans_lt a.isLt⟩

private theorem tail_flip (dir : Bool) {a b : ℕ} (adj : a+1=b ∨ b+1=a) :
    tailDir dir b = !(tailDir dir a) := by
  by_cases even : a%2=0
  · have odd : b%2 ≠ 0 := by omega
    simp [tailDir,even,odd]
  · have yes : b%2=0 := by omega
    simp [tailDir,even,yes]

private theorem head_step {m : ℕ} (forward : Bool) (a : Fin m) :
    match moveHead forward a with
    | none => orient forward m a.val + 1 = m
    | some b => orient forward m b.val = orient forward m a.val+1 ∧
        tailDir forward b.val = !(tailDir forward a.val) := by
  have bound := a.isLt
  cases forward
  · by_cases eq : a.val=0
    · simp [moveHead,eq,orient]; omega
    · simp only [moveHead,Bool.false_eq_true,ite_false,eq]
      exact ⟨by unfold orient; simp; omega,tail_flip false (.inr (by omega))⟩
  · by_cases step : a.val+1<m
    · simp only [moveHead,ite_true,dite_eq_left step]
      exact ⟨rfl,tail_flip true (.inl rfl)⟩
    · simp [moveHead,step,orient]; omega

/-- A bouncing odometer only changes one coordinate in each transition. -/
def nextPoint {m : ℕ} : (d : ℕ) → Point d m → Bool → Option (Point d m)
  | 0,_,_ => none
  | d+1,p,dir =>
    let a := p 0
    let rest := fun i => p i.succ
    match nextPoint d rest (tailDir dir a.val) with
    | some q => some (Fin.cons a q)
    | none => (moveHead dir a).map (fun b => Fin.cons b rest)

private theorem orient_flip {m x : ℕ} (dir : Bool) (hx : x<m) :
    orient (!dir) m x = m-1-orient dir m x := by cases dir <;> simp [orient] <;> omega

theorem odometer_advances {m : ℕ} (d : ℕ) (p : Point d m) (dir : Bool) :
    match nextPoint d p dir with
    | none => orient dir (m^d) (rank d p)+1=m^d
    | some q => orient dir (m^d) (rank d q) = orient dir (m^d) (rank d p)+1 := by
  induction d generalizing dir with
  | zero => cases dir <;> rfl
  | succ d ih =>
    let a := p 0
    let rest := fun i : Fin d => p i.succ
    let g := tailDir dir a.val
    have hr := ih rest g
    rw [nextPoint]
    cases he : nextPoint d rest g with
    | some q =>
      rw [he] at hr
      simp only [orient_step,Fin.cons_zero,Fin.cons_succ]
      change orient dir m a.val*m^d + orient g (m^d) (rank d q) =
        orient dir m a.val*m^d + orient g (m^d) (rank d rest) + 1
      rw [hr,Nat.add_assoc]
    | none =>
      rw [he] at hr
      have hh := head_step dir a
      cases step : moveHead dir a with
      | none =>
        rw [step] at hh
        simp only [Option.map_none,orient_step]
        change orient dir m a.val*m^d+orient g _ (rank d rest)+1=m^(d+1)
        calc
          _ = (orient dir m a.val+1)*m^d := by rw [Nat.succ_mul]; omega
          _ = m^(d+1) := by rw [hh,pow_succ,Nat.mul_comm]
      | some b =>
        rw [step] at hh
        obtain ⟨ha,hd⟩ := hh
        simp only [Option.map_some,orient_step,Fin.cons_zero,Fin.cons_succ]
        rw [ha,hd,orient_flip _ (rank_lt d rest),Nat.succ_mul]
        change orient dir m a.val*m^d + m^d + (m^d - 1 - orient g (m^d) (rank d rest)) =
          orient dir m a.val*m^d + orient g (m^d) (rank d rest) + 1
        omega

end StackLayout
namespace StackLayout

/-- Finite observations for a coordinate represented by two unary stacks. -/
abbrev Flag := Bool × Bool × Bool

private def flags {d m : ℕ} (p : Point d m) (i : Fin d) : Flag :=
  (decide ((p i).val=0),decide ((p i).val+1=m),decide ((p i).val % 2=1))

def innerDir (dir : Bool) (f : Flag) := if f.2.2 then !dir else dir

def allowed (f : Flag) (dir : Bool) := if dir then !f.2.1 else !f.1

def plan : (d : ℕ) → (Fin d → Flag) → Bool → Option (Fin d × Bool)
  | 0,_,_ => none
  | d+1,fs,dir =>
    match plan d (fun i => fs i.succ) (innerDir dir (fs 0)) with
    | some (i,sgn) => some (i.succ,sgn)
    | none => if allowed (fs 0) dir then some (0,dir) else none

private theorem enabled (d : ℕ) (fs : Fin d → Flag) (dir : Bool) :
    match plan d fs dir with | none => True | some (i,b) => allowed (fs i) b = true := by
  induction d generalizing dir with
  | zero => trivial
  | succ d ih =>
    rw [plan]
    have h := ih (fun i => fs i.succ) (innerDir dir (fs 0))
    cases choice : plan d (fun i => fs i.succ) (innerDir dir (fs 0)) with
    | none => cases ok : allowed (fs 0) dir <;> simp [ok]
    | some p =>
      obtain ⟨i,b⟩ := p
      rw [choice] at h
      exact h

private theorem inner_ok {d m : ℕ} (p : Point d m) (i : Fin d) (dir : Bool) :
    innerDir dir (flags p i) = tailDir dir (p i).val := by
  by_cases e : (p i).val % 2 = 0
  · have o : (p i).val % 2 ≠ 1 := by omega
    simp [innerDir,flags,tailDir,e]
  · have o : (p i).val % 2 = 1 := by omega
    simp [innerDir,flags,tailDir,o]

private theorem allowed_ok {d m : ℕ} (p : Point d m) (i : Fin d) (dir : Bool) :
    allowed (flags p i) dir = (moveHead dir (p i)).isSome := by
  have bound := (p i).isLt
  cases dir
  · by_cases z : (p i).val=0 <;> simp [allowed,flags,moveHead,z]
  · by_cases h : (p i).val+1<m
    · have n : (p i).val+1 ≠m := by omega
      simp [allowed,flags,moveHead,h,n]
    · have eq : (p i).val+1=m := by omega
      simp [allowed,flags,moveHead,eq]

private def moved {d m : ℕ} (p : Point d m) (q : Fin d × Bool) : Option (Point d m) :=
  (moveHead q.2 (p q.1)).map (Function.update p q.1)

private theorem update_head {d m : ℕ} (p : Point (d+1) m) (b : Fin m) :
    Function.update p 0 b = Fin.cons b (fun i => p i.succ) := by
  funext i
  exact Fin.cases (by simp) (fun j => by simp [Fin.succ_ne_zero]) i

private theorem update_succ {d m : ℕ} (p : Point (d+1) m) (i : Fin d) (b : Fin m) :
    Function.update p i.succ b = Fin.cons (p 0) (Function.update (fun q => p q.succ) i b) := by
  funext j
  cases j using Fin.cases with
  | zero => simp [Ne.symm (Fin.succ_ne_zero i)]
  | succ j =>
    by_cases e : j=i
    · subst j; simp
    · simp [e,show j.succ ≠ i.succ from fun h => e (Fin.succ_injective _ h)]

theorem plan_correct {m : ℕ} (d : ℕ) (p : Point d m) (dir : Bool) :
    nextPoint d p dir = (plan d (flags p) dir).bind (moved p) := by
  induction d generalizing dir with
  | zero => rfl
  | succ d ih =>
    let rest := fun i : Fin d => p i.succ
    let g := tailDir dir (p 0).val
    have ef : (fun i : Fin d => flags p i.succ) = flags rest := rfl
    rw [nextPoint,plan,inner_ok,ef,ih]
    cases pick : plan d (flags rest) g with
    | none =>
      simp only [Option.bind_none,allowed_ok]
      cases move : moveHead dir (p 0) with
      | none => simp
      | some b => simp [move,moved,update_head]
    | some op =>
      obtain ⟨i,sgn⟩ := op
      simp only [Option.bind_some]
      cases move : moveHead sgn (p i.succ) with
      | none =>
        have en := enabled d (flags rest) g
        rw [pick] at en
        change allowed (flags rest i) sgn = true at en
        rw [allowed_ok] at en
        change (moveHead sgn (p i.succ)).isSome = true at en
        simp [move] at en
      | some b =>
        simp only [moved,rest,move,Option.map_some,update_succ]

end StackLayout
namespace StackLayout

def forwardAt : (d : ℕ) → (Fin d → Flag) → Bool → Fin d → Bool
  | 0,_,_,i => i.elim0
  | d+1,f,dir,i => Fin.cases dir (fun j => forwardAt d (fun t=>f t.succ) (innerDir dir (f 0)) j) i

private theorem orientation {m : ℕ} (d : ℕ) (j : Fin d) (p q : Point d m) (edge : Link j p q)
    (dir : Bool) :
    if forwardAt d (flags p) dir j then
      orient dir (m^d) (rank d p) < orient dir (m^d) (rank d q)
    else orient dir (m^d) (rank d q) < orient dir (m^d) (rank d p) := by
  induction d generalizing dir with
  | zero => exact j.elim0
  | succ d ih =>
    cases j using Fin.cases with
    | zero =>
      have inc := by_head (p:=p) (q:=q) (show (p 0).val < (q 0).val by have := edge.1; omega)
      have bp := rank_lt _ p
      have bq := rank_lt _ q
      cases dir <;> simp only [forwardAt,Fin.cases_zero,orient,ite_true,Bool.false_eq_true,ite_false] <;> omega
    | succ j =>
      have eq := edge.2 0 (Fin.succ_ne_zero j).symm
      have tail := ih j _ _ (tail_link edge) (tailDir dir (p 0).val)
      simp only [orient_step,←eq,forwardAt,Fin.cases_succ,inner_ok,Nat.add_lt_add_iff_left]
      exact tail

private theorem direction_shared {m : ℕ} (d : ℕ) (j : Fin d) (p q : Point d m) (edge : Link j p q)
    (dir : Bool) : forwardAt d (flags p) dir j = forwardAt d (flags q) dir j := by
  induction d generalizing dir with
  | zero => exact j.elim0
  | succ d ih =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j =>
      have eq := edge.2 0 (Fin.succ_ne_zero j).symm
      simp only [forwardAt,Fin.cases_succ,inner_ok,←eq]
      exact ih _ _ _ (tail_link edge) _

/-- A fixed finite-control table can choose the page command from three flags per
coordinate. The data bit written by a push is false. -/
def controlToken (f : Flag) (increasing : Bool) (b : Fin 2) : Fin 4 :=
  if f.2.2 = decide (b.val=1) then
    if f.2.1 then 0 else if increasing then 2 else 1
  else if f.1 then 0 else if increasing then 1 else 2

private theorem low_color {a : ℕ} {b : Fin 2} :
    (decide (a%2=1) = decide (b.val=1)) ↔ a%2=b.val := by
  have := b.isLt
  by_cases a0 : a%2=0 <;> by_cases b0 : b.val=0 <;>
    simp [a0,b0,show a%2=0 ∨ a%2=1 by omega] <;> omega

theorem control_emits {d m : ℕ} (j : Fin d) (b : Fin 2) (p : Point d m) :
    controlToken (flags p j) (forwardAt d (flags p) true j) b = localToken j b (fun _=>false) p := by
  unfold controlToken localToken
  have bound := (p j).isLt
  by_cases color : (p j).val%2=b.val
  · have lo := low_color.mpr color
    simp only [flags,lo,ite_true]
    by_cases room : (p j).val+1<m
    · have away : (p j).val+1 ≠m := by omega
      let q := neighborUp j p room
      have edge : Link j p q :=
        ⟨by simp [q,neighborUp],fun i ne=>by simp [q,neighborUp,ne]⟩
      have order := orientation d j p q edge true
      cases sign : forwardAt d (flags p) true j with
      | false =>
        have later : rank d q < rank d p := by simpa [sign,orient] using order
        simp [localEdge,color,room,away,opens,q,sign,Nat.min_eq_right later.le,later.ne]
      | true =>
        have early : rank d p < rank d q := by simpa [sign,orient] using order
        simp [localEdge,color,room,away,opens,q,sign,Nat.min_eq_left early.le]
    · have last : (p j).val+1=m := by omega
      simp [localEdge,color,room,last]
  · have lo : ¬decide ((p j).val%2=1) = decide (b.val=1) := fun e=>color (low_color.mp e)
    simp only [flags,lo,ite_false]
    by_cases zero : (p j).val=0
    · have nz : ¬0=b.val := by simpa [zero] using color
      simp [localEdge,zero,nz]
    · have pos : 0<(p j).val := by omega
      let q := neighborDown j p
      have edge : Link j q p :=
        ⟨by simp [q,neighborDown]; omega,fun i ne=>by simp [q,neighborDown,ne]⟩
      have eq := direction_shared d j q p edge true
      have order := orientation d j q p edge true
      rw [eq] at order
      cases sign : forwardAt d (flags p) true j with
      | false =>
        have later : rank d p < rank d q := by simpa [sign,orient] using order
        simp [localEdge,color,zero,pos,opens,flags,q,Nat.min_eq_right later.le]
      | true =>
        have early : rank d q < rank d p := by simpa [sign,orient] using order
        simp [localEdge,color,zero,pos,opens,flags,q,Nat.min_eq_left early.le,early.ne]

end StackLayout
namespace StackLayout.Wired

open CutVerification

private def page {d : ℕ} (j : Fin d) (b : Fin 2) : Fin (d*2) := finProdFinEquiv (j,b)

/-- The complete Boolean operation at a grid tick depends only on the parity and
zero flags of its coordinates. All its operands are genuine current stack heads. -/
noncomputable def localGate (d : ℕ) (zero odd : Fin d → Bool) (bits : StackGates.Bits (d*2)) : Bool := by
  classical
  exact if ∀ i, odd i=false then
    if ∀ i, zero i=true then true else
      decide ((∑ j : Fin d, if zero j then 0 else (bits (page j 1)).toNat) % 2=1)
  else if h : ∃! i, odd i=true then bits (page h.choose 0) else false

private def zeroAt {d m : ℕ} (p : Point d m) (j : Fin d) := decide ((p j).val=0)
private def oddAt {d m : ℕ} (p : Point d m) (j : Fin d) := decide ((p j).val % 2=1)

private theorem get_page {d m : ℕ} {s t : Site d m} (j : Fin d) (b : Fin 2)
    (edge : Link j (location t) (location s)) (earlier : tick t<tick s) (color : ((location t) j).val % 2=b.val)
    (val : Site d m → Bool) :
    StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) (tick s)) (page j b)=val t := by
  let e : Edges d (2*m) j b := ⟨(location t,location s),edge,color⟩
  have h : (StackMatching.run (pageIntervals d (2*m) j b).matching (tick s)).head?=some (tick t) := by
    simpa only [e,tick,Nat.max_eq_right earlier.le,Nat.min_eq_left earlier.le] using pop_reads_own_edge j b e
  change (((StackMatching.run (stacked d (2*m) (page j b)) _).map (payload val)).head?).getD false=_
  let E : (Fin d × Fin 2) ≃ Fin (d*2) := finProdFinEquiv
  have same : stacked d (2*m) (page j b) = (pageIntervals d (2*m) j b).matching := by
    change (pageIntervals d (2*m) (E.symm (E (j,b))).1 (E.symm (E (j,b))).2).matching=_
    rw [E.symm_apply_apply]
  rw [same,List.head?_map,h]
  simp [payload,at_site]

private theorem relay_page {d m : ℕ} (u : Point d m) (j : Fin d) (val : Site d m → Bool) :
    StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) (tick (.relay u j))) (page j 0)=val (.main u) := by
  have edge : Link j (twice u) (middle u j) := ⟨by simp [twice,middle],fun i h=>by simp [middle,h]⟩
  have lt := rank_link d j (twice u) (middle u j) edge (fun i _=>by simp [twice])
  apply get_page (s:=.relay u j) (t:=.main u) j 0 edge lt
  simp [location,twice]

private theorem main_page {d m : ℕ} (u : Point d m) (j : Fin d) (pos : 0<(u j).val) (val : Site d m → Bool) :
    StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) (tick (.main u))) (page j 1)=
      val (.relay (PascalGrid.parent u j) j) := by
  have edge : Link j (middle (PascalGrid.parent u j) j) (twice u) := by
    constructor
    · simp [middle,PascalGrid.parent,twice]; omega
    · intro i ne; simp [middle,PascalGrid.parent,twice,ne]
  have lt := rank_link d j (middle (PascalGrid.parent u j) j) (twice u) edge (fun i hi=>by simp [middle,twice,Fin.ne_of_lt hi])
  apply get_page (s:=.main u) (t:=.relay (PascalGrid.parent u j) j) j 1 edge lt
  simp [location,middle]

private theorem total_zero {d m : ℕ} (u : Point d m) : PascalGrid.total (PascalGrid.coord u)=0 ↔ ∀ i,(u i).val=0 := by
  simp [PascalGrid.total,PascalGrid.coord,Finset.sum_eq_zero_iff]

private theorem all_even {d m : ℕ} (u : Point d m) : ∀ i,oddAt (twice u) i=false := by
  intro i; simp [oddAt,twice]

private theorem one_odd {d m : ℕ} (u : Point d m) (j i : Fin d) : oddAt (middle u j) i=decide (i=j) := by
  by_cases e : i=j
  · subst i; simp [oddAt,middle]
  · simp [oddAt,middle,twice,e]

private theorem local_site {d m : ℕ} (s : Site d m) (val : Site d m → Bool)
    (correct : Solves (graph d m) (fun p=>(val p).toNat)) :
    localGate d (zeroAt (location s)) (oddAt (location s))
      (StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) (tick s)))=val s := by
  classical
  cases s with
  | relay p j =>
    have odd := one_odd p j
    have someOdd : ¬∀i, oddAt (middle p j) i=false := by intro h; simpa [odd] using h j
    have exactly : ∃! i, oddAt (middle p j) i=true := by simpa only [odd,decide_eq_true_eq] using (show ∃! i : Fin d,i=j from ⟨j,rfl,fun _ h=>h⟩)
    have chosen : exactly.choose=j := of_decide_eq_true ((odd exactly.choose) ▸ exactly.choose_spec.1)
    simp only [localGate,location,someOdd,ite_false,dite_eq_left exactly,chosen]
    rw [relay_page]
    have copy := correct (.relay p j)
    change (val (.relay p j)).toNat=(val (.main p)).toNat at copy
    cases h1 : val (.main p) <;> cases h2 : val (.relay p j) <;> simp_all
  | main p =>
    have eqzero : (∀ i, zeroAt (twice p) i=true) ↔ PascalGrid.total (PascalGrid.coord p)=0 := by
      simp [zeroAt,twice,total_zero]
    have honest := correct (.main p)
    change (val (.main p)).toNat = (if PascalGrid.total (PascalGrid.coord p)=0 then 1 else
      (∑ j : Fin d, if 0<(p j).val then (val (.relay (PascalGrid.parent p j) j)).toNat else 0) % 2) at honest
    change localGate d (zeroAt (twice p)) (oddAt (twice p)) _ = _
    rw [localGate,ite_eq_left (all_even p)]
    by_cases zero : PascalGrid.total (PascalGrid.coord p)=0
    · rw [ite_eq_left (eqzero.mpr zero)]
      rw [ite_eq_left zero] at honest
      cases hx : val (.main p) <;> simp_all
    · rw [ite_eq_right (fun h=>zero (eqzero.mp h))]
      rw [ite_eq_right zero] at honest
      have sums : (∑ j : Fin d, if zeroAt (twice p) j then 0 else
        (StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) (tick (.main p))) (page j 1)).toNat) =
        ∑ j : Fin d, if 0<(p j).val then (val (.relay (PascalGrid.parent p j) j)).toNat else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases pos : 0<(p j).val
        · simp [zeroAt,twice,Nat.ne_of_gt pos,pos,main_page p j pos val]
        · simp [zeroAt,twice,show (p j).val=0 by omega]
      rw [sums,←honest]
      cases val (.main p) <;> decide

end StackLayout.Wired

namespace StackLayout.Wired

open CutVerification

private theorem local_empty {d m : ℕ} (p : Point d (2*m))
    (absent : ∀ s : Site d m, location s≠p) (bits : StackGates.Bits (d*2)) : localGate d (zeroAt p) (oddAt p) bits=false := by
  classical
  have odd : ¬∀j,oddAt p j=false := by
    intro h
    apply absent (.main (halve p))
    funext i
    apply Fin.ext
    have even:=h i
    simp [oddAt] at even
    change 2*((p i).val/2)=(p i).val
    omega
  have many : ¬∃! i,oddAt p i=true := by
    rintro ⟨j,hj,only⟩
    apply absent (.relay (halve p) j)
    funext i
    apply Fin.ext
    by_cases same : i=j
    · subst i
      simp [location,middle,halve]
      simp [oddAt] at hj
      omega
    · have even : (p i).val%2≠1 := by intro hi; exact same (only i (by simpa [oddAt] using hi))
      simp [location,middle,halve,twice,same]
      omega
  simp [localGate,odd,many]

/-- A uniform row operation for the whole physical traversal; its input consists
of local coordinate flags, obtained by the reflected counter. -/
noncomputable def addressedGate (d m t : ℕ) : StackGates.Bits (d*2) → Bool :=
  if h : t<(2*m)^d then
    let p:=pointAt d (m:=2*m) ⟨t,h⟩
    localGate d (zeroAt p) (oddAt p)
  else fun _=>false

private theorem addressed_computes {d m : ℕ} (val : Site d m → Bool)
    (ok : Solves (graph d m) (fun s=>(val s).toNat)) (t : ℕ) :
    addressedGate d m t (StackGates.tips (StackGates.contents (stacked d (2*m)) (payload val) t)) = payload val t := by
  classical
  by_cases has : ∃ s : Site d m,tick s=t
  · obtain ⟨s,rfl⟩ := has
    have h := rank_lt d (location s)
    have atRank : pointAt d (m:=2*m) ⟨tick s,h⟩=location s := rank_inj d (rank_at d _)
    simp only [addressedGate,dite_eq_left h,atRank,payload,at_site,Option.map_some,Option.getD_some]
    exact local_site s val ok
  · have empty : atTick d m t=none := by simp [atTick,has]
    simp only [payload,empty,Option.map_none,Option.getD_none]
    unfold addressedGate
    split
    next h =>
      apply local_empty
      intro s he
      exact has ⟨s,(congrArg (rank d) he).trans (rank_at d _)⟩
    next => rfl

/-- Every data bit produced by the actual multistack machine can be computed from
a gate table depending only on its 2d coordinate flags and its 2d current head bits. -/
theorem run_with_local_gates {d m : ℕ} (val : Site d m → Bool)
    (ok : Solves (graph d m) (fun s=>(val s).toNat)) (t : ℕ) (tail : List (StackGates.Row (d*2))) :
    (flip bind (StackGates.machine (d*2)).step)^[t]
      (some (Turing.initList (StackGates.machine (d*2))
        (StackGates.program (stacked d (2*m)) (addressedGate d m) t ++ tail))) =
    some (StackGates.frame tail (StackGates.contents (stacked d (2*m)) (payload val) t)) := by
  apply StackGates.program_run _ _ _ (addressed_computes val ok)
  intro i u
  exact grid_disjoint (m:=2*m) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 u

end StackLayout.Wired

namespace StackLayout.Wired

private def cmd3 (x : Fin 4) : Fin 3 := ⟨x.val % 3,Nat.mod_lt _ (by decide)⟩

/-- Finite-control instruction generator. Its input is three flags per axis; its
output is all page operations and the Boolean operation on their current heads. -/
noncomputable def instructionOf (d : ℕ) (fs : Fin d → Flag) : StackGates.Row (d*2) :=
  (fun i => let q := finProdFinEquiv.symm i
            cmd3 (controlToken (fs q.1) (forwardAt d fs true q.1) q.2),
   localGate d (fun i=>(fs i).1) (fun i=>(fs i).2.2))

private theorem command_token (M : StackMatching.Matching) (u : ℕ) :
    StackGates.command M u=cmd3 (StackStream.token M (fun _=>false) u) := by
  classical
  by_cases h : (M.stop u).isSome <;> by_cases g : ∃ a,M.stop a=some u <;>
    simp [StackGates.command,StackStream.token,h,g,cmd3] <;> rfl

theorem finite_instruction {d m : ℕ} (p : Point d (2*m)) :
    StackGates.instruction (stacked d (2*m)) (addressedGate d m) (rank d p) = instructionOf d (flags p) := by
  apply Prod.ext
  · funext i
    let q : Fin d × Fin 2 := finProdFinEquiv.symm i
    change StackGates.command (pageIntervals d (2*m) q.1 q.2).matching _ =
      cmd3 (controlToken (flags p q.1) (forwardAt d (flags p) true q.1) q.2)
    rw [command_token,local_token,control_emits]
  · have h:=rank_lt d p
    have inv : pointAt d (m:=2*m) ⟨rank d p,h⟩=p := rank_inj d (rank_at d _)
    change addressedGate d m (rank d p) = _
    rw [addressedGate,dite_eq_left h,inv]
    rfl

end StackLayout.Wired

namespace CounterEngine
open Turing

abbrev Flag := Bool × Bool × Bool
abbrev Bank (d k : ℕ) := Unit ⊕ ((Fin d × Bool) ⊕ Fin k)
private def input (d k : ℕ) : Bank d k := .inl ()
private def counter {d k : ℕ} (i : Fin d) (right : Bool) : Bank d k := .inr (.inl (i,right))
private def wires {d k : ℕ} (i : Fin k) : Bank d k := .inr (.inr i)
abbrev Bits (k : ℕ) := Fin k → Bool
abbrev Flags (d : ℕ) := Fin d → Flag
abbrev Row (k : ℕ) := (Fin k → Fin 3) × (Bits k → Bool)
abbrev Reg (d k : ℕ) := Bits d × Flags d × Bits k × Bool
abbrev Stack (d k : ℕ) := Bank d k → List Bool
private abbrev St (d k : ℕ) := TM2.Stmt (fun _ : Bank d k => Bool) (Fin 3) (Reg d k)
private def initial (d k : ℕ) (p : Bits d) : Reg d k := (p,fun _=>(false,false,false),fun _=>false,false)
private def jump {d k : ℕ} (l : Fin 3) : St d k := .load (fun r=>initial d k r.1) (.goto fun _=>l)

def physical {d k : ℕ} (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) : Stack d k
  | .inl _ => xs
  | .inr (.inl (i,false)) => L i
  | .inr (.inl (i,true)) => R i
  | .inr (.inr i) => S i

private def scanCoords {d k : ℕ} : List (Fin d) → St d k → St d k
  | [],q=>q
  | i::is,q=>.peek (counter i false)
      (fun r a=>(r.1,Function.update r.2.1 i (a.isNone,false,r.1 i),r.2.2))
      (.peek (counter i true)
        (fun r a=>(r.1,Function.update r.2.1 i ((r.2.1 i).1,a.isNone,r.1 i),r.2.2)) (scanCoords is q))

private def scanData {d k : ℕ} : List (Fin k) → St d k → St d k
  | [],q=>q
  | i::is,q=>.peek (wires i) (fun r a=>(r.1,r.2.1,Function.update r.2.2.1 i (a.getD false), r.2.2.2)) (scanData is q)

private def peeked {α β : Type} [DecidableEq α] (is : List α) (a b : α → β) (i : α) := if i∈is then a i else b i

private theorem peeked_cons {α β : Type} [DecidableEq α] (i : α) (is : List α) (a b : α → β) :
    peeked is a (Function.update b i (a i)) = peeked (i::is) a b := by
  funext j
  by_cases same : j=i
  · subst j; simp [peeked]
  · simp [peeked,same]

private def marks {d : ℕ} (L R : Fin d → List Bool) (par : Bits d) (i : Fin d) : Flag :=
  ((L i).head?.isNone,(R i).head?.isNone,par i)

def tips {k : ℕ} (S : Fin k → List Bool) (i : Fin k) := (S i).head?.getD false

private theorem scan_coords {d k : ℕ} (is : List (Fin d)) (q : St d k) (xs : List Bool)
    (L R : Fin d → List Bool) (S : Fin k → List Bool) (par : Bits d) (fs : Flags d) (bs : Bits k) (b : Bool) :
    TM2.stepAux (scanCoords is q) (par,fs,bs,b) (physical xs L R S) =
      TM2.stepAux q (par,peeked is (marks L R par) fs,bs,b) (physical xs L R S) := by
  induction is generalizing fs with
  | nil => congr
  | cons i is ih =>
    simp only [scanCoords,TM2.stepAux,counter,physical,Function.update_self,Function.update_idem]
    rw [ih]
    exact congrArg (fun h=>TM2.stepAux q (par,h,bs,b) (physical xs L R S)) (peeked_cons i is (marks L R par) fs)

private theorem scan_data {d k : ℕ} (is : List (Fin k)) (q : St d k) (xs : List Bool)
    (L R : Fin d → List Bool) (S : Fin k → List Bool) (par : Bits d) (fs : Flags d) (bs : Bits k) (b : Bool) :
    TM2.stepAux (scanData is q) (par,fs,bs,b) (physical xs L R S) =
      TM2.stepAux q (par,fs,peeked is (tips S) bs,b) (physical xs L R S) := by
  induction is generalizing bs with
  | nil => congr
  | cons i is ih =>
    simp only [scanData,TM2.stepAux,wires,physical]
    rw [ih]
    exact congrArg (fun h=>TM2.stepAux q (par,fs,h,b) (physical xs L R S)) (peeked_cons i is (tips S) bs)

private theorem all_peeked {n : ℕ} {A : Type} (a b : Fin n → A) : peeked (List.finRange n) a b=a := by
  funext i; simp [peeked]

end CounterEngine

namespace CounterEngine
open Turing

private theorem set_data {d k : ℕ} (xs : List Bool) (L R : Fin d → List Bool)
    (S : Fin k → List Bool) (i : Fin k) (u : List Bool) :
    Function.update (physical xs L R S) (wires i) u=physical xs L R (Function.update S i u) := by
  funext x
  rcases x with x|x
  · simp [wires,physical,Function.update]
  · rcases x with ⟨j,b⟩|j
    · cases b <;> simp [wires,physical,Function.update]
    · by_cases e : j=i
      · subst j; simp [wires,physical]
      · simp [wires,physical,Function.update,e]

private theorem set_counter {d k : ℕ} (xs : List Bool) (L R : Fin d → List Bool)
    (S : Fin k → List Bool) (i : Fin d) (b : Bool) (u : List Bool) :
    Function.update (physical xs L R S) (counter i b) u =
      physical xs (if b then L else Function.update L i u) (if b then Function.update R i u else R) S := by
  funext x
  rcases x with x|x
  · cases b <;> simp [counter,physical,Function.update]
  · rcases x with ⟨j,c⟩|j
    · by_cases e : j=i
      · subst j; cases b <;> cases c <;> simp [counter,physical,Function.update]
      · cases b <;> cases c <;> simp [counter,physical,Function.update,e]
    · cases b <;> simp [counter,physical,Function.update]

private theorem set_input {d k : ℕ} (xs : List Bool) (L R : Fin d → List Bool)
    (S : Fin k → List Bool) (u : List Bool) : Function.update (physical xs L R S) (input d k) u=physical u L R S := by
  funext x
  rcases x with x|x
  · cases x; simp [input,physical]
  · rcases x with ⟨j,b⟩|j
    · cases b <;> simp [input,physical,Function.update]
    · simp [input,physical,Function.update]

private def one (cmd : Fin 3) (v : Bool) (xs : List Bool) := if cmd=0 then xs else if cmd=1 then xs.tail else v::xs
private def many {I A : Type} [DecidableEq I] (f : I → A → A) : List I → (I → A) → (I → A)
  | [],S => S
  | i::is,S => many f is (Function.update S i (f i (S i)))

private theorem many_spec {I A : Type} [DecidableEq I] (f : I → A → A) (is : List I) (S : I → A)
    (nd : is.Nodup) (j : I) : many f is S j = if j∈is then f j (S j) else S j := by
  induction is generalizing S with
  | nil => simp [many]
  | cons i is ih =>
    obtain ⟨h,hd⟩:=List.nodup_cons.mp nd
    rw [many,ih _ hd]
    by_cases e : j=i
    · subst j; simp [h]
    · simp [e]

private theorem many_full {k : ℕ} {A : Type} (f : Fin k → A → A) (S : Fin k → A) :
    many f (List.finRange k) S = fun j=>f j (S j) := by
  funext j; rw [many_spec f _ _ (List.nodup_finRange k)]; simp

private def writeData {d k : ℕ} (get : Flags d → Row k) : List (Fin k) → St d k → St d k
  | [],q=>q
  | i::is,q=>
    let z:=writeData get is q
    .branch (fun r=>decide ((get r.2.1).1 i=0)) z
      (.branch (fun r=>decide ((get r.2.1).1 i=1)) (.pop (wires i) (fun r _=>r) z)
        (.push (wires i) (fun r=>(get r.2.1).2 r.2.2.1) z))

private theorem write_data {d k : ℕ} (get : Flags d → Row k) (is : List (Fin k)) (q : St d k) (xs : List Bool)
    (L R : Fin d → List Bool) (S : Fin k → List Bool) (par : Bits d) (fs : Flags d) (bs : Bits k) (b : Bool) :
    TM2.stepAux (writeData get is q) (par,fs,bs,b) (physical xs L R S)=
      TM2.stepAux q (par,fs,bs,b) (physical xs L R (many (fun i=>one ((get fs).1 i) ((get fs).2 bs)) is S)) := by
  induction is generalizing S with
  | nil => rfl
  | cons i is ih =>
    by_cases h0 : (get fs).1 i=0
    · simp [writeData,TM2.stepAux,h0,one,many,ih]
    · by_cases h1 : (get fs).1 i=1
      · simp only [writeData,TM2.stepAux,h1,decide_true,Bool.cond_true]
        change TM2.stepAux (writeData get is q) (par,fs,bs,b)
          (Function.update (physical xs L R S) (wires i) (S i).tail)=_
        rw [set_data,ih]
        simp [many,one,h1]
      · simp only [writeData,TM2.stepAux,h0,h1,decide_false,Bool.cond_false]
        change TM2.stepAux (writeData get is q) (par,fs,bs,b)
          (Function.update (physical xs L R S) (wires i) (((get fs).2 bs)::S i))=_
        rw [set_data,ih]
        simp [many,one,h0,h1]

end CounterEngine

namespace CounterEngine
open Turing

private def shift {d k : ℕ} (i : Fin d) (dir : Bool) : St d k :=
  .pop (counter i dir) (fun r _=>r) (.push (counter i (!dir)) (fun _=>false)
    (.load (fun r=>initial d k (Function.update r.1 i (!(r.1 i)))) (.goto fun _=>1)))

private def dispatch {d k : ℕ} (choose : Flags d → Option (Fin d × Bool)) : List (Fin d) → St d k
  | [] => jump 2
  | i::is => .branch (fun r=>decide (choose r.2.1=some (i,true))) (shift i true)
      (.branch (fun r=>decide (choose r.2.1=some (i,false))) (shift i false) (dispatch choose is))

private theorem selected {d k : ℕ} (choose : Flags d → Option (Fin d × Bool)) (is : List (Fin d))
    (r : Reg d k) (S : Stack d k) :
    TM2.stepAux (dispatch choose is) r S =
      match choose r.2.1 with
      | none => TM2.stepAux (jump 2) r S
      | some (i,dir) => if i∈is then TM2.stepAux (shift i dir) r S else TM2.stepAux (jump 2) r S := by
  induction is with
  | nil => cases h:choose r.2.1 with
    | none=>rfl
    | some z=> obtain ⟨i,b⟩:=z; simp [dispatch]
  | cons j is ih =>
    cases h : choose r.2.1 with
    | none => simp [dispatch,TM2.stepAux,h] at ih ⊢; exact ih
    | some z =>
      obtain ⟨i,b⟩:=z
      by_cases e:i=j
      · subst j; cases b <;> simp [dispatch,TM2.stepAux,h]
      · cases b <;> simp [dispatch,TM2.stepAux,h,e] at ih ⊢ <;> exact ih

private def addRight {d k : ℕ} : List (Fin d) → St d k → St d k
  | [],q=>q
  | i::is,q=>.push (counter i true) (fun _=>false) (addRight is q)

private theorem add_right {d k : ℕ} (is : List (Fin d)) (q : St d k) (r : Reg d k) (xs : List Bool)
    (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    TM2.stepAux (addRight is q) r (physical xs L R S) =
    TM2.stepAux q r (physical xs L (many (fun _ w=>false::w) is R) S) := by
  induction is generalizing R with
  | nil=>rfl
  | cons i is ih=>
    change TM2.stepAux (addRight is q) r (Function.update (physical xs L R S) (counter i true) (false::R i))=_
    rw [set_counter]; exact ih _

private def program {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool)) (l : Fin 3) : St d k :=
  if l=0 then .pop (input d k) (fun r a=>(r.1,r.2.1,r.2.2.1,a.isSome))
    (.branch (fun r=>r.2.2.2) (addRight (List.finRange d) (jump 0)) (jump 1))
  else if l=1 then scanCoords (List.finRange d) (scanData (List.finRange k)
    (writeData get (List.finRange k) (dispatch choose (List.finRange d))))
  else .halt

/-- Fixed physical multistack machine: a unary initialization word sets each
upper endpoint, then each subsequent macrostep computes one row and transfers
one unary counter cell in the direction designated by the finite controller. -/
noncomputable def machine {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool)) : FinTM2 where
  K:=Bank d k
  k₀:=input d k
  k₁:=input d k
  Γ:=fun _=>Bool
  Λ:=Fin 3
  main:=0
  σ:=Reg d k
  initialState:=initial d k (fun _=>false)
  Γk₀Fin:=inferInstanceAs (Fintype Bool)
  m:=program get choose

def frame {d k : ℕ} (l : Fin 3) (par : Bits d) (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    TM2.Cfg (fun _ : Bank d k=>Bool) (Fin 3) (Reg d k) := ⟨some l,initial d k par,physical xs L R S⟩

private theorem fill_symbol {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool))
    (par : Bits d) (x : Bool) (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    (machine get choose).step (frame 0 par (x::xs) L R S)=some (frame 0 par xs L (fun i=>false::R i) S) := by
  change TM2.step (program get choose) _ = _
  simp only [TM2.step,frame,program,ite_true,TM2.stepAux,initial,input,physical,List.head?_cons,List.tail_cons,
    Option.isSome_some,Bool.cond_true]
  change some (TM2.stepAux (addRight (List.finRange d) (jump 0)) _ (Function.update (physical (x::xs) L R S) (input d k) xs)) = _
  rw [set_input,add_right,many_full]
  rfl

private theorem fill_end {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool))
    (par : Bits d) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    (machine get choose).step (frame 0 par [] L R S)=some (frame 1 par [] L R S) := by
  change TM2.step (program get choose) _=_
  simp only [TM2.step,frame,program,ite_true,TM2.stepAux,initial,input,physical,List.head?_nil,List.tail_nil,
    Option.isSome_none,Bool.cond_false]
  change some (TM2.stepAux (jump 1) _ (Function.update (physical [] L R S) (input d k) []))=_
  rw [set_input]; rfl

end CounterEngine

namespace CounterEngine
open Turing

def flipAt {d : ℕ} (par : Bits d) (i : Fin d) := Function.update par i (!(par i))

def shifted {d k : ℕ} (i : Fin d) (dir : Bool) (par : Bits d) (xs : List Bool) (L R : Fin d → List Bool)
    (S : Fin k → List Bool) :=
  if dir then frame 1 (flipAt par i) xs (Function.update L i (false::L i)) (Function.update R i (R i).tail) S
  else frame 1 (flipAt par i) xs (Function.update L i (L i).tail) (Function.update R i (false::R i)) S

private theorem shift_spec {d k : ℕ} (i : Fin d) (dir : Bool) (par : Bits d) (fs : Flags d) (bits : Bits k) (b : Bool)
    (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    TM2.stepAux (shift i dir) (par,fs,bits,b) (physical xs L R S)=shifted i dir par xs L R S := by
  cases dir <;> simp only [shift,TM2.stepAux,Bool.not_false,Bool.not_true,set_counter,ite_true,Bool.false_eq_true,
    ite_false] <;> rfl

def evaluated {d k : ℕ} (get : Flags d → Row k) (fs : Flags d) (S : Fin k → List Bool) :=
  fun i=>one ((get fs).1 i) ((get fs).2 (tips S)) (S i)

def acted {d k : ℕ} (par : Bits d) (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    Option (Fin d × Bool) → TM2.Cfg (fun _ : Bank d k=>Bool) (Fin 3) (Reg d k)
  | none=>frame 2 par xs L R S
  | some (i,dir)=>shifted i dir par xs L R S

theorem active_step {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool))
    (par : Bits d) (xs : List Bool) (L R : Fin d → List Bool) (S : Fin k → List Bool) :
    (machine get choose).step (frame 1 par xs L R S) =
    some (acted par xs L R (evaluated get (marks L R par) S) (choose (marks L R par))) := by
  change some (TM2.stepAux (scanCoords (List.finRange d) (scanData (List.finRange k)
    (writeData get (List.finRange k) (dispatch choose (List.finRange d)))))
    (par,_,_,false) (physical xs L R S))=_
  rw [scan_coords,all_peeked,scan_data,all_peeked,write_data,many_full,selected]
  cases h : choose (marks L R par) with
  | none=>rfl
  | some p=>
    obtain ⟨i,b⟩:=p
    simp only [List.mem_finRange,ite_true,acted]
    exact congrArg some (shift_spec ..)

private abbrev Run {A : Type} (step : A → Option A) (n : ℕ) (a b : A) := (flip bind step)^[n] (some a)=some b
private theorem prepend {A : Type} {step : A → Option A} {n : ℕ} {a b c : A} (h : step a=some b) (t : Run step n b c) :
    Run step (n+1) a c := by
  unfold Run
  rw [Function.iterate_succ_apply]
  change (flip bind step)^[n] (step a)=some c
  rwa [h]

def unary (n : ℕ) := List.replicate n false

private theorem fill_all {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool)) (xs : List Bool)
    (n : ℕ) : Run (machine get choose).step (xs.length+1)
    (frame 0 (fun _=>false) xs (fun _=>[]) (fun _=>unary n) (fun _=>[]))
    (frame 1 (fun _=>false) [] (fun _=>[]) (fun _=>unary (n+xs.length)) (fun _=>[])) := by
  induction xs generalizing n with
  | nil =>
    apply prepend (fill_end get choose _ _ _ _)
    rfl
  | cons x xs ih =>
    apply prepend (fill_symbol get choose _ x xs _ _ _)
    have sub:=ih (n+1)
    rw [show n+1+xs.length=n+(x::xs).length by simp;omega] at sub
    exact (show unary (n+1)=false::unary n from List.replicate_succ ..) ▸ sub

theorem initialized {d k : ℕ} (get : Flags d → Row k) (choose : Flags d → Option (Fin d × Bool)) (xs : List Bool) :
    (flip bind (machine get choose).step)^[xs.length+1] (some (initList (machine get choose) xs))=
    some (frame 1 (fun _=>false) [] (fun _=>[]) (fun _=>unary xs.length) (fun _=>[])) := by
  have eq : initList (machine get choose) xs=frame 0 (fun _=>false) xs (fun _=>[]) (fun _=>[]) (fun _=>[]) := by
    unfold initList frame
    congr 1
    funext z
    rcases z with z|z
    · cases z; rfl
    · rcases z with ⟨i,b⟩|i
      · cases b <;> rfl
      · rfl
  rw [eq]
  have start:=fill_all get choose xs 0
  rw [Nat.zero_add] at start
  exact start

end CounterEngine
namespace StackLayout.Wired

open CutVerification

private def low {d M : ℕ} (p : Point d M) (j : Fin d) := CounterEngine.unary (p j).val
private def high {d M : ℕ} (p : Point d M) (j : Fin d) := CounterEngine.unary (M-1-(p j).val)
private def geomFrame {d M : ℕ} (p : Point d M) (S : Fin (d*2) → List Bool) :=
  CounterEngine.frame 1 (oddAt p) [] (low p) (high p) S

private theorem empty_unary (n : ℕ) : (CounterEngine.unary n).head?.isNone=decide (n=0) := by
  cases n <;> rfl

private theorem measured {d M : ℕ} (p : Point d M) : CounterEngine.marks (low p) (high p) (oddAt p)=flags p := by
  funext j
  unfold CounterEngine.marks low high flags
  rw [empty_unary,empty_unary]
  have bound:=(p j).isLt
  have iff : M-1-(p j).val=0 ↔ (p j).val+1=M := by omega
  simp [iff,oddAt]

private theorem unary_push {a b : ℕ} (h : b=a+1) : false::CounterEngine.unary a=CounterEngine.unary b := by
  subst b; exact (List.replicate_succ ..).symm
private theorem unary_pop {a b : ℕ} (h : a=b+1) : (CounterEngine.unary a).tail=CounterEngine.unary b := by
  subst a; rw [←unary_push rfl]; rfl

private theorem moved_frame {d M : ℕ} (p q : Point d M) (j : Fin d) (dir : Bool)
    (h : moved p (j,dir)=some q) (S : Fin (d*2) → List Bool) :
    CounterEngine.shifted j dir (oddAt p) [] (low p) (high p) S=geomFrame q S := by
  unfold moved at h
  cases move : moveHead dir (p j) with
  | none => simp [move] at h
  | some z =>
    have eq : Function.update p j z=q := by simpa [move] using h
    subst q
    have adj : if dir then z.val=(p j).val+1 else z.val+1=(p j).val := by
      cases dir <;> simp only [moveHead,Bool.false_eq_true,ite_false,ite_true] at move ⊢ <;> split at move <;>
        first | (have hz:=congrArg Fin.val (Option.some.inj move); dsimp only at hz; omega) | contradiction
    have par : CounterEngine.flipAt (oddAt p) j=oddAt (Function.update p j z) := by
      funext i
      by_cases same:i=j
      · subst i
        simp only [CounterEngine.flipAt,oddAt,Function.update_self]
        cases dir <;> simp at adj <;> cases v : decide (z.val % 2 = 1) <;> simp_all <;> omega
      · simp [CounterEngine.flipAt,oddAt,same]
    have bound := (p j).isLt
    have pos := z.isLt
    cases dir with
    | false =>
      simp at adj
      have L : Function.update (low p) j (low p j).tail=low (Function.update p j z) := by
        funext i; by_cases same : i=j
        · subst i; simp only [low,Function.update_self]; exact unary_pop adj.symm
        · simp [low,same]
      have R : Function.update (high p) j (false::high p j)=high (Function.update p j z) := by
        funext i; by_cases same : i=j
        · subst i; simp only [high,Function.update_self]; apply unary_push; omega
        · simp [high,same]
      simp [CounterEngine.shifted,geomFrame,par,L,R]
    | true =>
      simp at adj
      have L : Function.update (low p) j (false::low p j)=low (Function.update p j z) := by
        funext i; by_cases same : i=j
        · subst i; simp only [low,Function.update_self]; exact unary_push adj
        · simp [low,same]
      have R : Function.update (high p) j (high p j).tail=high (Function.update p j z) := by
        funext i; by_cases same : i=j
        · subst i; simp only [high,Function.update_self]; apply unary_pop; omega
        · simp [high,same]
      simp [CounterEngine.shifted,geomFrame,par,L,R]

/-- The matrix dimensions fix the number of stacks and the controller. The side
length will be supplied in unary on the input stack. -/
noncomputable def gridMachine (d : ℕ) := CounterEngine.machine (instructionOf d) (fun f=>plan d f true)

private noncomputable def actualData {d m : ℕ} (val : Site d m → Bool) (t : ℕ) :=
  StackGates.contents (stacked d (2*m)) (payload val) t

private theorem evaluate_at {d m : ℕ} (p : Point d (2*m)) (val : Site d m → Bool)
    (ok : Solves (graph d m) (fun s=>(val s).toNat)) :
    CounterEngine.evaluated (instructionOf d) (flags p) (actualData val (rank d p))=actualData val (rank d p+1) := by
  change StackGates.next (instructionOf d (flags p)) _=_
  rw [←finite_instruction]
  apply StackGates.next_stacks _ _ _ _ (addressed_computes val ok _)
  intro i
  exact grid_disjoint (m:=2*m) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 _

private theorem move_at {d m : ℕ} (p q : Point d (2*m)) (nxt : nextPoint d p true=some q) (val : Site d m → Bool)
    (ok : Solves (graph d m) (fun s=>(val s).toNat)) :
    (gridMachine d).step (geomFrame p (actualData val (rank d p))) = some (geomFrame q (actualData val (rank d p+1))) := by
  have ctl:=plan_correct d p true
  have step:=CounterEngine.active_step (instructionOf d) (fun f=>plan d f true) (oddAt p) [] (low p) (high p) (actualData val (rank d p))
  rw [measured,evaluate_at p val ok] at step
  rw [nxt] at ctl
  cases pick : plan d (flags p) true with
  | none => simp [pick] at ctl
  | some pair =>
    obtain ⟨j,b⟩:=pair
    have mv : moved p (j,b)=some q := by simpa [pick] using ctl.symm
    rw [pick] at step
    exact step.trans (congrArg some (moved_frame p q j b mv _))

end StackLayout.Wired

namespace StackLayout.Wired
open CutVerification

private def origin {M : ℕ} (d : ℕ) (pos : 0<M) : Point d M := fun _=>⟨0,pos⟩
private theorem origin_rank {M : ℕ} (d : ℕ) (pos : 0<M) : rank d (origin d pos)=0 := by
  induction d with
  | zero=>rfl
  | succ d ih=>change 0*M^d+reflect (M^d) 0 (rank d (origin d pos))=0; rw [ih]; simp [reflect]

/-- From a unary input holding just the physical side length minus one, a fixed
multistack machine visits every grid point and maintains every Pascal data stack.
All gate instructions and coordinate updates are computed by its own control. -/
theorem unary_traverses {d m : ℕ} (hm : 0<m) (val : Site d m → Bool)
    (ok : Solves (graph d m) (fun s=>(val s).toNat)) (t : ℕ) (bound : t < (2*m)^d) :
    (flip bind (gridMachine d).step)^[2*m+t]
      (some (Turing.initList (gridMachine d) (CounterEngine.unary (2*m-1)))) =
      some (geomFrame (pointAt d ⟨t,bound⟩) (actualData val t)) := by
  have cap : 0<2*m := by omega
  induction t with
  | zero =>
    have pin : pointAt d (m:=2*m) ⟨0,bound⟩=origin d cap := rank_inj d ((rank_at d _).trans (origin_rank d cap).symm)
    rw [pin,Nat.add_zero]
    have ini:=CounterEngine.initialized (instructionOf d) (fun fs=>plan d fs true) (CounterEngine.unary (2*m-1))
    have len : (CounterEngine.unary (2*m-1)).length=2*m-1 := List.length_replicate ..
    rw [len,show 2*m-1+1=2*m by omega] at ini
    exact ini
  | succ t ih =>
    have prev : t<(2*m)^d := by omega
    let p:=pointAt d (m:=2*m) ⟨t,prev⟩
    let q:=pointAt d (m:=2*m) ⟨t+1,bound⟩
    have rp : rank d p=t := rank_at d _
    have rq : rank d q=t+1 := rank_at d _
    have adj : nextPoint d p true=some q := by
      have next:=odometer_advances d p true
      cases found : nextPoint d p true with
      | none => simp [found,orient,rp] at next; omega
      | some z =>
        have hz : rank d z=t+1 := by simpa [found,orient,rp] using next
        exact congrArg some (rank_inj d (hz.trans rq.symm))
    have tick:=move_at p q adj val ok
    rw [rp] at tick
    rw [Nat.add_succ,Function.iterate_succ_apply',ih prev]
    exact tick

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The same labels are produced by an advice-free unary-input machine, described
by a small De Morgan circuit, and subject to the explicit vertex-opening bound. -/
theorem unary_machine_separation (d a r W : ℕ) (hm : 0<a+r) (width : a+r≤2^W) :
    ∃ C : Circuit, FanInTwo C ∧ C.size≤3*(W*(d*d))+1 ∧
      (let val : Site d (a+r) → Bool := fun s=>C.eval (List.ofFn (PascalCircuit.gridInput W (cell s)))
       Solves (graph d (a+r)) (fun s=>(val s).toNat) ∧
       (∀ t : ℕ, ∀ h : t < (2*(a+r))^d,
         (flip bind (gridMachine d).step)^[2*(a+r)+t]
           (some (Turing.initList (gridMachine d) (CounterEngine.unary (2*(a+r)-1))))=
         some (geomFrame (pointAt d ⟨t,h⟩) (actualData val t))) ∧
       ∀ (S : Scheme (graph d (a+r))) (B : ℕ), Site.main (Grid.top (d:=d) hm) ∈ S.cut →
        (∀ c, (S.region c).card≤B) →
        a^d*(r+1)^d ≤ a^d*B+(r+1)^d*(d*r+1)*((d+1)*S.cut.card)) := by
  obtain ⟨C,shape,size,solves,lower⟩:=stack_separation d a r W hm width
  exact ⟨C,shape,size,solves,unary_traverses hm _ solves,lower⟩

end StackLayout.Wired

namespace UnaryPower
open Turing

abbrev K := Bool ⊕ Bool
private def input : K := .inl false
private def output : K := .inl true
private def work (p : Bool) : K := .inr p
abbrev Label := Bool × Fin 3
private abbrev St := TM2.Stmt (fun _ : K=>Bool) Label Bool
private def go (p : Bool) (l : Fin 3) : St := .load (fun _=>false) (.goto (fun _=>(p,l)))
private def program (q : Label) : St :=
  let p:=q.1
  if q.2=0 then .pop input (fun _ a=>a.isSome) <| .branch id
    (.push (work (!p)) (fun _=>false) (go p 1)) (go p 2)
  else if q.2=1 then .pop (work p) (fun _ a=>a.isSome) <| .branch id
    (.push (work (!p)) (fun _=>false) (.push (work (!p)) (fun _=>false) (go p 1))) (go (!p) 0)
  else .pop (work p) (fun _ a=>a.isSome) <| .branch id
    (.push output (fun _=>false) (go p 2)) (.load (fun _=>false) .halt)

/-- A fixed four-stack machine expanding an n-bit word to 2^n−1 false cells. -/
def machine : FinTM2 where
  K:=K; k₀:=input; k₁:=output; Γ:=fun _=>Bool; Λ:=Label; main:=(false,0); σ:=Bool; initialState:=false
  Γk₀Fin:=inferInstanceAs (Fintype Bool); m:=program

def unary (s : ℕ) := List.replicate s false
private def bank (p : Bool) (xs : List Bool) (src dst out : ℕ) : K → List Bool
  | .inl false=>xs
  | .inl true=>unary out
  | .inr i=>if i=p then unary src else unary dst
private def frame (p : Bool) (l : Fin 3) (xs : List Bool) (src dst out : ℕ) : machine.Cfg :=
  ⟨some (p,l),false,bank p xs src dst out⟩

private theorem set_input (p : Bool) (x y : List Bool) (s d o : ℕ) :
    Function.update (bank p x s d o) input y=bank p y s d o := by
  funext z; rcases z with b|b <;> cases b <;> simp [bank,input,Function.update]
private theorem set_output (p : Bool) (x : List Bool) (s d o o' : ℕ) :
    Function.update (bank p x s d o) output (unary o')=bank p x s d o' := by
  funext z; rcases z with b|b <;> cases b <;> simp [bank,output,Function.update]
private theorem set_src (p : Bool) (x : List Bool) (s s' d o : ℕ) :
    Function.update (bank p x s d o) (work p) (unary s')=bank p x s' d o := by
  funext z; rcases z with b|b <;> cases b <;> cases p <;> rfl
private theorem set_dst (p : Bool) (x : List Bool) (s d d' o : ℕ) :
    Function.update (bank p x s d o) (work (!p)) (unary d')=bank p x s d' o := by
  funext z; rcases z with b|b <;> cases b <;> cases p <;> rfl
private theorem switch (p : Bool) (x : List Bool) (s d o : ℕ) : bank p x s d o=bank (!p) x d s o := by
  funext z; rcases z with b|b <;> cases b <;> cases p <;> rfl

private theorem head_src (p : Bool) (x : List Bool) (s d o : ℕ) : bank p x s d o (work p)=unary s := by simp [bank,work]
private theorem head_dst (p : Bool) (x : List Bool) (s d o : ℕ) : bank p x s d o (work (!p))=unary d := by cases p <;> rfl
private theorem unary_succ (n : ℕ) : unary (n+1)=false::unary n := List.replicate_succ ..

private theorem open_round (p b : Bool) (xs : List Bool) (s : ℕ) :
    machine.step (frame p 0 (b::xs) s 0 0)=some (frame p 1 xs s 1 0) := by
  change some (TM2.stepAux (program (p,0)) false (bank p (b::xs) s 0 0))=_
  simp only [program,ite_true,TM2.stepAux,input,bank,List.head?_cons,List.tail_cons,Option.isSome_some,id_eq,Bool.cond_true]
  change some (TM2.stepAux (go p 1) true (Function.update (Function.update (bank p (b::xs) s 0 0) input xs) (work (!p))
    (false::Function.update (bank p (b::xs) s 0 0) input xs (work (!p)))))=_
  rw [set_input,head_dst,←unary_succ,set_dst]; rfl

private theorem finish_input (p : Bool) (s : ℕ) : machine.step (frame p 0 [] s 0 0)=some (frame p 2 [] s 0 0) := by
  change some (TM2.stepAux (program (p,0)) false (bank p [] s 0 0))=_
  simp only [program,ite_true,TM2.stepAux,input,bank,List.head?_nil,List.tail_nil,Option.isSome_none,id_eq,Bool.cond_false]
  change some (TM2.stepAux (go p 2) false (Function.update (bank p [] s 0 0) input []))=_
  rw [set_input]; rfl

private theorem double_cell (p : Bool) (xs : List Bool) (s d : ℕ) :
    machine.step (frame p 1 xs (s+1) d 0)=some (frame p 1 xs s (d+2) 0) := by
  change some (TM2.stepAux (program (p,1)) false (bank p xs (s+1) d 0))=_
  simp only [program,show (1:Fin 3)≠0 by decide,ite_false,ite_true,TM2.stepAux,head_src,unary_succ,List.head?_cons,
    List.tail_cons,Option.isSome_some,id_eq,Bool.cond_true]
  rw [set_src,head_dst,←unary_succ,set_dst,head_dst,←unary_succ,set_dst]
  rfl

private theorem double_end (p : Bool) (xs : List Bool) (d : ℕ) : machine.step (frame p 1 xs 0 d 0)=some (frame (!p) 0 xs d 0 0) := by
  change some (TM2.stepAux (program (p,1)) false (bank p xs 0 d 0))=_
  simp only [program,show (1:Fin 3)≠0 by decide,ite_false,ite_true,TM2.stepAux,head_src]
  change some (TM2.stepAux (go (!p) 0) false (Function.update (bank p xs 0 d 0) (work p) (unary 0)))=_
  rw [set_src,switch p]; rfl

private theorem emit_cell (p : Bool) (s o : ℕ) :
    machine.step (frame p 2 [] (s+1) 0 o)=some (frame p 2 [] s 0 (o+1)) := by
  change some (TM2.stepAux (program (p,2)) false (bank p [] (s+1) 0 o))=_
  simp only [program,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false,TM2.stepAux,head_src,unary_succ,
    List.head?_cons,List.tail_cons,Option.isSome_some,id_eq,Bool.cond_true]
  rw [set_src]
  change some (TM2.stepAux (go p 2) true (Function.update (bank p [] s 0 o) output (false::unary o)))=_
  rw [←unary_succ,set_output]; rfl

private theorem emit_end (p : Bool) (o : ℕ) : machine.step (frame p 2 [] 0 0 o)=some (haltList machine (unary o)) := by
  change some (TM2.stepAux (program (p,2)) false (bank p [] 0 0 o))=_
  simp only [program,show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,ite_false,TM2.stepAux,head_src]
  change some (⟨none,false,Function.update (bank p [] 0 0 o) (work p) (unary 0)⟩ : TM2.Cfg (fun _ : K=>Bool) Label Bool)=_
  rw [set_src]
  congr 2
  funext z; rcases z with b|b <;> cases b <;> cases p <;> rfl

end UnaryPower

namespace UnaryPower
open Turing

private abbrev Run (n : ℕ) (a b : machine.Cfg) := (flip bind machine.step)^[n] (some a)=some b
private theorem pre {n : ℕ} {a b c : machine.Cfg} (h : machine.step a=some b) (t : Run n b c) : Run (n+1) a c := by
  unfold Run
  rw [Function.iterate_succ_apply]
  change (flip bind machine.step)^[n] (machine.step a)=some c
  rwa [h]
private theorem join {n m : ℕ} {a b c : machine.Cfg} (h : Run n a b) (t : Run m b c) : Run (n+m) a c := by
  unfold Run at *
  rw [Nat.add_comm n m,Function.iterate_add_apply,h,t]

private theorem round_run (p : Bool) (xs : List Bool) (s d : ℕ) : Run (s+1)
    (frame p 1 xs s d 0) (frame (!p) 0 xs (d+2*s) 0 0) := by
  induction s generalizing d with
  | zero=>apply pre (double_end p xs d); simp [Run]
  | succ n ih=>
    apply pre (double_cell p xs n d)
    have eq : d+2*n.succ = (d+2)+2*n := by omega
    rw [eq]; exact ih (d+2)

private theorem emit_run (p : Bool) (s o : ℕ) : Run (s+1) (frame p 2 [] s 0 o) (haltList machine (unary (o+s))) := by
  induction s generalizing o with
  | zero=>apply pre (emit_end p o); rfl
  | succ n ih=>
    apply pre (emit_cell p n o)
    rw [show o+n.succ=o+1+n by omega]; exact ih (o+1)

private def amount : ℕ → ℕ → ℕ
  | 0,s=>s
  | n+1,s=>amount n (1+2*s)
private def duration : ℕ → ℕ → ℕ
  | 0,s=>s+2
  | n+1,s=>(s+1+1)+duration n (1+2*s)

private theorem total_run (p : Bool) (xs : List Bool) (s : ℕ) : Run (duration xs.length s)
    (frame p 0 xs s 0 0) (haltList machine (unary (amount xs.length s))) := by
  induction xs generalizing p s with
  | nil=>
    have take:=emit_run p s 0
    rw [Nat.zero_add] at take
    exact pre (finish_input p s) take
  | cons b xs ih=>exact join (pre (open_round p b xs s) (round_run p xs s 1)) (ih (!p) (1+2*s))

private theorem amount_formula (n s : ℕ) : amount n s+1=(s+1)*2^n := by
  induction n generalizing s with
  | zero=>simp [amount]
  | succ n ih=>rw [amount,ih,Nat.pow_succ]; ring

private theorem duration_formula (n s : ℕ) : duration n s+s=(s+1)*2^(n+1)+n := by
  induction n generalizing s with
  | zero=>simp [duration]; omega
  | succ n ih=>
    have e:=ih (1+2*s)
    rw [duration,show 2^(n+1+1)=2^(n+1)*2 from Nat.pow_succ ..]
    nlinarith

/-- Exponential expansion and its exact physical macrostep count. -/
theorem expands (xs : List Bool) :
    (flip bind machine.step)^[2^(xs.length+1)+xs.length] (some (initList machine xs))=
      some (haltList machine (unary (2^xs.length-1))) := by
  have start : initList machine xs=frame false 0 xs 0 0 0 := by
    unfold initList frame; congr 1; funext z; rcases z with b|b <;> cases b <;> rfl
  have n:=duration_formula xs.length 0
  simp only [Nat.add_zero,Nat.zero_add,Nat.one_mul] at n
  have s:=amount_formula xs.length 0
  simp only [Nat.zero_add,Nat.one_mul] at s
  rw [start,←n,show 2^xs.length-1=amount xs.length 0 by omega]
  exact total_run false xs 0

end UnaryPower
namespace StackLayout.Wired

open Turing PEqualNP.Library.Machines CutVerification

private theorem splice {A : Type} (F : A → A) {u v w : A} {a b : ℕ}
    (h : F^[a] u=v) (g : F^[b] v=w) : F^[b+a] u=w := by
  rw [Function.iterate_add_apply,h,g]

/-- Prefix simulation through the project's physical composition machine. -/
private theorem comp_prefix {M₁ M₂ : FinTM2} (φ : M₁.Γ M₁.k₁ → M₂.Γ M₂.k₀) (blank : M₂.Γ M₂.k₀)
    (i : List (M₁.Γ M₁.k₀)) (o : List (M₁.Γ M₁.k₁)) (c : M₂.Cfg) (s t : ℕ)
    (first : (flip bind M₁.step)^[s] (some (initList M₁ i))=some (haltList M₁ o))
    (second : (flip bind M₂.step)^[t] (some (initList M₂ (o.map φ)))=some c) :
    ∃ n ≤ s+(2*o.length+2)+t,
      (flip bind (comp M₁ M₂ φ (some blank)).step)^[n] (some (initList (comp M₁ M₂ φ (some blank)) i))=
        some (emb2 M₁.initialState none c) := by
  have p1:=simulate (TM2.step M₁.m) (TM2.step (prog M₁ M₂ φ (some blank)))
    (emb1 (M₂.initialState,none)) (step1 φ (some blank) _) s _ _ first
  rw [emb1_init φ (some blank),emb1_halt] at p1
  obtain ⟨nt,hnt,pt⟩:=transfer φ (some blank) (by simp) M₁.initialState M₂.initialState o
  have p2:=simulate (TM2.step M₂.m) (TM2.step (prog M₁ M₂ φ (some blank)))
    (emb2 M₁.initialState none) (step2 φ (some blank) _ _) t _ _ second
  rw [emb2_init] at p2
  refine ⟨t+(nt+s),by omega,?_⟩
  let F : Option (CCfg M₁ M₂) → Option (CCfg M₁ M₂):=flip bind (TM2.step (prog M₁ M₂ φ (some blank)))
  exact splice F (splice F p1 pt) p2

/-- A single machine for each fixed d. An input of n+1 bits gives a coarse
Pascal side 2^n and a physical traversal of (2^(n+1))^d vertices. -/
noncomputable def shortMachine (d : ℕ) : FinTM2 := comp UnaryPower.machine (gridMachine d) id (some false)

noncomputable def observedFrame {d m : ℕ} (p : Point d (2*m)) (S : Fin (d*2) → List Bool) : (shortMachine d).Cfg :=
  emb2 UnaryPower.machine.initialState none (geomFrame p S)

/-- The logarithmic-size input gives the full actual conditional state at every
address, with a uniform startup bound linear in the expanded side length. -/
theorem short_traverses {d n : ℕ} (xs : List Bool) (len : xs.length=n+1) (val : Site d (2^n) → Bool)
    (ok : Solves (graph d (2^n)) (fun s=>(val s).toNat)) (t : ℕ) (h : t<(2*(2^n))^d) :
    ∃ elapsed≤5*(2^(n+1))+xs.length+2+t,
      (flip bind (shortMachine d).step)^[elapsed] (some (initList (shortMachine d) xs))=
        some (observedFrame (pointAt d ⟨t,h⟩) (actualData val t)) := by
  let m:=2^n
  have pos : 0<m:=Nat.two_pow_pos _
  have side : 2^xs.length=2*m := by rw [len,Nat.pow_succ,Nat.mul_comm]
  have start:=UnaryPower.expands xs
  have grid:=unary_traverses pos val ok t h
  have mapid : ((UnaryPower.unary (2^xs.length-1)).map (id : Bool → Bool))=CounterEngine.unary (2*m-1) := by
    rw [List.map_id,side]; rfl
  have second : (flip bind (gridMachine d).step)^[2*m+t]
      (some (initList (gridMachine d) ((UnaryPower.unary (2^xs.length-1)).map (id : Bool→Bool))))=
      some (geomFrame (pointAt d ⟨t,h⟩) (actualData val t)) := by
    exact (congrArg (fun l : List Bool=>(flip bind (gridMachine d).step)^[2*m+t] (some (initList (gridMachine d) l))) mapid).trans grid
  obtain ⟨e,bnd,run⟩:=comp_prefix (M₁:=UnaryPower.machine) (M₂:=gridMachine d) id false xs _ _ _ _ start second
  refine ⟨e,?_,run⟩
  have cells : (UnaryPower.unary (2^xs.length-1)).length=2^xs.length-1 := List.length_replicate ..
  change e≤2^(xs.length+1)+xs.length+(2*(UnaryPower.unary (2^xs.length-1)).length+2)+(2*m+t) at bnd
  rw [cells,Nat.pow_succ 2 xs.length,side] at bnd
  rw [←len,side]
  omega

end StackLayout.Wired

namespace CutScaling

/-- An integer normalization of the two cut/opening terms. -/
private theorem normalize (P Q M H D B C : ℕ) (pos : 0<P*Q) (height : 1≤H)
    (first : M≤Q) (second : M*D≤H*P) (cover : P*Q≤P*B+Q*D*C) : M≤H*(B+C) := by
  apply Nat.le_of_mul_le_mul_left (c:=P*Q) (hc:=pos)
  calc
    P*Q*M ≤ (P*B+Q*D*C)*M := Nat.mul_le_mul_right _ cover
    _ = (M*P)*B+(M*D)*(Q*C) := by ring
    _ ≤ (Q*P)*B+(H*P)*(Q*C) := Nat.add_le_add (Nat.mul_le_mul_right B (Nat.mul_le_mul_right P first)) (Nat.mul_le_mul_right _ second)
    _ = (P*Q)*(B+H*C) := by ring
    _ ≤ (P*Q)*(H*(B+C)) := by
      apply Nat.mul_le_mul_left
      rw [Nat.mul_add]
      exact Nat.add_le_add_right (by simpa using Nat.mul_le_mul_right B height) _

/-- For side 2^((d+1)k), the number of explicit vertices disclosed is
at least 2^(d²k) divided by a factor depending only on dimension. -/
theorem dyadic (d k B C : ℕ) (hk : 0<k) :
    let r:=2^(d*k)
    let N:=2^((d+1)*k)
    let a:=N-r
    a^d*(r+1)^d≤a^d*B+(r+1)^d*(d*r+1)*((d+1)*C) →
    2^(d*(d*k))≤(2^d*(d+1)^2)*(B+C) := by
  dsimp only
  intro cover
  let r:=2^(d*k)
  let N:=2^((d+1)*k)
  let a:=N-r
  let H:=2^d*(d+1)^2
  change a^d*(r+1)^d≤a^d*B+(r+1)^d*(d*r+1)*((d+1)*C) at cover
  have rpos : 0<r:=Nat.two_pow_pos _
  have two : 2≤2^k := (show 2=2^1 by decide) ▸ Nat.pow_le_pow_right (by decide : 0<2) hk
  have N_eq : N=r*2^k := by dsimp [N,r]; rw [Nat.succ_mul,Nat.pow_add]
  have r2 : 2*r≤N := by rw [N_eq,Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r two
  have apos : 0<a := by dsimp [a]; omega
  have half : N≤2*a := by dsimp [a];omega
  have both : r^(d+1)=N^d := by dsimp [r,N]; rw [←Nat.pow_mul,←Nat.pow_mul]; congr 1;ring
  have mass : r^(d+1)≤2^d*a^d := by rw [both,←Nat.mul_pow]; exact Nat.pow_le_pow_left half _
  have pen : d*r+1≤(d+1)*r := by rw [Nat.succ_mul];omega
  have second : r^d*((d*r+1)*(d+1))≤H*a^d := by
    calc
      _ ≤ r^d*(((d+1)*r)*(d+1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ pen)
      _ = r^(d+1)*(d+1)^2 := by rw [Nat.pow_succ];ring
      _ ≤ (2^d*a^d)*(d+1)^2 := Nat.mul_le_mul_right _ mass
      _ = H*a^d := by dsimp [H];ring
  have bound:=normalize (a^d) ((r+1)^d) (r^d) H ((d*r+1)*(d+1)) B C
    (Nat.mul_pos (Nat.pow_pos apos) (Nat.pow_pos (Nat.succ_pos _)))
    (Nat.mul_pos (Nat.two_pow_pos d) (Nat.pow_pos (Nat.succ_pos d)))
    (Nat.pow_le_pow_left (Nat.le_succ r) d) second (by simpa only [Nat.mul_assoc] using cover)
  change 2^(d*(d*k))≤H*(B+C)
  exact (show 2^(d*(d*k))=r^d by dsimp [r]; rw [←Nat.pow_mul]; congr 1; ring) ▸ bound

end CutScaling

namespace CutScaling

/-- Any integer exponent gap p<q eventually beats the fixed dimension-q
normalization in the explicit-opening inequality, even with both additive constants. -/
theorem beats_allowance (p q K : ℕ) (less : p<q) :
    ∃ k : ℕ, 0<k ∧
      (2^q*(q+1)^2)*(2*(K*2^(p*((q+1)*k+1))+K)) < 2^(q*(q*k)) := by
  let H:=2^q*(q+1)^2
  let A:=H*4*K*(2^p)
  let k:=A+1
  let e:=(p*(q+1))*k
  have slot : p*(q+1)+1≤q*q := by have z:=Nat.mul_le_mul_right (q+1) less; nlinarith
  have exp : k+e≤q*(q*k) := by
    have z:=Nat.mul_le_mul_right k slot
    dsimp [e];rw [Nat.add_mul,Nat.one_mul] at z;rw [←Nat.mul_assoc]; omega
  have split : p*((q+1)*k+1)=e+p := by dsimp [e];ring
  have factor : K ≤ K*2^(p*((q+1)*k+1)) := by simpa using Nat.mul_le_mul_left K (Nat.one_le_two_pow (n:=p*((q+1)*k+1)))
  have small : A<2^k := (Nat.lt_succ_self A).trans Nat.lt_two_pow_self
  refine ⟨k,Nat.succ_pos _,?_⟩
  change H*(2*(K*2^(p*((q+1)*k+1))+K)) < 2^(q*(q*k))
  calc
    _ ≤ H*(2*(K*2^(p*((q+1)*k+1))+K*2^(p*((q+1)*k+1)))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left factor _))
    _ = A*2^e := by rw [split,Nat.pow_add]; dsimp [A];ring
    _ < 2^k*2^e := Nat.mul_lt_mul_of_pos_right small (Nat.two_pow_pos _)
    _ = 2^(k+e) := (Nat.pow_add ..).symm
    _ ≤ 2^(q*(q*k)) := Nat.pow_le_pow_right (by decide) exp

/-- The entire startup plus any one of the true grid times fits the same
2^(qN) clock on the original N-bit input. -/
theorem startup (q n t : ℕ) (hq : 0<q) (ht : t<(2*(2^n))^q) :
    5*2^(n+1)+(n+1)+2+t≤9*2^(q*(n+1)) := by
  have e : n+1≤q*(n+1) := by simpa using Nat.mul_le_mul_right (n+1) hq
  have large := Nat.pow_le_pow_right (by decide : 0<2) e
  have width : (2*(2^n))^q=2^(q*(n+1)) := by
    rw [Nat.mul_comm 2,←Nat.pow_succ,←Nat.pow_mul,Nat.mul_comm]
  rw [width] at ht
  have pos:=Nat.two_pow_pos (q*(n+1))
  have nlt : n+1<2^(n+1):=Nat.lt_two_pow_self
  omega

end CutScaling
namespace StackLayout.Wired
open Turing CutVerification PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem separation_at (d a r n N : ℕ) (eq : a+r=N) (hp : 0<N) (w : N≤2^n) :
    ∃ C : Circuit, FanInTwo C ∧ C.size≤3*(n*(d*d))+1 ∧
      Solves (graph d N) (fun s=>(C.eval (List.ofFn (PascalCircuit.gridInput n (cell s)))).toNat) ∧
      ∀ (S : Scheme (graph d N)) (B : ℕ), Site.main (Grid.top (d:=d) hp) ∈ S.cut →
        (∀ c, (S.region c).card≤B) → a^d*(r+1)^d≤a^d*B+(r+1)^d*(d*r+1)*((d+1)*S.cut.card) := by
  subst N
  exact stack_separation d a r n hp w

/-- One fixed multistack machine per dimension reads a logarithmic-size input.
Every true Pascal site has a logarithmic-size circuit description, while all
explicit predecessor-opening schemes must disclose exponentially many vertices. -/
theorem short_machine_separation (d k : ℕ) (hk : 0<k) (xs : List Bool) (len : xs.length=(d+1)*k+1) :
    let n:=(d+1)*k
    let N:=2^n
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 3*(n*(d*d))+1 ∧
      (let val : Site d N → Bool:=fun s=>C.eval (List.ofFn (PascalCircuit.gridInput n (cell s)))
       Solves (graph d N) (fun s=>(val s).toNat) ∧
       (∀ t : ℕ, ∀ h : t<(2*N)^d, ∃ elapsed≤5*(2^(n+1))+xs.length+2+t,
          (flip bind (shortMachine d).step)^[elapsed] (some (initList (shortMachine d) xs))=
            some (observedFrame (pointAt d ⟨t,h⟩) (actualData val t))) ∧
       ∀ (S : Scheme (graph d N)) (B : ℕ), Site.main (Grid.top (d:=d) (Nat.two_pow_pos n)) ∈ S.cut →
         (∀ c,(S.region c).card≤B) → 2^(d*(d*k))≤2^d*(d+1)^2*(B+S.cut.card)) := by
  let n:=(d+1)*k
  let N:=2^n
  let r:=2^(d*k)
  let a:=N-r
  have rle : r≤N := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right k (Nat.le_succ d))
  have ar : a+r=N:=Nat.sub_add_cancel rle
  have cert:=separation_at d a r n N ar (Nat.two_pow_pos _) le_rfl
  obtain ⟨C,shape,size,solves,lower⟩:=cert
  refine ⟨C,shape,size,solves,short_traverses xs len _ solves,?_⟩
  intro S B out width
  exact CutScaling.dyadic d k B S.cut.card hk (lower S B out width)

end StackLayout.Wired

namespace StackLayout.Wired
open Turing CutVerification PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- For every candidate pair p<q and coefficient K there is a real O(2^(qN))
trace on an N-bit word that defeats every explicit cut/opening scheme bounded
by K*2^(pN)+K on both disclosure sizes. Its true vertex labels still have a
small addressed circuit. This statement quantifies precisely over `Scheme`. -/
theorem explicit_opening_barrier (p q K : ℕ) (less : p<q) :
    ∃ k : ℕ, 0<k ∧ ∃ xs : List Bool, xs.length=(q+1)*k+1 ∧
      (let n:=(q+1)*k
       let N:=2^n
       ∃ C : Circuit, FanInTwo C ∧ C.size≤3*(n*(q*q))+1 ∧
        (let val : Site q N → Bool:=fun s=>C.eval (List.ofFn (PascalCircuit.gridInput n (cell s)))
         Solves (graph q N) (fun s=>(val s).toNat) ∧
         (∀ t : ℕ, ∀ h : t<(2*N)^q, ∃ elapsed≤9*2^(q*xs.length),
           (flip bind (shortMachine q).step)^[elapsed] (some (initList (shortMachine q) xs))=
             some (observedFrame (pointAt q ⟨t,h⟩) (actualData val t))) ∧
         ∀ S : Scheme (graph q N), Site.main (Grid.top (d:=q) (Nat.two_pow_pos n)) ∈ S.cut →
           (∀ c,(S.region c).card≤K*2^(p*xs.length)+K) → K*2^(p*xs.length)+K < S.cut.card)) := by
  obtain ⟨k,hk,gap⟩:=CutScaling.beats_allowance p q K less
  let n:=(q+1)*k
  let xs:=List.replicate (n+1) false
  have len : xs.length=(q+1)*k+1:=List.length_replicate ..
  obtain ⟨C,shape,size,solves,runs,lower⟩:=short_machine_separation q k hk xs len
  refine ⟨k,hk,xs,len,C,shape,size,solves,?_,?_⟩
  · intro t h
    obtain ⟨time,budget,run⟩:=runs t h
    refine ⟨time,?_,run⟩
    rw [len] at budget ⊢
    exact budget.trans (CutScaling.startup q n t (by omega) h)
  · intro S out width
    let limit:=K*2^(p*xs.length)+K
    have need:=lower S limit out width
    by_contra! small
    have both : limit+S.cut.card≤2*limit := by change S.cut.card≤limit at small;omega
    have rate:=(need.trans (Nat.mul_le_mul_left (2^q*(q+1)^2) both))
    exact (Nat.not_lt_of_ge rate) (by simpa only [limit,len] using gap)

end StackLayout.Wired

#print axioms StackLayout.Wired.short_traverses
#print axioms StackLayout.Wired.short_machine_separation
#print axioms StackLayout.Wired.explicit_opening_barrier
