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

namespace PascalStream

open Turing

/-- A bit address is grouped by binary place, with one bit of each coordinate in
each group. One command reads one group. The grouping is fixed in the machine. -/
abbrev State := Bool × Bool × Bool
private def blank : State := (true,false,false)
private abbrev St := TM2.Stmt (fun _ : Unit => Bool) Unit State

private def feed (r : State) (x : Option Bool) : State :=
  let b:=x.getD false
  (r.1 && !(r.2.1 && b),r.2.1 || b,false)

private def group : ℕ → St
  | 0 => .load (fun r=>(r.1,false,false)) (.goto fun _=>())
  | n+1 => .pop () feed (group n)

def code (d : ℕ) (_ : Unit) : St :=
  .peek () (fun r x=>(r.1,false,x.isSome)) (.branch (fun r=>r.2.2)
    (group d) (.push () Prod.fst (.load (fun _=>blank) .halt)))

def machine (d : ℕ) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _=>Bool
  Λ := Unit
  main := ()
  σ := State
  initialState := blank
  m := code d

abbrev column (xs : List Bool) := xs.count true ≤ 1

private def cfg (input : List Bool) (r : State) : TM2.Cfg (fun _ : Unit => Bool) Unit State :=
  ⟨some (),r,fun _=>input⟩

private theorem updated (x xs : List Bool) :
    Function.update (fun _ : Unit => x) () xs = fun _=>xs := by funext i; cases i; simp

private theorem group_aux (xs tail : List Bool) (r : State) :
    TM2.stepAux (group xs.length) r (fun _=>xs++tail) =
      cfg tail ((xs.foldl (fun acc b=>feed acc (some b)) r).1,false,false) := by
  induction xs generalizing r with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.length_cons,group,TM2.stepAux,List.cons_append,List.head?_cons,List.tail_cons,
      updated,ih,List.foldl_cons]

private theorem fold_value (xs : List Bool) (ok seen tag : Bool) :
    (xs.foldl (fun acc b=>feed acc (some b)) (ok,seen,tag)).1 =
      (ok && decide (xs.count true + seen.toNat ≤ 1)) := by
  induction xs generalizing ok seen tag with
  | nil => cases seen <;> simp
  | cons b xs ih =>
    rw [List.foldl_cons]
    change (xs.foldl _ (ok && !(seen && b),seen || b,false)).1 = _
    rw [ih]
    cases b <;> cases seen <;> cases ok <;>
      simp [Bool.toNat,show ¬xs.count true+1+1≤1 by omega]

private theorem one_column (d : ℕ) (xs tail : List Bool) (len : xs.length=d) (pos : 0<d) (ok : Bool) :
    (machine d).step (cfg (xs++tail) (ok,false,false)) =
      some (cfg tail (ok && decide (column xs),false,false)) := by
  have nonempty : xs≠[] := by intro e; simp [e] at len; omega
  have has : (xs++tail).head?.isSome=true := by
    cases xs with
    | nil => contradiction
    | cons x xs => rfl
  change TM2.step (code d) _ = _
  simp only [TM2.step,code,cfg,TM2.stepAux,has]
  rw [←len,group_aux,fold_value]
  simp [column,cfg]

private theorem final_step (d : ℕ) (ok : Bool) :
    (machine d).step (cfg [] (ok,false,false)) = some (haltList (machine d) [ok]) := by
  change TM2.step (code d) _=_
  simp [TM2.step,code,cfg,TM2.stepAux,haltList,machine,updated]
  rfl

private theorem start_frame (d : ℕ) (xs : List Bool) :
    initList (machine d) xs=cfg xs (true,false,false) := by
  unfold initList cfg machine
  congr 1

private theorem process {d : ℕ} (hd : 0<d) (cs : List (List Bool))
    (lens : ∀ c∈cs,c.length=d) (ok : Bool) :
    (flip bind (machine d).step)^[cs.length+1] (some (cfg cs.flatten (ok,false,false))) =
      some (haltList (machine d) [ok && cs.all (fun c=>decide (column c))]) := by
  induction cs generalizing ok with
  | nil =>
    change (machine d).step (cfg [] (ok,false,false)) = some (haltList (machine d) [ok && true])
    simpa using final_step d ok
  | cons c cs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    change (flip bind (machine d).step)^[cs.length+1] ((machine d).step (cfg (c++cs.flatten) (ok,false,false))) = _
    rw [one_column d _ _ (lens c List.mem_cons_self) hd]
    apply (ih (fun _ h => lens _ (List.mem_cons_of_mem _ h)) (ok && decide (column c))).trans
    simp [Bool.and_assoc]

/-- Returns the actual one-bit output with all machine work storage restored. -/
def outputs {d : ℕ} (hd : 0<d) (cs : List (List Bool)) (lens : ∀ c∈cs,c.length=d) :
    TM2OutputsInTime (machine d) cs.flatten (some [cs.all (fun c=>decide (column c))]) (cs.length+1) := by
  refine ⟨⟨cs.length+1,?_⟩,le_rfl⟩
  rw [start_frame]
  simpa using process hd cs lens true

end PascalStream
namespace PascalStream

open CutVerification
open Turing

private theorem pair_condition {d : ℕ} (f : Fin d → Bool) :
    column (List.ofFn f) ↔ ∀ i j : Fin d, i<j → f i=true → f j=false := by
  simp only [column,List.count_ofFn,Finset.card_le_one,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro unique i j lt ok
    cases bad : f j
    · rfl
    · exact False.elim ((Fin.ne_of_lt lt) (unique i ok j bad))
  · intro noPair i hi j hj
    rcases lt_trichotomy i j with lt|eq|gt
    · exact False.elim (Bool.noConfusion ((noPair _ _ lt hi).symm.trans hj))
    · exact eq
    · exact False.elim (Bool.noConfusion ((noPair _ _ gt hj).symm.trans hi))

/-- Encodes an address as binary places, then coordinates within each place. -/
def columns {d m : ℕ} (W : ℕ) (p : Grid.Point d m) : List (List Bool) :=
  List.ofFn (fun k : Fin W => List.ofFn (fun i : Fin d => PascalCircuit.bitsOf W (p i).val k))

private theorem column_answer {d m : ℕ} (W : ℕ) (p : Grid.Point d m) (width : m ≤ 2^W) :
    (columns W p).all (fun xs=>decide (column xs)) = decide (PascalGrid.ways (PascalGrid.coord p)%2=1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,decide_eq_true_eq,columns,List.forall_mem_ofFn_iff,pair_condition]
  have h := PascalGrid.pascal_ports d W (fun i k => PascalCircuit.bitsOf W (p i).val k)
  have dec (i : Fin d) : PascalGrid.decode W (PascalCircuit.bitsOf W (p i).val) = (p i).val :=
    PascalCircuit.decode_bits _ _ ((p i).isLt.trans_le width)
  simp only [dec] at h
  exact h.symm

/-- The same fixed machine for dimension d returns a grid-site label from the
binary address alone in W + 1 macrosteps on its dW-bit encoding. -/
def actual_label {d m : ℕ} (hd : 0<d) (W : ℕ) (p : Grid.Point d m) (width : m≤2^W) :
    TM2OutputsInTime (machine d) (columns W p).flatten
      (some [decide (PascalGrid.ways (PascalGrid.coord p)%2=1)]) (W+1) := by
  rw [←column_answer W p width]
  have h := outputs hd (columns W p) (by simp [columns])
  simpa only [columns,List.length_ofFn] using h

open StackLayout.Wired

/-- The direct address reader supplies every correct label of the concrete wired
stack dataflow and outputs each bit with empty auxiliary stacks. -/
theorem labels_without_witness {d m : ℕ} (hd : 0<d) (W : ℕ) (width : m≤2^W) :
    ∃ val : Site d m → Bool, Solves (graph d m) (fun s=>(val s).toNat) ∧
    ∀ s, Nonempty (TM2OutputsInTime (machine d) (columns W (cell s)).flatten (some [val s]) (W+1)) := by
  let val := fun s : Site d m=>decide (PascalGrid.ways (PascalGrid.coord (cell s))%2=1)
  refine ⟨val,?_,fun s=>⟨actual_label hd W (cell s) width⟩⟩
  have ok (p : Grid.Point d m) : (decide (PascalGrid.ways (PascalGrid.coord p)%2=1)).toNat =
      PascalGrid.ways (PascalGrid.coord p)%2 := by
    by_cases one : PascalGrid.ways (PascalGrid.coord p)%2=1 <;> simp [one]; omega
  simpa only [val,ok] using mirrored_labels (PascalGrid.labels_solve d m)

end PascalStream

#print axioms StackLayout.Wired.finite_machine_separation
#print axioms PascalStream.labels_without_witness
