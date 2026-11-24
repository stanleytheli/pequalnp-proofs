import PortAccess
import BinaryWords

namespace SparsePermanent.DirectedGrowth
open Finset BinaryWords
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- A simultaneous collection of full directed binary trees through depth R.
Two opposite orientations may share their center. Every non-root vertex
belongs to only one tree. -/
structure Forest (dir : I→V→V→Prop) (R : ℕ) where
  node : I→Word→V
  inject : ∀ i u v,u.length≤R→v.length≤R→node i u=node i v→u=v
  apart : ∀ i j,i≠j→∀ u v,0<u.length→u.length≤R→v.length≤R→node i u≠node j v
  step : ∀ i u,u.length<R→∀ b : Bool,dir i (node i u) (node i (u++[b]))

namespace Forest
variable {dir : I→V→V→Prop} {R : ℕ} (T : Forest dir R)

noncomputable def under (i : I) (w : Word) (S : Finset Word) :=
  S.image (fun z=>T.node i (w++z))
noncomputable def core (h : ℕ) := univ.biUnion (fun i : I=>(through h).image (T.node i))

theorem core_card (h : ℕ) : (T.core h).card≤Fintype.card I*2^(h+1) := by
  classical
  calc
    _ ≤ ∑ i : I,((through h).image (T.node i)).card := card_biUnion_le
    _ ≤ ∑ _i : I,2^(h+1) := sum_le_sum (fun _ _=>card_image_le.trans (card_through h))
    _ = _ := by simp

private theorem at_depth {i : I} {u : Word} {h : ℕ} (pos : 0<u.length) (bound : u.length≤R)
    (small : h≤R) (inside : T.node i u∈T.core h) : u.length≤h := by
  obtain ⟨j,_,hit⟩:=mem_biUnion.mp inside
  obtain ⟨v,old,e⟩:=mem_image.mp hit
  have vl:=mem_through.mp old
  by_cases eq : i=j
  · subst j
    have same:=T.inject _ _ _ bound (vl.trans small) e.symm
    simpa [same] using vl
  · exact False.elim (T.apart i j eq u v pos bound (vl.trans small) e.symm)

private theorem walk {i : I} (w z : Word) (h : ℕ) (size : z.length≤h) (budget : w.length+h≤R) :
    Route (dir i) (univ \ T.under i w (through h)) (T.node i w) (T.node i (w++z)) z.length := by
  have safe (u : Word) (hu : u.length≤h) : T.node i (w++u)∉univ\T.under i w (through h) := by
    intro miss
    exact (mem_sdiff.mp miss).2 (mem_image.mpr ⟨u,mem_through.mpr hu,rfl⟩)
  induction z using List.reverseRecOn with
  | nil=>
    simpa using (Route.nil (E:=dir i) (safe [] (by simp)))
  | append_singleton z b ih=>
    have small : z.length+1≤h := by simpa using size
    have prev:=ih (by omega)
    have edge:=T.step i (w++z) (by simp at size ⊢;omega) b
    simpa [List.append_assoc] using Route.snoc prev edge (by simpa [List.append_assoc] using safe (z++[b]) size)

private theorem fat {i : I} {w : Word} {s : ℕ} (bound : w.length+s≤R) :
    (T.under i w (words s)).card=2^s := by
  rw [under,card_image_of_injOn,card_words]
  intro a ha b hb same
  apply List.append_right_injective w
  exact T.inject i _ _ (by simp [mem_words.mp ha];omega) (by simp [mem_words.mp hb];omega) same

private theorem branches_disjoint (i : I) (w : Word) (s : ℕ) (bound : w.length+2*s≤R) :
    Pairwise (fun a b : Fin (2^s)=>Disjoint
      (T.under i (w++((enumerate s) a).val) (through s)) (T.under i (w++((enumerate s) b).val) (through s))) := by
  intro a b neq
  apply disjoint_left.mpr
  intro v ha hb
  obtain ⟨x,hx,ex⟩:=mem_image.mp ha
  obtain ⟨y,hy,ey⟩:=mem_image.mp hb
  have ax:=mem_words.mp ((enumerate s) a).prop
  have ay:=mem_words.mp ((enumerate s) b).prop
  have sx:=mem_through.mp hx
  have sy:=mem_through.mp hy
  have same:=T.inject i _ _ (by simp [ax];omega) (by simp [ay];omega) (ex.trans ey.symm)
  have tail:=List.append_right_injective w (by simpa only [List.append_assoc] using same)
  exact neq ((enumerate s).injective (Subtype.ext (prefix_eq (ax.trans ay.symm) tail)))

/-- A depth-l prefix in a depth-(l+2s) full binary tree provides 2^s private
groups of 2^s available leaves and paths of exactly 2s arcs. -/
noncomputable def port (i : I) (w : Word) (l s : ℕ) (length : w.length=l) (pos : 0<s)
    (budget : l+2*s≤R) : Port (dir i) (T.core (l+s)) (2^s) (2^s) (2*s) where
  origin:=T.node i w
  trunk:=T.under i w (through s)
  trunk_in:=by
    intro x hx
    obtain ⟨z,hz,e⟩:=mem_image.mp hx
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨w++z,mem_through.mpr
      (by simp [length]; exact mem_through.mp hz),e⟩⟩
  group:=fun j=>T.under i (w++((enumerate s) j).val) (through s)
  leaves:=fun j=>T.under i (w++((enumerate s) j).val) (words s)
  separate:=T.branches_disjoint i w s (by omega)
  in_group:=by
    intro j a ha
    obtain ⟨z,hz,e⟩:=mem_image.mp ha
    exact mem_image.mpr ⟨z,mem_through.mpr (mem_words.mp hz).le,e⟩
  many:=by intro j; exact (T.fat (by simp [length,mem_words.mp ((enumerate s) j).prop];omega)).ge
  out_P:=by
    intro j
    apply disjoint_left.mpr
    intro a ha hp
    obtain ⟨z,hz,e⟩:=mem_image.mp ha
    rw [←e] at hp
    have len : ((w++((enumerate s) j).val)++z).length=l+2*s := by
      simp [length,mem_words.mp ((enumerate s) j).prop,mem_words.mp hz];omega
    have short:=T.at_depth (by omega) (by omega) (by omega) hp
    omega
  clear:=by
    intro j a ha
    obtain ⟨inside,hp⟩:=mem_inter.mp ha
    obtain ⟨z,hz,e⟩:=mem_image.mp inside
    rw [←e] at hp ⊢
    have zj:=mem_through.mp hz
    have len : ((w++((enumerate s) j).val)++z).length=l+s+z.length := by
      simp [length,mem_words.mp ((enumerate s) j).prop,Nat.add_assoc]
    have short:=T.at_depth (by omega) (by omega) (by omega) hp
    have empty : z=[]:=List.length_eq_zero_iff.mp (by omega)
    subst z
    exact mem_image.mpr ⟨_,mem_through.mpr (mem_words.mp ((enumerate s) j).prop).le,by simp⟩
  access:=by
    intro j a ha
    obtain ⟨z,hz,e⟩:=mem_image.mp ha
    have groupLen:=mem_words.mp ((enumerate s) j).prop
    have finalLen:=mem_words.mp hz
    let part:=((enumerate s) j).val
    have start:=T.walk (i:=i) w part s groupLen.le (by omega)
    have finish:=T.walk (i:=i) (w++part) z s finalLen.le (by simp [part,length,groupLen];omega)
    have tour:=(start.mono (sdiff_subset_sdiff_right univ subset_union_left)).trans
      (finish.mono (sdiff_subset_sdiff_right univ subset_union_right))
    refine ⟨part.length+z.length,by dsimp [part];omega,?_⟩
    rw [←e]; exact tour

/-- Different depth-l prefixes have disjoint protected port subtrees. -/
theorem port_disjoint {i j : I} {u v : Word} {l s : ℕ} (lu:u.length=l) (lv:v.length=l)
    (lp : 0<l) (sp : 0<s) (budget : l+2*s≤R) (distinct : i≠j ∨ u≠v) :
    Disjoint (T.port i u l s lu sp budget).trunk (T.port j v l s lv sp budget).trunk := by
  apply disjoint_left.mpr
  intro x a b
  obtain ⟨p,hp,ep⟩:=mem_image.mp a
  obtain ⟨q,hq,eq⟩:=mem_image.mp b
  have hp':=mem_through.mp hp
  have hq':=mem_through.mp hq
  have bp : (u++p).length≤R := by simp [lu];omega
  have bq : (v++q).length≤R := by simp [lv];omega
  by_cases e : i=j
  · subst j
    exact (distinct.resolve_left (by simp)) (prefix_eq (lu.trans lv.symm) (T.inject i _ _ bp bq (ep.trans eq.symm)))
  · exact T.apart i j e _ _ (by simp [lu];omega) bp bq (ep.trans eq.symm)

end Forest
end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Forest.port
