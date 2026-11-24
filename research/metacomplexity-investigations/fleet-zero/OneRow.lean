import ZeroSize
import ParityEncoding
import ParityCircuitReplay

namespace ParityEncoding
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open MetaComplexity.LocalThreshold

theorem fixed_zero_mem {a : ℕ} (T : List (Option Bool)) (hlen : T.length=2^a) :
    (false::encodePartial T)∈PartialMCSP ↔
    ∃ f, Consistent a T f ∧ HasCircuitSize a f 0 := by
  constructor
  · rintro ⟨a',s',T',e,h,f,hc,hs⟩
    obtain ⟨e1,e2⟩ := LocalConstruct.split_unique 0 s' _ _ e
    obtain eq := LocalConstruct.encodePartial_injective _ _ e2
    subst s'; subst T'
    have ea : a'=a := Nat.pow_right_injective (Nat.le_refl 2) (h.symm.trans hlen)
    subst a'; exact ⟨f,hc,hs⟩
  · rintro ⟨f,hc,hs⟩
    exact ⟨a,0,T,rfl,hlen,f,hc,hs⟩

theorem index_one (x : Fin 1→Bool) : tableIndex x=if x 0 then 1 else 0 := by
  unfold tableIndex
  rw [Fin.sum_univ_one]
  cases x 0 <;> simp

theorem one_mem (T : List (Option Bool)) (hlen : T.length=2^1) :
    (false::encodePartial T)∈PartialMCSP ↔ (T.getD 0 none) ≠ some true := by
  rw [fixed_zero_mem T hlen]
  constructor
  · rintro ⟨f,consistent,sized⟩ h
    let z : Fin 1→Bool := fun _=>false
    have ix : tableIndex z=0 := by simp [tableIndex,z]
    have val := consistent z true (by rwa [ix])
    rcases (size_zero_iff f).mp sized with rfl|⟨i,rfl⟩ <;> simp [z] at val
  · intro ok
    by_cases one : T.getD 1 none = some true
    · refine ⟨fun x=>x 0,?_,(size_zero_iff _).mpr (.inr ⟨0,rfl⟩)⟩
      intro x b hb
      change x 0=b
      rw [index_one] at hb
      cases e : x 0 <;> cases b <;> simp_all
    · refine ⟨fun _=>false,?_,(size_zero_iff _).mpr (.inl rfl)⟩
      intro x b hb
      cases b with
      | false => rfl
      | true =>
        exfalso
        rw [index_one] at hb
        cases e : x 0 <;> simp_all

theorem one_scope {n q : ℕ} (w : (Fin n→Bool)→List Bool)
    (T : (Fin n→Bool)→List (Option Bool)) (loc : QueryLocal n q w)
    (fmt : ∀ x, w x=false::encodePartial (T x) ∧ (T x).length=2^1)
    (red : ∀ x, (Finset.univ.filter fun i : Fin n=>x i=true).card % 2=1 ↔ w x∈PartialMCSP) :
    n ≤ q := by
  classical
  let z : Fin n→Bool := fun _=>false
  have bad : w z∉PartialMCSP := by
    rw [← red z]
    simp [z]
  have hz : (T z).getD 0 none = some true := by
    by_contra h
    exact bad ((fmt z).1 ▸ (one_mem (T z) (fmt z).2).mpr h)
  obtain ⟨S,sc,cert⟩ := (fixed_locality (s:=0) w T loc (fun x=>(fmt x).1) z 0).2
  by_contra small
  obtain ⟨i,absent⟩ := Helpers.LocalFormat.exists_notMem S (by omega)
  let u := Helpers.LocalFormat.unit i
  have tag := cert u (Helpers.LocalFormat.unit_agree i S absent)
  have good : w u∈PartialMCSP := (red u).mp (Helpers.LocalFormat.unit_odd i)
  rw [(fmt u).1,one_mem (T u) (fmt u).2] at good
  apply good
  exact decode_one (by simpa only [hz,value,Option.getD_some] using tag)

end ParityEncoding
#print axioms ParityEncoding.fixed_zero_mem
#print axioms ParityEncoding.one_mem
#print axioms ParityEncoding.one_scope
