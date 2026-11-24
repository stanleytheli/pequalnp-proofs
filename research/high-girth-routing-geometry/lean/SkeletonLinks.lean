import ForestRouting
import RouteSimple

namespace SparsePermanent.DirectedGrowth
open Finset BinaryWords
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

namespace Forest
variable {dir:I→V→V→Prop} {R:ℕ} (T:Forest dir R)

theorem core_mono {i j : ℕ} (h:i≤j) : T.core i⊆T.core j := by
  intro x hx
  obtain ⟨a,ha,w⟩:=mem_biUnion.mp hx
  obtain ⟨z,hz,eq⟩:=mem_image.mp w
  exact mem_biUnion.mpr ⟨a,ha,mem_image.mpr ⟨z,mem_through.mpr ((mem_through.mp hz).trans h),eq⟩⟩

/-- A port's trunk meets the original short routing skeleton only at its
own port. This remains true for unused leaves of the full binary trees. -/
theorem trunk_origin (i:I) (w:Word) (l s:ℕ) (hw:w.length=l) (lp:0<l) (sp:0<s) (budget:l+2*s≤R)
    {x:V} (hit:x∈(T.port i w l s hw sp budget).trunk) (core:x∈T.core l) :
    x=(T.port i w l s hw sp budget).origin := by
  obtain ⟨z,hz,ze⟩:=mem_image.mp hit
  obtain ⟨j,_,cover⟩:=mem_biUnion.mp core
  obtain ⟨u,hu,ue⟩:=mem_image.mp cover
  have len:=mem_through.mp hu
  have zl:=mem_through.mp hz
  have positive:0<(w++z).length:=by simp [hw];omega
  have depth:(w++z).length≤R:=by simp [hw];omega
  by_cases same:i=j
  · subst j
    have eq:=T.inject i (w++z) u depth (by omega) (ze.trans ue.symm)
    have equal:=congrArg List.length eq
    simp only [List.length_append,hw] at equal
    have nil:z=[]:=List.length_eq_zero_iff.mp (by omega)
    change x=T.node i w
    simpa [nil] using ze.symm
  · exact False.elim (T.apart i j same (w++z) u positive depth (by omega) (ze.trans ue.symm))

variable {E:V→V→Prop} {m l s M:ℕ}

/-- An ordered path between a demand's two private ports meets the complete
short skeleton only at its endpoints. -/
theorem protected_ends (T:Forest (@oriented V E m) R) (width:m≤2^l) (lp:0<l) (sp:0<s) (budget:l+2*s≤R)
    (p:Fin m×Fin m) {xs:List V} (path:PrivatePath (M:=M) (T.demand width sp budget p) xs) :
    ∀x∈xs,x∈T.core l→x=(T.demand width sp budget p).forward.origin ∨ x=(T.demand width sp budget p).backward.origin := by
  intro x hx hcore
  have h:=path.2.2 (mem_inter.mpr ⟨List.mem_toFinset.mpr hx,T.core_mono (show l≤l+s by omega) hcore⟩)
  rcases mem_union.mp h with f|b
  · left;exact T.trunk_origin _ _ _ _ (mem_words.mp ((enumerate l) (p.2.castLE width)).property) lp sp budget f hcore
  · right;exact T.trunk_origin _ _ _ _ (mem_words.mp ((enumerate l) (p.1.castLE width)).property) lp sp budget b hcore

end Forest
end SparsePermanent.DirectedGrowth
#print axioms SparsePermanent.DirectedGrowth.Forest.protected_ends
