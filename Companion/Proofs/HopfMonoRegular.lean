module

public import Companion.Foundations.CategoryTheory.Limits.RegularMonoEquivalence
public import Companion.Hopf.Cocommutative.CommComonCartesianClosed
public import Companion.Hopf.Embed.CommComonEmbeds
public import Companion.InternalGroups.GrpStabilizerRegular
public import UlmerBialgebras.Proofs.Sec6.SubgroupCorrespondenceBiIdeal

/-!
# Every monomorphism of cocommutative Hopf algebras over a field is regular

Let `k` be a field. In `Grp (CommComon (ModuleCat k))`, the category of cocommutative Hopf
`k`-algebras, every monomorphism is regular:

1. every monomorphism of internal groups into `H` is a stabilizer, because Newman's bi-ideal map
   of `H` is injective (`InternalGroups.biIdealMap_bijective_of_field`,
   `InternalGroups.biIdealMap_injective_iff_mono`);
2. `CommComon (ModuleCat k)` is cartesian closed
   (`UlmerBialgebras.CommComon.monoidalClosed_moduleCat`) and every cocommutative coalgebra embeds
   into a cocommutative Hopf algebra (`InternalGroups.embedsInGrpObj_commComon_moduleCat`), so
   every stabilizer is regular, as an equalizer into a wreath product
   (`InternalGroups.isRegularMono_of_grpIsStabilizer_of_embedsInGrpObj`).

The same holds for `CocommHopf (ModuleCat k)`, through the equivalence
`UlmerBialgebras.GrpHopf.grpCommComonEquivCocommHopf`.

A monomorphism of `Grp C` is also a monomorphism of `C`, since the forgetful functor preserves
limits. So the monomorphisms of internal groups and the monomorphisms of `Hopf_k^coc` are the
same.

## Main results

* `InternalGroups.isRegularMonoCategory_grp_commComon_of_field`: every monomorphism of
  `Grp (CommComon (ModuleCat k))` is regular;
* `InternalGroups.isRegularMonoCategory_cocommHopf_of_field`: every monomorphism of
  `CocommHopf (ModuleCat k)` is regular.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace InternalGroups

variable (k : Type u) [Field k]

/-- **Every monomorphism of cocommutative Hopf algebras over a field is regular**, in the form of
group objects of `Comon_k^coc`. -/
theorem isRegularMonoCategory_grp_commComon_of_field :
    IsRegularMonoCategory (Grp (CategoryTheory.CommComon (ModuleCat.{u} k))) where
  regularMonoOfMono {X Y} m _ := by
    have hst := (biIdealMap_injective_iff_mono (h := Y.X)).1
      (biIdealMap_bijective_of_field Y.X).1 X m inferInstance
    exact isRegularMono_of_grpIsStabilizer_of_embedsInGrpObj
      (embedsInGrpObj_commComon_moduleCat (k := k)) hst

/-- **Every monomorphism of cocommutative Hopf monoids of `ModuleCat k` is regular**, for a field
`k`. -/
theorem isRegularMonoCategory_cocommHopf_of_field :
    IsRegularMonoCategory (UlmerBialgebras.GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  have := isRegularMonoCategory_grp_commComon_of_field k
  isRegularMonoCategory_of_equivalence UlmerBialgebras.GrpHopf.grpCommComonEquivCocommHopf

end InternalGroups
