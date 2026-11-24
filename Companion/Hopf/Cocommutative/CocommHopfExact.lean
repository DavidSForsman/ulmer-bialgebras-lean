module

public import Companion.Hopf.Cocommutative.GrpCommComonHopf
public import InternalGroups.GrpObjSubgroupCorrespondenceExactCocomm
public import Foundations.CategoryTheory.Exact.SemiAbelianEquiv

/-!
# Newman's correspondence implies exactness of cocommutative Hopf monoids

For a symmetric monoidal category `A`,
group objects of cocommutative comonoids are cocommutative Hopf monoids
(`UlmerBialgebras.GrpHopf.grpCommComonEquivCocommHopf`, an equivalence of categories, not an
equality), so the Barr exactness of `Grp (CommComon A)`
(`InternalGroups.isBarrExact_grp_commComon`) transports to the category
`UlmerBialgebras.GrpHopf.CocommHopf A` of cocommutative Hopf monoids of `A`
(`CategoryTheory.isBarrExact_of_equivalence`).

These results are due to D. Forsman. They were announced by the author and will appear in a
forthcoming preprint.

## Main results

* `InternalGroups.isBarrExact_cocommHopf`: if Newman's correspondence holds in `CommComon A`, then
  the category of cocommutative Hopf monoids of `A` is Barr exact;
* `InternalGroups.isBarrExact_cocommHopf_of_biIdeal`: for abelian `A` with exact tensor product,
  if the bi-ideal correspondence is bijective for every internal group of `CommComon A`, then the
  category of cocommutative Hopf monoids of `A` is Barr exact.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits UlmerBialgebras.GrpHopf

namespace InternalGroups

section General

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [HasCoreflexiveEqualizers A] [UlmerBialgebras.TensorPreservesCoreflexiveEqualizers A]
  [HasReflexiveCoequalizers A] [∀ Z : A, PreservesReflexiveCoeq (tensorLeft Z)]

/-- **Newman's correspondence implies exactness of cocommutative Hopf monoids.**  If
Newman's correspondence holds for every internal group of `CommComon A`, then the category of
cocommutative Hopf monoids of `A` is Barr exact. -/
theorem isBarrExact_cocommHopf (h : SubgroupCorrespondence (CommComon A)) :
    IsBarrExact (CocommHopf A) :=
  have : IsBarrExact (Grp (CommComon A)) := isBarrExact_grp_commComon h
  isBarrExact_of_equivalence grpCommComonEquivCocommHopf.symm

end General

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ X : A, PreservesFiniteLimits (tensorLeft X)] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

attribute [local instance] preservesFiniteLimits_tensorRight_of_left
  tensorPreservesCoreflexiveEqualizers_of_preservesFiniteLimits
  preservesReflexiveCoeq_tensorLeft_of_preservesFiniteColimits

/-- **The bi-ideal form, for abelian `A` with exact tensor product.**  If Newman's bi-ideal
correspondence is bijective for every internal group of `CommComon A`, then the category of
cocommutative Hopf monoids of `A` is Barr exact. -/
theorem isBarrExact_cocommHopf_of_biIdeal
    (h : ∀ (H : CommComon A) [GrpObj H], Function.Bijective (biIdealMap H)) :
    IsBarrExact (CocommHopf A) :=
  isBarrExact_cocommHopf (forall_biIdealMap_bijective_iff.1 h)

end Abelian

end InternalGroups
