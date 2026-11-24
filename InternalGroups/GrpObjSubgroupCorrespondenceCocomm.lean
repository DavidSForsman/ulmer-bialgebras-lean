module

public import InternalGroups.GrpObjSubgroupCorrespondenceCharacterization
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import Foundations.CategoryTheory.Monoidal.ComonColimits
public import Foundations.CategoryTheory.Monoidal.CommComonEqualizers
public import Foundations.CategoryTheory.Limits.CoreflexiveLimits

/-!
# Newman's correspondence for cocommutative comonoids

This file specializes the characterization `InternalGroups.subgroupCorrespondence_iff` of
`InternalGroups/GrpObjSubgroupCorrespondenceCharacterization.lean` to the author's setting
`C = CommComon A` of cocommutative comonoid objects of a symmetric monoidal category `A`.

## Structural input

The general theory needs `C` to be cartesian monoidal, finitely complete, and to have reflexive
coequalizers of modules.  For `C = CommComon A`:

* **cartesian monoidal**: available for any symmetric monoidal `A`, with the tensor product of
  `A` as categorical product (Fox's theorem), see
  `UlmerBialgebras.CommComon.instCartesianMonoidalCategory`;
* **finite products**: `HasFiniteProducts (CommComon A)`, same file;
* **reflexive coequalizers**: `CommComon A` has all the colimits that `A` has
  (`UlmerBialgebras.CommComon.hasColimitsOfShape`), computed on underlying objects;
* **coreflexive equalizers**: constructed in
  `Foundations/CategoryTheory/Monoidal/CocommEqualizers.lean` from the author's hypothesis that
  tensoring in either variable preserves them.  For a coreflexive pair `f g : X ⟶ Y` in
  `CommComon A` with a common retraction `r : Y ⟶ X` (`f ≫ r = g ≫ r = 𝟙_X`), the equalizer
  `e : E ⟶ X` in `A` carries a comonoid structure: the candidate `d = e ≫ Δ_X` equalizes
  `f ⊗ 𝟙` and `g ⊗ 𝟙`, hence factors through `E ⊗ X`; the mirror identity and cancellation by
  the preserved monomorphism then factor it through `E ⊗ E`, giving the comultiplication, and
  the comonoid axioms are inherited by cancellation.  The equalizer map is a comonoid morphism,
  so the fork is a limit fork in `CommComon A`, giving
  `UlmerBialgebras.commComonHasCoreflexiveEqualizers` (an `instance`);
* **finite limits and pullbacks**: all equalizers follow from binary products by replacing
  `f, g` with `⟨id, f⟩, ⟨id, g⟩ : X ⟶ X × Y` (common retraction `fst`), and pullbacks from
  equalizers and products (`Foundations/CategoryTheory/Limits/CoreflexiveLimits.lean`); finite
  limits then follow from Mathlib's `hasFiniteLimits_of_hasTerminal_and_pullbacks`.

## Main result

* `InternalGroups.subgroupCorrespondence_commComon`: Newman's correspondence for `CommComon A` is
  equivalent to coset injectivity and regularity of every epi quotient, under the author's
  hypotheses `[HasCoreflexiveEqualizers A]` and
  `[TensorPreservesCoreflexiveEqualizers A]`.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj
open UlmerBialgebras

namespace InternalGroups


variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [SymmetricCategory A]

/-- **Finite limits of `CommComon A` from Fox's theorem and the author's coreflexive
equalizers.**  The products come from Fox's theorem (the tensor product of `A`); the coreflexive
equalizers are constructed in `Foundations.CategoryTheory.Monoidal.CocommEqualizers` from the
author's hypothesis that tensoring preserves them. -/
theorem hasFiniteLimits_commComon [HasCoreflexiveEqualizers A]
    [TensorPreservesCoreflexiveEqualizers A] : HasFiniteLimits (CommComon A) :=
  hasFiniteLimits_of_hasTerminal_and_coreflexiveEqualizers

/-- **Finite limits of `CommComon A` imply the pullback structure needed by Newman's
correspondence.** -/
instance (priority := 100) hasPullbacks_commComon [HasCoreflexiveEqualizers A]
    [TensorPreservesCoreflexiveEqualizers A] : HasPullbacks (CommComon A) :=
  hasPullbacks_of_hasCoreflexiveEqualizers

variable [HasCoreflexiveEqualizers A] [TensorPreservesCoreflexiveEqualizers A]

/-- **Newman's correspondence for cocommutative comonoids.**  The characterization of
`subgroupCorrespondence_iff`, specialized to `C = CommComon A` under the author's coreflexive
equalizers: Fox's theorem supplies the products, the generic bridge turns them into pullbacks,
and the characterization applies. -/
theorem subgroupCorrespondence_commComon :
    SubgroupCorrespondence (CommComon A) ↔
      CosetInjective (CommComon A) ∧ EveryEpiQuotientRegular (CommComon A) :=
  subgroupCorrespondence_iff


end InternalGroups
