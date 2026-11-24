module

public import InternalGroups.GrpObjSubgroupCorrespondenceStabilizer
public import InternalGroups.GrpObjSubgroupCorrespondenceCocomm
public import InternalGroups.GrpObjSubgroupCorrespondenceBiIdealEpi

/-!
# Newman's correspondence implies exactness: cocommutative comonoids

The specialization of `InternalGroups.isBarrExact_grp_of_subgroupCorrespondence` to
`C = CommComon A`, the cocommutative comonoids of a symmetric monoidal category `A`.

These results are due to D. Forsman. They were announced by the author and will appear in a
forthcoming preprint.

## Hypotheses

The generic theorem needs `C` cartesian monoidal, finitely complete, with reflexive coequalizers
preserved by the product in each variable.  For `C = CommComon A` these come from `A` as follows:

* **cartesian monoidal**: from `A` symmetric monoidal, by Fox's theorem
  (`UlmerBialgebras.CommComon.instCartesianMonoidalCategory`);
* **finite limits**: from `HasCoreflexiveEqualizers A` and
  `TensorPreservesCoreflexiveEqualizers A` (`InternalGroups.hasFiniteLimits_commComon`);
* **reflexive coequalizers**: from `HasReflexiveCoequalizers A`
  (`UlmerBialgebras.CommComon.hasReflexiveCoequalizers`);
* **the product preserves them**: in addition, `tensorLeft Z` preserves reflexive coequalizers
  in `A` (`UlmerBialgebras.CommComon.preservesReflexiveCoeq_tensorLeft`, `…_tensorRight`).

No abelian, additive or pointedness assumption on `A` enters.  In the abelian setting, with
the tensor product exact in each variable, all four hold, and Newman's correspondence is the
bijectivity of the bi-ideal correspondence for every cocommutative Hopf monoid
(`InternalGroups.forall_biIdealMap_bijective_iff`).

## Main results

* `InternalGroups.isBarrExact_grp_commComon`: if Newman's correspondence holds in
  `CommComon A`, then `Grp (CommComon A)` is Barr exact;
* `InternalGroups.isBarrExact_grp_commComon_of_biIdeal`: for abelian `A` with exact tensor
  product, if the bi-ideal correspondence is bijective for every internal group of
  `CommComon A`, then `Grp (CommComon A)` is Barr exact;
* `InternalGroups.subgroupCorrespondence_commComon_iff_monos_are_stabilizers`,
  `InternalGroups.forall_biIdealMap_bijective_iff_monos_are_stabilizers`: Newman's correspondence
  says that monomorphisms are stabilizers and epi quotients are regular.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace InternalGroups


section General

variable {A : Type u} [Category.{v} A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [HasCoreflexiveEqualizers A] [UlmerBialgebras.TensorPreservesCoreflexiveEqualizers A]
  [HasReflexiveCoequalizers A] [∀ Z : A, PreservesReflexiveCoeq (tensorLeft Z)]

/-- **Newman's correspondence implies exactness, for cocommutative comonoids.**  If
Newman's correspondence holds for every internal group of `CommComon A`, then
`Grp (CommComon A)` is Barr exact.  The hypotheses on `A` are those of the table above. -/
theorem isBarrExact_grp_commComon (h : SubgroupCorrespondence (CommComon A)) :
    IsBarrExact (Grp (CommComon A)) :=
  have : HasFiniteLimits (CommComon A) := hasFiniteLimits_commComon
  isBarrExact_grp_of_subgroupCorrespondence h

/-- **Newman's correspondence in `CommComon A`, translated.**  It holds iff every monomorphism of
`Grp (CommComon A)` is a stabilizer and every epi quotient of an internal group is a regular
epimorphism of modules.  The hypotheses on `A` are those of the table above. -/
theorem subgroupCorrespondence_commComon_iff_monos_are_stabilizers :
    SubgroupCorrespondence (CommComon A) ↔
      (∀ {G H : Grp (CommComon A)} (m : G ⟶ H), Mono m → GrpIsStabilizer m) ∧
        EveryEpiQuotientRegular (CommComon A) :=
  have : HasFiniteLimits (CommComon A) := hasFiniteLimits_commComon
  subgroupCorrespondence_iff_monos_are_stabilizers

end General

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory.{v} A] [SymmetricCategory A]
  [∀ X : A, PreservesFiniteLimits (tensorLeft X)] [∀ X : A, PreservesFiniteColimits (tensorLeft X)]

attribute [local instance] preservesFiniteLimits_tensorRight_of_left
  tensorPreservesCoreflexiveEqualizers_of_preservesFiniteLimits
  preservesReflexiveCoeq_tensorLeft_of_preservesFiniteColimits

/-- **The bi-ideal form, for abelian `A` with exact tensor product.**  If Newman's bi-ideal
correspondence is bijective for every internal group of `CommComon A`, then `Grp (CommComon A)`
is Barr exact. -/
theorem isBarrExact_grp_commComon_of_biIdeal
    (h : ∀ (H : CommComon A) [GrpObj H], Function.Bijective (biIdealMap H)) :
    IsBarrExact (Grp (CommComon A)) :=
  isBarrExact_grp_commComon (forall_biIdealMap_bijective_iff.1 h)

/-- **Newman's bi-ideal correspondence, translated, for abelian `A` with exact tensor product.**
The bi-ideal correspondence is bijective for every internal group of `CommComon A` iff every
monomorphism of `Grp (CommComon A)` is a stabilizer and every epi quotient of an internal group is
a regular epimorphism of modules. -/
theorem forall_biIdealMap_bijective_iff_monos_are_stabilizers :
    (∀ (H : CommComon A) [GrpObj H], Function.Bijective (biIdealMap H)) ↔
      (∀ {G H : Grp (CommComon A)} (m : G ⟶ H), Mono m → GrpIsStabilizer m) ∧
        EveryEpiQuotientRegular (CommComon A) :=
  forall_biIdealMap_bijective_iff.trans subgroupCorrespondence_commComon_iff_monos_are_stabilizers

end Abelian


end InternalGroups
