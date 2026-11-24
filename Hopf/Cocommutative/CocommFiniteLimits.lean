module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.TorsionFree
public import Hopf.Cocommutative.ComonCoreflexiveEq
public import Hopf.Cocommutative.Reflexive
public import Foundations.CategoryTheory.Monoidal.CocommProducts

/-!
# Cocommutative coalgebras over a field have all finite limits

Let `k` be a field.  Every `k`-vector space is flat, so tensoring with a fixed vector space is an
exact functor; in particular `Z ⊗ -` and `- ⊗ Z` preserve equalizers of coreflexive pairs.  By
`Hopf/Cocommutative/ComonCoreflexiveEq.lean` the forgetful functor
`CommComon (ModuleCat k) ⥤ ModuleCat k` therefore *creates* coreflexive equalizers: the
equalizer of a coreflexive pair of morphisms of cocommutative coalgebras is the equalizer of the
underlying `k`-linear maps.

Together with the fact that the tensor product of cocommutative coalgebras is their categorical
product (`Foundations/CategoryTheory/Monoidal/CocommProducts.lean`), and with
`UlmerBialgebras.hasFiniteLimits_of_coreflexive`, this gives *all* finite limits of cocommutative
coalgebras: a general equalizer of `f, g : A ⟶ B` is the coreflexive equalizer of
`⟨𝟙, f⟩, ⟨𝟙, g⟩ : A ⟶ A ⨯ B`.

This discharges the finite-limit hypothesis of the categorical Galois connection for internal
groups (`InternalGroups/SubgroupCorrespondence.lean`) for cocommutative coalgebras over a field.

## Main results

* `UlmerBialgebras.CocommComon.hasCoreflexiveEqualizers` — `Comon_k^coc` has coreflexive equalizers,
  computed in `Vect_k`;
* `UlmerBialgebras.CocommComon.hasFiniteLimits` — `Comon_k^coc` has all finite limits;
* `UlmerBialgebras.CocommComon.hasEqualizers`.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (proof)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace UlmerBialgebras

namespace CocommComon

variable (k : Type u) [Field k]

/-- Over a field every module is flat, so `Z ⊗ -` preserves finite limits, in particular the
equalizers of coreflexive pairs. -/
instance preservesCoreflexiveEq_tensorLeft (Z : ModuleCat.{u} k) :
    PreservesCoreflexiveEq (tensorLeft Z) :=
  preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- Over a field every module is flat, so `- ⊗ Z` preserves the equalizers of coreflexive
pairs. -/
instance preservesCoreflexiveEq_tensorRight (Z : ModuleCat.{u} k) :
    PreservesCoreflexiveEq (tensorRight Z) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- **The cocommutative coalgebras over a field have coreflexive equalizers**, computed in
`Vect_k`. -/
instance hasCoreflexiveEqualizers :
    HasCoreflexiveEqualizers (CommComon (ModuleCat.{u} k)) :=
  ComonCoreflexiveEq.hasCoreflexiveEqualizers_commComon (ModuleCat.{u} k)

/-- **The cocommutative coalgebras over a field have all finite limits.** -/
instance hasFiniteLimits : HasFiniteLimits (CommComon (ModuleCat.{u} k)) :=
  hasFiniteLimits_of_coreflexive

/-- The cocommutative coalgebras over a field have all equalizers. -/
instance hasEqualizers : HasEqualizers (CommComon (ModuleCat.{u} k)) :=
  hasEqualizers_of_coreflexive

end CocommComon

end UlmerBialgebras
