module

public import Hopf.Cocommutative.ComonCoreflexiveEq
public import Hopf.Cocommutative.CommComonTensor
public import Hopf.Cocommutative.Reflexive
public import UlmerBialgebras.Proofs.Sec5.Sec5_7

/-!
# Structural input for Corollary 6.11 with minimal ambient limits

The ambient symmetric monoidal category needs only coreflexive equalizers and
reflexive coequalizers, preserved componentwise by tensor. Fox's products in
cocommutative comonoids, together with the created coreflexive equalizers,
provide all finite limits. No ambient finite-limit or arbitrary-coequalizer
assumption is imposed.

## Main results

* `UlmerBialgebras.Paper.Cor611.cocomm_hasFiniteLimits`: `CommComon V` has finite limits.
* `UlmerBialgebras.Paper.Cor611.cocomm_product_preservesReflexiveCoeq`: `tensorLeft X` on
  `CommComon V` preserves reflexive coequalizers.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.17 (and its dual) and Corollary 6.11
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.Paper.Cor611

open CategoryTheory Limits MonoidalCategory

variable (V : Type u) [Category.{v} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Fox's products and created coreflexive equalizers give finite limits. -/
theorem cocomm_hasFiniteLimits [HasCoreflexiveEqualizers V]
    [∀ Z : V, PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ Z : V, PreservesCoreflexiveEq (tensorRight Z)] :
    HasFiniteLimits (CategoryTheory.CommComon V) :=
  hasFiniteLimits_of_coreflexive

/-- Fox's product preserves reflexive coequalizers when the ambient tensor does. -/
theorem cocomm_product_preservesReflexiveCoeq [HasReflexiveCoequalizers V]
    [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    (X : CategoryTheory.CommComon V) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft X) := by
  exact CategoryTheory.preservesReflexiveCoeq_of_natIso _
    (UlmerBialgebras.CommComon.forgetV V) (tensorLeft X.X)
    (UlmerBialgebras.CommComon.tensorLeftForgetIso X)

/-- The product-preservation input in the general internal-group development. -/
theorem cocomm_product_preservesWalkingReflexivePair [HasReflexiveCoequalizers V]
    [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    (X : CategoryTheory.CommComon V) :
    PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X) := by
  have := cocomm_product_preservesReflexiveCoeq V X
  exact CategoryTheory.preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq
      _

/-- Preservation in the other product variable follows by symmetry. -/
theorem cocomm_productRight_preservesWalkingReflexivePair [HasReflexiveCoequalizers V]
    [∀ Z : V, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    (X : CategoryTheory.CommComon V) :
    PreservesColimitsOfShape WalkingReflexivePair (tensorRight X) := by
  have : ∀ Y : CategoryTheory.CommComon V,
      PreservesColimitsOfShape WalkingReflexivePair (tensorLeft Y) :=
    fun Y => cocomm_product_preservesWalkingReflexivePair V Y
  let : BraidedCategory (CategoryTheory.CommComon V) :=
    BraidedCategory.ofCartesianMonoidalCategory
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

end UlmerBialgebras.Paper.Cor611
