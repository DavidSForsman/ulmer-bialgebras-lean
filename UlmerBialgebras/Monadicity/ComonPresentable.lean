module

public import Mathlib.CategoryTheory.Monoidal.Comon_
public import UlmerBialgebras.Kan.Sifted
public import Foundations.CategoryTheory.Limits.SiftedShapes
public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Basic.InsEqCat
public import UlmerBialgebras.Monadicity.AccCompleteIff
public import Foundations.CategoryTheory.Monoidal.ComonColimits

/-!
# Local presentability of comonoid objects

The intended argument combines

* the accessibility of `Comon V` when `V` is accessible with accessible tensor product, and
* `UlmerBialgebras.Comon.hasColimitsOfShape`
  (`Foundations/CategoryTheory/Monoidal/ComonColimits.lean`): the forgetful functor
  `Comon V ⥤ V` creates colimits,

with the criterion `UlmerBialgebras.isLocallyPresentable_of_hasColimits` (an accessible cocomplete
category is locally presentable) to show that the category of comonoid objects of a locally
presentable monoidal category with accessible tensor product is locally presentable.  This is
an instance of Theorem 5.11 (2) for the coalgebraic theory of comonoids.

This file only records the auxiliary fact that a locally presentable category is cocomplete
(`UlmerBialgebras.hasColimitsOfSize_of_isLocallyPresentable`); the accessibility of `Comon V` and
the local presentability statement are not formalized in it. Over a field, with `V = ModuleCat k`,
the statement is proved directly in the development repository's
`UlmerBialgebras/Examples/ComonModulePresentable.lean`
(`UlmerBialgebras.ComonModule.isLocallyFinitelyPresentable`).

## Main results

* `UlmerBialgebras.hasColimitsOfSize_of_isLocallyPresentable`: a locally presentable category is
  cocomplete.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 5.3 and Theorem 5.11
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC],
  Corollary 2.47
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe w u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory

/-- A locally presentable category is cocomplete. -/
theorem hasColimitsOfSize_of_isLocallyPresentable (C : Type u) [Category.{w} C]
    [IsLocallyPresentable.{w} C] : HasColimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  infer_instance

namespace Comon

variable (V : Type u) [Category.{w} V] [MonoidalCategory V]

section

variable [HasColimitsOfSize.{w, w} V]

end

end Comon

end UlmerBialgebras
