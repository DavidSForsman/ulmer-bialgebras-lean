module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Foundations.CategoryTheory.Monoidal.CocommProducts
public import Foundations.CategoryTheory.Monoidal.ComonColimits
public import Foundations.CategoryTheory.Monoidal.CommComonReflexive
public import Foundations.CategoryTheory.Grp.GrpTensorReflexive

/-!
# The product of cocommutative comonoids preserves reflexive coequalizers

The general transfer for cocommutative comonoids over a symmetric monoidal category is proved in
`Foundations/CategoryTheory/Monoidal/CommComonReflexive.lean`: the product with a fixed
cocommutative comonoid is conjugate, along the forgetful functor to the ambient category, to the
tensor product with its underlying object, so it preserves reflexive coequalizers as soon as the
tensor product of the ambient category does in each variable.

This file keeps the two specialisations that need the algebraic hypotheses of the ambient
category:

* the shape-wide preservation statements, which require colimits of the shape in the ambient
  category (the individual-diagram forms are in `Foundations`);
* the case `V = ModuleCat k` of modules over a commutative ring, where the tensor product is a
  left adjoint and hence preserves all colimits.

## Main results

* `UlmerBialgebras.CommComon.forget₂Comon_preservesColimitsOfShape`,
  `UlmerBialgebras.CommComon.forgetV_preservesColimitsOfShape` — the forgetful functors preserve
  colimits of a shape that the ambient category has;
* `UlmerBialgebras.CommComon.preservesReflexiveCoeq_tensorLeft_module` — over a commutative ring
  the tensor product of modules preserves reflexive coequalizers;
* `UlmerBialgebras.CommComon.preservesColimitsOfShape_walkingReflexivePair_tensorLeft_moduleCat` —
  for cocommutative coalgebras over a commutative ring, the product preserves colimits indexed by
  the walking reflexive pair.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe w w' v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped ComonObj

namespace CommComon

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

/-- The forgetful functor `CommComon V ⥤ Comon V` preserves colimits of shape `J` (it creates them,
and they exist). -/
instance forget₂Comon_preservesColimitsOfShape {J : Type w} [Category.{w'} J]
    [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (CategoryTheory.CommComon.forget₂Comon V) where
  preservesColimit := preservesColimit_of_createsColimit_and_hasColimit _ _

/-- The forgetful functor `CommComon V ⥤ V` preserves colimits of shape `J` whenever `V` has them.
-/
instance forgetV_preservesColimitsOfShape {J : Type w} [Category.{w'} J]
    [HasColimitsOfShape J V] : PreservesColimitsOfShape J (forgetV V) := by
  unfold forgetV
  exact comp_preservesColimitsOfShape _ _

/-! ## The case of modules over a commutative ring -/

section ModuleCat

variable (k : Type u) [CommRing k]

/-- The tensor product of modules is a left adjoint, hence preserves reflexive coequalizers. -/
instance preservesReflexiveCoeq_tensorLeft_module (Z : ModuleCat.{u} k) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z) := by
  have : (tensorLeft Z).IsLeftAdjoint := ⟨_, ⟨ihom.adjunction Z⟩⟩
  exact ⟨fun _ _ _ => inferInstance⟩

/-- **For cocommutative coalgebras over a commutative ring, the product preserves colimits
indexed by the walking reflexive pair.**  The tensor product of modules is a left adjoint, so it
preserves all colimits, and colimits of cocommutative coalgebras are computed on underlying
modules. -/
instance preservesColimitsOfShape_walkingReflexivePair_tensorLeft_moduleCat
    (A : CategoryTheory.CommComon (ModuleCat.{u} k)) :
    PreservesColimitsOfShape WalkingReflexivePair
      (tensorLeft A : CategoryTheory.CommComon (ModuleCat.{u} k) ⥤ _) :=
  inferInstance

end ModuleCat

end CommComon

end UlmerBialgebras
