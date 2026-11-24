module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Foundations.CategoryTheory.Monoidal.ComonTransport
public import Foundations.CategoryTheory.Monoidal.CommComonReflexive

/-!
# Cocommutative comonoids: colimits and closedness

Let `V` be a symmetric monoidal category.  The category `CategoryTheory.CommComon V` of
cocommutative comonoid objects of `V` is cartesian monoidal: its product is the tensor product of
the underlying objects (`Foundations/CategoryTheory/Monoidal/CocommProducts.lean`).  This file
proves that this cartesian structure is closed as soon as

* `V` has all colimits and tensoring with an object of `V` preserves them, and
* `CommComon V` is co-well-powered and has a small separating family.

Colimits of cocommutative comonoids are created by the forgetful functor `forgetV`, so
`CommComon V` has every colimit `V` has, and `forgetV` preserves and reflects them.  The product
with a fixed cocommutative comonoid is conjugate along `forgetV` to tensoring in `V`
(`tensorLeftForgetIso`), so it preserves colimits, and the special adjoint functor theorem
(`isLeftAdjoint_of_preservesColimits_of_isSeparating`) gives it a right adjoint.

## Main results

* `UlmerBialgebras.ComonObj.ofIso`, `UlmerBialgebras.CommComon.ofIso` — transport of a
  (cocommutative) comonoid structure along an isomorphism, and `CommComon.isoOfIso`, the
  isomorphism to the transported comonoid;
* `UlmerBialgebras.monoidalClosedOfPreservesColimitsOfSeparating` — a monoidal category with all
  colimits, co-well-powered, with a small separating family, in which tensoring on the left
  preserves colimits, is monoidal closed;
* `UlmerBialgebras.CommComon.hasColimitsOfSize` — `CommComon V` has the colimits `V` has;
* `UlmerBialgebras.CommComon.preservesColimitsOfSize_tensorLeft` — the product with a fixed
  cocommutative comonoid preserves them;
* `UlmerBialgebras.CommComon.monoidalClosed` — `CommComon V` is cartesian closed.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe w w' v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory
open scoped ComonObj

section General

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Closedness from the special adjoint functor theorem.**  A monoidal category with all
colimits, co-well-powered and with a small separating family, in which tensoring on the left with
any object preserves colimits, is monoidal closed. -/
@[instance_reducible]
noncomputable def monoidalClosedOfPreservesColimitsOfSeparating [HasColimits C]
    [WellPowered.{v} Cᵒᵖ] {P : ObjectProperty C} [ObjectProperty.Small.{v} P]
    (hP : P.IsSeparating) [∀ X : C, PreservesColimits (tensorLeft X)] : MonoidalClosed C where
  closed X :=
    haveI : (tensorLeft X).IsLeftAdjoint :=
      isLeftAdjoint_of_preservesColimits_of_isSeparating hP _
    { rightAdj := (tensorLeft X).rightAdjoint
      adj := Adjunction.ofIsLeftAdjoint _ }

end General

namespace CommComon

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]
variable {J : Type w} [Category.{w'} J]

/-- The forgetful functor `CommComon V ⥤ V` preserves the colimits that `V` has. -/
instance forgetV_preservesColimitsOfShape [HasColimitsOfShape J V] :
    PreservesColimitsOfShape J (forgetV V) where
  preservesColimit {F} := by
    have : CreatesColimit F (CategoryTheory.CommComon.forget₂Comon V) :=
      CommComon.createsColimit_forget₂Comon _
    unfold forgetV
    infer_instance

/-- `CommComon V` has the colimits that `V` has. -/
instance hasColimitsOfSize [HasColimitsOfSize.{w', w} V] :
    HasColimitsOfSize.{w', w} (CategoryTheory.CommComon V) where
  has_colimits_of_shape _ _ := inferInstance

/-- The forgetful functor `CommComon V ⥤ V` reflects the colimits that `V` has. -/
instance forgetV_reflectsColimitsOfShape [HasColimitsOfShape J V] :
    ReflectsColimitsOfShape J (forgetV V) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- The product with a fixed cocommutative comonoid preserves the colimits of a shape that
tensoring in `V` preserves. -/
instance preservesColimitsOfShape_tensorLeft [HasColimitsOfShape J V]
    [∀ Z : V, PreservesColimitsOfShape J (tensorLeft Z)] (A : CategoryTheory.CommComon V) :
    PreservesColimitsOfShape J (tensorLeft A) := by
  have : PreservesColimitsOfShape J (tensorLeft A ⋙ forgetV V) :=
    preservesColimitsOfShape_of_natIso (tensorLeftForgetIso A).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (tensorLeft A) (forgetV V)

/-- The product with a fixed cocommutative comonoid preserves the colimits that tensoring in `V`
preserves. -/
instance preservesColimitsOfSize_tensorLeft [HasColimitsOfSize.{w', w} V]
    [∀ Z : V, PreservesColimitsOfSize.{w', w} (tensorLeft Z)] (A : CategoryTheory.CommComon V) :
    PreservesColimitsOfSize.{w', w} (tensorLeft A) where
  preservesColimitsOfShape := inferInstance

/-- **`CommComon V` is cartesian closed** when `V` has all colimits, tensoring in `V` preserves
them, and `CommComon V` is co-well-powered with a small separating family. -/
@[instance_reducible]
noncomputable def monoidalClosed [HasColimits V] [∀ Z : V, PreservesColimits (tensorLeft Z)]
    [WellPowered.{v} (CategoryTheory.CommComon V)ᵒᵖ]
    {P : ObjectProperty (CategoryTheory.CommComon V)} [ObjectProperty.Small.{v} P]
    (hP : P.IsSeparating) : MonoidalClosed (CategoryTheory.CommComon V) :=
  monoidalClosedOfPreservesColimitsOfSeparating hP

/-- Transport of a cocommutative comonoid along an isomorphism of underlying objects. -/
def ofIso (A : CategoryTheory.CommComon V) {Y : V} (e : A.X ≅ Y) : CategoryTheory.CommComon V :=
  letI := ComonObj.ofIso e
  letI := ComonObj.isCommComonObj_ofIso e
  ⟨Y⟩

/-- A cocommutative comonoid is isomorphic to its transport along an isomorphism. -/
def isoOfIso (A : CategoryTheory.CommComon V) {Y : V} (e : A.X ≅ Y) : A ≅ ofIso A e :=
  letI := ComonObj.ofIso e
  { hom := @homMk V _ _ _ A (ofIso A e) e.hom (ComonObj.isComonHom_ofIso_hom e)
    inv := @homMk V _ _ _ (ofIso A e) A e.inv (ComonObj.isComonHom_ofIso_inv e)
    hom_inv_id := by ext; exact e.hom_inv_id
    inv_hom_id := by ext; exact e.inv_hom_id }

end CommComon

end UlmerBialgebras
