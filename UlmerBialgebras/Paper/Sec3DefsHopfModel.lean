module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import UlmerBialgebras.Examples.HopfEx
public import UlmerBialgebras.Kan.KanModel
public import UlmerBialgebras.Examples.MonModel

/-!
# The Hopf model of a braided monoidal category

The skew-monoidal 2-signature with an interchange law (`UlmerBialgebras.HopfEx.twoSig`) is
interpreted in a braided monoidal category `C` by

* the tensor product `□ ↦ ⊗` and the unit `I ↦ 𝟙_ C`;
* the associator `(x ⊗ y) ⊗ z → x ⊗ (y ⊗ z)`, the left unitor `𝟙_ C ⊗ x → x` and the inverse
  right unitor `x → x ⊗ 𝟙_ C`;
* the interchange law `tensorμ : (x ⊗ y) ⊗ (z ⊗ v) → (x ⊗ z) ⊗ (y ⊗ v)`, built from the
  braiding.

## Main definitions

* `UlmerBialgebras.Paper.HopfModel.hopfModel C`: this model in `CAT`.
* `UlmerBialgebras.Paper.HopfModel.ThyObj C`: the category `M^{T_Hopf}` of bialgebras of the theory
  of Hopf algebras (`UlmerBialgebras.HopfEx.theory`) in this model.
* `UlmerBialgebras.Paper.HopfModel.hopfForget C`: the forgetful functor from Mathlib's category
  `Hopf C` of Hopf monoids to `C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (2), Example 4.20
* [A. Joyal, R. Street, *Braided Tensor Categories*][joyalBraidedTensorCategories1993]
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.Paper.HopfModel

open CategoryTheory MonoidalCategory

section PreModel

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The interpretation of the category and functor symbols of the Hopf 2-signature: the
tensor product and the unit. -/
@[implicit_reducible]
def hopfPreModel : PreModel HopfEx.twoSig Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with
    | .tens => (MonEx.tensFunctor C).toCatHom
    | .unit => (MonEx.unitFunctor C).toCatHom

end PreModel

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The interpretation of a transformation symbol of the Hopf 2-signature: the associator,
the left unitor, the inverse right unitor and the interchange law `tensorμ`. -/
def hopfCell : ∀ a : HopfEx.TrSym,
    (hopfPreModel C).interp ((hopfPreModel C).Pctx a).π (HopfEx.twoSig.trsrc a) ⟶
      (hopfPreModel C).interp ((hopfPreModel C).Pctx a).π (HopfEx.twoSig.trtgt a)
  | .assoc =>
    NatTrans.toCatHom₂ {
      app := fun p => (α_ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2)).hom
      naturality := fun _ _ f =>
        associator_naturality (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2) }
  | .lunit =>
    NatTrans.toCatHom₂ {
      app := fun p => (λ_ (MonEx.ev C p 0)).hom
      naturality := fun _ _ f =>
        (congrArg (· ≫ _) (id_tensorHom (𝟙_ C) (MonEx.evMap C f 0))).trans
          (leftUnitor_naturality (MonEx.evMap C f 0)) }
  | .runit =>
    NatTrans.toCatHom₂ {
      app := fun p => (ρ_ (MonEx.ev C p 0)).inv
      naturality := fun _ _ f =>
        (rightUnitor_inv_naturality (MonEx.evMap C f 0)).trans
          (congrArg (_ ≫ ·) (tensorHom_id (MonEx.evMap C f 0) (𝟙_ C)).symm) }
  | .chi =>
    NatTrans.toCatHom₂ {
      app := fun p =>
        tensorμ (MonEx.ev C p 0) (MonEx.ev C p 1) (MonEx.ev C p 2) (MonEx.ev C p 3)
      naturality := fun _ _ f =>
        tensorμ_natural (MonEx.evMap C f 0) (MonEx.evMap C f 1) (MonEx.evMap C f 2)
          (MonEx.evMap C f 3) }

/-- **A braided monoidal category is a model of the Hopf 2-signature in `CAT`**
(Examples 3.20 (2) of [forsman2026syntactic]). -/
@[implicit_reducible]
def hopfModel : Model HopfEx.twoSig Cat.{v, u} where
  toPreModel := hopfPreModel C
  tr := hopfCell C

variable [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  [HasChosenProductsOfSize.{0} Cat.{v, u}]

/-- The object `M^{T_Hopf}` of `T_Hopf`-bialgebras in the Hopf model of `C`, as an object
of `CAT`. -/
abbrev thyCat : Cat.{v, u} := (hopfModel C).thyObj HopfEx.oneSig HopfEx.theory

/-- The category `M^{T_Hopf}` of `T_Hopf`-bialgebras in the Hopf model of `C`. -/
abbrev ThyObj : Type u := (thyCat C : Type u)

/-- The object `M₀ = ∏_{s} C` over the single sort of `σ_Hopf`. -/
abbrev baseCat : Cat.{v, u} := ((hopfModel C).P0 HopfEx.oneSig).pt

/-- The forgetful 1-cell `U : M^{T_Hopf} → M₀`. -/
abbrev forget : thyCat C ⟶ baseCat C := (hopfModel C).thyForget HopfEx.oneSig HopfEx.theory

/-- The forgetful functor `Hopf C ⥤ C`: a Hopf monoid goes to its underlying object, and a
morphism of Hopf monoids to its underlying morphism of `C`. -/
@[simps]
def hopfForget : Hopf C ⥤ C where
  obj A := A.X
  map f := f.hom.hom.hom

end UlmerBialgebras.Paper.HopfModel
