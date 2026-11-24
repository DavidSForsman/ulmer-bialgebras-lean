module

public import Mathlib.CategoryTheory.Functor.KanExtension.RestrictedYoneda
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type
public import Foundations.CategoryTheory.Presentable.PresentableModel

/-!
# Locally presentable categories are complete

A locally presentable category is, by definition (in Mathlib), a cocomplete category with a
`κ`-filtered generator of `κ`-presentable objects.  In this file we prove the classical
theorem that such a category is also *complete*.

The proof is the standard one: the full subcategory of `κ`-presentable objects is
essentially small and **dense**, so the restricted Yoneda embedding

`restrictedYoneda C κ : C ⥤ (PresentableModel C κ)ᵒᵖ ⥤ Type w`

is fully faithful, and it has a left adjoint (the left Kan extension along the Yoneda
embedding, which exists because `C` is cocomplete).  Thus `C` is a **reflective**
subcategory of a presheaf category, and a reflective subcategory of a complete category is
complete.

## Main results

* `UlmerBialgebras.reflective_restrictedYoneda` — a cocomplete accessible category is a reflective
  subcategory of a presheaf category;
* `UlmerBialgebras.hasLimitsOfSize_of_isCardinalLocallyPresentable`,
  `UlmerBialgebras.hasLimitsOfSize_of_isLocallyPresentable` — locally presentable categories are
  complete.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 5.3 (the discussion preceding Theorem 5.10)
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Corollary 2.47
-/

@[expose] public section

universe w u

namespace UlmerBialgebras

open CategoryTheory Limits IsCardinalAccessibleCategory

section

variable (C : Type u) [Category.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalAccessibleCategory.{w} C κ]

variable [HasColimitsOfSize.{w, w} C]

/-- **A cocomplete accessible category is a reflective subcategory of a presheaf category.**
The reflector is the left Kan extension along the Yoneda embedding. -/
noncomputable instance reflective_restrictedYoneda : Reflective (restrictedYoneda C κ) where
  L := uliftYoneda.{w}.leftKanExtension (presentableModelι C κ)
  adj := Presheaf.restrictedULiftYonedaAdjunction.{w} (uliftYoneda.{w}.leftKanExtensionUnit _)

end

/-- **A locally presentable category is complete.** -/
theorem hasLimitsOfSize_of_isCardinalLocallyPresentable (C : Type u) [Category.{w} C]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable.{w} C κ] :
    HasLimitsOfSize.{w, w} C where
  has_limits_of_shape _ _ := hasLimitsOfShape_of_reflective (restrictedYoneda C κ)

/-- **A locally presentable category is complete.** -/
theorem hasLimitsOfSize_of_isLocallyPresentable (C : Type u) [Category.{w} C]
    [IsLocallyPresentable.{w} C] : HasLimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal C
  exact hasLimitsOfSize_of_isCardinalLocallyPresentable C κ

end UlmerBialgebras
