module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Presheaf

/-!
# A small model of the presentable objects

Let `C` be a `κ`-accessible category, with `κ : Cardinal.{w}` a regular cardinal. The full
subcategory of `κ`-presentable objects of `C` is essentially small. This file fixes a small model
`PresentableModel C κ` of it, with its dense, fully faithful inclusion into `C`, and the restricted
Yoneda functor `C ⥤ (PresentableModel C κ)ᵒᵖ ⥤ Type w`, which is fully faithful.

## Main results

* `CategoryTheory.IsCardinalAccessibleCategory.PresentableModel`: the small model;
* `CategoryTheory.IsCardinalAccessibleCategory.presentableModelι`: its inclusion into `C`, which is
  fully faithful and dense;
* `CategoryTheory.IsCardinalAccessibleCategory.presentableModelι_essImage`: every `κ`-presentable
  object is in its essential image;
* `CategoryTheory.IsCardinalAccessibleCategory.restrictedYoneda`: the restricted Yoneda functor,
  and `fullyFaithfulRestrictedYoneda`.

## References

* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Section 2.D
-/

@[expose] public section

universe w u

namespace CategoryTheory

open Limits Opposite Presheaf

namespace IsCardinalAccessibleCategory

variable (C : Type u) [Category.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalAccessibleCategory C κ]

/-- A small category which is equivalent to the full subcategory of `κ`-presentable objects
of a `κ`-accessible category `C`. -/
abbrev PresentableModel : Type w :=
  SmallModel.{w} (isCardinalPresentable C κ).FullSubcategory

/-- The fully faithful functor `PresentableModel C κ ⥤ C`, whose essential image consists
of the `κ`-presentable objects of `C`. -/
noncomputable def presentableModelι : PresentableModel C κ ⥤ C :=
  (equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).inverse ⋙
    (isCardinalPresentable C κ).ι

/-- The inclusion `presentableModelι C κ` is full. -/
instance : (presentableModelι C κ).Full := by
  dsimp [presentableModelι]; infer_instance

/-- The inclusion `presentableModelι C κ` is faithful. -/
instance : (presentableModelι C κ).Faithful := by
  dsimp [presentableModelι]; infer_instance

/-- The inclusion `presentableModelι C κ` of the `κ`-presentable objects is dense. -/
instance : (presentableModelι C κ).IsDense := by
  dsimp [presentableModelι]; infer_instance

/-- The image of every object of `PresentableModel C κ` in `C` is `κ`-presentable. -/
instance (a : PresentableModel C κ) : IsCardinalPresentable ((presentableModelι C κ).obj a) κ :=
  ((equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).inverse.obj a).property

/-- Every `κ`-presentable object of `C` is in the essential image of `presentableModelι C κ`. -/
lemma presentableModelι_essImage (X : C) (hX : IsCardinalPresentable X κ) :
    (presentableModelι C κ).essImage X :=
  ⟨(equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).functor.obj ⟨X, hX⟩,
    ⟨(isCardinalPresentable C κ).ι.mapIso
      ((equivSmallModel.{w} (isCardinalPresentable C κ).FullSubcategory).unitIso.app
        ⟨X, hX⟩).symm⟩⟩

/-- The restricted Yoneda functor `C ⥤ (PresentableModel C κ)ᵒᵖ ⥤ Type w`, which sends
`X : C` to the presheaf `a ↦ (presentableModelι C κ).obj a ⟶ X` (up to a `ULift`). -/
noncomputable def restrictedYoneda : C ⥤ (PresentableModel C κ)ᵒᵖ ⥤ Type w :=
  restrictedULiftYoneda.{w} (presentableModelι C κ)

/-- The restricted Yoneda functor is full. -/
instance : (restrictedYoneda C κ).Full := by
  dsimp [restrictedYoneda]; infer_instance

/-- The restricted Yoneda functor is faithful. -/
instance : (restrictedYoneda C κ).Faithful := by
  dsimp [restrictedYoneda]; infer_instance

/-- The restricted Yoneda functor is fully faithful. -/
noncomputable def fullyFaithfulRestrictedYoneda : (restrictedYoneda C κ).FullyFaithful :=
  .ofFullyFaithful _

end IsCardinalAccessibleCategory

end CategoryTheory
