module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Naturality of the diagonal

In a cartesian monoidal category the diagonal `lift (𝟙 X) (𝟙 X) : X ⟶ X ⊗ X` is natural in `X`.

## Main results

* `CategoryTheory.CartesianMonoidalCategory.lift_id_id_naturality`: the naturality square of the
  diagonal.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], III.4 (products)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- The diagonal `lift (𝟙 X) (𝟙 X) : X ⟶ X ⊗ X` is natural in `X`. -/
lemma lift_id_id_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ lift (𝟙 Y) (𝟙 Y) = lift (𝟙 X) (𝟙 X) ≫ (f ⊗ₘ f) := by
  rw [comp_lift, lift_map, Category.comp_id, Category.id_comp]

end CategoryTheory.CartesianMonoidalCategory
