module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Limits of internal groups

Let `C` be a cartesian monoidal category.  For any shape `J` such that `C` has limits of
shape `J`, the category `Grp C` of group objects of `C` has limits of shape `J`, and the
forgetful functor `Grp.forget C : Grp C ⥤ C` preserves them.

Mathlib (`Mathlib/CategoryTheory/Monoidal/Cartesian/GrpLimits.lean`) proves that `Grp.forget C`
creates limits. This file retains compatibility names without registering duplicate instances.
The direct
reflection instance for `Grp.forget` packages Mathlib’s composition instance; typeclass search
does not synthesize it from the composed functor automatically. The finite-limit adapter
packages Mathlib’s shape-wise instances into
`HasFiniteLimits`, which Mathlib does not register for group objects in the pinned version.

## Main results

* `CategoryTheory.Grp.hasLimitsOfShape`: `Grp C` has limits of shape `J` whenever `C` does;
* `CategoryTheory.Grp.forget_reflectsIsomorphisms`: the forgetful functor `Grp C ⥤ C` reflects
  isomorphisms;

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.11
-/

@[expose] public section

universe v u v₂ u₂

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {J : Type u₂} [Category.{v₂} J] [HasLimitsOfShape J C]

namespace Grp

/-- `Grp C` has limits of shape `J` whenever `C` does. -/
abbrev hasLimitsOfShape : HasLimitsOfShape J (Grp C) := inferInstance

/-- The forgetful functor from group objects to monoid objects reflects isomorphisms. -/
lemma forget₂Mon_reflectsIsomorphisms : (Grp.forget₂Mon C).ReflectsIsomorphisms :=
  inferInstance

/-- The forgetful functor `Grp C ⥤ C` reflects isomorphisms. -/
instance forget_reflectsIsomorphisms : (Grp.forget C).ReflectsIsomorphisms := by
  have : (Grp.forget₂Mon C ⋙ Mon.forget C).ReflectsIsomorphisms := inferInstance
  exact this

end Grp

end CategoryTheory
