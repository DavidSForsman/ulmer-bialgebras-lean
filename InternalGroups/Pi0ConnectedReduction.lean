module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Tactic.Group
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import InternalGroups.GrpObjSubgroupCorrespondence

/-!
# Unit maps and connected components

Compatibility of connected-component maps with unit homomorphisms.

Its content is classical, following Newman [Newman1975] and Sweedler [Sweedler], Chapter 8, and is
not a result of the author; it is part of the library because the exactness criterion uses it.

## Main results

* `InternalGroups.Pi0.comp_one_hom`: for `e : V ⟶ W`, `e ≫ (1 : W ⟶ G) = 1`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory Opposite
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups

namespace Pi0

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

namespace Pi0Setting

variable {C}

end Pi0Setting

/-! ## Injectivity on points -/

section Points

open InternalGroups QuotMod

variable {C} {G : C} [GrpObj G]

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

end Points

/-! ## Connected objects -/

section Connected

variable {C}

end Connected

/-! ## The reduction to connected objects -/

section Reduction

open InternalGroups QuotMod

variable {C} {G : C} [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

end Reduction

/-! ## The identity component -/

section IdentityComponent

open InternalGroups QuotMod

variable {C}

/-- Precomposing the unit morphism `1 : W ⟶ G` with any `e : V ⟶ W` gives `1 : V ⟶ G`. -/
lemma comp_one_hom {W G : C} [MonObj G] {V : C} (e : V ⟶ W) : e ≫ (1 : W ⟶ G) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc]
  congr 1
  exact toUnit_unique _ _

variable {G : C} [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

end IdentityComponent

/-! ## A sufficient condition: group objects without infinitesimal elements -/

section Discrete

open InternalGroups QuotMod

variable {C} {G : C} [GrpObj G]

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

end Discrete

/-! ## The classical setting `C = Type u` -/

namespace Types

open InternalGroups

end Types

end Pi0

end InternalGroups
