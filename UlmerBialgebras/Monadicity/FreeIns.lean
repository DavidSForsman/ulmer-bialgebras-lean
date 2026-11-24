module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Transposing an inserter structure cell

An adjunction transposes the structure morphism of an inserter object into a morphism from the
left adjoint's value.

## Main results

* `UlmerBialgebras.Ins.cellTranspose`: for `L ⊣ G`, the transpose `L (F z) ⟶ z` of the structure
  morphism of an object of `Ins(F, G)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section Chain

variable (F : C ⥤ D) (L : D ⥤ C) [HasBinaryCoproducts C]

end Chain

namespace Ins

/-- The transpose `L (F z) ⟶ z` of the structure morphism of an object of the inserter. -/
def cellTranspose {F G : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ G) (Z : Ins F G) :
    L.obj (F.obj Z.pt) ⟶ Z.pt :=
  (adj.homEquiv _ _).symm Z.cell

section Free

variable {G : C ⥤ D} (F : C ⥤ D) (L : D ⥤ C) [HasBinaryCoproducts C]
  [HasColimitsOfShape ℕ C] [PreservesColimitsOfShape ℕ F]

variable [PreservesColimitsOfShape ℕ L]

variable (adj : L ⊣ G)

end Free

end Ins

end UlmerBialgebras
