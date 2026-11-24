module

public import Foundations.CategoryTheory.Bicategory.TwoCategoryData
public import Foundations.CategoryTheory.Bicategory.StrictCoherence
public import Foundations.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Category.Cat

/-!
# `CAT` as a strict 2-category

The 2-category `CAT` of categories, functors and natural transformations is a strict
2-category (`Bicategory.Strict`): composition of functors is associative and
unital *on the nose*, and whiskering is the usual whiskering of natural transformations.

This is what allows the representable notions (such as `UlmerBialgebras.RepOFS`) to be compared with
the ordinary ones of Section 6 (`UlmerBialgebras.OFS`, `UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`); that comparison is carried out, for factorization systems, in
`RepCat.lean`.

We also record the terminal category `UlmerBialgebras.One` and the evaluation equivalence
`UlmerBialgebras.oneEquiv C : (One ⥤ C) ≌ C`, which is the "hom-category at the unit object" used to
recover a structure on `C` from a representable one.

## Main results

* `CategoryTheory.Cat.bicategory`: `CAT` as a strict 2-category (`Bicategory.Strict`).
* `UlmerBialgebras.One`: the terminal category.
* `UlmerBialgebras.oneEquiv`: the equivalence `(One ⥤ C) ≌ C` given by evaluation.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [G. M. Kelly, *Basic concepts of enriched category theory*][Kelly:Enriched]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory

/-! ## The terminal category -/

/-- The underlying type of the terminal category: one object. -/
inductive OneObj : Type u
  | /-- The unique object. -/ star

/-- The terminal category structure on `OneObj`: a single morphism between any two objects. -/
instance : Category.{v} OneObj.{u} where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- The terminal category, as an object of `CAT`. -/
def One : Cat.{v, u} := Cat.of OneObj.{u}

/-- The unique object of the terminal category. -/
abbrev One.star : One.{v, u} := OneObj.star

/-- Evaluation at the unique object of the terminal category. -/
@[simps]
def oneEval (C : Cat.{v, u}) : (One.{v, u} ⥤ C) ⥤ C where
  obj F := F.obj One.star
  map α := α.app One.star

/-- Evaluation at the unique object of the terminal category is faithful. -/
instance (C : Cat.{v, u}) : (oneEval C).Faithful where
  map_injective {F G} α β h := by
    ext x
    cases x
    exact h

/-- Evaluation at the unique object of the terminal category is full. -/
instance (C : Cat.{v, u}) : (oneEval C).Full where
  map_surjective {F G} f :=
    ⟨{ app := fun _ => f
       naturality := fun x y g => by
        cases x; cases y
        obtain rfl : g = 𝟙 One.star.{v, u} := rfl
        rw [show F.map (𝟙 One.star) = 𝟙 _ from F.map_id _,
          show G.map (𝟙 One.star) = 𝟙 _ from G.map_id _]
        exact (Category.id_comp f).trans (Category.comp_id f).symm }, rfl⟩

/-- Evaluation at the unique object of the terminal category is essentially surjective. -/
instance (C : Cat.{v, u}) : (oneEval C).EssSurj where
  mem_essImage X := ⟨(Functor.const _).obj X, ⟨Iso.refl _⟩⟩

/-- Evaluation at the unique object of the terminal category is an equivalence. -/
instance (C : Cat.{v, u}) : (oneEval C).IsEquivalence where

/-! ## Hom-categories of `CAT` -/

/-- The hom-category of `C` at the terminal category is `C` itself. -/
noncomputable def oneEquiv (C : Cat.{v, u}) : (One.{v, u} ⥤ C) ≌ C :=
  (oneEval C).asEquivalence

/-- Unwrapping CAT 1-cells identifies its hom-category with the functor category. -/
def catHomEquivalence (X Y : Cat.{v, u}) : (X ⟶ Y) ≌ (X ⥤ Y) where
  functor := { obj := fun F => F.toFunctor, map := fun α => α.toNatTrans }
  inverse := { obj := fun F => F.toCatHom, map := fun α => α.toCatHom₂ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end UlmerBialgebras
