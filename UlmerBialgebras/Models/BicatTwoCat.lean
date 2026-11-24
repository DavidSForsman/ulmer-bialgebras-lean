module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import UlmerBialgebras.Basic.PIE

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# A strict 2-category as a bicategory: adjunctions and mates

Strict 2-categories given as field-wise data are bicategories in Mathlib's sense, with
associators and unitors given by `eqToHom`.  We record this on a type synonym
`UlmerBialgebras.AsBicat Obj`, so that no `Category`/`Bicategory` instance is imposed on `Obj`
itself, and use it to import Mathlib's calculus of adjunctions and mates in a bicategory
(`Mathlib.CategoryTheory.Bicategory.Adjunction.Mate`) into the language of field-wise strict
2-categories (`UlmerBialgebras.TwoAdj`).

## Main results

* `UlmerBialgebras.AsBicat`: a type synonym for a strict 2-category.
* `UlmerBialgebras.AsBicat`: the bicategory structure on `UlmerBialgebras.AsBicat Obj`.
* `UlmerBialgebras.TwoAdj`: adjunctions `f ⊣ g` between 1-cells of a strict 2-category.
* `UlmerBialgebras.TwoAdj.mk'`: an adjunction built from a unit, a counit and the two triangle
  identities.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2
* [G. M. Kelly, R. Street,
  *Review of the elements of 2-categories*][kellyReviewElements2categories1974]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory

/-- A type synonym for a strict 2-category, carrying the induced `Bicategory` structure. -/
abbrev AsBicat (Obj : Type u) [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] : Type u := Obj

namespace AsBicat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- The underlying object of the strict 2-category. -/
def down (X : AsBicat.{u, v, w} Obj) : Obj := X

section Simp

variable {X Y Z W : AsBicat.{u, v, w} Obj}

/-- The associator of `AsBicat Obj` is `eqToHom` of the strict associativity law. -/
@[simp] lemma associator_hom (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (Bicategory.associator f g h).hom = eqToHom (Category.assoc f g h) := by
  simp [Bicategory.Strict.associator_eqToIso]

/-- The inverse associator of `AsBicat Obj` is `eqToHom` of the reversed associativity law. -/
@[simp] lemma associator_inv (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (Bicategory.associator f g h).inv = eqToHom (Category.assoc f g h).symm := by
  simp [Bicategory.Strict.associator_eqToIso]

/-- The left unitor of `AsBicat Obj` is `eqToHom` of the strict left unit law. -/
@[simp] lemma leftUnitor_hom (f : X ⟶ Y) :
    (Bicategory.leftUnitor f).hom = eqToHom (Category.id_comp f) := by
  simp [Bicategory.Strict.leftUnitor_eqToIso]

/-- The inverse left unitor of `AsBicat Obj` is `eqToHom` of the reversed left unit law. -/
@[simp] lemma leftUnitor_inv (f : X ⟶ Y) :
    (Bicategory.leftUnitor f).inv = eqToHom (Category.id_comp f).symm := by
  simp [Bicategory.Strict.leftUnitor_eqToIso]

/-- The right unitor of `AsBicat Obj` is `eqToHom` of the strict right unit law. -/
@[simp] lemma rightUnitor_hom (f : X ⟶ Y) :
    (Bicategory.rightUnitor f).hom = eqToHom (Category.comp_id f) := by
  simp [Bicategory.Strict.rightUnitor_eqToIso]

/-- The inverse right unitor of `AsBicat Obj` is `eqToHom` of the reversed right unit law. -/
@[simp] lemma rightUnitor_inv (f : X ⟶ Y) :
    (Bicategory.rightUnitor f).inv = eqToHom (Category.comp_id f).symm := by
  simp [Bicategory.Strict.rightUnitor_eqToIso]

end Simp

end AsBicat

/-! ## Adjunctions -/

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- An adjunction `f ⊣ g` between 1-cells of a strict 2-category. -/
abbrev TwoAdj {a b : Obj} (f : a ⟶ b) (g : b ⟶ a) : Type w :=
  Bicategory.Adjunction (B := AsBicat.{u, v, w} Obj) f g

namespace TwoAdj

variable {a b : Obj} {f : a ⟶ b} {g : b ⟶ a}

/-- The unit of an adjunction, in the language of strict 2-categories. -/
abbrev unit' (A : TwoAdj f g) : 𝟙 a ⟶ f ≫ g := A.unit

/-- The counit of an adjunction, in the language of strict 2-categories. -/
abbrev counit' (A : TwoAdj f g) : g ≫ f ⟶ 𝟙 b := A.counit

/-- The left triangle identity of a 2-adjunction `f ⊣ g`, in the strict form
`(η ▷ f) ≫ (f ◁ ε) = 𝟙` up to `eqToHom`. -/
theorem left_triangle' (A : TwoAdj f g) :
    (A.unit' ▷ f) ≫ eqToHom (Category.assoc f g f) ≫ (f ◁ A.counit')
      = eqToHom (Category.id_comp f) ≫ eqToHom (Category.comp_id f).symm := by
  have := A.left_triangle
  simpa [Bicategory.leftZigzag, bicategoricalComp] using this

/-- The right triangle identity of a 2-adjunction `f ⊣ g`, in the strict form
`(g ◁ η) ≫ (ε ▷ g) = 𝟙` up to `eqToHom`. -/
theorem right_triangle' (A : TwoAdj f g) :
    (g ◁ A.unit') ≫ eqToHom (Category.assoc g f g).symm ≫ (A.counit' ▷ g)
      = eqToHom (Category.comp_id g) ≫ eqToHom (Category.id_comp g).symm := by
  have := A.right_triangle
  simpa [Bicategory.rightZigzag, bicategoricalComp] using this

/-- Construct an adjunction in a strict 2-category from the two triangle identities. -/
def mk' (unit : 𝟙 a ⟶ f ≫ g) (counit : g ≫ f ⟶ 𝟙 b)
    (hl : (unit ▷ f) ≫ eqToHom (Category.assoc f g f) ≫ (f ◁ counit)
      = eqToHom (Category.id_comp f) ≫ eqToHom (Category.comp_id f).symm)
    (hr : (g ◁ unit) ≫ eqToHom (Category.assoc g f g).symm ≫ (counit ▷ g)
      = eqToHom (Category.comp_id g) ≫ eqToHom (Category.id_comp g).symm) : TwoAdj f g where
  unit := unit
  counit := counit
  left_triangle := by simpa [Bicategory.leftZigzag, bicategoricalComp] using hl
  right_triangle := by simpa [Bicategory.rightZigzag, bicategoricalComp] using hr

/-! ## Mates -/

section Mate

variable {c d e : Obj} {a' b' : Obj}

end Mate

/-! ## Pasting of squares -/

section Paste

end Paste

end TwoAdj

end UlmerBialgebras
