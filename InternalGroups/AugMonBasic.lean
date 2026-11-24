module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Foundations.CategoryTheory.Monoidal.CartesianHomExt

/-!
# Augmented monoids: objects, morphisms, and cartesian specialization

An augmented monoid in a monoidal category `C` is a monoid object `X` together with a monoid
morphism `ε : X ⟶ 𝟙_ C` to the tensor unit. In a cartesian monoidal category the tensor unit is
terminal, so every monoid object and every group object carries a canonical augmentation, giving
the functor `InternalGroups.AugMon.grpToAugMon : Grp C ⥤ AugMon C`.

The full quotient-module and stabilizer adjunction lives in the development repository's
`InternalGroups/AugMonQuotGalois.lean`,
the development repository's `InternalGroups/AugMonAdjunction.lean`, the development repository's
`InternalGroups/AugMonCartesian.lean`, and
the development repository's `InternalGroups/AugMonGroup.lean`.

## Main definitions

* `InternalGroups.AugMon`: augmented monoid objects;
* `InternalGroups.AugMon.AugMonHom`: morphisms of augmented monoids;
* `InternalGroups.AugMon.instCategoryAugMon`: the category structure on `AugMon C`;
* `InternalGroups.AugMon.augMonOfMon`: a monoid object in a cartesian monoidal category as an
  augmented monoid;
* `InternalGroups.AugMon.grpToAugMon`: the functor from group objects to augmented monoids;
* `InternalGroups.AugMon.hom_ext_lift_assoc_cartesian`: extensionality on iterated products.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj
open scoped MonObj

namespace InternalGroups

/-- An **augmented monoid** in a monoidal category: a monoid object together with a monoid
morphism `ε : X ⟶ 𝟙_ C`. -/
structure AugMon (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- the underlying object -/
  X : C
  [monObj : MonObj X]
  /-- the augmentation -/
  ε : X ⟶ 𝟙_ C
  [isMonHom_ε : IsMonHom ε]

attribute [instance] AugMon.monObj AugMon.isMonHom_ε

namespace AugMon

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A **morphism of augmented monoids**: a monoid morphism compatible with the augmentations. -/
structure AugMonHom (n m : AugMon C) where
  /-- the underlying morphism -/
  hom : n.X ⟶ m.X
  [isMonHom_hom : IsMonHom hom]
  /-- compatibility with the augmentations -/
  comm : hom ≫ m.ε = n.ε

attribute [instance] AugMonHom.isMonHom_hom
attribute [ext] AugMonHom

/-- The identity morphism of an augmented monoid. -/
def AugMonHom.id (m : AugMon C) : AugMonHom m m where
  hom := 𝟙 m.X
  comm := Category.id_comp _

/-- Composition of morphisms of augmented monoids. -/
def AugMonHom.comp {k m n : AugMon C} (f : AugMonHom k m) (g : AugMonHom m n) :
    AugMonHom k n where
  hom := f.hom ≫ g.hom
  comm := by rw [Category.assoc, g.comm, f.comm]

/-- The underlying morphism of a composite of morphisms of augmented monoids. -/
@[simp] lemma AugMonHom.comp_hom {k m n : AugMon C} (f : AugMonHom k m) (g : AugMonHom m n) :
    (f.comp g).hom = f.hom ≫ g.hom := rfl

/-- The category of augmented monoids in a monoidal category: objects are augmented monoids
and morphisms are `InternalGroups.AugMon.AugMonHom`. -/
instance instCategoryAugMon : Category (AugMon C) where
  Hom n m := AugMonHom n m
  id m := AugMonHom.id m
  comp f g := AugMonHom.comp f g
  assoc f g h := by ext; simp [AugMonHom.comp_hom, Category.assoc]
  id_comp f := by ext; simp [AugMonHom.comp_hom, AugMonHom.id]
  comp_id f := by ext; simp [AugMonHom.comp_hom, AugMonHom.id]

end Monoidal

section Cartesian

open CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- In a cartesian monoidal category a monoid object is an augmented monoid: the augmentation
is the unique map to the terminal unit. -/
abbrev augMonOfMon (M : Mon C) : AugMon C where
  X := M.X
  ε := toUnit M.X
  isMonHom_ε := by
    constructor
    · exact isTerminalTensorUnit.hom_ext _ _
    · exact isTerminalTensorUnit.hom_ext _ _

/-- Extensionality on a product `(A ⊗ B) ⊗ Q`. -/
lemma hom_ext_lift_assoc_cartesian {A B Q D : C} {u v : (A ⊗ B) ⊗ Q ⟶ D}
    (h : ∀ {T : C} (a : T ⟶ A) (b : T ⟶ B) (y : T ⟶ Q),
      lift (lift a b) y ≫ u = lift (lift a b) y ≫ v) : u = v := by
  refine hom_ext_lift ?_
  intro T x y
  have hx : lift (x ≫ fst A B) (x ≫ snd A B) = x := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have h' := h (x ≫ fst A B) (x ≫ snd A B) y
  rwa [hx] at h'

/-- Group objects are augmented monoids, functorially. This is the composite
`grpToMon ⋙ monToAugMon`, written out so that its object part is reducible: later constructions
need `grpToAugMon.obj G` to unfold to the augmented monoid of `G` during elaboration. -/
abbrev grpToAugMon : Grp C ⥤ AugMon C where
  obj G := augMonOfMon G.toMon
  map f :=
    { hom := f.hom.hom
      isMonHom_hom := f.hom.isMonHom_hom
      comm := isTerminalTensorUnit.hom_ext _ _ }
  map_id _ := AugMonHom.ext rfl
  map_comp _ _ := AugMonHom.ext rfl

end Cartesian

end AugMon

end InternalGroups
