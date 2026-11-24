module

public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Inserter and equifier categories

The 1-categorical PIE limits of *A Syntactic Approach to Ulmer's Bialgebras* (Remark 2.2),
used throughout Sections 4–7: for a parallel pair of functors `F, G : C ⥤ D` we introduce

* the inserter category `UlmerBialgebras.Ins F G`, whose objects are pairs `(x, φ : F x ⟶ G x)`,
  together with its forgetful functor `UlmerBialgebras.Ins.forget : Ins F G ⥤ C`;
* the equifier category `UlmerBialgebras.Equif η θ` of two natural transformations `η, θ : F ⟶ G`,
  the full subcategory of `C` on the objects where `η` and `θ` agree, with its forgetful
  functor `UlmerBialgebras.Equif.forget`.

Products are Mathlib's product of categories `∀ i, C i` with the projections
`CategoryTheory.Pi.eval`.

`Ins F G` is the same category as Mathlib's inserter `CategoryTheory.Inserter F G`
(`Mathlib/CategoryTheory/Inserter/Basic.lean`), up to a strict isomorphism of categories that
carries the forgetful functor and the universal 2-cell of each to those of the other:
the development repository's `Foundations/CategoryTheory/Limits/InsMathlib.lean`.

We record the basic structural facts (faithfulness, fullness of the equifier inclusion,
and the strict lifting properties of objects and morphisms) which encode that these
categories really are the strict 2-dimensional limits in `CAT`.

## Main definitions

* `UlmerBialgebras.Ins`: the inserter category of `F, G : C ⥤ D`, with objects `(x, φ : F x ⟶ G x)`.
* `UlmerBialgebras.Ins.forget`, `UlmerBialgebras.Ins.liftFunctor`: its forgetful functor to `C` and
  the functor into it induced by `h : X ⥤ C` and `α : h ⋙ F ⟶ h ⋙ G`.
* `UlmerBialgebras.Equif`: the equifier of `η, θ : F ⟶ G`, the full subcategory where `η` and `θ`
  agree.
* `UlmerBialgebras.Equif.forget`, `UlmerBialgebras.Equif.liftFunctor`: its inclusion into `C` and
  the induced functors into it.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1 and Remark 2.2
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
* [G. J. Bird, G. M. Kelly, A. J. Power, R. Street,
  *Flexible limits for 2-categories*][birdFlexibleLimits2categories1989]
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-! ## The inserter category -/

/-- The inserter of a parallel pair of functors `F, G : C ⥤ D`: objects are pairs of an
object `x` of `C` and a morphism `F x ⟶ G x`. -/
structure Ins (F G : C ⥤ D) where
  /-- The underlying object of `C`. -/
  pt : C
  /-- The structure morphism. -/
  cell : F.obj pt ⟶ G.obj pt

namespace Ins

variable {F G : C ⥤ D}

/-- A morphism in the inserter category: a morphism of the underlying objects compatible
with the structure morphisms. -/
@[ext]
structure Hom (x y : Ins F G) where
  /-- The underlying morphism of `C`. -/
  base : x.pt ⟶ y.pt
  /-- Compatibility with the structure morphisms. -/
  w : x.cell ≫ G.map base = F.map base ≫ y.cell

/-- The category structure on the inserter: composition and identities are those of `C`. -/
instance : Category (Ins F G) where
  Hom x y := Hom x y
  id x := ⟨𝟙 x.pt, by simp⟩
  comp {x y z} f g :=
    ⟨f.base ≫ g.base, by
      rw [F.map_comp, G.map_comp, ← Category.assoc, f.w, Category.assoc, g.w, Category.assoc]⟩
/-- The underlying morphism of the identity of `x` is `𝟙 x.pt`. -/
@[simp] lemma id_base (x : Ins F G) : Hom.base (𝟙 x) = 𝟙 x.pt := rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp] lemma comp_base {x y z : Ins F G} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).base = f.base ≫ g.base := rfl


/-- Morphisms in the inserter are equal as soon as their underlying morphisms are. -/
@[ext] lemma hom_ext {x y : Ins F G} {f g : x ⟶ y} (h : f.base = g.base) : f = g :=
  Hom.ext h

/-- The forgetful functor from the inserter category. -/
@[simps, implicit_reducible]
def forget (F G : C ⥤ D) : Ins F G ⥤ C where
  obj x := x.pt
  map f := f.base

/-- The forgetful functor of the inserter is conservative. -/
instance forget_reflectsIsomorphisms : (forget F G).ReflectsIsomorphisms where
  reflects {x y} f hf := by
    have : IsIso f.base := hf
    refine ⟨⟨⟨inv f.base, ?_⟩, ?_, ?_⟩⟩
    · rw [Functor.map_inv, Functor.map_inv, IsIso.eq_inv_comp, ← Category.assoc,
        IsIso.comp_inv_eq]
      exact f.w.symm
    · ext; simp
    · ext; simp

/-- The universal 2-cell of the inserter category. -/
@[simps]
def cellNat (F G : C ⥤ D) : forget F G ⋙ F ⟶ forget F G ⋙ G where
  app x := x.cell
  naturality _ _ f := f.w.symm

/-- The functor into the inserter category induced by a functor `h` together with a natural
transformation `h ⋙ F ⟶ h ⋙ G`. -/
@[simps]
def liftFunctor {X : Type*} [Category X] (h : X ⥤ C) (α : h ⋙ F ⟶ h ⋙ G) : X ⥤ Ins F G where
  obj x := ⟨h.obj x, α.app x⟩
  map {_ _} f := ⟨h.map f, (α.naturality f).symm⟩
  map_id x := by ext; exact h.map_id x
  map_comp f g := by ext; exact h.map_comp f g

/-- The object component of the functor into the inserter category. -/
@[simp] lemma liftFunctor_obj {X : Type*} [Category X] (h : X ⥤ C) (α : h ⋙ F ⟶ h ⋙ G)
    (x : X) : (liftFunctor h α).obj x = ⟨h.obj x, α.app x⟩ := rfl

/-- The morphism component of the functor into the inserter category. -/
@[simp] lemma liftFunctor_map {X : Type*} [Category X] (h : X ⥤ C) (α : h ⋙ F ⟶ h ⋙ G)
    {x y : X} (f : x ⟶ y) :
    (liftFunctor h α).map f = ⟨h.map f, (α.naturality f).symm⟩ := rfl

/-- The underlying morphism of `eqToHom h` is `eqToHom` of the equality of underlying objects. -/
lemma eqToHom_base {x y : Ins F G} (h : x = y) :
    (eqToHom h).base = eqToHom (congrArg Ins.pt h) := by
  subst h; rfl

/-- Objects of the inserter category are strictly determined by their underlying object
together with the structure morphism. -/
lemma obj_ext : ∀ {x y : Ins F G} (h : x.pt = y.pt),
    x.cell = eqToHom (by rw [h]) ≫ y.cell ≫ eqToHom (by rw [h]) → x = y := by
  rintro ⟨x, cx⟩ ⟨y, cy⟩ h h'
  cases h
  simpa using h'

end Ins

/-! ## The equifier category -/

/-- The property of an object of `C` of equifying two natural transformations. -/
def equifProp {F G : C ⥤ D} (η θ : F ⟶ G) : ObjectProperty C := fun x => η.app x = θ.app x

/-- The equifier of two natural transformations `η, θ : F ⟶ G`: the full subcategory of `C`
spanned by the objects `x` with `η x = θ x`. -/
abbrev Equif {F G : C ⥤ D} (η θ : F ⟶ G) : Type u := (equifProp η θ).FullSubcategory

namespace Equif

variable {F G : C ⥤ D} {η θ : F ⟶ G}

/-- The forgetful functor from the equifier category. -/
abbrev forget (η θ : F ⟶ G) : Equif η θ ⥤ C := (equifProp η θ).ι

/-- The functor into the equifier category induced by a functor equifying `η` and `θ`. -/
@[simps]
def liftFunctor {X : Type*} [Category X] (h : X ⥤ C)
    (H : Functor.whiskerLeft h η = Functor.whiskerLeft h θ) : X ⥤ Equif η θ where
  obj x := ⟨h.obj x, congr_app H x⟩
  map f := ⟨h.map f⟩

end Equif

end UlmerBialgebras
