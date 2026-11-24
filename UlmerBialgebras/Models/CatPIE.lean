module

public import UlmerBialgebras.Basic.CatTwoCat
public import UlmerBialgebras.Basic.InsEqCat
public import UlmerBialgebras.Models.Induced
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# `CAT` is PIE-complete

The 2-category `CAT` of categories, functors and natural transformations (`CatTwoCat.lean`)
has strict products, inserters and equifiers, in the sense of Definition 2.1 (see Remark 2.2):

* `UlmerBialgebras.catProduct` — the product of a small family of categories;
* `UlmerBialgebras.catInserter` — the inserter category `Ins F.toFunctor G.toFunctor` of
    `InsEqCat.lean`;
* `UlmerBialgebras.catEquifier` — the equifier category `Equif η.toNatTrans θ.toNatTrans` of
    `InsEqCat.lean`;
* `UlmerBialgebras.catPIEComplete : PIEComplete.{0} Cat.{u, u}`.

Together with `CategoryTheory.Cat.bicategory` this makes all of Section 3 — in particular
Theorem 3.22, the Induced Functor of Algebras Theorem — applicable to ordinary categories,
functors and natural transformations.

## Main results

* `UlmerBialgebras.catProduct`, `UlmerBialgebras.catInserter`, `UlmerBialgebras.catEquifier`:
  products, inserters and equifiers in `CAT`.
* `UlmerBialgebras.exists_product_cat_eq_pi`: small products in `CAT` are cartesian products of
  categories with evaluation projections.
* `UlmerBialgebras.catPIEComplete`: `CAT` is PIE-complete_0 (Definition 2.1, Remark 2.2).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1 and Remark 2.2
* [G. J. Bird, G. M. Kelly, A. J. Power, R. H. Street,
  *Flexible limits for 2-categories*][birdFlexibleLimits2categories1989]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v s t

namespace UlmerBialgebras

open CategoryTheory
open scoped Bicategory

/-! ## Products -/

/-- A family of categories indexed in universe `s` has a strict product in CAT: the category of
families, in `Cat.{max s v, max s u}`. The lifts are taken componentwise. -/
def catProduct {ι : Type s} (c : ι → Cat.{max s v, max s u}) : Product c where
  pt := Cat.of (∀ i, (c i : Type (max s u)))
  π i := (Pi.eval _ i).toCatHom
  lift g := (Functor.pi' (fun i => (g i).toFunctor)).toCatHom
  lift_π _ _ := rfl
  lift_uniq _ := rfl
  -- Keep the components visible at reducible transparency for the concrete theory models.
  lift₂ {_ _ _} α :=
    { toNatTrans := {
        app := fun p i => (α i).toNatTrans.app p
        naturality := (NatTrans.pi' fun i => (α i).toNatTrans).naturality } }
  lift₂_π _ _ := rfl
  lift₂_uniq _ := rfl

section

variable {ι : Type s} (c : ι → Cat.{max s v, max s u})

/-- The apex of `catProduct` is the category of families. -/
lemma catProduct_pt : (catProduct c).pt = Cat.of (∀ i, (c i : Type (max s u))) := rfl

/-- The projections of `catProduct` are the evaluations. -/
lemma catProduct_π (i : ι) : (catProduct c).π i = (Pi.eval _ i).toCatHom := rfl

/-- The lift into `catProduct` of a family of functors is the functor into the families. -/
lemma catProduct_lift {x : Cat.{max s v, max s u}} (g : ∀ i, x ⟶ c i) :
    (catProduct c).lift g = (Functor.pi' (fun i => (g i).toFunctor)).toCatHom := rfl

/-- The lift into `catProduct` of a family of natural transformations is taken componentwise. -/
lemma catProduct_lift₂_app {x : Cat.{max s v, max s u}} {f g : x ⟶ (catProduct c).pt}
    (α : ∀ i, f ≫ (catProduct c).π i ⟶ g ≫ (catProduct c).π i) (p : x) (i : ι) :
    ((catProduct c).lift₂ α).toNatTrans.app p i = (α i).toNatTrans.app p := rfl

/-- Small products in `CAT` are cartesian products of categories: any family
`c : ι → Cat.{max s v, max s u}` has a strict product whose apex is the category of families
`∀ i, c i` and whose projections are the evaluation functors `Pi.eval _ i`. -/
theorem exists_product_cat_eq_pi :
    ∃ P : Product c, P.pt = Cat.of (∀ i, (c i : Type (max s u))) ∧
      HEq P.π (fun i => (Pi.eval (fun j => (c j : Type (max s u))) i).toCatHom) :=
  ⟨catProduct c, rfl, HEq.rfl⟩

end

/-! ## Inserters -/

/-- The inserter lift carries the specified natural transformation. -/
theorem cat_inserter_lift_cell {a b x : Cat.{v, max u v}} {F G : a ⟶ b}
    (h : x ⟶ a) (α : h ≫ F ⟶ h ≫ G) :
    (Ins.liftFunctor h.toFunctor α.toNatTrans).toCatHom ◁
        (Ins.cellNat F.toFunctor G.toFunctor).toCatHom₂ =
      eqToHom rfl ≫ α ≫ eqToHom rfl := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app]
  -- The transports are identities, up to unfolding.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- A functor into the inserter is the lift specified by its projection and structure cell. -/
theorem cat_inserter_lift_unique {a b x : Cat.{v, max u v}} {F G : a ⟶ b}
    (k : x ⟶ Cat.of (Ins F.toFunctor G.toFunctor)) (h : x ⟶ a) (α : h ≫ F ⟶ h ≫ G)
    (hu : k ≫ (Ins.forget F.toFunctor G.toFunctor).toCatHom = h)
    (hφ : k ◁ (Ins.cellNat F.toFunctor G.toFunctor).toCatHom₂ =
      eqToHom (congrArg (· ≫ F) hu) ≫ α ≫ eqToHom (congrArg (· ≫ G) hu).symm) :
    k = (Ins.liftFunctor h.toFunctor α.toNatTrans).toCatHom := by
  subst h
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun x => ?_) (fun x y f => ?_)
  · refine Ins.obj_ext rfl ?_
    have hx := NatTrans.congr_app congr(Cat.Hom₂.toNatTrans $hφ) x
    simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app] at hx
    exact hx
  · apply Ins.hom_ext
    rw [Ins.comp_base, Ins.comp_base, Ins.eqToHom_base, Ins.eqToHom_base]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- A commutative square with identity transports on its horizontal arrows commutes. -/
theorem cat_inserter_square_of_transport {C : Type u} [Category.{v} C] {W X Y Z : C}
    {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {i : Y ⟶ Z}
    (e : (𝟙 W ≫ f ≫ 𝟙 X) ≫ g = h ≫ 𝟙 Y ≫ i ≫ 𝟙 Z) : f ≫ g = h ≫ i := by
  simpa only [Category.id_comp, Category.comp_id] using e

/-- A parallel pair of functors has a strict inserter in `CAT`: the underlying category is the
ordinary inserter `Ins F G`, which stays in `Cat.{v, max u v}`. Its lifts use the functors and
transformations of the ordinary inserter. -/
def catInserter {a b : Cat.{v, max u v}} (F G : a ⟶ b) : Inserter F G where
  pt := Cat.of (Ins F.toFunctor G.toFunctor)
  u := (Ins.forget F.toFunctor G.toFunctor).toCatHom
  φ := (Ins.cellNat F.toFunctor G.toFunctor).toCatHom₂
  lift h α := (Ins.liftFunctor h.toFunctor α.toNatTrans).toCatHom
  lift_u _ _ := rfl
  lift_φ := cat_inserter_lift_cell
  lift_uniq := cat_inserter_lift_unique
  lift₂ {_ _ _} α h :=
    { toNatTrans := {
        app := fun x => ⟨α.toNatTrans.app x,
          cat_inserter_square_of_transport (congr_app (congrArg Cat.Hom₂.toNatTrans h) x)⟩
        naturality := fun _ _ f => Ins.hom_ext (α.toNatTrans.naturality f) } }
  lift₂_u _ _ := rfl
  lift₂_uniq _ _ h := Cat.Hom₂.ext (NatTrans.ext (funext fun x =>
    Ins.hom_ext (congr_app (congrArg Cat.Hom₂.toNatTrans h) x)))

/-- The apex of `catInserter` is the ordinary inserter. -/
lemma catInserter_pt {a b : Cat.{v, max u v}} (F G : a ⟶ b) :
    (catInserter F G).pt = Cat.of (Ins F.toFunctor G.toFunctor) := rfl

/-- The 1-cell out of `catInserter` is the forgetful functor of the ordinary inserter. -/
lemma catInserter_u {a b : Cat.{v, max u v}} (F G : a ⟶ b) :
    (catInserter F G).u = (Ins.forget F.toFunctor G.toFunctor).toCatHom := rfl

/-! ## Equifiers -/

/-- A functor into the equifier is the lift of its projection. -/
theorem cat_equifier_lift_unique {a b x : Cat.{v, max u v}} {F G : a ⟶ b}
    {η θ : F ⟶ G} (k : x ⟶ Cat.of (Equif η.toNatTrans θ.toNatTrans)) (h : x ⟶ a)
    (H : h ◁ η = h ◁ θ) (hk : k ≫ (Equif.forget η.toNatTrans θ.toNatTrans).toCatHom = h) :
    k = (Equif.liftFunctor h.toFunctor (congrArg Cat.Hom₂.toNatTrans H)).toCatHom := by
  subst h
  cases k
  rfl

/-- A parallel pair of natural transformations has a strict equifier in `CAT`: the underlying
category is the full subcategory `Equif η θ`, which stays in `Cat.{v, max u v}`. The full
inclusion gives the lift of 2-cells. -/
def catEquifier {a b : Cat.{v, max u v}} {F G : a ⟶ b} (η θ : F ⟶ G) : Equifier η θ where
  pt := Cat.of (Equif η.toNatTrans θ.toNatTrans)
  e := (Equif.forget η.toNatTrans θ.toNatTrans).toCatHom
  cond := Cat.Hom₂.ext (NatTrans.ext (funext fun x => x.property))
  lift h H := (Equif.liftFunctor h.toFunctor (congrArg Cat.Hom₂.toNatTrans H)).toCatHom
  lift_e _ _ := rfl
  lift_uniq := cat_equifier_lift_unique
  full β :=
    ⟨{ toNatTrans := {
        app := fun x => ObjectProperty.homMk (β.toNatTrans.app x)
        naturality := fun _ _ f =>
          ObjectProperty.hom_ext _ (β.toNatTrans.naturality f) } }, rfl⟩
  faithful _ _ h := Cat.Hom₂.ext (NatTrans.ext (funext fun x =>
    ObjectProperty.hom_ext _ (congr_app (congrArg Cat.Hom₂.toNatTrans h) x)))

/-- The apex of `catEquifier` is the full subcategory where the two transformations agree. -/
lemma catEquifier_pt {a b : Cat.{v, max u v}} {F G : a ⟶ b} (η θ : F ⟶ G) :
    (catEquifier η θ).pt = Cat.of (Equif η.toNatTrans θ.toNatTrans) := rfl

/-- The 1-cell out of `catEquifier` is the inclusion of the full subcategory. -/
lemma catEquifier_e {a b : Cat.{v, max u v}} {F G : a ⟶ b} (η θ : F ⟶ G) :
    (catEquifier η θ).e = (Equif.forget η.toNatTrans θ.toNatTrans).toCatHom := rfl

/-- **`CAT` is PIE-complete_0**: `Cat.{v, max u v}` has products indexed by `Type`, inserters and
equifiers, all strict (Remark 2.2 and Example 2.3 (1) of [forsman2026syntactic]). Instance search
finds it for `Cat.{u, u}` too (`v := u`). -/
instance catPIEComplete : PIEComplete.{0} Cat.{v, max u v} where
  prod c := catProduct c
  finProd c := catProduct (ι := Fin _) c
  ins F G := catInserter F G
  equif η θ := catEquifier η θ

/-- **Finite products in `CAT`**: `Cat.{v, u}` has the strict products of finite families, for
independent `u` and `v` (the product of a family indexed by `Fin n` stays in `Cat.{v, u}`). At
`Cat.{v, max u v}` this is the finite-products parent of `catPIEComplete`, up to unfolding. -/
instance catHasChosenFinProducts : HasChosenFinProducts Cat.{v, u} where
  finProd c := catProduct (ι := Fin _) c

example : (catHasChosenFinProducts : HasChosenFinProducts Cat.{v, max u v}) =
    PIEComplete.toHasChosenFinProducts := rfl

/-- `catPIEComplete` at `Cat.{v, v}`: the same instance, for goals where instance search cannot
solve `max ?u v = v` (for example `Cat.{u + 1, u + 1}`). -/
instance catPIEComplete_self : PIEComplete.{0} Cat.{v, v} := catPIEComplete.{v, v}

/-- `catPIEComplete` at `Cat.{v, v + 1}` (for example `Set = Type v`): the same instance, for
goals where instance search cannot solve `max ?u v = v + 1`. -/
instance catPIEComplete_succ : PIEComplete.{0} Cat.{v, v + 1} := catPIEComplete.{v + 1, v}

/-- `CAT` (in universe `max s t`) has products of size `s`. Not an instance: an instance at a
second size would compete with the products of `catPIEComplete` during instance search. -/
@[implicit_reducible]
def catOfSize : HasChosenProductsOfSize.{s} Cat.{max s t, max s t} :=
  ⟨fun c => catProduct c⟩

section SizeHom

universe w

/-- `CAT` with hom-sets in `max s v` and objects in `max s v w` has products of size `s`. It is
`catOfSize` at `v = w = t`. Not an instance, for the same reason as `catOfSize`. (The object
universe is named `w` so that it sorts after `s` and `v` in normalized levels, which lets instance
search unify `max s v ?w` with `max s v w`.) -/
@[implicit_reducible]
def catOfSizeHom : HasChosenProductsOfSize.{s} Cat.{max s v, max s v w} :=
  ⟨fun c => catProduct.{max v w, v, s} c⟩

end SizeHom

/-- **Small products in `CAT`**: `Cat.{v, max u v}` has the products of families indexed by
`Type v`, the universe of its hom-sets. Not an instance: instance search would choose it for a
signature whose size is not yet known, instead of the size-`0` products of `catPIEComplete`. -/
@[implicit_reducible]
def catHasChosenProductsOfSizeHom : HasChosenProductsOfSize.{v} Cat.{v, max u v} :=
  ⟨fun c => catProduct.{max u v, v, v} c⟩

/-! ## Theorem 3.22 and Corollary 3.23 for categories -/

namespace LaxMor

variable {Sg : TwoSig} {M N : Model Sg Cat.{u, u}} (F : LaxMor M N) (sg : OneSig Sg)

end LaxMor

end UlmerBialgebras
