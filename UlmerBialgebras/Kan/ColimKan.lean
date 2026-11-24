module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import UlmerBialgebras.Models.CatPIE
public import UlmerBialgebras.Kan.KanModel

/-!
# Colimits as left Kan extensions along `I → 1`

In the 2-category `CAT`, a left extension of a functor `d : I ⥤ C` along the unique functor
`I → 1` into the terminal category is the same thing as a cocone under `d`, and an initial
such extension is the same thing as a colimit cocone.  This file makes that dictionary
precise:

* `UlmerBialgebras.toOne` — the unique functor `I ⟶ 1`;
* `UlmerBialgebras.coconeOfLeftExt`, `UlmerBialgebras.leftExtOfCocone` — the translation of objects;
* `UlmerBialgebras.leftExtHomEquiv` — the translation of morphisms;
* `UlmerBialgebras.isColimitCoconeOfLeftExt`, `UlmerBialgebras.isInitialLeftExtOfIsColimit` —
  the translation of the universal properties;
* `UlmerBialgebras.preservesLeftKan_of_preservesColimitsOfShape` — a functor preserving `I`-colimits
  preserves all left Kan extensions along `I ⟶ 1`.

This is what allows the Kan-extension results of Section 4 to be read as statements about
ordinary colimits; see `SiftedModel.lean` for Corollary 4.17.  In the terminology of
Definition 4.2, a left Kan extension along `I → 1` is an `I`-colimit.

## Main results

* `UlmerBialgebras.isColimitCoconeOfLeftExt`: an initial left extension along `I ⟶ 1` gives a
  colimit cocone.
* `UlmerBialgebras.isInitialLeftExtOfIsColimit`: a colimit cocone gives an initial left
  extension.
* `UlmerBialgebras.preservesLeftKan_of_preservesColimitsOfShape`: a functor preserving `I`-colimits
  preserves all left Kan extensions along `I ⟶ 1`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 4.2
* [R. Street, R. Walters,
  *Yoneda structures on 2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

/-- The unique functor from a category to the terminal category. -/
def toOne (I : Cat.{v, u}) : I ⟶ One.{v, u} :=
  (Functor.const I).obj One.star |>.toCatHom

variable {I C D : Cat.{v, u}}

/-! ## Cocones and left extensions -/

/-- The cocone under `d` corresponding to a left extension of `d` along `I ⟶ 1`. -/
@[simps]
def coconeOfLeftExt {d : I ⟶ C} (L : LeftExt (toOne I) d) :
    Cocone d.toFunctor where
  pt := L.ext.toFunctor.obj One.star
  ι :=
    { app := fun i => L.unit.toNatTrans.app i
      naturality := fun i j g => by
        have h := L.unit.toNatTrans.naturality g
        have h2 : L.ext.toFunctor.map ((toOne I).toFunctor.map g) = 𝟙 (L.ext.toFunctor.obj
            One.star) := L.ext.toFunctor.map_id One.star
        dsimp at h ⊢
        exact h.trans (L.unit.toNatTrans.app i ≫= h2) }

/-- The left extension of `d` along `I ⟶ 1` corresponding to a cocone under `d`. -/
def leftExtOfCocone {d : I ⟶ C} (c : Cocone d.toFunctor) :
    LeftExt (toOne I) d :=
  LeftExt.mk ((Functor.const One.{v, u}).obj c.pt).toCatHom c.ι.toCatHom₂

/-- A natural transformation between functors out of the terminal category is the same thing
as a morphism between their values. -/
@[simps]
def oneNat {E E' : One.{v, u} ⥤ (C : Type u)} (f : E.obj One.star ⟶ E'.obj One.star) : E ⟶ E' where
  app := fun x => match x with | OneObj.star => f
  naturality := by
    rintro ⟨⟩ ⟨⟩ g
    obtain rfl : g = 𝟙 One.star.{v, u} := rfl
    exact (E.map_id One.star.{v, u} =≫ f).trans ((Category.id_comp f).trans
      ((Category.comp_id f).symm.trans (f ≫= (E'.map_id One.star.{v, u}).symm)))

/-- Morphisms of left extensions along `I ⟶ 1` are morphisms of the corresponding
cocones. -/
def leftExtHomEquiv {d : I ⟶ C} (L L' : LeftExt (toOne I) d) :
    (L ⟶ L') ≃ (coconeOfLeftExt L ⟶ coconeOfLeftExt L') where
  toFun a :=
    { hom := (LeftExt.homCell a).toNatTrans.app One.star
      w := fun i => NatTrans.congr_app congr($(LeftExt.w a).toNatTrans) i }
  invFun m := LeftExt.homMk (oneNat m.hom).toCatHom₂ (by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext i
    exact m.w i)
  left_inv a := by
    apply LeftExt.hom_ext
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    cases x
    rfl
  right_inv m := rfl

/-- An initial left extension gives a colimit cocone. -/
noncomputable def isColimitCoconeOfLeftExt {d : I ⟶ C} {L : LeftExt (toOne I) d}
    (h : IsInitial L) : IsColimit (coconeOfLeftExt L) :=
  (Cocone.isColimitEquivIsInitial _).symm
    (IsInitial.ofUniqueHom (fun c => leftExtHomEquiv L (leftExtOfCocone c) (h.to _))
      (fun c m => by
        have hm : (leftExtHomEquiv L (leftExtOfCocone c)).symm m = h.to _ := h.hom_ext _ _
        rw [← hm]
        exact (Equiv.apply_symm_apply _ m).symm))

/-- A colimit cocone gives an initial left extension. -/
noncomputable def isInitialLeftExtOfIsColimit {d : I ⟶ C} {L : LeftExt (toOne I) d}
    (hc : IsColimit (coconeOfLeftExt L)) : IsInitial L :=
  IsInitial.ofUniqueHom
    (fun L' => (leftExtHomEquiv L L').symm
      (((Cocone.isColimitEquivIsInitial _) hc).to (coconeOfLeftExt L')))
    (fun L' m => by
      have hm : leftExtHomEquiv L L' m = ((Cocone.isColimitEquivIsInitial _) hc).to _ :=
        ((Cocone.isColimitEquivIsInitial _) hc).hom_ext _ _
      rw [← hm, Equiv.symm_apply_apply])

/-- Pushing a left extension along a 1-cell `F` corresponds to applying `F` to the
corresponding cocone. -/
def coconeOfLeftExtPushIso {d : I ⟶ C} (F : C ⟶ D) (L : LeftExt (toOne I) d) :
    coconeOfLeftExt ((LeftExt.push (toOne I) d F).obj L) ≅
      F.toFunctor.mapCocone (coconeOfLeftExt L) :=
  Cocone.ext (Iso.refl _) (by
    intro i
    simp [coconeOfLeftExt, LeftExt.push, toOne])

/-! ## Preservation -/

/-- A functor preserving `I`-colimits preserves all left Kan extensions along `I ⟶ 1`. -/
theorem preservesLeftKan_of_preservesColimitsOfShape (F : C ⟶ D) (d : I ⟶ C)
    [PreservesColimitsOfShape (I : Type u) F.toFunctor] :
    PreservesLeftKan (toOne I) d F := by
  intro L hL
  refine ⟨isInitialLeftExtOfIsColimit ?_⟩
  refine IsColimit.ofIsoColimit ?_ (coconeOfLeftExtPushIso F L).symm
  exact isColimitOfPreserves F.toFunctor (isColimitCoconeOfLeftExt hL.some)

end UlmerBialgebras
