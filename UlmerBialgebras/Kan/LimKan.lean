module

public import UlmerBialgebras.Kan.ColimKan

/-!
# Limits as right Kan extensions along `I → 1`

Dually to `ColimKan.lean`: in the 2-category `CAT`, a right extension of a functor
`d : I ⥤ C` along the unique functor `I → 1` into the terminal category is the same thing
as a cone over `d`, and a terminal such extension is the same thing as a limit cone.

* `UlmerBialgebras.coneOfRightExt`, `UlmerBialgebras.rightExtOfCone` — the translation of objects;
* `UlmerBialgebras.rightExtHomEquiv` — the translation of morphisms;
* `UlmerBialgebras.isLimitConeOfRightExt`, `UlmerBialgebras.isTerminalRightExtOfIsLimit` — the
  translation of the universal properties;
* `UlmerBialgebras.preservesRightKan_of_preservesLimitsOfShape` — a functor preserving `I`-limits
  preserves all right Kan extensions along `I ⟶ 1`.

This is what allows the Kan-extension results of Section 4 to be read as statements about
ordinary limits; see `CosiftedModel.lean` for the dual of Corollary 4.17.

## Main results

* `UlmerBialgebras.isLimitConeOfRightExt`: a terminal right extension along `I ⟶ 1` gives a limit
  cone.
* `UlmerBialgebras.isTerminalRightExtOfIsLimit`: a limit cone gives a terminal right extension.
* `UlmerBialgebras.preservesRightKan_of_preservesLimitsOfShape`: a functor preserving `I`-limits
  preserves all right Kan extensions along `I ⟶ 1`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 4.2
* [R. Street, R. Walters, *Yoneda structures on
  2-categories*][streetYonedaStructures2categories1978]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {I C D : Cat.{v, u}}

/-! ## Cones and right extensions -/

/-- The cone over `d` corresponding to a right extension of `d` along `I ⟶ 1`. -/
@[simps]
def coneOfRightExt {d : I ⟶ C} (R : RightExt (toOne I) d) :
    Cone d.toFunctor where
  pt := R.ext.toFunctor.obj One.star
  π :=
    { app := fun i => R.counit.toNatTrans.app i
      naturality := fun i j g => by
        have h := R.counit.toNatTrans.naturality g
        have h3 : (toOne I ≫ R.ext).toFunctor.map g = 𝟙 (R.ext.toFunctor.obj One.star) :=
            R.ext.toFunctor.map_id One.star
        dsimp at h ⊢
        exact (h3.symm =≫ R.counit.toNatTrans.app j).trans h }

/-- The right extension of `d` along `I ⟶ 1` corresponding to a cone over `d`. -/
def rightExtOfCone {d : I ⟶ C} (c : Cone d.toFunctor) :
    RightExt (toOne I) d :=
  RightExt.mk ((Functor.const One.{v, u}).obj c.pt).toCatHom c.π.toCatHom₂

/-- Morphisms of right extensions along `I ⟶ 1` are morphisms of the corresponding
cones. -/
def rightExtHomEquiv {d : I ⟶ C} (R R' : RightExt (toOne I) d) :
    (R ⟶ R') ≃ (coneOfRightExt R ⟶ coneOfRightExt R') where
  toFun a :=
    { hom := (RightExt.homCell a).toNatTrans.app One.star
      w := fun i => NatTrans.congr_app congr($(RightExt.w a).toNatTrans) i }
  invFun m := RightExt.homMk (oneNat m.hom).toCatHom₂ (by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext i
    exact m.w i)
  left_inv a := by
    apply RightExt.hom_ext
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    cases x
    rfl
  right_inv m := rfl

/-- A terminal right extension gives a limit cone. -/
noncomputable def isLimitConeOfRightExt {d : I ⟶ C} {R : RightExt (toOne I) d}
    (h : IsTerminal R) : IsLimit (coneOfRightExt R) :=
  (Cone.isLimitEquivIsTerminal _).symm
    (IsTerminal.ofUniqueHom (fun c => (rightExtHomEquiv (rightExtOfCone c) R) (h.from _))
      (fun c m => by
        have hm : (rightExtHomEquiv (rightExtOfCone c) R).symm m = h.from _ := h.hom_ext _ _
        rw [← hm]
        exact (Equiv.apply_symm_apply _ m).symm))

/-- A limit cone gives a terminal right extension. -/
noncomputable def isTerminalRightExtOfIsLimit {d : I ⟶ C} {R : RightExt (toOne I) d}
    (hc : IsLimit (coneOfRightExt R)) : IsTerminal R :=
  IsTerminal.ofUniqueHom
    (fun R' => (rightExtHomEquiv R' R).symm
      (((Cone.isLimitEquivIsTerminal _) hc).from (coneOfRightExt R')))
    (fun R' m => by
      have hm : rightExtHomEquiv R' R m = ((Cone.isLimitEquivIsTerminal _) hc).from _ :=
        ((Cone.isLimitEquivIsTerminal _) hc).hom_ext _ _
      rw [← hm, Equiv.symm_apply_apply])

/-- Pushing a right extension along a 1-cell `F` corresponds to applying `F` to the
corresponding cone. -/
def coneOfRightExtPushIso {d : I ⟶ C} (F : C ⟶ D) (R : RightExt (toOne I) d) :
    coneOfRightExt ((RightExt.push (toOne I) d F).obj R) ≅
      F.toFunctor.mapCone (coneOfRightExt R) :=
  Cone.ext (Iso.refl _) (by
    intro i
    simp [coneOfRightExt, RightExt.push, toOne])

/-! ## Preservation -/

/-- A functor preserving `I`-limits preserves all right Kan extensions along `I ⟶ 1`. -/
theorem preservesRightKan_of_preservesLimitsOfShape (F : C ⟶ D) (d : I ⟶ C)
    [PreservesLimitsOfShape (I : Type u) F.toFunctor] :
    PreservesRightKan (toOne I) d F := by
  intro R hR
  refine ⟨isTerminalRightExtOfIsLimit ?_⟩
  refine IsLimit.ofIsoLimit ?_ (coneOfRightExtPushIso F R).symm
  exact isLimitOfPreserves F.toFunctor (isLimitConeOfRightExt hR.some)

end UlmerBialgebras
