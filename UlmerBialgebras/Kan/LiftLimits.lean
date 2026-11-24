module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Creation of limits along the 1-categorical PIE limits

This is the `CAT`-instance of Theorem 4.7 (2), (3) for ordinary limits, which is what the
lifting of regularity and exactness along PIE limits (cf. Theorem 6.6) uses:

* the forgetful functor of an inserter `Ins F G` creates all limits of a shape that `G`
  preserves (`UlmerBialgebras.Ins.createsLimitsOfShape`);
* the forgetful functor of an equifier creates all limits of a shape that `G` preserves
  (via `UlmerBialgebras.equifProp_isClosedUnderLimitsOfShape`).

Products of categories are handled by Mathlib (`CategoryTheory.Limits.Pi`).

## Main results

* `UlmerBialgebras.Ins.createsLimitsOfShape`: the forgetful functor of an inserter `Ins F G` creates
  limits of every shape that `G` preserves.
* `UlmerBialgebras.equifProp_isClosedUnderLimitsOfShape`: the equifier condition is closed under
  limits of every shape that `G` preserves.
* `UlmerBialgebras.Ins.hasLimitsOfShape`, `UlmerBialgebras.Equif.hasLimitsOfShape`: if `C` has
  `J`-limits and `G` preserves them, the inserter and the equifier have `J`-limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 4.7 (2), (3), Corollary 4.8
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3, 3.4
-/

@[expose] public section

universe v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Ins

variable {F G : C ⥤ D}

variable {J : Type*} [Category J]

/-- The structure 2-cell of the lifted limit cone. -/
noncomputable def liftedCell (Dg : J ⥤ Ins F G) (c : Cone (Dg ⋙ forget F G)) (t : IsLimit c)
    [PreservesLimit (Dg ⋙ forget F G) G] : F.obj c.pt ⟶ G.obj c.pt :=
  (isLimitOfPreserves G t).lift
    { pt := F.obj c.pt
      π :=
        { app := fun j => F.map (c.π.app j) ≫ (Dg.obj j).cell
          naturality := fun j j' u => by
            have hw := (Dg.map u).w
            have hc : c.π.app j ≫ (Dg.map u).base = c.π.app j' := by
              simpa using (c.π.naturality u).symm
            simp only [Functor.const_obj_obj, Functor.comp_map, Category.id_comp,
              Functor.const_obj_map, Category.assoc, forget_map]
            rw [hw, ← Category.assoc, ← F.map_comp, hc] } }

/-- The lifted structure 2-cell, followed by `G.map (c.π.app j)`, is
`F.map (c.π.app j) ≫ (Dg.obj j).cell`. -/
lemma liftedCell_comp (Dg : J ⥤ Ins F G) (c : Cone (Dg ⋙ forget F G)) (t : IsLimit c)
    [PreservesLimit (Dg ⋙ forget F G) G] (j : J) :
    liftedCell Dg c t ≫ G.map (c.π.app j) = F.map (c.π.app j) ≫ (Dg.obj j).cell :=
  (isLimitOfPreserves G t).fac _ j

/-- The forgetful functor of an inserter creates the limits of any shape preserved by `G`
(Theorem 4.7 (2) in `CAT`). -/
@[instance_reducible]
noncomputable def createsLimit (Dg : J ⥤ Ins F G) [PreservesLimit (Dg ⋙ forget F G) G] :
    CreatesLimit Dg (forget F G) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := ⟨c.pt, liftedCell Dg c t⟩
          π :=
            { app := fun j => ⟨c.π.app j, liftedCell_comp Dg c t j⟩
              naturality := fun j j' u => by
                ext
                simpa using (c.π.naturality u) } }
      validLift := Cone.ext (Iso.refl _) (by simp)
      makesLimit :=
        { lift := fun s =>
            ⟨t.lift ((forget F G).mapCone s), by
              refine (isLimitOfPreserves G t).hom_ext fun j => ?_
              have hfac : t.lift ((forget F G).mapCone s) ≫ c.π.app j = (s.π.app j).base :=
                t.fac ((forget F G).mapCone s) j
              have hw : s.pt.cell ≫ G.map (s.π.app j).base
                  = F.map (s.π.app j).base ≫ (Dg.obj j).cell := (s.π.app j).w
              simp only [Functor.mapCone_π_app, Category.assoc]
              rw [← G.map_comp, hfac, hw, liftedCell_comp, ← Category.assoc,
                ← F.map_comp, hfac]⟩
          fac := fun s j => by ext; exact t.fac ((forget F G).mapCone s) j
          uniq := fun s m hm => by
            ext
            refine t.uniq ((forget F G).mapCone s) m.base fun j => ?_
            exact congrArg Ins.Hom.base (hm j) } }

/-- The forgetful functor of an inserter creates all limits of a shape preserved by `G`. -/
noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (forget F G) where
  CreatesLimit := createsLimit _

/-- An inserter `Ins F G` has limits of shape `J` when `C` has them and `G` preserves them. -/
instance hasLimitsOfShape [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (Ins F G) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget F G)

/-- An inserter `Ins F G` has finite limits when `C` has them and `G` preserves them. -/
instance hasFiniteLimits [HasFiniteLimits C] [PreservesFiniteLimits G] :
    HasFiniteLimits (Ins F G) where
  out _ _ _ := hasLimitsOfShape

end Ins

/-! ## Equifiers -/

section Equif

variable {F G : C ⥤ D} {η θ : F ⟶ G} {J : Type*} [Category J]

/-- The equifier condition `η.app x = θ.app x` is closed under isomorphisms. -/
instance : (equifProp η θ).IsClosedUnderIsomorphisms where
  of_iso {x y} e hx := by
    have h₁ := η.naturality e.hom
    have h₂ := θ.naturality e.hom
    have hx' : η.app x = θ.app x := hx
    have : F.map e.hom ≫ η.app y = F.map e.hom ≫ θ.app y := by
      rw [h₁, h₂, hx']
    have hiso : IsIso (F.map e.hom) := inferInstance
    exact (cancel_epi (F.map e.hom)).1 this

/-- The equifier condition is closed under limits of shape `J` when `G` preserves them. -/
instance equifProp_isClosedUnderLimitsOfShape [PreservesLimitsOfShape J G] :
    (equifProp η θ).IsClosedUnderLimitsOfShape J := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro X ⟨Dg, hDg⟩
  have hc : IsLimit (limit.cone Dg) := limit.isLimit Dg
  have key := isLimitOfPreserves G hc
  change η.app _ = θ.app _
  refine key.hom_ext fun j => ?_
  simp only [Functor.mapCone_π_app]
  have hπ : (limit.cone Dg).π.app j = limit.π Dg j := rfl
  rw [hπ]
  have h₁ : η.app (limit Dg) ≫ G.map (limit.π Dg j) = F.map (limit.π Dg j) ≫ η.app (Dg.obj j) :=
    (η.naturality (limit.π Dg j)).symm
  have h₂ : θ.app (limit Dg) ≫ G.map (limit.π Dg j) = F.map (limit.π Dg j) ≫ θ.app (Dg.obj j) :=
    (θ.naturality (limit.π Dg j)).symm
  have h₃ : η.app (Dg.obj j) = θ.app (Dg.obj j) := hDg j
  rw [h₁, h₂, h₃]

/-- An equifier `Equif η θ` has limits of shape `J` when `C` has them and `G` preserves them. -/
instance Equif.hasLimitsOfShape [HasLimitsOfShape J C] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (Equif η θ) :=
  Limits.hasLimitsOfShape_of_closedUnderLimits _ _

/-- An equifier `Equif η θ` has finite limits when `C` has them and `G` preserves them. -/
instance Equif.hasFiniteLimits [HasFiniteLimits C] [PreservesFiniteLimits G] :
    HasFiniteLimits (Equif η θ) where
  out _ _ _ := Equif.hasLimitsOfShape

end Equif

end UlmerBialgebras
