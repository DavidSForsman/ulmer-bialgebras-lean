module

public import Mathlib.CategoryTheory.Presentable.Basic
public import UlmerBialgebras.Basic.InsEqCat

/-!
# Inserters and equifiers of accessible functors: colimits and presentable objects

This file contains the "easy half" of the closure of `Acc` under inserters and equifiers:
for a parallel pair `F, G : C ⥤ D` of `κ`-accessible functors,

* the inserter `Ins F G` and the equifier `Equif η θ` have `κ`-filtered colimits, created
  by the forgetful functors to `C` (`UlmerBialgebras.Ins.isColimitCocone`,
  `UlmerBialgebras.equifProp_isClosedUnderColimitsOfShape`);
* the forgetful functors `Ins F G ⥤ C` and `Equif η θ ⥤ C` are `κ`-accessible;
* the functors into `Ins F G` and `Equif η θ` induced by `κ`-accessible functors are
  `κ`-accessible (so that the universal properties of these PIE limits restrict to
  accessible categories and functors);
* `κ`-presentable objects: an object `⟨x, ψ⟩` of the inserter is `κ`-presentable as soon
  as `x` and `F x` are `κ`-presentable (`UlmerBialgebras.Ins.isCardinalPresentable`), and an object
  of the equifier is `κ`-presentable as soon as it is so in `C`
  (`UlmerBialgebras.Equif.isCardinalPresentable`).

What remains for the full accessibility of `Ins F G` and `Equif η θ` is the *generation*
step: every object must be a `λ`-filtered colimit of `λ`-presentable objects of the
inserter (resp. the equifier), for a suitable `λ`.  That step genuinely needs a second
cardinal `λ` with `κ ◁ λ` and a transfinite closure argument; it is carried out in
`AccessibleInserter.lean` and `AccessibleEquifier.lean`.

## Main results

* `UlmerBialgebras.Ins.hasCardinalFilteredColimits`,
  `UlmerBialgebras.Equif.hasCardinalFilteredColimits`: the inserter and the equifier have
  `κ`-filtered colimits when `C` has them and `F` is `κ`-accessible.
* `UlmerBialgebras.Ins.forget_isCardinalAccessible`,
  `UlmerBialgebras.Equif.forget_isCardinalAccessible`: the forgetful functors to `C` are
  `κ`-accessible.
* `UlmerBialgebras.Ins.isCardinalPresentable`: an object `⟨x, ψ⟩` of the inserter is `κ`-presentable
  if `x` and `F x` are.
* `UlmerBialgebras.Equif.isCardinalPresentable`: an object of the equifier is `κ`-presentable if it
  is `κ`-presentable in `C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 2.3 and Theorem 5.11
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC],
  2.72 Theorem, 2.76 Lemma
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F G : C ⥤ D}

/-! ## Colimits in the inserter -/

namespace Ins

variable {J : Type*} [Category J]

/-- The structure cell on the colimit of a diagram in the inserter. -/
noncomputable def coconeCell (K : J ⥤ Ins F G) {c : Cocone (K ⋙ forget F G)} (hc : IsColimit c)
    [PreservesColimit (K ⋙ forget F G) F] : F.obj c.pt ⟶ G.obj c.pt :=
  (isColimitOfPreserves F hc).desc
    { pt := G.obj c.pt
      ι := { app := fun j => (K.obj j).cell ≫ G.map (c.ι.app j)
             naturality := fun j j' f => by
               dsimp
               rw [Category.comp_id, ← Category.assoc, ← (K.map f).w, Category.assoc,
                 ← G.map_comp, ← c.w f, Functor.comp_map, forget_map] } }

/-- The defining property of `coconeCell`: its restriction along `F.map (c.ι.app j)` is
`(K.obj j).cell ≫ G.map (c.ι.app j)`. -/
@[reassoc (attr := simp)]
lemma coconeCell_fac (K : J ⥤ Ins F G) {c : Cocone (K ⋙ forget F G)} (hc : IsColimit c)
    [PreservesColimit (K ⋙ forget F G) F] (j : J) :
    F.map (c.ι.app j) ≫ coconeCell K hc = (K.obj j).cell ≫ G.map (c.ι.app j) :=
  (isColimitOfPreserves F hc).fac _ j

/-- The cocone in the inserter lying over a colimit cocone of the underlying diagram. -/
@[simps]
noncomputable def cocone (K : J ⥤ Ins F G) {c : Cocone (K ⋙ forget F G)} (hc : IsColimit c)
    [PreservesColimit (K ⋙ forget F G) F] : Cocone K where
  pt := ⟨c.pt, coconeCell K hc⟩
  ι :=
    { app := fun j => ⟨c.ι.app j, (coconeCell_fac K hc j).symm⟩
      naturality := fun _ _ f => by
        ext
        dsimp
        rw [Category.comp_id]
        exact c.w f }

/-- Colimits of diagrams in the inserter of `F` and `G` are created by the forgetful functor,
as soon as `F` preserves them. -/
noncomputable def isColimitCocone (K : J ⥤ Ins F G) {c : Cocone (K ⋙ forget F G)}
    (hc : IsColimit c) [PreservesColimit (K ⋙ forget F G) F] : IsColimit (cocone K hc) where
  desc s :=
    { base := hc.desc ((forget F G).mapCocone s)
      w := by
        apply (isColimitOfPreserves F hc).hom_ext
        intro j
        have hs := (s.ι.app j).w
        have hfac : c.ι.app j ≫ hc.desc ((forget F G).mapCocone s) = (s.ι.app j).base :=
          hc.fac ((forget F G).mapCocone s) j
        -- (`hc.desc` is typed over `c.pt`, the point of `cocone K hc` only up to unfolding)
        change F.map (c.ι.app j) ≫ coconeCell K hc ≫ G.map (hc.desc ((forget F G).mapCocone s)) =
          F.map (c.ι.app j) ≫ F.map (hc.desc ((forget F G).mapCocone s)) ≫ s.pt.cell
        rw [← Category.assoc, coconeCell_fac K hc j, Category.assoc, ← G.map_comp, hfac,
          ← Category.assoc, ← F.map_comp, hfac]
        exact hs }
  fac s j := by
    ext
    exact hc.fac ((forget F G).mapCocone s) j
  uniq s m hm := by
    ext
    refine hc.uniq ((forget F G).mapCocone s) m.base (fun j => ?_)
    exact congr($(hm j).base)

/-- The inserter of `F` and `G` has colimits of shape `J` when `C` has them and
`F` preserves them. -/
instance hasColimitsOfShape [HasColimitsOfShape J C] [PreservesColimitsOfShape J F] :
    HasColimitsOfShape J (Ins F G) where
  has_colimit K := ⟨_, isColimitCocone K (colimit.isColimit (K ⋙ forget F G))⟩

/-- The forgetful functor of the inserter preserves the colimits that `F` preserves. -/
instance forget_preservesColimitsOfShape [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J (forget F G) where
  preservesColimit {K} :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitCocone K (colimit.isColimit (K ⋙ forget F G)))
      (IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ forget F G))
        (Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)))

end Ins

/-! ## Colimits in the equifier -/

/-- The equifier of `η, θ : F ⟶ G` is closed under the colimits preserved by `F`. -/
lemma equifProp_isClosedUnderColimitsOfShape (η θ : F ⟶ G)
    (J : Type*) [Category J] [PreservesColimitsOfShape J F] :
    (equifProp η θ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le X hX := by
    obtain ⟨p⟩ := hX
    have hF : IsColimit (F.mapCocone p.cocone) := isColimitOfPreserves F p.isColimit
    -- (membership in `equifProp η θ` is the equation `η.app X = θ.app X`)
    refine hF.hom_ext fun j => ?_
    have h : η.app (p.diag.obj j) = θ.app (p.diag.obj j) := p.prop_diag_obj j
    have h1 := η.naturality (p.ι.app j)
    have h2 := θ.naturality (p.ι.app j)
    dsimp at h1 h2 ⊢
    rw [h1, h2, h]

/-! ## The `κ`-accessible situation -/

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-! ### Inserters -/

namespace Ins

/-- The inserter of `F` and `G` has `κ`-filtered colimits when `C` has them and `F` is
`κ`-accessible. -/
instance hasCardinalFilteredColimits [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] : HasCardinalFilteredColimits.{w} (Ins F G) κ where
  hasColimitsOfShape' J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    infer_instance

/-- The forgetful functor of the inserter is `κ`-accessible. -/
instance forget_isCardinalAccessible [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] : (forget F G).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    infer_instance

/-- The inserter is locally small when the ambient category is. -/
instance locallySmall [LocallySmall.{w} C] : LocallySmall.{w} (Ins F G) where
  hom_small x y := small_of_injective (f := fun (f : x ⟶ y) => f.base)
    (fun _ _ h => Hom.ext h)

variable {κ}

/-- An object `⟨x, ψ⟩` of the inserter is `κ`-presentable as soon as `x` is `κ`-presentable
in `C` and `F x` is `κ`-presentable in `D`. -/
lemma isCardinalPresentable [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] (x : Ins F G)
    [IsCardinalPresentable x.pt κ] [IsCardinalPresentable (F.obj x.pt) κ] :
    IsCardinalPresentable x κ := by
  constructor
  intro J _ _
  have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
  have hFJ : PreservesColimitsOfShape J F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible κ J
  have hGJ : PreservesColimitsOfShape J G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible κ J
  constructor
  intro K
  constructor
  intro c hc
  have hfilt := isFiltered_of_isCardinalFiltered J κ
  have hcC : IsColimit ((forget F G).mapCocone c) := isColimitOfPreserves (forget F G) hc
  have hcG : IsColimit ((forget F G ⋙ G).mapCocone c) := isColimitOfPreserves G hcC
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · intro f
    obtain ⟨j, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcC f.base
    have hg' : g ≫ (c.ι.app j).base = f.base := hg
    -- the compatibility square holds after moving to a later stage
    have key : (x.cell ≫ G.map g) ≫ ((forget F G ⋙ G).mapCocone c).ι.app j
        = (F.map g ≫ (K.obj j).cell) ≫ ((forget F G ⋙ G).mapCocone c).ι.app j := by
      have h1 := f.w
      have h2 := (c.ι.app j).w
      dsimp at h1 h2
      simp only [Functor.mapCocone_ι_app, Functor.comp_map, forget_map]
      rw [Category.assoc, ← G.map_comp, hg', h1, Category.assoc, h2, ← Category.assoc,
        ← F.map_comp, hg']
    obtain ⟨k, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcG
      (x.cell ≫ G.map g) (F.map g ≫ (K.obj j).cell) key
    simp only [Functor.comp_map, forget_map] at hu
    refine ⟨k, ⟨g ≫ (K.map u).base, ?_⟩, ?_⟩
    · have hw := (K.map u).w
      rw [G.map_comp, ← Category.assoc, hu, Category.assoc, hw, ← Category.assoc,
        ← F.map_comp]
    · apply Hom.ext
      dsimp
      rw [Category.assoc]
      have := c.w u
      have h3 : (K.map u).base ≫ (c.ι.app k).base = (c.ι.app j).base := by
        rw [← comp_base, this]
      rw [h3]
      exact hg'.symm
  · intro j p q h
    have hb : p.base ≫ ((forget F G).mapCocone c).ι.app j
        = q.base ≫ ((forget F G).mapCocone c).ι.app j := Hom.ext_iff.mp h
    obtain ⟨k, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcC p.base q.base hb
    exact ⟨k, u, Hom.ext hu⟩

variable (κ)

/-- The functor into the inserter induced by a `κ`-accessible functor `h` together with a
natural transformation `h ⋙ F ⟶ h ⋙ G` is `κ`-accessible: the universal property of the
inserter restricts to accessible categories and functors. -/
instance liftFunctor_isCardinalAccessible [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] {X : Type*} [Category X] (h : X ⥤ C) (α : h ⋙ F ⟶ h ⋙ G)
    [h.IsCardinalAccessible κ] : (liftFunctor h α).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have hh : PreservesColimitsOfShape J h := h.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have : PreservesColimitsOfShape J (liftFunctor h α ⋙ forget F G) := hh
    have : ReflectsColimitsOfShape J (forget F G) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves (liftFunctor h α) (forget F G)

end Ins

/-! ### Equifiers -/

namespace Equif

variable {η θ : F ⟶ G}

/-- The equifier of `η` and `θ` has `κ`-filtered colimits when `C` has them and `F` is
`κ`-accessible. -/
instance hasCardinalFilteredColimits [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] : HasCardinalFilteredColimits.{w} (Equif η θ) κ where
  hasColimitsOfShape' J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have := equifProp_isClosedUnderColimitsOfShape η θ J
    infer_instance

/-- The inclusion of the equifier is `κ`-accessible. -/
instance forget_isCardinalAccessible [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] : (forget η θ).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have := equifProp_isClosedUnderColimitsOfShape η θ J
    have : CreatesColimitsOfShape J (equifProp η θ).ι := inferInstance
    infer_instance

/-- The equifier of `η` and `θ` is `w`-locally small when `C` is. -/
instance locallySmall [LocallySmall.{w} C] : LocallySmall.{w} (Equif η θ) where
  hom_small x y := small_of_injective (f := fun (f : x ⟶ y) => f.hom)
    (fun _ _ h => by ext; exact h)

variable {κ}

/-- An object of the equifier which is `κ`-presentable in the ambient category is
`κ`-presentable in the equifier. -/
lemma isCardinalPresentable [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] (x : Equif η θ) [IsCardinalPresentable x.obj κ] :
    IsCardinalPresentable x κ := by
  have e : forget η θ ⋙ coyoneda.obj (Opposite.op x.obj) ≅ coyoneda.obj (Opposite.op x) :=
    NatIso.ofComponents (fun _ => Equiv.toIso
      { toFun := fun f => ObjectProperty.homMk f
        invFun := fun f => (forget η θ).map f
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }) (by intros; rfl)
  exact Functor.isCardinalAccessible_of_natIso e κ

variable (κ)

/-- The functor into the equifier induced by a `κ`-accessible functor equifying `η` and `θ`
is `κ`-accessible: the universal property of the equifier restricts to accessible categories
and functors. -/
instance liftFunctor_isCardinalAccessible [HasCardinalFilteredColimits.{w} C κ]
    [F.IsCardinalAccessible κ] {X : Type*} [Category X] (h : X ⥤ C)
    (H : Functor.whiskerLeft h η = Functor.whiskerLeft h θ)
    [h.IsCardinalAccessible κ] : (liftFunctor h H).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have : HasColimitsOfShape J C := HasCardinalFilteredColimits.hasColimitsOfShape C κ J
    have : PreservesColimitsOfShape J F := F.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have hh : PreservesColimitsOfShape J h := h.preservesColimitsOfShape_of_isCardinalAccessible κ J
    have : PreservesColimitsOfShape J (liftFunctor h H ⋙ forget η θ) := hh
    have := equifProp_isClosedUnderColimitsOfShape η θ J
    have : PreservesColimitsOfShape J (forget η θ) := inferInstance
    have : ReflectsColimitsOfShape J (forget η θ) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves (liftFunctor h H) (forget η θ)

end Equif

end

end UlmerBialgebras
