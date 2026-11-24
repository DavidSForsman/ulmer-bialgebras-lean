module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import UlmerBialgebras.Basic.AccInsEq
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.OpTranslate
public import UlmerBialgebras.Kan.LiftLimits

/-!
# Creation of absolute coequalizers by the forgetful functors of PIE limits

Beck's monadicity theorem asks a functor to create the coequalizers of the parallel pairs
which become split coequalizers downstairs.  Split coequalizers are *absolute* — every
functor preserves them — so no preservation hypothesis on the structure functors of a PIE
limit is needed in order to create them.  This file assembles the tools:

* `UlmerBialgebras.preservesColimit_parallelPair_of_isSplitCoequalizer` — absoluteness of split
  coequalizers, in the form of a `PreservesColimit` statement;
* `UlmerBialgebras.Ins.createsColimit` — the forgetful functor of an inserter creates the colimit of
  a diagram whose image is preserved by the domain functor `F` (the fine-grained form of
  `UlmerBialgebras.Ins.forget_preservesColimitsOfShape`), and
  `UlmerBialgebras.Ins.createsColimitParallelPair` — its specialization to a parallel pair with a
  split coequalizer downstairs, which needs no hypothesis at all;
* `UlmerBialgebras.equifProp_of_isColimit` and `UlmerBialgebras.Equif.createsColimit` — the same for
  an equifier.

These are the two steps of the forgetful functor `U : M^T → M₀` of a Σ-model, and they are
what make Beck's criterion applicable to it (see `BigMonadicity.lean`).

## Main results

* `UlmerBialgebras.preservesColimit_parallelPair_of_isSplitCoequalizer`: every functor preserves the
  colimit of a parallel pair admitting a split coequalizer.
* `UlmerBialgebras.Ins.createsColimit`: the forgetful functor of `Ins F G` creates the colimit of a
  diagram whose underlying colimit is preserved by `F`.
* `UlmerBialgebras.Ins.createsColimitParallelPair`: it creates the coequalizer of every parallel
  pair which is split downstairs.
* `UlmerBialgebras.Equif.createsColimit`: the forgetful functor of an equifier creates the colimits
  which `F` preserves.
* `UlmerBialgebras.Ins.createsLimitParallelPair`, `UlmerBialgebras.Equif.createsLimit`: the dual
  statements for split equalizers and for limits preserved by `G`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.10,
  Lemma 5.2, Corollary 5.3
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Section VI.7
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

section Absolute

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The canonical isomorphism `parallelPair f g ⋙ H ≅ parallelPair (H f) (H g)`. -/
abbrev parallelPairComp {X Y : C} (f g : X ⟶ Y) (H : C ⥤ D) :
    parallelPair f g ⋙ H ≅ parallelPair (H.map f) (H.map g) :=
  diagramIsoParallelPair _

/-- **Split coequalizers are absolute**: every functor preserves the colimit of a parallel
pair admitting a split coequalizer. -/
lemma preservesColimit_parallelPair_of_isSplitCoequalizer {X Y Z : C} {f g : X ⟶ Y} {p : Y ⟶ Z}
    (q : IsSplitCoequalizer f g p) (H : C ⥤ D) : PreservesColimit (parallelPair f g) H :=
  preservesColimit_of_preserves_colimit_cocone q.isCoequalizer
    ((isColimitMapCoconeCoforkEquiv H q.condition).symm (q.map H).isCoequalizer)

/-- **Split coequalizers are absolute**, class form. -/
lemma preservesColimit_parallelPair_of_hasSplitCoequalizer {X Y : C} (f g : X ⟶ Y)
    [HasSplitCoequalizer f g] (H : C ⥤ D) : PreservesColimit (parallelPair f g) H :=
  preservesColimit_parallelPair_of_isSplitCoequalizer
    (HasSplitCoequalizer.isSplitCoequalizer f g) H

end Absolute

/-- A functor into a product of categories preserves a colimit as soon as all of its
components do (the fine-grained form of `UlmerBialgebras.pi'PreservesColimitsOfShape`). -/
instance pi'PreservesColimit {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
    {J : Type*} [Category J] {A : Type*} [Category A] (fs : ∀ j, A ⥤ C j) (K : J ⥤ A)
    [∀ j, PreservesColimit K (fs j)] : PreservesColimit K (Functor.pi' fs) :=
  ⟨fun hc => ⟨piIsColimitOfEval fun j => isColimitOfPreserves (fs j) hc⟩⟩

section Ins

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}

namespace Ins

/-- The forgetful functor of an inserter **creates** the colimit of a diagram whose
underlying colimit is preserved by `F`. -/
@[instance_reducible]
noncomputable def createsColimit {J : Type*} [Category J] (K : J ⥤ Ins F G)
    [PreservesColimit (K ⋙ Ins.forget F G) F] : CreatesColimit K (Ins.forget F G) :=
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Ins.cocone K t
      validLift := Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)
      makesColimit := Ins.isColimitCocone K t }

/-- The forgetful functor of an inserter creates the coequalizer of every parallel pair
which is split downstairs — no hypothesis on `F` is needed, split coequalizers being
absolute. -/
@[instance_reducible]
noncomputable def createsColimitParallelPair {X Y : Ins F G} (f g : X ⟶ Y)
    [HasSplitCoequalizer ((Ins.forget F G).map f) ((Ins.forget F G).map g)] :
    CreatesColimit (parallelPair f g) (Ins.forget F G) := by
  haveI : PreservesColimit (parallelPair f g ⋙ Ins.forget F G) F := by
    have := preservesColimit_parallelPair_of_hasSplitCoequalizer
      ((Ins.forget F G).map f) ((Ins.forget F G).map g) F
    exact preservesColimit_of_iso_diagram F (parallelPairComp f g (Ins.forget F G)).symm
  exact Ins.createsColimit (parallelPair f g)

end Ins

end Ins

section Equif

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}
  {η θ : F ⟶ G}

/-- The colimit of a diagram of objects equifying `η` and `θ` again equifies them, as soon
as `F` preserves that colimit. -/
lemma equifProp_of_isColimit {J : Type*} [Category J] (K : J ⥤ Equif η θ)
    {c : Cocone (K ⋙ Equif.forget η θ)} (hc : IsColimit c)
    [PreservesColimit (K ⋙ Equif.forget η θ) F] : equifProp η θ c.pt := by
  have hF : IsColimit (F.mapCocone c) := isColimitOfPreserves F hc
  apply hF.hom_ext
  intro j
  have h : η.app (K.obj j).obj = θ.app (K.obj j).obj := (K.obj j).property
  have h1 := η.naturality (c.ι.app j)
  have h2 := θ.naturality (c.ι.app j)
  dsimp at h1 h2 ⊢
  rw [h1, h2, h]

/-- The forgetful functor of an equifier **creates** the colimits which `F` preserves. -/
@[instance_reducible]
noncomputable def Equif.createsColimit {J : Type*} [Category J] (K : J ⥤ Equif η θ)
    [HasColimit (K ⋙ Equif.forget η θ)] [PreservesColimit (K ⋙ Equif.forget η θ) F] :
    CreatesColimit K (Equif.forget η θ) :=
  createsColimitFullSubcategoryInclusion' K (colimit.isColimit _)
    (equifProp_of_isColimit K (colimit.isColimit _))

end Equif

/-! ## The dual: split equalizers -/

section AbsoluteDual

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Split equalizers are absolute**: every functor preserves the limit of a parallel pair
admitting a split equalizer. -/
lemma preservesLimit_parallelPair_of_isSplitEqualizer {W X Y : C} {f g : X ⟶ Y} {i : W ⟶ X}
    (q : IsSplitEqualizer f g i) (H : C ⥤ D) : PreservesLimit (parallelPair f g) H :=
  preservesLimit_of_preserves_limit_cone q.isEqualizer
    ((isLimitMapConeForkEquiv H q.condition).symm (q.map H).isEqualizer)

/-- **Split equalizers are absolute**, class form. -/
lemma preservesLimit_parallelPair_of_hasSplitEqualizer {X Y : C} (f g : X ⟶ Y)
    [HasSplitEqualizer f g] (H : C ⥤ D) : PreservesLimit (parallelPair f g) H :=
  preservesLimit_parallelPair_of_isSplitEqualizer
    (HasSplitEqualizer.isSplitEqualizer f g) H

end AbsoluteDual

section InsDual

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}

/-- The forgetful functor of an inserter creates the equalizer of every parallel pair which
is split downstairs — no hypothesis on `G` is needed, split equalizers being absolute. -/
@[instance_reducible]
noncomputable def Ins.createsLimitParallelPair {X Y : Ins F G} (f g : X ⟶ Y)
    [HasSplitEqualizer ((Ins.forget F G).map f) ((Ins.forget F G).map g)] :
    CreatesLimit (parallelPair f g) (Ins.forget F G) := by
  haveI : PreservesLimit (parallelPair f g ⋙ Ins.forget F G) G := by
    have := preservesLimit_parallelPair_of_hasSplitEqualizer
      ((Ins.forget F G).map f) ((Ins.forget F G).map g) G
    exact preservesLimit_of_iso_diagram G (parallelPairComp f g (Ins.forget F G)).symm
  exact Ins.createsLimit (parallelPair f g)

end InsDual

section EquifDual

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F G : C ⥤ D}
  {η θ : F ⟶ G}

/-- The limit of a diagram of objects equifying `η` and `θ` again equifies them, as soon as
`G` preserves that limit. -/
lemma equifProp_of_isLimit {J : Type*} [Category J] (K : J ⥤ Equif η θ)
    {c : Cone (K ⋙ Equif.forget η θ)} (hc : IsLimit c)
    [PreservesLimit (K ⋙ Equif.forget η θ) G] : equifProp η θ c.pt := by
  have hG : IsLimit (G.mapCone c) := isLimitOfPreserves G hc
  apply hG.hom_ext
  intro j
  have h : η.app (K.obj j).obj = θ.app (K.obj j).obj := (K.obj j).property
  have h1 := η.naturality (c.π.app j)
  have h2 := θ.naturality (c.π.app j)
  dsimp at h1 h2 ⊢
  rw [← h1, ← h2, h]

/-- The forgetful functor of an equifier **creates** the limits which `G` preserves. -/
@[instance_reducible]
noncomputable def Equif.createsLimit {J : Type*} [Category J] (K : J ⥤ Equif η θ)
    [HasLimit (K ⋙ Equif.forget η θ)] [PreservesLimit (K ⋙ Equif.forget η θ) G] :
    CreatesLimit K (Equif.forget η θ) :=
  createsLimitFullSubcategoryInclusion' K (limit.isLimit _)
    (equifProp_of_isLimit K (limit.isLimit _))

end EquifDual

end UlmerBialgebras
