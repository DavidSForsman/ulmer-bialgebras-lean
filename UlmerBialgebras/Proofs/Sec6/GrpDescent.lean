module

public import UlmerBialgebras.Proofs.Sec6.ExactnessFamilyTransfer
public import Foundations.CategoryTheory.Grp.GrpReflexiveCoeq
public import Foundations.CategoryTheory.Grp.GrpFiniteLimits
public import Foundations.CategoryTheory.Exact.SemiAbelianEquiv

/-!
# Descent of exactness for internal groups along a jointly conservative family

The method of the proof of Corollary 6.11. Let `C` and `D i` be cartesian categories with
finite limits and reflexive coequalizers, preserved by the binary product in each variable.
Let `F i : C ⥤ D i` preserve finite limits and reflexive coequalizers, and suppose the family
is jointly conservative. If every `Grp (D i)` is Barr-exact, then so is `Grp C`.

The induced functors `Grp C ⥤ Grp (D i)` lie over the `F i`. The forgetful functors are
conservative and preserve, hence reflect, finite limits and reflexive coequalizers. So the
induced family is jointly conservative and preserves both. Lemma 6.5 (3), applied to its
functor into the product of the targets (`isBarrExact_of_family_transfer`), gives exactness.

## Main results

* `UlmerBialgebras.Paper.GrpDescent.isBarrExact_grp`: for a jointly conservative family
  `F i : C ⥤ D i` preserving finite limits and reflexive coequalizers, if every `Grp (D i)` is
  Barr-exact, so is `Grp C`.
* `UlmerBialgebras.Paper.GrpDescent.isBarrExact_grp_of_equivalence`: along a single equivalence
  of cartesian monoidal categories, with no hypothesis on limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.5 (3) and Corollary 6.11
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Lemma 4.1
-/

@[expose] public section

universe w v v₂ u u₂

namespace UlmerBialgebras.Paper.GrpDescent

open CategoryTheory Limits MonoidalCategory

/-- A kernel pair `g₁, g₂` of `f` is a reflexive pair, with common section the diagonal
`⟨𝟙, 𝟙⟩ : X ⟶ Z`. -/
lemma isReflexivePair_of_isKernelPair {E : Type*} [Category E] {X Y Z : E} {f : X ⟶ Y}
    {g₁ g₂ : Z ⟶ X} (h : IsKernelPair f g₁ g₂) : IsReflexivePair g₁ g₂ :=
  IsReflexivePair.mk' (h.lift (𝟙 X) (𝟙 X) rfl) (h.lift_fst _ _ _) (h.lift_snd _ _ _)

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {I : Type w} {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
  [∀ i, CartesianMonoidalCategory (D i)]

/-- The induced functors `Grp C ⥤ Grp (D i)` of a jointly conservative family of monoidal functors
form a jointly conservative family. -/
lemma jointlyConservative_mapGrp (F : ∀ i, C ⥤ D i) [∀ i, (F i).Monoidal]
    (hcons : CategoryTheory.JointlyConservative F) :
    CategoryTheory.JointlyConservative (fun i => (F i).mapGrp) := by
  refine ⟨?_⟩
  intro X Y f hf
  have : IsIso ((Grp.forget C).map f) := by
    refine hcons.isIso_of_forall _ (fun i => ?_)
    have := hf i
    exact (inferInstance : IsIso ((Grp.forget (D i)).map ((F i).mapGrp.map f)))
  exact isIso_of_reflects_iso f (Grp.forget C)

section FiniteLimits

variable [HasFiniteLimits C] [∀ i, HasFiniteLimits (D i)]

/-- The functor `Grp C ⥤ Grp (D i)` induced by a monoidal functor preserving finite limits
preserves finite limits. -/
lemma preservesFiniteLimits_mapGrp (i : I) (F : C ⥤ D i) [F.Monoidal] [PreservesFiniteLimits F] :
    PreservesFiniteLimits F.mapGrp := by
  constructor
  intro J _ _
  constructor
  intro K
  have : PreservesLimit K (F.mapGrp ⋙ Grp.forget (D i)) :=
    (inferInstance : PreservesLimit K (Grp.forget C ⋙ F))
  have : ReflectsLimitsOfShape J (Grp.forget (D i)) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimit_of_reflects_of_preserves F.mapGrp (Grp.forget (D i))

end FiniteLimits

variable [HasReflexiveCoequalizers C]
  [∀ Z : C, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : C, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]
  [∀ i, HasReflexiveCoequalizers (D i)]
  [∀ i (Z : D i), CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ i (Z : D i), CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]

/-- The functor `Grp C ⥤ Grp (D i)` induced by a monoidal functor preserving reflexive
coequalizers preserves the coequalizer of a reflexive pair. -/
lemma preservesColimit_mapGrp_of_isReflexivePair (i : I) (F : C ⥤ D i) [F.Monoidal]
    (hrefl : CategoryTheory.PreservesReflexiveCoeq F) {X Y : Grp C} (u v : X ⟶ Y)
    (huv : IsReflexivePair u v) : PreservesColimit (parallelPair u v) F.mapGrp := by
  -- `Grp.forget` creates the coequalizer of a reflexive pair, on both sides; `F` preserves it in
  -- between, so `F.mapGrp ⋙ Grp.forget = Grp.forget ⋙ F` preserves it, and `Grp.forget` reflects
  let G := F.mapGrp
  have hu : IsReflexivePair ((Grp.forget C).map u) ((Grp.forget C).map v) := by
    obtain ⟨s, hs₁, hs₂⟩ := huv.common_section
    exact IsReflexivePair.mk' ((Grp.forget C).map s)
      (by rw [← Functor.map_comp, hs₁, CategoryTheory.Functor.map_id])
      (by rw [← Functor.map_comp, hs₂, CategoryTheory.Functor.map_id])
  have hGu : IsReflexivePair (G.map u) (G.map v) := by
    obtain ⟨s, hs₁, hs₂⟩ := huv.common_section
    exact IsReflexivePair.mk' (G.map s)
      (by rw [← Functor.map_comp, hs₁, CategoryTheory.Functor.map_id])
      (by rw [← Functor.map_comp, hs₂, CategoryTheory.Functor.map_id])
  -- the composite `Grp.forget ⋙ F` preserves the coequalizer
  have : PreservesColimit (parallelPair u v) (Grp.forget C) :=
    CategoryTheory.PreservesReflexiveCoeq.preserves u v huv
  have : PreservesColimit (parallelPair ((parallelPair u v ⋙ Grp.forget C).map
      WalkingParallelPairHom.left) ((parallelPair u v ⋙ Grp.forget C).map
        WalkingParallelPairHom.right)) F := hrefl.preserves _ _ hu
  have : PreservesColimit (parallelPair u v ⋙ Grp.forget C) F :=
    preservesColimit_of_iso_diagram F (diagramIsoParallelPair _).symm
  have : PreservesColimit (parallelPair u v) (G ⋙ Grp.forget (D i)) :=
    (inferInstance : PreservesColimit (parallelPair u v) (Grp.forget C ⋙ F))
  -- the coequalizer of the image pair exists in `Grp (D i)`, and `Grp.forget` preserves it
  have : HasColimit (parallelPair ((parallelPair u v ⋙ G).map
      WalkingParallelPairHom.left) ((parallelPair u v ⋙ G).map
        WalkingParallelPairHom.right)) := by
    have : IsReflexivePair ((parallelPair u v ⋙ G).map WalkingParallelPairHom.left)
        ((parallelPair u v ⋙ G).map WalkingParallelPairHom.right) := hGu
    infer_instance
  have : HasColimit (parallelPair u v ⋙ G) :=
    hasColimit_of_iso (diagramIsoParallelPair _)
  have : PreservesColimit (parallelPair ((parallelPair u v ⋙ G).map
      WalkingParallelPairHom.left) ((parallelPair u v ⋙ G).map
        WalkingParallelPairHom.right)) (Grp.forget (D i)) :=
    CategoryTheory.PreservesReflexiveCoeq.preserves _ _ hGu
  have : PreservesColimit (parallelPair u v ⋙ G) (Grp.forget (D i)) :=
    preservesColimit_of_iso_diagram _ (diagramIsoParallelPair _).symm
  have : ReflectsColimit (parallelPair u v ⋙ G) (Grp.forget (D i)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact preservesColimit_of_reflects_of_preserves G (Grp.forget (D i))

variable [HasFiniteLimits C] [∀ i, HasFiniteLimits (D i)]

/-- **Exactness of internal groups descends along a jointly conservative family.** -/
theorem isBarrExact_grp (F : ∀ i, C ⥤ D i) [∀ i, PreservesFiniteLimits (F i)]
    (hrefl : ∀ i, CategoryTheory.PreservesReflexiveCoeq (F i))
    (hcons : CategoryTheory.JointlyConservative F) [∀ i, CategoryTheory.IsBarrExact (Grp (D i))] :
    CategoryTheory.IsBarrExact (Grp C) := by
  let : ∀ i, (F i).Monoidal := fun i => Functor.Monoidal.ofChosenFiniteProducts (F i)
  have : ∀ i, PreservesFiniteLimits ((F i).mapGrp) := fun i => preservesFiniteLimits_mapGrp i (F i)
  exact isBarrExact_of_family_transfer (fun i => (F i).mapGrp)
    (fun i => ⟨fun _ _ u v huv =>
      preservesColimit_mapGrp_of_isReflexivePair i (F i) (hrefl i) u v huv⟩)
    (jointlyConservative_mapGrp F hcons)

/-- **Barr exactness of internal groups transfers along an equivalence of cartesian monoidal
categories**: the equivalence preserves finite products, so it lifts to internal groups
(`Equivalence.mapGrp`). -/
theorem isBarrExact_grp_of_equivalence {C₁ D₁ : Type*} [Category C₁] [Category D₁]
    [CartesianMonoidalCategory C₁] [CartesianMonoidalCategory D₁] (e : C₁ ≌ D₁)
    [CategoryTheory.IsBarrExact (Grp D₁)] : CategoryTheory.IsBarrExact (Grp C₁) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts e.functor
  letI := Functor.Monoidal.ofChosenFiniteProducts e.inverse
  CategoryTheory.isBarrExact_of_equivalence e.mapGrp

end UlmerBialgebras.Paper.GrpDescent
