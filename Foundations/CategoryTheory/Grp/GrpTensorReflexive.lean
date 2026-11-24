module

public import Foundations.CategoryTheory.Grp.GrpReflexiveCoeq
public import Foundations.CategoryTheory.Grp.GrpLimits

/-!
# Transferring preservation of reflexive coequalizers

Let `D` be a cartesian monoidal category with finite limits and reflexive coequalizers in which
the binary product preserves reflexive coequalizers componentwise. The aim is the same statement
for the category `Grp D` of group objects of `D`: reflexive coequalizers of group objects are
computed in `D` (`Foundations/CategoryTheory/Grp/GrpReflexiveCoeq.lean`), the forgetful functor is
conservative and preserves them, and the product of group objects is computed in `D`. This file
provides the general transfer tools for that argument.

## Main results

* `CategoryTheory.preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq` —
  a functor preserving the coequalizers of reflexive pairs preserves colimits indexed by the
  walking reflexive pair;
* `CategoryTheory.preservesReflexiveCoeq_of_natIso` — a general transfer criterion for
  preservation of reflexive coequalizers along a conservative functor.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.9
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

section
open CategoryTheory

namespace CategoryTheory

section General

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor preserving the coequalizers of reflexive pairs preserves colimits indexed by the
walking reflexive pair, because the inclusion of the walking parallel pair is final. -/
lemma _root_.CategoryTheory.preservesColimitsOfShape_walkingReflexivePair_of_preservesReflexiveCoeq
    (F : A ⥤ B) [PreservesReflexiveCoeq F] : PreservesColimitsOfShape WalkingReflexivePair F where
  preservesColimit {K} := by
    have : PreservesColimit (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ K) F := by
      refine preservesColimit_of_iso_diagram F
        (K₁ := parallelPair (K.map .left) (K.map .right)) ?_
      exact (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ K)).symm
    exact Functor.Final.preservesColimit_of_comp WalkingParallelPair.inclusionWalkingReflexivePair

/-- **Transfer of preservation of reflexive coequalizers along a conservative functor.**
If `G` is conservative and preserves reflexive coequalizers, `H` preserves reflexive
coequalizers, and `F ⋙ G ≅ G ⋙ H`, then `F` preserves reflexive coequalizers. -/
lemma preservesReflexiveCoeq_of_natIso [HasReflexiveCoequalizers A] (F : A ⥤ A) (G : A ⥤ B)
    (H : B ⥤ B) [G.ReflectsIsomorphisms] [PreservesReflexiveCoeq G] [PreservesReflexiveCoeq H]
    (e : F ⋙ G ≅ G ⋙ H) : PreservesReflexiveCoeq F := by
  constructor
  intro X Y u v hr
  have := hr
  have : PreservesColimit (parallelPair u v) G :=
    CategoryTheory.PreservesReflexiveCoeq.preserves u v hr
  have : IsReflexivePair (G.map u) (G.map v) := isReflexivePair_map G hr
  have : PreservesColimit (parallelPair u v ⋙ G) H := by
    refine preservesColimit_of_iso_diagram H (K₁ := parallelPair (G.map u) (G.map v)) ?_
    exact (diagramIsoParallelPair (parallelPair u v ⋙ G)).symm
  have : PreservesColimit (parallelPair u v) (F ⋙ G) := preservesColimit_of_natIso _ e.symm
  have : IsReflexivePair (F.map u) (F.map v) := isReflexivePair_map F hr
  have : HasColimit (parallelPair u v ⋙ F) := by
    refine hasColimit_of_iso (F := parallelPair (F.map u) (F.map v)) ?_
    exact diagramIsoParallelPair (parallelPair u v ⋙ F)
  have : PreservesColimit (parallelPair u v ⋙ F) G := by
    refine preservesColimit_of_iso_diagram G (K₁ := parallelPair (F.map u) (F.map v)) ?_
    exact (diagramIsoParallelPair (parallelPair u v ⋙ F)).symm
  have : ReflectsColimit (parallelPair u v ⋙ F) G := reflectsColimit_of_reflectsIsomorphisms _ G
  exact preservesColimit_of_reflects_of_preserves F G

end General

section Grp

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  [HasFiniteLimits D]
  [HasReflexiveCoequalizers D]
  [∀ Z : D, PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : D, PreservesReflexiveCoeq (tensorRight Z)]

end Grp

end CategoryTheory

end
