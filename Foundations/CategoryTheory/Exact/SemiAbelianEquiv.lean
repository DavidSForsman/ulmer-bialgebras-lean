module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Foundations.CategoryTheory.Exact.JointlyConservative
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# Barr exactness is invariant under equivalence of categories

All four items of Definition 2.1 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

transfer along an equivalence of categories.  This file records the part of that transfer used in
the development.

## Main results

* `CategoryTheory.hasFiniteLimits_of_equivalence`: a category equivalent to one with finite limits
  has finite limits;
* `CategoryTheory.hasCoequalizer_of_equivalence`: coequalizers are reflected by an equivalence;
* `CategoryTheory.isBarrExact_of_equivalence`: a category equivalent to a Barr-exact category is
  Barr-exact, obtained from the reflection lemma
  `CategoryTheory.isBarrExact_of_jointlyConservative` applied to the one-member family consisting of
  the equivalence itself.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Definition 2.1
* [G. Janelidze, L. Márki, W. Tholen, *Semi-abelian categories*][JANELIDZE2002367]
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory
open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A category equivalent to one with finite limits has finite limits. -/
theorem hasFiniteLimits_of_equivalence (e : C ≌ D) [HasFiniteLimits D] : HasFiniteLimits C :=
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩

/-- Coequalizers are reflected by an equivalence. -/
theorem hasCoequalizer_of_equivalence (e : C ≌ D) {X Y : C} (f g : X ⟶ Y)
    [HasCoequalizer (e.functor.map f) (e.functor.map g)] : HasCoequalizer f g := by
  have : HasColimit (parallelPair f g ⋙ e.functor) :=
    @hasColimit_of_iso _ _ _ _ _ _ ‹_› (diagramIsoParallelPair (parallelPair f g ⋙ e.functor))
  exact Adjunction.hasColimit_of_comp_equivalence (parallelPair f g) e.functor

/-- A category equivalent to a Barr-exact category is Barr-exact. -/
theorem isBarrExact_of_equivalence (e : C ≌ D) [IsBarrExact D] : IsBarrExact C := by
  have : HasFiniteLimits C := hasFiniteLimits_of_equivalence e
  have : Regular D := CategoryTheory.IsBarrExact.toRegular
  -- coequalizers of kernel pairs exist in `C`
  have hcoeq : ∀ {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X}, IsKernelPair f g₁ g₂ →
      HasCoequalizer g₁ g₂ := by
    intro X Y Z f g₁ g₂ hk
    have : HasCoequalizer (e.functor.map g₁) (e.functor.map g₂) :=
      Regular.hasCoequalizer_of_isKernelPair (hk.map e.functor)
    exact hasCoequalizer_of_equivalence e g₁ g₂
  -- and so do coequalizers of internal equivalence relations
  have hcoeqrel : ∀ {R X : C} {r₁ r₂ : R ⟶ X}, IsInternalEquivalenceRelation r₁ r₂ →
      HasCoequalizer r₁ r₂ := by
    intro R X r₁ r₂ hrel
    obtain ⟨Y, f, hk⟩ := CategoryTheory.IsBarrExact.isKernelPair_of_isInternalEquivalenceRelation
      (hrel.map e.functor)
    have : HasCoequalizer (e.functor.map r₁) (e.functor.map r₂) :=
      Regular.hasCoequalizer_of_isKernelPair hk
    exact hasCoequalizer_of_equivalence e r₁ r₂
  refine isBarrExact_of_jointlyConservative (I := PUnit.{1}) (D := fun _ => D)
    (fun _ => e.functor)
    (by
      refine ⟨?_⟩; intro X Y f hf; have := hf PUnit.unit
      exact isIso_of_reflects_iso f e.functor)
    (fun _ => ⟨fun _ _ _ _ _ => inferInstance⟩) hcoeq hcoeqrel

end CategoryTheory
