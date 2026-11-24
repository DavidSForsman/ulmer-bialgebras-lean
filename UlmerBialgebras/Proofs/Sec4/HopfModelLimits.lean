module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Kan.SiftedApplications
public import UlmerBialgebras.Kan.RegMonoWidePullback
public import UlmerBialgebras.Proofs.Sec4.OpTranslateWide
public import UlmerBialgebras.Examples.MonModelUpdate

/-!
# Preservation properties of the Hopf model

For a braided monoidal category `C`, the functor symbols of the Hopf model
(`UlmerBialgebras.Paper.HopfModel.hopfModel C`) are the tensor product and the unit. This file shows
that the tensor product preserves (co)limits in each variable as soon as `X ⊗ -` does, which
are the hypotheses of the creation theorems of Section 4 used in Example 4.20.

## Main results

* `UlmerBialgebras.Paper.HopfModel.Internal.colimitsComponentwise`: if every `X ⊗ -` preserves
  `I`-colimits, the functor symbols preserve them componentwise.
* `UlmerBialgebras.Paper.HopfModel.Internal.limitsComponentwise`: the same for `I`-limits.
* `UlmerBialgebras.Paper.HopfModel.Internal.widePushoutsComponentwise`: for `C` monoidal closed, the
  functor symbols preserve wide pushouts of regular epimorphisms in each argument.
* `UlmerBialgebras.Paper.HopfModel.Internal.widePullbacksComponentwise`: if every `X ⊗ -` preserves
  finite limits, the functor symbols preserve finite wide pullbacks of regular monomorphisms in each
  argument.
* `UlmerBialgebras.Paper.HopfModel.Internal.tensorLeft_preservesCoreflexive`: if every `X ⊗ -`
  preserves finite limits, `X ⊗ -` preserves coreflexive equalizers (indexed by the `u`-small
  walking coreflexive pair).
* `UlmerBialgebras.Paper.HopfModel.Internal.regEpisAreReflexiveCoequalizers_of_hasPullbacks`: with
  pullbacks, every regular epimorphism is the coequalizer of a reflexive pair.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 4.20
-/

@[expose] public section

universe u v w w'

namespace UlmerBialgebras.Paper.HopfModel.Internal

open CategoryTheory MonoidalCategory Limits

/-! ## Componentwise preservation by the functor symbols -/

section Braided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- In a braided monoidal `C`, if every `X ⊗ -` preserves colimits of shape `I`, then the functor
symbols `⊗` and `I` of the Hopf model preserve them componentwise (used in Example 4.20 of
[forsman2026syntactic]); `- ⊗ X` is handled through the braiding. -/
theorem colimitsComponentwise (I : Type w') [Category.{w} I]
    (h : ∀ X : C, PreservesColimitsOfShape I (tensorLeft X)) :
    ∀ B, PreservesColimitsComponentwise (hopfModel C) I B := by
  intro B
  cases B with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesColimitsOfShape I (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have := h (x 1)
        have : PreservesColimitsOfShape I (tensorRight (x 1)) :=
          preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · have := h (x 0)
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

/-- In a braided monoidal `C`, if every `X ⊗ -` preserves limits of shape `I`, then the functor
symbols of the Hopf model preserve them componentwise (Example 4.20 of [forsman2026syntactic]). -/
theorem limitsComponentwise (I : Type w') [Category.{w} I]
    (h : ∀ X : C, PreservesLimitsOfShape I (tensorLeft X)) :
    ∀ B, PreservesLimitsComponentwise (hopfModel C) I B := by
  intro B
  cases B with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesLimitsOfShape I (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have := h (x 1)
        have : PreservesLimitsOfShape I (tensorRight (x 1)) :=
          preservesLimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesLimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · have := h (x 0)
        exact preservesLimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

/-- For `C` braided and monoidal closed, the functor symbols of the Hopf model preserve wide
pushouts of regular epimorphisms in each argument (Example 4.20 of [forsman2026syntactic]). -/
theorem widePushoutsComponentwise [MonoidalClosed C] (K : Type w) :
    ∀ (B : HopfEx.twoSig.Fun) (i : Fin (HopfEx.twoSig.arn B))
      (x : ∀ j, ((hopfModel C).obj (HopfEx.twoSig.art B j) : Type u)),
      PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙
        ((hopfModel C).fn B).toFunctor) := by
  intro B
  cases B with
  | tens =>
    intro i x dg _
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesColimitsOfShape (WidePushoutShape K)
          (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have : PreservesColimitsOfShape (WidePushoutShape K) (tensorRight (x 1)) :=
          preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · exact preservesColimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact (key i x).preservesColimit (K := dg)
  | unit => exact fun i _ => i.elim0

/-- If every `X ⊗ -` preserves finite limits, the functor symbols of the Hopf model preserve finite
wide pullbacks of regular monomorphisms in each argument (Example 4.20 of
[forsman2026syntactic]). -/
theorem widePullbacksComponentwise [∀ X : C, PreservesFiniteLimits (tensorLeft X)]
    (K : Type w) [Finite K] :
    ∀ (B : HopfEx.twoSig.Fun) (i : Fin (HopfEx.twoSig.arn B))
      (x : ∀ j, ((hopfModel C).obj (HopfEx.twoSig.art B j) : Type u)),
      RegMonoWide.PreservesWidePullbacksIn K (RegMonoWide.regMono _) (updateFunctor x i ⋙
        ((hopfModel C).fn B).toFunctor) := by
  intro B
  cases B with
  | tens =>
    intro i x dg _
    have := Fintype.ofFinite K
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesLimitsOfShape (WidePullbackShape K)
          (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have : PreservesLimitsOfShape (WidePullbackShape K) (tensorRight (x 1)) :=
          preservesLimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesLimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · exact preservesLimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact (key i x).preservesLimit (K := dg)
  | unit => exact fun i _ => i.elim0

end Braided

/-! ## Coreflexive equalizers are finite limits -/

/-- The walking reflexive pair has finitely many objects. -/
instance walkingReflexivePair_fintype : Fintype WalkingReflexivePair :=
  ⟨{WalkingReflexivePair.zero, WalkingReflexivePair.one}, fun x => by cases x <;> simp⟩

/-- The walking reflexive pair has finitely many morphisms between any two objects. -/
instance walkingReflexivePair_fintypeHom :
    ∀ X Y : WalkingReflexivePair, Fintype (WalkingReflexivePair.Hom X Y)
  | .zero, .zero => ⟨{.id _}, fun f => by cases f; simp⟩
  | .zero, .one => ⟨{.reflexion}, fun f => by cases f; simp⟩
  | .one, .zero => ⟨{.left, .right}, fun f => by cases f <;> simp⟩
  | .one, .one =>
    ⟨{.leftCompReflexion, .rightCompReflexion, .id _}, fun f => by cases f <;> simp⟩

/-- The walking reflexive pair is a finite category. -/
instance walkingReflexivePair_finCategory : FinCategory WalkingReflexivePair where
  fintypeObj := inferInstance
  fintypeHom := fun X Y => walkingReflexivePair_fintypeHom X Y

/-- A functor preserving finite limits preserves coreflexive equalizers. -/
theorem preservesCoreflexive_of_preservesFiniteLimits {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D] (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesLimitsOfShape (walkingCoreflexivePairCat.{u} : Type u) F :=
  preservesLimitsOfShape_of_equiv (AsSmall.equiv (C := WalkingCoreflexivePair)) F

/-- A functor preserving finite limits preserves limits of any shape `J` equivalent to the walking
coreflexive pair. -/
theorem preservesCoreflexive_of_equiv {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    (F : C ⥤ D) [PreservesFiniteLimits F] {J : Type w'} [Category.{w} J]
    (e : WalkingCoreflexivePair ≌ J) : PreservesLimitsOfShape J F :=
  preservesLimitsOfShape_of_equiv e F

/-- If every `X ⊗ -` preserves finite limits, then `X ⊗ -` preserves coreflexive equalizers. -/
theorem tensorLeft_preservesCoreflexive {C : Type u} [Category.{u} C] [MonoidalCategory C]
    [∀ X : C, PreservesFiniteLimits (tensorLeft X)] (X : C) :
    PreservesLimitsOfShape (walkingCoreflexivePairCat.{u} : Type u) (tensorLeft X) :=
  preservesCoreflexive_of_preservesFiniteLimits (tensorLeft X)

/-! ## Regular epimorphisms and kernel pairs -/

/-- With kernel pairs, every regular epimorphism is the coequalizer of its kernel pair, which
is reflexive. -/
theorem regEpisAreReflexiveCoequalizers_of_hasPullbacks {X : Type u} [Category.{v} X]
    [HasPullbacks X] : RegEpisAreReflexiveCoequalizers X := by
  exact OpTranslate.regEpis_reflexive_of_kernelPairs (fun _ => inferInstance)

end UlmerBialgebras.Paper.HopfModel.Internal
