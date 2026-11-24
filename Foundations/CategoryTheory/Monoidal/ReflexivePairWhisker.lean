module

public import Foundations.CategoryTheory.Grp.GrpRegular
public import Foundations.CategoryTheory.Factorization.ExactCriterion
public import Foundations.CategoryTheory.Limits.ReflexivePairMap

/-!
# Reflexive pairs, coequalizers and whiskering

This file proves three general lemmas about coequalizers of reflexive pairs in a monoidal
category.

They are used for the quotients of Newman's correspondence for internal groups
(`InternalGroups/SubgroupCorrespondence.lean`).

## Main results

* `UlmerBialgebras.isColimitCoforkWhiskerLeft`: when `W ◁ -` preserves coequalizers of reflexive
  pairs, whiskering a reflexive coequalizer on the left gives a coequalizer.

## References

* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type u} [Category.{v} C]

variable [CartesianMonoidalCategory C]

section Whisker

variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorRight X)]

omit [∀ X : C, PreservesColimitsOfShape WalkingReflexivePair (tensorRight X)] in
/-- Whiskering on the left preserves coequalizers of reflexive pairs. -/
noncomputable def isColimitCoforkWhiskerLeft {X Y Z : C} {a b : X ⟶ Y} [IsReflexivePair a b]
    {qq : Y ⟶ Z}
    {w : a ≫ qq = b ≫ qq} (hq : IsColimit (Cofork.ofπ qq w)) (W : C) :
    IsColimit (Cofork.ofπ (W ◁ qq)
      (show (W ◁ a) ≫ (W ◁ qq) = (W ◁ b) ≫ (W ◁ qq) by
        rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w])) := by
  haveI := preservesColimit_parallelPair_of_reflexive (tensorLeft W) a b
  exact isColimitMapCoconeCoforkEquiv (tensorLeft W) w (isColimitOfPreserves (tensorLeft W) hq)

end Whisker

end UlmerBialgebras
