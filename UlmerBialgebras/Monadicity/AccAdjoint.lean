module

public import UlmerBialgebras.Monadicity.AccCompleteIff
public import Mathlib.CategoryTheory.Presentable.SolutionSetCondition

/-!
# Adjoint functor theorems for accessible functors

An accessible functor between accessible categories has a left adjoint as soon as it is
continuous and its domain is complete:

* `UlmerBialgebras.isRightAdjoint_of_isAccessible_of_preservesLimits`.

The proof combines the general adjoint functor theorem with Mathlib's
`CategoryTheory.SolutionSetCondition.of_isCardinalAccessible`.
The dual statement (a cocontinuous accessible functor whose domain is cocomplete has a right
adjoint) is not formalized here.

## Main results

* `CategoryTheory.SolutionSetCondition.of_isCardinalAccessible`: an accessible functor
  between accessible categories satisfies the solution set condition.
* `UlmerBialgebras.isRightAdjoint_of_isAccessible_of_preservesLimits`: an accessible,
  limit-preserving functor between accessible categories, with complete domain, is a right adjoint
  (cf. Theorem 5.10 (2)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.10
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
-/

@[expose] public section

universe w u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]

/-- **Adjoint functor theorem for accessible functors.**  A continuous accessible functor
between accessible categories whose domain is complete has a left adjoint (cf. Theorem
5.10 (2) of [forsman2026syntactic]; [LPC]). -/
theorem isRightAdjoint_of_isAccessible_of_preservesLimits [IsAccessibleCategory.{w} C]
    [IsAccessibleCategory.{w} D] [HasLimitsOfSize.{w, w} C] (F : C ⥤ D) [Functor.IsAccessible.{w} F]
    [PreservesLimitsOfSize.{w, w} F] : F.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_solutionSetCondition F
    (SolutionSetCondition.of_isCardinalAccessible F)

end UlmerBialgebras
