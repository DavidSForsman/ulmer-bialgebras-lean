module

public import UlmerBialgebras.Proofs.Sec4.Sec4RelativelyAlgebraic
public import UlmerBialgebras.Proofs.Sec2.Sec2
public import UlmerBialgebras.Proofs.Sec3.Sec3
public import UlmerBialgebras.Proofs.Sec4.Sec4
public import UlmerBialgebras.Proofs.Sec5.Sec5_7
public import UlmerBialgebras.Proofs.Sec6.Sec6Loc
public import UlmerBialgebras.Proofs.Sec6.SubSigExact
public import UlmerBialgebras.Proofs.Appendix.Appendix
public import UlmerBialgebras.Proofs.Appendix.AppendixA3A5
public import Companion.Proofs.Extras
public import UlmerBialgebras.Proofs.Sec6.CocommStructure
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import UlmerBialgebras.Examples.MonModel
public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Proofs.Sec6.AffGrpLoc
public import UlmerBialgebras.Proofs.Sec6.ComonDescent
public import UlmerBialgebras.Proofs.Sec6.Sec6Hopf
public import UlmerBialgebras.Proofs.Sec6.UniversalAlgebra.Exactness
public import UlmerBialgebras.Proofs.Sec3.Sec3Ex
public import UlmerBialgebras.Proofs.Sec3.Sec3ExBicat
public import UlmerBialgebras.Proofs.Sec3.Sec3Theories
public import UlmerBialgebras.Proofs.Sec4.Sec4Hopf
public import UlmerBialgebras.Proofs.Sec7.Sec7Variant
public import UlmerBialgebras.Proofs.Sec5.ExtrasAlgTheory
public import Companion.Proofs.ExtrasAlgTheoryFO
public import UlmerBialgebras.Proofs.Sec3.Sec3MonadAlgObject
public import UlmerBialgebras.Proofs.Sec5.CatAccessibleMonadicity
public import UlmerBialgebras.Proofs.Sec5.CardinalMonadicity
public import UlmerBialgebras.Proofs.Sec5.CatCardinalMonadicity
public import UlmerBialgebras.Proofs.Sec5.ExplicitCardinalAccessibility
public import Companion.Proofs.ExtrasClassical
public import Companion.Proofs.ExtrasTheoryMorphism
public import Companion.Proofs.ExtrasAlgTranslations
public import UlmerBialgebras.Proofs.Sec5.ExtrasDoctrinal
public import Companion.Proofs.ExtrasDoctrinalBicat
public import UlmerBialgebras.Proofs.Sec5.HomTwoFunctor
public import UlmerBialgebras.Proofs.Sec5.LaxNatLeftAdjoint
public import UlmerBialgebras.Proofs.Sec5.ThmSevenFourRoute
public import UlmerBialgebras.Proofs.Sec4.Sec4Ex420
public import Companion.Proofs.ExtrasHopf

/-!
# Solution

Proofs of every theorem stated in `Challenge`, with the same statements; Comparator checks that
the statements agree and that only the standard axioms are used.

## Main results

* `Solution.Sec2_3`, `Solution.Sec4`, `Solution.Sec5_7`, `Solution.Sec6Hopf`,
  `Solution.SecAppendix`: proofs of the numbered results of Sections 2–7 and Appendix A;
* `Solution.Extras`: proofs of the checked statements without a number of their own.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
-/

@[expose] public section
