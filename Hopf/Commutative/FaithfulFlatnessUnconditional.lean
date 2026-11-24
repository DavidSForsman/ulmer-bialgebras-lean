module

public import Hopf.CharZero.Reduced
public import Hopf.Commutative.FaithfulFlatnessCharZero
public import Hopf.Commutative.AugSpan

/-!
# Takeuchi's theorem, without hypotheses

The results of `Hopf/Commutative/FaithfulFlatnessCharZero.lean` were stated relative to the explicit
hypothesis `HopfAlgebra.Commutative.CharZeroReduced` (Cartier's theorem, which is not in Mathlib).
That hypothesis is now a theorem, `HopfAlgebra.CharZero.charZeroReduced_holds`, proved in
`Hopf/CharZero/Reduced.lean`, so all of them become unconditional:

* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds`: **Takeuchi's Theorem 3.1**, in the form
  `HopfAlgebra.InjectiveIsFaithfullyFlat` — an injective morphism of commutative Hopf algebras over
  a field makes the target faithfully flat over the source;
* `HopfAlgebra.Commutative.faithfullyFlatOverSubHopf_holds`: the sub-Hopf algebra form
  `HopfAlgebra.Commutative.FaithfullyFlatOverSubHopf`;
* `HopfAlgebra.Commutative.faithfullyFlat_subHopfAlgebra`: the formulation of Takeuchi's paper — a
  commutative Hopf algebra is faithfully flat over each of its sub-Hopf algebras.

The consequence for affine group schemes, `AffineGroupSchemes.coexact_commHopfAlgCat_unconditional`,
is in `AffineGroupSchemes/CoexactUnconditional.lean`.

## Main results

* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds`: `HopfAlgebra.InjectiveIsFaithfullyFlat`
  holds (Takeuchi's Theorem 3.1).
* `HopfAlgebra.Commutative.faithfullyFlatOverSubHopf_holds`:
  `HopfAlgebra.Commutative.FaithfullyFlatOverSubHopf` holds.
* `HopfAlgebra.Commutative.faithfullyFlat_subHopfAlgebra`: a commutative Hopf algebra `H` over a
  field is faithfully flat over each sub-Hopf algebra `K`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 11.4 (Cartier's theorem)
-/

@[expose] public section

universe u

namespace HopfAlgebra.Commutative
open HopfAlgebra.Commutative

/-- **Takeuchi's Theorem 3.1** [Takeuchi1972]: an injective morphism of commutative Hopf algebras
over a field makes the target a faithfully flat module over the source. -/
theorem injectiveIsFaithfullyFlat_holds : HopfAlgebra.InjectiveIsFaithfullyFlat.{u} :=
  HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_of_charZeroReduced
      HopfAlgebra.CharZero.charZeroReduced_holds

/-- **Takeuchi's Theorem 3.1**, in the formulation of the paper: a commutative Hopf algebra over a
field is faithfully flat over each of its sub-Hopf algebras. -/
theorem faithfullyFlatOverSubHopf_holds :
    HopfAlgebra.Commutative.FaithfullyFlatOverSubHopf.{u} :=
  HopfAlgebra.Commutative.faithfullyFlatOverSubHopf_of_charZeroReduced
      HopfAlgebra.CharZero.charZeroReduced_holds

section

/-- **Takeuchi's Theorem 3.1**, in the formulation of the paper: a commutative Hopf algebra `H`
over a field is faithfully flat over any sub-Hopf algebra `K`. -/
theorem faithfullyFlat_subHopfAlgebra (k H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
    (K : Subalgebra k H) (hK : HopfAlgebra.IsSubHopfAlgebra k K) :
    Module.FaithfullyFlat (↥K) H :=
  faithfullyFlatOverSubHopf_holds k H K hK

end

section

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

end

end HopfAlgebra.Commutative
