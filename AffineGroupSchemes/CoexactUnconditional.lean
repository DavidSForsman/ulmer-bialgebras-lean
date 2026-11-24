module

public import AffineGroupSchemes.CoexactEffective
public import Hopf.Commutative.FaithfulFlatnessUnconditional

/-!
# Coexactness from Takeuchi's Theorem 4.3 alone

`AffineGroupSchemes/CoexactEffective.lean` shows that the surjectivity half of Takeuchi's Theorem
4.3 (`HopfAlgebra.Commutative.NormalHopfIdealEqAugSpan`) implies the effectivity of internal
equivalence relations of affine group schemes
(`AffineGroupSchemes.CoeffectiveEquivalenceRelations`), which was one of the two hypotheses quoted
by Forsman's paper. The other one, Takeuchi's Theorem 3.1, is proved in
`Hopf/Commutative/FaithfulFlatnessUnconditional.lean`, which gives Theorem 3.15 depending only on
the effectivity of internal equivalence relations
(`AffineGroupSchemes.coexact_commHopfAlgCat_unconditional`). With that hypothesis replaced by
Takeuchi's Theorem 4.3 it becomes
`AffineGroupSchemes.coexact_commHopfAlgCat_of_normalHopfIdealEqAugSpan`.

## Main results

* `AffineGroupSchemes.coexact_commHopfAlgCat_unconditional`: `(CommHopfAlgCat k)ᵒᵖ` is Barr-exact,
  assuming `AffineGroupSchemes.CoeffectiveEquivalenceRelations`.
* `AffineGroupSchemes.coexact_commHopfAlgCat_of_normalHopfIdealEqAugSpan`: `(CommHopfAlgCat k)ᵒᵖ` is
  Barr-exact, assuming Takeuchi surjectivity over every field.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.15
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  4.3
* [M. Barr, *Exact categories*][Ba]
* [G. Janelidze, L. Márki, W. Tholen, *Semi-abelian categories*][JANELIDZE2002367]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AffineGroupSchemes
open HopfAlgebra.Commutative

variable (k : Type u) [Field k]

/-- **Theorem 3.15** of [forsman2026semiabeliannessaffinegroupschemes] (coexactness), depending only
on the effectivity of internal equivalence relations of affine group schemes. -/
theorem coexact_commHopfAlgCat_unconditional (hEff : CoeffectiveEquivalenceRelations.{u}) :
    IsBarrExact (CommHopfAlgCat.{u} k)ᵒᵖ :=
  coexact_commHopfAlgCat k injectiveIsFaithfullyFlat_holds hEff

/-- **Theorem 3.15** of [forsman2026semiabeliannessaffinegroupschemes] (coexactness of the
opposite of the category of commutative Hopf algebras, i.e. of the category of affine group
schemes), depending only on the surjectivity half of Takeuchi's Theorem 4.3 [Takeuchi1972]. -/
theorem coexact_commHopfAlgCat_of_normalHopfIdealEqAugSpan
    (hSurj : ∀ (k' H : Type u) [Field k'] [CommRing H] [HopfAlgebra k' H],
      HopfAlgebra.Commutative.NormalHopfIdealEqAugSpan k' H) :
    IsBarrExact (CommHopfAlgCat.{u} k)ᵒᵖ :=
  coexact_commHopfAlgCat_unconditional k
    (coeffectiveEquivalenceRelations_of_normalHopfIdealEqAugSpan hSurj)

end AffineGroupSchemes
