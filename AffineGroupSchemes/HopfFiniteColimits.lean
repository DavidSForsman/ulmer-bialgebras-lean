module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Foundations.CategoryTheory.Grp.GrpFiniteLimits
public import AffineGroupSchemes.HopfGrpEquiv

/-!
# Finite colimits of commutative Hopf algebras

Transporting `CategoryTheory.hasFiniteLimits_grp` along the equivalence
`AffineGroupSchemes.opCommHopfAlgCatEquivGrp` shows that the category of affine group `R`-schemes
has finite limits, equivalently that the category of commutative Hopf `R`-algebras has finite
colimits. In particular commutative Hopf algebras have binary coproducts (the tensor product, since
coproducts of commutative Hopf algebras are products of affine group schemes, which are computed in
affine schemes).

This is part of the cocompleteness assertion of Proposition 3.1 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

Note that it is *not* the ingredient needed for Theorem 3.16: that one asks for binary
coproducts of affine group schemes (free products), i.e. binary *products* of commutative Hopf
algebras.

## Main results

* `AffineGroupSchemes.hasFiniteLimits_op_commHopfAlgCat`: `(CommHopfAlgCat R)ᵒᵖ` has finite limits.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Proposition 3.1
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Section 1.4
* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AffineGroupSchemes


variable (R : Type u) [CommRing R]

/-- The category of affine group `R`-schemes has finite limits. -/
instance hasFiniteLimits_op_commHopfAlgCat : HasFiniteLimits (CommHopfAlgCat.{u} R)ᵒᵖ :=
  ⟨fun _ _ _ =>
    Adjunction.hasLimitsOfShape_of_equivalence (opCommHopfAlgCatEquivGrp R).functor⟩

end AffineGroupSchemes
