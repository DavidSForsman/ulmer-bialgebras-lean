module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Foundations.CategoryTheory.Grp.GrpObjPullback
public import Foundations.CategoryTheory.Grp.GrpLimits

/-!
# Finite limits of internal group objects

Let `C` be a cartesian monoidal category with pullbacks.  Together with
`Foundations/CategoryTheory/Grp/GrpObjPullback.lean` (pullbacks in `Grp C`) and the trivial group
object,
which we show here to be terminal, this gives finite limits in `Grp C`. Mathlib supplies
the terminal-object and pullback instances. The finite-limit instance below only packages
these shape-wise limits, using the finite-limit adapter from
`Foundations/CategoryTheory/Grp/GrpLimits.lean`.

For `C = (CommAlgCat R)ᵒᵖ` this says that the category of affine group `R`-schemes has finite
limits, i.e. that the category of commutative Hopf `R`-algebras has finite colimits; see
`AffineGroupSchemes/HopfGrpEquiv.lean`.

## Main results

* `CategoryTheory.isTerminalGrpTrivial`: the trivial group object is terminal in `Grp C`;
* `CategoryTheory.hasFiniteLimits_grp`: the category of internal group objects of a cartesian
  monoidal category with pullbacks has finite limits.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.11
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Proposition 3.1
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Section 1.4
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

/-- The trivial group object is terminal in `Grp C` (from Mathlib's `Grp.isZero_trivial`). -/
noncomputable def isTerminalGrpTrivial : IsTerminal (Grp.trivial C) :=
  (Grp.isZero_trivial C).isTerminal

variable [HasPullbacks C]

/-- The category of internal group objects of a cartesian monoidal category with pullbacks has
finite limits. -/
instance hasFiniteLimits_grp : HasFiniteLimits (Grp C) := by
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  exact ⟨fun _ _ _ => inferInstance⟩

end CategoryTheory
