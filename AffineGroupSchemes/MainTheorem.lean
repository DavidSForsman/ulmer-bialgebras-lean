module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Algebra.Category.CommHopfAlgCat
public import AffineGroupSchemes.HopfGrpEquiv
public import AffineGroupSchemes.HopfCoregular
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Foundations.CategoryTheory.Grp.ProtomodularGrp

/-!
# The main theorem of the paper

This file records the statements of the main results of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

namely Theorem 3.15 (coexactness: the category of affine group `k`-schemes is Barr-exact), in
the form in which the paper proves it, from two cited inputs carried here as explicit hypotheses:

* `HopfAlgebra.InjectiveIsFaithfullyFlat` — Takeuchi's theorem (Theorem 3.9 of the paper): every
  injective morphism of commutative Hopf `k`-algebras is faithfully flat. It gives coregularity
  (Theorem 3.12, `AffineGroupSchemes.CommHopfAlgCat.regular_op` in
  `AffineGroupSchemes/HopfCoregular.lean`). It is now *proved*, in
  `Hopf/Commutative/FaithfulFlatnessUnconditional.lean`
  (`HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_holds`);
* `AffineGroupSchemes.CoeffectiveEquivalenceRelations` — the effectivity of internal equivalence
  relations of affine group schemes, which the paper deduces from Takeuchi's characterisation of
  normal Hopf ideals (Theorem 3.14) together with the cited categorical criterion Theorem 2.3(2). It
  is now derived from Takeuchi's Theorem 4.3 in `AffineGroupSchemes/CoexactEffective.lean`, and
  Theorem 3.15 is restated without hypotheses in `AffineGroupSchemes/CoexactTheorem.lean`.

The theorem itself is `AffineGroupSchemes.coexact_commHopfAlgCat` below.

## Main results

* `AffineGroupSchemes.CoeffectiveEquivalenceRelations`: the statement that for every field `k`,
  every internal equivalence relation in `(CommHopfAlgCat k)ᵒᵖ` is the kernel pair of a morphism.
* `AffineGroupSchemes.coexact_commHopfAlgCat`: Theorem 3.15 of
  [forsman2026semiabeliannessaffinegroupschemes] — assuming `HopfAlgebra.InjectiveIsFaithfullyFlat`
  and `AffineGroupSchemes.CoeffectiveEquivalenceRelations`, `(CommHopfAlgCat k)ᵒᵖ` is Barr-exact.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Theorems 3.12, 3.15 and 3.16
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Chapter 14
* [G. Janelidze, L. Márki, W. Tholen, *Semi-abelian categories*][JANELIDZE2002367]
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [M. Barr, *Exact categories*][Ba]
* [H.-E. Porst, *Limits and colimits of Hopf algebras*][Porst-CoLimits] (local presentability,
  quoted as Proposition 3.1 of [forsman2026semiabeliannessaffinegroupschemes])
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AffineGroupSchemes

open CategoryTheory
open HopfAlgebra

/-- The effectivity of internal equivalence relations of affine group `k`-schemes: every
internal equivalence relation is the kernel pair of a morphism.  Together with coregularity
(Theorem 3.12) this is exactly coexactness, Theorem 3.15 of the paper, which deduces it from
Takeuchi's characterisation of normal Hopf ideals (Theorem 3.14) and from the categorical
criterion Theorem 2.3(2).  It is carried here as an explicit hypothesis; it is derived from
Takeuchi's Theorem 4.3 in `AffineGroupSchemes/CoexactEffective.lean`. -/
def CoeffectiveEquivalenceRelations : Prop :=
  ∀ (k : Type u) [Field k] {R X : (CommHopfAlgCat.{u} k)ᵒᵖ} {r₁ r₂ : R ⟶ X},
    IsInternalEquivalenceRelation r₁ r₂ →
      ∃ (Y : (CommHopfAlgCat.{u} k)ᵒᵖ) (f : X ⟶ Y), IsKernelPair f r₁ r₂

variable (k : Type u) [Field k]

/-- **Theorem 3.15** (coexactness): the category of commutative Hopf `k`-algebras is coexact,
i.e. its opposite is Barr-exact.  Regularity is Theorem 3.12, proved from Takeuchi's faithful
flatness theorem; the effectivity of equivalence relations is the hypothesis `hEff`. -/
theorem coexact_commHopfAlgCat (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    (hEff : CoeffectiveEquivalenceRelations.{u}) : IsBarrExact (CommHopfAlgCat.{u} k)ᵒᵖ where
  toRegular := CommHopfAlgCat.regular_op hInjFlat
  isKernelPair_of_isInternalEquivalenceRelation := hEff k

end AffineGroupSchemes
