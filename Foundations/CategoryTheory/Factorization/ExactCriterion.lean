module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Foundations.CategoryTheory.Factorization.RegularExact

/-!
# An exactness criterion along a conservative functor

This file records two lemmas for the categorical ingredient (a form of Lemma 6.5 (3)) of
Corollary 6.11: if `U : A ⥤ B` is conservative, preserves finite limits, `A` is regular, `B` is
exact and every internal equivalence relation of `A` admits a coequalizer which is preserved by
`U`, then `A` is exact. The criterion itself is proved elsewhere; this file contains the lemmas
below.

They are the bridge between coequalizers of reflexive pairs and colimits indexed by
the walking reflexive pair (`UlmerBialgebras.preservesColimit_parallelPair_of_reflexive`).

## Main results

* `UlmerBialgebras.preservesColimit_parallelPair_of_reflexive`: a functor preserving colimits
  indexed by the walking reflexive pair preserves the coequalizer of every reflexive pair;
* `UlmerBialgebras.IsEquivRel.isReflexivePair`: an internal equivalence relation is a reflexive
  pair.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4, Lemma 6.5 (3) and Corollary 6.11
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- A functor preserving colimits indexed by the walking reflexive pair preserves the
coequalizer of every reflexive pair. -/
lemma preservesColimit_parallelPair_of_reflexive (U : A ⥤ B) {R c : A} (r s : R ⟶ c)
    [IsReflexivePair r s] [PreservesColimitsOfShape WalkingReflexivePair U] :
    PreservesColimit (parallelPair r s) U :=
  preservesColimit_of_iso_diagram U (inclusionWalkingReflexivePairOfIsReflexivePairIso r s)

/-- An internal equivalence relation is a reflexive pair. -/
lemma IsEquivRel.isReflexivePair {R c : A} {r s : R ⟶ c} (h : IsEquivRel r s) :
    IsReflexivePair r s :=
  ⟨h.diagonal⟩

end UlmerBialgebras
