module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Monad.Monadicity
public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Monadicity.SplitCreate
public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Monadicity.AccTransfer

/-!
# Creation of limits and colimits by equivalences

An equivalence creates a diagram's limit or colimit whenever it exists in the target
category. These interfaces apply Mathlib's fully faithful creation constructions.

## Main results

* `UlmerBialgebras.createsColimitOfIsEquivalence`: an equivalence creates every colimit which exists
  in the target.
* `UlmerBialgebras.createsLimitOfIsEquivalence`: an equivalence creates every limit which exists in
  the target.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 5.2,
  Corollary 5.3, Theorem 7.6
* [J. M. Beck, *Triples, algebras and cohomology*][Beck]
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## Creation of colimits and limits by an equivalence -/

section EquivCreates

variable {J : Type*} [Category J] {C : Type*} [Category C] {D : Type*} [Category D]

/-- An equivalence creates every colimit which exists downstairs. -/
@[instance_reducible]
noncomputable def createsColimitOfIsEquivalence (D₁ : J ⥤ C) (F : C ⥤ D) [F.IsEquivalence]
    [HasColimit (D₁ ⋙ F)] : CreatesColimit D₁ F :=
  createsColimitOfFullyFaithfulOfIso (F.objPreimage (colimit (D₁ ⋙ F)))
    (F.objObjPreimageIso _)

/-- An equivalence creates every limit which exists downstairs. -/
@[instance_reducible]
noncomputable def createsLimitOfIsEquivalence (D₁ : J ⥤ C) (F : C ⥤ D) [F.IsEquivalence]
    [HasLimit (D₁ ⋙ F)] : CreatesLimit D₁ F :=
  createsLimitOfFullyFaithfulOfIso (F.objPreimage (limit (D₁ ⋙ F)))
    (F.objObjPreimageIso _)

end EquivCreates

end UlmerBialgebras
