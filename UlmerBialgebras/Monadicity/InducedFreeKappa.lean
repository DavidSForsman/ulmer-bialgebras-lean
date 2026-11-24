module

public import Mathlib.SetTheory.Cardinal.Regular
public import UlmerBialgebras.Monadicity.FreeInsTransfinite
public import UlmerBialgebras.Monadicity.FreeEquifTransfinite

/-!
# Bounds for diagram shapes

Cardinal bounds for the diagram shapes used by the free-model constructions.

## Main results

* `UlmerBialgebras.Kappa.shape`: the well-ordered type of ordinals below `κ`, indexing the chains.
* `UlmerBialgebras.Kappa.mk_shape_le`: `UlmerBialgebras.Kappa.shape κ` has cardinality at most `κ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

section

variable (κ : Cardinal.{w}) (C : Type u) [Category.{v} C]

variable {C} {D : Type u'} [Category.{v'} D]

end

namespace Kappa

variable {κ : Cardinal.{w}}

/-- The well-ordered type of ordinals below `κ`, used as the index of the chains. -/
abbrev shape (κ : Cardinal.{w}) : Type w := κ.ord.ToType

/-- The type of ordinals below `κ` has cardinality at most `κ`. -/
lemma mk_shape_le : Cardinal.mk (shape κ) ≤ κ := by
  rw [Cardinal.mk_toType, Cardinal.card_ord]

end Kappa

open Kappa

end UlmerBialgebras
