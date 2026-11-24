module

public import UlmerBialgebras.Monadicity.AccCocomplete

/-!
# An accessible category is complete if and only if it is cocomplete

Putting together

* `UlmerBialgebras.hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits` (`AccCocomplete.lean`):
  a complete accessible category is cocomplete, and
* `UlmerBialgebras.hasLimitsOfSize_of_isLocallyPresentable` (`LPComplete.lean`): a locally
  presentable category is complete,

we obtain the classical theorem of Adámek–Rosický ([LPC], Corollary 2.47) that an accessible
category is complete iff it is cocomplete, in the following form:

* `UlmerBialgebras.isLocallyPresentable_of_isAccessibleCategory` — an accessible category which is
  complete or cocomplete is locally presentable;
* `UlmerBialgebras.isLocallyPresentable_of_hasColimits`,
  `UlmerBialgebras.isCardinalLocallyPresentable_of_hasColimits` — a cocomplete accessible category
  is locally presentable.

Note that in Mathlib local presentability is *defined* as accessibility together with
cocompleteness, so the substance of the last statement is the implication
"complete ⇒ cocomplete".

## Main results

* `UlmerBialgebras.isCardinalLocallyPresentable_of_hasColimits`: a cocomplete `κ`-accessible
  category is locally `κ`-presentable.
* `UlmerBialgebras.isLocallyPresentable_of_hasColimits`: a cocomplete accessible category is locally
  presentable.
* `UlmerBialgebras.isLocallyPresentable_of_isAccessibleCategory`: an accessible category which is
  complete or cocomplete is locally presentable.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 5.3
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Corollary 2.47
-/

@[expose] public section

universe w u

namespace UlmerBialgebras

open CategoryTheory Limits

variable (C : Type u) [Category.{w} C]

/-- A cocomplete `κ`-accessible category is locally `κ`-presentable. -/
theorem isCardinalLocallyPresentable_of_hasColimits (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory.{w} C κ] [HasColimitsOfSize.{w, w} C] :
    IsCardinalLocallyPresentable.{w} C κ where

/-- **A cocomplete accessible category is locally presentable.** -/
theorem isLocallyPresentable_of_hasColimits [IsAccessibleCategory.{w} C]
    [HasColimitsOfSize.{w, w} C] : IsLocallyPresentable.{w} C where
  exists_cardinal := by
    obtain ⟨κ, _, _⟩ := IsAccessibleCategory.exists_cardinal.{w} C
    exact ⟨κ, inferInstance, isCardinalLocallyPresentable_of_hasColimits C κ⟩

/-- **An accessible category which is complete or cocomplete is locally presentable.** -/
theorem isLocallyPresentable_of_isAccessibleCategory [IsAccessibleCategory.{w} C]
    (h : HasLimitsOfSize.{w, w} C ∨ HasColimitsOfSize.{w, w} C) : IsLocallyPresentable.{w} C := by
  have : HasColimitsOfSize.{w, w} C := by
    rcases h with h | h
    · have := h
      exact hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits C
    · exact h
  exact isLocallyPresentable_of_hasColimits C

end UlmerBialgebras
